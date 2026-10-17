using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Api;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Iced.Intel;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.InstructionSets;

// This is honestly an X64InstructionSet by all means. Everything here screams "I AM X64".
public class X86InstructionSet : Cpp2IlInstructionSet
{
    private static readonly MasmFormatter Formatter = new();
    private static readonly StringOutput Output = new();
    private static readonly X86CallingConventionResolver CallingConventions = new();

    public override BaseCallingConventionResolver CallingConventionResolver => CallingConventions;

    private static ISIL.Immediate Imm(long value) => new(value);
    private static ISIL.Immediate Imm(ulong value) => new(unchecked((long)value));

    private const int MaxCalleeScanInstructions = 4096;

    // Method decompilation runs in parallel, so these caches are shared across threads.
    private readonly ConcurrentDictionary<(ApplicationAnalysisContext Context, ulong Target), int?> _calleeArgumentCleanupCache = new();
    private readonly ConcurrentDictionary<(ApplicationAnalysisContext Context, ulong Target), bool> _calleeCanReturnCache = new();
    private readonly ConcurrentDictionary<ApplicationAnalysisContext, Lazy<byte[]>> _rawBinaryContentCache = new();

    /// <summary>
    /// Size in bytes that a push/pop of the given operand moves on the stack.
    /// Register and memory operands report their width. Immediate pushes are the exception:
    /// iced reports <see cref="MemorySize.Unknown"/> for them, so they fall back to one stack
    /// slot (the pointer width), which is what the hardware actually moves.
    /// </summary>
    internal static int GetStackAccessSize(Instruction instruction)
    {
        var size = instruction.Op0Kind == OpKind.Register ? instruction.Op0Register.GetSize() : instruction.MemorySize.GetSize();

        if (size == 0)
        {
            // Immediate push: iced reports MemorySize.Unknown. The immediate kind identifies the
            // mode - 64-bit pushes use the sign-extended-to-64 kinds, 32-bit pushes the to-32 ones.
            size = instruction.Op0Kind is OpKind.Immediate8to64 or OpKind.Immediate32to64 ? 8 : 4;
        }

        return size;
    }

    /// <summary>
    /// Checks if the instruction is an add/sub of an immediate to the stack pointer, i.e. a
    /// stack allocation/cleanup like <c>add esp, 8</c>, and if so returns the equivalent
    /// <see cref="ISIL.OpCode.ShiftStack"/> amount (negative when the stack grows).
    /// </summary>
    /// <remarks>
    /// The full register must be compared: in 32-bit mode the stack pointer decodes as ESP, not RSP,
    /// and only its full (upscaled) register is RSP.
    /// </remarks>
    internal static bool TryGetImmediateStackAdjustment(Instruction instruction, out int shiftAmount)
    {
        shiftAmount = 0;

        if (instruction.Op0Register.GetFullRegister() != Register.RSP || !instruction.Op1Kind.IsImmediate())
            return false;

        var amount = (int)instruction.GetImmediate(1);
        shiftAmount = instruction.Mnemonic == Mnemonic.Sub ? -amount : amount;
        return true;
    }

    /// <summary>
    /// Follows control flow from <paramref name="startIp"/> through <paramref name="raw"/> (the raw content
    /// of the whole binary, translated by <paramref name="mapVirtualAddressToRaw"/>) and returns the number
    /// of argument bytes the function pops on return (<c>ret imm16</c> - x86 stdcall / thiscall), or zero if
    /// every reachable return is a plain <c>ret</c> (cdecl / caller cleanup).
    /// Returns null when the cleanup cannot be determined: no reachable return, disagreeing return sizes,
    /// an unresolvable branch, or hitting the instruction budget.
    /// </summary>
    internal static int? TryScanRetArgumentCleanup(byte[] raw, Func<ulong, int> mapVirtualAddressToRaw, ulong startIp, int bitness, int maxInstructions)
    {
        var returnSizes = new HashSet<int>();
        var visited = new HashSet<ulong>();
        var pending = new Queue<ulong>();
        pending.Enqueue(startIp);
        var decodedCount = 0;

        while (pending.Count > 0 && decodedCount < maxInstructions)
        {
            var ip = pending.Dequeue();

            if (!visited.Add(ip))
                continue;

            var offset = mapVirtualAddressToRaw(ip);

            if (offset < 0 || offset >= raw.Length)
                continue; // outside the binary (e.g. code reached through an import)

            var decoder = Decoder.Create(bitness, new ByteArrayCodeReader(raw, offset, raw.Length - offset), ip);

            while (decodedCount < maxInstructions)
            {
                var instruction = decoder.Decode();
                decodedCount++;

                if (instruction.IsInvalid)
                    break; // decodable code ended (or was never here)

                if (instruction.Mnemonic == Mnemonic.Ret)
                {
                    // Plain ret (C3) decodes with Op0Kind.Register, ret imm16 (C2) with OpKind.Immediate16.
                    returnSizes.Add(instruction.Op0Kind == OpKind.Immediate16 ? (int)instruction.GetImmediate(0) : 0);
                    break;
                }

                if (instruction.FlowControl == FlowControl.ConditionalBranch)
                {
                    // All x86 conditional branches are near-relative; explore the taken path, then fall through.
                    pending.Enqueue(instruction.NearBranchTarget);
                    continue;
                }

                if (instruction.FlowControl == FlowControl.UnconditionalBranch)
                {
                    if (instruction.Op0Kind is OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64)
                        pending.Enqueue(instruction.NearBranchTarget);
                    break; // nothing follows a jump in this path
                }

                if (instruction.FlowControl is FlowControl.Next or FlowControl.Call)
                    continue; // calls return to the fall-through address

                break; // indirect branch, interrupt, etc - give up on this path
            }
        }

        if (returnSizes.Count != 1)
            return null;

        return returnSizes.First(); // exactly one distinct size was seen across all reachable returns
    }

    /// <summary>
    /// Determines how many argument bytes the callee at <paramref name="target"/> pops when it returns, by
    /// reading the callee's native code, so call sites to callee-cleanup (stdcall / thiscall) functions can
    /// account for the stack arguments disappearing. Returns 0 for caller-cleanup (cdecl) functions and
    /// null when it could not be determined. Results are cached per binary and target address.
    /// </summary>
    internal int? GetCalleeArgumentCleanup(MethodAnalysisContext context, ulong target)
    {
        var key = (context.AppContext, target);

        if (_calleeArgumentCleanupCache.TryGetValue(key, out var cached))
            return cached;

        int? cleanup = null;
        var app = context.AppContext;
        var binary = app.Binary;

        if (binary.TryMapVirtualAddressToRaw(target, out _))
        {
            cleanup = TryScanRetArgumentCleanup(
                GetRawBinaryContentArray(app),
                va => binary.TryMapVirtualAddressToRaw(va, out var rawAddress) ? (int)rawAddress : -1,
                target,
                binary.is32Bit ? 32 : 64,
                MaxCalleeScanInstructions);
        }

        _calleeArgumentCleanupCache[key] = cleanup;
        return cleanup;
    }

    private byte[] GetRawBinaryContentArray(ApplicationAnalysisContext app)
        => _rawBinaryContentCache.GetOrAdd(app, static appContext => new Lazy<byte[]>(() => appContext.Binary.GetRawBinaryContent().ToArray())).Value;

    /// <summary>
    /// True when a <c>ret</c> is reachable from the function's entry point, i.e. the function can
    /// return to its caller. The walk mirrors <see cref="TryScanRetArgumentCleanup"/>; code that
    /// cannot be scanned (imports, indirect flow, budget exhausted) counts as no return found so
    /// unknown callees never block throw conversion. Results are cached per binary and target.
    /// </summary>
    public override bool CalleeCanReturn(ApplicationAnalysisContext context, ulong address)
    {
        var key = (context, address);
        if (_calleeCanReturnCache.TryGetValue(key, out var cached))
            return cached;

        var result = false;
        var binary = context.Binary;

        if (binary.TryMapVirtualAddressToRaw(address, out _))
        {
            result = HasReachableReturn(
                GetRawBinaryContentArray(context),
                va => binary.TryMapVirtualAddressToRaw(va, out var rawAddress) ? (int)rawAddress : -1,
                address,
                binary.is32Bit ? 32 : 64,
                MaxCalleeScanInstructions);
        }

        _calleeCanReturnCache[key] = result;
        return result;
    }

    internal static bool HasReachableReturn(byte[] raw, Func<ulong, int> mapVirtualAddressToRaw, ulong startIp, int bitness, int maxInstructions)
    {
        var pending = new Queue<ulong>();
        var visited = new HashSet<ulong>();
        pending.Enqueue(startIp);
        var decodedCount = 0;

        while (pending.Count > 0 && decodedCount < maxInstructions)
        {
            var ip = pending.Dequeue();

            if (!visited.Add(ip))
                continue;

            var offset = mapVirtualAddressToRaw(ip);

            if (offset < 0 || offset >= raw.Length)
                continue; // outside the binary (e.g. code reached through an import)

            var decoder = Decoder.Create(bitness, new ByteArrayCodeReader(raw, offset, raw.Length - offset), ip);

            while (decodedCount < maxInstructions)
            {
                var instruction = decoder.Decode();
                decodedCount++;

                if (instruction.IsInvalid)
                    break; // decodable code ended (or was never here)

                if (instruction.Mnemonic == Mnemonic.Ret)
                    return true;

                if (instruction.FlowControl == FlowControl.ConditionalBranch)
                {
                    pending.Enqueue(instruction.NearBranchTarget);
                    continue;
                }

                if (instruction.FlowControl == FlowControl.UnconditionalBranch)
                {
                    if (instruction.Op0Kind is OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64)
                        pending.Enqueue(instruction.NearBranchTarget);
                    break; // nothing follows a jump in this path
                }

                if (instruction.FlowControl is FlowControl.Next or FlowControl.Call)
                    continue; // calls return to the fall-through address

                break; // indirect branch, interrupt, etc - give up on this path
            }
        }

        return false; // no return was ever reached: the function does not return normally
    }

    private static string FormatInstructionInternal(Instruction instruction)
    {
        Formatter.Format(instruction, Output);
        return Output.ToStringAndReset();
    }

    public static string FormatInstruction(Instruction instruction)
    {
        lock (Formatter)
        {
            return FormatInstructionInternal(instruction);
        }
    }

    public override BinarySlice GetRawBytesForMethod(MethodAnalysisContext context, bool isAttributeGenerator) => X86Utils.GetRawManagedOrCaCacheGenMethodBody(context.UnderlyingPointer, isAttributeGenerator, context.AppContext);

    public override BaseKeyFunctionAddresses CreateKeyFunctionAddressesInstance() => new X86KeyFunctionAddresses();

    public override string PrintAssembly(MethodAnalysisContext context)
    {
        lock (Formatter)
        {
            var insns = X86Utils.Iterate(context);

            return string.Join("\n", insns.Select(FormatInstructionInternal));
        }
    }

    public override List<ISIL.Instruction> GetIsilFromMethod(MethodAnalysisContext context)
    {
        var instructions = new List<ISIL.Instruction>();
        var addresses = new List<ulong>();

        foreach (var instruction in X86Utils.Iterate(context))
            ConvertInstructionStatement(instruction, instructions, addresses, context);

        // Add return if the function doesn't end with one already
        if (instructions.Count > 0 && instructions[^1].OpCode != ISIL.OpCode.Return)
        {
            var index = instructions[^1].Index + 1;

            if (context.IsVoid)
                instructions.Add(new ISIL.Instruction(index, ISIL.OpCode.Return));
            else if (context.Definition?.RawReturnType?.Type is Il2CppTypeEnum.IL2CPP_TYPE_R4 or Il2CppTypeEnum.IL2CPP_TYPE_R8)
                instructions.Add(new ISIL.Instruction(index, ISIL.OpCode.Return, new ISIL.Register(null, "xmm0")));
            else
                instructions.Add(new ISIL.Instruction(index, ISIL.OpCode.Return, new ISIL.Register(null, "rax")));
        }

        // Indirect calls can be callee-cleanup (MSVC x86 thiscall for instance method pointers),
        // but unlike direct calls the callee's convention can't be scanned. Infer it from the
        // call site: if the push run immediately before the call isn't covered by a caller-side
        // add esp before the next call or branch, assume the callee popped the arguments.
        AssumeIndirectCallCalleeCleanup(instructions, addresses);

        // Key-function and exception-raiser calls are unmanaged, so on stack-passing x86 their
        // arguments were never attached as operands. Attach the push run so the pushes survive
        // dead-code elimination - the metadata resolver needs the exception operand to turn the
        // call into a CIL throw.
        if (context.AppContext.Binary.PointerSizeBytes == 4)
        {
            var keyFunctionAddresses = context.AppContext.GetOrCreateKeyFunctionAddresses();
            Func<ulong, bool> needsStackArguments = address =>
                keyFunctionAddresses.IsKeyFunctionAddress(address)
                || ThrowHelperRecovery.IsExceptionRaiser(context.AppContext, address);
            AttachKeyFunctionStackArguments(instructions, addresses, needsStackArguments);
        }

        // fix branches
        var conditionalThrowsToSynthesize = new List<(ISIL.Instruction Jump, ISIL.IOperand Exception)>();
        for (var i = 0; i < instructions.Count; i++)
        {
            var instruction = instructions[i];

            if (instruction.OpCode != ISIL.OpCode.Jump && instruction.OpCode != ISIL.OpCode.ConditionalJump)
                continue;

            var targetAddress = ((ISIL.Immediate)instruction.Operands[0]).UnsignedValue;
            var targetIndex = addresses.FindIndex(addr => addr == targetAddress);

            if (targetIndex == -1)
            {
                // A branch to an address outside this method is a tail-branch to an external helper -
                // typically the bounds/null-check path jumping straight to a throw helper such as the
                // IndexOutOfRange raiser. Recover it as a throw of that helper's exception instead of
                // leaving an unrecoverable Invalid.
                if (ThrowHelperRecovery.GetThrownException(context.AppContext, targetAddress) is { } thrownType)
                {
                    if (instruction.OpCode == ISIL.OpCode.Jump)
                    {
                        instruction.OpCode = ISIL.OpCode.Throw;
                        instruction.SetOperands(thrownType);
                        continue;
                    }

                    // Conditional branch to the throw helper: 'if cond -> throw'. The condition and the
                    // success fall-through are already correct, so retarget the branch at a throw block
                    // synthesized after the loop instead of dropping the exception path.
                    conditionalThrowsToSynthesize.Add((instruction, thrownType));
                    continue;
                }

                instruction.OpCode = ISIL.OpCode.Invalid;
                instruction.SetOperands(new ISIL.StringLiteral($"Jump target not found in method: 0x{targetAddress:X4}"));
                continue;
            }

            var targetInstruction = instructions[targetIndex];

            instruction.SetOperand(0, targetInstruction);
        }

        // Synthesize the throw blocks deferred above, after all real instructions (so they are only
        // reachable via their branch, never by fall-through).
        var syntheticIndex = instructions.Count > 0 ? instructions[^1].Index + 1 : 1;

        foreach (var (jump, exception) in conditionalThrowsToSynthesize)
        {
            var throwBlock = new ISIL.Instruction(syntheticIndex++, ISIL.OpCode.Throw, exception);
            instructions.Add(throwBlock);
            jump.SetOperand(0, throwBlock);
        }

        return instructions;
    }

    /// <summary>
    /// The method occupies the half-open byte range [methodStart, methodStart + rawLength); the end is
    /// exclusive, i.e. the first byte past the method. An unconditional branch landing exactly on that
    /// end targets the following method - an external tail-branch (a tail call), not an internal jump.
    /// Deriving the end from the jumping instruction's own address (as was done previously) overshoots by
    /// the branch offset, classifying such thunks as internal jumps and leaving them as an unrecoverable
    /// Invalid instead of a tail call.
    /// </summary>
    internal static bool IsBranchTargetOutsideMethod(ulong methodStart, int rawLength, ulong target) =>
        target < methodStart || target >= methodStart + (ulong)rawLength;

    /// <summary>
    /// MSVC x86 compiles instance methods as thiscall, so an indirect call (function pointer /
    /// vtable entry) can pop its own stack arguments. Direct calls scan the callee with
    /// <see cref="TryScanRetArgumentCleanup"/>, but indirect targets are usually runtime-resolved
    /// and unscannable, leaving the tracked stack to drift (-4 per slot per execution) until the
    /// stack analyzer blows its visit limit or reports a non-empty exit stack. This pass looks at
    /// the call site instead: the caller-side add esp found after the call (possibly coalesced
    /// past later pushes and followed through unconditional jumps) covers the pushes it names,
    /// and any remaining uncovered slots were popped by the callee's ret N — a matching cleanup
    /// is emitted for just that remainder. Fully caller-cleaned (cdecl) sites are left untouched.
    /// </summary>
    internal static void AssumeIndirectCallCalleeCleanup(List<ISIL.Instruction> instructions, List<ulong> addresses)
    {
        // Jump operands are still raw target addresses here (fix-branches runs after this pass).
        var jumpTargets = new HashSet<ulong>();
        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is ISIL.OpCode.Jump or ISIL.OpCode.ConditionalJump && instruction.Operands[0] is ISIL.Immediate target)
                jumpTargets.Add(target.UnsignedValue);
        }

        for (var i = 0; i < instructions.Count; i++)
        {
            if (instructions[i].OpCode != ISIL.OpCode.IndirectCall)
                continue;

            // Outstanding arguments for this call: the contiguous push run immediately preceding
            // it. MSVC pushes args right before the call with loads and lea results interleaved;
            // a positive ShiftStack or a branch/call boundary means earlier pushes belong to a
            // previous call (possibly cleaned up), and a jump-target address is the start of
            // another block whose instructions must not be counted. A sub esp for locals and the
            // prologue's push ebp also lower to negative ShiftStacks but are not arguments: the
            // locals allocation is not paired with a store into the push slot, and the frame
            // setup (mov ebp,esp) directly follows the prologue push.
            var pushedBytes = CountPushedArgumentBytes(instructions, addresses, jumpTargets, i);

            if (pushedBytes <= 0)
                continue;

            // A caller-side cleanup may be coalesced far past this call (MSVC batches several
            // calls' pushes into one add esp, possibly after conditional jumps whose fall-through
            // still belongs to the same region), and the code after a call often ends with an
            // unconditional jump whose target holds the cleanup — follow jumps as well as the
            // flat fall-through order. The positive ShiftStacks found before the next call or
            // epilogue cover this call's pushes from the caller side (cdecl cleans all of them,
            // and mixed sites clean part of them while the callee's ret N pops the rest); only
            // the uncovered remainder can be callee-popped.
            var net = 0L;
            var callerCleans = false;
            var visited = new HashSet<int> { i };
            var cursor = i + 1;
            var budget = 64;
            while (cursor < instructions.Count && budget-- > 0 && visited.Add(cursor))
            {
                var next = instructions[cursor];

                if (next.OpCode is ISIL.OpCode.Return or ISIL.OpCode.IndirectJump)
                    break;

                if (next is { OpCode: ISIL.OpCode.ShiftStack, Operands: [ISIL.Immediate delta] })
                {
                    if (delta.Value > 0 && IsEpiloguePop(instructions, cursor))
                        break; // callee-saved register restores before a return, not arg cleanup

                    net += delta.Value;

                    if (net >= pushedBytes)
                    {
                        callerCleans = true;
                        break;
                    }
                }

                if (next.OpCode == ISIL.OpCode.Jump && next.Operands[0] is ISIL.Immediate target)
                {
                    var targetIndex = addresses.IndexOf(target.UnsignedValue);

                    if (targetIndex < 0)
                        break;

                    cursor = targetIndex; // continue scanning at the jump target
                    continue;
                }

                cursor++;
            }

            if (callerCleans)
                continue;

            var insertBytes = pushedBytes - (int)Math.Max(0, net); // caller-covered part is not ours to pop
            var callIndex = instructions[i].Index;
            var cleanupInstruction = new ISIL.Instruction(callIndex, ISIL.OpCode.ShiftStack, new ISIL.Immediate(insertBytes));
            instructions.Insert(i + 1, cleanupInstruction);
            addresses.Insert(i + 1, addresses[i]); // same IP as the call; fix-branches matches the first, i.e. the call itself
            i++; // continue scanning after the inserted instruction
        }
    }

    /// <summary>
    /// The size in bytes of the contiguous argument-push run immediately preceding the call at
    /// <paramref name="callIndex"/>, or 0 if there is none. MSVC pushes args right before the call
    /// with loads and lea results interleaved; a positive ShiftStack or a branch/call boundary means
    /// earlier pushes belong to a previous call (possibly cleaned up), and a jump-target address is
    /// the start of another block whose instructions must not be counted. A sub esp for locals and
    /// the prologue's push ebp also lower to negative ShiftStacks but are not arguments: the locals
    /// allocation is not paired with a store into the push slot, and the frame setup (mov ebp,esp)
    /// directly follows the prologue push.
    /// </summary>
    private static int CountPushedArgumentBytes(List<ISIL.Instruction> instructions, List<ulong> addresses, HashSet<ulong> jumpTargets, int callIndex)
    {
        var pushedBytes = 0;
        for (var j = callIndex - 1; j >= 0; j--)
        {
            var previous = instructions[j];

            if (previous is { OpCode: ISIL.OpCode.ShiftStack, Operands: [ISIL.Immediate delta] })
            {
                if (delta.Value >= 0)
                    break; // caller-side cleanup for earlier pushes

                // An argument push expands to (ShiftStack -4; Move stack[0], value); a bare
                // sub esp for locals has no paired store and ends the argument region.
                if (j + 1 >= instructions.Count
                    || instructions[j + 1] is not { OpCode: ISIL.OpCode.Move, Operands: [ISIL.StackOffset, _] })
                    break;

                pushedBytes += (int)-delta.Value;
            }
            else if (previous is { OpCode: ISIL.OpCode.Move, Operands: [ISIL.StackOffset, _] })
            {
                // the store into the just-pushed slot
            }
            else if (previous is { OpCode: ISIL.OpCode.Move, Operands: [_, ISIL.Register { Name: "rsp" }] })
            {
                break; // mov ebp,esp: everything before is the function prologue, not arguments
            }
            else if (previous.OpCode is ISIL.OpCode.Call or ISIL.OpCode.IndirectCall or ISIL.OpCode.Jump
                or ISIL.OpCode.ConditionalJump or ISIL.OpCode.Return or ISIL.OpCode.IndirectJump)
            {
                break;
            }

            // A jump to this address starts a block here, but the expansion of one native
            // instruction (ShiftStack + store) shares a single address — stop only after
            // the whole group is consumed so the push at the block start is still counted.
            if (jumpTargets.Contains(addresses[j]) && (j == 0 || addresses[j - 1] != addresses[j]))
                break; // start of this block: everything before belongs to other blocks
        }

        return pushedBytes;
    }

    /// <summary>
    /// Key functions are unmanaged il2cpp runtime entry points, so on x86 (stack-passing) their
    /// arguments arrive as the contiguous push run immediately before the call rather than through
    /// a managed signature for <c>ResolveForManaged</c> to lay out, and
    /// <c>ResolveForUnmanaged</c> keeps the call bare. Bare calls read none of the pushed slots, so
    /// dead-code elimination deletes the argument pushes before the metadata resolver runs and
    /// key-function recovery can never see the class, value or length the call was given. Attach
    /// the run as stack-slot operands — argument closest to the call sits at slot 0 — so the pushes
    /// stay live and the resolved arguments reach <c>KeyFunctionRecovery</c> / <c>ArrayRecovery</c>.
    /// A call with no visible push run keeps the bare layout.
    /// </summary>
    internal static void AttachKeyFunctionStackArguments(List<ISIL.Instruction> instructions, List<ulong> addresses, Func<ulong, bool> isKeyFunctionTarget)
    {
        // Jump operands are still raw target addresses here (fix-branches runs after this pass).
        var jumpTargets = new HashSet<ulong>();
        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is ISIL.OpCode.Jump or ISIL.OpCode.ConditionalJump && instruction.Operands[0] is ISIL.Immediate target)
                jumpTargets.Add(target.UnsignedValue);
        }

        for (var i = 0; i < instructions.Count; i++)
        {
            var call = instructions[i];

            // The bare unmanaged-call layout from ConvertInstructionStatement: target + return
            // register (Call) or target alone for void calls (CallVoid), which is how a registered
            // void stub registers the raiser call.
            if (call is not { OpCode: ISIL.OpCode.Call or ISIL.OpCode.CallVoid, Operands: [ISIL.Immediate dest, ..] })
                continue;

            if (!isKeyFunctionTarget(dest.UnsignedValue))
                continue;

            var pushedBytes = CountPushedArgumentBytes(instructions, addresses, jumpTargets, i);
            var argumentCount = pushedBytes / 4; // one stack slot per pointer on x86

            for (var slot = 0; slot < argumentCount; slot++)
                call.AddOperands([new ISIL.StackOffset(slot * 4)]);
        }
    }

    /// <summary>
    /// True when the positive ShiftStack at <paramref name="index"/> restores a callee-saved
    /// register in a function epilogue (pop reg; ...; ret) rather than cleaning up arguments:
    /// epilogue pops are always the second half of a (load from stack[0], ShiftStack +4) pop
    /// pair and are immediately followed by more pops ending in a Return.
    /// </summary>
    private static bool IsEpiloguePop(List<ISIL.Instruction> instructions, int index)
    {
        // A pop expands to (Move dest, stack[0]; ShiftStack +4) — a bare add esp is not preceded
        // by a stack read.
        if (index == 0 || instructions[index - 1] is not { OpCode: ISIL.OpCode.Move, Operands: [_, ISIL.StackOffset] })
            return false;

        var scanEnd = Math.Min(instructions.Count, index + 8);
        for (var k = index + 1; k < scanEnd; k++)
        {
            var op = instructions[k].OpCode;

            if (op == ISIL.OpCode.Return)
                return true;

            if (op is ISIL.OpCode.Call or ISIL.OpCode.IndirectCall or ISIL.OpCode.Jump or ISIL.OpCode.ConditionalJump)
                return false;
        }

        return false;
    }

    private static ISIL.Register? ReturnRegisterClobberedBy(MethodAnalysisContext callee)
        => callee.IsVoid ? CallingConventions.ReturnRegister(callee) : null;

    public override List<ISIL.IOperand> GetParameterOperandsFromMethod(MethodAnalysisContext context)
    {
        return CallingConventions.ResolveForManagedBody(context).ToList();
    }

    public override ulong GetThunkTarget(ApplicationAnalysisContext context, ulong thunkAddress)
    {
        var binary = context.Binary;

        if (!binary.TryMapVirtualAddressToRaw(thunkAddress, out var rawAddress))
            return 0;

        var raw = binary.GetRawBinaryContent();
        var length = (int)Math.Min(32, raw.Length - rawAddress);
        if (length <= 0)
            return 0;

        var decoder = Decoder.Create(binary.is32Bit ? 32 : 64, new ByteArrayCodeReader(raw.Slice((int)rawAddress, length).ToArray()), thunkAddress);
        
        for (var i = 0; i < 4; i++)
        {
            var instruction = decoder.Decode();

            if (instruction.FlowControl == FlowControl.UnconditionalBranch && instruction.Op0Kind is OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64)
                return instruction.NearBranchTarget;

            if (instruction.FlowControl != FlowControl.Next)
                return 0;
        }

        return 0;
    }

    public override ulong GetInternalCallTarget(MethodAnalysisContext method)
    {
        var start = GetPointerForMethod(method);
        var length = method.RawBytes.Length;

        if (start == 0 || length == 0)
            return 0;

        var decoder = Decoder.Create(method.AppContext.Binary.is32Bit ? 32 : 64, new ByteArrayCodeReader(method.RawBytes.ToArray()), start);
        var target = 0ul;

        while (decoder.IP < start + (ulong)length)
        {
            var instruction = decoder.Decode();

            if (instruction.FlowControl != FlowControl.UnconditionalBranch || instruction.Op0Kind is not (OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64))
                continue;

            var branch = instruction.NearBranchTarget;

            if (branch >= start && branch < start + (ulong)length)
                continue; // ordinary control flow within the stub

            if (target != 0 && target != branch)
                return 0;

            target = branch;
        }

        return target;
    }

    public override (IReadOnlyList<ulong> DataReferences, IReadOnlyList<ulong> CallTargets) InspectPotentialThrowHelper(ApplicationAnalysisContext context, ulong address)
    {
        Iced.Intel.InstructionList body;
        try
        {
            body = X86Utils.GetMethodBodyAtVirtAddressNew(address, true, context);
        }
        catch
        {
            return ([], []);
        }

        var dataReferences = new List<ulong>();
        var callTargets = new List<ulong>();

        foreach (var insn in body)
            ClassifyThrowHelperInstruction(insn, dataReferences, callTargets);

        return (dataReferences, callTargets);
    }

    // Separate from the body walk so the classification can be tested without a binary.
    // Handles both 64-bit (RIP-relative, rel64 branches) and 32-bit (absolute addresses,
    // rel32 branches and jump thunks) forms: 32-bit code refers to global data with
    // absolute immediates or absolute memory operands rather than IP-relative LEAs.
    internal static void ClassifyThrowHelperInstruction(Iced.Intel.Instruction insn, List<ulong> dataReferences, List<ulong> callTargets)
    {
        if (insn.Mnemonic == Mnemonic.Lea && insn.IsIPRelativeMemoryOperand)
        {
            dataReferences.Add(insn.IPRelativeMemoryAddress);
            return;
        }

        // Calls and jump-thunk tails, so a chain of helpers can be followed on either bitness.
        if (insn.Mnemonic is Mnemonic.Call or Mnemonic.Jmp && insn.Op0Kind is OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64)
        {
            callTargets.Add(insn.NearBranchTarget);
            return;
        }

        // Absolute global access, e.g. "push dword ptr [0x10402000]" loading a C-string pointer.
        if (insn.MemoryBase == Register.None && insn.MemoryIndex == Register.None && !insn.IsIPRelativeMemoryOperand && insn.MemoryDisplacement64 != 0)
        {
            dataReferences.Add(insn.MemoryDisplacement64);
            return;
        }

        // Immediate global pointers, e.g. "push offset str" (a 32-bit absolute address).
        if (insn.Op0Kind is OpKind.Immediate32 or OpKind.Immediate32to64 or OpKind.Immediate64)
            dataReferences.Add(insn.Immediate64);
        else if (insn.Op1Kind is OpKind.Immediate32 or OpKind.Immediate32to64 or OpKind.Immediate64)
            dataReferences.Add(insn.Immediate64);
    }

    internal List<ISIL.Instruction> GetIsilFromInstruction(Instruction instruction)
    {
        var instructions = new List<ISIL.Instruction>();
        ConvertInstructionStatement(instruction, instructions, [], null!);
        return instructions;
    }

    private void ConvertInstructionStatement(Instruction instruction, List<ISIL.Instruction> instructions, List<ulong> addresses, MethodAnalysisContext context)
    {
        var callNoReturn = false;
        int operandSize;

        ISIL.Instruction Add(ulong address, ISIL.OpCode opCode, params List<ISIL.IOperand> operands)
        {
            addresses.Add(address);
            var newInstruction = new ISIL.Instruction(instructions.Count, opCode, operands);
            instructions.Add(newInstruction);
            return newInstruction;
        }

        // Preserve all the argument registers as we don't know which ones are used
        void AddIndirectCall(Instruction source)
        {
            var call = Add(source.IP, ISIL.OpCode.IndirectCall, ConvertOperand(source, 0), new ISIL.Register(null, "rax") /* return value */);
            call.AddOperands(CallingConventions.ResolveForUnmanaged(context.AppContext, source.IP));
        }
        
        // Preserve all the argument registers as we don't know which ones are used
        void AddIndirectJmp(Instruction source)
        {
            var call = Add(source.IP, ISIL.OpCode.IndirectJump, ConvertOperand(source, 0), new ISIL.Register(null, "rax") /* return value */);
            call.AddOperands(CallingConventions.ResolveForUnmanaged(context.AppContext, source.IP));
        }

        switch (instruction.Mnemonic)
        {
            case Mnemonic.Mov:
            case Mnemonic.Movzx: // For all intents and purposes we don't care about zero-extending
            case Mnemonic.Movsx: // move with sign-extendign
            case Mnemonic.Movsxd: // same
            case Mnemonic.Movaps: // Movaps is basically just a mov but with the potential future detail that the size is dependent on reg size
            case Mnemonic.Movups: // Movaps but unaligned
            case Mnemonic.Movd: // Mov but specifically dword
            case Mnemonic.Movq: // Mov but specifically qword
            case Mnemonic.Movdqa: // Movaps but multiple integers at once in theory
            case Mnemonic.Cvtdq2ps: // Technically a convert double to single, but for analysis purposes we can just treat it as a move
            case Mnemonic.Cvtps2pd: // same, but float to double
            case Mnemonic.Cvtdq2pd: // int to double
            case Mnemonic.Cvtpd2ps: // double to float
            case Mnemonic.Cvttsd2si: // same, but double to integer
            case Mnemonic.Movdqu: // DEST[127:0] := SRC[127:0]
            case Mnemonic.Movlpd: // move low packed double (64-bit) — treat as a plain move
            case Mnemonic.Movhpd: // move high packed double — same
            case Mnemonic.Cvttss2si: // truncate float to int — treat as a move, conversion is implicit in the type
            case Mnemonic.Cvtsd2ss: // convert double to float — same
            case Mnemonic.Cvtss2sd: // convert float to double — same
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Movss: // scalar single - as a move, but a load from a constant address is a float literal
            case Mnemonic.Movsd: // scalar double
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertScalarFloatOperand(instruction, 1, instruction.Mnemonic == Mnemonic.Movss, context));
                break;
            case Mnemonic.Cbw: // AX := sign-extend AL
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, X86Utils.GetRegisterName(Register.AX)),
                    new ISIL.Register(null, X86Utils.GetRegisterName(Register.AL)));
                break;
            case Mnemonic.Cwde: // EAX := sign-extend AX
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, X86Utils.GetRegisterName(Register.EAX)),
                    new ISIL.Register(null, X86Utils.GetRegisterName(Register.AX)));
                break;
            case Mnemonic.Cdqe: // RAX := sign-extend EAX
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, X86Utils.GetRegisterName(Register.RAX)),
                    new ISIL.Register(null, X86Utils.GetRegisterName(Register.EAX)));
                break;
            case Mnemonic.Cwd: // DX:AX := sign-extend AX
                Add(instruction.IP, ISIL.OpCode.ShiftRight, new ISIL.Register(null, X86Utils.GetRegisterName(Register.DX)),
                    new ISIL.Register(null, X86Utils.GetRegisterName(Register.AX)), Imm(15));
                break;
            case Mnemonic.Cdq: // EDX:EAX := sign-extend EAX
                Add(instruction.IP, ISIL.OpCode.ShiftRight, new ISIL.Register(null, X86Utils.GetRegisterName(Register.EDX)),
                    new ISIL.Register(null, X86Utils.GetRegisterName(Register.EAX)), Imm(31));
                break;
            case Mnemonic.Cqo: // RDX:RAX := sign-extend RAX
                Add(instruction.IP, ISIL.OpCode.ShiftRight, new ISIL.Register(null, X86Utils.GetRegisterName(Register.RDX)),
                    new ISIL.Register(null, X86Utils.GetRegisterName(Register.RAX)), Imm(63));
                break;
            case Mnemonic.Lea:
                var destination = ConvertOperand(instruction, 0);

                // RIP-relative LEA is effectively loading the absolute address.
                if (instruction.IsIPRelativeMemoryOperand)
                {
                    Add(instruction.IP, ISIL.OpCode.Move, destination, Imm((long)instruction.IPRelativeMemoryAddress));
                    return;
                }

                // Stack-address LEA keeps stack semantics represented as address-of stack slot.
                if (instruction.MemoryIndex == Register.None && instruction.MemoryBase.GetFullRegister() == Register.RSP)
                {
                    Add(instruction.IP, ISIL.OpCode.Move, destination, ConvertOperand(instruction, 1, true));
                    return;
                }

                // Absolute-address LEA also computes a value rather than loading from memory.
                if (instruction.MemoryBase == Register.None && instruction.MemoryIndex == Register.None)
                {
                    Add(instruction.IP, ISIL.OpCode.Move, destination, Imm((long)instruction.MemoryDisplacement64));
                    return;
                }

                if (instruction.MemoryIndex != Register.None)
                {
                    ISIL.IOperand? baseRegister = instruction.MemoryBase != Register.None
                        ? new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryBase))
                        : null;
                    var indexRegister = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryIndex));
                    var source = (ISIL.IOperand)indexRegister;

                    if (instruction.MemoryIndexScale > 1)
                    {
                        if (baseRegister != null)
                        {
                            var temp = new ISIL.Register(null, "TEMP");
                            Add(instruction.IP, ISIL.OpCode.Multiply, temp, indexRegister, Imm(instruction.MemoryIndexScale));
                            source = temp;
                        }
                        else
                        {
                            Add(instruction.IP, ISIL.OpCode.Multiply, destination, indexRegister, Imm(instruction.MemoryIndexScale));
                            source = destination;
                        }
                    }

                    if (baseRegister != null)
                        Add(instruction.IP, ISIL.OpCode.Add, destination, baseRegister, source);
                    else if (!ReferenceEquals(source, destination))
                        Add(instruction.IP, ISIL.OpCode.Move, destination, source);

                    var displacement = unchecked((long)instruction.MemoryDisplacement64);
                    if (displacement > 0)
                        Add(instruction.IP, ISIL.OpCode.Add, destination, destination, Imm(displacement));
                    else if (displacement < 0)
                        Add(instruction.IP, ISIL.OpCode.Subtract, destination, destination, Imm(-displacement));

                    return;
                }

                if (instruction.MemoryBase != Register.None && instruction.MemoryBase.GetFullRegister() != Register.RSP)
                {
                    var baseRegister = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryBase));
                    var displacement = unchecked((long)instruction.MemoryDisplacement64);

                    if (displacement == 0)
                        Add(instruction.IP, ISIL.OpCode.Move, destination, baseRegister);
                    else if (displacement > 0)
                        Add(instruction.IP, ISIL.OpCode.Add, destination, baseRegister, Imm(displacement));
                    else
                        Add(instruction.IP, ISIL.OpCode.Subtract, destination, baseRegister, Imm(-displacement));

                    return;
                }

                Add(instruction.IP, ISIL.OpCode.Move, destination, ConvertOperand(instruction, 1, true));
                break;
            case Mnemonic.Xor:
            case Mnemonic.Xorps: //xorps is just floating point xor
                if (instruction.Op0Kind == OpKind.Register && instruction.Op1Kind == OpKind.Register && instruction.Op0Register == instruction.Op1Register)
                    Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), Imm(0));
                else
                    Add(instruction.IP, ISIL.OpCode.Xor, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Shl: // unsigned shift
            case Mnemonic.Sal: // signed shift
                Add(instruction.IP, ISIL.OpCode.ShiftLeft, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Shld: // double-precision shift left: dest = (dest << count) | (src >> (size - count))
                // Approximate as a plain left shift of dest; the fill-from-src part is rarely load-bearing in IL-recovered code.
                Add(instruction.IP, ISIL.OpCode.ShiftLeft, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 2));
                break;
            case Mnemonic.Shrd: // double-precision shift right: dest = (dest >> count) | (src << (size - count))
                // Approximate as a plain right shift of dest, mirroring the Shld handling above.
                Add(instruction.IP, ISIL.OpCode.ShiftRight, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 2));
                break;
            case Mnemonic.Rol: // rotate left: dest = (dest << count) | (dest >> (size - count))
            case Mnemonic.Ror: // rotate right
                {
                    var rotDest = ConvertOperand(instruction, 0);
                    var rotCount = ConvertOperand(instruction, 1);
                    var rotWidth = (instruction.Op0Kind == OpKind.Register ? instruction.Op0Register.GetSize() : instruction.MemorySize.GetSize()) * 8;
                    var rotLeft = new ISIL.Register(null, "TEMP");
                    var rotRight = new ISIL.Register(null, "TEMP2");
                    var rotInvCount = new ISIL.Register(null, "TEMP3");

                    Add(instruction.IP, ISIL.OpCode.Subtract, rotInvCount, Imm(rotWidth), rotCount);

                    if (instruction.Mnemonic == Mnemonic.Rol)
                    {
                        Add(instruction.IP, ISIL.OpCode.ShiftLeft, rotLeft, rotDest, rotCount);
                        Add(instruction.IP, ISIL.OpCode.ShiftRight, rotRight, rotDest, rotInvCount);
                    }
                    else
                    {
                        Add(instruction.IP, ISIL.OpCode.ShiftRight, rotRight, rotDest, rotCount);
                        Add(instruction.IP, ISIL.OpCode.ShiftLeft, rotLeft, rotDest, rotInvCount);
                    }

                    Add(instruction.IP, ISIL.OpCode.Or, rotDest, rotLeft, rotRight);
                    break;
                }
            case Mnemonic.Bswap: // byte-swap - no ISIL opcode models this; the surrounding code is usually a hash/checksum loop we can't recover faithfully anyway.
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Shr: // unsigned shift
            case Mnemonic.Sar: // signed shift
                Add(instruction.IP, ISIL.OpCode.ShiftRight, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.And:
            case Mnemonic.Andps: //Floating point and
                Add(instruction.IP, ISIL.OpCode.And, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Or:
            case Mnemonic.Orps: //Floating point or
                Add(instruction.IP, ISIL.OpCode.Or, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Bts: // CF = old bit, then set it
                {
                    var dest = ConvertOperand(instruction, 0);
                    var bit = ConvertOperand(instruction, 1);
                    var temp = new ISIL.Register(null, "TEMP");
                    Add(instruction.IP, ISIL.OpCode.ShiftRight, temp, dest, bit);
                    Add(instruction.IP, ISIL.OpCode.And, new ISIL.Register(null, "CF"), temp, Imm(1));
                    Add(instruction.IP, ISIL.OpCode.ShiftLeft, temp, Imm(1), bit);
                    Add(instruction.IP, ISIL.OpCode.Or, dest, dest, temp);
                    break;
                }
            case Mnemonic.Btr: // CF = old bit, then clear it
                {
                    var dest = ConvertOperand(instruction, 0);
                    var bit = ConvertOperand(instruction, 1);
                    var temp = new ISIL.Register(null, "TEMP");
                    Add(instruction.IP, ISIL.OpCode.ShiftRight, temp, dest, bit);
                    Add(instruction.IP, ISIL.OpCode.And, new ISIL.Register(null, "CF"), temp, Imm(1));
                    Add(instruction.IP, ISIL.OpCode.ShiftLeft, temp, Imm(1), bit);
                    Add(instruction.IP, ISIL.OpCode.Not, temp, temp); // temp = ~(1 << bit)
                    Add(instruction.IP, ISIL.OpCode.And, dest, dest, temp);
                    break;
                }
            case Mnemonic.Btc: // CF = old bit, then flip it
                {
                    var dest = ConvertOperand(instruction, 0);
                    var bit = ConvertOperand(instruction, 1);
                    var temp = new ISIL.Register(null, "TEMP");
                    Add(instruction.IP, ISIL.OpCode.ShiftRight, temp, dest, bit);
                    Add(instruction.IP, ISIL.OpCode.And, new ISIL.Register(null, "CF"), temp, Imm(1));
                    Add(instruction.IP, ISIL.OpCode.ShiftLeft, temp, Imm(1), bit);
                    Add(instruction.IP, ISIL.OpCode.Xor, dest, dest, temp);
                    break;
                }
            case Mnemonic.Not:
                Add(instruction.IP, ISIL.OpCode.Not, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Neg: // dest := -dest
                Add(instruction.IP, ISIL.OpCode.Negate, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Imul:
                if (instruction.OpCount == 1)
                {
                    int opSize = instruction.Op0Kind == OpKind.Register ? instruction.Op0Register.GetSize() : instruction.MemorySize.GetSize();
                    switch (opSize) // one-operand form: result is a double-width value in D:A; we keep only the low half in A
                    {
                        case 1: // Op0 * AL -> AX
                            Add(instruction.IP, ISIL.OpCode.Multiply, Register.AX.MakeIndependent(), ConvertOperand(instruction, 0), Register.AL.MakeIndependent());
                            return;
                        case 2: // Op0 * AX -> DX:AX
                            Add(instruction.IP, ISIL.OpCode.Multiply, new ISIL.Register(null, X86Utils.GetRegisterName(Register.AX)), ConvertOperand(instruction, 0), new ISIL.Register(null, X86Utils.GetRegisterName(Register.AX)));
                            return;
                        case 4: // Op0 * EAX -> EDX:EAX
                            Add(instruction.IP, ISIL.OpCode.Multiply, new ISIL.Register(null, X86Utils.GetRegisterName(Register.EAX)), ConvertOperand(instruction, 0), new ISIL.Register(null, X86Utils.GetRegisterName(Register.EAX)));
                            return;
                        case 8: // Op0 * RAX -> RDX:RAX
                            Add(instruction.IP, ISIL.OpCode.Multiply, new ISIL.Register(null, X86Utils.GetRegisterName(Register.RAX)), ConvertOperand(instruction, 0), new ISIL.Register(null, X86Utils.GetRegisterName(Register.RAX)));
                            return;
                        default:
                            break;
                    }

                    // if got to here, it didn't work
                    goto default;
                }
                else if (instruction.OpCount == 3) Add(instruction.IP, ISIL.OpCode.Multiply, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                else Add(instruction.IP, ISIL.OpCode.Multiply, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));

                break;
            case Mnemonic.Mul: // unsigned one-operand form: result in D:A, keep only low half in A
                {
                    var mulSize = instruction.Op0Kind == OpKind.Register ? instruction.Op0Register.GetSize() : instruction.MemorySize.GetSize();
                    ISIL.IOperand? mulAcc = mulSize switch
                    {
                        1 => new ISIL.Register(null, X86Utils.GetRegisterName(Register.AL)),
                        2 => new ISIL.Register(null, X86Utils.GetRegisterName(Register.AX)),
                        4 => new ISIL.Register(null, X86Utils.GetRegisterName(Register.EAX)),
                        8 => new ISIL.Register(null, X86Utils.GetRegisterName(Register.RAX)),
                        _ => null
                    };
                    if (mulAcc == null)
                        goto default;
                    Add(instruction.IP, ISIL.OpCode.Multiply, mulAcc, ConvertOperand(instruction, 0), mulAcc);
                    break;
                }
            case Mnemonic.Idiv:
            case Mnemonic.Div:
                {
                    var divisorSize = instruction.Op0Kind == OpKind.Register ? instruction.Op0Register.GetSize() : instruction.MemorySize.GetSize();

                    // the 8-bit form puts the remainder in AH, which we can't deal with
                    if (divisorSize is not (2 or 4 or 8))
                        goto default;

                    // The real dividend is the D:A register pair, but every compiler sets D up with cdq/cqo or
                    // an xor immediately beforehand, so in reality it's just rax
                    var quotient = new ISIL.Register(null, X86Utils.GetRegisterName(Register.RAX));
                    var remainder = new ISIL.Register(null, X86Utils.GetRegisterName(Register.RDX));

                    var dividend = new ISIL.Register(null, "TEMP_DIVIDEND");
                    var divisor = new ISIL.Register(null, "TEMP_DIVISOR");

                    Add(instruction.IP, ISIL.OpCode.Move, dividend, quotient);
                    Add(instruction.IP, ISIL.OpCode.Move, divisor, ConvertOperand(instruction, 0));
                    Add(instruction.IP, ISIL.OpCode.Divide, quotient, dividend, divisor);
                    Add(instruction.IP, ISIL.OpCode.Modulo, remainder, dividend, divisor);
                    break;
                }
            case Mnemonic.Mulss:
            case Mnemonic.Vmulss:
            case Mnemonic.Mulsd: // double-precision variants
                if (instruction.OpCount == 3)
                    Add(instruction.IP, ISIL.OpCode.Multiply, ConvertOperand(instruction, 0), ConvertScalarFloatOperand(instruction, 1, instruction.Mnemonic is Mnemonic.Mulss or Mnemonic.Vmulss, context), ConvertScalarFloatOperand(instruction, 2, instruction.Mnemonic is Mnemonic.Mulss or Mnemonic.Vmulss, context));
                else if (instruction.OpCount == 2)
                    Add(instruction.IP, ISIL.OpCode.Multiply, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertScalarFloatOperand(instruction, 1, instruction.Mnemonic is Mnemonic.Mulss or Mnemonic.Vmulss, context));
                else
                    goto default;

                break;

            case Mnemonic.Divss: // Divide Scalar Single Precision Floating-Point Values. DEST[31:0] = DEST[31:0] / SRC[31:0]
            case Mnemonic.Divsd: // double-precision variant
                Add(instruction.IP, ISIL.OpCode.Divide, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertScalarFloatOperand(instruction, 1, instruction.Mnemonic == Mnemonic.Divss, context));
                break;
            case Mnemonic.Vdivss: // VEX Divide Scalar Single Precision Floating-Point Values. DEST[31:0] = SRC1[31:0] / SRC2[31:0]
                Add(instruction.IP, ISIL.OpCode.Divide, ConvertOperand(instruction, 0), ConvertScalarFloatOperand(instruction, 1, true, context), ConvertScalarFloatOperand(instruction, 2, true, context));
                break;

            case Mnemonic.Ret:
                // TODO: Verify correctness of operation with Vectors.

                // On x32, this will require better engineering since ulongs are handled somehow differently (return in 2 registers, I think?)
                // The x64 prototype should work.
                // Are st* registers even used in il2cpp games?

                if (context.IsVoid)
                    Add(instruction.IP, ISIL.OpCode.Return);
                else if (context.Definition?.RawReturnType?.Type is Il2CppTypeEnum.IL2CPP_TYPE_R4 or Il2CppTypeEnum.IL2CPP_TYPE_R8)
                    Add(instruction.IP, ISIL.OpCode.Return, new ISIL.Register(null, "xmm0"));
                else
                    Add(instruction.IP, ISIL.OpCode.Return, new ISIL.Register(null, "rax"));
                break;
            case Mnemonic.Push:
                operandSize = GetStackAccessSize(instruction);
                Add(instruction.IP, ISIL.OpCode.ShiftStack, Imm(-operandSize));
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.StackOffset(0), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Pop:
                operandSize = GetStackAccessSize(instruction);
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), new ISIL.StackOffset(0));
                Add(instruction.IP, ISIL.OpCode.ShiftStack, Imm(operandSize));
                break;
            case Mnemonic.Sub:
            case Mnemonic.Add:
                var isSubtract = instruction.Mnemonic == Mnemonic.Sub;

                // Special case - stack shift
                if (TryGetImmediateStackAdjustment(instruction, out var stackShift))
                {
                    Add(instruction.IP, ISIL.OpCode.ShiftStack, Imm(stackShift));
                    break;
                }

                var left = ConvertOperand(instruction, 0);
                var right = ConvertOperand(instruction, 1);
                if (isSubtract)
                    Add(instruction.IP, ISIL.OpCode.Subtract, left, left, right);
                else
                    Add(instruction.IP, ISIL.OpCode.Add, left, left, right);

                break;
            case Mnemonic.Adc: // dest = dest + src + CF
                {
                    var adcDest = ConvertOperand(instruction, 0);
                    var adcSrc = ConvertOperand(instruction, 1);
                    var adcTemp = new ISIL.Register(null, "TEMP");
                    Add(instruction.IP, ISIL.OpCode.Add, adcTemp, adcDest, adcSrc);
                    Add(instruction.IP, ISIL.OpCode.Add, adcDest, adcTemp, new ISIL.Register(null, "CF"));
                    break;
                }
            case Mnemonic.Sbb: // dest = dest - src - CF
                {
                    var sbbDest = ConvertOperand(instruction, 0);
                    var sbbSrc = ConvertOperand(instruction, 1);
                    var sbbTemp = new ISIL.Register(null, "TEMP");
                    Add(instruction.IP, ISIL.OpCode.Subtract, sbbTemp, sbbDest, sbbSrc);
                    Add(instruction.IP, ISIL.OpCode.Subtract, sbbDest, sbbTemp, new ISIL.Register(null, "CF"));
                    break;
                }
            case Mnemonic.Addss:
            case Mnemonic.Subss:
            case Mnemonic.Addsd: // double-precision variants — same logic, just not single
            case Mnemonic.Subsd:
                {
                    // Addss and subss are just floating point add/sub, but we don't need to handle the stack stuff
                    // But we do need to handle 2 vs 3 operand forms
                    var isSingle = instruction.Mnemonic is Mnemonic.Addss or Mnemonic.Subss;
                    ISIL.IOperand dest;
                    ISIL.IOperand src1;
                    ISIL.IOperand src2;

                    if (instruction.OpCount == 3)
                    {
                        //dest, src1, src2
                        dest = ConvertOperand(instruction, 0);
                        src1 = ConvertScalarFloatOperand(instruction, 1, isSingle, context);
                        src2 = ConvertScalarFloatOperand(instruction, 2, isSingle, context);
                    }
                    else if (instruction.OpCount == 2)
                    {
                        //DestAndSrc1, Src2
                        dest = ConvertOperand(instruction, 0);
                        src1 = dest;
                        src2 = ConvertScalarFloatOperand(instruction, 1, isSingle, context);
                    }
                    else
                        goto default;

                    if (instruction.Mnemonic is Mnemonic.Subss or Mnemonic.Subsd)
                        Add(instruction.IP, ISIL.OpCode.Subtract, dest, src1, src2);
                    else
                        Add(instruction.IP, ISIL.OpCode.Add, dest, src1, src2);
                    break;
                }
            // The following pair of instructions does not update the Carry Flag (CF):
            case Mnemonic.Dec:
                Add(instruction.IP, ISIL.OpCode.Subtract, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), Imm(1));
                break;
            case Mnemonic.Inc:
                Add(instruction.IP, ISIL.OpCode.Add, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), Imm(1));
                break;

            case Mnemonic.Shufps: // Packed Interleave Shuffle of Quadruplets of Single Precision Floating-Point Values
                {
                    if (instruction.Op1Kind == OpKind.Memory)
                        goto default;

                    var imm = instruction.Immediate8;
                    var src1 = X86Utils.GetRegisterName(instruction.Op0Register);
                    var src2 = X86Utils.GetRegisterName(instruction.Op1Register);

                    // Element selection
                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, "XMM_TEMP" + "_0"),
                        new ISIL.Register(null, $"{src1}_{imm & 0b11}"));

                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, "XMM_TEMP" + "_1"),
                        new ISIL.Register(null, $"{src1}_{(imm >> 2) & 0b11}"));

                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, "XMM_TEMP" + "_2"),
                        new ISIL.Register(null, $"{src2}_{(imm >> 4) & 0b11}"));

                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, "XMM_TEMP" + "_3"),
                        new ISIL.Register(null, $"{src2}_{(imm >> 6) & 0b11}"));

                    Add(instruction.IP, ISIL.OpCode.Move,
                        ConvertOperand(instruction, 0),
                        new ISIL.Register(null, "XMM_TEMP"));

                    break;
                }

            case Mnemonic.Unpcklps: // Unpack and Interleave Low Packed Single Precision Floating-Point Values
                {
                    if (instruction.Op1Kind == OpKind.Memory)
                        goto default;

                    var src1 = X86Utils.GetRegisterName(instruction.Op0Register);
                    var src2 = X86Utils.GetRegisterName(instruction.Op1Register);

                    // Interleaving lanes
                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, (string?)"XMM_TEMP" + "_0"),
                        new ISIL.Register(null, $"{src1}_0")); // SRC1[31:0]

                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, (string?)"XMM_TEMP" + "_1"),
                        new ISIL.Register(null, $"{src2}_0")); // SRC2[31:0]

                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, (string?)"XMM_TEMP" + "_2"),
                        new ISIL.Register(null, $"{src1}_1")); // SRC1[63:32]

                    Add(instruction.IP, ISIL.OpCode.Move,
                        new ISIL.Register(null, (string?)"XMM_TEMP" + "_3"),
                        new ISIL.Register(null, $"{src2}_1")); // SRC2[63:32]

                    Add(instruction.IP, ISIL.OpCode.Move,
                        ConvertOperand(instruction, 0),
                        new ISIL.Register(null, (string?)"XMM_TEMP"));

                    break;
                }

            case Mnemonic.Call:
                // We don't try and resolve which method is being called, but we do need to know how many parameters it has
                // I would hope that all of these methods have the same number of arguments, else how can they be inlined?

                var target = instruction.NearBranchTarget;

                if (instruction.Op0Kind == OpKind.Register || instruction.Op0Kind == OpKind.Memory)
                {
                    AddIndirectCall(instruction);
                }
                else if (context.AppContext.MethodsByAddress.TryGetValue(target, out var possibleMethods))
                {
                    if (possibleMethods.Count == 1)
                    {
                        ISIL.Instruction call;

                        if (possibleMethods[0].IsVoid)
                            call = Add(instruction.IP, ISIL.OpCode.CallVoid, Imm(target));
                        else
                            call = Add(instruction.IP, ISIL.OpCode.Call, Imm(target), CallingConventions.ReturnRegister(possibleMethods[0]));

                        call.AddOperands(CallingConventions.ResolveForManaged(possibleMethods[0]));
                        call.ImplicitDefinition = ReturnRegisterClobberedBy(possibleMethods[0]);
                    }
                    else
                    {
                        MethodAnalysisContext ctx = null!;
                        var lpars = -1;

                        // Very naive approach, folds with structs in parameters if GCC is used:
                        foreach (var method in possibleMethods)
                        {
                            var pars = method.Parameters.Count;
                            if (method.IsStatic) pars++;
                            if (pars > lpars)
                            {
                                lpars = pars;
                                ctx = method;
                            }
                        }

                        // On post-analysis, you can discard methods according to the registers used, see CallingConventions.
                        // This is less effective on GCC because MSVC doesn't overlap registers.

                        ISIL.Instruction call;

                        if (ctx.IsVoid)
                            call = Add(instruction.IP, ISIL.OpCode.CallVoid, Imm(target));
                        else
                            call = Add(instruction.IP, ISIL.OpCode.Call, Imm(target), CallingConventions.ReturnRegister(ctx));

                        call.AddOperands(CallingConventions.ResolveForManaged(ctx));
                        call.ImplicitDefinition = ReturnRegisterClobberedBy(ctx);
                    }
                }
                else
                {
                    // This isn't a managed method, so for now we don't know its parameter count.
                    // This will need to be rewritten if we ever stumble upon an unmanaged method that accepts more than 4 parameters.
                    // These can be converted to dedicated ISIL instructions for specific API functions at a later stage. (by a post-processing step)

                    var call = Add(instruction.IP, ISIL.OpCode.Call, Imm(target), new ISIL.Register(null, "rax") /* return value */);
                    call.AddOperands(CallingConventions.ResolveForUnmanaged(context.AppContext, target));
                }

                // Callee-cleanup conventions (x86 stdcall / thiscall) pop the stack arguments inside the callee,
                // so the caller never emits a matching cleanup. Account for that after the call so loops around
                // such calls don't drift the tracked stack size. Direct calls only - for indirect calls the
                // callee's convention is unknown, which keeps the previous (caller-only) behaviour.
                if (instruction.Op0Kind is OpKind.NearBranch16 or OpKind.NearBranch32 or OpKind.NearBranch64)
                {
                    var argumentCleanup = GetCalleeArgumentCleanup(context, target);

                    if (argumentCleanup is > 0)
                        Add(instruction.IP, ISIL.OpCode.ShiftStack, Imm(argumentCleanup.Value));
                }

                if (callNoReturn)
                {
                    // Our function decided to jump into a thunk or do a funny return.
                    // We will insert a return after the call.
                    // According to common sense, such callee must have the same return value as the caller, unless it's __noreturn.
                    // I hope someone else will catch up on this and figure out non-returning functions.

                    // TODO: Determine whether a function is an actual thunk and it's *technically better* to duplicate code for it, or if it's a regular retcall.
                    // Basic implementation may use context.AppContext.MethodsByAddress, but this doesn't catch thunks only.
                    // For example, SWDT often calls gc::GarbageCollector::SetWriteBarrier through a long jmp chain. That's a whole function, not just a thunk.

                    goto case Mnemonic.Ret;
                }

                break;
            case Mnemonic.Test:
                if (instruction.Op0Kind == OpKind.Register && instruction.Op1Kind == OpKind.Register && instruction.Op0Register == instruction.Op1Register)
                {
                    AddCompareInstruction(instruction.IP, ConvertOperand(instruction, 0), Imm(0));
                    break;
                }
                AddTestInstruction(instruction.IP, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Cmp:
                AddCompareInstruction(instruction.IP, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Comiss: //comiss is just a floating point compare dest[31:0] == src[31:0]
            case Mnemonic.Ucomiss: // same, but unsigned
            case Mnemonic.Comisd: // double-precision compare
            case Mnemonic.Ucomisd: // same, but unsigned
                AddCompareInstruction(instruction.IP, ConvertOperand(instruction, 0), ConvertScalarFloatOperand(instruction, 1, instruction.Mnemonic is Mnemonic.Comiss or Mnemonic.Ucomiss, context));
                break;

            case Mnemonic.Cmove: // move if condition
            case Mnemonic.Cmovne:
            case Mnemonic.Cmova:
            case Mnemonic.Cmovg:
            case Mnemonic.Cmovae:
            case Mnemonic.Cmovge:
            case Mnemonic.Cmovb:
            case Mnemonic.Cmovl:
            case Mnemonic.Cmovbe:
            case Mnemonic.Cmovle:
            case Mnemonic.Cmovs:
            case Mnemonic.Cmovns:
                switch (instruction.Mnemonic)
                {
                    case Mnemonic.Cmove: // equals
                        Add(instruction.IP, ISIL.OpCode.Not, new ISIL.Register(null, "TEMP"), new ISIL.Register(null, "ZF")); // TEMP = !ZF
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), new ISIL.Register(null, "TEMP")); // skip if not eq
                        break;
                    case Mnemonic.Cmovne: // not equals
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), new ISIL.Register(null, "ZF")); // skip if eq
                        break;
                    case Mnemonic.Cmovs: // sign
                        Add(instruction.IP, ISIL.OpCode.Not, new ISIL.Register(null, "TEMP"), new ISIL.Register(null, "SF")); // TEMP = !SF
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), new ISIL.Register(null, "TEMP")); // skip if not sign
                        break;
                    case Mnemonic.Cmovns: // not sign
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), new ISIL.Register(null, "SF")); // skip if sign
                        break;
                    case Mnemonic.Cmova:
                    case Mnemonic.Cmovg: // greater
                        var temp = new ISIL.Register(null, "TEMP");
                        Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                        Add(instruction.IP, ISIL.OpCode.Not, temp, temp); // TEMP = !TEMP
                        Add(instruction.IP, ISIL.OpCode.Or, temp, temp, new ISIL.Register(null, "ZF")); // TEMP = TEMP || ZF
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), temp); // skip if not gt
                        break;
                    case Mnemonic.Cmovae:
                    case Mnemonic.Cmovge: // greater or eq
                        temp = new ISIL.Register(null, "TEMP");
                        Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                        Add(instruction.IP, ISIL.OpCode.Not, temp, temp); // TEMP = !TEMP
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), temp); // skip if not gt or eq
                        break;
                    case Mnemonic.Cmovb:
                    case Mnemonic.Cmovl: // less
                        temp = new ISIL.Register(null, "TEMP");
                        Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), temp); // skip if not lt
                        break;
                    case Mnemonic.Cmovbe:
                    case Mnemonic.Cmovle: // less or eq
                        temp = new ISIL.Register(null, "TEMP");
                        var temp2 = new ISIL.Register(null, "TEMP2");
                        Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                        Add(instruction.IP, ISIL.OpCode.Not, temp2, new ISIL.Register(null, "ZF")); // TEMP2 = !ZF
                        Add(instruction.IP, ISIL.OpCode.And, temp, temp, temp2); // TEMP = TEMP && TEMP2
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), temp); // skip if not lt or eq
                        break;
                }
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)); // set if cond
                Add(instruction.IP + 1, ISIL.OpCode.Nop);
                break;

            // Convert a flag condition into the (byte) destination as 0/1, mirroring the Cmov conditions.
            case Mnemonic.Sete: // ZF
            case Mnemonic.Setne: // !ZF
            case Mnemonic.Seta: // above: !CF && !ZF
            case Mnemonic.Setae: // above or equal: !CF
            case Mnemonic.Setb: // below: CF
            case Mnemonic.Setbe: // below or equal: CF || ZF
            case Mnemonic.Setg: // greater: !ZF && SF == OF
            case Mnemonic.Setge: // greater or equal: SF == OF
            case Mnemonic.Setl: // less: SF != OF
            case Mnemonic.Setle: // less or equal: ZF || SF != OF
            case Mnemonic.Sets: // SF
            case Mnemonic.Setns: // !SF
                {
                    var dest = ConvertOperand(instruction, 0);
                    var cf = new ISIL.Register(null, "CF");
                    var zf = new ISIL.Register(null, "ZF");
                    var sf = new ISIL.Register(null, "SF");
                    var of = new ISIL.Register(null, "OF");
                    var temp = new ISIL.Register(null, "TEMP");

                    switch (instruction.Mnemonic)
                    {
                        case Mnemonic.Sete:
                            Add(instruction.IP, ISIL.OpCode.Move, dest, zf);
                            break;
                        case Mnemonic.Setne:
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, dest, zf, Imm(0));
                            break;
                        case Mnemonic.Setb:
                            Add(instruction.IP, ISIL.OpCode.Move, dest, cf);
                            break;
                        case Mnemonic.Setae:
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, dest, cf, Imm(0));
                            break;
                        case Mnemonic.Seta:
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, cf, Imm(0)); // TEMP = !CF
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, dest, zf, Imm(0)); // dest = !ZF
                            Add(instruction.IP, ISIL.OpCode.And, dest, dest, temp); // dest = !CF && !ZF
                            break;
                        case Mnemonic.Setbe:
                            Add(instruction.IP, ISIL.OpCode.Or, dest, cf, zf); // dest = CF || ZF
                            break;
                        case Mnemonic.Sets:
                            Add(instruction.IP, ISIL.OpCode.Move, dest, sf);
                            break;
                        case Mnemonic.Setns:
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, dest, sf, Imm(0));
                            break;
                        case Mnemonic.Setge:
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, dest, sf, of); // dest = SF == OF
                            break;
                        case Mnemonic.Setl:
                            Add(instruction.IP, ISIL.OpCode.CheckNotEqual, dest, sf, of); // dest = SF != OF
                            break;
                        case Mnemonic.Setg:
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, sf, of); // TEMP = SF == OF
                            Add(instruction.IP, ISIL.OpCode.CheckEqual, dest, zf, Imm(0)); // dest = !ZF
                            Add(instruction.IP, ISIL.OpCode.And, dest, dest, temp); // dest = !ZF && SF == OF
                            break;
                        case Mnemonic.Setle:
                            Add(instruction.IP, ISIL.OpCode.CheckNotEqual, temp, sf, of); // TEMP = SF != OF
                            Add(instruction.IP, ISIL.OpCode.Or, dest, temp, zf); // dest = ZF || SF != OF
                            break;
                    }
                    break;
                }

            case Mnemonic.Maxss: // dest < src ? src : dest
            case Mnemonic.Maxsd: // scalar double-precision variant
            case Mnemonic.Minss: // dest > src ? src : dest
            case Mnemonic.Minsd: // scalar double-precision variant
                {
                    var dest = ConvertOperand(instruction, 0);
                    var src = ConvertOperand(instruction, 1);
                    AddCompareInstruction(instruction.IP, dest, src); // compare dest & src
                    if (instruction.Mnemonic is Mnemonic.Maxss or Mnemonic.Maxsd)
                    {
                        var temp = new ISIL.Register(null, "TEMP");
                        Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), temp); // enter if dest < src
                    }
                    else
                    {
                        var temp = new ISIL.Register(null, "TEMP");
                        Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                        Add(instruction.IP, ISIL.OpCode.Not, temp, temp); // TEMP = !TEMP
                        Add(instruction.IP, ISIL.OpCode.Or, temp, temp, new ISIL.Register(null, "ZF")); // TEMP = TEMP || ZF
                        Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), temp); // enter if dest > src
                    }

                    Add(instruction.IP, ISIL.OpCode.Move, dest, src); // dest = src
                    Add(instruction.IP + 1, ISIL.OpCode.Nop); // exit for IF
                    break;
                }

            case Mnemonic.Cmpxchg: // compare and exchange
                {
                    var accumulator = new ISIL.Register(null, instruction.Op1Register.GetSize() switch
                    {
                        8 => X86Utils.GetRegisterName(Register.RAX),
                        4 => X86Utils.GetRegisterName(Register.EAX),
                        2 => X86Utils.GetRegisterName(Register.AX),
                        1 => X86Utils.GetRegisterName(Register.AL),
                        _ => throw new NotSupportedException("unexpected behavior")
                    });
                    var dest = ConvertOperand(instruction, 0);
                    var src = ConvertOperand(instruction, 1);
                    AddCompareInstruction(instruction.IP, accumulator, dest); // compare dest & accumulator
                    Add(instruction.IP, ISIL.OpCode.Not, new ISIL.Register(null, "TEMP"), new ISIL.Register(null, "ZF")); // TEMP = !ZF
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.IP + 1), new ISIL.Register(null, "TEMP")); // if accumulator == dest
                                                                                                                           // SET ZF = 1
                    Add(instruction.IP, ISIL.OpCode.Move, dest, src); // DEST = SRC
                    Add(instruction.IP, ISIL.OpCode.Jump, Imm(instruction.IP + 2)); // END IF
                                                                               // ELSE
                                                                               // SET ZF = 0
                    Add(instruction.IP + 1, ISIL.OpCode.Move, accumulator, dest); // accumulator = dest

                    Add(instruction.IP + 2, ISIL.OpCode.Nop); // exit for IF
                    break;
                }

            case Mnemonic.Jmp:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;

                    if (IsBranchTargetOutsideMethod(context.UnderlyingPointer, context.RawBytes.Length, jumpTarget))
                    {
                        callNoReturn = true;
                        goto case Mnemonic.Call;
                    }
                    else
                    {
                        Add(instruction.IP, ISIL.OpCode.Jump, Imm(jumpTarget));
                        break;
                    }
                }
                if (instruction.Op0Kind == OpKind.Register) // ex: jmp rax
                {
                    AddIndirectJmp(instruction);
                    break;
                }

                goto default;
            case Mnemonic.Je:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;

                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), new ISIL.Register(null, "ZF")); // if ZF == 1
                    break;
                }

                goto default;
            case Mnemonic.Jne:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;

                    Add(instruction.IP, ISIL.OpCode.Not, new ISIL.Register(null, "TEMP"), new ISIL.Register(null, "ZF")); // TEMP = !ZF
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), new ISIL.Register(null, "TEMP"));
                    break;
                }
                goto default;
            case Mnemonic.Js:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;

                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), new ISIL.Register(null, "SF")); // if SF == 1
                    break;
                }

                goto default;
            case Mnemonic.Jns:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;

                    Add(instruction.IP, ISIL.OpCode.Not, new ISIL.Register(null, "TEMP"), new ISIL.Register(null, "SF")); // TEMP = !SF
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), new ISIL.Register(null, "TEMP"));
                    break;
                }

                goto default;
            case Mnemonic.Jp: // jump if parity (PF == 1)
                if (instruction.Op0Kind != OpKind.Register)
                {
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.NearBranchTarget), new ISIL.Register(null, "PF"));
                    break;
                }

                goto default;
            case Mnemonic.Jnp: // jump if not parity (PF == 0)
                if (instruction.Op0Kind != OpKind.Register)
                {
                    Add(instruction.IP, ISIL.OpCode.Not, new ISIL.Register(null, "TEMP"), new ISIL.Register(null, "PF")); // TEMP = !PF
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(instruction.NearBranchTarget), new ISIL.Register(null, "TEMP"));
                    break;
                }

                goto default;
            case Mnemonic.Jg:
            case Mnemonic.Ja:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;
                    var temp = new ISIL.Register(null, "TEMP");
                    var temp2 = new ISIL.Register(null, "TEMP2");

                    Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                    Add(instruction.IP, ISIL.OpCode.Not, temp2, new ISIL.Register(null, "ZF")); // TEMP2 = !ZF
                    Add(instruction.IP, ISIL.OpCode.And, temp, temp, temp2); // TEMP = TEMP && TEMP2
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), temp);
                    break;
                }

                goto default;
            case Mnemonic.Jl:
            case Mnemonic.Jb:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;
                    var temp = new ISIL.Register(null, "TEMP");

                    Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                    Add(instruction.IP, ISIL.OpCode.Not, temp, temp); // TEMP = !TEMP
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), temp);
                    break;
                }

                goto default;
            case Mnemonic.Jge:
            case Mnemonic.Jae:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;
                    var temp = new ISIL.Register(null, "TEMP");

                    Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), temp);
                    break;
                }

                goto default;
            case Mnemonic.Jle:
            case Mnemonic.Jbe:
                if (instruction.Op0Kind != OpKind.Register)
                {
                    var jumpTarget = instruction.NearBranchTarget;
                    var temp = new ISIL.Register(null, "TEMP");

                    Add(instruction.IP, ISIL.OpCode.CheckEqual, temp, new ISIL.Register(null, "SF"), new ISIL.Register(null, "OF")); // TEMP = SF == OF
                    Add(instruction.IP, ISIL.OpCode.Not, temp, temp); // TEMP = !TEMP
                    Add(instruction.IP, ISIL.OpCode.Or, temp, temp, new ISIL.Register(null, "ZF")); // TEMP = TEMP || ZF
                    Add(instruction.IP, ISIL.OpCode.ConditionalJump, Imm(jumpTarget), temp);
                    break;
                }

                goto default;
            case Mnemonic.Xchg:
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "TEMP"), ConvertOperand(instruction, 0)); // TEMP = op0
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)); // op0 = op1
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 1), new ISIL.Register(null, "TEMP")); // op1 = TEMP
                break;
            case Mnemonic.Int:
            case Mnemonic.Int3:
                Add(instruction.IP, ISIL.OpCode.Interrupt); // We'll add it but eliminate later, can be used as a hint since compilers only emit it in normally unreachable code or in error handlers
                break;
            case Mnemonic.Prefetchw: // Fetches the cache line containing the specified byte from memory to the 1st or 2nd level cache, invalidating other cached copies.
            case Mnemonic.Nop:
                // While this is literally a nop and there's in theory no point emitting anything for it, it could be used as a jump target.
                // So we'll emit an ISIL nop for it.
                Add(instruction.IP, ISIL.OpCode.Nop);
                break;

            // x87 FPU instructions. We model the x87 stack as a single synthetic ST0 register
            // rather than a full 8-deep stack, which is enough to recover the common
            // load-compute-store pattern without emitting NotImplemented diagnostics.
            case Mnemonic.Fstp: // store ST(0) to dest and pop
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fst: // store ST(0) to dest without popping
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fld: // push src onto FPU stack
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fldz: // push 0.0
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "ST0"), new ISIL.FloatLiteral(0f));
                break;
            case Mnemonic.Fld1: // push 1.0
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "ST0"), new ISIL.FloatLiteral(1f));
                break;
            case Mnemonic.Fild: // load integer onto FPU stack
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fistp: // convert ST(0) to integer, store, and pop
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fadd: // ST(0) = ST(0) + src
                Add(instruction.IP, ISIL.OpCode.Add, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fsub: // ST(0) = ST(0) - src
                Add(instruction.IP, ISIL.OpCode.Subtract, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fsubr: // ST(0) = src - ST(0)
                Add(instruction.IP, ISIL.OpCode.Subtract, new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fmul: // ST(0) = ST(0) * src
                Add(instruction.IP, ISIL.OpCode.Multiply, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fdiv: // ST(0) = ST(0) / src
                Add(instruction.IP, ISIL.OpCode.Divide, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fdivr: // ST(0) = src / ST(0)
                Add(instruction.IP, ISIL.OpCode.Divide, new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0), new ISIL.Register(null, "ST0"));
                break;
            // The "p" (pop) forms combine the operation with popping the FPU stack. We don't model the
            // x87 stack, so the non-pop semantics (ST0 = ST0 op src) are emitted; with no explicit
            // operand (the common "faddp"/"fmulp" spellings) the source is ST1.
            case Mnemonic.Faddp: // ST0 = ST0 + src
                Add(instruction.IP, ISIL.OpCode.Add, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), instruction.OpCount > 0 ? ConvertOperand(instruction, 0) : new ISIL.Register(null, "ST1"));
                break;
            case Mnemonic.Fmulp: // ST0 = ST0 * src
                Add(instruction.IP, ISIL.OpCode.Multiply, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), instruction.OpCount > 0 ? ConvertOperand(instruction, 0) : new ISIL.Register(null, "ST1"));
                break;
            case Mnemonic.Fsubp: // ST0 = ST0 - src
                Add(instruction.IP, ISIL.OpCode.Subtract, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), instruction.OpCount > 0 ? ConvertOperand(instruction, 0) : new ISIL.Register(null, "ST1"));
                break;
            case Mnemonic.Fsubrp: // ST0 = src - ST0
                Add(instruction.IP, ISIL.OpCode.Subtract, new ISIL.Register(null, "ST0"), instruction.OpCount > 0 ? ConvertOperand(instruction, 0) : new ISIL.Register(null, "ST1"), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fdivp: // ST0 = ST0 / src
                Add(instruction.IP, ISIL.OpCode.Divide, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"), instruction.OpCount > 0 ? ConvertOperand(instruction, 0) : new ISIL.Register(null, "ST1"));
                break;
            case Mnemonic.Fdivrp: // ST0 = src / ST0
                Add(instruction.IP, ISIL.OpCode.Divide, new ISIL.Register(null, "ST0"), instruction.OpCount > 0 ? ConvertOperand(instruction, 0) : new ISIL.Register(null, "ST1"), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fchs: // ST(0) = -ST(0)
                Add(instruction.IP, ISIL.OpCode.Negate, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fabs: // ST(0) = |ST(0)| — approximate by AND-ing with itself (no effect, but keeps the value live)
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "ST0"), new ISIL.Register(null, "ST0"));
                break;
            case Mnemonic.Fcom: // compare ST(0) with src, set FPU flags
            case Mnemonic.Fcomp: // compare and pop
            case Mnemonic.Fucom: // unordered compare
            case Mnemonic.Fucomp: // unordered compare and pop
                AddCompareInstruction(instruction.IP, new ISIL.Register(null, "ST0"), ConvertOperand(instruction, 0));
                break;
            case Mnemonic.Fxch: // exchange ST(0) with ST(i)
                {
                    var fxchTemp = new ISIL.Register(null, "TEMP");
                    var fxchSti = ConvertOperand(instruction, 0);
                    Add(instruction.IP, ISIL.OpCode.Move, fxchTemp, new ISIL.Register(null, "ST0"));
                    Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "ST0"), fxchSti);
                    Add(instruction.IP, ISIL.OpCode.Move, fxchSti, fxchTemp);
                    break;
                }
            case Mnemonic.Fnop: // FPU no-op
                Add(instruction.IP, ISIL.OpCode.Nop);
                break;
            case Mnemonic.Das: // decimal adjust after subtraction - legacy BCD, never emitted by managed compilers
            case Mnemonic.Int1: // ICEBP debug trap
            case Mnemonic.In: // port I/O - no managed equivalent
            case Mnemonic.Out:
                Add(instruction.IP, ISIL.OpCode.Nop);
                break;

            case Mnemonic.Lahf: // AH = SF:ZF:0:AF:0:PF:1:CF — pack flags into AH (approximate as a flag-register load)
                Add(instruction.IP, ISIL.OpCode.Move, new ISIL.Register(null, "AH"), new ISIL.Register(null, "FLAGS"));
                break;

            case Mnemonic.Psrldq: // shift right double quadword — treat as a move for analysis purposes
            case Mnemonic.Pslldq: // shift left double quadword
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0));
                break;

            // Packed arithmetic: element-wise, but each element maps onto an ordinary arithmetic op.
            case Mnemonic.Addps:
            case Mnemonic.Addpd:
            case Mnemonic.Paddb:
            case Mnemonic.Paddw:
            case Mnemonic.Paddd:
            case Mnemonic.Paddq:
                Add(instruction.IP, ISIL.OpCode.Add, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Subps:
            case Mnemonic.Subpd:
            case Mnemonic.Psubb:
            case Mnemonic.Psubw:
            case Mnemonic.Psubd:
            case Mnemonic.Psubq:
                Add(instruction.IP, ISIL.OpCode.Subtract, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Mulps:
            case Mnemonic.Mulpd:
                Add(instruction.IP, ISIL.OpCode.Multiply, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Divps:
            case Mnemonic.Divpd:
                Add(instruction.IP, ISIL.OpCode.Divide, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Psrlq:
            case Mnemonic.Psrld:
            case Mnemonic.Psrlw:
                Add(instruction.IP, ISIL.OpCode.ShiftRight, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Mnemonic.Psllq:
            case Mnemonic.Pslld:
            case Mnemonic.Psllw:
                Add(instruction.IP, ISIL.OpCode.ShiftLeft, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            // Lane interleaves/extracts, shuffles and square roots have no faithful ISIL representation;
            // model them as moves so value flow is preserved, matching the Movaps/Cvtdq2ps handling above.
            case Mnemonic.Unpckhpd:
            case Mnemonic.Unpcklpd:
            case Mnemonic.Pshufd:
            case Mnemonic.Pshufw:
            case Mnemonic.Pextrw:
            case Mnemonic.Sqrtsd:
            case Mnemonic.Sqrtss:
            case Mnemonic.Sqrtps:
            case Mnemonic.Sqrtpd:
            case Mnemonic.Cvtsi2ss:
            case Mnemonic.Cvtsi2sd:
                Add(instruction.IP, ISIL.OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;

            default:
                Add(instruction.IP, ISIL.OpCode.NotImplemented, new ISIL.StringLiteral(FormatInstruction(instruction)));
                break;
        }

        void AddCompareInstruction(ulong ip, ISIL.IOperand op0, ISIL.IOperand op1)
        {
            var temp1 = new ISIL.Register(null, "TEMP1");
            var temp2 = new ISIL.Register(null, "TEMP2");
            var temp3 = new ISIL.Register(null, "TEMP3");
            var temp4 = new ISIL.Register(null, "TEMP4");
            var temp5 = new ISIL.Register(null, "TEMP5");

            Add(ip, ISIL.OpCode.CheckLess, new ISIL.Register(null, "CF"), op0, op1); // CF = op1 < op2
            Add(ip, ISIL.OpCode.Subtract, temp1, op0, op1); // temp1 = op1 - op2
            Add(ip, ISIL.OpCode.Xor, temp2, op0, op1); // temp2 = op1 ^ op2
            Add(ip, ISIL.OpCode.Xor, temp3, op0, temp1); // temp3 = op1 ^ temp1
            Add(ip, ISIL.OpCode.And, temp4, temp2, temp3); // temp4 = temp2 & temp3
            Add(ip, ISIL.OpCode.CheckLess, new ISIL.Register(null, "OF"), temp4, Imm(0)); // OF = temp4 < 0
            Add(ip, ISIL.OpCode.CheckLess, new ISIL.Register(null, "SF"), temp1, Imm(0)); // SF = temp1 < 0
            Add(ip, ISIL.OpCode.CheckEqual, new ISIL.Register(null, "ZF"), temp1, Imm(0)); // ZF = temp1 == 0
            Add(ip, ISIL.OpCode.And, temp5, temp2, Imm(1)); // temp5 = tmp2 & 1
            Add(ip, ISIL.OpCode.CheckEqual, new ISIL.Register(null, "PF"), temp5, Imm(0)); // PF = temp5 == 0
        }

        void AddTestInstruction(ulong ip, ISIL.IOperand op0, ISIL.IOperand op1)
        {
            var temp = new ISIL.Register(null, "TEMP");
            var temp2 = new ISIL.Register(null, "TEMP2");
            var temp5 = new ISIL.Register(null, "TEMP5");

            Add(ip, ISIL.OpCode.And, temp, op0, op1); // temp = op0 & op1
            Add(ip, ISIL.OpCode.CheckEqual, new ISIL.Register(null, "ZF"), temp, Imm(0)); // ZF = temp == 0
            Add(ip, ISIL.OpCode.CheckLess, new ISIL.Register(null, "SF"), temp, Imm(0)); // SF = temp < 0
            Add(ip, ISIL.OpCode.Move, new ISIL.Register(null, "CF"), Imm(0));  // CF = 0
            Add(ip, ISIL.OpCode.Move, new ISIL.Register(null, "OF"), Imm(0));  // OF = 0
            Add(ip, ISIL.OpCode.Xor, temp2, temp, Imm(0)); // temp2 = temp ^ 0
            Add(ip, ISIL.OpCode.And, temp5, temp2, Imm(1)); // temp5 = temp2 & 1
            Add(ip, ISIL.OpCode.CheckEqual, new ISIL.Register(null, "PF"), temp5, Imm(0)); // PF = temp5 == 0
        }
    }

    private ISIL.IOperand ConvertScalarFloatOperand(Instruction instruction, int operand, bool single, MethodAnalysisContext? context)
    {
        if (context == null || instruction.GetOpKind(operand) != OpKind.Memory)
            return ConvertOperand(instruction, operand);

        if (!instruction.IsIPRelativeMemoryOperand && instruction is not { MemoryBase: Register.None, MemoryIndex: Register.None })
            return ConvertOperand(instruction, operand);

        var address = instruction.IsIPRelativeMemoryOperand ? instruction.IPRelativeMemoryAddress : instruction.MemoryDisplacement64;

        return ReadFloatConstant(context.AppContext.Binary, address, single) ?? ConvertOperand(instruction, operand);
    }

    private static ISIL.IOperand? ReadFloatConstant(LibCpp2IL.Il2CppBinary binary, ulong addr, bool single)
    {
        if (!binary.TryMapVirtualAddressToRaw(addr, out var raw))
            return null;

        var content = binary.GetRawBinaryContent();
        var size = single ? 4 : 8;

        if (raw < 0 || raw + size > content.Length)
            return null;

        var bytes = content.Slice((int)raw, size).ToArray();

        return single
            ? new ISIL.FloatLiteral(BitConverter.ToSingle(bytes, 0))
            : new ISIL.DoubleLiteral(BitConverter.ToDouble(bytes, 0));
    }

    private ISIL.IOperand ConvertOperand(Instruction instruction, int operand, bool isLeaAddress = false)
    {
        var kind = instruction.GetOpKind(operand);

        if (kind == OpKind.Register)
            return new ISIL.Register(null, X86Utils.GetRegisterName(instruction.GetOpRegister(operand)));
        if (kind.IsImmediate())
            return new ISIL.Immediate((long)instruction.GetImmediate(operand));
        if (kind == OpKind.Memory && instruction.MemoryBase.GetFullRegister() == Register.RSP)
        {
            var slot = new ISIL.StackOffset((int)instruction.MemoryDisplacement32);
            return isLeaAddress ? new ISIL.AddressOf(slot) : slot;
        }

        //Memory
        //Most complex to least complex

        if (instruction.IsIPRelativeMemoryOperand)
            return new ISIL.MemoryOperand(addend: (long)instruction.IPRelativeMemoryAddress);

        //All four components
        if (instruction.MemoryIndex != Register.None && instruction.MemoryBase != Register.None && instruction.MemoryDisplacement64 != 0)
        {
            var mBase = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryBase));
            var mIndex = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryIndex));
            return new ISIL.MemoryOperand(mBase, mIndex, unchecked((int)instruction.MemoryDisplacement32), instruction.MemoryIndexScale);
        }

        //No addend
        if (instruction.MemoryIndex != Register.None && instruction.MemoryBase != Register.None)
        {
            var mBase = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryBase));
            var mIndex = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryIndex));
            return new ISIL.MemoryOperand(mBase, mIndex, scale: instruction.MemoryIndexScale);
        }

        //No base
        if (instruction.MemoryIndex != Register.None && instruction.MemoryDisplacement64 != 0)
        {
            var mIndex = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryIndex));
            return new ISIL.MemoryOperand(null, mIndex, unchecked((int)instruction.MemoryDisplacement32), instruction.MemoryIndexScale);
        }

        //No index (and so no scale)
        if (instruction.MemoryBase != Register.None && instruction.MemoryDisplacement64 > 0)
        {
            var mBase = new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryBase));
            return new ISIL.MemoryOperand(mBase, addend: unchecked((int)instruction.MemoryDisplacement32));
        }

        //Only base
        if (instruction.MemoryBase != Register.None)
        {
            return new ISIL.MemoryOperand(new ISIL.Register(null, X86Utils.GetRegisterName(instruction.MemoryBase)));
        }

        //Only addend
        return new ISIL.MemoryOperand(addend: (long)instruction.MemoryDisplacement64);
    }
}
