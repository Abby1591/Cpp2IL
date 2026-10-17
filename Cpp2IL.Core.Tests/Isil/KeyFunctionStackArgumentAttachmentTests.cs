using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Isil;

public class KeyFunctionStackArgumentAttachmentTests
{
    private const long KeyFunction = 0x10302870;
    private const long OtherFunction = 0x103028A0;

    private static Register Reg(string name) => new(null, name);

    private static void Add(List<Instruction> instructions, int index, OpCode opCode, params IOperand[] operands) =>
        instructions.Add(new Instruction(index, opCode, [.. operands]));

    private static void Push(List<Instruction> instructions, int index, IOperand value)
    {
        Add(instructions, index, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, index + 1, OpCode.Move, new StackOffset(0), value);
    }

    private static bool IsKey(ulong address) => address == (ulong)KeyFunction;

    // Unmanaged key-function calls carry no signature, so their argument pushes were dead and got
    // deleted before key-function recovery ran. The contiguous push run in front of the call is the
    // callee's stack-passed arguments: the push closest to the call is argument 0 at slot 0.

    [Test]
    public void KeyFunctionCallGetsItsPushRunAttached()
    {
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax")); // argument pushed first = last argument
        Push(instructions, 2, Reg("rcx")); // argument pushed last = argument 0
        Add(instructions, 4, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 5, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 1, 2, 3 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[4];
        Assert.That(call.Operands, Has.Count.EqualTo(4), "target, return register and two stack slots");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0), "closest push is argument 0");
        Assert.That(((StackOffset)call.Operands[3]).Offset, Is.EqualTo(4), "earlier push is argument 1");
    }

    [Test]
    public void NonKeyFunctionCallStaysBare()
    {
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax"));
        Add(instructions, 2, OpCode.Call, new Immediate(OtherFunction), Reg("rax"));
        Add(instructions, 3, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        Assert.That(instructions[2].Operands, Has.Count.EqualTo(2), "only target and return register");
    }

    [Test]
    public void KeyFunctionCallWithoutPushRunStaysBare()
    {
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 1, OpCode.Return);
        var addresses = new List<ulong> { 0, 1 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        Assert.That(instructions[0].Operands, Has.Count.EqualTo(2), "no arguments were pushed");
    }

    [Test]
    public void LoadsAndStoresInterleavedWithTheRunDoNotHideIt()
    {
        // MSVC pushes args right before the call with loads and lea results interleaved; only
        // branch/call boundaries and cleanups end the argument region.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax"));
        Add(instructions, 2, OpCode.Add, Reg("rdx"), Reg("rbp"), new Immediate(-32)); // lea, neutral
        Push(instructions, 3, Reg("rdx"));
        Add(instructions, 5, OpCode.Move, new MemoryOperand(Reg("rbp"), null, -16), Reg("xmm0")); // dead store, neutral
        Add(instructions, 6, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 7, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2, 2, 3, 4, 5 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[6];
        Assert.That(call.Operands, Has.Count.EqualTo(4), "both pushes are visible past the interleaved instructions");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0));
        Assert.That(((StackOffset)call.Operands[3]).Offset, Is.EqualTo(4));
    }

    [Test]
    public void PreviousCallStopsTheRun()
    {
        // The first push belongs to the earlier call, not to the key function.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax"));
        Add(instructions, 2, OpCode.Call, new Immediate(OtherFunction), Reg("rax"));
        Push(instructions, 3, Reg("rcx"));
        Add(instructions, 5, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 6, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2, 3, 4, 5 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[5];
        Assert.That(call.Operands, Has.Count.EqualTo(3), "only the push after the previous call is ours");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0));
    }

    [Test]
    public void CallerCleanupEndsTheRun()
    {
        // push; add esp,4 (for an earlier slot); push; call - the cleaned push is not ours.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax"));
        Add(instructions, 2, OpCode.ShiftStack, new Immediate(4));
        Push(instructions, 3, Reg("rcx"));
        Add(instructions, 5, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 6, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2, 3, 4, 5 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[5];
        Assert.That(call.Operands, Has.Count.EqualTo(3), "the positive ShiftStack ends the argument region");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0));
    }

    [Test]
    public void PrologueFrameSetupIsNotAnArgument()
    {
        // push ebp; mov ebp,esp; push arg; call - the frame push is not part of the run.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rbp"));
        Add(instructions, 2, OpCode.Move, Reg("rbp"), Reg("rsp"));
        Push(instructions, 3, Reg("rax"));
        Add(instructions, 5, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 6, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2, 3, 4, 5 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[5];
        Assert.That(call.Operands, Has.Count.EqualTo(3), "only the argument push counts");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0));
    }

    [Test]
    public void VoidCallGetsItsPushRunAttached()
    {
        // A registered void stub builds the raiser site as CallVoid (target only, no return
        // register), which the previous [Immediate, _] pattern rejected - the exception argument
        // push was then deleted before the resolver could turn the call into a CIL throw.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax")); // the exception being raised
        Add(instructions, 2, OpCode.CallVoid, new Immediate(KeyFunction));
        Add(instructions, 3, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[2];
        Assert.That(call.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(call.Operands, Has.Count.EqualTo(2), "target and the attached exception slot");
        Assert.That(((StackOffset)call.Operands[1]).Offset, Is.EqualTo(0), "closest push is argument 0");
    }

    [Test]
    public void CallTargetWithoutResultRegisterAlsoGetsAttached()
    {
        // Some sites build a non-void call with only the target operand; the pattern must key on
        // the leading immediate rather than an exact operand count.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rax"));
        Add(instructions, 2, OpCode.Call, new Immediate(KeyFunction));
        Add(instructions, 3, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[2];
        Assert.That(call.Operands, Has.Count.EqualTo(2), "target and the attached exception slot");
        Assert.That(((StackOffset)call.Operands[1]).Offset, Is.EqualTo(0));
    }

    [Test]
    public void JumpTargetBoundsTheRunToItsOwnBlock()
    {
        // A branch into the second push means the first push may not have executed on the path
        // reaching the call, so only the push in this block is argument 0.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ConditionalJump, new Immediate(0x1002));
        Push(instructions, 1, Reg("rax")); // block 0x1001
        Push(instructions, 3, Reg("rcx")); // block 0x1002 - the branch target
        Add(instructions, 5, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 6, OpCode.Return);
        var addresses = new List<ulong> { 0x1000, 0x1001, 0x1001, 0x1002, 0x1002, 0x1003, 0x1004 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey);

        var call = instructions[5];
        Assert.That(call.Operands, Has.Count.EqualTo(3), "only the jump-target block's push is counted");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0));
    }

    [Test]
    public void KnownArgumentCountExtendsAnUndercountedRun()
    {
        // il2cpp_array_new_specific(klass, length): branches push different lengths then jump to the
        // shared class push, so the contiguous scan only sees the class (slot 0). The known arity (2)
        // restores the missing length slot so array recovery can see it.
        var instructions = new List<Instruction>();
        Push(instructions, 0, Reg("rcx")); // the class push in this block
        Add(instructions, 2, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 3, OpCode.Return);
        var addresses = new List<ulong> { 0, 0, 1, 2 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey, _ => 2);

        var call = instructions[2];
        Assert.That(call.Operands, Has.Count.EqualTo(4), "target, return register and two stack slots");
        Assert.That(((StackOffset)call.Operands[2]).Offset, Is.EqualTo(0), "the scanned class push is argument 0");
        Assert.That(((StackOffset)call.Operands[3]).Offset, Is.EqualTo(4), "the known arity restores the missing length");
    }

    [Test]
    public void KnownArgumentCountDoesNotMaterialiseArgumentsWithoutAPushRun()
    {
        // A key function with a known arity but no visible push run was not called with stack
        // arguments here; the fallback must never fabricate operands from nothing.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.Call, new Immediate(KeyFunction), Reg("rax"));
        Add(instructions, 1, OpCode.Return);
        var addresses = new List<ulong> { 0, 1 };

        X86InstructionSet.AttachKeyFunctionStackArguments(instructions, addresses, IsKey, _ => 2);

        Assert.That(instructions[0].Operands, Has.Count.EqualTo(2), "no pushes means the call stays bare");
    }
}
