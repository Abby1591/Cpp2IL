using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL;

namespace Cpp2IL.Core.Analysis;

public static class MetadataResolver
{
    public static void ResolveAll(MethodAnalysisContext method)
    {
        ResolveStringLiteralAccessors(method);
        ResolveCalls(method);
        ResolveGetter(method);
        ResolveMetadataUsages(method);
    }

    private static void ResolveStringLiteralAccessors(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands[1] is not LocalVariable result)
                continue;

            for (var i = 2; i < instruction.Operands.Count; i++)
            {
                if (LiteralSlotAddress(instruction.Operands[i], definitions) is not { } address
                    || libContext.GetLiteralByAddress(address) is not { } literal)
                    continue;

                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(result, new StringLiteral(literal));
                break;
            }
        }
    }

    private static ulong? LiteralSlotAddress(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
        operand switch
        {
            Immediate immediate => immediate.UnsignedValue,
            LocalVariable local when definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, Immediate immediate] } => immediate.UnsignedValue,
            _ => null,
        };

    /// <summary>
    /// Resolves <c>Move local, [absoluteAddress]</c> loads of IL2CPP metadata-usage globals into a
    /// strongly-typed operand: a string literal, a <see cref="TypeAnalysisContext"/> (an Il2CppType*/
    /// Il2CppClass* usage) or, for a MethodInfo* usage, a <see cref="RuntimeMethodInfoAnalysisContext"/>
    /// naming the method it refers to (also used to type the local - see <see cref="LocalVariables"/>),
    /// or likewise a <see cref="RuntimeFieldInfoAnalysisContext"/> for a FieldInfo* usage.
    /// </summary>
    private static void ResolveMetadataUsages(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move)
                continue;

            if (instruction.Operands[0] is not LocalVariable)
                continue;

            var address = instruction.Operands[1] switch
            {
                MemoryOperand { Base: null, Index: null, Scale: 0 } memory => (ulong)memory.Addend,
                Immediate immediate => immediate.UnsignedValue,
                _ => 0ul,
            };

            if (address == 0)
                continue;

            // String literal.
            var stringLiteral = libContext.GetLiteralByAddress(address);
            if (stringLiteral != null)
            {
                instruction.SetOperand(1, new StringLiteral(stringLiteral));
                continue;
            }

            // Type metadata usage (Il2CppType* / Il2CppClass*).
            if (method.DeclaringType is { } declaringType)
            {
                var typeGlobal = libContext.GetTypeGlobalByAddress(address);
                if (typeGlobal != null)
                {
                    instruction.SetOperand(1, declaringType.AppContext.ResolveIl2CppType(typeGlobal));
                    continue;
                }
            }

            // Method metadata usage (MethodInfo*). On metadata v27+ GetMethodGlobalByAddress can return
            // any global, so confirm it is actually a method before resolving - the resolver's switch
            // throws on other usage kinds.
            var methodUsage = libContext.GetMethodGlobalByAddress(address);
            if (methodUsage?.Type is MetadataUsageType.MethodDef or MetadataUsageType.MethodRef
                && method.AppContext.ResolveContextForMethod(methodUsage) is { DeclaringType: { } methodDeclaringType } methodContext)
            {
                instruction.SetOperand(1, new RuntimeMethodInfoAnalysisContext(methodContext, methodDeclaringType.DeclaringAssembly));
                continue;
            }

            // Field metadata usage (FieldInfo*), e.g. the RuntimeFieldHandle passed to InitializeArray.
            if (libContext.GetRawFieldGlobalByAddress(address) is { Type: MetadataUsageType.FieldInfo } fieldUsage
                && method.AppContext.ResolveContextForField(fieldUsage.AsField()) is { DeclaringType.DeclaringAssembly: { } fieldAssembly } fieldContext)
                instruction.SetOperand(1, new RuntimeFieldInfoAnalysisContext(fieldContext, fieldAssembly));
        }
    }

    /// <summary>
    /// Replaces every <c>[base + addend]</c> memory operand whose base is a typed local with a
    /// <see cref="FieldReference"/> to the field at that offset. Returns whether any operand was
    /// resolved this pass, so the type/field fixpoint can detect convergence: as more bases become
    /// typed (a field load types its result, which is the base of the next load), more offsets
    /// resolve, so this is re-run until it stops finding new fields.
    /// </summary>
    public static bool ResolveFieldOffsets(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is not MemoryOperand memory)
                    continue;

                // Has to be [base (local) + addend (field offset)]
                if (memory.Index != null || memory.Scale != 0)
                    continue;

                if (memory.Base is not LocalVariable local || local?.Type == null)
                    continue;

                // check if static field access
                var staticOwner = (local.Type as StaticFieldStorageTypeAnalysisContext)?.OwnerType;
                var owner = staticOwner ?? local.Type;
                var genericOwner = owner as GenericInstanceTypeAnalysisContext;

                FieldAnalysisContext? field;
                if (genericOwner != null && staticOwner == null)
                {
                    // metadata has all-0 offsets for generic definitions, so recompute layout
                    // TODO support user-defined value types
                    if (genericOwner.GenericArguments.Any(a => a.IsValueType))
                        continue;

                    field = GenericInstanceFieldLayout.FindFieldAtOffset(genericOwner.GenericType, memory.Addend);
                }
                else if (staticOwner == null && owner.GenericParameters.Count > 0)
                {
                    field = GenericInstanceFieldLayout.FindFieldAtOffset(owner, memory.Addend);
                }
                else
                {
                    // an inherited field exists on the base type but sits at the same offset in the
                    // derived layout, so the whole chain is searched
                    field = null;
                    for (var candidateOwner = genericOwner?.GenericType ?? owner; candidateOwner != null && field == null; candidateOwner = candidateOwner.BaseType)
                        field = candidateOwner.Fields.FirstOrDefault(f => f.IsStatic == (staticOwner != null)
                            && (f.Attributes & FieldAttributes.Literal) == 0 // consts have no storage but their metadata offset is 0, which would match
                            && f.BackingData?.FieldOffset == memory.Addend);
                }

                if (field == null) // TODO: Support nested fields (Field1.Field2.Field3)
                    continue;

                // make sure we have a full GIT for field access. open type is bad.
                if (genericOwner != null)
                    field = new ConcreteGenericFieldAnalysisContext(field, genericOwner);

                instruction.SetOperand(i, new FieldReference(field, local, (int)memory.Addend));
                changed = true;
            }
        }

        return changed;
    }

    private static void ResolveCalls(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            if (block.BlockType != BlockType.Call && block.BlockType != BlockType.TailCall)
                continue;

            var callInstruction = block.Instructions[^1];
            if (callInstruction.Operands[0] is not Immediate dest)
                continue;

            var target = dest.UnsignedValue;

            var keyFunctionAddresses = method.AppContext.GetOrCreateKeyFunctionAddresses();

            if (keyFunctionAddresses.IsKeyFunctionAddress(target))
            {
                HandleKeyFunction(method.AppContext, callInstruction, target, keyFunctionAddresses);

                if (target == keyFunctionAddresses.il2cpp_codegen_initialize_runtime_metadata_inline
                    && callInstruction is { OpCode: OpCode.Call, Operands: [_, var initResult, var handle, ..] })
                {
                    callInstruction.OpCode = OpCode.Move;
                    callInstruction.SetOperands(initResult, handle);
                }

                continue;
            }

            //Non-key function call. Try to find a single match
            if (!method.AppContext.MethodsByAddress.TryGetValue(target, out var targetMethods))
            {
                // Not a managed method at all. It may be one of the runtime helpers built around an exception
                // type, which either throw it themselves or build it and hand it back for the caller to raise.
                TryConvertToThrowHelperOrRaiser(method, callInstruction, target);
                continue;
            }

            // Duplicated/Shared method bodies are resolved later in ResolveCallsViaMethodInfo/ResolveAmbiguousCalls.
            if (targetMethods is not [{ } singleTargetMethod])
                continue;

            // The native-method detector registers an injected stub for every unresolved call, but the
            // call may still target an exception helper or raiser - the stub binding must not win over
            // the CIL throw conversion.
            if (singleTargetMethod is NativeMethodAnalysisContext && TryConvertToThrowHelperOrRaiser(method, callInstruction, target))
                continue;

            callInstruction.SetOperand(0, singleTargetMethod);
            singleTargetMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(callInstruction, singleTargetMethod, method);
        }

        method.ControlFlowGraph.MergeCallBlocks();
    }

    /// <summary>
    /// Turns a call to <paramref name="target"/> into CIL that throws: <c>newobj</c> when the target
    /// is a runtime helper that builds an exception and the result is consumed (operand layout is
    /// preserved), or <c>throw</c> when the target throws the exception it was given (taken from the
    /// call's stack arguments, which only exist if <c>AttachKeyFunctionStackArguments</c> kept them).
    /// Returns false - leaving the instruction untouched - when the target is neither, so callers can
    /// fall through to normal binding (e.g. to an injected native stub).
    /// </summary>
    private static bool TryConvertToThrowHelperOrRaiser(MethodAnalysisContext method, Instruction callInstruction, ulong target)
    {
        if (ThrowHelperRecovery.GetThrownException(method.AppContext, target) is { } thrown)
        {
            if (callInstruction.Destination is LocalVariable produced && method.ControlFlowGraph!.Instructions.Any(i => i.Sources.Any(s => ReferenceEquals(s, produced))))
            {
                callInstruction.OpCode = OpCode.Newobj;
                callInstruction.SetOperands(produced, thrown);
            }
            else
            {
                callInstruction.OpCode = OpCode.Throw;
                callInstruction.SetOperands(thrown);
            }

            return true;
        }

        // Otherwise it may be one of the raisers, which throw the exception they are given
        var raisedIndex = callInstruction.OpCode == OpCode.CallVoid ? 1 : 2;

        if (callInstruction.Operands.Count > raisedIndex && ThrowHelperRecovery.IsExceptionRaiser(method.AppContext, target))
        {
            // IsExceptionRaiser is a reachability check, so ordinary functions that may raise on
            // error (klass lookups, array allocation) also match. A real raiser never hands a
            // result back to its caller: if the produced value is read somewhere this is one of
            // those, not a throw site, and must stay a normal call.
            if (callInstruction.Destination is LocalVariable produced && method.ControlFlowGraph!.Instructions.Any(i => i.Sources.Any(s => ReferenceEquals(s, produced))))
                return false;

            // Void-shaped sites have no result to check, so ask the callee instead: may-raise
            // functions return normally, real raisers do not. Unknown (unscannable) counts as
            // not returning, so this can only ever block a conversion, never starve one.
            if (method.AppContext.InstructionSet.CalleeCanReturn(method.AppContext, target))
                return false;

            var raised = callInstruction.Operands[raisedIndex];

            callInstruction.OpCode = OpCode.Throw;
            callInstruction.SetOperands(raised);
            return true;
        }

        return false;
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by matching the receiver's known
    /// type against the candidates' declaring types. Runs inside the type/field fixpoint and so
    /// re-fires as receivers become typed - a resolved call types its return value, which can type
    /// the receiver of a further call. Returns whether any call was resolved this pass.
    ///
    /// Conservative by design: it commits only when exactly one non-static candidate's declaring
    /// type matches the receiver's type. Anything still untyped or ambiguous is left for a later
    /// pass, or left unresolved - it never guesses.
    /// </summary>
    public static bool ResolveAmbiguousCalls(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            // A resolved call's target is a method/key-function name; only unresolved ones are still numeric.
            if (instruction.Operands[0] is not Immediate target)
                continue;

            var candidates = method.AppContext.GetCallCandidatesAt(target.UnsignedValue);
            if (candidates is not { Count: > 0 })
                continue;

            // A generic method's open definition shares its native body with the instantiation(s) it was
            // compiled into, so the definition sitting next to them is not real ambiguity. Once it's dropped a
            // single survivor is the answer. This runs after ResolveCallsViaMethodInfo every iteration, so a
            // call whose hidden MethodInfo names an instantiation that isn't in the map has already been bound
            // and won't reach here - leaving only the calls that really do target this one method.
            if (candidates.Count == 1)
            {
                var only = candidates[0];

                // A generic *method* is a special case: unless the metadata happened to record the caller's
                // instantiation, the only concrete in the map can be a placeholder (System.Object) that is not
                // what the caller wants. Only the hidden MethodInfo names the exact one, and that path may need
                // further passes to become usable, so never pre-empt it by guessing here.
                if (only is ConcreteGenericMethodAnalysisContext { BaseMethodContext.GenericParameters.Count: > 0 })
                    continue;

                instruction.SetOperand(0, only);
                only.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, only, method);
                changed = true;
                continue;
            }

            // e.g. string.Equals and string.op_Equality, identical params, instance type, and bodies are shared
            // we can't differentiate which is being called but it doesn't matter
            if (AreInterchangeable(candidates))
            {
                var preferred = PreferredOf(candidates);
                instruction.SetOperand(0, preferred);
                preferred.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, preferred, method);
                changed = true;
                continue;
            }

            // Handle methods with shared bodies
            var match = default(MethodAnalysisContext);

            // The receiver's own type is the best disambiguator, but a `this` receiver which hasn't
            // been typed yet still tells us the declaring type - that is enough to resolve a call
            // through a shared body (e.g. a ctor chaining to a folded base ctor, or a shared empty
            // Dispose) by matching the candidate whose declaring type is on our base chain.
            var receiver = GetReceiver(instruction, preferThis: method.Name == ".ctor");
            var receiverType = receiver?.Type ?? (receiver is { IsThis: true } ? method.DeclaringType : null);

            if (receiverType != null)
            {
                // Prefer picking base ctor if we are a ctor
                var callerIsCtor = method.Name == ".ctor" && receiver!.IsThis;

                for (var type = receiverType; type != null && match == null; type = type.BaseType)
                {
                    var matches = candidates.Where(c => !c.IsStatic && IsSameType(c.DeclaringType, type)).ToList();

                    if (matches.Count > 1 && callerIsCtor)
                        matches = matches.Where(c => c.Name == ".ctor").ToList();

                    if (matches.Count > 1)
                        break;

                    match = matches.SingleOrDefault();
                }
            }

            if (match == null)
                match = TryMatchStaticByFirstArgument(candidates, instruction);

            if (match == null && receiverType != null)
                match = TryMatchInstanceByTypedArguments(candidates, instruction, receiverType);

            if (match == null)
                match = TryMatchByTypedReturn(candidates, instruction);

            // Last resort: an ICF fold of unrelated types that share the exact call shape. Only reached when
            // neither the receiver's type nor any argument could disambiguate, so there is no better answer.
            if (match == null && ShareCallShape(candidates))
                match = PreferredOf(candidates);

            if (match == null)
                continue;

            instruction.SetOperand(0, match);
            match.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, match, method);
            changed = true;
        }

        return changed;
    }

    private static bool AreInterchangeable(List<MethodAnalysisContext> candidates)
    {
        var first = candidates[0];

        return candidates.All(c => c.IsStatic == first.IsStatic
            && ReferenceEquals(c.DeclaringType, first.DeclaringType)
            && ReferenceEquals(c.ReturnType, first.ReturnType)
            && c.Parameters.Count == first.Parameters.Count
            && SameParameterTypes(c, first));
    }

    // ICF folds genuinely unrelated methods to one body (e.g. every state machine's empty
    // `System.IDisposable.Dispose`) so the declaring types differ. When neither the receiver's type nor any
    // argument can pick one out, the call is nevertheless indistinguishable at the call site as long as the
    // observable call shape - name, argument and return slots - matches. Two methods that share a body behave
    // identically, and integer primitives of the same width occupy the same argument slots (byte/sbyte,
    // short/ushort, int/uint, long/ulong), so such bodies are interchangeable at the call.
    private static bool ShareCallShape(List<MethodAnalysisContext> candidates)
    {
        var first = candidates[0];
        var types = first.AppContext.SystemTypes;

        return candidates.All(c => c.IsStatic == first.IsStatic
            && c.Name == first.Name
            && AbiEquivalent(c.ReturnType, first.ReturnType, types)
            && c.Parameters.Count == first.Parameters.Count
            && SameAbiParameterTypes(c, first, types));
    }

    private static bool SameAbiParameterTypes(MethodAnalysisContext a, MethodAnalysisContext b, SystemTypesContext types)
    {
        for (var i = 0; i < a.Parameters.Count; i++)
        {
            if (!AbiEquivalent(a.Parameters[i].ParameterType, b.Parameters[i].ParameterType, types))
                return false;
        }

        return true;
    }

    private static bool AbiEquivalent(TypeAnalysisContext? a, TypeAnalysisContext? b, SystemTypesContext types)
    {
        if (ReferenceEquals(a, b))
            return true;

        var width = IntegerWidth(a, types);
        return width != 0 && width == IntegerWidth(b, types);
    }

    // The width of an integer primitive in bytes, or 0 for anything else. Only these are treated as
    // interchangeable: float/double and references have distinct calling behaviour and are left exact.
    private static int IntegerWidth(TypeAnalysisContext? type, SystemTypesContext types) =>
        ReferenceEquals(type, types.SystemSByteType) || ReferenceEquals(type, types.SystemByteType) ? 1
        : ReferenceEquals(type, types.SystemInt16Type) || ReferenceEquals(type, types.SystemUInt16Type) || ReferenceEquals(type, types.SystemCharType) ? 2
        : ReferenceEquals(type, types.SystemInt32Type) || ReferenceEquals(type, types.SystemUInt32Type) ? 4
        : ReferenceEquals(type, types.SystemInt64Type) || ReferenceEquals(type, types.SystemUInt64Type) ? 8
        : 0;

    private static bool SameParameterTypes(MethodAnalysisContext a, MethodAnalysisContext b)
    {
        for (var i = 0; i < a.Parameters.Count; i++)
        {
            if (!ReferenceEquals(a.Parameters[i].ParameterType, b.Parameters[i].ParameterType))
                return false;
        }

        return true;
    }

    // Prefer operators if possible
    private static MethodAnalysisContext PreferredOf(List<MethodAnalysisContext> candidates) =>
        candidates.FirstOrDefault(c => c.Name.StartsWith("op_")) ?? candidates[0];

    // The receiver ('this') of a call is the first integer-slot argument: operand 1 for CallVoid
    // (after the target), operand 2 for Call (after the target and the return value).
    // A value type receiver is passed byref, so it arrives as an AddressOf over the local.
    // When preferThis is set (constructor chaining), the explicit 'this' local is authoritative:
    // for an unresolved call the lifter attaches operands positionally without knowing the callee,
    // so 'this' may not sit at the conventional index.
    private static LocalVariable? GetReceiver(Instruction call, bool preferThis = false)
    {
        if (preferThis)
        {
            foreach (var operand in call.Operands)
            {
                var thisLocal = operand switch
                {
                    LocalVariable { IsThis: true } local => local,
                    AddressOf { Target: LocalVariable { IsThis: true } addressed } => addressed,
                    _ => null
                };

                if (thisLocal != null)
                    return thisLocal;
            }
        }

        var index = call.OpCode == OpCode.CallVoid ? 1 : 2;

        return index < call.Operands.Count
            ? call.Operands[index] switch
            {
                LocalVariable local => local,
                AddressOf { Target: LocalVariable addressed } => addressed,
                _ => null
            }
            : null;
    }

    // Static methods have no receiver, so a shared body such as the operator folds (op_Implicit,
    // op_Equality, op_Inequality...) is disambiguated by the type of the first argument instead:
    // e.g. IntPtr::op_Inequality(IntPtr, IntPtr) vs Type::op_Inequality(Type, Type) are told apart
    // by whether the first argument is an IntPtr or a Type. Only a unique match is committed.
    private static MethodAnalysisContext? TryMatchStaticByFirstArgument(List<MethodAnalysisContext> candidates, Instruction call)
    {
        // First argument sits after the target: operand 1 for CallVoid, operand 2 for Call
        // (which also carries the return value).
        var argIndex = call.OpCode == OpCode.CallVoid ? 1 : 2;

        if (argIndex >= call.Operands.Count)
            return null;

        var argType = call.Operands[argIndex] switch
        {
            LocalVariable { Type: { } localType } => localType,
            AddressOf { Target: LocalVariable { Type: { } addressedType } } => addressedType,
            _ => null
        };

        if (argType == null)
            return null;

        MethodAnalysisContext? match = null;

        foreach (var candidate in candidates)
        {
            if (!candidate.IsStatic || candidate.Parameters.Count == 0)
                continue;

            if (!IsSameType(candidate.Parameters[0].ParameterType, argType))
                continue;

            if (match != null)
                return null; // ambiguous - two static candidates take the same first argument

            match = candidate;
        }

        return match;
    }

    // Overloads that differ only by return type (e.g. Hazel.MessageReader::ReadSByte vs ReadByte, or
    // Nullable<X>::get_Value across instantiations) cannot be told apart by the receiver or the arguments,
    // but the call's result is written to a local that may already be typed. Keep only the candidates that
    // return that type and commit just when one survives.
    private static MethodAnalysisContext? TryMatchByTypedReturn(List<MethodAnalysisContext> candidates, Instruction call)
    {
        // A value-returning call carries its destination local right after the target.
        if (call.OpCode != OpCode.Call || call.Operands.Count < 2)
            return null;

        var returnType = call.Operands[1] switch
        {
            LocalVariable { Type: { } localType } => localType,
            AddressOf { Target: LocalVariable { Type: { } addressedType } } => addressedType,
            _ => null
        };

        if (returnType == null)
            return null;

        MethodAnalysisContext? match = null;

        foreach (var candidate in candidates)
        {
            if (candidate.ReturnType is not { } candidateReturn || !IsSameType(candidateReturn, returnType))
                continue;

            if (match != null)
                return null; // two candidates return the same type - still ambiguous

            match = candidate;
        }

        return match;
    }

    // Overloads on the same declaring type (e.g. Hazel.MessageWriter::Write(byte) vs Write(int)) share
    // a body address and cannot be told apart by the receiver. Disambiguate them by the types of the
    // arguments that are already known: a candidate is eliminated as soon as one of its parameters'
    // types disagrees with the corresponding typed operand. Commits only when exactly one candidate
    // survives and at least one argument was actually checked.
    private static MethodAnalysisContext? TryMatchInstanceByTypedArguments(List<MethodAnalysisContext> candidates, Instruction call, TypeAnalysisContext receiverType)
    {
        // Arguments start after the target and, for an instance call, the receiver: operand 2 for
        // CallVoid (target + this) and operand 3 for Call (target + return value + this).
        var paramStart = call.OpCode == OpCode.Call ? 3 : 2;
        var available = call.Operands.Count - paramStart;

        if (available <= 0)
            return null;

        MethodAnalysisContext? match = null;
        var anyChecked = false;

        foreach (var candidate in candidates)
        {
            if (candidate.IsStatic || candidate.Parameters.Count == 0 || candidate.Parameters.Count > available)
                continue;

            if (!IsOnBaseChain(candidate.DeclaringType, receiverType))
                continue;

            var ok = true;
            var checkedArgument = false;

            for (var i = 0; i < candidate.Parameters.Count; i++)
            {
                if (OperandType(call.Operands[paramStart + i]) is not { } operandType)
                    continue; // unknown argument type cannot discriminate

                checkedArgument = true;

                if (!IsSameType(candidate.Parameters[i].ParameterType, operandType))
                {
                    ok = false;
                    break;
                }
            }

            if (!ok || !checkedArgument)
                continue;

            anyChecked = true;

            if (match != null)
                return null; // ambiguous - two candidates agree with the typed arguments

            match = candidate;
        }

        return anyChecked ? match : null;
    }

    private static TypeAnalysisContext? OperandType(IOperand operand) =>
        operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            AddressOf { Target: LocalVariable { Type: { } addressedType } } => addressedType,
            _ => null
        };

    private static bool IsOnBaseChain(TypeAnalysisContext? type, TypeAnalysisContext baseType)
    {
        for (var current = baseType; current != null; current = current.BaseType)
            if (IsSameType(type, current))
                return true;

        return false;
    }

    // Concrete generic method contexts build their declaring type fresh rather than via the
    // GetOrCreate cache, so generic instances also need comparing structurally.
    // TODO Fix this, concrete generic methods should use GetOrCreate
    private static bool IsSameType(TypeAnalysisContext? a, TypeAnalysisContext? b)
    {
        if (ReferenceEquals(a, b))
            return true;

        if (a is not GenericInstanceTypeAnalysisContext leftInstance
            || b is not GenericInstanceTypeAnalysisContext rightInstance
            || !ReferenceEquals(leftInstance.GenericType, rightInstance.GenericType)
            || leftInstance.GenericArguments.Count != rightInstance.GenericArguments.Count)
            return false;

        for (var i = 0; i < leftInstance.GenericArguments.Count; i++)
        {
            if (!IsSameType(leftInstance.GenericArguments[i], rightInstance.GenericArguments[i]))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Resolves any Call (theoretically should always be a CallVoid) target directly after a Newobj to a constructor call.
    /// </summary>
    public static bool ResolveConstructorCalls(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable definition)
                definitions[definition] = instruction;

        var changed = false;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not Immediate callTarget)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(callTarget.UnsignedValue, out var candidates))
                continue;

            if (GetReceiver(instruction) is not { } receiver || AllocatedType(receiver, definitions) is not { } allocatedType)
                continue;

            var constructor = candidates.FirstOrDefault(c => !c.IsStatic && c.Name == ".ctor" && ReferenceEquals(c.DeclaringType, allocatedType))
                              ?? FindConstructorForSharedBody(allocatedType, candidates);
            if (constructor == null)
                continue;

            instruction.SetOperand(0, constructor);
            constructor.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, constructor, method);
            changed = true;
        }

        return changed;
    }

    private static MethodAnalysisContext? FindConstructorForSharedBody(TypeAnalysisContext allocatedType, List<MethodAnalysisContext> candidates)
    {
        var candidateParamCounts = new HashSet<int>(candidates
            .Where(c => c is { IsStatic: false, Name: ".ctor" })
            .Select(c => c.Parameters.Count));

        if (candidateParamCounts.Count == 0)
            return null;

        var definition = allocatedType is GenericInstanceTypeAnalysisContext genericInstance ? genericInstance.GenericType : allocatedType;
        var matches = definition.Methods
            .Where(m => m is { IsStatic: false, Name: ".ctor" } && candidateParamCounts.Contains(m.Parameters.Count))
            .ToList();

        if (matches is not [{ } match])
            return null;

        return allocatedType is GenericInstanceTypeAnalysisContext instance
            ? new ConcreteGenericMethodAnalysisContext(match, instance.GenericArguments, [])
            : match;
    }

    // Follow SSA copies from a local back to the Newobj that produced the value
    private static TypeAnalysisContext? AllocatedType(LocalVariable local, Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local) && definitions.TryGetValue(local, out var definition))
        {
            switch (definition.OpCode)
            {
                case OpCode.Newobj:
                    return (definition.Operands[0] as LocalVariable)?.Type;
                case OpCode.Move when definition.Operands[1] is LocalVariable source:
                    local = source;
                    continue;
            }

            break;
        }

        return null;
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by reading the runtime
    /// <c>MethodInfo*</c> the caller passes in, if there is one.
    /// </summary>
    public static bool ResolveCallsViaMethodInfo(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (instruction.Operands[0] is not Immediate target)
                //Already resolved
                continue;

            if (GetMethodInfoArgument(instruction) is not { RepresentedMethod: { } representedMethod })
                //No MethodInfo to work with
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates))
            {
                // Some shared generic bodies aren't in the address map at all (todo investigate?).
                // Il2cpp still passes the concrete MethodInfo as the hidden final parameter, so we can use a methodof there if we have one.
                // However, make sure it isn't our OWN hidden MethodInfo arg, because that would turn all unknown calls into recursion
                if (ReferenceEquals(representedMethod, method))
                    continue;

                var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                var hiddenParamIndex = firstArg
                    + (representedMethod.AppContext.InstructionSet.CallingConventionResolver?.ReturnsViaHiddenBuffer(representedMethod) == true ? 1 : 0)
                    + (representedMethod.IsStatic ? 0 : 1) + representedMethod.Parameters.Count;

                if (hiddenParamIndex >= instruction.Operands.Count
                    || AsMethodInfo(instruction.Operands[hiddenParamIndex]) == null)
                    continue;

                instruction.SetOperand(0, representedMethod);
                representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod, method);
                changed = true;
                continue;
            }

            if (candidates.Count < 2)
                continue;

            //Try to actually match on the method name so we don't just replace a call with something else.
            var representedBase = BaseMethodOf(representedMethod);
            if (!candidates.Any(candidate => ReferenceEquals(BaseMethodOf(candidate), representedBase)))
                continue;

            instruction.SetOperand(0, representedMethod);
            representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod, method);
            changed = true;
        }

        return changed;
    }

    // Offset of Il2CppClass::vtable, VirtualInvokeData entries of {methodPtr, MethodInfo*}.
    // TODO this is almost certainly not correct on every version
    private const long VTableOffset64 = 0x138;
    private const long VTableOffset32 = 0xC0;
    
    // Resolves virtual dispatch through <c>[klass + vtableOffset + slot * sizeof(VirtualInvokeData)]</c>
    // as long as the klass local's represented type is known.
    public static bool ResolveVirtualCalls(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = pointerSize == 8 ? VTableOffset64 : VTableOffset32;
        var invokeDataSize = 2L * pointerSize;
        var changed = false;

        var loads = new Dictionary<LocalVariable, MemoryOperand>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is MemoryOperand { Index: null, Scale: 0 } load)
                loads[destination] = load;
        }

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.IndirectCall)
                continue;

            if (SlotLoad(instruction.Operands[0]) is not { } target
                || target.Base is not LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } receiverType } } klassLocal)
                continue;

            var offset = target.Addend - vtableOffset;
            if (offset < 0 || offset % invokeDataSize != 0)
                continue;

            var slot = (int)(offset / invokeDataSize);
            if (ResolveVTableSlot(method.AppContext, receiverType, slot) is not { } resolved)
                continue;

            var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;

            instruction.OpCode = OpCode.Call; // same operand layout as IndirectCall, and we've resolved it now
            instruction.SetOperand(0, resolved);
            resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, resolved, method);

            // the MethodInfo field is also the same method, name it, for cleanliness and so it can
            // serve as a hidden final parameter if needed
            for (var i = 1; i < instruction.Operands.Count && assembly != null; i++)
            {
                if (SlotLoad(instruction.Operands[i]) is { } methodInfoLoad
                    && ReferenceEquals(methodInfoLoad.Base, klassLocal)
                    && methodInfoLoad.Addend == target.Addend + pointerSize)
                    instruction.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            }

            changed = true;
        }

        return changed;

        MemoryOperand? SlotLoad(IOperand operand) => operand switch
        {
            MemoryOperand { Index: null, Scale: 0 } inlined => inlined,
            LocalVariable local when loads.TryGetValue(local, out var load) => load,
            _ => null
        };
    }

    private static MethodAnalysisContext? ResolveVTableSlot(ApplicationAnalysisContext appContext, TypeAnalysisContext type, int slot)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? type.Definition;

        if (definition == null || slot >= definition.VtableCount)
            return null;

        if (appContext.ResolveContextForMethod(definition.VTable[slot]) is { } implementation)
            return implementation;

        // an abstract method has no implementation, try to resolve it
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
        {
            if (declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot) is { } declaration)
                return declaration;
        }

        return null;
    }

    private static MethodAnalysisContext BaseMethodOf(MethodAnalysisContext method) =>
        method is ConcreteGenericMethodAnalysisContext { BaseMethodContext: { } baseMethod } ? baseMethod : method;

    private static RuntimeMethodInfoAnalysisContext? GetMethodInfoArgument(Instruction call)
    {
        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;

        for (var i = call.Operands.Count - 1; i >= firstArg; i--)
        {
            if (AsMethodInfo(call.Operands[i]) is { } methodInfo)
                return methodInfo;
        }

        return null;
    }

    private static RuntimeMethodInfoAnalysisContext? AsMethodInfo(IOperand operand) =>
        operand switch
        {
            RuntimeMethodInfoAnalysisContext methodInfo => methodInfo,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext methodInfoLocal } => methodInfoLocal,
            _ => null
        };

    private static void HandleKeyFunction(ApplicationAnalysisContext appContext, Instruction instruction, ulong target, BaseKeyFunctionAddresses kFA)
    {
        var keyFunctionName = "";
        if (target == kFA.il2cpp_codegen_initialize_method || target == kFA.il2cpp_codegen_initialize_runtime_metadata)
        {
            if (appContext.MetadataVersion < 27)
            {
                keyFunctionName = nameof(kFA.il2cpp_codegen_initialize_method);
            }
            else
            {
                keyFunctionName = nameof(kFA.il2cpp_codegen_initialize_runtime_metadata);
            }
        }
        else
        {
            var pairs = kFA.Pairs.ToList();
            var key = pairs.FirstOrDefault(pair => pair.Value == target).Key;
            if (key == null)
                return;
            keyFunctionName = key;
        }

        if (keyFunctionName != "")
            instruction.SetOperand(0, new StringLiteral(keyFunctionName));
    }

    // Because of il2cpp fields (like cctor_finished_or_no_cctor) [local @ reg+offset] sometimes can't be resolved, but this works for now
    private static void ResolveGetter(MethodAnalysisContext method)
    {
        if (!method.Name.StartsWith("get_"))
            return;

        // Default get: Return [this @ reg+offset]
        var instructions = method.ControlFlowGraph!.Instructions;
        if (instructions.Count == 1)
        {
            var instr = instructions[0];

            if (instr.OpCode != OpCode.Return
                || instr.Operands.Count < 1
                || instr.Operands[0] is not MemoryOperand memory
                || memory.Index != null || memory.Scale != 0
                || memory.Base is not LocalVariable local)
                return;

            var fieldName = $"<{method.Name[4..]}>k__BackingField";

            var field = method.DeclaringType!.Fields.Find(f => f.Name == fieldName);
            if (field == null)
                return;

            instr.SetOperand(0, new FieldReference(field, local, (int)memory.Addend));
        }
    }
}
