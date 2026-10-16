using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Maps calls to KeyFunctionAddresses to their underlying IL opcodes. E.g. il2cpp_codegen_object_new => newobj.
/// Eventually will include box/unbox/throw/etc
/// </summary>
public static class KeyFunctionRecovery
{
    //All of these have the same params in the same order so we treat them as equal.
    private static readonly HashSet<string> ObjectNewFunctions =
    [
        "il2cpp_object_new",
        "il2cpp_vm_object_new",
        "il2cpp_codegen_object_new",
    ];

    //These all take the exception to throw as their only real argument.
    private static readonly HashSet<string> RaiseExceptionFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_raise_exception),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_exception_raise),
        nameof(BaseKeyFunctionAddresses.il2cpp_codegen_raise_exception),
    ];

    //Both take the class to box as and a pointer to the value.
    private static readonly HashSet<string> BoxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_value_box),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_box),
    ];

    //Both take the boxed object and return a pointer to the value inside it.
    private static readonly HashSet<string> UnboxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_object_unbox),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_unbox),
    ];

    public static void Run(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        foreach (var instruction in block.Instructions)
        {
            if (instruction.Operands is not [StringLiteral { Value: var keyFunction }, ..])
                continue;

            if (ObjectNewFunctions.Contains(keyFunction))
                RewriteObjectNew(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier))
                RemoveWriteBarrier(instruction);
            else if (RaiseExceptionFunctions.Contains(keyFunction))
                RewriteRaiseException(instruction);
            else if (BoxFunctions.Contains(keyFunction))
                RewriteBox(instruction);
            else if (UnboxFunctions.Contains(keyFunction))
                RewriteUnbox(instruction, method, block);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_vm_reflection_get_type_object))
                RewriteTypeObject(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.InternalCalls_Resolve))
                RewriteInternalCallResolve(instruction, method);
        }
    }

    private static void RemoveWriteBarrier(Instruction instruction)
    {
        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }
    
    private static void RewriteRaiseException(Instruction instruction)
    {
        // A void call has no return value operand, so the exception is one slot earlier
        var exceptionIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

        if (!instruction.IsCall || instruction.Operands.Count <= exceptionIndex)
            return;

        var exception = instruction.Operands[exceptionIndex];

        instruction.OpCode = OpCode.Throw;
        instruction.SetOperands(exception);
    }

    private static void RewriteBox(Instruction instruction)
    {
        // function name, result, class, address of value.
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, TypeAnalysisContext boxedType, var value, ..])
            return;

        instruction.OpCode = OpCode.Box;
        instruction.SetOperands(result, boxedType, value);
    }

    private static void RewriteUnbox(Instruction instruction, MethodAnalysisContext method, Block block)
    {
        // function name, result, the boxed object.
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, var value, ..])
            return;

        // Unlike box, object_unbox carries no class argument, so the type has to come from
        // how the result is used. Without usable evidence the call is left alone and keeps
        // emitting its diagnostic.
        if (FindUnboxType(instruction, method, block, result) is not { } unboxedType)
            return;

        instruction.OpCode = OpCode.Unbox;
        instruction.SetOperands(result, unboxedType, value);

        // Consumers read the unboxed value through the result as a managed pointer; a reference
        // type keeps the object reference itself instead (unbox of a reference type is a cast).
        if (result is LocalVariable resultLocal && unboxedType.IsValueType)
            resultLocal.Type = new ByRefTypeAnalysisContext(unboxedType);
    }

    private static TypeAnalysisContext? FindUnboxType(Instruction call, MethodAnalysisContext method, Block block, IOperand result) =>
        FindUnboxReturnType(call, method, block, result) ?? FindGuardedUnboxType(call, block);

    // Calls end their block in a freshly-built graph, and the guard conditional ends the block
    // before that, so both uses have to be looked for through single-path block chains.
    private const int UnboxEvidenceBlockLimit = 8;

    private static TypeAnalysisContext? FindUnboxReturnType(Instruction call, MethodAnalysisContext method, Block block, IOperand result)
    {
        // The unboxed value handed straight to a return is typed by the return type:
        // `return (T)obj;` lowers to an unbox followed by a load of the value at offset 0.
        var scan = block;
        var startIndex = block.Instructions.IndexOf(call) + 1;

        for (var depth = 0; scan != null && depth < UnboxEvidenceBlockLimit; depth++)
        {
            for (var i = startIndex; i < scan.Instructions.Count; i++)
            {
                var after = scan.Instructions[i];

                if (after.OpCode is OpCode.Jump or OpCode.IndirectJump or OpCode.Throw)
                    return null;

                if (after.OpCode != OpCode.Return)
                    continue;

                if (after.Operands.Count == 1)
                {
                    var returned = after.Operands[0];
                    var consumed = ReferenceEquals(returned, result)
                                   || returned is MemoryOperand { Addend: 0, Base: var returnedBase } && ReferenceEquals(returnedBase, result);

                    if (consumed && IsUsableUnboxType(method.ReturnType))
                        return method.ReturnType;
                }

                return null;
            }

            scan = scan.Successors.Count == 1 ? scan.Successors[0] : null;
            startIndex = 0;
        }

        return null;
    }

    private static TypeAnalysisContext? FindGuardedUnboxType(Instruction call, Block block)
    {
        // The class-load guarding the unbox (the isinst-style check native emits in front of it)
        // describes the type being unboxed. Two shapes carry it, both looked up nearest-first along
        // the blocks feeding the call:
        //  - a Move into a destination that actually holds a class pointer (or a bare typeof load
        //    into an untyped destination); an ordinary typed value local such as an argument or
        //    field load would otherwise be mistaken for the guard's class;
        //  - the guard check itself, whose operands reference the checked class directly. The class's
        //    defining Move often sits beyond a control-flow join the chain cannot cross, while the
        //    check reading it stays on the chain.
        // The walk is a breadth-first sweep (nearest depth first, instructions nearest-first inside
        // each block) over every predecessor: at a join, every incoming edge feeds this same call
        // site, so the guard for it sits on one of those edges rather than being unreachable.
        var visited = new HashSet<Block>();
        var frontier = new Queue<(Block Scan, int StartIndex, int Depth)>();
        frontier.Enqueue((block, block.Instructions.IndexOf(call) - 1, 0));

        while (frontier.Count > 0)
        {
            var (scan, startIndex, depth) = frontier.Dequeue();

            if (depth >= UnboxEvidenceBlockLimit || !visited.Add(scan))
                continue;

            for (var i = startIndex; i >= 0; i--)
            {
                var instruction = scan.Instructions[i];

                if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, var assigned] })
                {
                    if (destination.Type is RuntimeClassTypeAnalysisContext { RepresentedType: var represented } && IsUsableUnboxType(represented))
                        return represented;

                    if (destination.Type == null && assigned is TypeAnalysisContext assignedType && IsUsableUnboxType(UnwrapClass(assignedType)))
                        return UnwrapClass(assignedType);
                }
                else if (instruction.OpCode >= OpCode.CheckEqual && instruction.OpCode <= OpCode.CheckLessOrEqual)
                {
                    var checkedType = FindCheckedClassType(instruction.Operands);
                    if (checkedType != null)
                        return checkedType;
                }
            }

            foreach (var pred in scan.Predecessors)
                frontier.Enqueue((pred, pred.Instructions.Count - 1, depth + 1));
        }

        return null;
    }

    private static TypeAnalysisContext? FindCheckedClassType(OperandList operands)
    {
        foreach (var operand in operands)
        {
            switch (operand)
            {
                case TypeAnalysisContext direct when IsUsableUnboxType(UnwrapClass(direct)):
                    return UnwrapClass(direct);
                case LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented } } when IsUsableUnboxType(represented):
                    return represented;
                case MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var baseRepresented } } } when IsUsableUnboxType(baseRepresented):
                    return baseRepresented;
            }
        }

        return null;
    }

    private static TypeAnalysisContext? UnwrapClass(TypeAnalysisContext? type) =>
        type is RuntimeClassTypeAnalysisContext klass ? klass.RepresentedType : type;

    // IntPtr/UIntPtr are usable: a klass wrapper or typeof load of them is genuine evidence (e.g.
    // EqualityComparerNoAlloc<System.IntPtr> guards with typeof(IntPtr)). Plain value locals typed
    // IntPtr (such as an invoke_impl field) are already excluded by requiring a class wrapper or an
    // untyped destination, so they can no longer masquerade as guard evidence.
    private static bool IsUsableUnboxType(TypeAnalysisContext? type) =>
        type is not null && type.FullName is not ("System.Object" or "System.Void");

    private static void RewriteTypeObject(Instruction instruction)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, TypeAnalysisContext type, ..])
            return;

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, type);
    }

    private static void RewriteInternalCallResolve(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, Immediate nameAddress, ..])
            return;

        if (ThrowHelperRecovery.ReadCStringAtVirtualAddress(method.AppContext, nameAddress.UnsignedValue, 256) is not { } name)
            return;

        if (ResolveInternalCallName(method.AppContext, name) is not { DeclaringType.DeclaringAssembly: { } assembly } resolved)
            return;

        var pointer = new RuntimeMethodInfoAnalysisContext(resolved, assembly);

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, pointer);

        RewriteCachedPointerLoads(method, result, pointer);
    }

    private static void RewriteCachedPointerLoads(MethodAnalysisContext method, IOperand result, RuntimeMethodInfoAnalysisContext pointer)
    {
        var cache = method.ControlFlowGraph!.Instructions
            .Where(i => i is { OpCode: OpCode.Move, Operands: [MemoryOperand { IsConstant: true }, _] })
            .Where(i => ReferenceEquals(i.Operands[1], result))
            .Select(i => ((MemoryOperand)i.Operands[0]).Addend)
            .Distinct()
            .ToList();

        if (cache.Count != 1)
            return;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand { IsConstant: true } load] }
                && load.Addend == cache[0])
                instruction.SetOperands(destination, pointer);
        }
    }

    internal static MethodAnalysisContext? ResolveInternalCallName(ApplicationAnalysisContext appContext, string name)
    {
        var separator = name.IndexOf("::", StringComparison.Ordinal);

        if (separator < 0)
            return null;

        var typeName = name[..separator];
        var signature = name[(separator + 2)..];
        var parenthesis = signature.IndexOf('(');
        var methodName = parenthesis < 0 ? signature : signature[..parenthesis];

        if (appContext.LibCpp2IlContext.ReflectionCache.GetTypeByFullName(typeName) is not { } typeDefinition
            || appContext.ResolveContextForType(typeDefinition) is not { } type)
            return null;

        var candidates = type.Methods.Where(m => m.Name == methodName).ToList();

        if (candidates.Count <= 1)
            return candidates.FirstOrDefault();

        // Overloaded, so fall back on the parameter list in the name
        var parameters = parenthesis < 0 ? "" : signature[(parenthesis + 1)..].TrimEnd(')');
        var count = parameters.Length == 0 ? 0 : parameters.Split(',').Length;

        var byParameterCount = candidates.Where(m => m.Parameters.Count == count).ToList();

        return byParameterCount.Count == 1 ? byParameterCount[0] : null;
    }

    private static void RewriteObjectNew(Instruction instruction)
    {
        // Needs the function name and the result. The class argument (if present) is only used
        // by the parameterless-ctor fallback; the normal path fuses with the follow-up .ctor
        // call, which doesn't need it.
        if (instruction.OpCode != OpCode.Call || instruction.Operands.Count < 2)
            return;

        var result = instruction.Operands[1];
        var klass = instruction.Operands.Count > 2 ? instruction.Operands[2] : null;

        instruction.OpCode = OpCode.Newobj;
        if (klass != null)
            instruction.SetOperands(result, klass);
        else
            instruction.SetOperands(result);
    }
}
