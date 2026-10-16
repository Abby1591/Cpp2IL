using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public abstract class BaseCallingConventionResolver
{
    public static bool IsFloatingPoint(TypeAnalysisContext type)
        => type == type.AppContext.SystemTypes.SystemSingleType || type == type.AppContext.SystemTypes.SystemDoubleType;

    protected static bool IsFloatingPoint(ParameterAnalysisContext par) => IsFloatingPoint(par.ParameterType);

    public abstract Register ReturnRegister(MethodAnalysisContext ctx);

    public abstract bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx);

    public abstract Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx);

    public abstract IOperand[] ResolveForManaged(MethodAnalysisContext ctx);

    protected abstract (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app);

    // MSVC style: argument slot n is integer register n or float register n, not both
    protected virtual bool UsesShadowedArgumentSlots(ApplicationAnalysisContext app) => false;

    // false when the return buffer pointer lives outside the argument registers (e.g. arm64 uses x8)
    protected virtual bool HiddenBufferConsumesArgumentSlot => true;

    public IOperand[] ResolveForUnmanaged(ApplicationAnalysisContext app, ulong target)
    {
        // We don't know the callee's signature, so preserve every argument register.

        var (integerRegisters, floatRegisters) = RawRegisters(app);
        return integerRegisters.Concat(floatRegisters).Select(name => (IOperand)new Register(null, name)).ToArray();
    }

    public bool HasRawArgumentLayout(Instruction call, ApplicationAnalysisContext app)
    {
        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        if (call.Operands.Count != argBase + integerRegisters.Length + floatRegisters.Length)
            return false;

        for (var i = 0; i < integerRegisters.Length; i++)
            if (RegisterName(call.Operands[argBase + i]) != integerRegisters[i])
                return false;

        for (var i = 0; i < floatRegisters.Length; i++)
            if (RegisterName(call.Operands[argBase + integerRegisters.Length + i]) != floatRegisters[i])
                return false;

        return true;
    }

    public void RemapRawArguments(Instruction call, MethodAnalysisContext resolved, MethodAnalysisContext? caller = null)
    {
        var app = resolved.AppContext;
        var argBase = ArgBase(call);

        var (integerRegisters, floatRegisters) = RawRegisters(app);

        // Stack-passing conventions (x86) have no argument registers to remap. When a call is
        // resolved after initial lifter output (e.g. via MethodInfo), it may still carry the
        // unmanaged operand layout (just target + return register). Rebuild the argument
        // operands from the resolved signature so 'this' and parameters are present.
        // The StackAnalyzer has already replaced StackOffset with LocalVariable("vN", Register("stack_N")),
        // so we must reuse those existing locals rather than creating new Register operands.
        if (integerRegisters.Length == 0 && floatRegisters.Length == 0 && HasRawArgumentLayout(call, app))
        {
            var stackArgs = ResolveForManaged(resolved);

            // Index every LocalVariable in the caller method by its stack-slot register name
            var localsBySlot = new Dictionary<string, LocalVariable>();
            if (caller?.ControlFlowGraph != null)
            {
                foreach (var insn in caller.ControlFlowGraph.Instructions)
                {
                    foreach (var op in insn.Operands)
                    {
                        if (op is LocalVariable { Register.Name: var regName } lv && regName.StartsWith("stack") && !localsBySlot.ContainsKey(regName))
                            localsBySlot[regName] = lv;
                    }
                }
            }

            var rebuilt = new List<IOperand>(argBase + stackArgs.Length);
            for (var i = 0; i < argBase && i < call.Operands.Count; i++)
                rebuilt.Add(call.Operands[i]);

            // Reuse any LocalVariable the stack analysis already created for the slot; otherwise
            // synthesize one here. A raw Register would reach IL emission un-lowered ("Unknown
            // operand: stack[N]"), but LocalVariable operands are collected into method.Locals
            // and loaded via LoadLocal. Locals created after LocalVariables.CreateAll pick up no
            // type, which IlGenerator defaults to object.
            var localsForCall = new Dictionary<string, LocalVariable>();
            foreach (var arg in stackArgs)
            {
                if (arg is StackOffset slot)
                {
                    var name = slot.Offset < 0 ? $"stack_-{-slot.Offset:X}" : $"stack_{slot.Offset:X}";

                    if (!localsBySlot.TryGetValue(name, out var existing) && !localsForCall.TryGetValue(name, out existing))
                    {
                        existing = new LocalVariable(name, new Register(null, name));
                        localsForCall[name] = existing;
                    }

                    rebuilt.Add(existing);
                }
                else
                    rebuilt.Add(arg);
            }

            call.SetOperands(rebuilt);
            return;
        }

        if (!HasRawArgumentLayout(call, app))
            return;

        var slots = new List<(bool IsFloat, bool Emit)>();
        if (ReturnsViaHiddenBuffer(resolved) && HiddenBufferConsumesArgumentSlot)
            slots.Add((false, false));
        if (!resolved.IsStatic)
            slots.Add((false, true));
        foreach (var parameter in resolved.Parameters)
            slots.Add((IsFloatingPoint(parameter), true));
        slots.Add((false, true)); // the MethodInfo argument

        var operands = new List<IOperand>(argBase + slots.Count);
        for (var i = 0; i < argBase; i++)
            operands.Add(call.Operands[i]);

        if (UsesShadowedArgumentSlots(app))
        {
            for (var slot = 0; slot < slots.Count && slot < integerRegisters.Length; slot++)
                if (slots[slot].Emit)
                    operands.Add(call.Operands[argBase + (slots[slot].IsFloat ? integerRegisters.Length + slot : slot)]);
        }
        else
        {
            // independent integer/float counters
            var (integer, floating) = (0, 0);

            foreach (var (isFloat, emit) in slots)
            {
                if (isFloat ? floating >= floatRegisters.Length : integer >= integerRegisters.Length)
                    break;

                var operand = call.Operands[argBase + (isFloat ? integerRegisters.Length + floating++ : integer++)];
                if (emit)
                    operands.Add(operand);
            }
        }

        call.SetOperands(operands);
    }

    protected static int ArgBase(Instruction call) => call.OpCode is OpCode.CallVoid ? 1 : 2;

    private static string? RegisterName(IOperand operand) => operand switch
    {
        Register register => register.Name,
        LocalVariable { Register.Name: var name } => name,
        _ => null
    };
}
