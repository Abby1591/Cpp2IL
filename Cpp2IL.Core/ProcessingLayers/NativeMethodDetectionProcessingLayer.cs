using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Api;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ProcessingLayers;

public class NativeMethodDetectionProcessingLayer : Cpp2IlProcessingLayer
{
    public override string Name => "Native Method Detection";

    public override string Id => "nativemethoddetector";

    public override void Process(ApplicationAnalysisContext appContext, Action<int, int>? progressCallback = null)
    {
        // Force key-function discovery up front so the scan below can skip their addresses. Registering a
        // void stub at one of these addresses changes how X86InstructionSet builds the call (CallVoid with
        // no result operand instead of the unmanaged Call that always carries one), which starves the
        // key-function rewrites that expect a result operand and leaves an unrewritten StringLiteral call.
        var keyFunctionAddresses = appContext.GetOrCreateKeyFunctionAddresses();

        var nativeMethodInfoStack = new Stack<(ulong, bool)>();
        var cppNativeMethodsType = appContext.AssembliesByName["mscorlib"].InjectType(
            "Cpp2ILInjected",
            "CppNativeMethods",
            null,
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract | TypeAttributes.Sealed); //public static class
        foreach (var assemblyAnalysisContext in appContext.Assemblies)
        {
            foreach (var m in assemblyAnalysisContext.Types.SelectMany(t => t.Methods))
            {
                AnalyzeMethod(appContext, m, nativeMethodInfoStack, keyFunctionAddresses);
            }

            if (Cpp2IlApi.LowMemoryMode)
                GC.Collect();
        }

        if (Cpp2IlApi.LowMemoryMode)
            GC.Collect();

        while (nativeMethodInfoStack.Count > 0)
        {
            (var address, var isVoid) = nativeMethodInfoStack.Pop();
            if (keyFunctionAddresses.IsKeyFunctionAddress(address))
                continue;

            if (!appContext.MethodsByAddress.ContainsKey(address))
            {
                var m = new NativeMethodAnalysisContext(cppNativeMethodsType, address, isVoid);
                cppNativeMethodsType.Methods.Add(m);
                appContext.MethodsByAddress.Add(address, [m]);
                AnalyzeMethod(appContext, m, nativeMethodInfoStack, keyFunctionAddresses);
            }
        }
    }

    private static void AnalyzeMethod(ApplicationAnalysisContext appContext, MethodAnalysisContext m, Stack<(ulong, bool)> nativeMethodInfoStack, BaseKeyFunctionAddresses keyFunctionAddresses)
    {
        if (m.UnderlyingPointer == 0)
            return;

        var convertedIsil = appContext.InstructionSet.GetIsilFromMethod(m);

        if (convertedIsil is { Count: 0 })
        {
            return;
        }

        foreach (var instruction in convertedIsil)
        {
            if (instruction.OpCode == OpCode.Call)
            {
                if (TryGetAddressFromInstruction(instruction, out var address) && !appContext.MethodsByAddress.ContainsKey(address) && !keyFunctionAddresses.IsKeyFunctionAddress(address))
                {
                    nativeMethodInfoStack.Push((address, true));
                }
            }
            else if (instruction.OpCode == OpCode.CallVoid)
            {
                if (TryGetAddressFromInstruction(instruction, out var address) && !appContext.MethodsByAddress.ContainsKey(address) && !keyFunctionAddresses.IsKeyFunctionAddress(address))
                {
                    nativeMethodInfoStack.Push((address, m.IsVoid));
                }
            }
        }
    }

    private static bool TryGetAddressFromInstruction(Instruction instruction, out ulong address)
    {
        if (instruction.Operands.Count > 0 && instruction.Operands[0] is Immediate immediate)
        {
            address = immediate.UnsignedValue;
            return true;
        }

        address = default;
        return false;
    }
}
