using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class IlGeneratorTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void StaticCall_DoesNotLoadMethodInfoOperand()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;
        var systemInt = appContext.SystemTypes.SystemInt32Type;

        var callerContext = new InjectedMethodAnalysisContext(
            systemObject,
            "Caller",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var targetContext = new InjectedMethodAnalysisContext(
            systemObject,
            "TargetStatic",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [systemInt, systemInt]);

        var x = new LocalVariable("x", new Register(null, "x"));
        var y = new LocalVariable("y", new Register(null, "y"));

        var instructions = new List<Instruction>
        {
            
            new(0, OpCode.Move, x, Imm(5)),
            new(1, OpCode.Move, y, Imm(10)),
            // Operand layout: target, arg0, arg1, trailing-non-parameter.
            new(2, OpCode.CallVoid, targetContext, x, y, Imm(999)),
            new(3, OpCode.Return),
        };

        callerContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        callerContext.Locals = [x, y];
        callerContext.ParameterLocals = [];
        callerContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "IlGeneratorTestType", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        var callerMethodDef = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(callerMethodDef);

        var targetMethodDef = new MethodDefinition("TargetStatic", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Int32]));
        typeDef.Methods.Add(targetMethodDef);
        targetContext.PutExtraData("AsmResolverMethod", targetMethodDef);

        IlGenerator.GenerateIl(callerContext, callerMethodDef);

        var il = callerMethodDef.CilMethodBody!.Instructions;

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True, "expected generated method to contain a call");
        Assert.That(il.Any(i => i.Operand is int intOperand && intOperand == 999), Is.False,
            "trailing non-parameter operand must not be emitted as a call argument");
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloc), Is.EqualTo(2),
            "expected exactly two Ldloc instructions for the two parameters of the target method");
    }

    private static CilInstructionCollection GenerateIlForMove(Func<LocalVariable, LocalVariable, IOperand> makeSource, bool omitIndexLocalFromLocalsList = false)
        => GenerateIlForMove((baseLocal, indexLocal, dest) => new Instruction(0, OpCode.Move, dest, makeSource(baseLocal, indexLocal)), omitIndexLocalFromLocalsList);

    private static CilInstructionCollection GenerateIlForMove(Func<LocalVariable, LocalVariable, LocalVariable, Instruction> makeInstruction, bool omitIndexLocalFromLocalsList = false)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;

        var callerContext = new InjectedMethodAnalysisContext(
            systemObject,
            "Caller",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var dest = new LocalVariable("dest", new Register(null, "rax"));
        var baseLocal = new LocalVariable("arr", new Register(null, "rcx"));
        var indexLocal = new LocalVariable("idx", new Register(null, "rdx"));

        var instructions = new List<Instruction>
        {
            makeInstruction(baseLocal, indexLocal, dest),
            new(1, OpCode.Return),
        };

        callerContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        // Instruction operands may introduce their own locals (typed sources), so collect them all.
        callerContext.Locals = instructions.SelectMany(i => i.Operands.OfType<LocalVariable>())
            .Concat([dest, baseLocal, indexLocal])
            .Distinct()
            .ToList();
        if (omitIndexLocalFromLocalsList)
            callerContext.Locals.Remove(indexLocal);
        callerContext.ParameterLocals = [];
        callerContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "IlGeneratorTestType", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        var callerMethodDef = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(callerMethodDef);

        IlGenerator.GenerateIl(callerContext, callerMethodDef);

        return callerMethodDef.CilMethodBody!.Instructions;
    }

    private static void AssertNoUnmanagedDiagnostic(CilInstructionCollection il)
    {
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string s && s.Contains("Unmanaged memory load")),
            Is.False, "native addressing forms must not produce unmanaged-memory-load diagnostics");
    }

    // The test game's contexts don't run through the output format that attaches the AsmResolver
    // TypeDefinition, but IL generation needs it to build local signatures from a typed local.
    private static void AttachScratchAsmResolverType(TypeAnalysisContext type)
    {
        var module = new ModuleDefinition("Scratch.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var def = new TypeDefinition(type.Namespace, type.Name, TypeAttributes.Public | TypeAttributes.Sealed,
            module.CorLibTypeFactory.Object.ToTypeDefOrRef());
        module.TopLevelTypes.Add(def);
        type.PutExtraData("AsmResolverType", def);
    }

    [Test]
    public void ConstantAddressLoad_EmitsAddressAndLdind()
    {
        // il2cpp global reads like mov eax, ds:[12AFEB38h] must lower to a raw address load.
        var il = GenerateIlForMove((_, _) => new MemoryOperand(addend: 0x12AFEB38));

        AssertNoUnmanagedDiagnostic(il);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4 && (int)i.Operand! == 0x12AFEB38), Is.True,
            "expected the absolute address to be pushed");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldind_I4), Is.True);
    }

    [Test]
    public void EmptyMemoryLoad_EmitsNullPlaceholderWithoutDiagnostic()
    {
        // fs:[0] (the SEH chain slot) lowers to an empty memory operand; the placeholder is
        // intentional, but the diagnostic is noise for a recognised pattern.
        var il = GenerateIlForMove((_, _) => new MemoryOperand());

        AssertNoUnmanagedDiagnostic(il);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4_0), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.True);
    }

    [Test]
    public void ScaledIndexLoad_EmitsAddressComputation()
    {
        // [array + 0x10 + index*4]: raw pointer arithmetic over an il2cpp array object.
        var il = GenerateIlForMove((arr, idx) => new MemoryOperand(arr, idx, addend: 0x10, scale: 4));

        AssertNoUnmanagedDiagnostic(il);

        var codes = il.Select(i => i.OpCode).ToList();
        var firstLdloc = codes.IndexOf(CilOpCodes.Ldloc);
        var secondLdloc = codes.IndexOf(CilOpCodes.Ldloc, firstLdloc + 1);
        Assert.That(firstLdloc, Is.GreaterThanOrEqualTo(0), "expected base local to be loaded");
        Assert.That(secondLdloc, Is.GreaterThan(firstLdloc), "expected index local to be loaded after base");
        Assert.That(codes.IndexOf(CilOpCodes.Mul), Is.GreaterThan(secondLdloc), "expected index*scale multiply");
        Assert.That(codes.Count(c => c == CilOpCodes.Add), Is.GreaterThanOrEqualTo(2),
            "expected scale product and addend to be added into the address");
        Assert.That(codes.IndexOf(CilOpCodes.Ldind_I4), Is.GreaterThan(codes.IndexOf(CilOpCodes.Conv_I)),
            "expected the computed address to be converted and dereferenced");
    }

    [Test]
    public void MemoryIndexLocalMissingFromLocalsList_IsReAddedAtIlGeneration()
    {
        // RemoveUnused can't see locals that are only read through a memory operand's index
        // (Sources carries the MemoryOperand, not its components), so the index local can already
        // be gone from context.Locals by the time IL generation runs. GenerateIl must re-add it
        // like it already does for the base, or GenerateIl throws KeyNotFoundException.
        var il = GenerateIlForMove(
            (arr, idx) => new MemoryOperand(arr, idx, addend: 0x10, scale: 4),
            omitIndexLocalFromLocalsList: true);

        AssertNoUnmanagedDiagnostic(il);

        var codes = il.Select(i => i.OpCode).ToList();
        var firstLdloc = codes.IndexOf(CilOpCodes.Ldloc);
        var secondLdloc = codes.IndexOf(CilOpCodes.Ldloc, firstLdloc + 1);
        Assert.That(firstLdloc, Is.GreaterThanOrEqualTo(0), "expected base local to be loaded");
        Assert.That(secondLdloc, Is.GreaterThan(firstLdloc), "expected the re-added index local to be loaded after base");
        Assert.That(codes.IndexOf(CilOpCodes.Mul), Is.GreaterThan(secondLdloc), "expected index*scale multiply");
    }

    [Test]
    public void TypedValueStoreToFrameSlot_EmitsStobjWithExactWidth()
    {
        // A struct/long value written through [frame + displacement] (e.g. the native copy before
        // il2cpp_value_box) must store its full width; stind.i4 would truncate to 4 bytes.
        var systemInt64 = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt64Type;
        AttachScratchAsmResolverType(systemInt64);
        var typedSource = new LocalVariable("v", new Register(null, "rax"), systemInt64);

        var il = GenerateIlForMove((baseLocal, _, _) =>
        {
            var dest = new MemoryOperand(baseLocal, null, 8);
            return new Instruction(0, OpCode.Move, dest, typedSource);
        });

        var stobj = il.FirstOrDefault(i => i.OpCode == CilOpCodes.Stobj);
        Assert.That(stobj, Is.Not.Null, "expected stobj for a typed value-type store through [local + displacement]");
        Assert.That(stobj!.Operand!.ToString(), Does.Contain("Int64"));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stind_I4), Is.False,
            "stobj replaces the best-effort stind.i4 when the stored type is known");
    }

    [Test]
    public void UntypedValueStoreToFrameSlot_KeepsBestEffortStind()
    {
        // Register-backed sources have no managed type; keep the existing 4-byte best effort.
        var untypedSource = new LocalVariable("v", new Register(null, "rax"));

        var il = GenerateIlForMove((baseLocal, _, _) =>
        {
            var dest = new MemoryOperand(baseLocal, null, 8);
            return new Instruction(0, OpCode.Move, dest, untypedSource);
        });

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stind_I4), Is.True,
            "expected the best-effort stind.i4 fallback for an untyped source");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.False);
    }

    [Test]
    public void ReferenceValueStoreToFrameSlot_KeepsPointerWidthStore()
    {
        // A reference stored through [frame + displacement] is a pointer write, not a stobj.
        var systemObject = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType;
        AttachScratchAsmResolverType(systemObject);
        var refSource = new LocalVariable("v", new Register(null, "rax"), systemObject);

        var il = GenerateIlForMove((baseLocal, _, _) =>
        {
            var dest = new MemoryOperand(baseLocal, null, 8);
            return new Instruction(0, OpCode.Move, dest, refSource);
        });

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.False,
            "reference-typed values must not be stored with stobj");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stind_I4), Is.True);
    }

    [Test]
    public void UnboxEmitsTypedUnboxAndStackNeutralResult()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;
        var systemInt = appContext.SystemTypes.SystemInt32Type;
        AttachScratchAsmResolverType(systemObject);
        AttachScratchAsmResolverType(systemInt);

        var callerContext = new InjectedMethodAnalysisContext(
            systemObject,
            "Caller",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var obj = new LocalVariable("obj", new Register(null, "rcx"), systemObject);
        var dest = new LocalVariable("dest", new Register(null, "rax"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Unbox, dest, systemInt, obj),
            new(1, OpCode.Return),
        };

        callerContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        callerContext.Locals = [obj, dest];
        callerContext.ParameterLocals = [];
        callerContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "IlGeneratorTestType", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        var callerMethodDef = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(callerMethodDef);

        IlGenerator.GenerateIl(callerContext, callerMethodDef);

        var il = callerMethodDef.CilMethodBody!.Instructions;
        var unboxIndex = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Unbox);

        Assert.That(unboxIndex, Is.GreaterThanOrEqualTo(0), "expected a typed unbox to be emitted");
        Assert.That(il[unboxIndex].Operand!.ToString(), Does.Contain("Int32"), "unbox must carry the unboxed type token");
        Assert.That(il.Take(unboxIndex).Any(i => i.OpCode == CilOpCodes.Ldloc), Is.True,
            "expected the boxed object to be loaded onto the stack");
        Assert.That(il.Skip(unboxIndex + 1).Any(i => i.OpCode == CilOpCodes.Stloc), Is.True,
            "expected the managed pointer result to be stored");
    }
}