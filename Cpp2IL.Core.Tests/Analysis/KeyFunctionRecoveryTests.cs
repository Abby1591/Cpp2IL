using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class KeyFunctionRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static InjectedMethodAnalysisContext MakeMethod(List<Instruction> instructions, TypeAnalysisContext returnType)
    {
        var method = MakeMethod(returnType);
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        return method;
    }

    private static InjectedMethodAnalysisContext MakeMethod(ISILControlFlowGraph graph, TypeAnalysisContext returnType)
    {
        var method = MakeMethod(returnType);
        method.ControlFlowGraph = graph;
        return method;
    }

    private static InjectedMethodAnalysisContext MakeMethod(TypeAnalysisContext returnType)
    {
        var method = new InjectedMethodAnalysisContext(
            Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType,
            "UnboxCaller",
            returnType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        method.Locals = [];
        method.ParameterLocals = [];
        method.AnalysisWarnings = [];
        return method;
    }

    private static void AssertUnbox(Instruction instruction, IOperand result, TypeAnalysisContext type, IOperand value, string? because = null)
    {
        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Unbox), because ?? "expected the object_unbox call to be rewritten");
        Assert.That(instruction.Operands, Has.Count.EqualTo(3), "unbox takes destination, type and object");
        Assert.That(instruction.Operands[0], Is.SameAs(result));
        Assert.That(instruction.Operands[1], Is.SameAs(type), because);
        Assert.That(instruction.Operands[2], Is.SameAs(value));
    }

    [Test]
    public void UnboxAfterClassGuardUsesTheGuardClass()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var klass = new LocalVariable("klass", new Register(null, "eax"), new RuntimeClassTypeAnalysisContext(intType, intType.DeclaringAssembly));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, new MemoryOperand(addend: 0x10)),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[1], result, intType, obj);
    }

    [Test]
    public void UnboxTypeComesFromTheTypeLoadWhenTheDestinationIsUntyped()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var klass = new LocalVariable("klass", new Register(null, "eax"));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, intType),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[1], result, intType, obj);
    }

    [Test]
    public void UnboxFeedingAReturnUsesTheReturnType()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(1, OpCode.Return, new MemoryOperand(result, null, 0)),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[0], result, intType, obj);
    }

    [Test]
    public void UnboxWithoutUsableEvidenceKeepsItsCall()
    {
        var systemObject = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType;
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(1, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, systemObject));

        Assert.That(instructions[0].OpCode, Is.EqualTo(OpCode.Call), "no usable type evidence, so the diagnostic call must survive");
        Assert.That(instructions[0].Operands, Has.Count.EqualTo(3));
    }

    [Test]
    public void ObjectClassGuardIsSkippedInFavourOfTheCheckedType()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var intType = appContext.SystemTypes.SystemInt32Type;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var intKlass = new LocalVariable("intKlass", new Register(null, "eax"), new RuntimeClassTypeAnalysisContext(intType, intType.DeclaringAssembly));
        var objectKlass = new LocalVariable("objectKlass", new Register(null, "ebx"), new RuntimeClassTypeAnalysisContext(systemObject, systemObject.DeclaringAssembly));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, intKlass, new MemoryOperand(addend: 0x10)),
            new(1, OpCode.Move, objectKlass, new MemoryOperand(addend: 0x10)),
            new(2, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(3, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[2], result, intType, obj);
    }

    [Test]
    public void VmObjectUnboxIsAlsoRewritten()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, Str("il2cpp_vm_object_unbox"), result, obj),
            new(1, OpCode.Return, new MemoryOperand(result, null, 0)),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[0], result, intType, obj);
    }

    [Test]
    public void UnboxGuardSkipsPlainValueLocals()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var intType = appContext.SystemTypes.SystemInt32Type;
        var singleType = appContext.SystemTypes.SystemSingleType;
        var plainValue = new LocalVariable("plainValue", new Register(null, "ebx"), singleType);
        var intKlass = new LocalVariable("intKlass", new Register(null, "eax"), new RuntimeClassTypeAnalysisContext(intType, intType.DeclaringAssembly));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, intKlass, new MemoryOperand(addend: 0x10)),
            new(1, OpCode.Move, plainValue, new MemoryOperand(addend: 0x8)),
            new(2, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(3, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[2], result, intType, obj, "an ordinary typed value local must not be mistaken for the guard's class");
    }

    [Test]
    public void UnboxGuardCheckWithAKlassWrapperOfIntPtrSuppliesTheClass()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var intPtrType = appContext.SystemTypes.SystemIntPtrType;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var objectKlass = new LocalVariable("objectKlass", new Register(null, "ebx"), new RuntimeClassTypeAnalysisContext(systemObject, systemObject.DeclaringAssembly));
        var intPtrKlass = new LocalVariable("intPtrKlass", new Register(null, "eax"), new RuntimeClassTypeAnalysisContext(intPtrType, intPtrType.DeclaringAssembly));
        var flag = new LocalVariable("flag", new Register(null, "edi"));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, flag, new MemoryOperand(objectKlass, null, 0x10), new MemoryOperand(intPtrKlass, null, 0x10)),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intPtrType));

        AssertUnbox(instructions[1], result, intPtrType, obj, "a class wrapper of IntPtr is genuine evidence, e.g. EqualityComparerNoAlloc<System.IntPtr>");
    }

    [Test]
    public void UnboxGuardSkipsPlainIntPtrValueLocals()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var intType = appContext.SystemTypes.SystemInt32Type;
        var intPtrType = appContext.SystemTypes.SystemIntPtrType;
        var plainValue = new LocalVariable("invokeImpl", new Register(null, "ebx"), intPtrType);
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, plainValue, new MemoryOperand(addend: 0x8)),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        Assert.That(instructions[1].OpCode, Is.EqualTo(OpCode.Call), "a plain IntPtr value local such as an invoke_impl field is not guard evidence");
    }

    [Test]
    public void UnboxGuardCheckSuppliesTheClassWhenItsLoadIsBeyondAJoin()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var intType = appContext.SystemTypes.SystemInt32Type;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var objectKlass = new LocalVariable("objectKlass", new Register(null, "ebx"), new RuntimeClassTypeAnalysisContext(systemObject, systemObject.DeclaringAssembly));
        var intKlass = new LocalVariable("intKlass", new Register(null, "eax"), new RuntimeClassTypeAnalysisContext(intType, intType.DeclaringAssembly));
        var flag = new LocalVariable("flag", new Register(null, "edi"));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, flag, new MemoryOperand(objectKlass, null, 0x10), new MemoryOperand(intKlass, null, 0x10)),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[1], result, intType, obj, "the guard's class load sits beyond a join, so the check operands carry the type");
    }

    [Test]
    public void UnboxGuardCheckWithADirectTypeOperandSuppliesTheClass()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var flag = new LocalVariable("flag", new Register(null, "edi"));
        var value = new LocalVariable("value", new Register(null, "eax"));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, flag, new MemoryOperand(value, null, 0), intType),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[1], result, intType, obj);
    }

    [Test]
    public void UnboxGuardCheckWithoutAClassOperandKeepsTheCall()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var flag = new LocalVariable("flag", new Register(null, "edi"));
        var length = new LocalVariable("length", new Register(null, "eax"));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckLess, flag, new MemoryOperand(length, null, 0x8), Imm(0)),
            new(1, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(2, OpCode.Return),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        Assert.That(instructions[1].OpCode, Is.EqualTo(OpCode.Call), "an unrelated check must not be mistaken for the guard");
    }

    [Test]
    public void UnboxResultOfAValueTypeIsTypedAsAByRef()
    {
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(1, OpCode.Return, new MemoryOperand(result, null, 0)),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, intType));

        AssertUnbox(instructions[0], result, intType, obj);
        Assert.That(result.Type, Is.InstanceOf<ByRefTypeAnalysisContext>(), "the unboxed result is a managed pointer to the value");
        Assert.That(((ByRefTypeAnalysisContext)result.Type!).ElementType, Is.SameAs(intType));
    }

    [Test]
    public void UnboxResultOfAReferenceTypeIsNotABYRef()
    {
        var stringType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemStringType;
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(1, OpCode.Return, new MemoryOperand(result, null, 0)),
        };

        KeyFunctionRecovery.Run(MakeMethod(instructions, stringType));

        AssertUnbox(instructions[0], result, stringType, obj);
        Assert.That(result.Type, Is.Null, "unboxing to a reference type keeps the object reference, not a pointer to it");
    }

    [Test]
    public void UnboxGuardCheckIsFoundAcrossAControlFlowJoin()
    {
        // Mirrors the isinst-style guard sitting one block away from the call: the call block has
        // two predecessors (the conditional's two outgoing paths merge in front of it), so the walk
        // must cross the join to reach the check rather than giving up at the merge.
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var intType = appContext.SystemTypes.SystemInt32Type;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var objectKlass = new LocalVariable("objectKlass", new Register(null, "ebx"), new RuntimeClassTypeAnalysisContext(systemObject, systemObject.DeclaringAssembly));
        var intKlass = new LocalVariable("intKlass", new Register(null, "eax"), new RuntimeClassTypeAnalysisContext(intType, intType.DeclaringAssembly));
        var flag = new LocalVariable("flag", new Register(null, "edi"));
        var obj = new LocalVariable("obj", new Register(null, "ecx"));
        var result = new LocalVariable("result", new Register(null, "edx"));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, flag, new MemoryOperand(objectKlass, null, 0x10), new MemoryOperand(intKlass, null, 0x10)),
            new(1, OpCode.ConditionalJump, Imm(3), flag),
            new(2, OpCode.Jump, Imm(4)),
            new(3, OpCode.Jump, Imm(4)),
            new(4, OpCode.Call, Str("il2cpp_object_unbox"), result, obj),
            new(5, OpCode.Return),
        };

        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is not (OpCode.Jump or OpCode.ConditionalJump))
                continue;

            instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);
        }

        var graph = new ISILControlFlowGraph(instructions);
        var callBlock = graph.Blocks.Single(b => b.Instructions.Any(i => ReferenceEquals(i, instructions[4])));
        Assert.That(callBlock.Predecessors.Count, Is.EqualTo(2), "the call must sit in a join block for this test");

        KeyFunctionRecovery.Run(MakeMethod(graph, intType));

        AssertUnbox(instructions[4], result, intType, obj, "the guard check lives in a predecessor branch, so the walk must cross the join");
    }
}
