using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using System.Linq;

namespace Cpp2IL.Core.Tests.Isil;

public class X86CallingConventionResolverTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    static MethodAnalysisContext GetMethod(string typeName, string methodName, int parameterCount = -1)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = appContext.AssembliesByName["mscorlib"];
        var type = mscorlib.GetTypeByFullName(typeName);
        Assert.That(type, Is.Not.Null, $"expected to find {typeName} in mscorlib");
        var method = parameterCount >= 0 ? type!.GetMethod(methodName, parameterCount) : type!.GetMethod(methodName);
        Assert.That(method, Is.Not.Null, $"expected to find {typeName}::{methodName}");
        return method!;
    }

    [Test]
    public void Dispatches64BitInstanceMethodToX64Resolver()
    {
        // The test games are x64; the dispatcher must preserve x64 register-based layout.
        var ctx = GetMethod("System.AppDomain", "DoDomainUnload");
        var resolver = new X86CallingConventionResolver();
        var body = resolver.ResolveForManagedBody(ctx);
        var callsite = resolver.ResolveForManaged(ctx);

        // x64 MSVC: this in rcx, MethodInfo in rdx (or later slots)
        Assert.That(body, Has.Length.EqualTo(2));
        Assert.That(body[0], Is.InstanceOf<Register>());
        Assert.That(((Register)body[0]).Name, Is.EqualTo("rcx"));
        Assert.That(callsite[0], Is.InstanceOf<Register>());
        Assert.That(((Register)callsite[0]).Name, Is.EqualTo("rcx"));
    }

    [Test]
    public void Dispatches64BitStaticMethodToX64Resolver()
    {
        var ctx = GetMethod("System.String", "op_Equality", 2);
        var resolver = new X86CallingConventionResolver();
        var body = resolver.ResolveForManagedBody(ctx);
        var callsite = resolver.ResolveForManaged(ctx);

        // x64 MSVC static: param0=rcx, param1=rdx, MethodInfo=r8
        Assert.That(body, Has.Length.EqualTo(3));
        Assert.That(((Register)body[0]).Name, Is.EqualTo("rcx"));
        Assert.That(((Register)body[1]).Name, Is.EqualTo("rdx"));
        Assert.That(((Register)body[2]).Name, Is.EqualTo("r8"));
        Assert.That(((Register)callsite[0]).Name, Is.EqualTo("rcx"));
        Assert.That(((Register)callsite[1]).Name, Is.EqualTo("rdx"));
        Assert.That(((Register)callsite[2]).Name, Is.EqualTo("r8"));
    }

    [Test]
    public void ReturnRegisterIsXmm0ForFloatsOnBothBitnesses()
    {
        var ctx = GetMethod("System.Math", "Sqrt", 1);
        var resolver = new X86CallingConventionResolver();
        var reg = resolver.ReturnRegister(ctx);
        Assert.That(reg.Name, Is.EqualTo("xmm0"));
    }

    [Test]
    public void X86BodyLayoutGivesDoubleParametersTwoStackSlots()
    {
        // MSVC x86 pushes a double as two 4-byte stack slots, so the trailing MethodInfo
        // pointer sits at [ebp+0xC], not [ebp+0x8] - one slot later than a naive layout.
        var ctx = GetMethod("System.Math", "Sqrt", 1); // static double Sqrt(double)
        var resolver = new X86CallingConventionResolver();

        var body = resolver.ResolveStackArguments(ctx, entryRelative: true);
        var callsite = resolver.ResolveStackArguments(ctx, entryRelative: false);

        Assert.That(body, Has.Length.EqualTo(2));
        Assert.That(body[0], Is.EqualTo(new StackOffset(4)), "double parameter occupies [esp+4..esp+C)");
        Assert.That(body[1], Is.EqualTo(new StackOffset(0xC)), "MethodInfo follows the 8-byte double");

        Assert.That(callsite, Has.Length.EqualTo(2));
        Assert.That(callsite[0], Is.EqualTo(new StackOffset(0)));
        Assert.That(callsite[1], Is.EqualTo(new StackOffset(8)));
    }

    [Test]
    public void X86BodyLayoutKeepsPointerSizedParametersOneSlotEach()
    {
        var ctx = GetMethod("System.String", "op_Equality", 2); // static bool op_Equality(string, string)
        var resolver = new X86CallingConventionResolver();

        var body = resolver.ResolveStackArguments(ctx, entryRelative: true);

        Assert.That(body, Has.Length.EqualTo(3));
        Assert.That(body[0], Is.EqualTo(new StackOffset(4)));
        Assert.That(body[1], Is.EqualTo(new StackOffset(8)));
        Assert.That(body[2], Is.EqualTo(new StackOffset(0xC)));
    }

    [Test]
    public void StackArgumentSizeMatchesMsvcX86Granules()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];

        TypeAnalysisContext Type(string fullName)
        {
            var type = mscorlib.GetTypeByFullName(fullName);
            Assert.That(type, Is.Not.Null, $"expected to find {fullName}");
            return type!;
        }

        var pointerSize = app.Binary.PointerSizeBytes;
        Assert.That(X86CallingConventionResolver.StackArgumentSize(Type("System.Double"), pointerSize), Is.EqualTo(8));
        Assert.That(X86CallingConventionResolver.StackArgumentSize(Type("System.Int32"), pointerSize), Is.EqualTo(4));
        Assert.That(X86CallingConventionResolver.StackArgumentSize(Type("System.Decimal"), pointerSize), Is.EqualTo(16));
        Assert.That(X86CallingConventionResolver.StackArgumentSize(Type("System.String"), pointerSize), Is.EqualTo(4), "reference types pass as a pointer");
    }

    [Test]
    public void StackPassingRebuildReplacesUnmanagedLayoutWithStackLocals()
    {
        // Simulate the x86 all-stack convention by overriding the register lists. A resolved
        // call still carrying the unmanaged layout (just target + result) must be rebuilt with
        // stack-slot operands: reuse caller locals where a slot was already analysed, and
        // synthesize LocalVariables for missing slots. A raw Register would reach IL emission
        // un-lowered as "Unknown operand: stack[N]".
        var resolved = GetMethod("System.AppDomain", "DoDomainUnload");
        var caller = GetMethod("System.String", "op_Equality", 2);

        var existingStack4 = new LocalVariable("v9", new Register(null, "stack_4"));
        caller.ControlFlowGraph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, new LocalVariable("v8", new Register(null, "rax")), existingStack4),
            new(1, OpCode.Return),
        ]);

        var call = new Instruction(0, OpCode.Call, new Immediate(0x1234), new Register(null, "rax"));

        new StackPassingResolver().RemapRawArguments(call, resolved, caller);

        // target + result preserved, then this, param, MethodInfo from the stack layout
        Assert.That(call.Operands, Has.Count.EqualTo(5));
        Assert.That(call.Operands[0], Is.EqualTo(new Immediate(0x1234)));
        Assert.That(call.Operands[1], Is.InstanceOf<Register>());

        Assert.That(call.Operands[2], Is.InstanceOf<LocalVariable>());
        Assert.That(((LocalVariable)call.Operands[2]).Register.Name, Is.EqualTo("stack_0"));

        Assert.That(call.Operands[3], Is.SameAs(existingStack4), "existing local for stack_4 should be reused");

        Assert.That(call.Operands[4], Is.InstanceOf<LocalVariable>());
        Assert.That(((LocalVariable)call.Operands[4]).Register.Name, Is.EqualTo("stack_8"));

        // every stack argument must be a LocalVariable, never a raw Register
        for (var i = 2; i < call.Operands.Count; i++)
            Assert.That(call.Operands[i], Is.InstanceOf<LocalVariable>(), $"operand {i} must be a LocalVariable");
    }

    [Test]
    public void RegisterPassingRebuildLeavesNonMatchingLayoutUntouched()
    {
        // On a register-passing convention (x64) a partial unmanaged layout fails
        // HasRawArgumentLayout, so RemapRawArguments must be a no-op rather than rebuild.
        var resolved = GetMethod("System.AppDomain", "DoDomainUnload");
        var call = new Instruction(0, OpCode.Call, new Immediate(0x1234), new Register(null, "rax"));

        new X86CallingConventionResolver().RemapRawArguments(call, resolved);

        Assert.That(call.Operands, Has.Count.EqualTo(2));
        Assert.That(call.Operands[0], Is.EqualTo(new Immediate(0x1234)));
        Assert.That(call.Operands[1], Is.InstanceOf<Register>());
    }

    [Test]
    public void StackPassingRebuildLeavesAlreadyPresentArgumentsUntouched()
    {
        // A resolved call that already carries managed argument operands (produced by the lifter's
        // stack analysis) is NOT in the raw unmanaged layout, so RemapRawArguments must leave it
        // alone. Rebuilding here would overwrite correct operands with signature-derived frame
        // slots, which is exactly the mangling that produced wrong 'this'/parameter bindings.
        var resolved = GetMethod("System.AppDomain", "DoDomainUnload");
        var caller = GetMethod("System.String", "op_Equality", 2);

        var receiver = new LocalVariable("v8", new Register(null, "stack_0"));
        var argument = new LocalVariable("v9", new Register(null, "stack_4"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(0x1234), receiver, argument);

        new StackPassingResolver().RemapRawArguments(call, resolved, caller);

        Assert.That(call.Operands, Has.Count.EqualTo(3), "already-present operands must not be rebuilt");
        Assert.That(call.Operands[0], Is.EqualTo(new Immediate(0x1234)));
        Assert.That(call.Operands[1], Is.SameAs(receiver), "the existing receiver operand must survive");
        Assert.That(call.Operands[2], Is.SameAs(argument), "the existing argument operand must survive");
    }

    // Mimics the x86 all-stack convention on the (x64) test game.
    private sealed class StackPassingResolver : BaseCallingConventionResolver
    {
        public override Register ReturnRegister(MethodAnalysisContext ctx) => new(null, "rax");

        public override bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx) => false;

        public override Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx) => null;

        public override IOperand[] ResolveForManaged(MethodAnalysisContext ctx)
            => [new StackOffset(0), new StackOffset(4), new StackOffset(8)]; // this, param, MethodInfo

        protected override (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app) => ([], []);
    }
}
