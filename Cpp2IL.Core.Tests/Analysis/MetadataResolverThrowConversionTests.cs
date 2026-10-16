using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

// The native-method detector registers an injected stub for every unresolved call, so by the time
// the metadata resolver runs every exception raiser and throw-helper target is already in
// MethodsByAddress. The throw conversion has to preempt that binding or user `throw` statements
// stay as calls to NativeMethod_0x... stubs (with their exception argument pushes deleted as dead).
public class MetadataResolverThrowConversionTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static InjectedMethodAnalysisContext MakeMethod(List<Instruction> instructions, params LocalVariable[] locals)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType,
            "ThrowCaller",
            appContext.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.Locals = locals.ToList();
        method.ParameterLocals = [];
        method.AnalysisWarnings = [];
        return method;
    }

    [Test]
    public void ExceptionRaiserTargetRegisteredAsNativeStubStillBecomesThrow()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var keyFunctions = appContext.GetOrCreateKeyFunctionAddresses();

        if (keyFunctions.il2cpp_vm_exception_raise == 0)
            Assert.Ignore("test binary did not resolve il2cpp_vm_exception_raise");

        var nativeThrow = appContext.InstructionSet.InspectPotentialThrowHelper(appContext, keyFunctions.il2cpp_vm_exception_raise).CallTargets.LastOrDefault();
        Assert.That(nativeThrow, Is.Not.Zero, "vm::Exception::Raise should end in a call to the native throw");
        Assert.That(keyFunctions.IsKeyFunctionAddress(nativeThrow), Is.False, "test needs a raiser target outside the key-function set");
        Assert.That(ThrowHelperRecovery.IsExceptionRaiser(appContext, nativeThrow), Is.True, "the native throw is itself an exception raiser");

        var stub = new NativeMethodAnalysisContext(appContext.SystemTypes.SystemObjectType, nativeThrow, true);
        appContext.MethodsByAddress[nativeThrow] = [stub];

        var exception = new LocalVariable("exception", new Register(null, "esi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)nativeThrow)), exception);
        var method = MakeMethod([call, new Instruction(1, OpCode.Return)], exception);

        MetadataResolver.ResolveAll(method);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Throw), "the registered native stub must not win over the throw conversion");
        if (ThrowHelperRecovery.GetThrownException(appContext, nativeThrow) == null)
            Assert.That(call.Operands[0], Is.SameAs(exception), "a raiser throws the exception operand it was given");
        else
            Assert.That(call.Operands[0], Is.InstanceOf<TypeAnalysisContext>(), "the helper-throw path supplies the exception type");
    }

    [Test]
    public void UnrelatedNativeStubStillBindsAsTheCallTarget()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong unmappedTarget = 0x0000_00FF_DEAD_BEEF;

        // Precondition: this address is neither a throw helper nor a raiser, so it must keep the
        // ordinary stub binding - only exception sites may preempt it.
        Assert.That(ThrowHelperRecovery.IsExceptionRaiser(appContext, unmappedTarget), Is.False);
        Assert.That(ThrowHelperRecovery.GetThrownException(appContext, unmappedTarget), Is.Null);

        var stub = new NativeMethodAnalysisContext(appContext.SystemTypes.SystemObjectType, unmappedTarget, true);
        appContext.MethodsByAddress[unmappedTarget] = [stub];

        var exception = new LocalVariable("exception", new Register(null, "esi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)unmappedTarget)), exception);
        var method = MakeMethod([call, new Instruction(1, OpCode.Return)], exception);

        MetadataResolver.ResolveAll(method);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.CallVoid), "a non-raiser stub keeps its call");
        Assert.That(call.Operands[0], Is.SameAs(stub), "the stub binds as the call target");
    }

    [Test]
    public void ExceptionRaiserTargetWithNoRegisteredMethodStillBecomesThrow()
    {
        // The original unregistered-target path, kept honest by the helper extraction: a raiser
        // call whose address is not in MethodsByAddress at all converts the same way.
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var keyFunctions = appContext.GetOrCreateKeyFunctionAddresses();

        if (keyFunctions.il2cpp_vm_exception_raise == 0)
            Assert.Ignore("test binary did not resolve il2cpp_vm_exception_raise");

        var nativeThrow = appContext.InstructionSet.InspectPotentialThrowHelper(appContext, keyFunctions.il2cpp_vm_exception_raise).CallTargets.LastOrDefault();
        Assert.That(nativeThrow, Is.Not.Zero, "vm::Exception::Raise should end in a call to the native throw");
        Assert.That(ThrowHelperRecovery.IsExceptionRaiser(appContext, nativeThrow), Is.True);
        Assert.That(appContext.MethodsByAddress.ContainsKey(nativeThrow), Is.False, "test needs the raiser unregistered");

        var exception = new LocalVariable("exception", new Register(null, "esi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)nativeThrow)), exception);
        var method = MakeMethod([call, new Instruction(1, OpCode.Return)], exception);

        MetadataResolver.ResolveAll(method);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Throw));
        if (ThrowHelperRecovery.GetThrownException(appContext, nativeThrow) == null)
            Assert.That(call.Operands[0], Is.SameAs(exception));
        else
            Assert.That(call.Operands[0], Is.InstanceOf<TypeAnalysisContext>());
    }

    [Test]
    public void RaiserLikeCallWithUsedResultStaysACall()
    {
        // IsExceptionRaiser is a reachability check, so ordinary functions that may raise on
        // error (klass lookups, array allocation) also match. If the call hands a result back
        // that something reads, it is one of those and must keep its ordinary binding -
        // otherwise the rewritten throw deletes the result's definition chain and the
        // downstream array/type recovery in the same method stops matching.
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var keyFunctions = appContext.GetOrCreateKeyFunctionAddresses();

        if (keyFunctions.il2cpp_vm_exception_raise == 0)
            Assert.Ignore("test binary did not resolve il2cpp_vm_exception_raise");

        var nativeThrow = appContext.InstructionSet.InspectPotentialThrowHelper(appContext, keyFunctions.il2cpp_vm_exception_raise).CallTargets.LastOrDefault();
        Assert.That(nativeThrow, Is.Not.Zero, "vm::Exception::Raise should end in a call to the native throw");
        Assert.That(ThrowHelperRecovery.IsExceptionRaiser(appContext, nativeThrow), Is.True);
        Assert.That(ThrowHelperRecovery.GetThrownException(appContext, nativeThrow), Is.Null,
            "test needs the plain raiser branch, not the helper-that-builds-an-exception branch");

        var stub = new NativeMethodAnalysisContext(appContext.SystemTypes.SystemObjectType, nativeThrow, true);
        appContext.MethodsByAddress[nativeThrow] = [stub];

        var exception = new LocalVariable("exception", new Register(null, "esi"));
        var result = new LocalVariable("result", new Register(null, "eax"));
        var sink = new LocalVariable("sink", new Register(null, "edx"));
        var call = new Instruction(0, OpCode.Call, new Immediate(unchecked((long)nativeThrow)), result, exception);
        var read = new Instruction(1, OpCode.Move, sink, result); // something reads the result
        var method = MakeMethod([call, read, new Instruction(2, OpCode.Return)], exception, result, sink);

        MetadataResolver.ResolveAll(method);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call), "a may-raise function whose result is read must stay a call");
        Assert.That(call.Operands[0], Is.SameAs(stub), "the stub binds as the call target");
    }

    [Test]
    public void RaiserLikeCallWithDeadResultStillBecomesThrow()
    {
        // The counterpart: a genuinely unused result (the callee never returns normally) keeps
        // the conversion, so the guard above cannot starve real inline throw sites.
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var keyFunctions = appContext.GetOrCreateKeyFunctionAddresses();

        if (keyFunctions.il2cpp_vm_exception_raise == 0)
            Assert.Ignore("test binary did not resolve il2cpp_vm_exception_raise");

        var nativeThrow = appContext.InstructionSet.InspectPotentialThrowHelper(appContext, keyFunctions.il2cpp_vm_exception_raise).CallTargets.LastOrDefault();
        Assert.That(nativeThrow, Is.Not.Zero, "vm::Exception::Raise should end in a call to the native throw");
        Assert.That(ThrowHelperRecovery.IsExceptionRaiser(appContext, nativeThrow), Is.True);
        Assert.That(ThrowHelperRecovery.GetThrownException(appContext, nativeThrow), Is.Null,
            "test needs the plain raiser branch, not the helper-that-builds-an-exception branch");

        var exception = new LocalVariable("exception", new Register(null, "esi"));
        var result = new LocalVariable("result", new Register(null, "eax"));
        var call = new Instruction(0, OpCode.Call, new Immediate(unchecked((long)nativeThrow)), result, exception);
        var method = MakeMethod([call, new Instruction(1, OpCode.Return)], exception, result);

        MetadataResolver.ResolveAll(method);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Throw), "an unread result still converts");
        Assert.That(call.Operands[0], Is.SameAs(exception), "a raiser throws the exception operand it was given");
    }
}
