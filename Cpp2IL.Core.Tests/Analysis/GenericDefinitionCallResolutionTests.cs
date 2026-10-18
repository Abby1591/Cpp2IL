using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

// A generic method's open definition carries the same native pointer as the instantiated bodies it was
// compiled into, so il2cpp lists the definition next to its concrete instantiation(s) at one address.
// That used to read as genuine ambiguity and left every call to such a shared body unresolved. The open
// body can only be reached through an instantiation, so the definition must be dropped whenever a
// concrete instantiation of it sits at the same address - but kept when it is all that is there.
public class GenericDefinitionCallResolutionTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static MethodAnalysisContext FirstGenericTypeMethod(ApplicationAnalysisContext appContext, bool genericMethod)
    {
        var method = appContext.Assemblies
            .SelectMany(a => a.Types)
            .Where(t => t.GenericParameters.Count > 0)
            .SelectMany(t => t.Methods)
            .FirstOrDefault(m => m.Definition != null && (m.GenericParameters.Count > 0) == genericMethod);

        Assume.That(method, Is.Not.Null, "the test game must contain a method on a generic type");
        return method!;
    }

    private static ConcreteGenericMethodAnalysisContext Instantiate(ApplicationAnalysisContext appContext, MethodAnalysisContext definition)
    {
        var typeArguments = definition.DeclaringType!.GenericParameters
            .Select(_ => (TypeAnalysisContext)appContext.SystemTypes.SystemObjectType)
            .ToList();

        return definition.MakeConcreteGenericMethod(typeArguments, []);
    }

    [Test]
    public void CandidatesDropTheDefinitionWhenAnInstantiationSharesTheAddress()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var definition = FirstGenericTypeMethod(appContext, genericMethod: false);
        var instantiation = Instantiate(appContext, definition);

        const ulong address = 0x0000_00A0_1234_5001;
        appContext.MethodsByAddress[address] = [definition, instantiation];

        var candidates = appContext.GetCallCandidatesAt(address);

        Assert.That(candidates, Is.Not.Null);
        Assert.That(candidates!, Has.Count.EqualTo(1), "only the instantiation is a real target");
        Assert.That(candidates, Does.Contain(instantiation));
    }

    [Test]
    public void CandidatesKeepTheDefinitionWhenNothingIsInstantiated()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;

        var definitions = appContext.Assemblies
            .SelectMany(a => a.Types)
            .Where(t => t.GenericParameters.Count > 0)
            .SelectMany(t => t.Methods)
            .Where(m => m.Definition != null)
            .Take(2)
            .ToList();        Assume.That(definitions, Has.Count.EqualTo(2), "the test game must contain two methods on generic types");

        const ulong address = 0x0000_00A0_1234_5002;
        appContext.MethodsByAddress[address] = [definitions[0], definitions[1]];

        var candidates = appContext.GetCallCandidatesAt(address);

        Assert.That(candidates!, Has.Count.EqualTo(2), "a definition with no instantiation stays a valid target");
    }

    [Test]
    public void ResolveAmbiguousCallsBindsTheSingleRemainingInstantiation()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var definition = FirstGenericTypeMethod(appContext, genericMethod: false);
        var instantiation = Instantiate(appContext, definition);

        const ulong address = 0x0000_00A0_1234_5003;
        appContext.MethodsByAddress[address] = [definition, instantiation];

        var call = MakeCall(address);
        var caller = MakeCaller(appContext, call);

        MetadataResolver.ResolveAmbiguousCalls(caller);

        Assert.That(call.Operands[0], Is.SameAs(instantiation), "the call binds to the concrete instantiation");
    }

    [Test]
    public void ResolveAmbiguousCallsLeavesAGenericMethodInstantiationForTheHiddenMethodInfoPath()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var definition = FirstGenericTypeMethod(appContext, genericMethod: true);
        var instantiation = Instantiate(appContext, definition);

        const ulong address = 0x0000_00A0_1234_5005;
        appContext.MethodsByAddress[address] = [definition, instantiation];

        var call = MakeCall(address);
        var caller = MakeCaller(appContext, call);

        MetadataResolver.ResolveAmbiguousCalls(caller);

        // The map's instantiation may be a placeholder; only the caller's hidden MethodInfo names the exact one.
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>(), "a generic method instantiation must not be guessed");
    }

    [Test]
    public void ResolveAmbiguousCallsLeavesAnAlreadyResolvedCallAlone()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var definition = FirstGenericTypeMethod(appContext, genericMethod: true);
        var instantiation = Instantiate(appContext, definition);

        const ulong address = 0x0000_00A0_1234_5004;
        appContext.MethodsByAddress[address] = [definition, instantiation];

        // A call ResolveCallsViaMethodInfo already bound (it carries a hidden MethodInfo) is not an Immediate.
        var call = new Instruction(0, OpCode.CallVoid, new StringLiteral("already-resolved"));
        var caller = MakeCaller(appContext, call);

        MetadataResolver.ResolveAmbiguousCalls(caller);

        Assert.That(call.Operands[0], Is.InstanceOf<StringLiteral>(), "an already-bound call must be left untouched");
    }

    private static Instruction MakeCall(ulong address) => new(0, OpCode.CallVoid, new Immediate(unchecked((long)address)));

    private static InjectedMethodAnalysisContext MakeCaller(ApplicationAnalysisContext appContext, Instruction call)
    {
        var caller = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType,
            "Caller",
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            []);

        caller.ControlFlowGraph = new ISILControlFlowGraph([call, new Instruction(1, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        return caller;
    }
}
