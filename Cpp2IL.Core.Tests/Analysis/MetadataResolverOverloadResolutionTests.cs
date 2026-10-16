using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

// Several distinct overloads can share one native body address (e.g. Hazel.MessageWriter::Write
// byte/int/uint/bool). After lifting, such a call still points at a numeric address, so the
// resolver has to pick one from MethodsByAddress. The receiver only proves the declaring type;
// when two candidates share it (and agree with the receiver) the argument types are the remaining
// disambiguator. It must commit only on a unique survivor and never guess.
public class MetadataResolverOverloadResolutionTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static InjectedMethodAnalysisContext MakeCaller(List<Instruction> instructions, params LocalVariable[] locals)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType,
            "Caller",
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            []);

        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.Locals = locals.ToList();
        method.ParameterLocals = [];
        method.AnalysisWarnings = [];
        return method;
    }

    private static (MethodAnalysisContext Byte, MethodAnalysisContext Int) RegisterWriteOverloads(ulong shared)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;

        var writeByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Write",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemByteType]);

        var writeInt = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Write",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemInt32Type]);

        appContext.MethodsByAddress[shared] = [writeByte, writeInt];
        return (writeByte, writeInt);
    }

    [Test]
    public void InstanceOverloadsAreDisambiguatedByTypedArgument()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_5678;
        var (writeByte, _) = RegisterWriteOverloads(shared);

        // The shared declaring type (object) agrees with both candidates, so only the typed byte
        // argument can tell Write(byte) and Write(int) apart.
        var receiver = new LocalVariable("writer", new Register(null, "esi"), appContext.SystemTypes.SystemObjectType);
        var argument = new LocalVariable("value", new Register(null, "edi"), appContext.SystemTypes.SystemByteType);
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)), receiver, argument);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], receiver, argument);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.SameAs(writeByte), "the byte overload matches the typed byte argument");
    }

    [Test]
    public void OverloadsStayUnresolvedWhenNoArgumentTypeIsKnown()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_5679;
        RegisterWriteOverloads(shared);

        // With an untyped argument both candidates agree, so there is no unique match and the call
        // must be left pointing at its numeric target (the resolver never guesses).
        var receiver = new LocalVariable("writer", new Register(null, "esi"), appContext.SystemTypes.SystemObjectType);
        var argument = new LocalVariable("value", new Register(null, "edi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)), receiver, argument);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], receiver, argument);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>(), "no unique match means the call stays unresolved");
    }

    [Test]
    public void OverloadsWithDisagreeingTypedArgumentStayUnresolved()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_567A;
        RegisterWriteOverloads(shared);

        // A typed argument whose type matches neither candidate eliminates both, leaving no match.
        var receiver = new LocalVariable("writer", new Register(null, "esi"), appContext.SystemTypes.SystemObjectType);
        var argument = new LocalVariable("value", new Register(null, "edi"), appContext.SystemTypes.SystemBooleanType);
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)), receiver, argument);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], receiver, argument);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>(), "a disagreeing argument must not force a guess");
    }
}
