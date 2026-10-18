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

    [Test]
    public void MixedShapeIcfFoldFoldsTheCandidatesThatFitTheCall()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_567F;

        // ICF folds a run of parameterless Dispose()s together with an unrelated one-argument method.
        var disposeA = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Dispose",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public, []);
        var disposeB = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemVoidType, "Dispose",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public, []);
        var unrelated = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Touch",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemObjectType]);
        appContext.MethodsByAddress[shared] = [disposeA, disposeB, unrelated];

        // The call carries the receiver plus one extra operand the lifter attached, so only the parameterless
        // Disposes fit; they share a shape even though the unrelated method does not, so the call can resolve.
        var receiver = new LocalVariable("self", new Register(null, "esi"));
        var extra = new LocalVariable("extra", new Register(null, "edi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)), receiver, extra);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], receiver, extra);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.SameAs(disposeA), "the parameterless fold resolves the call");
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

    [Test]
    public void SameWidthIntegerOverloadsAreFoldedWhenNoArgumentTypeIsKnown()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_567D;

        // byte and sbyte occupy the same argument slot and share the body, so the call is unambiguous
        // even though the argument's type is unknown.
        var writeByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Write",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemByteType]);
        var writeSByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Write",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemSByteType]);
        appContext.MethodsByAddress[shared] = [writeByte, writeSByte];

        var receiver = new LocalVariable("writer", new Register(null, "esi"), appContext.SystemTypes.SystemObjectType);
        var argument = new LocalVariable("value", new Register(null, "edi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)), receiver, argument);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], receiver, argument);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.SameAs(writeByte), "same-width integer overloads are interchangeable at the call site");
    }

    [Test]
    public void DifferentWidthIntegerOverloadsStayUnresolved()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_567E;

        var writeByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Write",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemByteType]);
        var writeInt = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Write",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public,
            [appContext.SystemTypes.SystemInt32Type]);
        appContext.MethodsByAddress[shared] = [writeByte, writeInt];

        var receiver = new LocalVariable("writer", new Register(null, "esi"), appContext.SystemTypes.SystemObjectType);
        var argument = new LocalVariable("value", new Register(null, "edi"));
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)), receiver, argument);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], receiver, argument);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>(), "different-width overloads are not interchangeable");
    }

    [Test]
    public void IcfFoldedMethodsWithDifferentNamesAreFoldedAtTheCallSite()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_5680;

        // ICF folds unrelated same-shape methods onto one body (e.g. Environment::get_CurrentManagedThreadId
        // and TraceEventCache::GetThreadId), so the declaring types - and names - differ. Neither the receiver
        // nor any argument can pick one out and the call carries no operands, so the shared body is the only
        // thing left to go on: either name is a correct answer.
        var doByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Do",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemByteType]);
        var actSByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemVoidType, "Act",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemSByteType]);
        appContext.MethodsByAddress[shared] = [doByte, actSByte];

        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)));
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)]);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.SameAs(doByte), "a shared body makes the differing name irrelevant");
    }

    [Test]
    public void ArrayParametersWithDistinctInstancesAreFoldable()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_5681;

        // An array is a reference, so it occupies one pointer slot whatever its element type. The element
        // types are resolved per-parameter, so the two `byte[]`s here are different instances; a fold must
        // not be lost to that identity difference.
        var doArray = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Do",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static,
            [new SzArrayTypeAnalysisContext(appContext.SystemTypes.SystemByteType)]);
        var actArray = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemVoidType, "Act",
            appContext.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static,
            [new SzArrayTypeAnalysisContext(appContext.SystemTypes.SystemByteType)]);
        appContext.MethodsByAddress[shared] = [doArray, actArray];

        var call = new Instruction(0, OpCode.CallVoid, new Immediate(unchecked((long)shared)));
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)]);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.SameAs(doArray), "arrays with the same element type are interchangeable at the call");
    }

    [Test]
    public void ReturnTypedOverloadsAreDisambiguatedByTheResultLocal()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_567B;

        // ReadSByte and ReadByte share a body; the receiver and arguments agree, but their return types differ.
        var readByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Read",
            appContext.SystemTypes.SystemByteType, MethodAttributes.Public | MethodAttributes.Static, []);
        var readSByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemVoidType, "Read",
            appContext.SystemTypes.SystemSByteType, MethodAttributes.Public | MethodAttributes.Static, []);

        appContext.MethodsByAddress[shared] = [readByte, readSByte];

        // Only the destination's type tells the two overloads apart.
        var result = new LocalVariable("result", new Register(null, "eax"), appContext.SystemTypes.SystemSByteType);
        var call = new Instruction(0, OpCode.Call, new Immediate(unchecked((long)shared)), result);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], result);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.SameAs(readSByte), "the sbyte overload matches the typed result local");
    }

    [Test]
    public void ReturnTypedOverloadsStayUnresolvedWhenTheResultIsUntyped()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        const ulong shared = 0x0000_00A0_1234_567C;

        var readByte = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemObjectType, "Read",
            appContext.SystemTypes.SystemByteType, MethodAttributes.Public | MethodAttributes.Static, []);
        var readInt = new InjectedMethodAnalysisContext(
            appContext.SystemTypes.SystemVoidType, "Read",
            appContext.SystemTypes.SystemInt32Type, MethodAttributes.Public | MethodAttributes.Static, []);

        appContext.MethodsByAddress[shared] = [readByte, readInt];

        // An untyped destination leaves both candidates viable, so the call must stay unresolved.
        var result = new LocalVariable("result", new Register(null, "eax"));
        var call = new Instruction(0, OpCode.Call, new Immediate(unchecked((long)shared)), result);
        var method = MakeCaller([call, new Instruction(1, OpCode.Return)], result);

        MetadataResolver.ResolveAmbiguousCalls(method);

        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>(), "no unique return match means the call stays unresolved");
    }
}
