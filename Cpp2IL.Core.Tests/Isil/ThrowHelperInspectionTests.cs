using System.Collections.Generic;
using Cpp2IL.Core.InstructionSets;
using Iced.Intel;

namespace Cpp2IL.Core.Tests.Isil;

// The throw-helper inspector previously only understood 64-bit forms (RIP-relative LEAs and
// NearBranch64 calls), so on IL2CPP x86-32 games (e.g. Among Us) it saw no call targets and no
// data references at all: exception raisers were never recognised and no exception type names
// were ever resolved, leaving user throw sites as opaque native stub calls.
public class ThrowHelperInspectionTests
{
    private static Instruction Decode(byte[] bytes, bool is32Bit)
    {
        var codeReader = new ByteArrayCodeReader(bytes);
        var decoder = Decoder.Create(is32Bit ? 32 : 64, codeReader);
        decoder.Decode(out var instruction);
        return instruction;
    }

    private static (List<ulong> DataRefs, List<ulong> CallTargets) Classify(byte[] bytes, bool is32Bit)
    {
        var dataRefs = new List<ulong>();
        var callTargets = new List<ulong>();
        X86InstructionSet.ClassifyThrowHelperInstruction(Decode(bytes, is32Bit), dataRefs, callTargets);
        return (dataRefs, callTargets);
    }

    [Test]
    public void ThirtyTwoBitRelativeCallIsCollectedAsACallTarget()
    {
        var (dataRefs, callTargets) = Classify([0xE8, 0x00, 0x10, 0x00, 0x00], true); // call 0x1005

        Assert.That(callTargets, Is.EqualTo(new ulong[] { 0x1005 }));
        Assert.That(dataRefs, Is.Empty);
    }

    [Test]
    public void ThirtyTwoBitJumpThunkTailIsCollectedAsACallTarget()
    {
        var (dataRefs, callTargets) = Classify([0xE9, 0x00, 0x20, 0x00, 0x00], true); // jmp 0x2005

        Assert.That(callTargets, Is.EqualTo(new ulong[] { 0x2005 }));
        Assert.That(dataRefs, Is.Empty);
    }

    [Test]
    public void ThirtyTwoBitPushOfAnAbsoluteAddressIsCollectedAsADataReference()
    {
        var (dataRefs, callTargets) = Classify([0x68, 0x00, 0x20, 0x40, 0x10], true); // push 0x10402000

        Assert.That(dataRefs, Is.EqualTo(new ulong[] { 0x10402000 }));
        Assert.That(callTargets, Is.Empty);
    }

    [Test]
    public void ThirtyTwoBitMoveOfAnAbsoluteAddressIntoARegisterIsCollectedAsADataReference()
    {
        var (dataRefs, _) = Classify([0xB8, 0x78, 0x56, 0x34, 0x12], true); // mov eax, 0x12345678

        Assert.That(dataRefs, Is.EqualTo(new ulong[] { 0x12345678 }));
    }

    [Test]
    public void ThirtyTwoBitAbsoluteMemoryOperandIsCollectedAsADataReference()
    {
        var (dataRefs, callTargets) = Classify([0xFF, 0x34, 0x25, 0x00, 0x20, 0x40, 0x10], true); // push dword ptr [0x10402000]

        Assert.That(dataRefs, Is.EqualTo(new ulong[] { 0x10402000 }));
        Assert.That(callTargets, Is.Empty);
    }

    [TestCase(new byte[] { 0x6A, 0x00 }, true)] // push 0 - a small constant, not an address
    [TestCase(new byte[] { 0x89, 0xC8 }, true)] // mov eax, ecx - registers only
    [TestCase(new byte[] { 0xFF, 0xD0 }, true)] // call eax - indirect, no branch target
    [TestCase(new byte[] { 0xC3 }, true)] // ret - nothing
    public void InstructionsCarryingNoAddressProduceNothing(byte[] bytes, bool is32Bit)
    {
        var (dataRefs, callTargets) = Classify(bytes, is32Bit);

        Assert.That(dataRefs, Is.Empty);
        Assert.That(callTargets, Is.Empty);
    }

    [Test]
    public void SixtyFourBitRelativeCallIsStillCollectedAsACallTarget()
    {
        var (_, callTargets) = Classify([0xE8, 0x00, 0x10, 0x00, 0x00], false); // call 0x1005

        Assert.That(callTargets, Is.EqualTo(new ulong[] { 0x1005 }));
    }

    [Test]
    public void SixtyFourBitIpRelativeLeaIsStillCollectedAsADataReference()
    {
        var (dataRefs, _) = Classify([0x48, 0x8D, 0x05, 0x00, 0x10, 0x00, 0x00], false); // lea rax, [rip+0x1000]

        Assert.That(dataRefs, Is.EqualTo(new ulong[] { 0x1007 }));
    }
}
