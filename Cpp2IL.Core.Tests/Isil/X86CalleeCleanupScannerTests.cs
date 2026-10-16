using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Isil;

public class X86CalleeCleanupScannerTests
{
    private const int Bitness = 32;
    private const int Budget = 4096;

    // The scanner addresses a flat binary image, so the test map translates addresses relative to a base.
    private static int? Scan(byte[] raw, ulong startIp, ulong baseIp = 0x1000)
        => X86InstructionSet.TryScanRetArgumentCleanup(
            raw,
            va => va >= baseIp && va < baseIp + (ulong)raw.Length ? (int)(va - baseIp) : -1,
            startIp,
            Bitness,
            Budget);

    // A function's epilogue declares how it returns arguments: plain ret (C3) means the caller cleans up
    // (cdecl), ret imm16 (C2) means the callee pops that many bytes (stdcall / thiscall).

    [TestCase(new byte[] { 0xC3 }, 0)] // plain ret - caller cleanup
    [TestCase(new byte[] { 0xC2, 0x10, 0x00 }, 16)] // ret 10h - callee pops 16 bytes
    [TestCase(new byte[] { 0xC2, 0x08, 0x00 }, 8)] // ret 8
    [TestCase(new byte[] { 0x31, 0xC0, 0xC2, 0x04, 0x00 }, 4)] // xor eax,eax; ret 4
    public void SingleReturnReportsItsArgumentCleanup(byte[] raw, int expectedCleanup)
    {
        Assert.That(Scan(raw, 0x1000), Is.EqualTo(expectedCleanup));
    }

    [TestCase(new byte[] { 0x90, 0x90 }, null)] // decodes off the end of the binary - no return instruction
    [TestCase(new byte[] { 0xEB, 0x7F }, null)] // unconditional jump outside the mapped binary
    [TestCase(new byte[] { 0xEB, 0xFE }, null)] // jump to self - no reachable return
    [TestCase(new byte[] { 0xFF, 0xE0 }, null)] // indirect jump through eax - unresolvable
    [TestCase(new byte[] { 0x90 }, (ulong)0x100)] // entry point outside the mapped binary
    public void UndeterminableCleanupReportsNull(byte[] raw, ulong? startIp)
    {
        Assert.That(Scan(raw, startIp ?? 0x1000), Is.Null);
    }

    [Test]
    public void AllReachableReturnsAgreeingOnTheSameSizeReportsThatSize()
    {
        // test eax, eax
        // je +10 -> second epilogue
        // xor eax, eax
        // ret 10h          <- first epilogue
        // (5 bytes padding)
        // mov eax, 1
        // ret 10h          <- second epilogue
        byte[] raw =
        [
            0x85, 0xC0,
            0x74, 0x0A,
            0x31, 0xC0,
            0xC2, 0x10, 0x00,
            0x90, 0x90, 0x90, 0x90, 0x90,
            0xB8, 0x01, 0x00, 0x00, 0x00,
            0xC2, 0x10, 0x00,
        ];

        Assert.That(Scan(raw, 0x1000), Is.EqualTo(16));
    }

    [Test]
    public void MixedReturnSizesAreTreatedAsUndeterminable()
    {
        // test eax, eax
        // je +5 -> callee-cleanup epilogue
        // ret              <- plain ret path
        // (4 bytes padding)
        // ret 10h          <- callee-cleanup path
        byte[] raw =
        [
            0x85, 0xC0,
            0x74, 0x05,
            0xC3,
            0x90, 0x90, 0x90, 0x90,
            0xC2, 0x10, 0x00,
        ];

        Assert.That(Scan(raw, 0x1000), Is.Null);
    }

    [Test]
    public void UnconditionalJumpToSharedEpilogueIsFollowed()
    {
        // jmp +3 -> shared epilogue
        // (3 bytes padding)
        // ret 8            <- shared epilogue
        byte[] raw =
        [
            0xE9, 0x03, 0x00, 0x00, 0x00,
            0x90, 0x90, 0x90,
            0xC2, 0x08, 0x00,
        ];

        Assert.That(Scan(raw, 0x1000), Is.EqualTo(8));
    }

    [Test]
    public void JumpThunkToLowerAddressThanItsOwnEntryIsFollowed()
    {
        // Regression test: throw-helper thunks are a single `jmp` to code *below* the thunk's address,
        // which used to make the scanner walk outside its input and throw.
        //
        // ret 8             <- real epilogue below the entry point
        // (12 bytes padding)
        // jmp -20 -> base   <- thunk (the scanned entry point)
        byte[] raw =
        [
            0xC2, 0x08, 0x00,
            0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
            0xE9, 0xEC, 0xFF, 0xFF, 0xFF,
        ];

        Assert.That(Scan(raw, 0x100F), Is.EqualTo(8));
    }

    [Test]
    public void CallsAreNotFollowedButDoNotStopThePath()
    {
        // call +0x10 (target outside the mapped binary - the scanner must not follow it)
        // ret 4
        byte[] raw =
        [
            0xE8, 0x10, 0x00, 0x00, 0x00,
            0xC2, 0x04, 0x00,
        ];

        Assert.That(Scan(raw, 0x1000), Is.EqualTo(4));
    }

    [Test]
    public void ConditionalBranchTargetOnTheSameReturnAgrees()
    {
        // mov eax, 1
        // je +6 -> the other ret
        // mov eax, 2
        // ret
        // ret
        byte[] raw =
        [
            0xB8, 0x01, 0x00, 0x00, 0x00,
            0x74, 0x06,
            0xB8, 0x02, 0x00, 0x00, 0x00,
            0xC3,
            0xC3,
        ];

        Assert.That(Scan(raw, 0x1000), Is.EqualTo(0));
    }
}
