using System.Collections.Generic;
using Cpp2IL.Core.InstructionSets;
using Iced.Intel;

namespace Cpp2IL.Core.Tests.Isil;

public class X86StackAdjustmentTests
{
    private static List<Instruction> Decode(byte[] bytes, bool is32Bit)
    {
        var codeReader = new ByteArrayCodeReader(bytes);
        var decoder = Decoder.Create(is32Bit ? 32 : 64, codeReader);
        var instructions = new List<Instruction>();

        decoder.Decode(out var instruction);
        while (!instruction.IsInvalid)
        {
            instructions.Add(instruction);
            decoder.Decode(out instruction);
        }

        return instructions;
    }

    [TestCase(new byte[] { 0x83, 0xC4, 0x08 }, true, 8)] // add esp, 8
    [TestCase(new byte[] { 0x83, 0xEC, 0x04 }, true, -4)] // sub esp, 4
    [TestCase(new byte[] { 0x81, 0xC4, 0xF8, 0x00, 0x00, 0x00 }, true, 0xF8)] // add esp, 0xF8
    [TestCase(new byte[] { 0x48, 0x83, 0xC4, 0x08 }, false, 8)] // add rsp, 8
    [TestCase(new byte[] { 0x48, 0x83, 0xEC, 0x10 }, false, -16)] // sub rsp, 0x10
    public void ImmediateAddSubOfStackPointerIsRecognisedAsStackAdjustment(byte[] bytes, bool is32Bit, int expectedShift)
    {
        var instruction = Decode(bytes, is32Bit)[0];

        Assert.That(X86InstructionSet.TryGetImmediateStackAdjustment(instruction, out var shift), Is.True);
        Assert.That(shift, Is.EqualTo(expectedShift));
    }

    [TestCase(new byte[] { 0x83, 0xC0, 0x08 }, true)] // add eax, 8 - not the stack pointer
    [TestCase(new byte[] { 0x01, 0xD8 }, true)] // add eax, ebx - not an immediate
    [TestCase(new byte[] { 0x01, 0x1C, 0x24 }, true)] // add [esp], ebx - memory destination
    [TestCase(new byte[] { 0x48, 0x01, 0xC8 }, false)] // add rax, rcx - not the stack pointer
    public void NonStackAdjustmentsAreNotRecognised(byte[] bytes, bool is32Bit)
    {
        var instruction = Decode(bytes, is32Bit)[0];

        Assert.That(X86InstructionSet.TryGetImmediateStackAdjustment(instruction, out _), Is.False);
    }

    // Regression tests for the stack-state divergence seen on IL2CPP x86-32 games (e.g. Among Us):
    // iced reports MemorySize.Unknown for immediate pushes, which previously yielded a size of 0 and
    // emitted ShiftStack 0 - silently dropping the push from the tracked stack.
    [TestCase(new byte[] { 0x6A, 0x00 }, true, 4)] // push 0 (imm8)
    [TestCase(new byte[] { 0x68, 0x78, 0x56, 0x34, 0x12 }, true, 4)] // push 12345678h (imm32)
    [TestCase(new byte[] { 0x50 }, true, 4)] // push eax
    [TestCase(new byte[] { 0x57 }, true, 4)] // push edi
    [TestCase(new byte[] { 0x66, 0x50 }, true, 2)] // push ax (operand-size override)
    [TestCase(new byte[] { 0xFF, 0x30 }, true, 4)] // push dword ptr [eax]
    [TestCase(new byte[] { 0x6A, 0x00 }, false, 8)] // push 0 in 64-bit mode
    [TestCase(new byte[] { 0x50 }, false, 8)] // push rax
    [TestCase(new byte[] { 0xFF, 0x30 }, false, 8)] // push qword ptr [rax]
    public void PushMovesTheExpectedNumberOfBytes(byte[] bytes, bool is32Bit, int expectedSize)
    {
        var instruction = Decode(bytes, is32Bit)[0];

        Assert.That(X86InstructionSet.GetStackAccessSize(instruction), Is.EqualTo(expectedSize));
    }

    [TestCase(new byte[] { 0x58 }, true, 4)] // pop eax
    [TestCase(new byte[] { 0x5F }, true, 4)] // pop edi
    [TestCase(new byte[] { 0x8F, 0x00 }, true, 4)] // pop dword ptr [eax]
    [TestCase(new byte[] { 0x58 }, false, 8)] // pop rax
    public void PopMovesTheExpectedNumberOfBytes(byte[] bytes, bool is32Bit, int expectedSize)
    {
        var instruction = Decode(bytes, is32Bit)[0];

        Assert.That(X86InstructionSet.GetStackAccessSize(instruction), Is.EqualTo(expectedSize));
    }
}
