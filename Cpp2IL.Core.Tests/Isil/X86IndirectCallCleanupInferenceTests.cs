using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Isil;

public class X86IndirectCallCleanupInferenceTests
{
    private static Register Reg(string name) => new(null, name);

    private static void Add(List<Instruction> instructions, int index, OpCode opCode, params IOperand[] operands) =>
        instructions.Add(new Instruction(index, opCode, [.. operands]));

    // MSVC x86 thiscall (callee pops) vs cdecl (caller pops) vs the mixed split (callee ret N plus a
    // caller add esp) cannot be told apart from the indirect target, so the call site's push run and
    // the caller-side cleanup after the call decide how many bytes the tracked stack must recover.

    [Test]
    public void UncleanedPushRunIsAssumedCalleePopped()
    {
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 1, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 2, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 3, OpCode.Move, new StackOffset(0), Reg("rcx"));
        Add(instructions, 4, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 5, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4, 5 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(7), "expected one inserted cleanup");
        Assert.That(instructions[5].OpCode, Is.EqualTo(OpCode.ShiftStack));
        Assert.That(((Immediate)instructions[5].Operands[0]).Value, Is.EqualTo(8), "callee pops both slots");
        Assert.That(instructions[6].OpCode, Is.EqualTo(OpCode.Return));
    }

    [Test]
    public void CallerCleanupRightAfterTheCallIsLeftUntouched()
    {
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 1, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 2, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 3, OpCode.Move, new StackOffset(0), Reg("rcx"));
        Add(instructions, 4, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 5, OpCode.ShiftStack, new Immediate(8));
        Add(instructions, 6, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4, 5, 6 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(7), "cdecl site must not gain a cleanup");
        Assert.That(instructions[5].OpCode, Is.EqualTo(OpCode.ShiftStack));
        Assert.That(((Immediate)instructions[5].Operands[0]).Value, Is.EqualTo(8));
    }

    [Test]
    public void MixedSiteInsertsOnlyTheUncoveredRemainder()
    {
        // push x4; call; add esp, 0Ch — the callee's ret 4 pops one slot and the caller cleans
        // the other three; only the four uncovered bytes may be modeled as callee-popped.
        var instructions = new List<Instruction>();
        for (var i = 0; i < 4; i++)
        {
            Add(instructions, i * 2, OpCode.ShiftStack, new Immediate(-4));
            Add(instructions, i * 2 + 1, OpCode.Move, new StackOffset(0), Reg("rax"));
        }

        Add(instructions, 8, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 9, OpCode.ShiftStack, new Immediate(12));
        Add(instructions, 10, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(12), "expected one inserted cleanup");
        Assert.That(instructions[9].OpCode, Is.EqualTo(OpCode.ShiftStack));
        Assert.That(((Immediate)instructions[9].Operands[0]).Value, Is.EqualTo(4), "only the caller-uncovered remainder");
    }

    [Test]
    public void PrologueFrameSetupIsNotPartOfThePushRun()
    {
        // push ebp; mov ebp,esp; push arg; call; add esp,4; pop ebp; ret — the prologue push is
        // not an argument, so the four caller-cleared bytes fully cover the run.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 1, OpCode.Move, new StackOffset(0), Reg("rbp"));
        Add(instructions, 2, OpCode.Move, Reg("rbp"), Reg("rsp"));
        Add(instructions, 3, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 4, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 5, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 6, OpCode.ShiftStack, new Immediate(4));
        Add(instructions, 7, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4, 5, 6, 7 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(8), "prologue push must not inflate the assumption");
    }

    [Test]
    public void LocalsAllocationIsNotPartOfThePushRun()
    {
        // sub esp, 10h has no paired store into the push slot and ends the argument region.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-16));
        Add(instructions, 1, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 2, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 3, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 4, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(6), "expected one inserted cleanup");
        Assert.That(((Immediate)instructions[4].Operands[0]).Value, Is.EqualTo(4), "only the argument push, not the locals allocation");
    }

    [Test]
    public void CoalescedCallerCleanupAfterFollowingCallIsFound()
    {
        // call A; push argsB; call B; add esp,8 — one add esp covering both calls means A is
        // caller-cleaned as well.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 1, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 2, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 3, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 4, OpCode.Move, new StackOffset(0), Reg("rcx"));
        Add(instructions, 5, OpCode.Call, new Immediate(0x2000));
        Add(instructions, 6, OpCode.ShiftStack, new Immediate(8));
        Add(instructions, 7, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4, 5, 6, 7 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(8), "coalesced add esp must suppress the insert");
    }

    [Test]
    public void UnconditionalJumpToCleanupIsFollowed()
    {
        // call; jmp over dead code to the shared add esp — the cleanup still belongs to the call.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 1, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 2, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 3, OpCode.Jump, new Immediate(0x1006));
        Add(instructions, 4, OpCode.Return);
        Add(instructions, 5, OpCode.ShiftStack, new Immediate(4));
        Add(instructions, 6, OpCode.Return);
        var addresses = new List<ulong> { 0x1000, 0x1001, 0x1002, 0x1003, 0x1005, 0x1006, 0x1007 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(7), "jumped-to cleanup must suppress the insert");
    }

    [Test]
    public void EpilogueRegisterPopsAreNotCallerCleanup()
    {
        // pop reg expands to (Move reg, stack[0]; ShiftStack +4) right before the return and must
        // not be mistaken for an add esp covering the arguments.
        var instructions = new List<Instruction>();
        Add(instructions, 0, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 1, OpCode.Move, new StackOffset(0), Reg("rax"));
        Add(instructions, 2, OpCode.ShiftStack, new Immediate(-4));
        Add(instructions, 3, OpCode.Move, new StackOffset(0), Reg("rcx"));
        Add(instructions, 4, OpCode.IndirectCall, Reg("rax"), Reg("rax"));
        Add(instructions, 5, OpCode.Move, Reg("rdi"), new StackOffset(0));
        Add(instructions, 6, OpCode.ShiftStack, new Immediate(4));
        Add(instructions, 7, OpCode.Return);
        var addresses = new List<ulong> { 0, 1, 2, 3, 4, 5, 6, 7 };

        X86InstructionSet.AssumeIndirectCallCalleeCleanup(instructions, addresses);

        Assert.That(instructions, Has.Count.EqualTo(9), "expected one inserted cleanup");
        Assert.That(((Immediate)instructions[5].Operands[0]).Value, Is.EqualTo(8), "pops must not cover the argument slots");
    }
}
