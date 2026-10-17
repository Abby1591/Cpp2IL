using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackAnalyzerTests
{
    [OneTimeSetUp]
    public void LoadGame()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static MethodAnalysisContext GetAnyMethod()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = appContext.AssembliesByName["mscorlib"];
        var appDomain = mscorlib.GetTypeByFullName("System.AppDomain")!;

        return appDomain.GetMethod("DoDomainUnload")!;
    }

    private static void RunStackAnalyzer(List<Instruction> instructions)
    {
        // Resolve jump targets from raw indices to instruction references, as the graph builder expects.
        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is not (OpCode.Jump or OpCode.ConditionalJump))
                continue;

            instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);
        }

        var method = GetAnyMethod();
        method.AnalysisWarnings.Clear();
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        StackAnalyzer.Analyze(method);
    }

    [Test]
    public void BalancedLoopWithCallerCleanupConverges()
    {
        // The shape of the loop that failed to settle on Among Us (AccountManager::GetRandomName),
        // now with correctly-modelled shifts: two pushes, a call, then an 8-byte caller cleanup,
        // looping until a condition exits. The tracked stack change per iteration is zero.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Jump, Imm(1)),
            new(1, OpCode.ShiftStack, Imm(-4)), // push arg1
            new(2, OpCode.ShiftStack, Imm(-4)), // push arg2
            new(3, OpCode.Call, Imm(0x1234)),
            new(4, OpCode.ShiftStack, Imm(8)), // add esp, 8
            new(5, OpCode.ConditionalJump, Imm(7), new Register(null, "ZF")),
            new(6, OpCode.Jump, Imm(1)),
            new(7, OpCode.Return),
        };

        Assert.DoesNotThrow(() => RunStackAnalyzer(instructions), "stack-neutral loop should settle");
        Assert.That(GetAnyMethod().AnalysisWarnings, Is.Empty, "method should end with an empty stack");
    }

    [Test]
    public void DivergentLoopThrowsWhenVisitLimitReached()
    {
        // The same loop shape as produced by the pre-fix x86-32 translation, where immediate pushes
        // became ShiftStack 0 and caller cleanups (add esp, N) were dropped entirely: the tracked
        // stack shrinks by 4 per iteration and can never settle.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Jump, Imm(1)),
            new(1, OpCode.ShiftStack, Imm(0)), // bugged immediate push: no stack movement
            new(2, OpCode.ShiftStack, Imm(-4)), // push register
            new(3, OpCode.Call, Imm(0x1234)),
            new(4, OpCode.ConditionalJump, Imm(6), new Register(null, "ZF")),
            new(5, OpCode.Jump, Imm(1)),
            new(6, OpCode.Return),
        };

        var originalLimit = StackAnalyzer.MaxBlockVisitCount;
        StackAnalyzer.MaxBlockVisitCount = 200;

        try
        {
            var exception = Assert.Throws<DecompilerException>(() => RunStackAnalyzer(instructions));
            Assert.That(exception!.Message, Does.Contain("Stack state not settling"));
        }
        finally
        {
            StackAnalyzer.MaxBlockVisitCount = originalLimit;
        }
    }

    [Test]
    public void FramePointerRestoreKeepsExitBalance()
    {
        // `mov esp, ebp` in an epilogue restores the stack pointer to the frame, discarding the
        // tracked size - without modelling this, tracking `sub esp, N` would leave the exit state
        // permanently unbalanced for every frame-pointer method.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ShiftStack, Imm(-4)), // push ebp
            new(1, OpCode.Move, new Register(null, "rbp"), new Register(null, "rsp")), // mov ebp, esp
            new(2, OpCode.ShiftStack, Imm(-16)), // sub esp, 0x10
            new(3, OpCode.ShiftStack, Imm(-4)), // push x
            new(4, OpCode.ShiftStack, Imm(4)), // pop x
            new(5, OpCode.Move, new Register(null, "rsp"), new Register(null, "rbp")), // mov esp, ebp
            new(6, OpCode.ShiftStack, Imm(4)), // pop ebp
            new(7, OpCode.Return),
        };

        Assert.DoesNotThrow(() => RunStackAnalyzer(instructions));
        Assert.That(GetAnyMethod().AnalysisWarnings, Is.Empty, "restoring the frame pointer should rebalance the exit stack");
    }

    [Test]
    public void UnrestoredStackPointerStillWarns()
    {
        // Restoring from a register that never captured the stack pointer is not a valid restore,
        // so the end-of-method balance check must still fire.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ShiftStack, Imm(-4)),
            new(1, OpCode.ShiftStack, Imm(-16)),
            new(2, OpCode.Move, new Register(null, "rsp"), new Register(null, "rbx")), // mov esp, ebx
            new(3, OpCode.ShiftStack, Imm(4)),
            new(4, OpCode.Return),
        };

        Assert.DoesNotThrow(() => RunStackAnalyzer(instructions));
        Assert.That(GetAnyMethod().AnalysisWarnings, Has.Some.Contains("non empty stack"));
    }

    [Test]
    public void FramePointerLoadIsRewrittenBeforeEpilogueInvalidation()
    {
        // [ebp+N] uses must be rewritten with the still-active alias even though the epilogue
        // (`pop ebp`) reassigns the frame pointer later in the method: invalidation and rewriting
        // happen in one forward pass, not in separate phases (the phased version dropped the
        // alias before any body use was rewritten, leaving hundreds of thousands of frame-pointer
        // loads on x86 to fall through to the IL generator's null-placeholder fallback).
        var rbp = new Register(null, "rbp");
        var rsp = new Register(null, "rsp");
        var rax = new Register(null, "rax");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ShiftStack, Imm(-4)), // push ebp
            new(1, OpCode.Move, rbp, rsp), // mov ebp, esp
            new(2, OpCode.Move, rax, new MemoryOperand(rbp, addend: 8)), // mov eax, [ebp+8] (this)
            new(3, OpCode.Move, rbp, new Register(null, "stack_0")), // pop ebp
            new(4, OpCode.Return),
        };

        Assert.DoesNotThrow(() => RunStackAnalyzer(instructions));

        var load = instructions[2];
        Assert.That(load.Operands[1], Is.Not.InstanceOf<MemoryOperand>(),
            "[ebp+8] must be converted to a stack slot even though the epilogue reassigns rbp");
        Assert.That(load.Operands[1], Is.InstanceOf<Register>());
        Assert.That(((Register)load.Operands[1]).Name, Is.EqualTo("stack_4"),
            "slot = frame capture (-4) + 8 = +4 above the entry stack");
    }

    [Test]
    public void BodyFrameLoadSurvivesASiblingEpilogueListedFirst()
    {
        // The ISIL instruction list is BFS order, not execution order. An early-exit epilogue that
        // reassigns the frame pointer can be a sibling block listed before the body, so a flat
        // forward pass drops the alias before ever reaching the body's [ebp+N] use - even though
        // that use runs before the epilogue. Alias validity must follow control flow.
        var rbp = new Register(null, "rbp");
        var rsp = new Register(null, "rsp");
        var rax = new Register(null, "rax");
        var zf = new Register(null, "ZF");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ShiftStack, Imm(-4)), // A: push ebp
            new(1, OpCode.Move, rbp, rsp), // A: mov ebp, esp
            new(2, OpCode.ConditionalJump, Imm(6), zf), // A: branch to the body, else fall into the epilogue
            new(3, OpCode.Move, rsp, rbp), // B: early-exit epilogue
            new(4, OpCode.Move, rbp, new Register(null, "stack_0")), // B: pop ebp (reassigns the frame)
            new(5, OpCode.Return), // B
            new(6, OpCode.Move, rax, new MemoryOperand(rbp, addend: 8)), // C: mov eax, [ebp+8] (this)
            new(7, OpCode.Return), // C
        };

        Assert.DoesNotThrow(() => RunStackAnalyzer(instructions));

        var load = instructions[6];
        Assert.That(load.Operands[1], Is.InstanceOf<Register>(),
            "[ebp+8] must be folded even though a sibling epilogue clobbering rbp is listed first");
        Assert.That(((Register)load.Operands[1]).Name, Is.EqualTo("stack_4"));
    }
}
