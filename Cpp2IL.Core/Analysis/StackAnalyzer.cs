using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public class StackAnalyzer
{
    [DebuggerDisplay("Size = {Size}")]
    private class StackState
    {
        public int Size;
        public StackState Copy() => new() { Size = this.Size };
    }

    private Dictionary<Block, StackState> _inComingState = [];
    private Dictionary<Block, StackState> _outGoingState = [];
    private Dictionary<Instruction, StackState> _instructionState = [];

    // Registers holding a captured copy of the stack pointer (e.g. frame pointers from `mov rbp, rsp`),
    // mapped to the stack size at the point of capture. Used so epilogues like `mov rsp, rbp` can
    // restore the tracked size instead of leaving it stale.
    private readonly Dictionary<string, int> _capturedStackPointers = [];

    /// <summary>
    /// Max allowed count of blocks to visit (-1 for no limit).
    /// </summary>
    public static int MaxBlockVisitCount = 500000; //High enough to not be legitimately hit, but still give up if something loops infinitely.

    public static void Analyze(MethodAnalysisContext method)
    {
        var analyzer = new StackAnalyzer();

        var graph = method.ControlFlowGraph!;
        graph.RemoveUnreachableBlocks(); // Without this indirect jumps (in try catch i think) cause some weird stuff

        analyzer._inComingState = new Dictionary<Block, StackState> { { graph.EntryBlock, new StackState() } };

        analyzer.TraverseGraph(graph.EntryBlock, method.FullName);

        // The exit block has no outgoing state if it was never reached (e.g. every path loops or
        // throws). That's fine - just skip the end-of-method stack balance check in that case.
        if (analyzer._outGoingState.TryGetValue(graph.ExitBlock, out var outDelta) && outDelta.Size != 0)
        {
            var outText = outDelta.Size < 0 ? "-" + (-outDelta.Size).ToString("X") : outDelta.Size.ToString("X");
            method.AddWarning($"Method ends with non empty stack ({outText}), the output could be wrong!");
        }

        analyzer.ResolveFrameAliases(graph);
        analyzer.CorrectOffsets(graph);
        ReplaceStackWithRegisters(method);

        graph.RemoveNops();
        graph.RemoveEmptyBlocks();
    }

    // consider mov [reg], [stack pointer]
    // now we need to handle [reg] as if it were a stack pointer, forever.
    private void ResolveFrameAliases(ISILControlFlowGraph graph)
    {
        var aliases = new Dictionary<string, int>();
        var captures = new HashSet<Instruction>();

        foreach (var instruction in graph.EntryBlock.Successors.SelectMany(b => b.Instructions))
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [Register destination, Register { Name: "rsp" }] }
                && _instructionState.TryGetValue(instruction, out var atCopy))
            {
                aliases[destination.Name] = atCopy.Size;
                captures.Add(instruction);
            }
        }

        if (aliases.Count == 0)
            return;

        // A captured frame pointer stays trustworthy until a path clobbers the register. The
        // instruction list is *not* in execution order - an epilogue's `pop frame` can be listed
        // before the body it runs after - so validity has to follow the control flow rather than
        // list position, otherwise a body `[frame+N]` use is dropped merely because an unrelated
        // epilogue appears earlier in the list.
        var liveAliases = ComputeLiveAliases(graph, aliases, captures);

        foreach (var instruction in graph.Instructions)
        {
            if (!_instructionState.TryGetValue(instruction, out var state))
                continue;

            var live = liveAliases.TryGetValue(instruction, out var set) ? set : (ISet<string>?)null;

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand { Index: null, Scale: 0, Base: Register frameBase } memory)
                    continue;

                if (live == null || !live.Contains(frameBase.Name))
                    continue;

                instruction.SetOperand(i, new StackOffset((int)(aliases[frameBase.Name] + memory.Addend - state.Size)));
            }
        }
    }

    // Forward must-analysis: a captured frame register still holds its prologue stack pointer at an
    // instruction only if no path reaching that instruction reassigned it. An alias written anywhere
    // in a block is treated as clobbered for the whole block's exit (conservative but safe).
    private static Dictionary<Instruction, ISet<string>> ComputeLiveAliases(ISILControlFlowGraph graph, Dictionary<string, int> aliases, HashSet<Instruction> captures)
    {
        var all = (ISet<string>)new HashSet<string>(aliases.Keys);
        var outState = new Dictionary<Block, ISet<string>>();

        bool changed;
        do
        {
            changed = false;

            foreach (var block in graph.Blocks)
            {
                var incoming = InState(block, graph, outState, all);
                var current = incoming;

                foreach (var instruction in block.Instructions)
                {
                    if (!captures.Contains(instruction) && instruction.Destination is Register written && current.Contains(written.Name))
                    {
                        var next = new HashSet<string>(current);
                        next.Remove(written.Name);
                        current = next;
                    }
                }

                if (!outState.TryGetValue(block, out var existing) || !existing.SetEquals(current))
                {
                    outState[block] = current;
                    changed = true;
                }
            }
        } while (changed);

        var result = new Dictionary<Instruction, ISet<string>>();

        foreach (var block in graph.Blocks)
        {
            var current = InState(block, graph, outState, all);

            foreach (var instruction in block.Instructions)
            {
                result[instruction] = current;

                if (!captures.Contains(instruction) && instruction.Destination is Register written && current.Contains(written.Name))
                {
                    var next = new HashSet<string>(current);
                    next.Remove(written.Name);
                    current = next;
                }
            }
        }

        return result;
    }

    private static ISet<string> InState(Block block, ISILControlFlowGraph graph, Dictionary<Block, ISet<string>> outState, ISet<string> all)
    {
        // The prologue capture runs at the very start of the body, so the entry block already has
        // every alias available; a register is live at a normal block only if it is live on every
        // incoming edge.
        if (block == graph.EntryBlock)
            return all;

        HashSet<string>? incoming = null;

        foreach (var predecessor in block.Predecessors)
        {
            var outOfPred = outState.TryGetValue(predecessor, out var value) ? value : all;

            if (incoming == null)
                incoming = new HashSet<string>(outOfPred);
            else
                incoming.IntersectWith(outOfPred);
        }

        return incoming ?? (ISet<string>)new HashSet<string>();
    }

    private void CorrectOffsets(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.ShiftStack })
                {
                    // Nop the shift stack instruction
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                    continue;
                }

                int? state = null;

                // Correct offset for stack operands.
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    var op = instruction.Operands[i];

                    var slot = op switch
                    {
                        StackOffset direct => direct,
                        AddressOf { Target: StackOffset addressed } => addressed,
                        _ => (StackOffset?)null
                    };

                    if (slot is { } offset)
                    {
                        // This can only be done before modifying any of the instruction operands,
                        // as doing so will make the dictionary lookup impossible.
                        state ??= _instructionState[instruction].Size;

                        var actual = new StackOffset(state.Value + offset.Offset);
                        instruction.SetOperand(i, op is AddressOf ? new AddressOf(actual) : actual);
                    }
                }
            }
        }
    }

    // Traverse the graph and calculate the stack state for each block and instruction
    private void TraverseGraph(Block initialBlock, string methodName, int initialVisitedBlockCount = 0)
    {
        var blockLevelState = new Stack<(Block, int)>();
        blockLevelState.Push((initialBlock, initialVisitedBlockCount));

        while (blockLevelState.Count > 0)
        {
            var (block, visitedBlockCount) = blockLevelState.Pop();

            // Copy current state
            var incomingState = _inComingState[block];
            var currentState = incomingState.Copy();

            // Process instructions
            foreach (var instruction in block.Instructions)
            {
                _instructionState[instruction] = currentState;

                if (instruction.OpCode == OpCode.ShiftStack)
                {
                    var offset = (int)((Immediate)instruction.Operands[0]).Value;
                    currentState = currentState.Copy();
                    currentState.Size += offset;
                }
                else if (instruction is { OpCode: OpCode.Move, Operands: [Register destination, Register source] })
                {
                    if (source.Name == "rsp")
                    {
                        // `mov reg, rsp` captures the stack pointer (typically a frame pointer in the prologue).
                        _capturedStackPointers[destination.Name] = currentState.Size;
                    }
                    else if (destination.Name == "rsp" && _capturedStackPointers.TryGetValue(source.Name, out var frameSize))
                    {
                        // `mov rsp, reg` restores a previously captured stack pointer (e.g. `mov esp, ebp`),
                        // so the tracked size jumps back to whatever it was at the point of capture.
                        currentState = currentState.Copy();
                        currentState.Size = frameSize;
                    }
                    else
                    {
                        // Following a register that gets reassigned would need flow analysis, so stop trusting it entirely
                        _capturedStackPointers.Remove(destination.Name);
                    }
                }
                else if (block.Instructions[^1] == instruction && block.BlockType == BlockType.TailCall)
                {
                    // Tail calls clear stack
                    currentState = currentState.Copy();
                    currentState.Size = 0;
                }
                else if (instruction.Destination is Register writtenRegister)
                {
                    _capturedStackPointers.Remove(writtenRegister.Name);
                }
            }

            // Tail calls clear stack
            if (block.BlockType == BlockType.TailCall)
                currentState.Size = 0;

            _outGoingState[block] = currentState;

            visitedBlockCount++;

            if (MaxBlockVisitCount != -1 && visitedBlockCount > MaxBlockVisitCount)
                throw new DecompilerException(
                    $"Stack state not settling! " +
                    $"Method={methodName}, " +
                    $"Visits={visitedBlockCount}, " +
                    $"BlockID={block.ID}, " +
                    $"BlockType={block.BlockType}, " +
                    $"Incoming={incomingState.Size}, " +
                    $"Outgoing={currentState.Size}, " +
                    $"InstructionCount={block.Instructions.Count}");

            // Visit successors
            foreach (var successor in block.Successors)
            {
                // Already visited
                if (_inComingState.TryGetValue(successor, out var existingState))
                {
                    if (existingState.Size != currentState.Size)
                    {
                        _inComingState[successor] = currentState.Copy();
                        blockLevelState.Push((successor, visitedBlockCount + 1));
                    }
                }
                else
                {
                    // Set incoming delta and add to queue
                    _inComingState[successor] = currentState.Copy();
                    blockLevelState.Push((successor, visitedBlockCount + 1));
                }
            }
        }
    }

    private static void ReplaceStackWithRegisters(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;

        // Replace stack offset operands
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is StackOffset offset)
                    instruction.SetOperand(i, new Register(null, NameForSlot(offset)));

                if (operand is AddressOf { Target: StackOffset addressed })
                    instruction.SetOperand(i, new AddressOf(new Register(null, NameForSlot(addressed))));
            }
        }

        // Replace params
        for (var i = 0; i < method.ParameterOperands.Count; i++)
        {
            var parameter = method.ParameterOperands[i];

            if (parameter is StackOffset offset)
                method.ParameterOperands[i] = new Register(null, NameForSlot(offset));
        }
    }

    private static string NameForSlot(StackOffset offset) => offset.Offset < 0 ? $"stack_-{-offset.Offset:X}" : $"stack_{offset.Offset:X}";
}
