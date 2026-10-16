using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class RgctxResolverTests
{
    private static MethodAnalysisContext CreateMethod(ISILControlFlowGraph graph, ApplicationAnalysisContext app, params LocalVariable[] locals)
    {
        var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph = graph;
        method.Locals = locals.ToList();
        method.ParameterLocals = [];
        method.AppContext = app;
        return method;
    }

    [Test]
    public void ResolvesGenericTypeParameterEntryToRuntimeClassWrapper()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        // Find System.Lazy`1 - a generic type whose rgctx has an IL2CPP_RGCTX_DATA_CLASS entry
        // at index 0 that resolves to its own type parameter T.
        var lazyType = app.Assemblies
            .SelectMany(a => a.Types)
            .FirstOrDefault(t => t.FullName == "System.Lazy`1");

        Assert.That(lazyType, Is.Not.Null, "System.Lazy`1 must exist in the 2022 test game");
        Assert.That(lazyType!.GenericParameters.Count, Is.GreaterThan(0), "Lazy`1 must have generic parameters");

        Il2CppRGCTXDefinition[] entries;
        try { entries = lazyType.Definition!.RgctXs; }
        catch { Assert.Ignore("RgctXs not available for this metadata version"); return; }

        Assert.That(entries.Length, Is.GreaterThan(0), "Lazy`1 must have rgctx entries");
        var entry = entries[0];
        Assert.That(entry!.type, Is.AnyOf(
                Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CLASS,
                Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_TYPE),
            "entry 0 should be a CLASS or TYPE entry");

        var resolvedParam = app.ResolveIl2CppType(entry.Type);
        Assert.That(resolvedParam, Is.InstanceOf<GenericParameterTypeAnalysisContext>(),
            "entry 0 should resolve to the type parameter T");

        var is32Bit = app.Binary.is32Bit;
        var rgctxOffset = is32Bit ? 0x60L : 0xC0L;
        var pointerSize = is32Bit ? 4 : 8;

        var klassLocal = new LocalVariable("klass", new Register(null, "klass"))
        {
            Type = new RuntimeClassTypeAnalysisContext(lazyType, lazyType.DeclaringAssembly)
        };
        var tableLocal = new LocalVariable("table", new Register(null, "table"));
        var destLocal  = new LocalVariable("dest",  new Register(null, "dest"));

        var instructions = new List<Instruction>
        {
            // table := [klass + rgctxOffset]
            new(0, OpCode.Move, tableLocal, new MemoryOperand(klassLocal, null, rgctxOffset, 0)),
            // dest := [table + 0]
            new(1, OpCode.Move, destLocal, new MemoryOperand(tableLocal, null, 0, 0)),
            new(2, OpCode.Return),
        };

        var graph = new ISILControlFlowGraph(instructions);
        var method = CreateMethod(graph, app, klassLocal, tableLocal, destLocal);

        var changed = RgctxResolver.Run(method);

        Assert.That(changed, Is.True, "RgctxResolver should have rewritten at least one instruction");

        // The rgctx-table load should be typed as an Il2CppClass wrapper around T.
        Assert.That(tableLocal.Type, Is.InstanceOf<RgctxTableTypeAnalysisContext>(),
            "table local should be typed as an rgctx table for Lazy`1");

        // The entry load should be typed as RuntimeClassTypeAnalysisContext wrapping T.
        Assert.That(destLocal.Type, Is.InstanceOf<RuntimeClassTypeAnalysisContext>(),
            "dest local should be an Il2CppClass wrapper");
        var destKlass = (RuntimeClassTypeAnalysisContext)destLocal.Type!;
        Assert.That(destKlass.RepresentedType, Is.InstanceOf<GenericParameterTypeAnalysisContext>(),
            "the class wrapper should contain the T type parameter");
        Assert.That(destKlass.RepresentedType.FullName, Is.EqualTo("T"),
            "the contained type should be named T");
    }
}
