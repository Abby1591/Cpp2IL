using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

#pragma warning disable IDE0305, IDE0300

/// <summary>
/// Calling-convention resolver for the X86 instruction set, which serves both 32-bit and 64-bit
/// binaries. Routes to <see cref="X64CallingConventionResolver"/> for 64-bit binaries and applies
/// the il2cpp/MSVC x86 stack-passing convention for 32-bit binaries.
/// </summary>
public class X86CallingConventionResolver : BaseCallingConventionResolver
{
    const int ptrSize32 = 4;

    private static readonly X64CallingConventionResolver X64 = new();

    private static bool Is32Bit(MethodAnalysisContext ctx) => ctx.AppContext.Binary.PointerSizeBytes == 4;

    private static bool Is32Bit(ApplicationAnalysisContext app) => app.Binary.PointerSizeBytes == 4;

    public override Register ReturnRegister(MethodAnalysisContext ctx)
        => Is32Bit(ctx)
            ? new(null, IsFloatingPoint(ctx.ReturnType) ? "xmm0" : "rax")
            : X64.ReturnRegister(ctx);

    // On x86 the hidden return buffer (when used) arrives as the first stack argument, not in a register.
    public override Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx)
        => Is32Bit(ctx) ? null : X64.HiddenReturnBufferRegister(ctx);

    public override bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx)
    {
        if (!Is32Bit(ctx))
            return X64.ReturnsViaHiddenBuffer(ctx);

        if (ctx.IsVoid)
            return false;

        var returnType = ctx.ReturnType;
        if (!returnType.IsValueType || IsFloatingPoint(returnType))
            return false;

        var size = TypeSizes.UnboxedSize(returnType, ptrSize32);
        if (size == 0)
            return false; // unknown size (e.g. generic): assume a register return

        // MSVC x86 returns structs of up to 8 bytes in EAX:EDX; anything larger uses a
        // hidden pointer-to-caller-buffer argument passed on the stack.
        return size > 8;
    }

    // il2cpp on x86 (MSVC targets) passes every argument on the stack, cdecl-style, so there
    // are no argument registers to preserve for unknown callees.
    protected override (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app)
        => Is32Bit(app) ? ([], []) : X64.RawRegistersFor(app);

    protected override bool UsesShadowedArgumentSlots(ApplicationAnalysisContext app)
        => !Is32Bit(app) && X64.UsesShadowedArgumentSlotsFor(app);

    /// <summary>
    /// Call-site layout. On x64 this is the register/stack layout the x64 resolver defines.
    /// On x86 the arguments were just pushed (last push = first argument at [esp]) and the
    /// return address is not part of the tracked stack state, so the first argument sits at
    /// offset 0 relative to the current stack pointer.
    /// </summary>
    public override IOperand[] ResolveForManaged(MethodAnalysisContext ctx)
        => Is32Bit(ctx) ? ResolveStackArguments(ctx, entryRelative: false) : X64.ResolveForManaged(ctx);

    /// <summary>
    /// Callee-entry layout. Identical to the call-site layout on x64 (register-based). On x86
    /// the return address occupies [esp+0] in the callee's own frame, shifting every argument
    /// up by one pointer size.
    /// </summary>
    public IOperand[] ResolveForManagedBody(MethodAnalysisContext ctx)
        => Is32Bit(ctx) ? ResolveStackArguments(ctx, entryRelative: true) : X64.ResolveForManaged(ctx);

    internal IOperand[] ResolveStackArguments(MethodAnalysisContext ctx, bool entryRelative)
    {
        List<IOperand> args = [];

        var offset = entryRelative ? ptrSize32 : 0;

        void AddParameter()
        {
            args.Add(new StackOffset(offset));
            offset += ptrSize32;
        }

        void AddTypedParameter(TypeAnalysisContext? type)
        {
            args.Add(new StackOffset(offset));
            offset += type == null ? ptrSize32 : StackArgumentSize(type, ctx.AppContext.Binary.PointerSizeBytes);
        }

        if (ReturnsViaHiddenBuffer(ctx))
            offset += ptrSize32; // the hidden buffer pointer occupies the first stack slot

        if (!ctx.IsStatic)
            AddParameter(); // this

        foreach (var parameter in ctx.Parameters)
            AddTypedParameter(parameter.ParameterType);

        AddParameter(); // The MethodInfo argument

        return args.ToArray();
    }

    // MSVC x86 passes each argument as whole 4-byte stack granules: pointer-sized for
    // reference types, byrefs and uninstantiated generic parameters, 8 bytes for double and
    // long long, and the full unboxed size (rounded up to 4) for structs. Counting every
    // parameter as a single slot shifts all later arguments - including the trailing
    // MethodInfo pointer - off their native frame positions, so frame reads like [ebp+0x1C]
    // land on an unmapped fresh local instead of the typed parameter.
    internal static int StackArgumentSize(TypeAnalysisContext type, int metadataPointerSize)
    {
        type = type switch
        {
            CustomModifierTypeAnalysisContext modifier => modifier.ElementType,
            _ => type,
        };

        if (!type.IsValueType)
            return ptrSize32;

        // The header in the metadata's instance size matches the game's own pointer size.
        var size = TypeSizes.UnboxedSize(type, metadataPointerSize);
        if (size <= 0)
            return ptrSize32;

        return (int)((size + 3) & ~3L);
    }
}
