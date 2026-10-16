#nullable enable
using System;
using System.IO;
using LibCpp2IL;
using LibCpp2IL.BinaryStructures;
using Xunit;

namespace LibCpp2ILTests;

public class Il2CppRGCTXDefinitionTests
{
    private const uint ImageBase = 0x10000000;

    private sealed class TestBinary(byte[] bytes) : Il2CppBinary(new MemoryStream(bytes))
    {
        public override long RawLength => bytes.LongLength;
        public override byte GetByteAtRawAddress(ulong addr) => bytes[addr];

        public override long MapVirtualAddressToRaw(ulong uiAddr, bool throwOnError = true)
        {
            if (uiAddr < ImageBase || uiAddr - ImageBase >= (ulong)bytes.Length)
            {
                if (throwOnError)
                    throw new OverflowException($"Provided address, 0x{uiAddr:X}, is out of range.");
                return -1;
            }

            return (long)(uiAddr - ImageBase);
        }

        public override ulong MapRawAddressToVirtual(uint offset, bool throwOnError = true) => ImageBase + offset;
        public override ulong GetRva(ulong pointer) => pointer - ImageBase;
        public override ReadOnlySpan<byte> GetRawBinaryContent() => bytes;
        public override ulong GetVirtualAddressOfExportedFunctionByName(string toFind) => 0;
        public override ReadOnlySpan<byte> GetEntirePrimaryExecutableSection() => bytes;
        public override ulong GetVirtualAddressOfPrimaryExecutableSection() => ImageBase;
    }

    private static (TestBinary Binary, LibCpp2IlContext Context) CreateContext(bool is32Bit, byte[]? bytes = null)
    {
        var binary = new TestBinary(bytes ?? new byte[0x800]) { is32Bit = is32Bit };
        var context = new LibCpp2IlContext(new LibCpp2IlMain.LibCpp2IlSettings());
        context.Binary = binary;
        return (binary, context);
    }

    private static Il2CppRGCTXDefinition CreateDefinition(LibCpp2IlContext context, float metadataVersion = 31f)
        => new()
        {
            MetadataVersion = metadataVersion,
            OwningContext = context,
        };

    [Fact]
    public void Read_ReadsPointerBasedEntriesWith8ByteStrideOn32Bit()
    {
        var bytes = new byte[0x800];
        var span = bytes.AsSpan();

        // Entry 0 at raw 0x100: {type=CLASS, data=&0x10000400}
        BitConverter.TryWriteBytes(span.Slice(0x100, 4), (int)Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CLASS);
        BitConverter.TryWriteBytes(span.Slice(0x104, 4), ImageBase + 0x400);
        // Entry 1 at raw 0x108: {type=METHOD, data=&0x10000408}
        BitConverter.TryWriteBytes(span.Slice(0x108, 4), (int)Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_METHOD);
        BitConverter.TryWriteBytes(span.Slice(0x10C, 4), ImageBase + 0x408);
        // Targets hold packed metadata indexes.
        BitConverter.TryWriteBytes(span.Slice(0x400, 4), 15152);
        BitConverter.TryWriteBytes(span.Slice(0x408, 4), 14968);

        var (binary, context) = CreateContext(is32Bit: true, bytes);

        binary.Position = 0x100;
        var first = CreateDefinition(context);
        first.Read(binary);
        var second = CreateDefinition(context);
        second.Read(binary);

        Assert.Equal(Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CLASS, first.type);
        Assert.Equal(15152, first.TypeIndex);
        Assert.Equal(Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_METHOD, second.type);
        Assert.Equal(14968, second.TypeIndex);
    }

    [Fact]
    public void Read_ReadsPointerBasedEntriesWithPadded16ByteStrideOn64Bit()
    {
        var bytes = new byte[0x800];
        var span = bytes.AsSpan();

        // Entry 0 at raw 0x100: {int32 type, int32 pad, uint64 data}
        BitConverter.TryWriteBytes(span.Slice(0x100, 4), (int)Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_TYPE);
        BitConverter.TryWriteBytes(span.Slice(0x104, 4), 0); // struct padding
        BitConverter.TryWriteBytes(span.Slice(0x108, 8), (ulong)(ImageBase + 0x400));
        // Entry 1 at raw 0x110
        BitConverter.TryWriteBytes(span.Slice(0x110, 4), (int)Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_ARRAY);
        BitConverter.TryWriteBytes(span.Slice(0x114, 4), 0);
        BitConverter.TryWriteBytes(span.Slice(0x118, 8), (ulong)(ImageBase + 0x408));
        // Targets hold packed metadata indexes.
        BitConverter.TryWriteBytes(span.Slice(0x400, 4), 42);
        BitConverter.TryWriteBytes(span.Slice(0x408, 4), 43);

        var (binary, context) = CreateContext(is32Bit: false, bytes);

        binary.Position = 0x100;
        var first = CreateDefinition(context);
        first.Read(binary);
        var second = CreateDefinition(context);
        second.Read(binary);

        Assert.Equal(Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_TYPE, first.type);
        Assert.Equal(42, first.TypeIndex);
        Assert.Equal(Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_ARRAY, second.type);
        Assert.Equal(43, second.TypeIndex);
    }

    [Fact]
    public void Read_ReadsConstrainedEntryDataOn32Bit()
    {
        var bytes = new byte[0x800];
        var span = bytes.AsSpan();
        BitConverter.TryWriteBytes(span.Slice(0x100, 4), (int)Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CONSTRAINED);
        BitConverter.TryWriteBytes(span.Slice(0x104, 4), ImageBase + 0x400);
        BitConverter.TryWriteBytes(span.Slice(0x400, 4), 777); // type index
        BitConverter.TryWriteBytes(span.Slice(0x404, 4), 888); // encoded method index

        var (binary, context) = CreateContext(is32Bit: true, bytes);

        binary.Position = 0x100;
        var definition = CreateDefinition(context);
        definition.Read(binary);

        Assert.Equal(Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CONSTRAINED, definition.type);
        Assert.Equal(777, definition.TypeIndex);
        Assert.Equal(888, definition.MethodIndex);
    }

    [Fact]
    public void Read_ReadsInlineIndexEntriesOnVersionsBelow27_2()
    {
        var bytes = new byte[0x800];
        var span = bytes.AsSpan();
        BitConverter.TryWriteBytes(span.Slice(0x100, 4), (int)Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_TYPE);
        BitConverter.TryWriteBytes(span.Slice(0x104, 4), 1234);

        var (binary, context) = CreateContext(is32Bit: true, bytes);

        binary.Position = 0x100;
        var definition = CreateDefinition(context, metadataVersion: 27.1f);
        definition.Read(binary);

        Assert.Equal(Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_TYPE, definition.type);
        Assert.Equal(1234, definition.TypeIndex);
    }
}
