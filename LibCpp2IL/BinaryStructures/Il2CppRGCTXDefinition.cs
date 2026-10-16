using LibCpp2IL.Metadata;

namespace LibCpp2IL.BinaryStructures;

public class Il2CppRGCTXDefinition : ReadableClass
{
    public Il2CppRGCTXDataType type;

    public int MethodIndex => _defData?.MethodIndex ?? _constrainedData!.MethodIndex;

    public int TypeIndex => _defData?.TypeIndex ?? _constrainedData!.TypeIndex;

    public Il2CppMethodSpec MethodSpec => OwningContext.Metadata.GetMethodSpec(MethodIndex);

    public Il2CppType Type => OwningContext.Binary.GetType(Il2CppVariableWidthIndex<Il2CppType>.MakeTemporaryForFixedWidthUsage(TypeIndex));


    public class Il2CppRGCTXDefinitionData : ReadableClass
    {
        private int rgctxDataDummy;
        public int MethodIndex => rgctxDataDummy;
        public int TypeIndex => rgctxDataDummy;
        public override void Read(ClassReadingBinaryReader reader)
        {
            rgctxDataDummy = reader.ReadInt32();
        }
    }

    public class Il2CppRGCTXConstrainedData : ReadableClass
    {
        public int _typeIndex;
        public int _encodedMethodIndex;
        public int TypeIndex => _typeIndex;
        public int MethodIndex => _encodedMethodIndex;

        public override void Read(ClassReadingBinaryReader reader)
        {
            _typeIndex = reader.ReadInt32();
            _encodedMethodIndex = reader.ReadInt32();
        }
    }
    [Version(Min = 27.2f)]
    private Il2CppRGCTXConstrainedData? _constrainedData;

    private Il2CppRGCTXDefinitionData? _defData;

    public override void Read(ClassReadingBinaryReader reader)
    {
        if (IsAtLeast(108))
        {
            //packed down to 5 bytes now that it lives in the metadata file
            type = (Il2CppRGCTXDataType)reader.ReadByte();
            _defData = new Il2CppRGCTXDefinitionData();
            _defData.Read(reader);
            return;
        }

        if (IsLessThan(27.2f))
        {
            //Data is an inline index rather than a pointer: {int32 type; int32 data}
            type = (Il2CppRGCTXDataType)reader.ReadInt32();
            _defData = new Il2CppRGCTXDefinitionData();
            _defData.Read(reader);
            return;
        }

        //Pointers from 27.2 up to (but not including) 108: struct Il2CppRGCTXDefinition { Il2CppRGCTXDataType type; const void* data; }
        //On 64-bit the enum is padded up to pointer alignment, so consume those pad bytes before the pointer.
        type = (Il2CppRGCTXDataType)reader.ReadInt32();
        if (!reader.is32Bit)
            reader.Position += 4;

        var va = reader.ReadNUint();
        var bakPosition = reader.Position;

        reader.Position = OwningContext.Binary.MapVirtualAddressToRaw(va);

        if (type == Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CONSTRAINED)
        {
            _constrainedData = new Il2CppRGCTXConstrainedData();
            _constrainedData.Read(reader);
        }
        else
        {
            _defData = new Il2CppRGCTXDefinitionData();
            _defData.Read(reader);
        }

        reader.Position = bakPosition;
    }
}
