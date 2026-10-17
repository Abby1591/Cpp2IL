using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Text;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Model.Contexts;

public class GenericInstanceTypeAnalysisContext : ReferencedTypeAnalysisContext
{
    public TypeAnalysisContext GenericType { get; }

    public List<TypeAnalysisContext> GenericArguments { get; } = [];

    public sealed override TypeAttributes DefaultAttributes => GenericType.DefaultAttributes;

    public sealed override TypeAttributes? OverrideAttributes { get => GenericType.OverrideAttributes; set => GenericType.OverrideAttributes = value; }

    public sealed override string DefaultName => $"{GenericType.DefaultName}<{string.Join(", ", GenericArguments.Select(a => a.DefaultFullName))}>";

    public sealed override string? OverrideName
    {
        get => $"{GenericType.Name}<{string.Join(", ", GenericArguments.Select(a => a.FullName))}>";
        set => throw new NotSupportedException();
    }

    public sealed override string DefaultNamespace => GenericType.DefaultNamespace;

    public sealed override string? OverrideNamespace
    {
        get => GenericType.OverrideNamespace;
        set => GenericType.OverrideNamespace = value;
    }

    // The base type of a generic instance is the base type of the open generic definition, with the
    // instance's generic arguments substituted where the base is itself generic (e.g. Action<T>'s
    // MulticastDelegate, or Derived<T>'s Base<T> -> Base<actual>). Previously this was only populated
    // by the (TypeAnalysisContext, args) constructor, leaving instances built from metadata with a null
    // base type - which in turn made IsDelegate/IsValueType/IsEnumType resolve incorrectly.
    public sealed override TypeAnalysisContext? DefaultBaseType => InstantiateBaseType();

    private TypeAnalysisContext? InstantiateBaseType()
    {
        var baseType = GenericType.BaseType;

        if (baseType == null || !baseType.HasAnyGenericParameters())
            return baseType;

        try
        {
            return GenericInstantiation.Instantiate(baseType, GenericArguments, []);
        }
        catch (Exception e) when (e is ArgumentOutOfRangeException or IndexOutOfRangeException)
        {
            // Nested/partial generics can reference declaring-type parameters we don't hold here - fall back.
            return baseType;
        }
    }

    private List<MethodAnalysisContext>? _instantiatedMethods;

    // Expose the open generic's methods with this instance's type arguments substituted, so that callers
    // (delegate recovery, type resolution, display) see e.g. Action<string>.Invoke(string) rather than nothing.
    public override List<MethodAnalysisContext> Methods => _instantiatedMethods ??= BuildInstantiatedMethods();

    private List<MethodAnalysisContext> BuildInstantiatedMethods()
    {
        var methods = new List<MethodAnalysisContext>(GenericType.Methods.Count);

        foreach (var method in GenericType.Methods)
        {
            try
            {
                methods.Add(new ConcreteGenericMethodAnalysisContext(method, GenericArguments, []));
            }
            catch (ArgumentException)
            {
                // Arity mismatch (e.g. a nested type whose declaring-type arguments differ) - keep the base method.
                methods.Add(method);
            }
        }

        return methods;
    }

    public sealed override Il2CppTypeEnum Type => Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;

    public sealed override bool IsGenericInstance => true;

    public sealed override bool IsValueType => GenericType.IsValueType; //We don't set a definition so the default implementation cannot determine if we're a value type or not. 

    // instances being constructed on the current thread, keyed by their cache identity (see GetOrCreate for why)
    [ThreadStatic] private static Dictionary<(ApplicationAnalysisContext, Il2CppType), GenericInstanceTypeAnalysisContext>? _underConstruction;

    private GenericInstanceTypeAnalysisContext(Il2CppType rawType, ApplicationAnalysisContext context) : base(context.ResolveContextForAssembly(rawType.GetGenericClass().TypeDefinition.DeclaringAssembly!))
    {
        var underConstruction = _underConstruction ??= new();
        underConstruction[(context, rawType)] = this;
        try
        {
            //Generic type has to be a type definition
            var gClass = rawType.GetGenericClass();
            GenericType = context.ResolveContextForType(gClass.TypeDefinition) ?? throw new($"Could not resolve type {gClass.TypeDefinition.FullName} for generic instance base type");

            GenericArguments.AddRange(gClass.Context.ClassInst!.Types.Select(context.ResolveIl2CppType)!);

            SetDeclaringType();
        }
        finally
        {
            underConstruction.Remove((context, rawType));
        }
    }

    public GenericInstanceTypeAnalysisContext(TypeAnalysisContext genericType, IEnumerable<TypeAnalysisContext> genericArguments) : base(genericType.CustomAttributeAssembly)
    {
        GenericType = genericType;
        GenericArguments.AddRange(genericArguments);

        SetDeclaringType();
    }

    /// <summary>
    /// Get or create a <see cref="GenericInstanceTypeAnalysisContext"/> from an <see cref="Il2CppType"/>.
    /// </summary>
    /// <param name="rawType">The underlying <see cref="Il2CppType"/>.</param>
    /// <param name="referencedFrom">The assembly that is referencing this generic instance.</param>
    /// <returns>The context for the <paramref name="rawType"/>.</returns>
    public static GenericInstanceTypeAnalysisContext GetOrCreate(Il2CppType rawType, ApplicationAnalysisContext referencedFrom)
    {
        if (rawType.Type != Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST)
            throw new ArgumentException($"Cannot create {nameof(GenericInstanceTypeAnalysisContext)} from type {rawType.Type}. Expected {Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST}.");

        // A self-referencing generic re-enters here while we're still building it (#469). In this case, the constructing thread gets 
        // its own in-progress instance from a thread-local map instead (otherwise it recurses into Lazy.Value, which throws).
        if (_underConstruction != null && _underConstruction.TryGetValue((referencedFrom, rawType), out var partial))
            return partial;

        return referencedFrom.GenericInstanceTypesByIl2CppType
            .GetOrAdd(rawType, key => new Lazy<GenericInstanceTypeAnalysisContext>(() => new GenericInstanceTypeAnalysisContext(key, referencedFrom)))
            .Value;
    }

    public override string GetCSharpSourceString()
    {
        var sb = new StringBuilder();

        sb.Append(GenericType.GetCSharpSourceString());
        sb.Append('<');
        var first = true;
        foreach (var genericArgument in GenericArguments)
        {
            if (!first)
                sb.Append(", ");
            else
                first = false;

            sb.Append(genericArgument.GetCSharpSourceString());
        }

        sb.Append('>');

        return sb.ToString();
    }

    private void SetDeclaringType()
    {
        var declaringType = GenericType.DeclaringType;
        if (declaringType is null)
            return;

        DeclaringType = declaringType.GenericParameters.Count == 0
            ? declaringType
            : declaringType.MakeGenericInstanceType(GenericArguments.Take(declaringType.GenericParameters.Count));
    }
}
