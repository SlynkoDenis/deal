package deal.codegen.jvm;

import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The JVM host ABI emission surface of the production project artifact
 * (ISSUE-0650; design source
 * {@code host-module-load-and-host-call-realization} H1, H2 items 1-2 and
 * H7's carrier set; the host-load contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C2's "the JVM
 * artifact additionally carries the host ABI surface and the synthesized
 * host-record scope it needs").
 *
 * <p>One instance of this unit covers one production project compile and
 * emits, from the compile's host declaration surface alone:</p>
 *
 * <ol>
 *   <li>the module-keyed load entry of every host import (idempotent per
 *       module; the implementation class resolved through the landed
 *       {@link JvmBackend#classNameFor(String)} derivation, each declared
 *       function export bound as a {@code java.lang.reflect.Method}
 *       through the landed declared-parameter-class projection, each
 *       declared class export's mandatory {@code <C>_defaults} map
 *       captured) and the per-export wrappers with the declared parameter
 *       cells and the declared return cell (the pinned E8010 projections
 *       at the call origin);</li>
 *   <li>the shared boundary-check seam of those cells (the parameter and
 *       return projections, the closed runtime-kind projection, and the
 *       malformed-string reason) — the emitted wrapper is the single check
 *       authority for the host cells;</li>
 *   <li>the synthesized top-level {@code $DealRt} host-record and
 *       host-carrier scope: one {@code $Host$<specifier>$<Class>} record
 *       per declared host class (declared fields in declaration order,
 *       settled carriers), the declared element-shape array carriers
 *       (including the per-class {@code $HostArr$} wrappers), {@code
 *       Bytes}, the {@code FnValue} interface, and one per-signature
 *       wrapper class per declared function position (the landed
 *       {@link JvmBackend#fnShapeId(Type.Func)} /
 *       {@link JvmBackend#escapedIdentifier(String)} derivation), so the
 *       deployed host implementations compile unchanged.</li>
 * </ol>
 *
 * <p><b>Unreachability.</b> This unit reads the validated project's
 * {@code MODULE_IMPORT} facts, the compile's host declaration surface,
 * and the static name/descriptor derivations only: no AST, no checker
 * result, no route input, no retained backend generation entry point, and
 * no host code at compile time.</p>
 */
final class JvmHostAbiEmission {

    /** One host import of the closure: the resolved module identity, the raw specifier, and the declaration facts. */
    record HostModule(String modulePath, String rawSpecifier,
                      HostDeclarationSurface.DeclarationFacts facts) {
    }

    /** One declared host class synthesized as a shared {@code $DealRt} record. */
    private record RecordInfo(String simpleName, String arrayWrapper,
                              String identityText, List<FieldInfo> fields) {
    }

    /**
     * One declared field of a synthesized record: the declared field name,
     * its translated Java name, the optional flag, the declared type's
     * canonical descriptor text (the host-crossing projections' key), and
     * the settled host-facing storage type.
     */
    private record FieldInfo(String name, String javaName, String storageType,
                             String descriptorText, boolean optional) {
    }

    /**
     * The construction facts of one declared host class (ISSUE-0624;
     * {@code semantic-ir-construct-coverage-cutover} K10): the synthesized
     * record's simple name, the load-time-captured {@code <C>_defaults}
     * field, the canonical identity text, and the declared fields in
     * declaration order.
     */
    record HostClassFacts(String recordSimpleName, String defaultsField,
                          String identityText, List<HostFieldFacts> fields) {
    }

    /** One declared field of a host class construction (declaration order). */
    record HostFieldFacts(String name, String javaName, String storageType,
                          String descriptorText, boolean optional) {
    }

    private final List<HostModule> modules;
    /**
     * The production artifact's top-level class name (the crossing
     * bridges' host-to-DEAL delegation target): the emitted bridge
     * classes live in the {@code $DealRt} scope, so they name the class
     * explicitly.
     */
    private final String artifactClass;
    /** The per-signature wrapper classes by shape id (declaration order). */
    private final Map<String, Type.Func> shapes = new LinkedHashMap<>();
    /** The synthesized records by simple name (declaration order). */
    private final Map<String, RecordInfo> records = new LinkedHashMap<>();
    /** The synthesized records by canonical identity text (the class identity join). */
    private final Map<String, RecordInfo> recordsByIdentity = new LinkedHashMap<>();
    /** The per-class array-wrapper simple names by class-carrying specifier/name key. */
    private final Map<String, String> classArrayWrappers = new LinkedHashMap<>();
    /** The declared array descriptor → element type (the crossing source). */
    private final Map<String, Type> arrayElements = new LinkedHashMap<>();

    JvmHostAbiEmission(List<HostModule> modules, String artifactClass) {
        this.modules = List.copyOf(Objects.requireNonNull(modules,
            "modules must not be null"));
        this.artifactClass = Objects.requireNonNull(artifactClass,
            "artifactClass must not be null");
        for (HostModule module : this.modules) {
            for (Map.Entry<String, HostDeclarationSurface.DeclaredClass> entry
                    : module.facts().classes().entrySet()) {
                declareRecord(module, entry.getKey(), entry.getValue());
            }
        }
        for (HostModule module : this.modules) {
            for (Map.Entry<String, Type> export
                    : module.facts().exports().entrySet()) {
                collectType(module, export.getValue());
                collectArrayElement(export.getValue());
            }
            for (HostDeclarationSurface.DeclaredClass declared
                    : module.facts().classes().values()) {
                for (HostDeclarationSurface.DeclaredField field : declared.fields()) {
                    collectArrayElement(field.type());
                }
            }
        }
    }

    /** Collects every declared array position's element type (the crossing shapes). */
    private void collectArrayElement(Type type) {
        switch (type) {
            case Type.Nullable nullable -> collectArrayElement(nullable.inner());
            case Type.Func func -> {
                for (Type param : func.paramTypes()) {
                    collectArrayElement(param);
                }
                collectArrayElement(func.returnType());
            }
            case Type.Array array -> {
                arrayElements.putIfAbsent(descriptorText(array), array.element());
                collectArrayElement(array.element());
            }
            default -> {
            }
        }
    }

    // =========================================================================
    // Discovery (compile-time only)
    // =========================================================================

    /**
     * The host imports of the closure in dependency and import order,
     * deduplicated by the resolved module identity: the module is the load
     * key, so two aliases (or two declaration imports) of one host module
     * contribute exactly one load entry and one shared surface.
     */
    static List<HostModule> collect(ExecutableLoweredProject project,
                                    HostDeclarationSurface surface) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(surface, "surface must not be null");
        Map<String, HostModule> modules = new LinkedHashMap<>();
        for (Map.Entry<ModuleId, LoweredModuleUnit> entry
                : project.modules().entrySet()) {
            for (SemanticOp op : entry.getValue().ops()) {
                if (op.kind() != SemanticOpKind.MODULE_IMPORT) {
                    continue;
                }
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) op.payload();
                if (payload.kind() != ModuleImportKind.HOST) {
                    continue;
                }
                HostDeclarationSurface.DeclarationFacts facts =
                    surface.require(payload.resolvedModule());
                if (facts.kind()
                        != HostDeclarationSurface.DeclarationKind.HOST) {
                    throw new IllegalStateException("the declaration module '"
                        + payload.resolvedModule().path() + "' of MODULE_IMPORT "
                        + op.opId() + " is kind " + facts.kind()
                        + ": the extern-C declaration load is the FFI child's"
                        + " (fail-closed remnant)");
                }
                modules.putIfAbsent(payload.resolvedModule().path(),
                    new HostModule(payload.resolvedModule().path(),
                        payload.rawSpecifier(), facts));
            }
        }
        return List.copyOf(modules.values());
    }

    /** The module key of one host import identity (injective, `$`-free). */
    static String key(String modulePath) {
        return JvmBackend.escapedIdentifier(modulePath);
    }

    /**
     * The construction facts of one declared host class (ISSUE-0624; K10),
     * or {@code null} when the class identity is not a declared host class
     * of this compile's surface — the fail-closed resolution the host
     * construction arm requires.
     */
    HostClassFacts hostClassFacts(ClassId classId) {
        Objects.requireNonNull(classId, "classId must not be null");
        RecordInfo record = recordsByIdentity.get(classId.text());
        if (record == null) {
            return null;
        }
        for (HostModule module : modules) {
            for (HostDeclarationSurface.DeclaredClass declared
                    : module.facts().classes().values()) {
                if (!declared.name().equals(classId.name())) {
                    continue;
                }
                Type.Class classType = classTypeOf(module, classId.name());
                if (classType == null
                        || !descriptorText(classType).equals(record.identityText())) {
                    continue;
                }
                List<HostFieldFacts> fields = new ArrayList<>();
                for (FieldInfo field : record.fields()) {
                    fields.add(new HostFieldFacts(field.name(), field.javaName(),
                        field.storageType(), field.descriptorText(), field.optional()));
                }
                return new HostClassFacts(record.simpleName(),
                    defaultsField(key(module.modulePath()), classId.name()),
                    record.identityText(), List.copyOf(fields));
            }
        }
        return null;
    }

    static String loadedFlag(String key) {
        return "__hostLoaded$" + key;
    }

    static String classField(String key) {
        return "__hostClass$" + key;
    }

    static String loadEntry(String key) {
        return "__hostLoad$" + key;
    }

    static String methodField(String key, String exportName) {
        return "__hostM$" + key + "$" + JvmBackend.javaName(exportName);
    }

    static String defaultsField(String key, String className) {
        return "__hostD$" + key + "$" + JvmBackend.javaName(className);
    }

    static String wrapperName(String key, String exportName) {
        return "__host$" + key + "$" + JvmBackend.javaName(exportName);
    }

    /** The canonical descriptor text of one declared type (the one producer). */
    static String descriptorText(Type type) {
        return JvmBackend.typeDescriptor(type);
    }

    private void declareRecord(HostModule module, String className,
                               HostDeclarationSurface.DeclaredClass declared) {
        Type.Class classType = classTypeOf(module, className);
        String identityText = descriptorText(classType);
        String specifier = externalSpecifier(classType);
        String simple = JvmBackend.hostRecordSimpleName(specifier, className);
        if (records.containsKey(simple)) {
            return;
        }
        List<FieldInfo> fields = new ArrayList<>();
        for (HostDeclarationSurface.DeclaredField field : declared.fields()) {
            Type fieldType = field.type();
            // The declared field type carries its own nullability: a
            // required-present `T | null` field stores the boxed/reference
            // carrier exactly like an optional field does (the optional flag
            // is the omission rule, not the nullability rule).
            String storage = carrierType(fieldType, field.declaration().optional());
            fields.add(new FieldInfo(field.declaration().name(),
                JvmBackend.javaName(field.declaration().name()), storage,
                descriptorText(fieldType), field.declaration().optional()));
        }
        String arrayWrapper = "$HostArr$" + JvmBackend.escapedIdentifier(
            specifier.replace('.', '/')) + "$" + JvmBackend.javaName(className);
        RecordInfo record = new RecordInfo(simple, arrayWrapper, identityText, fields);
        // The record registers before its field types are collected: a
        // self-referential declared class (a class-typed or class-array
        // field naming its own class, the `presence.Config` shape) must
        // resolve its own record, never re-enter this declaration.
        records.put(simple, record);
        recordsByIdentity.put(identityText, record);
        classArrayWrappers.putIfAbsent(classNameKey(specifier, className),
            arrayWrapper);
        for (HostDeclarationSurface.DeclaredField field : declared.fields()) {
            collectType(module, field.type());
        }
    }

    /** Collects every shape the declared type positions need. */
    private void collectType(HostModule owner, Type type) {
        switch (type) {
            case Type.Nullable nullable -> collectType(owner, nullable.inner());
            case Type.Array array -> collectType(owner, array.element());
            case Type.Func func -> {
                shapes.putIfAbsent(JvmBackend.fnShapeId(func), func);
                for (Type param : func.paramTypes()) {
                    collectType(owner, param);
                }
                collectType(owner, func.returnType());
            }
            case Type.Class cls -> {
                // A class position needs its synthesized record; the
                // declaring declaration module is resolved through the
                // class's carried external specifier.
                if (!records.containsKey(recordSimpleNameOf(cls))) {
                    HostModule declaring = moduleOfClass(owner, cls);
                    if (declaring == null) {
                        throw new IllegalStateException("the declared class '"
                            + cls.name() + "' of " + descriptorText(cls)
                            + " has no declaration-surface module in the"
                            + " closure (a producer defect)");
                    }
                    declareRecord(declaring, cls.name(),
                        declaring.facts().declaredClass(cls.name()));
                }
            }
            default -> {
            }
        }
    }

    /** The declaration module declaring one class type (its own module first). */
    private HostModule moduleOfClass(HostModule owner, Type.Class cls) {
        String specifier = externalSpecifier(cls);
        for (HostModule module : modules) {
            if (module == owner && module.facts().declaredClass(cls.name()) != null) {
                return module;
            }
            if (matchesSpecifier(module.rawSpecifier(), specifier)) {
                return module;
            }
        }
        return owner.facts().declaredClass(cls.name()) != null ? owner : null;
    }

    private static boolean matchesSpecifier(String raw, String specifier) {
        if (raw == null || specifier == null) {
            return false;
        }
        return raw.equals(specifier)
            || raw.replace('/', '.').equals(specifier.replace('/', '.'))
            || raw.replace('.', '/').equals(specifier.replace('.', '/'));
    }

    private static String externalSpecifier(Type.Class cls) {
        CanonicalModuleIdentity identity = cls.identity().moduleIdentity();
        if (identity instanceof CanonicalModuleIdentity.ExternalModule external) {
            return external.rawImportSpecifier();
        }
        throw new IllegalStateException("the declared host class '"
            + cls.name() + "' carries the non-external identity "
            + identity + " (a producer defect)");
    }

    /** The canonical class type of one declared class of one host module. */
    private Type.Class classTypeOf(HostModule module, String className) {
        for (Type export : module.facts().exports().values()) {
            Type candidate = unwrapNullable(export);
            if (candidate instanceof Type.Class cls && cls.name().equals(className)) {
                return cls;
            }
        }
        for (HostDeclarationSurface.DeclaredClass declared
                : module.facts().classes().values()) {
            for (HostDeclarationSurface.DeclaredField field : declared.fields()) {
                Type candidate = unwrapNullable(field.type());
                if (candidate instanceof Type.Class cls && cls.name().equals(className)) {
                    return cls;
                }
            }
        }
        return Types.classType(className, new CanonicalClassIdentity(
            new CanonicalModuleIdentity.ExternalModule(module.rawSpecifier()),
            className));
    }

    private static Type unwrapNullable(Type type) {
        return type instanceof Type.Nullable nullable ? nullable.inner() : type;
    }

    private static String recordSimpleNameOf(Type.Class cls) {
        return JvmBackend.hostRecordSimpleName(externalSpecifier(cls), cls.name());
    }

    private static String classNameKey(String specifier, String className) {
        return JvmBackend.escapedIdentifier(specifier.replace('.', '/')) + "$"
            + JvmBackend.javaName(className);
    }

    // =========================================================================
    // Java carrier projection
    // =========================================================================

    /**
     * The Java carrier of one declared position: primitives to their
     * production carriers (a nullable form to the boxed reference), {@code
     * bytes} to the shared {@code $DealRt.Bytes}, an array to its declared
     * element-shape carrier, a function type to its per-signature wrapper
     * class, and a declared class to its synthesized record. {@code
     * nullable} selects the boxed/nullable form (an optional record field
     * or a {@code ?T} position).
     */
    String carrierType(Type type, boolean nullable) {
        if (type instanceof Type.Nullable inner) {
            return carrierType(inner.inner(), true);
        }
        if (nullable) {
            return boxedCarrier(type);
        }
        return switch (type) {
            case Type.Null ignored -> "java.lang.Object";
            case Type.Boolean ignored -> "boolean";
            case Type.Int ignored -> "int";
            case Type.Number ignored -> "double";
            case Type.String ignored -> "java.lang.String";
            case Type.Bytes ignored -> "$DealRt.Bytes";
            case Type.Class cls -> "$DealRt." + recordSimpleNameOf(cls);
            case Type.Array array -> "$DealRt." + arrayCarrier(array.element());
            case Type.Func func -> "$DealRt." + JvmBackend.fnShapeId(func);
            case Type.Table ignored -> "java.lang.Object";
            default -> throw new IllegalStateException(
                "the declared host position " + type + " has no settled"
                    + " carrier (a producer defect)");
        };
    }

    private String boxedCarrier(Type inner) {
        return switch (inner) {
            case Type.Int ignored -> "java.lang.Integer";
            case Type.Number ignored -> "java.lang.Double";
            case Type.Boolean ignored -> "java.lang.Boolean";
            case Type.String ignored -> "java.lang.String";
            case Type.Bytes ignored -> "$DealRt.Bytes";
            case Type.Class cls -> "$DealRt." + recordSimpleNameOf(cls);
            case Type.Array array -> "$DealRt." + arrayCarrier(array.element());
            case Type.Func func -> "$DealRt." + JvmBackend.fnShapeId(func);
            default -> "java.lang.Object";
        };
    }

    /** The declared element-shape array carrier name of one element type. */
    private String arrayCarrier(Type element) {
        if (element instanceof Type.Nullable nullable) {
            return orNullArrayCarrier(nullable.inner());
        }
        return switch (element) {
            case Type.Int ignored -> "__IntArray";
            case Type.Number ignored -> "__NumberArray";
            case Type.String ignored -> "__StringArray";
            case Type.Boolean ignored -> "__BooleanArray";
            case Type.Bytes ignored -> "__BytesArray";
            case Type.Class cls -> classArrayWrapperName(cls);
            default -> "__RefArray";
        };
    }

    private String orNullArrayCarrier(Type inner) {
        return switch (inner) {
            case Type.Int ignored -> "__IntOrNullArray";
            case Type.Number ignored -> "__NumberOrNullArray";
            case Type.String ignored -> "__StringOrNullArray";
            case Type.Boolean ignored -> "__BooleanOrNullArray";
            case Type.Bytes ignored -> "__BytesOrNullArray";
            case Type.Class cls -> classArrayWrapperName(cls);
            default -> "__RefArray";
        };
    }

    private String classArrayWrapperName(Type.Class cls) {
        String specifier = externalSpecifier(cls);
        String name = classArrayWrappers.get(classNameKey(specifier, cls.name()));
        if (name != null) {
            return name;
        }
        String wrapper = "$HostArr$"
            + JvmBackend.escapedIdentifier(specifier.replace('.', '/')) + "$"
            + JvmBackend.javaName(cls.name());
        classArrayWrappers.put(classNameKey(specifier, cls.name()), wrapper);
        return wrapper;
    }

    /**
     * The declared parameter-class projection of one declared position:
     * the JVM {@code Class} literal the load-time export check uses —
     * primitives to their carrier class (a nullable primitive to the boxed
     * reference), {@code bytes} to {@code $DealRt.Bytes}, a declared array
     * to its element-shape carrier, a function type to its per-signature
     * wrapper class, and a declared class to its synthesized record.
     */
    String paramClassLiteral(Type type) {
        boolean nullable = type instanceof Type.Nullable;
        Type inner = unwrapNullable(type);
        return switch (inner) {
            case Type.Int ignored -> nullable ? "java.lang.Integer.class" : "int.class";
            case Type.Number ignored -> nullable ? "java.lang.Double.class" : "double.class";
            case Type.Boolean ignored -> nullable ? "java.lang.Boolean.class" : "boolean.class";
            case Type.String ignored -> "java.lang.String.class";
            case Type.Bytes ignored -> "$DealRt.Bytes.class";
            case Type.Class cls -> "$DealRt." + recordSimpleNameOf(cls) + ".class";
            case Type.Array array -> "$DealRt." + arrayCarrier(array.element()) + ".class";
            case Type.Func func -> "$DealRt." + JvmBackend.fnShapeId(func) + ".class";
            default -> "java.lang.Object.class";
        };
    }

    private static String javaString(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                case '\t' -> sb.append("\\t");
                case '\r' -> sb.append("\\r");
                default -> {
                    if (c < 0x20 || c > 0x7e) {
                        sb.append(String.format("\\u%04x", (int) c));
                    } else {
                        sb.append(c);
                    }
                }
            }
        }
        return sb.append('"').toString();
    }

    /**
     * The per-export wrapper name of one resolved host module and declared
     * function export: the emitted surface entry the sync host arms invoke.
     * A call whose resolved module or export has no emitted wrapper is a
     * fail-closed producer defect — never a silent call.
     */
    String requireWrapper(String modulePath, String exportName) {
            for (HostModule module : modules) {
                if (!module.modulePath().equals(modulePath)) {
                    continue;
                }
                for (Map.Entry<String, Type> export
                        : module.facts().exports().entrySet()) {
                    if (export.getKey().equals(exportName)
                            && export.getValue() instanceof Type.Func) {
                        return wrapperName(key(modulePath), exportName);
                    }
                }
            }
            throw new IllegalStateException("the host call resolves '" + modulePath
                + "." + exportName + "' but the emitted host ABI surface carries"
                + " no per-export wrapper for it (a producer defect)");
        }

    /**
     * The declared signature of one host module's function export: the
     * declaration surface's own type (the H7 crossing projection's single
     * declared-type source). A missing module or export is the same
     * fail-closed producer defect as {@link #requireWrapper}.
     */
    Type.Func declaredFunction(String modulePath, String exportName) {
            for (HostModule module : modules) {
                if (!module.modulePath().equals(modulePath)) {
                    continue;
                }
                Type declared = module.facts().exports().get(exportName);
                if (declared instanceof Type.Func func) {
                    return func;
                }
            }
            throw new IllegalStateException("the host call resolves '" + modulePath
                + "." + exportName + "' but the declaration surface carries no"
                + " declared function export for it (a producer defect)");
        }

    /**
     * The declared signature of one host-materialized function value's
     * crossing descriptor (a function-typed {@code HOST_TO_DEAL} return
     * position of a declared host export): the declaration surface's own
     * type, the H7 projection's single declared-type source. A crossing
     * descriptor with no declared position is a fail-closed producer
     * defect.
     */
    Type.Func declaredFunctionValue(String descriptorText) {
        for (HostModule module : modules) {
            for (Type export : module.facts().exports().values()) {
                Type.Func found = findDeclaredFunction(export, descriptorText);
                if (found != null) {
                    return found;
                }
            }
            for (HostDeclarationSurface.DeclaredClass declared
                    : module.facts().classes().values()) {
                for (HostDeclarationSurface.DeclaredField field : declared.fields()) {
                    Type.Func found = findDeclaredFunction(field.type(), descriptorText);
                    if (found != null) {
                        return found;
                    }
                }
            }
        }
        throw new IllegalStateException("the host-materialized function value of"
            + " descriptor '" + descriptorText + "' has no declared function"
            + " position in the compile's declaration surface (a producer defect)");
    }

    private static Type.Func findDeclaredFunction(Type type, String descriptorText) {
        switch (type) {
            case Type.Nullable nullable -> {
                return findDeclaredFunction(nullable.inner(), descriptorText);
            }
            case Type.Array array -> {
                return findDeclaredFunction(array.element(), descriptorText);
            }
            case Type.Func func -> {
                if (descriptorText(func).equals(descriptorText)) {
                    return func;
                }
                for (Type param : func.paramTypes()) {
                    Type.Func found = findDeclaredFunction(param, descriptorText);
                    if (found != null) {
                        return found;
                    }
                }
                return findDeclaredFunction(func.returnType(), descriptorText);
            }
            default -> {
                return null;
            }
        }
    }

    // =========================================================================
    // Emission: the artifact's host ABI class members
    // =========================================================================

    /**
     * Emits the host ABI class members of the production artifact: the
     * module-keyed load and binding fields, the per-module load entries,
     * the per-export wrappers, and the emitted boundary-check seam.
     */
    void emitClassMembers(StringBuilder out) {
        out.append("\n  // ---- JVM host ABI surface (ISSUE-0650; "
            + "host-module-load-and-host-call-realization H1/H2) ----\n");
        for (HostModule module : modules) {
            String key = key(module.modulePath());
            out.append("  static boolean ").append(loadedFlag(key)).append(";\n");
            out.append("  static java.lang.Class<?> ").append(classField(key))
                .append(";\n");
            for (Map.Entry<String, Type> export
                    : module.facts().exports().entrySet()) {
                if (export.getValue() instanceof Type.Func) {
                    out.append("  static java.lang.reflect.Method ")
                        .append(methodField(key, export.getKey())).append(";\n");
                }
            }
            for (String className : module.facts().classes().keySet()) {
                out.append("  static java.util.Map<java.lang.String, "
                    + "java.lang.Object> ")
                    .append(defaultsField(key, className)).append(";\n");
            }
        }
        out.append("\n");
        for (HostModule module : modules) {
            emitLoadEntry(out, module);
        }
        for (HostModule module : modules) {
            emitWrappers(out, module);
        }
        emitSeams(out);
        emitCrossings(out);
    }

    /**
     * Emits one module-keyed load entry: idempotent per module (a second
     * alias of one module binds nothing new), resolving the
     * implementation class through the landed
     * {@link JvmBackend#classNameFor(String)} derivation, binding one
     * {@code java.lang.reflect.Method} per declared function export in
     * declaration order with the declared parameter-class projection
     * (E8011 {@code missing host export '<name>' in module '<raw>'}), and
     * capturing one declared class export's mandatory
     * {@code <C>_defaults} map (E8011 when missing).
     */
    private void emitLoadEntry(StringBuilder out, HostModule module) {
        String key = key(module.modulePath());
        String raw = module.rawSpecifier();
        String clsName = JvmBackend.classNameFor(raw);
        out.append("  // Load-time validation of host module '").append(raw)
            .append("' (declared exports must exist; extras are ignored;"
                + " one load per module).\n");
        out.append("  static void ").append(loadEntry(key))
            .append("(java.lang.String oFile, int oLine, int oCol) {\n");
        out.append("    if (").append(loadedFlag(key))
            .append(") { return; }\n");
        out.append("    ").append(loadedFlag(key)).append(" = true;\n");
        out.append("    java.lang.Class<?> __h;\n");
        out.append("    try {\n");
        out.append("      __h = java.lang.Class.forName(")
            .append(javaString(clsName)).append(");\n");
        out.append("    } catch (java.lang.ClassNotFoundException __e) {\n");
        out.append("      throw JvmRuntime.fail(\"E8011\", \"host module '")
            .append(raw).append("' not found (class ").append(clsName)
            .append(")\", oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    }\n");
        out.append("    ").append(classField(key)).append(" = __h;\n");
        for (Map.Entry<String, Type> export
                : module.facts().exports().entrySet()) {
            if (export.getValue() instanceof Type.Func func) {
                StringBuilder params = new StringBuilder();
                for (Type param : func.paramTypes()) {
                    if (params.length() > 0) {
                        params.append(", ");
                    }
                    params.append(paramClassLiteral(param));
                }
                out.append("    ").append(methodField(key, export.getKey()))
                    .append(" = __hostMethod(__h, ").append(javaString(raw))
                    .append(", ").append(javaString(export.getKey()))
                    .append(", ").append(javaString(descriptorText(func)))
                    .append(", new java.lang.Class[]{ ").append(params)
                    .append(" }, oFile, oLine, oCol);\n");
            } else if (export.getValue() instanceof Type.Class cls) {
                out.append("    ").append(defaultsField(key, cls.name()))
                    .append(" = __hostDefaults(__h, ").append(javaString(raw))
                    .append(", ").append(javaString(cls.name()))
                    .append(", oFile, oLine, oCol);\n");
            } else {
                throw new IllegalStateException("the declared host export '"
                    + export.getKey() + "' of module '" + raw
                    + "' is neither a function nor a declared class (a"
                    + " producer defect)");
            }
        }
        // The loaded module's surface is the host import's namespace
        // value and the surface the reads child's EXPORT_READ resolves
        // (ISSUE-0651; H1 and H2 item 1): the module table carries one
        // production FunctionValue carrier per declared function export,
        // bridging the emitted per-export wrapper (the host-to-DEAL half
        // of H7's function crossing). The surface is written only after
        // every load-time binding and defaults capture succeeded, so a
        // failed load leaves no partial surface; a class export's entry
        // is the declaration-owned construction child's.
        List<Map.Entry<String, Type>> functionExports = new ArrayList<>();
        for (Map.Entry<String, Type> export : module.facts().exports().entrySet()) {
            if (export.getValue() instanceof Type.Func) {
                functionExports.add(export);
            }
        }
        if (!functionExports.isEmpty()) {
            out.append("    JvmRuntime.Table __surf = exportSurface(")
                .append(javaString(module.modulePath())).append(");\n");
            for (Map.Entry<String, Type> export : functionExports) {
                Type.Func func = (Type.Func) export.getValue();
                StringBuilder surfaceArgs = new StringBuilder();
                for (int i = 0; i < func.paramTypes().size(); i++) {
                    surfaceArgs.append("__a[").append(i).append("], ");
                }
                surfaceArgs.append("\"-\", 0, 0");
                // A declared null return emits a void wrapper: the
                // surface entry's invoker runs it as a statement and
                // yields the language null. A declared async return's
                // wrapper yields the host operation handle itself (never a
                // completion value), so the invoker passes it through
                // unchanged. Every other declared return is boxed onto the
                // production value carrier (the wrapper returns the
                // host-facing primitive/boxed carrier, while the surface
                // entry's invoker is a production function value carrier
                // over the same convention, so an int return becomes the
                // production Long).
                String invoker;
                if (func.returnType() instanceof Type.Null) {
                    invoker = "__a -> { " + wrapperName(key, export.getKey()) + "("
                        + surfaceArgs + "); return null; }";
                } else if (func.isAsync()) {
                    invoker = "__a -> " + wrapperName(key, export.getKey()) + "("
                        + surfaceArgs + ")";
                } else {
                    invoker = "__a -> " + JvmSemanticEmitter.productionValueOf(
                        func.returnType(), wrapperName(key, export.getKey()) + "("
                            + surfaceArgs + ")");
                }
                out.append("    __surf.write(").append(javaString(export.getKey()))
                    .append(", new JvmRuntime.FunctionValue(").append(invoker)
                    .append(", ")
                    .append(javaString(JvmSemanticEmitter.runtimeDescriptorText(
                        DescriptorService.describe(func))))
                    .append(", ")
                    .append(javaString(descriptorText(func))).append(", null));\n");
            }
        }
        out.append("  }\n\n");
    }

    /**
     * Emits the per-export wrapper of every declared function export: the
     * declared parameter cells in one-based order (the pinned E8010
     * {@code parameter {i} type mismatch} at the call origin), the
     * reflective invocation through the module binding, and the declared
     * return cell (the pinned E8010 {@code return value 1 type mismatch:
     * expected {expected}, got {actual}} / {@code got nothing}); a
     * declared async return runs the operation-shape check and returns the
     * host operation handle.
     */
    private void emitWrappers(StringBuilder out, HostModule module) {
        String key = key(module.modulePath());
        String raw = module.rawSpecifier();
        for (Map.Entry<String, Type> export
                : module.facts().exports().entrySet()) {
            if (!(export.getValue() instanceof Type.Func func)) {
                continue;
            }
            String returnType = func.isAsync() ? "java.lang.Object"
                : returnJavaType(func.returnType());
            out.append("  // Declared host export '").append(raw).append(".")
                .append(export.getKey()).append("  ")
                .append(descriptorText(func)).append("\n");
            out.append("  static ").append(returnType).append(' ')
                .append(wrapperName(key, export.getKey())).append('(');
            List<String> argNames = new ArrayList<>();
            for (int i = 0; i < func.paramTypes().size(); i++) {
                argNames.add("__a" + i);
                out.append("java.lang.Object __a").append(i).append(", ");
            }
            out.append("java.lang.String oFile, int oLine, int oCol) {\n");
            for (int i = 0; i < func.paramTypes().size(); i++) {
                out.append("    __a").append(i).append(" = __hostParamCheck(")
                    .append(i + 1).append(", ")
                    .append(javaString(descriptorText(func.paramTypes().get(i))))
                    .append(", __a").append(i)
                    .append(", oFile, oLine, oCol);\n");
                // The host-facing projection of the checked parameter (H7):
                // the declared carrier class at the crossing, never the
                // production value carrier.
                out.append("    __a").append(i)
                    .append(" = __hostProjectArg(")
                    .append(javaString(descriptorText(func.paramTypes().get(i))))
                    .append(", __a").append(i).append(");\n");
            }
            out.append("    java.lang.Object __r = __hostInvoke(")
                .append(methodField(key, export.getKey()))
                .append(", new java.lang.Object[]{ ")
                .append(String.join(", ", argNames)).append(" }, oFile, oLine, oCol);\n");
            emitReturnCell(out, func);
            out.append("  }\n\n");
        }
    }

    /** The Java return type of one declared sync return position. */
    private String returnJavaType(Type type) {
        if (type instanceof Type.Null) {
            return "void";
        }
        if (needsReturnProjection(type)) {
            return "java.lang.Object";
        }
        boolean nullable = type instanceof Type.Nullable;
        return carrierType(type, nullable);
    }

    /**
     * Whether one declared return position needs the host-to-DEAL
     * projection at the crossing (H7): a declared array or function
     * return is materialized back into the production value carriers
     * (a {@link JvmRuntime.Array} / the bridged production function
     * carrier) instead of the host-facing carrier class. Every other
     * position's carrier is the production value itself.
     */
    boolean needsReturnProjection(Type type) {
        Type inner = unwrapNullable(type);
        return inner instanceof Type.Array || inner instanceof Type.Func;
    }

    /** The declared return cell of one wrapper. */
    private void emitReturnCell(StringBuilder out, Type.Func func) {
        Type ret = func.returnType();
        String desc = descriptorText(ret);
        if (func.isAsync()) {
            out.append("    if (!(__r instanceof "
                    + "java.util.concurrent.CompletableFuture)) {\n");
            out.append("      throw JvmRuntime.fail(\"E8010\", \"host async"
                    + " function must return an async operation, got \" +"
                    + " __hostKind(__r), oFile + \":\" + oLine + \":\" + oCol,"
                    + " \"async operation\", __hostKind(__r));\n");
            out.append("    }\n");
            out.append("    return __r;\n");
            return;
        }
        if (ret instanceof Type.Null) {
            out.append("    __hostCheck(\"null\", __r, false, oFile, oLine,"
                + " oCol);\n");
            out.append("    return;\n");
            return;
        }
        boolean nullable = ret instanceof Type.Nullable;
        if (!nullable) {
            out.append("    if (__r == null) {\n");
            out.append("      throw JvmRuntime.fail(\"E8010\", \"return value 1"
                    + " type mismatch: expected ").append(desc)
                .append(", got nothing\", oFile + \":\" + oLine + \":\" + oCol,"
                    + " \"").append(desc)
                .append("\", \"nothing\");\n");
            out.append("    }\n");
        }
        String checked = "__hostCheck(" + javaString(desc)
            + ", __r, false, oFile, oLine, oCol)";
        if (needsReturnProjection(ret)) {
            // The host-to-DEAL crossing (H7): the declared array carrier is
            // materialized back into the production array carrier and a
            // declared function value into the bridged production carrier.
            out.append("    return __hostToDeal(").append(javaString(desc))
                .append(", ").append(checked).append(");\n");
            return;
        }
        String carrier = carrierType(ret, nullable);
        out.append("    return ").append(castExpression(carrier, checked))
            .append(";\n");
    }

    /** The Java cast of one checked return value onto its settled carrier. */
    private static String castExpression(String carrier, String expression) {
        return switch (carrier) {
            case "int" -> "((java.lang.Integer) " + expression + ").intValue()";
            case "double" -> "((java.lang.Double) " + expression + ").doubleValue()";
            case "boolean" -> "((java.lang.Boolean) " + expression + ").booleanValue()";
            default -> "(" + carrier + ") " + expression;
        };
    }

    // =========================================================================
    // Emission: the shared boundary-check seam
    // =========================================================================

    /**
     * Emits the boundary-check seam of the wrappers: the closed runtime
     * kind projection, the parameter and return cells with the pinned
     * E8010 texts, the descriptor-driven value check, the Lua-mirrored
     * inner reason, the load-time presence and defaults helpers, and the
     * reflective invocation.
     */
    private void emitSeams(StringBuilder out) {
        out.append("  // ---- The emitted host boundary-check seam (host-module-abi; "
            + "the pinned E8010 parameter/return projections) ----\n");
        out.append("  static java.lang.Object __hostParamCheck(int i, "
            + "java.lang.String desc, java.lang.Object v, java.lang.String"
            + " oFile, int oLine, int oCol) {\n");
        out.append("    try {\n");
        out.append("      return __hostCheckValue(desc, v, oFile, oLine, oCol);\n");
        out.append("    } catch (JvmRuntime.DealError __inner) {\n");
        out.append("      if (\"E8001\".equals(__inner.code) && __inner.msg.startsWith(\"expected instance of \")) { throw __inner; }\n");
        out.append("      throw JvmRuntime.fail(\"E8010\", \"parameter \" + i + \" type mismatch: \" + __hostInnerMessage(desc, v, __inner), oFile + \":\" + oLine + \":\" + oCol, desc, __hostKind(v));\n");
        out.append("    }\n");
        out.append("  }\n\n");
        out.append("  static java.lang.Object __hostCheck(java.lang.String desc, "
            + "java.lang.Object v, boolean completion, java.lang.String oFile,"
            + " int oLine, int oCol) {\n");
        out.append("    try {\n");
        out.append("      return __hostCheckValue(desc, v, oFile, oLine, oCol);\n");
        out.append("    } catch (JvmRuntime.DealError __inner) {\n");
        out.append("      if (\"E8001\".equals(__inner.code) && __inner.msg.startsWith(\"expected instance of \")) { throw __inner; }\n");
        out.append("      if (completion) { throw JvmRuntime.fail(\"E8001\", __hostInnerMessage(desc, v, __inner), oFile + \":\" + oLine + \":\" + oCol, desc, __hostKind(v)); }\n");
        out.append("      throw JvmRuntime.fail(\"E8010\", \"return value 1 type mismatch: \" + __hostInnerMessage(desc, v, __inner), oFile + \":\" + oLine + \":\" + oCol, desc, __hostKind(v));\n");
        out.append("    }\n");
        out.append("  }\n\n");
        out.append("  static JvmRuntime.DealError __hostFail(java.lang.String reason, "
            + "java.lang.String desc, java.lang.Object v, java.lang.String oFile,"
            + " int oLine, int oCol) {\n");
        out.append("    return JvmRuntime.fail(\"E8001\", reason, oFile + \":\" + oLine + \":\" + oCol, desc, __hostKind(v));\n");
        out.append("  }\n\n");
        out.append("  static java.lang.String __hostKind(java.lang.Object v) {\n");
        out.append("    if (v == null) return \"null\";\n");
        out.append("    if (v instanceof java.lang.String) return \"string\";\n");
        out.append("    if (v instanceof java.lang.Long || v instanceof java.lang.Integer || v instanceof java.lang.Double) return \"number\";\n");
        out.append("    if (v instanceof java.lang.Boolean) return \"boolean\";\n");
        out.append("    if (v instanceof $DealRt.Bytes) return \"bytes\";\n");
        out.append("    if (v instanceof JvmRuntime.FunctionValue || v instanceof $DealRt.FnValue) return \"table\";\n");
        out.append("    if (v instanceof JvmRuntime.Table || v instanceof JvmRuntime.Array || v instanceof JvmRuntime.ClassInstance) return \"table\";\n");
        out.append("    for (java.lang.Class<?> __k : v.getClass().getInterfaces()) { int __n = 0; for (java.lang.reflect.Method __m : __k.getMethods()) { if (java.lang.reflect.Modifier.isAbstract(__m.getModifiers())) __n++; } if (__n == 1) return \"function\"; }\n");
        out.append("    return \"table\";\n");
        out.append("  }\n\n");
        out.append("  static java.lang.String __hostStringReason(java.lang.String s) {\n");
        out.append("    boolean malformed = false;\n");
        out.append("    for (int i = 0; i < s.length(); i++) {\n");
        out.append("      char c = s.charAt(i);\n");
        out.append("      if (java.lang.Character.isHighSurrogate(c) && i + 1 < s.length() && java.lang.Character.isLowSurrogate(s.charAt(i + 1))) { i++; }\n");
        out.append("      else if (java.lang.Character.isHighSurrogate(c) || java.lang.Character.isLowSurrogate(c)) { malformed = true; break; }\n");
        out.append("    }\n");
        out.append("    if (!malformed) return null;\n");
        out.append("    return s.length() == 1 ? \"expected string, got UTF-16 surrogate code point\" : \"expected string, got invalid UTF-8 encoding\";\n");
        out.append("  }\n\n");
        out.append("  static java.lang.String __hostInnerMessage(java.lang.String d, "
            + "java.lang.Object v, JvmRuntime.DealError inner) {\n");
        out.append("    if (d.startsWith(\"?\")) return __hostInnerMessage(d.substring(1), v, inner);\n");
        out.append("    if (inner != null && (\"E8010\".equals(inner.code) || \"E8003\".equals(inner.code))) return inner.msg;\n");
        out.append("    if (d.startsWith(\"[\")) return \"expected array\";\n");
        out.append("    if (d.startsWith(\"(\") || d.startsWith(\"async(\")) return \"expected function\";\n");
        out.append("    if (d.equals(\"null\")) return \"expected null\";\n");
        out.append("    if (d.equals(\"int\")) {\n");
        out.append("      if (v instanceof java.lang.Double __dd) { if (__dd.isNaN()) return \"expected int, got NaN\"; if (__dd.isInfinite()) return \"expected int, got infinity\"; if (__dd % 1.0 != 0.0) return \"expected int, got non-integer number\"; }\n");
        out.append("      return \"expected int\";\n");
        out.append("    }\n");
        out.append("    if (d.equals(\"number\")) return \"expected number\";\n");
        out.append("    if (d.equals(\"boolean\")) return \"expected boolean\";\n");
        out.append("    if (d.equals(\"string\")) {\n");
        out.append("      if (v instanceof java.lang.String __s) { java.lang.String __r = __hostStringReason(__s); if (__r != null) return __r; }\n");
        out.append("      return \"expected string\";\n");
        out.append("    }\n");
        out.append("    if (d.equals(\"bytes\")) return \"expected bytes\";\n");
        out.append("    if (d.equals(\"table\")) return \"expected table\";\n");
        out.append("    if (d.startsWith(\"@\")) return \"expected class instance\";\n");
        out.append("    return \"expected \" + d;\n");
        out.append("  }\n\n");
        emitCheckValue(out);
        out.append("  static java.lang.Object __hostDefault(java.util.Map<java.lang.String, java.lang.Object> defaults, java.lang.String name, java.lang.String cls, java.lang.String oFile, int oLine, int oCol) {\n");
        out.append("    java.lang.Object v = defaults.get(name);\n");
        out.append("    if (v == null) throw JvmRuntime.fail(\"E8001\", \"missing default for field '\" + name + \"' of class '\" + cls + \"'\", oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    return v;\n");
        out.append("  }\n\n");
        out.append("  static java.lang.reflect.Method __hostMethod(java.lang.Class<?> h,"
            + " java.lang.String module, java.lang.String name, java.lang.String"
            + " desc, java.lang.Class<?>[] params, java.lang.String oFile, int"
            + " oLine, int oCol) {\n");
        out.append("    try {\n");
        out.append("      return h.getDeclaredMethod(name, params);\n");
        out.append("    } catch (java.lang.NoSuchMethodException __e) {\n");
        out.append("      throw JvmRuntime.fail(\"E8011\", \"missing host export '\" + name + \"' in module '\" + module + \"'\", oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    }\n");
        out.append("  }\n\n");
        out.append("  static java.util.Map<java.lang.String, java.lang.Object>"
            + " __hostDefaults(java.lang.Class<?> h, java.lang.String module,"
            + " java.lang.String name, java.lang.String oFile, int oLine, int"
            + " oCol) {\n");
        out.append("    try {\n");
        out.append("      java.lang.reflect.Field f = h.getDeclaredField(name + \"_defaults\");\n");
        out.append("      f.setAccessible(true);\n");
        out.append("      java.lang.Object v = f.get(null);\n");
        out.append("      if (v instanceof java.util.Map m) { return m; }\n");
        out.append("      throw JvmRuntime.fail(\"E8011\", \"host class '\" + name + \"' in module '\" + module + \"' has a non-map defaults value\", oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    } catch (java.lang.NoSuchFieldException __e) {\n");
        out.append("      throw JvmRuntime.fail(\"E8011\", \"host class '\" + name + \"' in module '\" + module + \"' is missing its defaults field (\" + name + \"_defaults)\", oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    } catch (java.lang.IllegalAccessException __e) {\n");
        out.append("      throw JvmRuntime.fail(\"E8011\", \"host class '\" + name + \"' in module '\" + module + \"' defaults are inaccessible\", oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    }\n");
        out.append("  }\n\n");
        out.append("  static java.lang.Object __hostInvoke(java.lang.reflect.Method m,"
            + " java.lang.Object[] args, java.lang.String oFile, int oLine, int"
            + " oCol) {\n");
        out.append("    try {\n");
        out.append("      return m.invoke(null, args);\n");
        out.append("    } catch (java.lang.reflect.InvocationTargetException __e) {\n");
        out.append("      java.lang.Throwable __c = __e.getCause();\n");
        out.append("      if (__c instanceof RuntimeException __rr) { throw __rr; }\n");
        out.append("      if (__c instanceof Error __er) { throw __er; }\n");
        out.append("      throw JvmRuntime.fail(\"E8010\", \"host function raised: \" + __c, oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    } catch (java.lang.IllegalAccessException | java.lang.IllegalArgumentException __e) {\n");
        out.append("      throw JvmRuntime.fail(\"E8010\", \"host function invocation failed: \" + __e, oFile + \":\" + oLine + \":\" + oCol, null, null);\n");
        out.append("    }\n");
        out.append("  }\n\n");
    }

    // =========================================================================
    // Emission: the host-boundary crossing projections (H7)
    // =========================================================================

    /**
     * Emits the host-boundary crossing projections (ISSUE-0651;
     * {@code host-module-load-and-host-call-realization} H7 and the
     * host-boundary carrier projection contract): the DEAL-to-host
     * parameter projection (the declared host-facing carrier: the
     * per-signature function bridge and the declared element-shape array
     * carrier), the host-to-DEAL declared-return projection (the
     * production function carrier and the materialized
     * {@link JvmRuntime.Array}), and the normal-return copy-back of a
     * declared array parameter's host element writes. The declared
     * descriptor already fixed the carrier class, so every projection is
     * a per-crossing materialization, never a runtime path selection. A
     * nullable declared position's descriptor text carries the {@code ?}
     * prefix while the declared element-shape carrier keys are the
     * un-prefixed array descriptors, so the array dispatch and the
     * copy-back match the stripped descriptor text.
     */
    private void emitCrossings(StringBuilder out) {
        out.append("  // ---- The host-boundary crossing projections (ISSUE-0651; H7) ----\n");
        out.append("  static java.lang.Object __hostProjectArg(java.lang.String d, java.lang.Object v) {\n");
        out.append("    if (v == null) return null;\n");
        out.append("    java.lang.String inner = d.startsWith(\"?\") ? d.substring(1) : d;\n");
        out.append("    if (inner.startsWith(\"(\") || inner.startsWith(\"async(\")) return __hostFnCarrier(inner, v);\n");
        out.append("    if (inner.startsWith(\"[\")) return __hostArrayFromDeal(inner, v);\n");
        out.append("    if (inner.equals(\"int\")) return java.lang.Integer.valueOf(((java.lang.Number) v).intValue());\n");
        out.append("    if (inner.equals(\"number\")) return java.lang.Double.valueOf(((java.lang.Number) v).doubleValue());\n");
        out.append("    return v;\n");
        out.append("  }\n\n");
        out.append("  static java.lang.Object __hostToDeal(java.lang.String d, java.lang.Object v) {\n");
        out.append("    if (v == null) return null;\n");
        out.append("    java.lang.String inner = d.startsWith(\"?\") ? d.substring(1) : d;\n");
        out.append("    if (inner.startsWith(\"(\") || inner.startsWith(\"async(\")) return __hostFnToDeal(inner, v);\n");
        out.append("    if (inner.startsWith(\"[\")) return __hostArrayToDeal(inner, v);\n");
        out.append("    return v;\n");
        out.append("  }\n\n");
        emitFunctionCrossings(out);
        emitArrayCrossings(out);
    }

    /**
     * The function-position projections: DEAL-to-host materializes the
     * declared per-signature bridge over the production carrier (the
     * bridge runs the carrier and applies the declared return cell),
     * host-to-DEAL republishes the bridged production carrier — the
     * identical value for a value that crossed out and back — and adapts
     * a foreign wrapper whose descriptor text is byte-equal. A raw host
     * function value is never adapted.
     */
    private void emitFunctionCrossings(StringBuilder out) {
        out.append("  static java.lang.Object __hostFnCarrier(java.lang.String d, java.lang.Object v) {\n");
        out.append("    if (v == null) return null;\n");
        out.append("    if (v instanceof JvmRuntime.FunctionValue __fv) {\n");
        for (Map.Entry<String, Type.Func> shape : shapes.entrySet()) {
            out.append("      if (d.equals(").append(javaString(descriptorText(shape.getValue())))
                .append(")) return new $DealRt.__Bridge$").append(shape.getKey())
                .append("(__fv);\n");
        }
        out.append("    }\n");
        out.append("    return v;\n");
        out.append("  }\n\n");
        out.append("  static java.lang.Object __hostFnToDeal(java.lang.String d, java.lang.Object v) {\n");
        out.append("    if (v == null) return null;\n");
        for (Map.Entry<String, Type.Func> shape : shapes.entrySet()) {
            String desc = javaString(descriptorText(shape.getValue()));
            String shapeId = shape.getKey();
            out.append("    if (d.equals(").append(desc).append(")) {\n");
            out.append("      if (v instanceof $DealRt.__Bridge$").append(shapeId)
                .append(" __b) return __b.$carrier;\n");
            out.append("      if (v instanceof $DealRt.").append(shapeId)
                .append(" __w) return __hostForeignFn$").append(shapeId)
                .append("(__w);\n");
            out.append("      return v;\n");
            out.append("    }\n");
        }
        out.append("    return v;\n");
        out.append("  }\n\n");
        for (Map.Entry<String, Type.Func> shape : shapes.entrySet()) {
            emitForeignFnAdapter(out, shape.getKey(), shape.getValue());
        }
    }

    /** One foreign {@code $DealRt.FnValue} adapter per declared signature. */
    private void emitForeignFnAdapter(StringBuilder out, String shapeId, Type.Func func) {
        StringBuilder params = new StringBuilder();
        for (int i = 0; i < func.paramTypes().size(); i++) {
            if (i > 0) {
                params.append(", ");
            }
            params.append(paramClassLiteral(func.paramTypes().get(i)));
        }
        out.append("  static JvmRuntime.FunctionValue __hostForeignFn$").append(shapeId)
            .append("($DealRt.").append(shapeId).append(" fw) {\n");
        out.append("    java.lang.reflect.Method m;\n");
        out.append("    try {\n");
        out.append("      m = $DealRt.").append(shapeId)
            .append(".class.getDeclaredMethod(\"invoke\"");
        for (Type param : func.paramTypes()) {
            out.append(", ").append(paramClassLiteral(param));
        }
        out.append(");\n");
        out.append("      m.setAccessible(true);\n");
        out.append("    } catch (java.lang.Exception __e) {\n");
        out.append("      throw JvmRuntime.fail(\"E8010\", \"host function value "
            + "adaptation failed: \" + __e, \"-\", null, null);\n");
        out.append("    }\n");
        out.append("    return new JvmRuntime.FunctionValue(__args -> {\n");
        // The production arguments project onto the host-facing declared
        // carriers before the reflective invocation (H7's argument
        // projection, the same one the per-export wrapper's parameters
        // run), and the host-facing result returns onto the production
        // value carrier (an int result is the production Long).
        StringBuilder projected = new StringBuilder();
        for (int i = 0; i < func.paramTypes().size(); i++) {
            if (projected.length() > 0) {
                projected.append(", ");
            }
            projected.append("__hostProjectArg(")
                .append(javaString(descriptorText(func.paramTypes().get(i))))
                .append(", __args[").append(i).append("])");
        }
        String invocation = projected.length() == 0
            ? "m.invoke(fw)" : "m.invoke(fw, " + projected + ")";
        out.append("      java.lang.Object __hc;\n");
        out.append("      try { __hc = ").append(invocation).append("; }\n");
        out.append("      catch (java.lang.reflect.InvocationTargetException __e) {\n");
        out.append("        java.lang.Throwable __c = __e.getCause();\n");
        out.append("        if (__c instanceof RuntimeException __rr) { throw __rr; }\n");
        out.append("        if (__c instanceof Error __er) { throw __er; }\n");
        out.append("        throw JvmRuntime.fail(\"E8010\", \"host function value "
            + "raised: \" + __c, \"-\", null, null);\n");
        out.append("      }\n");
        out.append("      catch (java.lang.IllegalAccessException |"
            + " java.lang.IllegalArgumentException __e) {\n");
        out.append("        throw JvmRuntime.fail(\"E8010\", \"host function value "
            + "invocation failed: \" + __e, \"-\", null, null);\n");
        out.append("      }\n");
        out.append("      return ")
            .append(JvmSemanticEmitter.checkedResultOf(func.returnType(), "__hc"))
            .append(";\n");
        out.append("    }, ").append(javaString(JvmSemanticEmitter.runtimeDescriptorText(
            DescriptorService.describe(func)))).append(", ")
            .append(javaString(descriptorText(func))).append(", null);\n");
        out.append("  }\n\n");
    }

    /**
     * The declared element-shape array crossings: DEAL-to-host materializes
     * the declared carrier from the production {@link JvmRuntime.Array}
     * slots (after the declared element cell admitted them), host-to-DEAL
     * materializes the production array from the carrier, and a
     * normal-return copy-back mirrors the host's element writes into the
     * production array (a failed call copies nothing back). Every matcher
     * keys on the un-prefixed array descriptor, so a nullable declared
     * array position ({@code ?[T]}) crosses like its {@code [T]} form.
     */
    private void emitArrayCrossings(StringBuilder out) {
        // DEAL -> host: the declared carrier materialized per crossing.
        out.append("  static java.lang.Object __hostArrayFromDeal(java.lang.String d, java.lang.Object v) {\n");
        out.append("    if (v == null) return null;\n");
        out.append("    if (!(v instanceof JvmRuntime.Array __a)) return v;\n");
        for (Map.Entry<String, Type> entry : arrayElements.entrySet()) {
            String desc = entry.getKey();
            Type element = entry.getValue();
            String carrier = arrayCarrier(element);
            String component = elementComponent(element);
            out.append("    if (d.equals(").append(javaString(desc)).append(")) {\n");
            out.append("      ").append(component).append("[] __d = new ")
                .append(component).append("[").append("__a.length];\n");
            out.append("      for (int __i = 0; __i < __a.length; __i++) { __d[__i] = ")
                .append(elementExtract(element,
                    "__i < __a.elements.size() ? __a.elements.get(__i) : null"))
                .append("; }\n");
            out.append("      return new $DealRt.").append(carrier).append("(__d);\n");
            out.append("    }\n");
        }
        out.append("    return v;\n");
        out.append("  }\n\n");
        // host -> DEAL: the production array materialized from the carrier.
        out.append("  static JvmRuntime.Array __hostArrayToDeal(java.lang.String d, java.lang.Object v) {\n");
        out.append("    if (v == null) return null;\n");
        out.append("    if (v instanceof JvmRuntime.Array __a) return __a;\n");
        for (Map.Entry<String, Type> entry : arrayElements.entrySet()) {
            String desc = entry.getKey();
            Type element = entry.getValue();
            String carrier = arrayCarrier(element);
            out.append("    if (d.equals(").append(javaString(desc))
                .append(") && v instanceof $DealRt.").append(carrier).append(" __c) {\n");
            out.append("      JvmRuntime.Array __r = new JvmRuntime.Array(__c.data.length);\n");
            out.append("      for (int __i = 0; __i < __c.data.length; __i++) { __r.elements.add(")
                .append(elementStore(element, "__c.data[__i]"))
                .append("); }\n");
            out.append("      return __r;\n");
            out.append("    }\n");
        }
        out.append("    throw JvmRuntime.fail(\"E8010\", \"host array value has no "
            + "declared carrier for \" + d, \"-\", d, null);\n");
        out.append("  }\n\n");
        // The normal-return copy-back of a declared array parameter.
        out.append("  static void __hostArrayCopyBack(java.lang.String d, "
            + "java.lang.Object v, JvmRuntime.Array t) {\n");
        out.append("    if (v == null || t == null) return;\n");
        out.append("    if (v instanceof JvmRuntime.Array) return;\n");
        out.append("    java.lang.String __key = d.startsWith(\"?\") ? d.substring(1) : d;\n");
        for (Map.Entry<String, Type> entry : arrayElements.entrySet()) {
            String desc = entry.getKey();
            Type element = entry.getValue();
            String carrier = arrayCarrier(element);
            out.append("    if (__key.equals(").append(javaString(desc))
                .append(") && v instanceof $DealRt.").append(carrier).append(" __c) {\n");
            out.append("      for (int __i = 0; __i < __c.data.length && __i < t.length; __i++) {\n");
            out.append("        while (t.elements.size() <= __i) t.elements.add(null);\n");
            out.append("        t.elements.set(__i, ")
                .append(elementStore(element, "__c.data[__i]")).append(");\n");
            out.append("      }\n");
            out.append("      return;\n");
            out.append("    }\n");
        }
        out.append("  }\n\n");
    }

    /** The Java component type of one declared array element. */
    private String elementComponent(Type element) {
        if (element instanceof Type.Nullable nullable) {
            return boxedCarrier(nullable.inner());
        }
        return switch (element) {
            case Type.Int ignored -> "int";
            case Type.Number ignored -> "double";
            case Type.Boolean ignored -> "boolean";
            case Type.String ignored -> "java.lang.String";
            case Type.Bytes ignored -> "$DealRt.Bytes";
            case Type.Class cls -> "$DealRt." + recordSimpleNameOf(cls);
            default -> "java.lang.Object";
        };
    }

    /** The production slot → declared carrier component extraction. */
    private String elementExtract(Type element, String expression) {
        if (element instanceof Type.Nullable nullable) {
            Type inner = nullable.inner();
            return "(" + expression + " == null ? null : "
                + boxedOf(inner, "((java.lang.Number) " + expression + ")", expression)
                + ")";
        }
        return switch (element) {
            case Type.Int ignored -> "((java.lang.Number) (" + expression + ")).intValue()";
            case Type.Number ignored -> "((java.lang.Number) (" + expression + ")).doubleValue()";
            case Type.Boolean ignored -> "((java.lang.Boolean) (" + expression + ")).booleanValue()";
            case Type.String ignored -> "(java.lang.String) (" + expression + ")";
            case Type.Bytes ignored -> "($DealRt.Bytes) (" + expression + ")";
            case Type.Class cls -> "($DealRt." + recordSimpleNameOf(cls) + ") ("
                + expression + ")";
            default -> "(" + expression + ")";
        };
    }

    /**
     * The declared carrier component → production slot store (the boxed
     * value model: an {@code int} element stays a {@code Long}, a
     * {@code number} a {@code Double}, a nullable element keeps null).
     */
    private String elementStore(Type element, String expression) {
        Type inner = element instanceof Type.Nullable nullable ? nullable.inner() : element;
        boolean nullable = element instanceof Type.Nullable;
        String boxed = switch (inner) {
            case Type.Int ignored -> "java.lang.Long.valueOf(((java.lang.Number) ("
                + expression + ")).longValue())";
            case Type.Number ignored -> "java.lang.Double.valueOf(((java.lang.Number) ("
                + expression + ")).doubleValue())";
            case Type.Boolean ignored -> "java.lang.Boolean.valueOf(((java.lang.Boolean) ("
                + expression + ")).booleanValue())";
            default -> "(" + expression + ")";
        };
        if (nullable) {
            return "(" + expression + " == null ? null : " + boxed + ")";
        }
        return boxed;
    }

    /** The boxed expression of one primitive inner carrier. */
    private String boxedOf(Type inner, String numberExpression, String expression) {
        return switch (inner) {
            case Type.Int ignored -> "java.lang.Integer.valueOf("
                + numberExpression + ".intValue())";
            case Type.Number ignored -> "java.lang.Double.valueOf("
                + numberExpression + ".doubleValue())";
            case Type.Boolean ignored -> "java.lang.Boolean.valueOf((java.lang.Boolean) "
                + expression + ")";
            default -> expression;
        };
    }

    /** The descriptor-driven value check of the parameter/return cells. */
    private void emitCheckValue(StringBuilder out) {
        out.append("  static java.lang.Object __hostCheckValue(java.lang.String d,"
            + " java.lang.Object v, java.lang.String oFile, int oLine, int oCol) {\n");
        out.append("    if (d.startsWith(\"?\")) {\n");
        out.append("      if (v == null) return null;\n");
        out.append("      return __hostCheckValue(d.substring(1), v, oFile, oLine, oCol);\n");
        out.append("    }\n");
        out.append("    if (d.equals(\"null\")) { if (v == null) return null; throw __hostFail(\"expected null\", d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.equals(\"boolean\")) { if (v instanceof java.lang.Boolean) return v; throw __hostFail(\"expected boolean\", d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.equals(\"int\")) {\n");
        out.append("      if (v instanceof java.lang.Integer) return v;\n");
        out.append("      if (v instanceof java.lang.Long) return v;\n");
        out.append("      if (v instanceof java.lang.Double __dd) {\n");
        out.append("        if (__dd.isNaN()) throw __hostFail(\"expected int, got NaN\", d, v, oFile, oLine, oCol);\n");
        out.append("        if (__dd.isInfinite()) throw __hostFail(\"expected int, got infinity\", d, v, oFile, oLine, oCol);\n");
        out.append("        if (__dd % 1.0 != 0.0) throw __hostFail(\"expected int, got non-integer number\", d, v, oFile, oLine, oCol);\n");
        out.append("        if (__dd < -2147483648.0 || __dd > 2147483647.0) { throw JvmRuntime.fail(\"E8004\", \"int out of safe range\", oFile + \":\" + oLine + \":\" + oCol, \"int\", \"number\"); }\n");
        out.append("        return v;\n");
        out.append("      }\n");
        out.append("      throw __hostFail(\"expected int\", d, v, oFile, oLine, oCol);\n");
        out.append("    }\n");
        out.append("    if (d.equals(\"number\")) { if (v instanceof java.lang.Double || v instanceof java.lang.Long) return v; throw __hostFail(\"expected number\", d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.equals(\"string\")) { if (v instanceof java.lang.String __s) { java.lang.String __r = __hostStringReason(__s); if (__r != null) throw __hostFail(__r, d, v, oFile, oLine, oCol); return v; } throw __hostFail(\"expected string\", d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.equals(\"bytes\")) { if (v instanceof $DealRt.Bytes) return v; throw __hostFail(\"expected bytes\", d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.equals(\"table\")) { if (v instanceof JvmRuntime.Table) return v; throw __hostFail(\"expected table\", d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.startsWith(\"[\")) { return __hostCheckArray(d, v, oFile, oLine, oCol); }\n");
        out.append("    if (d.startsWith(\"(\") || d.startsWith(\"async(\")) {\n");
        out.append("      java.lang.String __carried = null;\n");
        out.append("      if (v instanceof $DealRt.FnValue __f) { __carried = __f.descriptor(); }\n");
        out.append("      else if (v instanceof JvmRuntime.FunctionValue __fv) { __carried = __fv.spec != null ? __fv.spec : __fv.signature; }\n");
        out.append("      if (__carried != null && __carried.equals(d)) return v;\n");
        out.append("      if (__carried != null) { throw JvmRuntime.fail(\"E8010\", \"function signature mismatch: expected \" + d + \", got \" + __carried, oFile + \":\" + oLine + \":\" + oCol, d, __carried); }\n");
        out.append("      throw __hostFail(\"expected function\", d, v, oFile, oLine, oCol);\n");
        out.append("    }\n");
        out.append("    if (d.startsWith(\"@\")) { return __hostCheckIdentity(d, v, oFile, oLine, oCol); }\n");
        out.append("    throw __hostFail(\"expected \" + d, d, v, oFile, oLine, oCol);\n");
        out.append("  }\n\n");
        out.append("  static java.lang.Object __hostCheckArray(java.lang.String d,"
            + " java.lang.Object v, java.lang.String oFile, int oLine, int oCol) {\n");
        out.append("    java.lang.String __inner = d.substring(1, d.length() - 1);\n");
        out.append("    if (v instanceof JvmRuntime.Array __arr) {\n");
        out.append("      for (int __i = 0; __i < __arr.elements.size(); __i++) {\n");
        out.append("        java.lang.Object __e = __arr.elements.get(__i);\n");
        out.append("        try { __hostCheckValue(__inner, __e, oFile, oLine, oCol); }\n");
        out.append("        catch (JvmRuntime.DealError __leaf) { throw JvmRuntime.fail(\"E8003\", \"array element \" + (__i + 1) + \" type mismatch\", oFile + \":\" + oLine + \":\" + oCol, __inner, __hostKind(__e)); }\n");
        out.append("      }\n");
        out.append("      return v;\n");
        out.append("    }\n");
        for (Map.Entry<String, String> carrier : declaredArrayCarriers().entrySet()) {
            out.append("    if (d.equals(").append(javaString(carrier.getKey()))
                .append(") && v instanceof $DealRt.").append(carrier.getValue())
                .append(") { return v; }\n");
        }
        out.append("    throw __hostFail(\"expected array\", d, v, oFile, oLine, oCol);\n");
        out.append("  }\n\n");
        out.append("  static java.lang.Object __hostCheckIdentity(java.lang.String d,"
            + " java.lang.Object v, java.lang.String oFile, int oLine, int oCol) {\n");
        for (RecordInfo record : records.values()) {
            out.append("    if (v instanceof $DealRt.").append(record.simpleName())
                .append(" __rec && d.equals(__rec.$identity)) { return v; }\n");
        }
        out.append("    if (v instanceof JvmRuntime.ClassInstance __ci && d.equals(__ci.classIdText())) { return v; }\n");
        out.append("    throw JvmRuntime.fail(\"E8001\", \"expected instance of \" + d + \", got \" + __hostKind(v), oFile + \":\" + oLine + \":\" + oCol, d, null);\n");
        out.append("  }\n\n");
    }

    /** The declared array descriptor → carrier-class pairs collected from the module positions. */
    private Map<String, String> declaredArrayCarriers() {
        Map<String, String> carriers = new LinkedHashMap<>();
        for (HostModule module : modules) {
            for (Type export : module.facts().exports().values()) {
                collectArrayCarriers(export, carriers);
            }
            for (HostDeclarationSurface.DeclaredClass declared
                    : module.facts().classes().values()) {
                for (HostDeclarationSurface.DeclaredField field : declared.fields()) {
                    collectArrayCarriers(field.type(), carriers);
                }
            }
        }
        return carriers;
    }

    private void collectArrayCarriers(Type type, Map<String, String> carriers) {
        switch (type) {
            case Type.Nullable nullable -> collectArrayCarriers(nullable.inner(), carriers);
            case Type.Func func -> {
                for (Type param : func.paramTypes()) {
                    collectArrayCarriers(param, carriers);
                }
                collectArrayCarriers(func.returnType(), carriers);
            }
            case Type.Array array -> {
                carriers.putIfAbsent(descriptorText(array),
                    arrayCarrier(array.element()));
                collectArrayCarriers(array.element(), carriers);
            }
            default -> {
            }
        }
    }

    // =========================================================================
    // Emission: the synthesized host-record and host-carrier scope
    // =========================================================================

    /**
     * Emits the one top-level {@code $DealRt} scope: the {@code FnValue}
     * interface, the declared element-shape array carriers, {@code
     * Bytes}, the {@code $Host$} records with their per-class array
     * wrappers, and one per-signature function wrapper class per declared
     * function position.
     */
    void emitScope(StringBuilder out) {
        out.append("\n// The synthesized host-record and host-carrier scope of the"
            + " production artifact\n// (ISSUE-0650; host-module-load-and-host-call-"
            + "realization H2 item 3 and H7's carrier set):\n// the deployed host"
            + " implementations compile against these classes unchanged.\n");
        out.append("class $DealRt {\n");
        out.append("  interface FnValue { java.lang.String descriptor(); }\n");
        out.append("  static final class Bytes { byte[] data; Bytes(byte[] data) { this.data = data; } }\n");
        out.append("  static final class __IntArray { int[] data; __IntArray(int[] data) { this.data = data; } }\n");
        out.append("  static final class __NumberArray { double[] data; __NumberArray(double[] data) { this.data = data; } }\n");
        out.append("  static final class __StringArray { java.lang.String[] data; __StringArray(java.lang.String[] data) { this.data = data; } }\n");
        out.append("  static final class __BooleanArray { boolean[] data; __BooleanArray(boolean[] data) { this.data = data; } }\n");
        out.append("  static final class __IntOrNullArray { java.lang.Integer[] data; __IntOrNullArray(java.lang.Integer[] data) { this.data = data; } }\n");
        out.append("  static final class __NumberOrNullArray { java.lang.Double[] data; __NumberOrNullArray(java.lang.Double[] data) { this.data = data; } }\n");
        out.append("  static final class __StringOrNullArray { java.lang.String[] data; __StringOrNullArray(java.lang.String[] data) { this.data = data; } }\n");
        out.append("  static final class __BooleanOrNullArray { java.lang.Boolean[] data; __BooleanOrNullArray(java.lang.Boolean[] data) { this.data = data; } }\n");
        out.append("  static final class __BytesArray { Bytes[] data; __BytesArray(Bytes[] data) { this.data = data; } }\n");
        out.append("  static final class __BytesOrNullArray { Bytes[] data; __BytesOrNullArray(Bytes[] data) { this.data = data; } }\n");
        out.append("  static class __RefArray { java.lang.Object[] data; __RefArray(java.lang.Object[] data) { this.data = data; } }\n");
        for (RecordInfo record : records.values()) {
            emitRecord(out, record);
            out.append("  static final class ").append(record.arrayWrapper())
                .append(" extends __RefArray { ")
                .append(record.arrayWrapper())
                .append("(java.lang.Object[] data) { super(data); } }\n");
        }
        for (Map.Entry<String, Type.Func> shape : shapes.entrySet()) {
            emitShape(out, shape.getKey(), shape.getValue());
        }
        out.append("}\n");
    }

    /** One synthesized host-class record with declared fields in declaration order. */
    private void emitRecord(StringBuilder out, RecordInfo record) {
        out.append("  // Synthesized host-class record ").append(record.identityText())
            .append(" (the declared fields in declaration order; the\n")
            .append("  // JvmRuntime.ClassInstance surface is the production"
                + " field-op entry — ISSUE-0624/K10).\n");
        out.append("  static final class ").append(record.simpleName())
            .append(" implements JvmRuntime.ClassInstance {\n");
        out.append("    final java.lang.String $identity;\n");
        for (FieldInfo field : record.fields()) {
            out.append("    ").append(field.storageType()).append(' ')
                .append(field.javaName()).append(";\n");
            if (field.optional()) {
                out.append("    boolean ").append(field.javaName())
                    .append("$present;\n");
            }
        }
        StringBuilder params = new StringBuilder();
        for (int i = 0; i < record.fields().size(); i++) {
            FieldInfo field = record.fields().get(i);
            if (i > 0) {
                params.append(", ");
            }
            params.append(field.storageType()).append(' ').append(field.javaName());
            if (field.optional()) {
                params.append(", boolean ").append(field.javaName())
                    .append("$present");
            }
        }
        out.append("    ").append(record.simpleName()).append('(')
            .append(params).append(") {\n");
        out.append("      this.$identity = ")
            .append(javaString(record.identityText())).append(";\n");
        for (FieldInfo field : record.fields()) {
            out.append("      this.").append(field.javaName()).append(" = ")
                .append(field.javaName()).append(";\n");
            if (field.optional()) {
                out.append("      this.").append(field.javaName())
                    .append("$present = ").append(field.javaName())
                    .append("$present;\n");
            }
        }
        out.append("    }\n");
        for (FieldInfo field : record.fields()) {
            if (field.optional()) {
                out.append("    ").append(field.storageType()).append(" $optSet$")
                    .append(field.javaName()).append('(')
                    .append(field.storageType()).append(" v) { this.")
                    .append(field.javaName()).append(" = v; this.")
                    .append(field.javaName()).append("$present = true; return v; }\n");
            }
        }
        emitRecordClassInstance(out, record);
        out.append("  }\n");
    }

    /**
     * The {@link JvmRuntime.ClassInstance} surface of one synthesized
     * record (ISSUE-0624; K10): the closed field-op entry the production
     * arms already speak — {@code FIELD_READ} reads the presence-aware
     * field with the production value carriers projected back (an absent
     * field is {@link JvmRuntime#MISSING}), {@code FIELD_WRITE} stores the
     * boundary-checked production value, {@code FIELD_DELETE} clears an
     * optional field, and {@code HAS_FIELD} resolves presence — with the
     * declared field's host-facing storage as the record's own state the
     * deployed host implementation reads directly. A required-field delete
     * is unreachable from the checker (E4004) and stays a fail-closed
     * producer defect.
     */
    private void emitRecordClassInstance(StringBuilder out, RecordInfo record) {
        out.append("    @Override public java.lang.String classIdText() { return $identity; }\n");
        out.append("    @Override public boolean isPresent(java.lang.String key) {\n");
        for (FieldInfo field : record.fields()) {
            out.append("      if (").append(javaString(field.name()))
                .append(".equals(key)) return ")
                .append(field.optional() ? field.javaName() + "$present" : "true")
                .append(";\n");
        }
        out.append("      return false;\n");
        out.append("    }\n");
        out.append("    @Override public java.lang.Object read(java.lang.String key) {\n");
        for (FieldInfo field : record.fields()) {
            out.append("      if (").append(javaString(field.name()))
                .append(".equals(key)) ");
            if (field.optional()) {
                out.append("return ").append(field.javaName()).append("$present ? ")
                    .append(readProjection(field, field.javaName()))
                    .append(" : JvmRuntime.MISSING;\n");
            } else {
                out.append("return ")
                    .append(readProjection(field, field.javaName())).append(";\n");
            }
        }
        out.append("      return JvmRuntime.MISSING;\n");
        out.append("    }\n");
        out.append("    @Override public void write(java.lang.String key, "
            + "java.lang.Object value) {\n");
        for (FieldInfo field : record.fields()) {
            out.append("      if (").append(javaString(field.name()))
                .append(".equals(key)) { ").append(field.javaName()).append(" = ")
                .append(writeProjection(field, "value")).append(";");
            if (field.optional()) {
                out.append(" ").append(field.javaName()).append("$present = true;");
            }
            out.append(" return; }\n");
        }
        out.append("      throw new java.lang.IllegalStateException("
            + "\"host class field write to undeclared field '\" + key + \"' (producer defect)\");\n");
        out.append("    }\n");
        out.append("    @Override public void delete(java.lang.String key) {\n");
        for (FieldInfo field : record.fields()) {
            out.append("      if (").append(javaString(field.name()))
                .append(".equals(key)) ");
            if (field.optional()) {
                out.append("{ ").append(field.javaName()).append(" = null; ")
                    .append(field.javaName()).append("$present = false; return; }\n");
            } else {
                out.append("throw new java.lang.IllegalStateException(\"delete of"
                    + " required host class field '" + field.name()
                    + "' (the checker's E4004 rejects the shape — producer defect)\");\n");
            }
        }
        out.append("      throw new java.lang.IllegalStateException(\"host class field"
            + " delete of undeclared field '\" + key + \"' (producer defect)\");\n");
        out.append("    }\n");
    }

    /**
     * The record storage → production carrier projection of one declared
     * field (the {@code FIELD_READ} direction): the primitive-int and
     * primitive-number storages box into the closed production carriers,
     * a declared array/function storage crosses through the emitted
     * host-to-DEAL projections, and every other storage (string, boolean,
     * record, bytes) is the production value itself.
     */
    private String readProjection(FieldInfo field, String expression) {
        String inner = field.descriptorText().startsWith("?")
            ? field.descriptorText().substring(1) : field.descriptorText();
        // A primitive storage cannot carry the language null (the declared
        // boundary rejects it); every reference storage can (an optional
        // field's present null), so the boxing forms guard it.
        boolean primitive = switch (field.storageType()) {
            case "int", "double", "boolean" -> true;
            default -> false;
        };
        if (inner.equals("int")) {
            String boxed = "java.lang.Long.valueOf((long) " + expression + ")";
            return primitive ? boxed
                : "(" + expression + " == null ? null : " + boxed + ")";
        }
        if (inner.equals("number")) {
            String boxed = "java.lang.Double.valueOf((double) " + expression + ")";
            return primitive ? boxed
                : "(" + expression + " == null ? null : " + boxed + ")";
        }
        if (inner.startsWith("[") || inner.startsWith("(")
                || inner.startsWith("async(")) {
            return artifactClass + ".__hostToDeal(" + javaString(inner) + ", "
                + expression + ")";
        }
        return expression;
    }

    /**
     * The production carrier → record storage projection of one declared
     * field (the {@code FIELD_WRITE} direction): the declared host-facing
     * projection ({@code __hostProjectArg}) then the storage's own
     * unboxing/cast.
     */
    private String writeProjection(FieldInfo field, String expression) {
        return hostFieldWriteProjection(field.descriptorText(), field.storageType(),
            expression, artifactClass + ".__hostProjectArg");
    }

    /**
     * The production carrier &#8594; record storage projection of one
     * declared field (the {@code FIELD_WRITE} and construction-argument
     * direction, ISSUE-0624/K10): the declared host-facing projection
     * ({@code __hostProjectArg}) then the storage's own unboxing/cast — the
     * one producer the record's {@code write} surface and the production
     * construction arm share. The projection helper's reference is qualified
     * explicitly inside the {@code $DealRt} scope (the artifact class owns
     * the crossing helpers) and unqualified inside the artifact class's own
     * emitted members.
     */
    static String hostFieldWriteProjection(String descriptorText, String storageType,
                                           String expression, String projectArgRef) {
        String projected = projectArgRef + "(" + javaString(descriptorText)
            + ", " + expression + ")";
        return switch (storageType) {
            case "int" -> "((java.lang.Number) " + projected + ").intValue()";
            case "double" -> "((java.lang.Number) " + projected + ").doubleValue()";
            case "boolean" -> "((java.lang.Boolean) " + projected + ").booleanValue()";
            default -> storageType.equals("java.lang.Object")
                ? projected
                : "(" + storageType + ") " + projected;
        };
    }

    /** One per-signature function wrapper class (the landed shape id). */
    private void emitShape(StringBuilder out, String shapeId, Type.Func func) {
        out.append("  // DEAL function-value wrapper for descriptor ")
            .append(descriptorText(func)).append(".\n");
        out.append("  static abstract class ").append(shapeId)
            .append(" implements FnValue {\n");
        out.append("    final java.lang.String descriptor = ")
            .append(javaString(descriptorText(func))).append(";\n");
        out.append("    public java.lang.String descriptor() { return descriptor; }\n");
        String ret = returnJavaType(func.returnType());
        out.append("    abstract ").append(ret).append(" invoke(");
        for (int i = 0; i < func.paramTypes().size(); i++) {
            if (i > 0) {
                out.append(", ");
            }
            out.append(carrierType(func.paramTypes().get(i),
                func.paramTypes().get(i) instanceof Type.Nullable))
                .append(" p").append(i);
        }
        out.append(");\n");
        out.append("  }\n\n");
        // The declared bridge of this signature (ISSUE-0651; H7): the
        // host-facing wrapper class over one production function carrier —
        // its typed invoke runs the carrier (the DEAL body's own frames and
        // return cell) and applies the declared return cell's projection.
        // The carrier is resolved the way JvmRuntime.invokeAdapter resolves
        // its source: a production JvmRuntime.AdapterValue runs the D15
        // protocol (JvmRuntime.invokeAdapter resolves the source per the
        // capture mode, runs the source-signature check, and pushes the
        // source body's frame); every other carrier runs its own function id
        // pushed around the invocation, so a host-invoked DEAL body's error
        // snapshot carries the closure's own frame.
        out.append("  static final class __Bridge$").append(shapeId)
            .append(" extends ").append(shapeId).append(" {\n");
        out.append("    final JvmRuntime.FunctionValue $carrier;\n");
        out.append("    __Bridge$").append(shapeId)
            .append("(JvmRuntime.FunctionValue carrier) { this.$carrier = carrier; }\n");
        out.append("    ").append(returnJavaType(func.returnType())).append(" invoke(");
        for (int i = 0; i < func.paramTypes().size(); i++) {
            if (i > 0) {
                out.append(", ");
            }
            out.append(carrierType(func.paramTypes().get(i),
                func.paramTypes().get(i) instanceof Type.Nullable)).append(" p").append(i);
        }
        out.append(") {\n");
        StringBuilder boxed = new StringBuilder();
        for (int i = 0; i < func.paramTypes().size(); i++) {
            if (i > 0) {
                boxed.append(", ");
            }
            boxed.append(boxedParameter(func.paramTypes().get(i), "p" + i));
        }
        Type bridgedReturn = func.returnType();
        boolean voidReturn = bridgedReturn instanceof Type.Null;
        String args = "new java.lang.Object[]{ " + boxed + " }";
        if (!voidReturn) {
            out.append("      java.lang.Object __r;\n");
        }
        out.append("      if (this.$carrier instanceof JvmRuntime.AdapterValue __a) {\n");
        out.append("        ").append(voidReturn ? "" : "__r = ")
            .append("JvmRuntime.invokeAdapter(__a, \"-\", ").append(args)
            .append(");\n");
        out.append("      } else {\n");
        out.append("        boolean __pushed = this.$carrier.fid != null;\n");
        out.append("        if (__pushed) JvmRuntime.pushFrame(this.$carrier.fid);\n");
        out.append("        try {\n");
        out.append("          ").append(voidReturn ? "" : "__r = ")
            .append("this.$carrier.fn.invoke(").append(args).append(");\n");
        out.append("        } finally {\n");
        out.append("          if (__pushed) JvmRuntime.popFrame();\n");
        out.append("        }\n");
        out.append("      }\n");
        if (!voidReturn) {
            out.append("      return ").append(bridgeReturn(func)).append(";\n");
        }
        out.append("    }\n");
        out.append("  }\n");
    }

    /** The boxed production argument of one bridge parameter position. */
    private String boxedParameter(Type param, String name) {
        boolean nullable = param instanceof Type.Nullable;
        Type inner = unwrapNullable(param);
        return switch (inner) {
            case Type.Int ignored -> nullable
                ? "(" + name + " == null ? null : java.lang.Long.valueOf((long) "
                    + name + ".intValue()))"
                : "java.lang.Long.valueOf((long) " + name + ")";
            case Type.Number ignored -> "java.lang.Double.valueOf(" + name + ")";
            case Type.Boolean ignored -> "java.lang.Boolean.valueOf(" + name + ")";
            default -> name;
        };
    }

    /** The declared return cell's projection of one bridge invocation. */
    private String bridgeReturn(Type.Func func) {
        Type ret = func.returnType();
        String desc = descriptorText(ret);
        Type inner = unwrapNullable(ret);
        boolean nullable = ret instanceof Type.Nullable;
        String expression;
        if (inner instanceof Type.Array || inner instanceof Type.Func) {
            String carrier = inner instanceof Type.Array array
                ? arrayCarrier(array.element())
                : JvmBackend.fnShapeId((Type.Func) inner);
            expression = "($DealRt." + carrier + ") " + artifactClass
                + ".__hostProjectArg(" + javaString(desc) + ", __r)";
            if (nullable) {
                expression = "(__r == null ? null : " + expression + ")";
            }
            return expression;
        }
        String carrier = carrierType(ret, nullable);
        return switch (carrier) {
            case "int" -> "((java.lang.Number) __r).intValue()";
            case "double" -> "((java.lang.Number) __r).doubleValue()";
            case "boolean" -> "((java.lang.Boolean) __r).booleanValue()";
            case "java.lang.Integer" -> "(__r == null ? null : java.lang.Integer.valueOf(((java.lang.Number) __r).intValue()))";
            case "java.lang.Double" -> "(__r == null ? null : java.lang.Double.valueOf(((java.lang.Number) __r).doubleValue()))";
            case "java.lang.Boolean" -> "(__r == null ? null : java.lang.Boolean.valueOf(((java.lang.Boolean) __r).booleanValue()))";
            default -> "(" + carrier + ") __r";
        };
    }
}
