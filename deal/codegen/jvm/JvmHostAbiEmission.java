package deal.codegen.jvm;

import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
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

    /** One declared field of a synthesized record. */
    private record FieldInfo(String javaName, String storageType, boolean optional) {
    }

    private final List<HostModule> modules;
    /** The per-signature wrapper classes by shape id (declaration order). */
    private final Map<String, Type.Func> shapes = new LinkedHashMap<>();
    /** The synthesized records by simple name (declaration order). */
    private final Map<String, RecordInfo> records = new LinkedHashMap<>();
    /** The per-class array-wrapper simple names by class-carrying specifier/name key. */
    private final Map<String, String> classArrayWrappers = new LinkedHashMap<>();

    JvmHostAbiEmission(List<HostModule> modules) {
        this.modules = List.copyOf(Objects.requireNonNull(modules,
            "modules must not be null"));
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
            Type inner = fieldType instanceof Type.Nullable nullable
                ? nullable.inner() : fieldType;
            String storage = carrierType(inner, field.declaration().optional());
            fields.add(new FieldInfo(JvmBackend.javaName(field.declaration().name()),
                storage, field.declaration().optional()));
            collectType(module, fieldType);
        }
        String arrayWrapper = "$HostArr$" + JvmBackend.escapedIdentifier(
            specifier.replace('.', '/')) + "$" + JvmBackend.javaName(className);
        records.put(simple, new RecordInfo(simple, arrayWrapper, identityText, fields));
        classArrayWrappers.putIfAbsent(classNameKey(specifier, className),
            arrayWrapper);
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
        boolean nullable = type instanceof Type.Nullable;
        return carrierType(type, nullable);
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
            .append(" (the declared fields in declaration order).\n");
        out.append("  static final class ").append(record.simpleName()).append(" {\n");
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
        out.append("  }\n");
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
        out.append("  }\n");
    }
}
