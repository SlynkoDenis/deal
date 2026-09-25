package deal.codegen.lua;

import deal.diagnostics.DiagnosticRange;
import deal.ffi.FfiCdefBundle;
import deal.ffi.FfiCdefEntry;
import deal.ffi.FfiClassDescriptor;
import deal.ffi.FfiCompilerClassDefaultPlan;
import deal.ffi.FfiFieldDescriptor;
import deal.ffi.FfiForwardBindings;
import deal.ffi.FfiFunctionDescriptor;
import deal.ffi.FfiGeneratedModule;
import deal.ffi.FfiImportedClassPlanReference;
import deal.ffi.FfiImportedFunctionReference;
import deal.ffi.FfiModuleDescriptor;
import deal.ffi.FfiType;
import deal.project.ProtectedPathOps;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.SemanticIrTextDecodeException;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The LuaJIT FFI import-emission serializer of the extern-C metadata seam
 * (emitter page D6, Architecture item 5; settled seam S1–S6): consumes
 * one immutable {@link FfiGeneratedModule} produced by the extern-C
 * metadata phase ({@code CompilationOrchestrator.ffiGenerations()} —
 * descriptor, cdef bundle, retained plans, forward bindings) and
 * serializes the four argument literals of the pinned
 * {@code __rt.load_ffi(moduleKey, cdefBundle, plans, bindings, file,
 * line, column)} call:
 *
 * <ul>
 *   <li>{@code moduleKey} — the descriptor's {@code "ffi:"} +
 *       canonical-external-identity key (seam S1);</li>
 *   <li>{@code cdefBundle} — digest fields, the complete canonical
 *       {@code fullContent}, the ordered entry list, the native-library
 *       reference, and the canonical function/class metadata (seam
 *       S2–S4);</li>
 *   <li>{@code plans} — per-class plan records carrying the three
 *       canonical content strings, the plan digest, and the ordered
 *       field-entry list whose deferred evaluators are lowered from the
 *       canonical evaluator content (seam S5); no evaluator ever runs
 *       during emission or load;</li>
 *   <li>{@code bindings} — moduleKey, {@code "UNBOUND"}, the source-order
 *       forward cells, and the carried graph-ordered imported
 *       references (seam S6).</li>
 * </ul>
 *
 * <p>The emitter never emits {@code ffi.C[...]} access and never raises
 * {@code FFI_UNSUPPORTED_BACKEND} (LuaJIT is the capable backend).
 * Unrepresentable content (an evaluator shape outside the lowered
 * surface, an unresolvable loader text) returns a {@link FfiFailure};
 * the backend reports it as a defensive E6000 config failure at the
 * import statement and writes no misleading artifact content.</p>
 *
 * <p>Native-library loader texts are normalized at emission: a
 * {@code MANIFEST_RELATIVE_PATH} loader text (directives D5) resolves
 * against the compilation's manifest directory through
 * {@link ProtectedPathOps#normalizePrefixResolved} — the pinned
 * symlink-resolved physical text that becomes the runtime identity field
 * {@code exactNormalizedLoaderText} (seam S3). The classification kind
 * stays the compile-side classification; the loader text alone is the
 * normalized value {@code dlopen} receives.</p>
 *
 * <p>Determinism: every iteration is source order or sorted; digests and
 * content strings are carried verbatim from the metadata (indexes only,
 * never recomputed); no address, timestamp, ordinal, or process state
 * enters any literal.</p>
 */
public final class LuaFfiBindingGenerator {

    private LuaFfiBindingGenerator() {
        // Static utility; no instances.
    }

    /** One unrepresentable extern-c shape (a defensive config failure). */
    public record FfiFailure(String message) {
    }

    /**
     * The four argument literals of the {@code load_ffi} call, in the
     * pinned five-position envelope order (the span triplet is appended
     * by the backend from the import node's span), plus the import
     * prelude: one {@code local <prefix><alias> = require("<module>")}
     * line per provider module the plan evaluators reference (graph
     * order, first-reference order) — the retained per-module backend
     * emits them before the bindings local so every evaluator closure
     * captures a bound provider. The production project session
     * re-points the same bindings at the chunk's export-surface registry
     * through {@link #providerBindings} (never a {@code require} line:
     * the one-chunk layout has no per-provider module artifact).
     */
    public record LoadCallParts(String moduleKeyLiteral, String bundleLiteral,
                                String plansLiteral,
                                String bindingsLiteral,
                                List<String> importLines) {
    }

    /**
     * One provider binding of the emitted import prelude: the import
     * alias the deployed plan evaluators call through
     * ({@code <prefix><alias>.<export>.f(...)}) with the provider
     * module's dotted path (the chunk export-surface registry key of
     * the production session).
     *
     * @param importAlias         the declaration's import alias;
     *                            non-null
     * @param importedModulePath  the provider module's dotted module
     *                            path; non-null
     */
    public record ProviderBinding(String importAlias,
                                  String importedModulePath) {

        public ProviderBinding {
            Objects.requireNonNull(importAlias, "importAlias must not be null");
            Objects.requireNonNull(importedModulePath,
                "importedModulePath must not be null");
        }
    }

    /** Either the failure or the complete call parts. */
    public record Generation(FfiFailure failure, LoadCallParts parts) {
    }

    // =========================================================================
    // Generation entry
    // =========================================================================

    /**
     * Generates the complete {@code load_ffi} argument literals for one
     * extern-c import from the metadata phase's generated module.
     *
     * @param module            the validated-and-generated extern-c module
     *                          inputs (descriptor, bundle, plans, bindings)
     * @param manifestDirectory the compilation's manifest directory text
     *                          (the base of manifest-relative loader-text
     *                          resolution); an empty text denotes the
     *                          process CWD exactly like the protected path
     *                          conversion does
     * @param bindingsLocal     the Lua local name the backend emits for
     *                          the bindings literal — deferred evaluators
     *                          close over it to dereference the same-module
     *                          forward cells (adopted D6: evaluators close
     *                          over cells, never over a not-yet-published
     *                          export table)
     * @param importPrefix      the per-import Lua local prefix of the
     *                          imported provider bindings — deferred
     *                          evaluators referencing imported functions
     *                          call {@code <prefix><alias>.<export>.f}
     *                          on the provider module the prelude requires
     * @return the failure or the four literals plus the prelude lines
     */
    public static Generation generate(FfiGeneratedModule module,
            String manifestDirectory, String bindingsLocal,
            String importPrefix) {
        Objects.requireNonNull(module, "module");
        Objects.requireNonNull(bindingsLocal, "bindingsLocal");
        Objects.requireNonNull(importPrefix, "importPrefix");
        FfiModuleDescriptor descriptor = module.descriptor();
        FfiCdefBundle bundle = module.cdefBundle();

        // The native-library reference (seam S3): the classified kind plus
        // the normalized loader text. A manifest-relative text resolves
        // absolute against the manifest directory through the pinned
        // prefix-resolved symlink conversion (the library file itself may
        // not exist yet — the runtime open is the existence check).
        String kind = bundle.nativeLibraryKind();
        String loaderText = bundle.nativeLibraryLoaderText();
        if ("MANIFEST_RELATIVE_PATH".equals(kind)) {
            Path relative = Path.of(loaderText == null ? "" : loaderText);
            String absoluteText = manifestDirectory == null
                || manifestDirectory.isEmpty()
                    ? relative.toString()
                    : Path.of(manifestDirectory).resolve(relative).toString();
            ProtectedPathOps.PathResult resolved =
                ProtectedPathOps.normalizePrefixResolved(absoluteText);
            if (resolved instanceof ProtectedPathOps.PathResult.Failure
                    failure) {
                return new Generation(new FfiFailure(
                    "native library loader text '" + loaderText
                        + "' of module '" + descriptor.moduleKey()
                        + "' cannot be resolved against the manifest"
                        + " directory: " + failure.reason()), null);
            }
            loaderText = ((ProtectedPathOps.PathResult.Success) resolved)
                .resolvedPath().toString();
        }

        String bundleLiteral = bundleLiteral(bundle, kind, loaderText);
        Object[] plans = plansLiteral(module, bindingsLocal, importPrefix);
        if (plans[0] instanceof FfiFailure failure) {
            return new Generation(failure, null);
        }
        String bindingsLiteral = bindingsLiteral(descriptor,
            module.bindings());

        return new Generation(null, new LoadCallParts(
            LuaAbi.stringLiteral(descriptor.moduleKey()),
            bundleLiteral, (String) plans[0], bindingsLiteral,
            importPrelude(module.bindings(), importPrefix)));
    }

    /**
     * The provider bindings of one generated module, in graph order
     * (first reference per alias; the validator's import surface binds
     * one alias to exactly one provider module, so the first reference
     * is the binding): the one alias &rarr; provider-module mapping
     * authority both emission layouts consume — the retained per-module
     * prelude through {@link #importPrelude} and the production project
     * session through the chunk export-surface registry.
     *
     * @param bindings the generated module's frozen forward bindings;
     *                 non-null
     * @return the provider bindings in the generator's order; non-null
     */
    public static List<ProviderBinding> providerBindings(
            FfiForwardBindings bindings) {
        Objects.requireNonNull(bindings, "bindings must not be null");
        Map<String, String> aliasModules = new LinkedHashMap<>();
        for (FfiImportedFunctionReference ref
                : bindings.importedFunctions()) {
            aliasModules.putIfAbsent(ref.importAlias(),
                ref.importedModulePath());
        }
        for (FfiImportedClassPlanReference ref
                : bindings.importedClassPlans()) {
            aliasModules.putIfAbsent(ref.importAlias(),
                ref.importedModulePath());
        }
        List<ProviderBinding> result = new ArrayList<>();
        for (Map.Entry<String, String> entry : aliasModules.entrySet()) {
            result.add(new ProviderBinding(entry.getKey(), entry.getValue()));
        }
        return List.copyOf(result);
    }

    /**
     * The import prelude: one {@code local <prefix><alias> =
     * require("<dotted module path>")} line per provider module the
     * carried references name, in graph order.
     */
    private static List<String> importPrelude(FfiForwardBindings bindings,
            String importPrefix) {
        List<String> lines = new ArrayList<>();
        for (ProviderBinding binding : providerBindings(bindings)) {
            lines.add("local " + importPrefix + binding.importAlias()
                + " = require("
                + LuaAbi.stringLiteral(binding.importedModulePath()) + ")");
        }
        return lines;
    }

    // =========================================================================
    // Bundle literal (seam S1–S4)
    // =========================================================================

    /** The complete cdef-bundle table literal. */
    private static String bundleLiteral(FfiCdefBundle bundle, String kind,
            String loaderText) {
        StringBuilder out = new StringBuilder("{ ");
        out.append(LuaAbi.tableField("bundleDigest",
            LuaAbi.stringLiteral(bundle.bundleDigest())));
        out.append(", ").append(LuaAbi.tableField("identityDigest",
            LuaAbi.stringLiteral(bundle.identityDigest())));
        out.append(", ").append(LuaAbi.tableField("fullContent",
            LuaAbi.stringLiteral(bundle.fullContent())));

        // The native-library reference: kind/loaderText may be nil only
        // for the defensive no-library case (a runtime FFI_LIBRARY_LOAD).
        StringBuilder nativeLibrary = new StringBuilder("{ ");
        nativeLibrary.append(LuaAbi.tableField("kind",
            kind == null ? "nil" : LuaAbi.stringLiteral(kind)));
        nativeLibrary.append(", ").append(LuaAbi.tableField("loaderText",
            loaderText == null ? "nil" : LuaAbi.stringLiteral(loaderText)));
        nativeLibrary.append(" }");
        out.append(", ").append(LuaAbi.tableField("nativeLibrary",
            nativeLibrary.toString()));

        // Ordered entries: struct typedefs first (dependency order), then
        // function typedefs (declaration order).
        StringBuilder entries = new StringBuilder("{ ");
        boolean first = true;
        for (FfiCdefEntry entry : bundle.entries()) {
            if (!first) {
                entries.append(", ");
            }
            first = false;
            StringBuilder owned = new StringBuilder("{ ");
            for (int i = 0; i < entry.ownedNames().size(); i++) {
                if (i > 0) {
                    owned.append(", ");
                }
                owned.append(LuaAbi.stringLiteral(entry.ownedNames().get(i)));
            }
            owned.append(" }");
            entries.append("{ ").append(LuaAbi.tableField("entryDigest",
                LuaAbi.stringLiteral(entry.entryDigest())));
            entries.append(", ").append(LuaAbi.tableField("fullText",
                LuaAbi.stringLiteral(entry.fullText())));
            entries.append(", ").append(LuaAbi.tableField("ownedNames",
                owned.toString()));
            entries.append(" }");
        }
        entries.append(" }");
        out.append(", ").append(LuaAbi.tableField("entries",
            entries.toString()));

        // Canonical function metadata in declaration order.
        StringBuilder functions = new StringBuilder("{ ");
        for (int i = 0; i < bundle.functions().size(); i++) {
            if (i > 0) {
                functions.append(", ");
            }
            functions.append(functionLiteral(bundle.functions().get(i)));
        }
        functions.append(" }");
        out.append(", ").append(LuaAbi.tableField("functions",
            functions.toString()));

        // Canonical class metadata in declaration order.
        StringBuilder classes = new StringBuilder("{ ");
        for (int i = 0; i < bundle.classes().size(); i++) {
            if (i > 0) {
                classes.append(", ");
            }
            classes.append(classLiteral(bundle.classes().get(i)));
        }
        classes.append(" }");
        out.append(", ").append(LuaAbi.tableField("classes",
            classes.toString()));
        out.append(" }");
        return out.toString();
    }

    /** One function metadata row literal (seam S4). */
    private static String functionLiteral(FfiFunctionDescriptor fn) {
        StringBuilder params = new StringBuilder("{ ");
        for (int i = 0; i < fn.orderedParams().size(); i++) {
            if (i > 0) {
                params.append(", ");
            }
            params.append(typeLiteral(fn.orderedParams().get(i)));
        }
        params.append(" }");
        StringBuilder out = new StringBuilder("{ ");
        out.append(LuaAbi.tableField("dealName",
            LuaAbi.stringLiteral(fn.dealName())));
        out.append(", ").append(LuaAbi.tableField("cSymbol",
            LuaAbi.stringLiteral(fn.cSymbol())));
        out.append(", ").append(LuaAbi.tableField("privateFunctionPointerType",
            LuaAbi.stringLiteral(fn.privateFunctionPointerType())));
        out.append(", ").append(LuaAbi.tableField("orderedParams",
            params.toString()));
        out.append(", ").append(LuaAbi.tableField("returnType",
            typeLiteral(fn.returnType())));
        out.append(" }");
        return out.toString();
    }

    /** One class metadata row literal (seam S4). */
    private static String classLiteral(FfiClassDescriptor cls) {
        StringBuilder fields = new StringBuilder("{ ");
        for (int i = 0; i < cls.orderedFields().size(); i++) {
            if (i > 0) {
                fields.append(", ");
            }
            FfiFieldDescriptor field = cls.orderedFields().get(i);
            fields.append("{ ").append(LuaAbi.tableField("dealName",
                LuaAbi.stringLiteral(field.dealName())));
            fields.append(", ").append(LuaAbi.tableField("fieldOrdinal",
                Integer.toString(field.fieldOrdinal())));
            fields.append(", ").append(LuaAbi.tableField("type",
                typeLiteral(field.type())));
            fields.append(" }");
        }
        fields.append(" }");
        StringBuilder out = new StringBuilder("{ ");
        out.append(LuaAbi.tableField("name",
            LuaAbi.stringLiteral(cls.name())));
        out.append(", ").append(LuaAbi.tableField("canonicalClassIdentity",
            LuaAbi.stringLiteral(cls.canonicalClassIdentity())));
        out.append(", ").append(LuaAbi.tableField("qualifiedDealDescriptor",
            LuaAbi.stringLiteral(cls.qualifiedDealDescriptor())));
        out.append(", ").append(LuaAbi.tableField("kind",
            LuaAbi.stringLiteral(cls.kind().name())));
        out.append(", ").append(LuaAbi.tableField("orderedFields",
            fields.toString()));
        out.append(" }");
        return out.toString();
    }

    /** The settled FfiType row literal (seam S4). */
    private static String typeLiteral(FfiType type) {
        return "{ " + LuaAbi.tableField("kind",
            LuaAbi.stringLiteral(type.kind().name()))
            + ", " + LuaAbi.tableField("canonicalDescriptor",
                LuaAbi.stringLiteral(type.canonicalDescriptor()))
            + ", " + LuaAbi.tableField("canonicalClassIdentity",
                type.canonicalClassIdentity() == null ? "nil"
                    : LuaAbi.stringLiteral(type.canonicalClassIdentity()))
            + " }";
    }

    // =========================================================================
    // Plans literal (seam S5)
    // =========================================================================

    /**
     * The plans table literal plus the failure channel:
     * {@code [0] == null} carries the literal, else the failure.
     */
    private static Object[] plansLiteral(FfiGeneratedModule module,
            String bindingsLocal, String importPrefix) {
        Set<String> sameModuleFunctions = new LinkedHashSet<>();
        for (FfiFunctionDescriptor fn : module.descriptor().functions()) {
            sameModuleFunctions.add(fn.dealName());
        }
        Map<String, FfiImportedFunctionReference> importedFunctions =
            new LinkedHashMap<>();
        for (FfiImportedFunctionReference ref
                : module.bindings().importedFunctions()) {
            importedFunctions.put(ref.importAlias() + "|"
                + ref.exportName(), ref);
        }
        StringBuilder out = new StringBuilder("{ ");
        boolean first = true;
        for (Map.Entry<String, FfiCompilerClassDefaultPlan> entry
                : module.plans().entrySet()) {
            if (!first) {
                out.append(", ");
            }
            first = false;
            FfiCompilerClassDefaultPlan plan = entry.getValue();
            StringBuilder planList = new StringBuilder("{ ");
            for (int i = 0; i < plan.entries().size(); i++) {
                if (i > 0) {
                    planList.append(", ");
                }
                FfiCompilerClassDefaultPlan.Entry field = plan.entries().get(i);
                String evaluator;
                if (field.hasDefaultEvaluator()) {
                    Object[] lowered = lowerEvaluator(
                        field.evaluatorContent(), sameModuleFunctions,
                        importedFunctions, bindingsLocal, importPrefix,
                        "default of field '" + field.name() + "' of plan '"
                            + entry.getKey() + "'");
                    if (lowered[0] instanceof FfiFailure failure) {
                        return new Object[] { failure };
                    }
                    evaluator = "function() return " + lowered[0] + " end";
                } else {
                    evaluator = "nil";
                }
                planList.append("{ ").append(LuaAbi.tableField("name",
                    LuaAbi.stringLiteral(field.name())));
                planList.append(", ").append(LuaAbi.tableField("descriptor",
                    LuaAbi.stringLiteral(field.canonicalDescriptor())));
                planList.append(", optional = false");
                planList.append(", ").append(LuaAbi.tableField("evaluator",
                    evaluator));
                planList.append(" }");
            }
            planList.append(" }");
            StringBuilder record = new StringBuilder("{ ");
            record.append(LuaAbi.tableField("plan", planList.toString()));
            record.append(", ").append(LuaAbi.tableField(
                "canonicalPlanContent",
                LuaAbi.stringLiteral(plan.canonicalPlanContent())));
            record.append(", ").append(LuaAbi.tableField(
                "semanticDefaultContents",
                LuaAbi.stringLiteral(plan.semanticDefaultContents())));
            record.append(", ").append(LuaAbi.tableField(
                "evaluatorImplementationContents",
                LuaAbi.stringLiteral(plan.evaluatorImplementationContents())));
            record.append(", ").append(LuaAbi.tableField("planDigest",
                LuaAbi.stringLiteral(plan.planDigest())));
            record.append(" }");
            out.append(LuaAbi.tableField(entry.getKey(), record.toString()));
        }
        out.append(" }");
        return new Object[] { out.toString() };
    }

    // =========================================================================
    // Bindings literal (seam S6)
    // =========================================================================

    /** The forward-bindings table literal. */
    private static String bindingsLiteral(FfiModuleDescriptor descriptor,
            FfiForwardBindings bindings) {
        StringBuilder out = new StringBuilder("{ ");
        out.append(LuaAbi.tableField("moduleKey",
            LuaAbi.stringLiteral(descriptor.moduleKey())));
        out.append(", ").append(LuaAbi.tableField("state",
            LuaAbi.stringLiteral("UNBOUND")));
        StringBuilder cells = new StringBuilder("{ ");
        // Source order (the descriptor's declaration order — the same
        // order the metadata generator created the cells in); the map's
        // own iteration order is not guaranteed.
        boolean first = true;
        for (FfiFunctionDescriptor fn : descriptor.functions()) {
            if (!first) {
                cells.append(", ");
            }
            first = false;
            cells.append(LuaAbi.tableField(fn.dealName(),
                "{ state = \"UNBOUND\", wrapper = nil, errorValue = nil }"));
        }
        cells.append(" }");
        out.append(", ").append(LuaAbi.tableField("cells",
            cells.toString()));

        StringBuilder importedFunctions = new StringBuilder("{ ");
        for (int i = 0; i < bindings.importedFunctions().size(); i++) {
            if (i > 0) {
                importedFunctions.append(", ");
            }
            importedFunctions.append(importedFunctionLiteral(
                bindings.importedFunctions().get(i)));
        }
        importedFunctions.append(" }");
        out.append(", ").append(LuaAbi.tableField("importedFunctions",
            importedFunctions.toString()));

        StringBuilder importedClassPlans = new StringBuilder("{ ");
        for (int i = 0; i < bindings.importedClassPlans().size(); i++) {
            if (i > 0) {
                importedClassPlans.append(", ");
            }
            importedClassPlans.append(importedClassPlanLiteral(
                bindings.importedClassPlans().get(i)));
        }
        importedClassPlans.append(" }");
        out.append(", ").append(LuaAbi.tableField("importedClassPlans",
            importedClassPlans.toString()));
        out.append(" }");
        return out.toString();
    }

    /** One carried graph-ordered imported function reference literal. */
    private static String importedFunctionLiteral(
            FfiImportedFunctionReference ref) {
        return "{ " + LuaAbi.tableField("importAlias",
            LuaAbi.stringLiteral(ref.importAlias()))
            + ", " + LuaAbi.tableField("exportName",
                LuaAbi.stringLiteral(ref.exportName()))
            + ", " + LuaAbi.tableField("importedModulePath",
                LuaAbi.stringLiteral(ref.importedModulePath()))
            + ", " + LuaAbi.tableField("canonicalDescriptor",
                LuaAbi.stringLiteral(ref.canonicalDescriptor()))
            + ", " + LuaAbi.tableField("providerContractDigest",
                LuaAbi.stringLiteral(ref.providerContractDigest()))
            + ", " + LuaAbi.tableField("graphOrder",
                Integer.toString(ref.graphOrder()))
            + ", " + LuaAbi.tableField("sourceRange",
                rangeLiteral(ref.sourceRange()))
            + " }";
    }

    /** One carried graph-ordered imported class-plan reference literal. */
    private static String importedClassPlanLiteral(
            FfiImportedClassPlanReference ref) {
        return "{ " + LuaAbi.tableField("importAlias",
            LuaAbi.stringLiteral(ref.importAlias()))
            + ", " + LuaAbi.tableField("className",
                LuaAbi.stringLiteral(ref.className()))
            + ", " + LuaAbi.tableField("importedModulePath",
                LuaAbi.stringLiteral(ref.importedModulePath()))
            + ", " + LuaAbi.tableField("canonicalDescriptor",
                LuaAbi.stringLiteral(ref.canonicalDescriptor()))
            + ", " + LuaAbi.tableField("providerContractDigest",
                LuaAbi.stringLiteral(ref.providerContractDigest()))
            + ", " + LuaAbi.tableField("graphOrder",
                Integer.toString(ref.graphOrder()))
            + ", " + LuaAbi.tableField("sourceRange",
                rangeLiteral(ref.sourceRange()))
            + " }";
    }

    /** The complete scalar source range literal of one reference. */
    private static String rangeLiteral(DiagnosticRange range) {
        return "{ " + LuaAbi.tableField("file",
            LuaAbi.stringLiteral(range.file()))
            + ", " + LuaAbi.tableField("startLine",
                Integer.toString(range.startLine()))
            + ", " + LuaAbi.tableField("startColumn",
                Integer.toString(range.startColumn()))
            + ", " + LuaAbi.tableField("endLine",
                Integer.toString(range.endLine()))
            + ", " + LuaAbi.tableField("endColumn",
                Integer.toString(range.endColumn()))
            + ", " + LuaAbi.tableField("startScalarOffset",
                Integer.toString(range.startScalarOffset()))
            + ", " + LuaAbi.tableField("endScalarOffset",
                Integer.toString(range.endScalarOffset()))
            + ", " + LuaAbi.tableField("scalarLength",
                Integer.toString(range.scalarLength()))
            + ", " + LuaAbi.tableField("origin",
                LuaAbi.stringLiteral(range.origin().name()))
            + " }";
    }

    // =========================================================================
    // Deferred evaluator lowering (seam S5)
    // =========================================================================

    /**
     * Lowers one canonical evaluator-content expression (the validator's
     * {@code FfiContentSerializer} structural JSON) to a Lua expression:
     * {@code [0] == null} carries the rendered text, else the
     * {@link FfiFailure}. The lowered surface covers the declarable
     * default forms — int/number/boolean/string/null literals and calls
     * of declared functions (a same-file callee dereferences the
     * same-module forward cell; an {@code alias.export} callee routes
     * through the prelude's required provider module) — and fails closed
     * on every other shape so no artifact ever misrepresents a default.
     */
    private static Object[] lowerEvaluator(String content,
            Set<String> sameModuleFunctions,
            Map<String, FfiImportedFunctionReference> importedFunctions,
            String bindingsLocal, String importPrefix, String context) {
        CanonicalJson.Value value;
        try {
            value = CanonicalJson.parse(content);
        } catch (SemanticIrTextDecodeException e) {
            return new Object[] { new FfiFailure(
                context + " carries malformed canonical evaluator content: "
                    + e.getMessage()) };
        }
        return lowerExpression(value, sameModuleFunctions,
            importedFunctions, bindingsLocal, importPrefix, context);
    }

    /** One canonical expression node to Lua source. */
    private static Object[] lowerExpression(CanonicalJson.Value value,
            Set<String> sameModuleFunctions,
            Map<String, FfiImportedFunctionReference> importedFunctions,
            String bindingsLocal, String importPrefix, String context) {
        if (!(value instanceof CanonicalJson.Obj obj)) {
            return new Object[] { new FfiFailure(
                context + " is not a canonical expression node") };
        }
        String kind = objField(obj, "k");
        if (kind == null) {
            return new Object[] { new FfiFailure(
                context + " carries no expression kind") };
        }
        return switch (kind) {
            case "literal" -> {
                CanonicalJson.Value literal = objValue(obj, "value");
                yield literal == null
                    ? new Object[] { new FfiFailure(
                        context + " literal carries no value") }
                    : lowerLiteral(literal, context);
            }
            case "call" -> lowerCall(obj, sameModuleFunctions,
                importedFunctions, bindingsLocal, importPrefix, context);
            default -> new Object[] { new FfiFailure(
                context + " uses the unsupported canonical expression form"
                    + " '" + kind + "' (the emitted evaluator surface covers"
                    + " literals and calls of declared functions —"
                    + " same-file or imported)") };
        };
    }

    /** One canonical literal value to Lua source. */
    private static Object[] lowerLiteral(CanonicalJson.Value value,
            String context) {
        return switch (value) {
            case CanonicalJson.Null ignored -> new Object[] { "__NULL" };
            case CanonicalJson.Bool b -> new Object[] {
                b.value() ? "true" : "false" };
            case CanonicalJson.Int i -> new Object[] {
                Integer.toString(i.value()) };
            case CanonicalJson.Num n -> {
                double v = n.value();
                if (Double.isNaN(v)) {
                    yield new Object[] { "(0/0)" };
                }
                if (Double.isInfinite(v)) {
                    yield new Object[] { v > 0 ? "(1/0)" : "(-1/0)" };
                }
                yield new Object[] { Double.toString(v) };
            }
            case CanonicalJson.Str s -> new Object[] {
                LuaAbi.stringLiteral(s.value()) };
            default -> new Object[] { new FfiFailure(
                context + " carries a non-literal value") };
        };
    }

    /**
     * One canonical call node: the callee is either a bare identifier
     * naming a same-file declared function — the wrapper is dereferenced
     * through the module's forward cell (adopted D6) — or an
     * {@code alias.export} member naming a graph-ordered imported
     * function reference (seam S6), invoked through the prelude's
     * required provider module. Either wrapper is invoked with the
     * rendered arguments plus the pinned trailing call-site triplet. The
     * evaluator content carries the default expression's scalar range
     * only (no line/column triplet), so the forwarded span fields are
     * nils — the same empty site every canonical content string implies.
     */
    private static Object[] lowerCall(CanonicalJson.Obj call,
            Set<String> sameModuleFunctions,
            Map<String, FfiImportedFunctionReference> importedFunctions,
            String bindingsLocal, String importPrefix, String context) {
        CanonicalJson.Value callee = objValue(call, "callee");
        if (!(callee instanceof CanonicalJson.Obj calleeObj)) {
            return new Object[] { new FfiFailure(
                context + " call carries no callee expression") };
        }
        String calleeKind = objField(calleeObj, "k");
        String calleeText;
        if ("identifier".equals(calleeKind)) {
            // A same-module declared function: dereference the
            // same-module forward cell (adopted D6).
            String name = objField(calleeObj, "name");
            if (name == null || !sameModuleFunctions.contains(name)) {
                return new Object[] { new FfiFailure(
                    context + " calls '" + (name == null ? "<none>" : name)
                        + "', which is not a declared function of the same"
                        + " extern-c module") };
            }
            calleeText = LuaAbi.memberAccess(
                bindingsLocal + ".cells", name) + ".wrapper";
        } else if ("member".equals(calleeKind)) {
            // An imported provider function: alias.<export> routes
            // through the prelude's required provider module (the
            // graph-ordered imported references, seam S6).
            CanonicalJson.Value object = objValue(calleeObj, "object");
            String alias = object instanceof CanonicalJson.Obj objectObj
                && "identifier".equals(objField(objectObj, "k"))
                    ? objField(objectObj, "name") : null;
            String exportName = objField(calleeObj, "field");
            FfiImportedFunctionReference ref = alias == null
                || exportName == null ? null
                    : importedFunctions.get(alias + "|" + exportName);
            if (ref == null) {
                return new Object[] { new FfiFailure(
                    context + " calls '" + (alias == null ? "<none>" : alias)
                        + "." + (exportName == null ? "<none>" : exportName)
                        + "', which carries no imported function reference"
                        + " of the extern-c module") };
            }
            calleeText = LuaAbi.memberAccess(importPrefix + alias,
                exportName);
        } else {
            return new Object[] { new FfiFailure(
                context + " calls a non-identifier and non-member callee"
                    + " (canonical form '" + (calleeKind == null
                        ? "<none>" : calleeKind)
                    + "' is outside the emitted evaluator surface)") };
        }
        CanonicalJson.Value argsValue = objValue(call, "args");
        if (!(argsValue instanceof CanonicalJson.Arr args)) {
            return new Object[] { new FfiFailure(
                context + " call carries no argument list") };
        }
        StringBuilder rendered = new StringBuilder();
        for (int i = 0; i < args.items().size(); i++) {
            Object[] lowered = lowerExpression(args.items().get(i),
                sameModuleFunctions, importedFunctions, bindingsLocal,
                importPrefix, context + " argument " + (i + 1));
            if (lowered[0] instanceof FfiFailure failure) {
                return new Object[] { failure };
            }
            if (i > 0) {
                rendered.append(", ");
            }
            rendered.append(lowered[0]);
        }
        // The wrapper closure takes f(v1, ..., vN, file, line, column):
        // the three span fields are nils (the canonical evaluator content
        // carries scalar offsets only, never a call-site triplet).
        String spanSuffix = rendered.length() == 0
            ? "nil, nil, nil" : ", nil, nil, nil";
        return new Object[] { calleeText + ".f(" + rendered
            + spanSuffix + ")" };
    }

    /** The string value of one object field, or null. */
    private static String objField(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = objValue(obj, key);
        return value instanceof CanonicalJson.Str str ? str.value() : null;
    }

    /** The value of one object field, or null. */
    private static CanonicalJson.Value objValue(CanonicalJson.Obj obj,
            String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        return null;
    }
}
