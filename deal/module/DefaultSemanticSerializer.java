package deal.module;

import deal.ast.Block;
import deal.ast.ClassDeclaration;
import deal.ast.ForInit;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.FunctionExpr;
import deal.ast.LiteralValue;
import deal.ast.Parameter;
import deal.ast.StatementNode;
import deal.ast.TryStatement;
import deal.ast.TypeNode;
import deal.ast.VariableDeclaration;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.diagnostics.DiagnosticRange;
import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;
import deal.semantic.ir.CanonicalJson;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The versioned canonical serializer of typed default semantics
 * (ISSUE-0542, design source
 * {@code provider-versioned-default-plans} D5/D6/D8/D9): the
 * expression grammar over the complete checked construct set, the
 * statement-level {@code CanonicalFunctionSemantics} grammar for
 * provider function bodies, SHA-256 digests as indexes with
 * full-content equality, {@code canonicalPlanContent}/
 * {@code planDigest}, the {@code semanticDefaultContents} projection,
 * and the completion of the plan-embedded
 * {@link ResolvedDefaultExpression#runtimeResources()} with the
 * computed provider digests.
 *
 * <p><b>Invocation contract (task-pinned):</b> digest computation is
 * demand-driven and is invoked only for compilations whose merged
 * runtime-edge occurrence structure is acyclic — the production
 * pipeline invokes this serializer only after the graph epic's
 * (ISSUE-0543) digest-free SCC pass rejects runtime SCCs with E2005,
 * so digest equations are well-founded (D9). The graph epic
 * (ISSUE-0543) owns the orchestrator phase that invokes this
 * serializer after its digest-free SCC pass, demanding the ordinary
 * runtime-use occurrences through the additional-demand overload
 * ({@link #serialize(Map, Map, List)}). A defensive reentrant-demand
 * guard fails closed with a deterministic E6005 error at the first
 * reentrant provider — never a hang, never a placeholder — so a broken
 * acyclicity gate fails loudly.</p>
 *
 * <p><b>Boundary (task-pinned):</b> this epic completes
 * {@code runtimeResources} only. It constructs no
 * {@link RuntimeImportDependency} record, merges no edge set, runs no
 * graph, and emits no E2005.</p>
 */
public final class DefaultSemanticSerializer {

    private DefaultSemanticSerializer() {
        // Static entry; no instances.
    }

    /**
     * The one versioned canonical format constant shared by the
     * expression grammar (D6) and the statement grammar (D9). Any
     * incompatible change to either grammar bumps this constant.
     */
    public static final String SERIALIZER_VERSION = "1";

    // =========================================================================
    // Result shapes
    // =========================================================================

    /**
     * One serialized class: the completed compiler plan (every entry's
     * default carries canonical content, semantic digest, and ordered
     * digest-bearing runtime resources; {@code runtimeDependencies}
     * stays empty — the graph epic's seam) plus the three pinned
     * content projections (D6).
     *
     * @param completedPlan            the completed compiler plan
     * @param canonicalPlanContent     the complete canonical plan
     *                                 serialization
     * @param planDigest               SHA-256 over
     *                                 {@code canonicalPlanContent} (an
     *                                 index only)
     * @param semanticDefaultContents  the ordered per-entry canonical
     *                                 semantic-default content
     *                                 projection
     */
    public record SerializedDefaultClass(
        CompilerClassDefaultPlan completedPlan,
        String canonicalPlanContent,
        String planDigest,
        String semanticDefaultContents
    ) {

        public SerializedDefaultClass {
            Objects.requireNonNull(completedPlan, "completedPlan");
            Objects.requireNonNull(canonicalPlanContent,
                "canonicalPlanContent");
            Objects.requireNonNull(planDigest, "planDigest");
            Objects.requireNonNull(semanticDefaultContents,
                "semanticDefaultContents");
        }
    }

    /**
     * The serialization result: the diagnostics (never null) and the
     * serialized classes in planning order, keyed by module source
     * path (empty when any error-level diagnostic fired — failure
     * publishes nothing), plus the computed provider digests and the
     * computed provider canonical contents, keyed by the provider's
     * semantic resource identity (a function's canonical
     * {@code CanonicalFunctionSemantics} text, a class's full
     * {@code canonicalPlanContent}).
     */
    public record Result(
        List<CompilerDiagnostic> diagnostics,
        Map<String, List<SerializedDefaultClass>> serializedClasses,
        Map<SemanticResourceIdentity, String> providerDigests,
        Map<SemanticResourceIdentity, String> providerContents
    ) {

        public Result {
            diagnostics = List.copyOf(Objects.requireNonNull(diagnostics,
                "diagnostics"));
            serializedClasses = unmodifiableOrderedClasses(
                Objects.requireNonNull(serializedClasses,
                    "serializedClasses"));
            providerDigests = unmodifiableOrderedMap(
                Objects.requireNonNull(providerDigests,
                    "providerDigests"));
            providerContents = unmodifiableOrderedMap(
                Objects.requireNonNull(providerContents,
                    "providerContents"));
        }

        /** True when any diagnostic is an error (no classes then). */
        public boolean hasErrors() {
            return diagnostics.stream().anyMatch(
                d -> "error".equals(d.severity()));
        }
    }

    /**
     * Serializes every planned class of the given compilation inputs:
     * canonical default content and semantic digests per entry,
     * digest-bearing completed {@code runtimeResources} in the
     * planner's first-occurrence order, provider digests per kind
     * (implementation function, declared function wrapper, class plan)
     * computed provider-before-consumer and demand-driven, and the
     * {@code canonicalPlanContent}/{@code planDigest}/
     * {@code semanticDefaultContents} projections.
     *
     * <p>Fail-closed: any defect — a construct outside the serializer's
     * checked set, a broken occurrence record, an unresolvable nested
     * plan, a reentrant provider demand — is a deterministic E6005
     * error at the construct range and the result carries no classes;
     * no raw exception escapes and no placeholder digest is ever
     * produced.</p>
     *
     * @param modules        module source path &rarr; the read-only
     *                       per-module facts
     * @param plannedClasses module source path &rarr; the planned
     *                       classes with their provisional occurrence
     *                       data (the planner output, in planning
     *                       order)
     * @return the diagnostics, the serialized classes, and the
     *         computed provider digests
     */
    public static Result serialize(
            Map<String, DefaultSerializerModuleInput> modules,
            Map<String, List<PlannedDefaultClass>> plannedClasses) {
        Objects.requireNonNull(modules, "modules");
        Objects.requireNonNull(plannedClasses, "plannedClasses");
        return new Serializer(modules, plannedClasses, List.of()).run();
    }

    /**
     * The graph epic's (ISSUE-0543) demand overload: serializes every
     * planned class exactly like {@link #serialize(Map, Map)} and then
     * additionally demands the provider digest of every given
     * provisional occurrence (the ordinary runtime-use occurrences of
     * an acyclic compilation, which the planned-class flow alone never
     * demands), so {@link Result#providerDigests()} covers both the
     * planner's default edges and the ordinary edges the graph merges
     * with them. The additional demands never change the serialized
     * classes or the canonical contents — they only extend the
     * demanded-digest projection. Demand failure (a broken occurrence,
     * an unresolvable provider, a reentrant demand) fails closed with
     * E6005 and publishes nothing, exactly like the main flow.
     *
     * <p>The production pipeline invokes this overload only after the
     * graph's digest-free SCC pass succeeded (a runtime SCC fails the
     * compilation with E2005 before any digest demand), so digest
     * equations stay well-founded (D9).</p>
     *
     * @param modules                 module source path &rarr; the
     *                                read-only per-module facts
     * @param plannedClasses          module source path &rarr; the
     *                                planned classes (the planner
     *                                output, in planning order)
     * @param additionalDigestDemands the ordinary runtime-use
     *                                occurrences whose provider
     *                                digests to demand additionally
     *                                (possibly empty)
     * @return the diagnostics, the serialized classes, and the
     *         computed provider digests (covering the additional
     *         demands)
     */
    public static Result serialize(
            Map<String, DefaultSerializerModuleInput> modules,
            Map<String, List<PlannedDefaultClass>> plannedClasses,
            List<DefaultResourceOccurrence> additionalDigestDemands) {
        Objects.requireNonNull(modules, "modules");
        Objects.requireNonNull(plannedClasses, "plannedClasses");
        Objects.requireNonNull(additionalDigestDemands,
            "additionalDigestDemands");
        return new Serializer(modules, plannedClasses,
            additionalDigestDemands).run();
    }

    // =========================================================================
    // Internal implementation
    // =========================================================================

    /** The provider kinds digest demand distinguishes (D5). */
    private enum ProviderKind { FUNCTION, CLASS }

    /**
     * One imported-resource reference site of an IR walk: the resource
     * identity, the reference kind, and the consuming construct's
     * complete scalar range.
     */
    private record Site(SemanticResourceIdentity identity,
                        RuntimeResourceReference.Kind kind,
                        DiagnosticRange range) {
    }

    private static final class Serializer {

        private final Map<String, DefaultSerializerModuleInput> modules =
            new LinkedHashMap<>();
        private final Map<String, List<PlannedDefaultClass>> plannedClasses =
            new LinkedHashMap<>();
        private final Map<String, DefaultSerializerModuleInput> moduleByUri =
            new LinkedHashMap<>();

        private final List<CompilerDiagnostic> diagnostics =
            new ArrayList<>();
        private final Map<String, List<SerializedDefaultClass>> serialized =
            new LinkedHashMap<>();
        private final Map<SemanticResourceIdentity, String> providerDigests =
            new LinkedHashMap<>();
        /** The computed provider canonical contents, keyed by resource
         * identity. */
        private final Map<SemanticResourceIdentity, String>
            providerContents = new LinkedHashMap<>();

        /** The demand-driven digest memo, keyed by provider: the
         * computed digest plus the canonical provider content it
         * derives from, so the memo fast-path republishes both the
         * digest and the content for a demanded provider identity
         * (the {@code providerDigests} and {@code providerContents}
         * projections always agree for a demanded provider). */
        private final Map<DigestKey, DigestMemo> digestMemo =
            new LinkedHashMap<>();
        /** The already-serialized class plans, keyed by the exact
         * class declaration (name plus its complete scalar range). */
        private final Map<DigestKey, SerializedDefaultClass> classMemo =
            new LinkedHashMap<>();
        /** The reentrant-demand guard: providers whose digest is being
         * derived right now. */
        private final Set<DigestKey> inProgress = new LinkedHashSet<>();
        /** Lazily rebuilt declaration-scope name resolvers. */
        private final Map<String, NameResolver> declarationResolvers =
            new LinkedHashMap<>();
        /** Lazily rebuilt declaration-module root scopes (the
         * declaration analyzer's resolution surface). */
        private final Map<String, SymbolTable> declarationRoots =
            new LinkedHashMap<>();
        /** The scopes this serializer created synthetically (the
         * pass-1 resolver never walks class-default subexpressions, so
         * default-position bodies have no recorded scopes): local
         * declarations are defined into exactly these scopes while the
         * statements are walked. */
        private final Set<SymbolTable> syntheticScopes =
            new HashSet<>();

        private boolean failed = false;

        /**
         * One provider digest-memo key: the module, the declared name,
         * the provider kind, and — for class providers — the exact
         * class declaration's complete scalar range. Class plans are
         * keyed by declaration, never by declared name alone: a module
         * may legally declare same-named classes in distinct scopes
         * (the checker rejects duplicates only at module level), and a
         * name-only key silently collapses the second class's plan
         * serialization into the first's, corrupting its canonical
         * content and planDigest with no diagnostic (D6/D8 identity
         * and the fail-closed contract). Function providers keep a
         * null range: imported function references always resolve to
         * the provider module's top-level exports, where declared
         * names are unique.
         */
        private record DigestKey(String moduleSourcePath,
                                 String declaredName, ProviderKind kind,
                                 DiagnosticRange declarationRange) {
        }

        /** One memoized provider digest derivation: the digest and
         * the canonical provider content it derives from (the content
         * is republished verbatim on the memo fast-path). */
        private record DigestMemo(String digest, String content) {
        }

        /** The additional digest demands (the graph epic's ordinary
         * runtime-use occurrences), demanded after the main flow. */
        private final List<DefaultResourceOccurrence> additionalDemands;

        Serializer(Map<String, DefaultSerializerModuleInput> modules,
                   Map<String, List<PlannedDefaultClass>> plannedClasses,
                   List<DefaultResourceOccurrence> additionalDemands) {
            this.modules.putAll(modules);
            this.plannedClasses.putAll(plannedClasses);
            this.additionalDemands = List.copyOf(additionalDemands);
            for (DefaultSerializerModuleInput input : modules.values()) {
                moduleByUri.put(input.location().semanticModuleIdentity()
                    .canonicalResolvedSourceUri(), input);
            }
        }

        Result run() {
            for (Map.Entry<String, List<PlannedDefaultClass>> entry
                    : plannedClasses.entrySet()) {
                if (failed) {
                    break;
                }
                String sourcePath = entry.getKey();
                DefaultSerializerModuleInput input = modules.get(sourcePath);
                if (input == null) {
                    fail("no serializer module input for planned module '"
                        + sourcePath + "'",
                        DiagnosticRange.synthetic(sourcePath));
                    break;
                }
                List<SerializedDefaultClass> classes = new ArrayList<>();
                for (PlannedDefaultClass planned : entry.getValue()) {
                    if (failed) {
                        break;
                    }
                    classes.add(serializedClassFor(sourcePath, planned));
                }
                if (!failed) {
                    serialized.put(sourcePath, List.copyOf(classes));
                }
            }
            if (failed) {
                return new Result(List.copyOf(diagnostics), Map.of(),
                    Map.of(), Map.of());
            }
            // The graph epic's additional digest demands (ISSUE-0543):
            // every ordinary runtime-use occurrence demands its
            // provider digest after the planned-class flow completed,
            // so the providerDigests projection covers both edge sets.
            // Demand failure fails closed with E6005 and publishes
            // nothing — the same fail-closed contract as the main flow.
            for (DefaultResourceOccurrence occurrence
                    : additionalDemands) {
                if (failed) {
                    break;
                }
                digestFor(occurrence.semanticResourceIdentity(),
                    providerKindOf(occurrence.kind()));
            }
            if (failed) {
                return new Result(List.copyOf(diagnostics), Map.of(),
                    Map.of(), Map.of());
            }
            return new Result(List.copyOf(diagnostics), serialized,
                providerDigests, providerContents);
        }

        // =================================================================
        // Class serialization
        // =================================================================

        /**
         * The demand-driven class-plan serialization with the
         * reentrancy guard: serializes the class if needed and
         * memoizes its plan digest under its class key.
         */
        private SerializedDefaultClass serializedClassFor(String sourcePath,
                PlannedDefaultClass planned) {
            CompilerClassDefaultPlan plan = planned.plan();
            ClassDeclaration declaration = planned.declaration();
            DigestKey key = new DigestKey(sourcePath,
                declaration.name(), ProviderKind.CLASS,
                declaration.span().range());
            SerializedDefaultClass existing = classMemo.get(key);
            if (existing != null) {
                return existing;
            }
            if (inProgress.contains(key)) {
                failReentrant(key);
                return null;
            }
            inProgress.add(key);
            try {
                SerializedDefaultClass result = serializeClass(sourcePath,
                    planned);
                if (result != null) {
                    classMemo.put(key, result);
                    digestMemo.put(key, new DigestMemo(
                        result.planDigest(),
                        result.canonicalPlanContent()));
                }
                return result;
            } finally {
                inProgress.remove(key);
            }
        }

        /**
         * Serializes one planned class: completes every entry default,
         * validates the provisional occurrence data, and produces the
         * three projections.
         */
        private SerializedDefaultClass serializeClass(String sourcePath,
                PlannedDefaultClass planned) {
            CompilerClassDefaultPlan plan = planned.plan();
            DefaultSerializerModuleInput input = modules.get(sourcePath);
            SymbolTable classScope = classDeclarationScope(input,
                planned.declaration());
            if (classScope == null) {
                return null;
            }
            List<CompilerClassDefaultEntry> completedEntries =
                new ArrayList<>();
            List<Site> classSites = new ArrayList<>();
            Set<SemanticResourceIdentity> classSeen = new LinkedHashSet<>();
            Set<SemanticResourceIdentity> occurrenceIdentities =
                occurrenceIdentitiesOf(planned.occurrences());

            for (CompilerClassDefaultEntry entry : plan.orderedFields()) {
                if (failed) {
                    return null;
                }
                if (entry.defaultExpression() == null) {
                    completedEntries.add(entry);
                    continue;
                }
                CompletedDefault completed = serializeDefault(input,
                    plan.classIdentity().className(), entry,
                    planned.occurrences(), occurrenceIdentities,
                    classScope);
                if (completed == null) {
                    return null;
                }
                completedEntries.add(completed.entry());
                for (Site site : completed.sites()) {
                    if (classSeen.add(site.identity())) {
                        classSites.add(site);
                    }
                }
            }
            if (failed) {
                return null;
            }
            validateClassOccurrences(planned, classSites);
            if (failed) {
                return null;
            }

            CompilerClassDefaultPlan completedPlan =
                new CompilerClassDefaultPlan(plan.classIdentity(),
                    plan.declaringSemanticModuleIdentity(),
                    completedEntries, Set.of());

            String classIdentityText = descriptorTextOf(input,
                plan.classIdentity());
            if (failed) {
                return null;
            }
            String moduleIdentityDigest =
                SemanticIdentityContent.moduleIdentityDigest(
                    plan.declaringSemanticModuleIdentity());

            // The entries are an ordered JSON array of per-entry
            // objects in class source order (D2 orderedFields), never a
            // name-keyed object: CanonicalJson key-sorts object
            // entries, which would lose the pinned entry order and let
            // order-only plan variants share one planDigest (D6/D8).
            List<CanonicalJson.Value> planEntries = new ArrayList<>();
            List<CanonicalJson.Value> semanticEntries =
                new ArrayList<>();
            for (CompilerClassDefaultEntry entry : completedEntries) {
                CanonicalJson.Value defaultContent = entry
                    .defaultExpression() == null
                    ? CanonicalJson.nullValue()
                    : parsedDefaultContent(entry);
                if (failed) {
                    return null;
                }
                planEntries.add(CanonicalJson.obj(
                    CanonicalJson.e("name",
                        CanonicalJson.str(entry.name())),
                    CanonicalJson.e("runtimeTypeDescriptor",
                        CanonicalJson.str(entry.runtimeTypeDescriptor())),
                    CanonicalJson.e("optional",
                        CanonicalJson.bool(entry.optional())),
                    CanonicalJson.e("canonicalDefaultContent",
                        defaultContent)));
                semanticEntries.add(CanonicalJson.obj(
                    CanonicalJson.e("name",
                        CanonicalJson.str(entry.name())),
                    CanonicalJson.e("runtimeTypeDescriptor",
                        CanonicalJson.str(entry.runtimeTypeDescriptor())),
                    CanonicalJson.e("optional",
                        CanonicalJson.bool(entry.optional())),
                    CanonicalJson.e("canonicalDefaultContent",
                        defaultContent)));
            }
            String canonicalPlanContent = CanonicalJson.serializeText(
                CanonicalJson.obj(
                    CanonicalJson.e("serializerVersion",
                        CanonicalJson.str(SERIALIZER_VERSION)),
                    CanonicalJson.e("classIdentity",
                        CanonicalJson.str(classIdentityText)),
                    CanonicalJson.e(
                        "declaringSemanticModuleIdentityDigest",
                        CanonicalJson.str(moduleIdentityDigest)),
                    CanonicalJson.e("entries",
                        CanonicalJson.arr(planEntries))));
            String planDigest =
                RuntimeResourceReference.providerContractDigestOf(
                    canonicalPlanContent);
            String semanticDefaultContents = CanonicalJson.serializeText(
                CanonicalJson.obj(
                    CanonicalJson.e("serializerVersion",
                        CanonicalJson.str(SERIALIZER_VERSION)),
                    CanonicalJson.e("classIdentity",
                        CanonicalJson.str(classIdentityText)),
                    CanonicalJson.e("entries",
                        CanonicalJson.arr(semanticEntries))));
            return new SerializedDefaultClass(completedPlan,
                canonicalPlanContent, planDigest, semanticDefaultContents);
        }

        /**
         * The stored canonical default content re-parsed into its
         * structured value (the single canonical JSON facility's exact
         * round-trip: re-serializing reproduces the stored text
         * byte-for-byte).
         */
        private CanonicalJson.Value parsedDefaultContent(
                CompilerClassDefaultEntry entry) {
            try {
                return CanonicalJson.parse(entry.defaultExpression()
                    .canonicalSemanticContent());
            } catch (RuntimeException defect) {
                fail("the canonical default content of field '"
                    + entry.name() + "' cannot be re-parsed: "
                    + defect.getMessage(), entry.defaultExpression()
                        .sourceRange());
                return null;
            }
        }

        /**
         * The E4 canonical descriptor text of a canonical class
         * identity (the plan's public identity).
         */
        private String descriptorTextOf(DefaultSerializerModuleInput input,
                CanonicalClassIdentity classIdentity) {
            try {
                return input.descriptors().encode(Types.classType(
                    classIdentity.className(), classIdentity));
            } catch (IllegalStateException defect) {
                fail("class '" + classIdentity.className()
                    + "' has no canonical descriptor text ("
                    + defect.getMessage() + ")",
                    DiagnosticRange.synthetic(input.sourcePath()));
                return null;
            }
        }

        // =================================================================
        // Default expression serialization
        // =================================================================

        private record CompletedDefault(CompilerClassDefaultEntry entry,
                                        List<Site> sites) {
        }

        /**
         * Serializes one default expression: collects and validates the
         * reference sites against the class occurrences, produces the
         * canonical content and semantic digest, and completes the
         * ordered digest-bearing runtime resources.
         */
        private CompletedDefault serializeDefault(
                DefaultSerializerModuleInput input, String className,
                CompilerClassDefaultEntry entry,
                List<DefaultResourceOccurrence> classOccurrences,
                Set<SemanticResourceIdentity> occurrenceIdentities,
                SymbolTable classScope) {
            ResolvedDefaultExpression expr = entry.defaultExpression();
            if (!(expr.semanticIr() instanceof DefaultIrNode root)) {
                fail("the default of field '" + entry.name()
                    + "' of class '" + className
                    + "' has no typed evaluator IR root",
                    expr.sourceRange());
                return null;
            }
            List<Site> sites = new ArrayList<>();
            Set<SemanticResourceIdentity> seen = new LinkedHashSet<>();
            collectSites(root, classOccurrences, occurrenceIdentities,
                false, sites, seen);
            if (failed) {
                return null;
            }
            Set<Site> siteSet = new LinkedHashSet<>(sites);
            String content = serializeDefaultRoot(root, input, siteSet,
                occurrenceIdentities, classScope);
            if (failed) {
                return null;
            }
            String digest =
                RuntimeResourceReference.providerContractDigestOf(content);
            Set<RuntimeResourceReference> resources =
                new LinkedHashSet<>();
            for (Site site : sites) {
                String providerDigest = digestFor(site.identity(),
                    providerKindOf(site.kind()));
                if (providerDigest == null) {
                    return null;
                }
                resources.add(new RuntimeResourceReference(site.kind(),
                    site.identity(), providerDigest, site.range()));
            }
            ResolvedDefaultExpression completed =
                expr.withCanonicalSemantics(content, digest, resources);
            return new CompletedDefault(
                new CompilerClassDefaultEntry(entry.name(),
                    entry.resolvedFieldType(),
                    entry.runtimeTypeDescriptor(), entry.optional(),
                    completed),
                sites);
        }

        /**
         * Walks the IR in pre-order (the consuming construct before
         * its children — the planner's occurrence order) and collects
         * the imported-resource reference sites: a candidate node whose
         * {@code (identity, kind, range)} matches a class occurrence is
         * the site; a later node of an already-seen identity is the
         * planner's deduplicated repeat; a class-literal target whose
         * identity has no occurrence record is a host-declared imported
         * class (no plan exists — identity-only target); any other
         * unmatched imported target is broken occurrence data (fail
         * closed).
         */
        private void collectSites(DefaultIrNode node,
                List<DefaultResourceOccurrence> classOccurrences,
                Set<SemanticResourceIdentity> occurrenceIdentities,
                boolean calleeShadow, List<Site> sites,
                Set<SemanticResourceIdentity> seen) {
            DefaultIrNode.Target target = node.target();
            if (target != null
                    && target.kind()
                        == DefaultIrNode.TargetKind.IMPORTED_RESOURCE
                    && !calleeShadow) {
                RuntimeResourceReference.Kind kind = occurrenceKindOf(node);
                if (kind == null) {
                    fail("IR node kind " + node.kind()
                        + " with an imported resource target has no"
                        + " reference kind (the checked construct set"
                        + " records imported targets only on calls,"
                        + " member accesses, and contextual class"
                        + " literals)", node.span());
                    return;
                }
                SemanticResourceIdentity identity =
                    target.resourceIdentity();
                if (identity == null) {
                    fail("IR node with an imported resource target"
                        + " carries no resource identity", node.span());
                    return;
                }
                if (matchingOccurrence(classOccurrences, identity, kind,
                        node.span()) != null) {
                    if (seen.add(identity)) {
                        sites.add(new Site(identity, kind, node.span()));
                    }
                } else if (occurrenceIdentities.contains(identity)) {
                    // The planner's deduplicated repeat: the occurrence
                    // keeps the first reference range (D4).
                } else if (kind == RuntimeResourceReference.Kind
                        .IMPORTED_CLASS_DEFAULT_PLAN
                        && node.kind()
                            == DefaultIrNode.NodeKind.OBJECT_LITERAL) {
                    // A contextual class literal typed as a
                    // host-declared imported class: no plan exists
                    // (the host supplies <C>_defaults at load), so no
                    // occurrence and no provider digest — the target
                    // serializes identity-only (D2/D6).
                } else {
                    fail("broken occurrence data: the imported"
                        + " resource target '"
                        + identity.lexicalDeclarationIdentity()
                            .declaredName()
                        + "' has no occurrence record", node.span());
                    return;
                }
            }
            for (DefaultIrNode child : node.children()) {
                boolean shadow = false;
                if (node.kind() == DefaultIrNode.NodeKind.CALL
                        && node.target() != null
                        && node.target().kind()
                            == DefaultIrNode.TargetKind.IMPORTED_RESOURCE
                        && !node.children().isEmpty()
                        && node.children().get(0) == child) {
                    // The callee member access under an
                    // imported-target call is the occurrence shadow:
                    // the call-site range is the reference range.
                    shadow = true;
                }
                collectSites(child, classOccurrences,
                    occurrenceIdentities, shadow, sites, seen);
            }
        }

        /**
         * The class-level occurrence validation: the provisional
         * occurrence list must equal the deduplicated reference-site
         * sequence derived from the IR — every occurrence matches a
         * candidate node by {@code (identity, kind, range)} exactly,
         * in the planner's first-occurrence order, with no extra or
         * missing record.
         */
        private void validateClassOccurrences(PlannedDefaultClass planned,
                List<Site> classSites) {
            List<DefaultResourceOccurrence> occurrences =
                planned.occurrences();
            if (occurrences.size() != classSites.size()) {
                fail("broken occurrence data: the plan of class '"
                    + planned.plan().classIdentity().className()
                    + "' carries " + occurrences.size()
                    + " occurrence records but the typed evaluator IR"
                    + " derives " + classSites.size()
                    + " reference sites", occurrences.isEmpty()
                        ? DiagnosticRange.synthetic("occurrence")
                        : occurrences.get(0).sourceRange());
                return;
            }
            for (int i = 0; i < occurrences.size(); i++) {
                DefaultResourceOccurrence occurrence = occurrences.get(i);
                Site site = classSites.get(i);
                if (!occurrence.semanticResourceIdentity()
                        .equals(site.identity())
                        || occurrence.kind() != site.kind()
                        || !occurrence.sourceRange().equals(site.range())) {
                    fail("broken occurrence data: occurrence " + i
                        + " of class '"
                        + planned.plan().classIdentity().className()
                        + "' is (" + occurrence.kind() + ", '"
                        + occurrence.semanticResourceIdentity()
                            .lexicalDeclarationIdentity().declaredName()
                        + "', " + rangeText(occurrence.sourceRange())
                        + ") but the typed evaluator IR derives ("
                        + site.kind() + ", '"
                        + site.identity().lexicalDeclarationIdentity()
                            .declaredName() + "', "
                        + rangeText(site.range()) + ")",
                        occurrence.sourceRange());
                    return;
                }
            }
        }

        /**
         * Serializes a default root node under the class's recorded
         * declaration scope — the declaring lexical context the
         * planner checked the default in (D3), never the module root
         * scope — so body-local annotations resolve exactly as the
         * checker resolved them. The root range is always
         * behavior-affecting (the E3001 anchor).
         */
        private String serializeDefaultRoot(DefaultIrNode root,
                DefaultSerializerModuleInput input, Set<Site> siteSet,
                Set<SemanticResourceIdentity> occurrenceIdentities,
                SymbolTable declarationScope) {
            SymbolTable scope = declarationScope != null
                ? declarationScope : new SymbolTable();
            CanonicalNode node = serializeNode(root, input, siteSet,
                occurrenceIdentities, true, scope);
            if (failed) {
                return null;
            }
            return new CanonicalDefaultSemantics(SERIALIZER_VERSION,
                node).canonicalText();
        }

        // =================================================================
        // Canonical node and statement production
        // =================================================================

        /**
         * Produces the canonical node of one IR node.
         *
         * @param isRoot    true exactly for the default expression root
         *                  (its range is the E3001 anchor)
         * @param inheritedScope the lexical scope for statement-side
         *                  resolution, or null in expression-only
         *                  positions
         */
        private CanonicalNode serializeNode(DefaultIrNode node,
                DefaultSerializerModuleInput input, Set<Site> siteSet,
                Set<SemanticResourceIdentity> occurrenceIdentities,
                boolean isRoot, SymbolTable inheritedScope) {
            if (failed) {
                return null;
            }
            String kind = node.kind().name();
            String operatorKind = node.operatorKind();
            String resultDescriptor = null;
            if (node.resultType() != null) {
                resultDescriptor = descriptorOf(input, node.resultType(),
                    node.span());
                if (failed) {
                    return null;
                }
            }
            List<String> contexts = new ArrayList<>();
            for (Type context : node.contextualTypes()) {
                contexts.add(descriptorOf(input, context, node.span()));
                if (failed) {
                    return null;
                }
            }
            List<CanonicalChild> children = new ArrayList<>();
            CanonicalJson.Value literalValue = null;
            switch (node.kind()) {
                case LITERAL -> {
                    literalValue = literalJson(node);
                    if (failed) {
                        return null;
                    }
                }
                case ARRAY_LITERAL, ASSIGNMENT, AWAIT, BINARY, CALL,
                     HAS, IDENTIFIER, INDEX, MEMBER_ACCESS,
                     OBJECT_LITERAL, TEMPLATE_LITERAL, UNARY -> {
                    for (DefaultIrNode child : node.children()) {
                        children.add(serializeNode(child, input, siteSet,
                            occurrenceIdentities, false, inheritedScope));
                        if (failed) {
                            return null;
                        }
                    }
                }
                case FUNCTION_EXPRESSION -> {
                    SymbolTable bodyScope = functionBodyScope(input,
                        node, inheritedScope);
                    if (failed) {
                        return null;
                    }
                    for (DefaultIrNode child : node.children()) {
                        children.add(serializeStatement(child, input,
                            siteSet, occurrenceIdentities, bodyScope));
                        if (failed) {
                            return null;
                        }
                    }
                }
                default -> {
                    // Statements never reach the node grammar (the
                    // serializer is total over the closed sets and
                    // dispatches statement kinds to the statement
                    // grammar), so this arm is unreachable; fail
                    // closed nevertheless.
                    fail("unsupported IR node kind " + node.kind()
                        + " in the canonical expression grammar",
                        node.span());
                    return null;
                }
            }
            CanonicalNode.Target target = serializeTarget(node, input,
                siteSet, occurrenceIdentities);
            if (failed) {
                return null;
            }
            DiagnosticRange sourceRange = null;
            if (isRoot) {
                sourceRange = node.span();
            } else if (node.target() != null
                    && node.target().kind()
                        == DefaultIrNode.TargetKind.IMPORTED_RESOURCE
                    && node.target().resourceIdentity() != null) {
                RuntimeResourceReference.Kind referenceKind =
                    occurrenceKindOf(node);
                if (referenceKind != null
                        && siteSet.contains(new Site(
                            node.target().resourceIdentity(),
                            referenceKind, node.span()))) {
                    sourceRange = node.span();
                }
            }
            return new CanonicalNode(kind, operatorKind, resultDescriptor,
                contexts, children, literalValue, target, sourceRange);
        }

        /**
         * Produces the canonical statement of one IR statement node,
         * deriving the fixed condition/value/binding/type/nested roles
         * from the recorded statement AST (the serializer's recovery
         * surface, {@link DefaultIrNode#statement()}) and threading the
         * lexical scope exactly like the recorder.
         */
        private CanonicalStatement serializeStatement(DefaultIrNode node,
                DefaultSerializerModuleInput input, Set<Site> siteSet,
                Set<SemanticResourceIdentity> occurrenceIdentities,
                SymbolTable inheritedScope) {
            if (failed) {
                return null;
            }
            StatementNode statementAst = node.statement();
            if (statementAst == null) {
                fail("statement IR node " + node.kind()
                    + " carries no statement AST (broken IR)",
                    node.span());
                return null;
            }
            SymbolTable effectiveScope = statementScope(input,
                statementAst, inheritedScope);
            String kind = node.kind().name();
            CanonicalNode condition = null;
            CanonicalNode value = null;
            String bindingMarker = null;
            String typeDescriptor = null;
            CanonicalNested nested = null;
            List<CanonicalChild> children = new ArrayList<>();

            switch (node.kind()) {
                case BLOCK -> {
                    for (DefaultIrNode child : node.children()) {
                        children.add(serializeStatement(child, input,
                            siteSet, occurrenceIdentities,
                            effectiveScope));
                        if (failed) {
                            return null;
                        }
                    }
                }
                case VARIABLE_DECLARATION -> {
                    bindingMarker = node.declaredName();
                    if (!(statementAst instanceof VariableDeclaration
                            vd)) {
                        fail("VARIABLE_DECLARATION IR node carries no"
                            + " variable declaration AST (broken IR)",
                            node.span());
                        return null;
                    }
                    Type declared = null;
                    if (vd.typeAnnotation().isPresent()) {
                        declared = resolveTypeNode(input,
                            vd.typeAnnotation().get(), effectiveScope,
                            node.span());
                        if (failed) {
                            return null;
                        }
                        typeDescriptor = descriptorOf(input, declared,
                            node.span());
                        if (failed) {
                            return null;
                        }
                    }
                    // Mirror NameResolver.walkVarDecl: the binding is
                    // defined in the walked scope before the
                    // initializer walks, so shadowing and later
                    // annotations resolve exactly as the checker
                    // resolved them.
                    defineIn(effectiveScope, vd.name(),
                        new Symbol.VariableSymbol(vd.name(), declared,
                            false), node.span());
                    if (failed) {
                        return null;
                    }
                    if (!node.children().isEmpty()) {
                        children.add(serializeNode(node.children().get(0),
                            input, siteSet, occurrenceIdentities, false,
                            effectiveScope));
                        if (failed) {
                            return null;
                        }
                    }
                }
                case EXPRESSION_STATEMENT -> {
                    if (node.children().size() != 1) {
                        fail("EXPRESSION_STATEMENT IR node carries "
                            + node.children().size() + " children",
                            node.span());
                        return null;
                    }
                    children.add(serializeNode(node.children().get(0),
                        input, siteSet, occurrenceIdentities, false,
                        effectiveScope));
                    if (failed) {
                        return null;
                    }
                }
                case RETURN -> {
                    if (!node.children().isEmpty()) {
                        value = serializeNode(node.children().get(0),
                            input, siteSet, occurrenceIdentities, false,
                            effectiveScope);
                        if (failed) {
                            return null;
                        }
                    }
                }
                case THROW -> {
                    if (node.children().size() != 1) {
                        fail("THROW IR node carries " + node.children()
                            .size() + " children", node.span());
                        return null;
                    }
                    value = serializeNode(node.children().get(0), input,
                        siteSet, occurrenceIdentities, false,
                        effectiveScope);
                    if (failed) {
                        return null;
                    }
                }
                case IF -> {
                    if (node.children().size() < 2
                            || node.children().size() > 3) {
                        fail("IF IR node carries " + node.children()
                            .size() + " children", node.span());
                        return null;
                    }
                    condition = serializeNode(node.children().get(0),
                        input, siteSet, occurrenceIdentities, false,
                        effectiveScope);
                    if (failed) {
                        return null;
                    }
                    children.add(serializeStatement(node.children().get(1),
                        input, siteSet, occurrenceIdentities,
                        effectiveScope));
                    if (failed) {
                        return null;
                    }
                    if (node.children().size() == 3) {
                        children.add(serializeStatement(
                            node.children().get(2), input, siteSet,
                            occurrenceIdentities, effectiveScope));
                        if (failed) {
                            return null;
                        }
                    }
                }
                case WHILE -> {
                    if (node.children().size() != 2) {
                        fail("WHILE IR node carries " + node.children()
                            .size() + " children", node.span());
                        return null;
                    }
                    condition = serializeNode(node.children().get(0),
                        input, siteSet, occurrenceIdentities, false,
                        effectiveScope);
                    if (failed) {
                        return null;
                    }
                    children.add(serializeStatement(node.children().get(1),
                        input, siteSet, occurrenceIdentities,
                        effectiveScope));
                    if (failed) {
                        return null;
                    }
                }
                case FOR -> {
                    if (!(statementAst instanceof ForStatement fs)) {
                        fail("FOR IR node carries no for-statement AST"
                            + " (broken IR)", node.span());
                        return null;
                    }
                    // The recorder's fixed role order:
                    // [init?, condition?, update?, body]; the AST
                    // presence flags select the exact roles.
                    int index = 0;
                    if (fs.init().isPresent()) {
                        ForInit init = fs.init().get();
                        if (index >= node.children().size()) {
                            fail("FOR IR node is missing its init"
                                + " child", node.span());
                            return null;
                        }
                        DefaultIrNode initNode =
                            node.children().get(index++);
                        if (init instanceof ForInit.VarDecl) {
                            children.add(serializeStatement(initNode,
                                input, siteSet, occurrenceIdentities,
                                effectiveScope));
                        } else if (init instanceof ForInit.AssignExpr) {
                            children.add(serializeNode(initNode, input,
                                siteSet, occurrenceIdentities, false,
                                effectiveScope));
                        } else {
                            fail("FOR init has an unsupported shape",
                                node.span());
                            return null;
                        }
                        if (failed) {
                            return null;
                        }
                    }
                    if (fs.condition().isPresent()) {
                        if (index >= node.children().size()) {
                            fail("FOR IR node is missing its condition"
                                + " child", node.span());
                            return null;
                        }
                        condition = serializeNode(
                            node.children().get(index++), input, siteSet,
                            occurrenceIdentities, false, effectiveScope);
                        if (failed) {
                            return null;
                        }
                    }
                    if (fs.update().isPresent()) {
                        if (index >= node.children().size()) {
                            fail("FOR IR node is missing its update"
                                + " child", node.span());
                            return null;
                        }
                        children.add(serializeNode(
                            node.children().get(index++), input, siteSet,
                            occurrenceIdentities, false, effectiveScope));
                        if (failed) {
                            return null;
                        }
                    }
                    if (index + 1 != node.children().size()) {
                        fail("FOR IR node has an inconsistent child"
                            + " shape (" + node.children().size()
                            + " children)", node.span());
                        return null;
                    }
                    children.add(serializeStatement(
                        node.children().get(index), input, siteSet,
                        occurrenceIdentities, effectiveScope));
                    if (failed) {
                        return null;
                    }
                }
                case FOR_OF -> {
                    if (node.children().size() != 2) {
                        fail("FOR_OF IR node carries " + node.children()
                            .size() + " children", node.span());
                        return null;
                    }
                    bindingMarker = node.declaredName();
                    // The iterable walks in the enclosing scope (pass 1
                    // resolves it before entering the loop-variable
                    // scope); the body walks under the loop-variable
                    // scope.
                    children.add(serializeNode(node.children().get(0),
                        input, siteSet, occurrenceIdentities, false,
                        effectiveScope));
                    if (failed) {
                        return null;
                    }
                    SymbolTable loopScope = forOfScope(input, node,
                        effectiveScope);
                    if (failed) {
                        return null;
                    }
                    children.add(serializeStatement(node.children().get(1),
                        input, siteSet, occurrenceIdentities, loopScope));
                    if (failed) {
                        return null;
                    }
                }
                case TRY -> {
                    if (node.children().size() != 2) {
                        fail("TRY IR node carries " + node.children()
                            .size() + " children", node.span());
                        return null;
                    }
                    // The try block walks under the enclosing scope;
                    // the catch block under the catch scope (recorded
                    // by pass 1, or the synthetic child carrying the
                    // catch variable) — sibling scopes, exactly as
                    // NameResolver.walkTry builds them.
                    children.add(serializeStatement(node.children().get(0),
                        input, siteSet, occurrenceIdentities,
                        effectiveScope));
                    if (failed) {
                        return null;
                    }
                    SymbolTable catchScope = tryCatchScope(input, node,
                        effectiveScope);
                    if (failed) {
                        return null;
                    }
                    children.add(serializeStatement(node.children().get(1),
                        input, siteSet, occurrenceIdentities, catchScope));
                    if (failed) {
                        return null;
                    }
                }
                case DELETE -> {
                    if (node.children().size() != 1) {
                        fail("DELETE IR node carries " + node.children()
                            .size() + " children", node.span());
                        return null;
                    }
                    children.add(serializeNode(node.children().get(0),
                        input, siteSet, occurrenceIdentities, false,
                        effectiveScope));
                    if (failed) {
                        return null;
                    }
                }
                case BREAK, CONTINUE -> {
                    // No children, no roles.
                }
                case FUNCTION_DECLARATION -> {
                    bindingMarker = node.declaredName();
                    if (!(statementAst instanceof FunctionDeclaration
                            fd)) {
                        fail("FUNCTION_DECLARATION IR node carries no"
                            + " function declaration AST (broken IR)",
                            node.span());
                        return null;
                    }
                    // Mirror NameResolver.walkFuncDecl: the signature
                    // resolves in the enclosing scope (never the
                    // parameter scope), the declaration is defined in
                    // the enclosing scope, and the body walks under
                    // the parameter scope (recorded by pass 1, or the
                    // synthetic child carrying the parameters).
                    Type.Func funcType = functionTypeOf(fd,
                        inheritedScope);
                    if (funcType == null) {
                        funcType = resolveFunctionType(input, fd,
                            inheritedScope, node.span());
                    }
                    if (funcType == null) {
                        return null;
                    }
                    defineIn(inheritedScope, fd.name(),
                        new Symbol.FunctionSymbol(fd.name(), funcType),
                        node.span());
                    if (failed) {
                        return null;
                    }
                    SymbolTable bodyScope = functionParameterScope(
                        input, fd, inheritedScope, node.span());
                    if (failed) {
                        return null;
                    }
                    CanonicalFunctionSemantics semantics =
                        nestedFunctionSemantics(node, input,
                            funcType, bodyScope, siteSet,
                            occurrenceIdentities);
                    if (failed) {
                        return null;
                    }
                    nested = new CanonicalNested.FunctionSemantics(
                        semantics);
                    if (node.children().size() == 1) {
                        children.add(serializeStatement(
                            node.children().get(0), input, siteSet,
                            occurrenceIdentities, bodyScope));
                        if (failed) {
                            return null;
                        }
                    }
                }
                case CLASS_DECLARATION -> {
                    bindingMarker = node.declaredName();
                    if (!(statementAst instanceof ClassDeclaration
                            nestedDeclaration)) {
                        fail("CLASS_DECLARATION IR node carries no"
                            + " class declaration AST (broken IR)",
                            node.span());
                        return null;
                    }
                    if (!node.declaredName().equals(
                            nestedDeclaration.name())) {
                        fail("CLASS_DECLARATION IR node declares '"
                            + node.declaredName()
                            + "' but carries the declaration of '"
                            + nestedDeclaration.name()
                            + "' (broken IR)", node.span());
                        return null;
                    }
                    // Mirror NameResolver.walkClassDecl: the nested
                    // class binding is defined in the walked scope, so
                    // later body annotations resolve it exactly as
                    // pass 1 would.
                    Symbol classSymbol = classSymbolFor(input,
                        node.declaredName(), node.span());
                    if (failed) {
                        return null;
                    }
                    defineIn(effectiveScope, node.declaredName(),
                        classSymbol, node.span());
                    if (failed) {
                        return null;
                    }
                    // The inline plan content resolves by the exact
                    // nested declaration (name plus its complete
                    // scalar range), never by declared name alone:
                    // same-named classes in distinct scopes each inline
                    // their own plan, and an unresolvable declaration
                    // fails closed.
                    String planContent = nestedPlanContent(input,
                        nestedDeclaration);
                    if (failed) {
                        return null;
                    }
                    nested = new CanonicalNested.PlanContent(planContent);
                }
                default -> {
                    fail("unsupported IR statement kind " + node.kind()
                        + " in the canonical statement grammar",
                        node.span());
                    return null;
                }
            }
            // Reference sites are expression nodes; a statement itself
            // never carries a source range (D9).
            return new CanonicalStatement(kind, condition, value,
                bindingMarker, typeDescriptor, nested, children, null);
        }

        /**
         * The nested function semantics of a FUNCTION_DECLARATION
         * statement: the resolved signature (from the enclosing
         * scope's function symbol or the declared annotations) with the
         * body statements serialized through the statement grammar
         * under the function's parameter scope.
         */
        private CanonicalFunctionSemantics nestedFunctionSemantics(
                DefaultIrNode node, DefaultSerializerModuleInput input,
                Type.Func funcType, SymbolTable bodyScope, Set<Site>
                    siteSet,
                Set<SemanticResourceIdentity> occurrenceIdentities) {
            List<String> parameters = new ArrayList<>();
            for (Type parameter : funcType.paramTypes()) {
                parameters.add(descriptorOf(input, parameter,
                    node.span()));
                if (failed) {
                    return null;
                }
            }
            String returnDescriptor = descriptorOf(input,
                funcType.returnType(), node.span());
            if (failed) {
                return null;
            }
            List<CanonicalStatement> body = new ArrayList<>();
            if (node.children().size() == 1
                    && node.children().get(0).kind()
                        == DefaultIrNode.NodeKind.BLOCK) {
                CanonicalStatement blockStatement = serializeStatement(
                    node.children().get(0), input, siteSet,
                    occurrenceIdentities, bodyScope);
                if (failed) {
                    return null;
                }
                for (CanonicalChild child : blockStatement.children()) {
                    if (!(child instanceof CanonicalStatement stmt)) {
                        fail("a function body block child is not a"
                            + " statement (broken IR)", node.span());
                        return null;
                    }
                    body.add(stmt);
                }
            }
            return new CanonicalFunctionSemantics(SERIALIZER_VERSION,
                funcType.isAsync(), parameters, returnDescriptor, body);
        }

        /**
         * The nested class's full canonical plan content (D6
         * projection) — demand-driven through the class plan, keyed
         * by the exact nested declaration (name plus its complete
         * scalar range), never by declared name alone: same-named
         * classes in distinct scopes each inline their own plan, and
         * an unresolvable declaration fails closed instead of
         * silently reusing another class's serialization.
         */
        private String nestedPlanContent(DefaultSerializerModuleInput input,
                ClassDeclaration nestedDeclaration) {
            List<PlannedDefaultClass> modulePlans =
                plannedClasses.get(input.sourcePath());
            if (modulePlans == null) {
                fail("the nested class '" + nestedDeclaration.name()
                    + "' of module '" + input.modulePath()
                    + "' has no planned classes",
                    nestedDeclaration.span().range());
                return null;
            }
            PlannedDefaultClass match = null;
            for (PlannedDefaultClass planned : modulePlans) {
                ClassDeclaration cd = planned.declaration();
                if (cd.name().equals(nestedDeclaration.name())
                        && cd.span().range().equals(
                            nestedDeclaration.span().range())) {
                    if (match != null) {
                        fail("the nested class '"
                            + nestedDeclaration.name() + "' at "
                            + rangeText(
                                nestedDeclaration.span().range())
                            + " matches multiple planned classes"
                            + " (broken planner input)",
                            nestedDeclaration.span().range());
                        return null;
                    }
                    match = planned;
                }
            }
            if (match == null) {
                fail("the nested class '" + nestedDeclaration.name()
                    + "' of module '" + input.modulePath()
                    + "' has no planned class record at its"
                    + " declaration range (broken planner input)",
                    nestedDeclaration.span().range());
                return null;
            }
            SerializedDefaultClass serializedPlan =
                serializedClassFor(input.sourcePath(), match);
            if (serializedPlan == null) {
                return null;
            }
            return serializedPlan.canonicalPlanContent();
        }

        /**
         * The canonical target of one IR node.
         */
        private CanonicalNode.Target serializeTarget(DefaultIrNode node,
                DefaultSerializerModuleInput input, Set<Site> siteSet,
                Set<SemanticResourceIdentity> occurrenceIdentities) {
            DefaultIrNode.Target target = node.target();
            if (target == null) {
                return null;
            }
            String kind = target.kind().name();
            String name = target.name();
            String identityDigest = null;
            String providerDigest = null;
            switch (target.kind()) {
                case LOCAL_BINDING, INTRINSIC, MODULE_ALIAS -> {
                    // Binding marker only.
                }
                case SAME_MODULE_RESOURCE -> {
                    if (target.resourceIdentity() == null) {
                        fail("same-module resource target carries no"
                            + " resource identity", node.span());
                        return null;
                    }
                    identityDigest = SemanticIdentityContent
                        .resourceIdentityDigest(target
                            .resourceIdentity());
                }
                case IMPORTED_RESOURCE -> {
                    if (target.resourceIdentity() == null) {
                        fail("imported resource target carries no"
                            + " resource identity", node.span());
                        return null;
                    }
                    identityDigest = SemanticIdentityContent
                        .resourceIdentityDigest(target
                            .resourceIdentity());
                    RuntimeResourceReference.Kind referenceKind =
                        occurrenceKindOf(node);
                    if (referenceKind
                            == RuntimeResourceReference.Kind
                                .IMPORTED_CLASS_DEFAULT_PLAN
                            && node.kind()
                                == DefaultIrNode.NodeKind.OBJECT_LITERAL
                            && !occurrenceIdentities.contains(
                                target.resourceIdentity())) {
                        // A host-declared imported class literal: no
                        // plan exists, identity-only (D2/D6).
                    } else if (referenceKind == null) {
                        fail("IR node kind " + node.kind()
                            + " with an imported resource target has no"
                            + " reference kind", node.span());
                        return null;
                    } else {
                        providerDigest = digestFor(
                            target.resourceIdentity(),
                            providerKindOf(referenceKind));
                        if (providerDigest == null) {
                            return null;
                        }
                    }
                }
            }
            return new CanonicalNode.Target(kind, name, identityDigest,
                providerDigest);
        }

        // =================================================================
        // Provider digests (D5)
        // =================================================================

        /**
         * The demand-driven provider digest with the reentrancy guard:
         * computes the provider's canonical contract content — an
         * implementation function's resolved signature plus typed body
         * semantics, a declared function wrapper's canonical declared
         * signature plus the declaration's semantic resource identity,
         * or a class's full canonical plan content — and its digest,
         * memoized by provider.
         */
        private String digestFor(SemanticResourceIdentity identity,
                ProviderKind kind) {
            DefaultSerializerModuleInput input = moduleByUri.get(identity
                .semanticModuleIdentity().canonicalResolvedSourceUri());
            if (input == null) {
                fail("no serializer module input for the provider"
                    + " module of resource '"
                    + identity.lexicalDeclarationIdentity()
                        .declaredName() + "'",
                    identity.lexicalDeclarationIdentity()
                        .sourceScalarRange());
                return null;
            }
            // Class providers are keyed by their exact declaration
            // range (the identity's complete source scalar range), so
            // a same-named class in a distinct scope never reuses
            // another class's memoized digest or content; function
            // providers stay name-keyed (imported references always
            // resolve to the module's unique top-level exports).
            DiagnosticRange declarationRange = kind == ProviderKind.CLASS
                ? identity.lexicalDeclarationIdentity()
                    .sourceScalarRange()
                : null;
            DigestKey key = new DigestKey(input.sourcePath(),
                identity.lexicalDeclarationIdentity().declaredName(),
                kind, declarationRange);
            DigestMemo memo = digestMemo.get(key);
            if (memo != null) {
                // The memo fast-path still publishes the digest and
                // the canonical content for the demanded identity
                // (the first demand of a provider serialized earlier
                // as the main flow), so providerDigests and
                // providerContents always agree for a demanded
                // provider.
                providerDigests.put(identity, memo.digest());
                if (memo.content() != null) {
                    providerContents.put(identity, memo.content());
                }
                return memo.digest();
            }
            if (inProgress.contains(key)) {
                failReentrant(key);
                return null;
            }
            inProgress.add(key);
            try {
                String digest;
                String content;
                if (kind == ProviderKind.FUNCTION) {
                    content = functionContent(input, key);
                    if (content == null) {
                        return null;
                    }
                    digest = RuntimeResourceReference
                        .providerContractDigestOf(content);
                } else {
                    SerializedDefaultClass serializedPlan =
                        classDigest(input, key);
                    if (serializedPlan == null) {
                        return null;
                    }
                    content = serializedPlan.canonicalPlanContent();
                    digest = serializedPlan.planDigest();
                }
                providerContents.put(identity, content);
                digestMemo.put(key, new DigestMemo(digest, content));
                providerDigests.put(identity, digest);
                return digest;
            } finally {
                inProgress.remove(key);
            }
        }

        /**
         * The serialized plan of a class provider (D5/D6): the
         * demand-driven class serialization whose {@code planDigest} is
         * the provider digest — resolved by the exact demanded class
         * declaration (declared name plus its complete scalar range,
         * the {@code DigestKey}'s range), never by declared name
         * alone. A demand with no matching planned declaration fails
         * closed at the demanded declaration range: same-named classes
         * in distinct scopes never silently reuse another class's
         * serialization.
         */
        private SerializedDefaultClass classDigest(
                DefaultSerializerModuleInput input, DigestKey key) {
            List<PlannedDefaultClass> modulePlans =
                plannedClasses.get(input.sourcePath());
            if (modulePlans == null) {
                fail("no planned classes for provider module '"
                    + input.modulePath() + "'",
                    DiagnosticRange.synthetic(input.sourcePath()));
                return null;
            }
            PlannedDefaultClass match = null;
            for (PlannedDefaultClass planned : modulePlans) {
                ClassDeclaration cd = planned.declaration();
                if (cd.name().equals(key.declaredName())
                        && cd.span().range().equals(
                            key.declarationRange())) {
                    if (match != null) {
                        fail("the demanded class plan '"
                            + key.declaredName() + "' at "
                            + rangeText(key.declarationRange())
                            + " matches multiple planned classes"
                            + " (broken planner input)",
                            key.declarationRange());
                        return null;
                    }
                    match = planned;
                }
            }
            if (match == null) {
                fail("no planned class '" + key.declaredName()
                    + "' of provider module '" + input.modulePath()
                    + "' at the demanded declaration range "
                    + rangeText(key.declarationRange())
                    + " (a class reference with no planned record —"
                    + " never silently reuse another class's"
                    + " serialization)",
                    key.declarationRange());
                return null;
            }
            return serializedClassFor(input.sourcePath(), match);
        }

        /**
         * The canonical provider content of a function provider: an
         * implementation function's canonical
         * {@link CanonicalFunctionSemantics} text (D9) or a declared
         * function wrapper's canonical declared signature content plus
         * the declaration's semantic resource identity (D5).
         */
        private String functionContent(DefaultSerializerModuleInput input,
                DigestKey key) {
            if (input.isDeclarationFile()) {
                return declaredFunctionDigest(input, key);
            }
            return implementationFunctionContent(input, key);
        }

        /**
         * The implementation-function provider digest: the resolved
         * signature plus the typed body semantics serialized as
         * {@link CanonicalFunctionSemantics}.
         */
        private String implementationFunctionContent(
                DefaultSerializerModuleInput input, DigestKey key) {
            FunctionDeclaration fd = AstDeclarations.findFunctionDeclaration(
                input.program(), key.declaredName());
            if (fd == null) {
                ClassDeclaration synthetic =
                    AstDeclarations.jsonableClassForSynthetic(
                        input.program(), key.declaredName());
                if (synthetic != null) {
                    // A synthetic @jsonable export (C$fromJson/
                    // C$toJson): no FunctionDeclaration exists — the
                    // provider contract content derives from the
                    // resolved export signature plus the declaration's
                    // semantic resource identity (the declared-wrapper
                    // rule of D5), never a failure or a placeholder.
                    return syntheticJsonableExportContent(input, key,
                        synthetic);
                }
            }
            if (fd == null || fd.body() == null) {
                fail("the provider function '" + key.declaredName()
                    + "' of module '" + input.modulePath()
                    + "' has no function declaration with a body",
                    declarationRangeOf(input, key.declaredName()));
                return null;
            }
            Type exportType = input.exports().get(key.declaredName());
            if (!(exportType instanceof Type.Func funcType)) {
                fail("the provider function '" + key.declaredName()
                    + "' of module '" + input.modulePath()
                    + "' has no resolved exported signature",
                    fd.span().range());
                return null;
            }
            SymbolTable moduleScope = input.checkResult().symbolTable();
            DefaultIrRecorder recorder = new DefaultIrRecorder(
                input.checkResult().typeMap(),
                input.checkResult().scopeMap(), input.imports(),
                input.classification(), input.location(),
                input.modulePath(), input.program(),
                (typeNode, resolutionScope) -> {
                    input.nameResolver().setCurrentScope(
                        resolutionScope);
                    return input.nameResolver().resolveTypeNode(
                        typeNode);
                },
                Map.of());
            List<DefaultIrNode> statements = recorder.recordFunctionBody(
                fd, moduleScope);
            Set<Site> siteSet = new LinkedHashSet<>();
            Set<SemanticResourceIdentity> occurrenceIdentities =
                new LinkedHashSet<>();
            for (DefaultResourceOccurrence occurrence
                    : recorder.occurrences()) {
                occurrenceIdentities.add(
                    occurrence.semanticResourceIdentity());
                siteSet.add(new Site(occurrence.semanticResourceIdentity(),
                    occurrence.kind(), occurrence.sourceRange()));
            }
            List<String> parameters = new ArrayList<>();
            for (Type parameter : funcType.paramTypes()) {
                parameters.add(descriptorOf(input, parameter,
                    fd.span().range()));
                if (failed) {
                    return null;
                }
            }
            String returnDescriptor = descriptorOf(input,
                funcType.returnType(), fd.span().range());
            if (failed) {
                return null;
            }
            SymbolTable bodyScope = functionBodyScopeOf(input, fd,
                moduleScope);
            List<CanonicalStatement> body = new ArrayList<>();
            for (DefaultIrNode statement : statements) {
                body.add(serializeStatement(statement, input, siteSet,
                    occurrenceIdentities, bodyScope));
                if (failed) {
                    return null;
                }
            }
            CanonicalFunctionSemantics semantics =
                new CanonicalFunctionSemantics(SERIALIZER_VERSION,
                    funcType.isAsync(), parameters, returnDescriptor,
                    body);
            return semantics.canonicalText();
        }

        /**
         * The declared function wrapper digest: the canonical declared
         * signature content (serializer version, declared name, exact
         * sync marker, ordered parameter descriptors, return
         * descriptor) plus the declaration's semantic resource
         * identity — both through digests only, never raw URIs.
         */
        private String declaredFunctionDigest(
                DefaultSerializerModuleInput input, DigestKey key) {
            Type exportType = input.exports().get(key.declaredName());
            if (!(exportType instanceof Type.Func funcType)) {
                fail("the declared provider function '"
                    + key.declaredName() + "' of module '"
                    + input.modulePath() + "' has no resolved declared"
                    + " signature", declarationRangeOf(input,
                        key.declaredName()));
                return null;
            }
            DiagnosticRange declarationRange = declarationRangeOf(input,
                key.declaredName());
            SemanticResourceIdentity identity =
                new SemanticResourceIdentity(
                    input.location().semanticModuleIdentity(),
                    LexicalDeclarationIdentity.DeclarationKind.FUNCTION,
                    new LexicalDeclarationIdentity(
                        LexicalDeclarationIdentity.DeclarationKind
                            .FUNCTION,
                        key.declaredName(), input.modulePath(),
                        declarationRange));
            List<CanonicalJson.Value> parameterValues = new ArrayList<>();
            for (Type parameter : funcType.paramTypes()) {
                parameterValues.add(CanonicalJson.str(
                    descriptorOf(input, parameter, declarationRange)));
                if (failed) {
                    return null;
                }
            }
            String returnDescriptor = descriptorOf(input,
                funcType.returnType(), declarationRange);
            if (failed) {
                return null;
            }
            return CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("serializerVersion",
                    CanonicalJson.str(SERIALIZER_VERSION)),
                CanonicalJson.e("kind",
                    CanonicalJson.str("DECLARED_FUNCTION_SIGNATURE")),
                CanonicalJson.e("name",
                    CanonicalJson.str(key.declaredName())),
                CanonicalJson.e("isAsync",
                    CanonicalJson.bool(funcType.isAsync())),
                CanonicalJson.e("parameters",
                    CanonicalJson.arr(parameterValues)),
                CanonicalJson.e("returnDescriptor",
                    CanonicalJson.str(returnDescriptor)),
                CanonicalJson.e("semanticResourceIdentityDigest",
                    CanonicalJson.str(SemanticIdentityContent
                        .resourceIdentityDigest(identity)))));
        }

        /**
         * The canonical provider contract content of a synthetic
         * {@code @jsonable} export ({@code C$fromJson}/
         * {@code C$toJson}): the resolved export signature — the
         * exact Func type {@code input.exports()} carries — plus the
         * declaration's semantic resource identity digest, mirroring
         * the declared-wrapper rule of D5 (the generated binding/FFI
         * plan semantics join the domain once binding generation
         * lands). Identities participate through digests only, never
         * raw URIs.
         */
        private String syntheticJsonableExportContent(
                DefaultSerializerModuleInput input, DigestKey key,
                ClassDeclaration syntheticClass) {
            Type exportType = input.exports().get(key.declaredName());
            if (!(exportType instanceof Type.Func funcType)) {
                fail("the synthetic jsonable export '"
                    + key.declaredName() + "' of module '"
                    + input.modulePath() + "' has no resolved"
                    + " exported signature",
                    syntheticClass.span().range());
                return null;
            }
            DiagnosticRange declarationRange =
                syntheticClass.span().range();
            SemanticResourceIdentity identity =
                new SemanticResourceIdentity(
                    input.location().semanticModuleIdentity(),
                    LexicalDeclarationIdentity.DeclarationKind.FUNCTION,
                    new LexicalDeclarationIdentity(
                        LexicalDeclarationIdentity.DeclarationKind
                            .FUNCTION,
                        key.declaredName(), input.modulePath(),
                        declarationRange));
            List<CanonicalJson.Value> parameterValues = new ArrayList<>();
            for (Type parameter : funcType.paramTypes()) {
                parameterValues.add(CanonicalJson.str(
                    descriptorOf(input, parameter, declarationRange)));
                if (failed) {
                    return null;
                }
            }
            String returnDescriptor = descriptorOf(input,
                funcType.returnType(), declarationRange);
            if (failed) {
                return null;
            }
            return CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("serializerVersion",
                    CanonicalJson.str(SERIALIZER_VERSION)),
                CanonicalJson.e("kind",
                    CanonicalJson.str(
                        "SYNTHETIC_JSONABLE_EXPORT_SIGNATURE")),
                CanonicalJson.e("name",
                    CanonicalJson.str(key.declaredName())),
                CanonicalJson.e("isAsync",
                    CanonicalJson.bool(funcType.isAsync())),
                CanonicalJson.e("parameters",
                    CanonicalJson.arr(parameterValues)),
                CanonicalJson.e("returnDescriptor",
                    CanonicalJson.str(returnDescriptor)),
                CanonicalJson.e("semanticResourceIdentityDigest",
                    CanonicalJson.str(SemanticIdentityContent
                        .resourceIdentityDigest(identity)))));
        }

        // =================================================================
        // Resolution helpers
        // =================================================================

        /**
         * The reference kind a node kind pins for imported-resource
         * targets: calls and member accesses reference function
         * wrappers, contextual class literals reference class default
         * plans (D4).
         */
        private static RuntimeResourceReference.Kind occurrenceKindOf(
                DefaultIrNode node) {
            return switch (node.kind()) {
                case CALL, MEMBER_ACCESS ->
                    RuntimeResourceReference.Kind
                        .IMPORTED_FUNCTION_WRAPPER;
                case OBJECT_LITERAL ->
                    RuntimeResourceReference.Kind
                        .IMPORTED_CLASS_DEFAULT_PLAN;
                default -> null;
            };
        }

        private static ProviderKind providerKindOf(
                RuntimeResourceReference.Kind kind) {
            return switch (kind) {
                case IMPORTED_FUNCTION_WRAPPER -> ProviderKind.FUNCTION;
                case IMPORTED_CLASS_DEFAULT_PLAN -> ProviderKind.CLASS;
            };
        }

        /**
         * The exact literal scalar as a canonical JSON value: a
         * signed-int32 decimal integer (the literal carrier range is
         * guarded), a unique IEEE-754 hex float, the full Unicode
         * scalar string content, a boolean, or null — never folded,
         * truncated, or reformatted.
         */
        private CanonicalJson.Value literalJson(DefaultIrNode node) {
            LiteralValue literal = node.literalValue();
            if (literal == null) {
                fail("LITERAL IR node carries no literal value",
                    node.span());
                return null;
            }
            if (literal instanceof LiteralValue.NullLiteral) {
                return CanonicalJson.nullValue();
            }
            if (literal instanceof LiteralValue.BooleanLiteral b) {
                return CanonicalJson.bool(b.value());
            }
            if (literal instanceof LiteralValue.IntLiteral i) {
                if (i.value() < Integer.MIN_VALUE
                        || i.value() > Integer.MAX_VALUE) {
                    fail("int literal " + i.value()
                        + " is outside the signed-int32 range",
                        node.span());
                    return null;
                }
                return CanonicalJson.intValue((int) i.value());
            }
            if (literal instanceof LiteralValue.NumberLiteral n) {
                return CanonicalJson.number(n.value());
            }
            if (literal instanceof LiteralValue.StringLiteral s) {
                try {
                    return CanonicalJson.str(s.value());
                } catch (IllegalArgumentException defect) {
                    fail("string literal is not a Unicode scalar"
                        + " sequence: " + defect.getMessage(),
                        node.span());
                    return null;
                }
            }
            fail("unsupported literal value kind " + literal.getClass()
                .getSimpleName(), node.span());
            return null;
        }

        /** The E4 canonical descriptor text of a type, fail-closed. */
        private String descriptorOf(DefaultSerializerModuleInput input,
                Type type, DiagnosticRange range) {
            try {
                return input.descriptors().encode(type);
            } catch (IllegalStateException defect) {
                fail("no canonical runtime descriptor for a resolved"
                    + " type (" + defect.getMessage() + ")", range);
                return null;
            }
        }

        /**
         * The lexical scope a statement walks under: the recorded
         * pass-1 scope when present (provider-module bodies were
         * walked by the resolver); otherwise the pass-1 scope creation
         * mirrored exactly for the constructs that create scopes —
         * blocks and for statements. The pass-1 resolver never walks
         * class-default subexpressions, so default-position bodies
         * have no recorded scopes and the mirrored scopes carry the
         * body-local declarations as the statements are walked.
         */
        private SymbolTable statementScope(
                DefaultSerializerModuleInput input, StatementNode stmt,
                SymbolTable inherited) {
            if (input.checkResult() != null) {
                SymbolTable recorded = input.checkResult().scopeMap()
                    .get(stmt);
                if (recorded != null) {
                    return recorded;
                }
            }
            return switch (stmt) {
                case Block ignored -> enterScope(inherited);
                case ForStatement ignored -> enterScope(inherited);
                default -> inherited;
            };
        }

        /**
         * The scope function-expression body statements serialize
         * under: the pass-1 recorded body scope when present
         * (provider-module bodies were walked by the resolver),
         * otherwise the recorder's exact synthetic fallback — a fresh
         * child scope of the inherited (declaration) scope carrying
         * the function-expression parameters, mirroring
         * {@code DefaultIrRecorder.recordFunctionExpression}, so
         * type-annotation resolution inside default-nested bodies runs
         * at the body/declaration scope, exactly as the checker
         * resolved it (TypeChecker.checkFunctionExpr's fallback).
         */
        private SymbolTable functionBodyScope(
                DefaultSerializerModuleInput input, DefaultIrNode node,
                SymbolTable inheritedScope) {
            if (!(node.expression() instanceof FunctionExpr fe)) {
                fail("FUNCTION_EXPRESSION IR node carries no function"
                    + " expression AST (broken IR)", node.span());
                return null;
            }
            if (input.checkResult() != null) {
                SymbolTable recorded = input.checkResult().scopeMap()
                    .get(fe.body());
                if (recorded != null) {
                    return recorded;
                }
            }
            SymbolTable scope = enterScope(inheritedScope);
            for (Parameter p : fe.params()) {
                Type paramType = resolveTypeNode(input, p.type(), scope,
                    node.span());
                if (failed) {
                    return null;
                }
                defineIn(scope, p.name(),
                    new Symbol.VariableSymbol(p.name(), paramType, true),
                    node.span());
                if (failed) {
                    return null;
                }
            }
            return scope;
        }

        /**
         * The parameter scope of a function declaration: the recorded
         * pass-1 scope when present, else the synthetic child scope
         * carrying the parameters — mirroring
         * {@code NameResolver.walkFuncDecl} (parameters resolved and
         * defined inside the new scope).
         */
        private SymbolTable functionParameterScope(
                DefaultSerializerModuleInput input,
                FunctionDeclaration fd, SymbolTable enclosingScope,
                DiagnosticRange range) {
            if (input.checkResult() != null) {
                SymbolTable recorded = input.checkResult().scopeMap()
                    .get(fd);
                if (recorded != null) {
                    return recorded;
                }
            }
            SymbolTable scope = enterScope(enclosingScope);
            for (Parameter p : fd.params()) {
                Type paramType = resolveTypeNode(input, p.type(), scope,
                    range);
                if (failed) {
                    return null;
                }
                defineIn(scope, p.name(),
                    new Symbol.VariableSymbol(p.name(), paramType, true),
                    range);
                if (failed) {
                    return null;
                }
            }
            return scope;
        }

        /**
         * The body scope for a top-level provider function body: the
         * recorded pass-1 scope, else the recorder's synthetic
         * fallback (the parameter scope of the function).
         */
        private SymbolTable functionBodyScopeOf(
                DefaultSerializerModuleInput input,
                FunctionDeclaration fd, SymbolTable moduleScope) {
            SymbolTable recorded = input.checkResult() == null ? null
                : input.checkResult().scopeMap().get(fd.body());
            if (recorded != null) {
                return recorded;
            }
            return functionParameterScope(input, fd, moduleScope,
                fd.span().range());
        }

        /**
         * The scope of a for-of loop variable: the recorded pass-1
         * scope never exists for for-of statements (only the body
         * block is recorded), so the synthetic child scope carrying
         * the loop variable — the variable type resolves in the
         * enclosing scope first, mirroring
         * {@code NameResolver.walkForOf}.
         */
        private SymbolTable forOfScope(DefaultSerializerModuleInput input,
                DefaultIrNode node, SymbolTable enclosingScope) {
            if (!(node.statement() instanceof ForOfStatement fos)) {
                fail("FOR_OF IR node carries no for-of statement AST"
                    + " (broken IR)", node.span());
                return null;
            }
            Type varType = resolveTypeNode(input, fos.varType(),
                enclosingScope, node.span());
            if (failed) {
                return null;
            }
            SymbolTable scope = enterScope(enclosingScope);
            defineIn(scope, fos.varName(),
                new Symbol.VariableSymbol(fos.varName(), varType, false),
                node.span());
            if (failed) {
                return null;
            }
            return scope;
        }

        /**
         * The catch scope of a try statement: the recorded pass-1
         * scope when present, else the synthetic child scope carrying
         * the catch variable (the intrinsic Error class type, exactly
         * as {@code NameResolver.walkTry} defines it) — a sibling of
         * the try block's scope, never its parent.
         */
        private SymbolTable tryCatchScope(DefaultSerializerModuleInput input,
                DefaultIrNode node, SymbolTable enclosingScope) {
            if (!(node.statement() instanceof TryStatement ts)) {
                fail("TRY IR node carries no try-statement AST"
                    + " (broken IR)", node.span());
                return null;
            }
            if (input.checkResult() != null) {
                SymbolTable recorded = input.checkResult().scopeMap()
                    .get(ts);
                if (recorded != null) {
                    return recorded;
                }
            }
            SymbolTable scope = enterScope(enclosingScope);
            defineIn(scope, ts.catchVar(),
                new Symbol.VariableSymbol(ts.catchVar(),
                    Types.classType("Error",
                        NameResolver.intrinsicErrorIdentity()),
                    true),
                node.span());
            if (failed) {
                return null;
            }
            return scope;
        }

        /**
         * The declaration scope of the class being serialized: the
         * exact scope the checker visited the declaration in (the
         * declaring lexical context the planner resolved the class's
         * defaults against, D3), looked up by the exact class
         * declaration — never by declared name alone, so same-named
         * classes in distinct scopes each resolve their defaults in
         * their own declaration scope — or the declaration module's
         * rebuilt root scope (the declaration analyzer's surface).
         * Never the module root scope of implementation modules.
         */
        private SymbolTable classDeclarationScope(
                DefaultSerializerModuleInput input,
                ClassDeclaration declaration) {
            if (input.checkResult() != null) {
                SymbolTable scope =
                    input.checkResult().classScopes().get(declaration);
                if (scope != null) {
                    return scope;
                }
                fail("class '" + declaration.name() + "' of module '"
                    + input.modulePath() + "' has no recorded"
                    + " declaration scope (broken planner input: plans"
                    + " exist only for checker-visited classes)",
                    declaration.span().range());
                return null;
            }
            SymbolTable root = declarationRootFor(input);
            if (root == null) {
                return null;
            }
            return root;
        }

        /** The declaration module's rebuilt root scope. */
        private SymbolTable declarationRootFor(
                DefaultSerializerModuleInput input) {
            SymbolTable cached = declarationRoots.get(
                input.sourcePath());
            if (cached != null) {
                return cached;
            }
            NameResolver resolver = resolverFor(input,
                DiagnosticRange.synthetic(input.sourcePath()));
            if (resolver == null) {
                return null;
            }
            SymbolTable root = declarationRoots.get(input.sourcePath());
            if (root == null) {
                fail("the declaration module '" + input.modulePath()
                    + "' produced no root scope", DiagnosticRange
                        .synthetic(input.sourcePath()));
                return null;
            }
            return root;
        }

        /**
         * The canonical class symbol of a body-local class
         * declaration, mirroring {@code NameResolver.walkClassDecl}:
         * the module-identity layer's class identity for the
         * declaration.
         */
        private Symbol classSymbolFor(DefaultSerializerModuleInput input,
                String className, DiagnosticRange range) {
            CanonicalModuleIdentity moduleIdentity =
                input.classification().get(input.modulePath());
            if (moduleIdentity == null) {
                fail("no canonical public module identity for module '"
                    + input.modulePath() + "' (a class there can never"
                    + " carry an identity)", range);
                return null;
            }
            return new Symbol.ClassSymbol(className, List.of(),
                input.modulePath(),
                new CanonicalClassIdentity(moduleIdentity, className));
        }

        /**
         * Enters a fresh synthetic scope and registers it: body-local
         * declarations are defined into exactly these scopes while the
         * default-nested statements are walked (pass-1-built scopes
         * already carry their declarations).
         */
        private SymbolTable enterScope(SymbolTable parent) {
            SymbolTable scope = (parent != null ? parent
                : new SymbolTable()).enterScope();
            syntheticScopes.add(scope);
            return scope;
        }

        /**
         * Defines a body-local declaration into a synthetic scope (a
         * no-op for pass-1-built scopes, which already carry every
         * declaration). Fail-closed on a duplicate: the checker
         * rejects redeclarations, so a duplicate here is a defect.
         */
        private void defineIn(SymbolTable scope, String name,
                Symbol symbol, DiagnosticRange range) {
            if (!syntheticScopes.contains(scope)) {
                return;
            }
            if (scope.containsLocally(name)) {
                fail("duplicate local declaration '" + name
                    + "' while re-walking a default-nested scope",
                    range);
                return;
            }
            scope.define(name, symbol);
        }

        /**
         * Resolves a type annotation in the given scope through the
         * module's name resolver (rebuilt for declaration modules,
         * mirroring the declaration analyzer).
         */
        private Type resolveTypeNode(DefaultSerializerModuleInput input,
                TypeNode typeNode, SymbolTable scope,
                DiagnosticRange range) {
            NameResolver resolver = resolverFor(input, range);
            if (resolver == null) {
                return null;
            }
            resolver.setCurrentScope(scope);
            Type resolved = resolver.resolveTypeNode(typeNode);
            if (resolved == null || resolved == Type.Error.INSTANCE) {
                fail("a declared type annotation has no resolved type",
                    range);
                return null;
            }
            return resolved;
        }

        /**
         * The module's name resolver: the phase-3 resolver for
         * implementation modules, a lazily rebuilt declaration-scope
         * resolver for declaration modules (the declaration analyzer's
         * exact construction).
         */
        private NameResolver resolverFor(
                DefaultSerializerModuleInput input,
                DiagnosticRange range) {
            if (input.nameResolver() != null) {
                return input.nameResolver();
            }
            NameResolver cached = declarationResolvers.get(
                input.sourcePath());
            if (cached != null) {
                return cached;
            }
            NameResolver resolver = new NameResolver(input.modulePath(),
                input.moduleResolver(), new HashSet<>(),
                input.classification()::get);
            SymbolTable root;
            try {
                root = resolver.resolve(input.program());
            } catch (RuntimeException defect) {
                fail("declaration default serialization failed: "
                    + defect.getMessage(), range);
                return null;
            }
            declarationResolvers.put(input.sourcePath(), resolver);
            declarationRoots.put(input.sourcePath(), root);
            return resolver;
        }

        /**
         * The resolved function type of a function declaration: the
         * symbol resolution first, the declared annotations otherwise.
         */
        private Type.Func functionTypeOf(FunctionDeclaration fd,
                SymbolTable scope) {
            if (scope == null) {
                return null;
            }
            Symbol sym = scope.resolve(fd.name());
            if (sym instanceof Symbol.FunctionSymbol fs) {
                return fs.funcType();
            }
            return null;
        }

        /** Resolves a function type from the declared annotations. */
        private Type.Func resolveFunctionType(
                DefaultSerializerModuleInput input,
                FunctionDeclaration fd, SymbolTable scope,
                DiagnosticRange range) {
            List<Type> paramTypes = new ArrayList<>();
            for (Parameter p : fd.params()) {
                Type paramType = resolveTypeNode(input, p.type(), scope,
                    range);
                if (paramType == null) {
                    return null;
                }
                paramTypes.add(paramType);
            }
            Type returnType = resolveTypeNode(input, fd.returnType(),
                scope, range);
            if (returnType == null) {
                return null;
            }
            return new Type.Func(paramTypes, returnType, fd.isAsync());
        }

        // =================================================================
        // Program helpers
        // =================================================================

        /**
         * The declaration range of a function provider (the
         * reentrant-provider and missing-declaration anchor): the
         * top-level function declaration's complete scalar range when
         * findable, the canonical synthetic range otherwise. Class
         * providers anchor on their exact demanded declaration range
         * (the {@code DigestKey}'s range) — never a name-only lookup,
         * which could silently anchor another same-named class's
         * declaration.
         */
        private DiagnosticRange declarationRangeOf(
                DefaultSerializerModuleInput input, String name) {
            FunctionDeclaration fd = AstDeclarations.findFunctionDeclaration(
                input.program(), name);
            if (fd != null) {
                return fd.span().range();
            }
            return DiagnosticRange.synthetic(input.sourcePath());
        }

        private void failReentrant(DigestKey key) {
            DefaultSerializerModuleInput input = modules.get(
                key.moduleSourcePath());
            fail("reentrant provider digest demand for '"
                + key.declaredName() + "' in module '"
                + key.moduleSourcePath() + "': the merged runtime-edge"
                + " occurrence structure is not acyclic, so the"
                + " acyclicity gate must reject the compilation before"
                + " digest demand (never a hang, never a placeholder)",
                input == null
                    ? DiagnosticRange.synthetic(key.moduleSourcePath())
                    : key.declarationRange() != null
                        ? key.declarationRange()
                        : declarationRangeOf(input, key.declaredName()));
        }

        private void fail(String reason, DiagnosticRange range) {
            if (failed) {
                return;
            }
            failed = true;
            diagnostics.add(CompilerDiagnostic.error(
                DiagnosticCode.E6005,
                "canonical serialization failed: " + reason, range));
        }

        private static String rangeText(DiagnosticRange range) {
            return range.startLine() + ":" + range.startColumn() + "-"
                + range.endLine() + ":" + range.endColumn() + "@"
                + range.startScalarOffset() + ".."
                + range.endScalarOffset();
        }

        private static DefaultResourceOccurrence matchingOccurrence(
                List<DefaultResourceOccurrence> occurrences,
                SemanticResourceIdentity identity,
                RuntimeResourceReference.Kind kind,
                DiagnosticRange range) {
            for (DefaultResourceOccurrence occurrence : occurrences) {
                if (occurrence.semanticResourceIdentity()
                        .equals(identity)
                        && occurrence.kind() == kind
                        && occurrence.sourceRange().equals(range)) {
                    return occurrence;
                }
            }
            return null;
        }

        private static Set<SemanticResourceIdentity>
                occurrenceIdentitiesOf(
                    List<DefaultResourceOccurrence> occurrences) {
            Set<SemanticResourceIdentity> identities =
                new LinkedHashSet<>();
            for (DefaultResourceOccurrence occurrence : occurrences) {
                identities.add(occurrence.semanticResourceIdentity());
            }
            return identities;
        }
    }

    // =========================================================================
    // Ordered copies
    // =========================================================================

    private static Map<String, List<SerializedDefaultClass>>
            unmodifiableOrderedClasses(
                Map<String, List<SerializedDefaultClass>> classes) {
        Map<String, List<SerializedDefaultClass>> copy =
            new LinkedHashMap<>();
        for (Map.Entry<String, List<SerializedDefaultClass>> entry
                : classes.entrySet()) {
            Objects.requireNonNull(entry.getKey(), "module key");
            List<SerializedDefaultClass> list = new ArrayList<>();
            for (SerializedDefaultClass value
                    : Objects.requireNonNull(entry.getValue(),
                        "serializedClasses entry")) {
                list.add(Objects.requireNonNull(value,
                    "serialized class"));
            }
            copy.put(entry.getKey(), List.copyOf(list));
        }
        return Collections.unmodifiableMap(copy);
    }

    private static Map<SemanticResourceIdentity, String>
            unmodifiableOrderedMap(
                Map<SemanticResourceIdentity, String> digests) {
        Map<SemanticResourceIdentity, String> copy =
            new LinkedHashMap<>();
        for (Map.Entry<SemanticResourceIdentity, String> entry
                : digests.entrySet()) {
            Objects.requireNonNull(entry.getKey(), "digest key");
            Objects.requireNonNull(entry.getValue(), "digest value");
            copy.put(entry.getKey(), entry.getValue());
        }
        return Collections.unmodifiableMap(copy);
    }
}
