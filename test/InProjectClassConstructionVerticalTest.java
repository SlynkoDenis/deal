package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.ClassConstructionValidator;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.AddressChainProtocol;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;

/**
 * ISSUE-0644: the in-project imported-class construction vertical
 * verification
 * ({@code module-export-reads-and-in-project-class-construction} M7 and
 * the in-project imported-class construction contract;
 * {@code semantic-ir-construct-coverage-cutover} K3;
 * {@code luajit-jvm-single-lowering-production-cutover} C1).
 *
 * <p>A focused probe project — the owner module exports a class with a
 * defaulted field whose default expression is evaluated by the owner's
 * factory, the entry module imports the owner and constructs the imported
 * class literal (one empty literal, one with provided fields), and no
 * cross-module call exists in the closure — is driven through the real
 * project entry, the composed validator chain, the semantic oracle, and
 * both production artifacts under the real toolchains ({@code luajit};
 * {@code javac --release 25 -proc:none} + {@code java}), with the
 * production arm's own {@link ProductionProjectEmission}.</p>
 *
 * <ol>
 *   <li>the probe lowers through {@link SemanticLowerer#lowerProject}
 *       with zero {@code RETAINED_ABI_DEFERRED} diagnostics to exactly
 *       one project carrying the complete closure (the owner in
 *       dependency order before the entry), and the checker-valid
 *       imported-class literal is admitted by the composed chain the
 *       entry runs internally;</li>
 *   <li>the entry unit carries exactly one {@code CLASS_NEW} per
 *       constructed imported class, each with
 *       {@code defaultOwner: SHARED_FACTORY}, the owner interface's
 *       {@code constructionEntry} as the factory reference, the owner
 *       unit's layout, an empty local default-child list, the
 *       literal-order provided fields, the declaration-order field
 *       boundaries, and the omitted defaulted field boundary wired to
 *       the owner factory op's result;</li>
 *   <li>the composed validator verdict admits the chain with no composer
 *       error (the project-form gate, the closed 14 rules, the
 *       address-chain protocol, the control-flow validator, and the
 *       class-construction validator over the entry unit with the
 *       in-project facts); the same class-construction verdict rejects
 *       the same unit without the facts (the D10 fact producer is
 *       load-bearing);</li>
 *   <li>the oracle executes the probe closure: the owner's
 *       {@code CLASS_FACTORY} events parent to the caller's
 *       {@code CLASS_NEW} (cross-unit K-D12), every factory and
 *       {@code CLASS_DEFAULT} event carries the owner module
 *       attribution, the owner-scope default value is observable as the
 *       owner factory's evaluated default, and the entry's field reads
 *       publish the constructed values (the empty literal's defaults and
 *       the provided literal's overlay);</li>
 *   <li>the production artifacts: the JVM class stages as the one project
 *       artifact, compiles with {@code javac --release 25 -proc:none},
 *       executes under {@code java}, constructs the instances through the
 *       owner's factory, and its field reads observe the constructed
 *       values (the entry's construction probe re-invoked through the
 *       published export surface); the LuaJIT chunk stages with the
 *       unchanged deployment copies and repeated staging is byte-identical
 *       per target;</li>
 *   <li><b>a seam gap surfaced by the drive is recorded, not repaired
 *       (the leaf contract).</b> The executed LuaJIT production artifact
 *       cannot reach the owner factory's detached {@code CLASS_DEFAULT}
 *       functions from a function body: the emitter declares the detached
 *       defaults as chunk-level {@code local function D<opId>}
 *       <em>after</em> the function factories whose bodies reference them,
 *       so the reference resolves to a nil global at the call (Lua scoping
 *       — the factory-name locals are pre-declared for exactly this
 *       reason, the detached-default locals are not). The drive records
 *       this finding with its exact emitted-text and runtime evidence and
 *       asserts the remaining outcomes; it makes no production lowering or
 *       emission change, and adds no second fact producer.</li>
 *   <li><b>the owner-resolution namespace boundary is recorded too.</b>
 *       The oracle and both emitters resolve a {@code SHARED_FACTORY}
 *       owner as {@code new ModuleId(payload.classId().modulePath())} — the
 *       class descriptor namespace. In the conventional root/module layout
 *       (root {@code src}, module {@code owner.deal}) that namespace
 *       ({@code @src/Address}) is not the module identity ({@code owner}),
 *       so the same drive fails closed there (the oracle's producer defect
 *       and the production arm's E6005). The probe therefore uses the
 *       identity-coherent layout (root directory {@code owner}, module
 *       {@code owner.deal}) under which the landed chain resolves, and the
 *       conventional-layout boundary is pinned and recorded as a second
 *       finding — never repaired here by a second fact producer.</li>
 * </ol>
 */
public class InProjectClassConstructionVerticalTest {

    private static int passed = 0;
    private static int failed = 0;
    private static final List<String> findings = new ArrayList<>();

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    /** Records a seam finding the leaf contract forbids repairing here. */
    private static void recordFinding(String finding) {
        findings.add(finding);
        System.out.println("FINDING (recorded, not repaired): " + finding);
    }

    // =========================================================================
    // The probe project
    // =========================================================================

    private static final ModuleId OWNER = new ModuleId("owner");
    private static final ModuleId APP = new ModuleId("app");

    /**
     * The identity-coherent probe layout: the module root directory's
     * configured text (its final path component, {@code owner}) equals
     * the owner module's identity, so the class descriptor namespace the
     * landed owner resolution derives from the {@code CLASS_NEW} payload's
     * class identity ({@code @owner/Address}) is the owner's module
     * identity ({@code owner}). The conventional layout's boundary is
     * recorded by {@link #testRecordedOwnerResolutionBoundary()}.
     */
    private static final String COHERENT_ROOT = "owner";

    /**
     * The owner: an exported class with one explicitly-defaulted field
     * and one field whose default expression is computed in the owner's
     * default block ({@code 10000 + 115} — {@code 10115} is never a
     * literal of the owner source, so the observable {@code int:10115}
     * can only be the owner factory's evaluated default).
     */
    private static final String OWNER_SOURCE = """
        export class Address {
          city: string = "berlin";
          zip: int = 10000 + 115;
        }
        """;

    /**
     * The entry: one empty imported-class literal (both fields default
     * through the owner's factory) and one with provided fields, with the
     * field reads guarding the constructed values. The construction site
     * is the exported entry function itself, so the artifact drivers
     * re-invoke it through the published export surface after the module
     * walks — its guard holds only when every field read observed the
     * constructed value. No cross-module call exists in the closure.
     */
    private static final String APP_SOURCE = """
        import * as Owner from "./owner"

        export function main(): null {
          let empty: Owner.Address = {}
          let provided: Owner.Address = {zip: 9, city: "munich"}
          if (empty.zip !== 10115 || empty.city !== "berlin") {
            throw {
              code: "FAIL_EMPTY_FIELDS",
              message: "the defaulted imported-class field reads diverged"
            }
          }
          if (provided.zip !== 9 || provided.city !== "munich") {
            throw {
              code: "FAIL_PROVIDED_FIELDS",
              message: "the provided imported-class field reads diverged"
            }
          }
          return null
        }
        """;

    private record Fixture(
        Path root,
        Path moduleRoot,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        DistributionHome distributionHome) {
    }

    /** The release-owned production invocation (the epic's production record). */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /**
     * The fixture frontend compile (the harness-invocation pattern the
     * sibling fixtures use): the checked project, the interface index,
     * the requirement manifests, the declaration surface, and the
     * deployment resolver the production unit consumes. The fixture
     * itself is arm-independent; the unit is driven with the
     * release-owned production invocation.
     */
    private static Fixture compileFixture() throws Exception {
        return compileFixture(COHERENT_ROOT);
    }

    private static Fixture compileFixture(String rootDirectory) throws Exception {
        Path root = Files.createTempDirectory("in-project-class-vertical");
        Path moduleRoot = root.resolve(rootDirectory);
        writeFileIn(root, rootDirectory + "/owner.deal", OWNER_SOURCE);
        writeFileIn(root, rootDirectory + "/app.deal", APP_SOURCE);
        Path entry = moduleRoot.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(moduleRoot.toAbsolutePath()), null, null,
            ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the probe project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, moduleRoot, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            new LinkedHashMap<>(), new LinkedHashMap<>(),
            DistributionHome.forManifestDirectory(moduleRoot.toString()));
    }

    /** The one project lowering over the real checked project. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    /** One production-arm drive of the probe (the real production unit). */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager) throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, false, fixture.distributionHome(), stager);
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit,
            SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    /** The imported-class constructions of the entry unit (not the Error literals). */
    private static List<SemanticOp> addressConstructions(LoweredModuleUnit app,
            ClassId classId) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ofKind(app, SemanticOpKind.CLASS_NEW)) {
            if (op.payload() instanceof KindPayload.ClassNewPayload payload
                    && payload.classId().equals(classId)) {
                matches.add(op);
            }
        }
        return matches;
    }

    /**
     * The owner's in-project construction facts, resolved exactly the way
     * the D10 fact producer accumulates them: the owner interface entry
     * from the project index, the owner unit's layout, the owner
     * registry's factory op id for the interface {@code constructionEntry},
     * and the factory op's result value.
     */
    private record OwnerFacts(ClassId classId, ClassInterface interfaceEntry,
            ClassLayout layout, OpId factoryOpId, ValueId factoryResult) {

        SharedFactoryFacts toSharedFactoryFacts() {
            return new SharedFactoryFacts(classId, interfaceEntry, layout,
                factoryOpId, factoryResult);
        }
    }

    /**
     * Resolves the owner facts from the lowered project (the same triple
     * the probe's assertions compare the produced payload against).
     * Returns {@code null} after recording the failed preconditions.
     */
    private static OwnerFacts ownerFacts(Fixture fixture,
            SemanticLowerer.ProjectLoweringResult result) {
        LoweredModuleUnit owner = result.project().modules().get(OWNER);
        LoweredModuleUnit app = result.project().modules().get(APP);
        check(owner != null && app != null,
            "both the owner and the dependent module are in the closure");
        if (owner == null || app == null) {
            return null;
        }
        deal.semantic.ir.ExternalModuleInterface ownerInterface =
            fixture.index().modules().get(OWNER);
        check(ownerInterface != null,
            "the owner carries an interface-index entry");
        if (ownerInterface == null) {
            return null;
        }
        ClassInterface entry = null;
        int classCount = 0;
        for (ClassInterface candidate : ownerInterface.classes()) {
            classCount++;
            if (candidate.classId().name().equals("Address")) {
                entry = candidate;
            }
        }
        check(classCount == 1 && entry != null,
            "the owner interface declares exactly the exported Address class");
        if (entry == null) {
            return null;
        }
        ClassLayout layout = owner.classLayouts().get(entry.classId());
        ClassFactoryRegistry registry = result.registryOf(OWNER);
        check(layout != null && registry != null,
            "the owner unit's layout and the owner registry resolve");
        if (layout == null || registry == null) {
            return null;
        }
        OpId factoryOpId = registry.factoryFor(entry.constructionEntry());
        SemanticOp factoryOp = factoryOpId == null ? null : opOf(owner, factoryOpId);
        check(factoryOpId != null && factoryOp != null
                && factoryOp.kind() == SemanticOpKind.CLASS_FACTORY
                && factoryOp.result() instanceof ValueId,
            "the owner's CLASS_FACTORY is registered under the interface "
                + "constructionEntry with a result value");
        if (factoryOpId == null || factoryOp == null
                || !(factoryOp.result() instanceof ValueId factoryResult)) {
            return null;
        }
        return new OwnerFacts(entry.classId(), entry, layout, factoryOpId,
            factoryResult);
    }

    // =========================================================================
    // 1. The lowering drive, the CLASS_NEW payload facts, and the
    //    composed validator verdict
    // =========================================================================

    private static void testLoweringAndClassNewFacts() throws Exception {
        System.out.println("-- the probe lowers through the one project entry with "
            + "zero RETAINED_ABI_DEFERRED; the entry unit carries the "
            + "CLASS_NEW(SHARED_FACTORY) payload facts; the composed chain admits "
            + "the in-project facts --");
        Fixture fixture = compileFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(!result.hasErrors() && result.project() != null,
                "the probe lowers to exactly one project: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            check(result.diagnostics().isEmpty(),
                "the checker-valid imported in-project class literal is admitted "
                    + "with zero diagnostics: " + result.diagnostics());
            boolean retainedAbiDeferred = false;
            for (CompilerDiagnostic diagnostic : result.diagnostics()) {
                if (diagnostic.message().contains("RETAINED_ABI_DEFERRED")) {
                    retainedAbiDeferred = true;
                }
            }
            check(!retainedAbiDeferred,
                "the checker-valid in-project input reports zero "
                    + "RETAINED_ABI_DEFERRED");
            checkEq(List.of(OWNER, APP),
                List.copyOf(result.project().modules().keySet()),
                "exactly one project carries the complete closure: the owner in "
                    + "dependency order before the entry");
            checkEq(APP, result.project().entryModule(), "the entry module is app");

            OwnerFacts facts = ownerFacts(fixture, result);
            if (facts == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            List<SemanticOp> constructions =
                addressConstructions(app, facts.classId());
            checkEq(2, constructions.size(),
                "the dependent module lowers one CLASS_NEW per constructed "
                    + "imported in-project class");
            if (constructions.size() != 2) {
                return;
            }

            KindPayload.ClassNewPayload empty =
                (KindPayload.ClassNewPayload) constructions.get(0).payload();
            KindPayload.ClassNewPayload provided =
                (KindPayload.ClassNewPayload) constructions.get(1).payload();
            for (KindPayload.ClassNewPayload payload : List.of(empty, provided)) {
                checkEq(facts.classId(), payload.classId(),
                    "every construction names the imported in-project class");
                checkEq(DefaultOwner.SHARED_FACTORY, payload.defaultOwner(),
                    "the imported literal carries defaultOwner SHARED_FACTORY");
                checkEq(facts.interfaceEntry().constructionEntry(),
                    payload.classFactoryRef(),
                    "the literal carries the owner interface's constructionEntry "
                        + "as its factory reference");
                check(payload.classDefaultOpIds().isEmpty(),
                    "the SHARED_FACTORY literal carries an empty classDefaultOpIds "
                        + "list (the defaults transfer to the owner's factory)");
                checkEq(facts.layout(), payload.layout(),
                    "the payload layout is the owner unit's layout, resolved "
                        + "through the in-project interface facts");
            }

            // The empty literal: no provided field, both boundaries are the
            // omitted defaults in declaration order (city, zip), each wired
            // to the owner factory op's result value.
            check(empty.providedFields().isEmpty(),
                "the empty literal carries no provided field");
            checkEq(List.of("city", "zip"), empty.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::field).toList(),
                "the empty literal's boundaries run in declaration order");
            checkEq(List.of(BoundaryKind.CLASS_DEFAULT_FIELD,
                    BoundaryKind.CLASS_DEFAULT_FIELD),
                empty.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::kind).toList(),
                "both omitted defaulted fields are CLASS_DEFAULT_FIELD "
                    + "boundaries");
            for (KindPayload.FieldBoundary boundary : empty.fieldBoundaries()) {
                SemanticOp boundaryOp = opOf(app, boundary.boundaryOpId());
                check(boundaryOp != null
                        && boundaryOp.payload()
                            instanceof KindPayload.BoundaryPayload payload
                        && facts.factoryResult().equals(payload.input()),
                    "the omitted defaulted field's boundary wires the owner factory "
                        + "op's result ValueId (" + boundary.field() + ")");
            }

            // The provided literal: literal-order provided fields,
            // declaration-order literal boundaries.
            checkEq(List.of("zip", "city"), provided.providedFields().stream()
                    .map(KindPayload.ProvidedField::name).toList(),
                "the provided fields stay in literal order");
            checkEq(List.of("city", "zip"), provided.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::field).toList(),
                "the provided literal's boundaries run in declaration order");
            checkEq(List.of(BoundaryKind.CLASS_LITERAL_FIELD,
                    BoundaryKind.CLASS_LITERAL_FIELD),
                provided.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::kind).toList(),
                "both provided fields carry their CLASS_LITERAL_FIELD boundary");

            // No cross-module call exists in the closure (the probe's
            // objective boundary): neither unit records an EXTERNAL_ENTRY,
            // and no CALL carries an external callee route.
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                checkEq(0, ofKind(unit, SemanticOpKind.EXTERNAL_ENTRY).size(),
                    "module " + unit.moduleId().path()
                        + " records no cross-module entry");
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() != SemanticOpKind.CALL) {
                        continue;
                    }
                    check(op.payload() instanceof KindPayload.CallPayload call
                            && call.externalEntryRef() == null,
                        "the probe closure carries no cross-module call "
                            + "(module " + unit.moduleId().path() + ")");
                }
            }

            // The composed chain: the project-form gate plus the per-unit
            // members re-asserted over the produced units (the lowering entry
            // ran the complete chain internally, so its empty diagnostics are
            // the composer verdict; the direct re-runs prove the arm reached).
            SemanticIrValidator.ComparisonFacts comparisonFacts =
                new SemanticIrValidator.ComparisonFacts(
                    fixture.index().interfaceIndexDigest(),
                    SemanticProfile.DEAL_V1_2_INT32,
                    productionInvocation().capabilityRegistryHash());
            check(SemanticIrValidator.validate(result.project(), comparisonFacts)
                    .isEmpty(),
                "the project-form closed gate admits the complete closure");
            for (ModuleId moduleId : List.of(OWNER, APP)) {
                LoweredModuleUnit unit = result.project().modules().get(moduleId);
                StructuredBodyTable table = result.tableOf(moduleId);
                check(table != null, "the produced table of " + moduleId + " is carried");
                check(SemanticIrValidator.validate(unit, comparisonFacts).isEmpty(),
                    "module " + moduleId.path() + " passes the closed 14 rules");
                check(AddressChainProtocol.validate(unit).isEmpty(),
                    "module " + moduleId.path()
                        + " passes the address-chain protocol");
                check(deal.semantic.ControlFlowValidator.validate(unit, table)
                        .isEmpty(),
                    "module " + moduleId.path()
                        + " passes the control-flow validator");
            }
            Map<ClassId, SharedFactoryFacts> inProjectFacts = new LinkedHashMap<>();
            inProjectFacts.put(facts.classId(), facts.toSharedFactoryFacts());
            Optional<CompilerDiagnostic> classVerdict =
                ClassConstructionValidator.validate(app, result.tableOf(APP),
                    result.registryOf(APP), new JsonDefaultChildTable(Map.of()),
                    fixture.index().modules().get(APP), inProjectFacts);
            check(classVerdict.isEmpty(),
                "the class-construction validator admits the imported-class chain "
                    + "with no composer error: " + classVerdict);

            // The D10 fact producer is load-bearing: the identical unit
            // without the in-project facts is rejected (never a silently
            // emitted SHARED_FACTORY construction, the RETAINED_ABI
            // deferral arm).
            Optional<CompilerDiagnostic> withoutFacts =
                ClassConstructionValidator.validate(app, result.tableOf(APP),
                    result.registryOf(APP), new JsonDefaultChildTable(Map.of()),
                    fixture.index().modules().get(APP), Map.of());
            check(withoutFacts.isPresent(),
                "the same unit without the in-project facts is rejected");
            if (withoutFacts.isPresent()) {
                check("E6005".equals(withoutFacts.get().code())
                        && withoutFacts.get().message()
                            .contains(facts.classId().text()),
                    "the facts-absent verdict is the fail-closed E6005 naming the "
                        + "unresolvable imported class; got "
                        + withoutFacts.get().message());
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The oracle: the factory/default events and the field outcomes
    // =========================================================================

    private static void testOracleEvents() throws Exception {
        System.out.println("-- the oracle executes the probe closure: the owner's "
            + "CLASS_FACTORY events parent to the caller's CLASS_NEW, the owner "
            + "module attribution and the owner-scope default value are "
            + "observable, and the field reads publish the constructed values --");
        Fixture fixture = compileFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe lowers: " + result.diagnostics());
                return;
            }
            OwnerFacts facts = ownerFacts(fixture, result);
            if (facts == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            List<SemanticOp> constructions =
                addressConstructions(app, facts.classId());
            if (constructions.size() != 2) {
                fail("the probe lowers exactly two imported-class constructions; got "
                    + constructions.size());
                return;
            }
            SemanticRuntimeModel.ConsumerRun oracle =
                SemanticOracle.executeProjectInits(result.project(), result.tables(),
                    result.registries(), null);
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle completes the closure's init walks: "
                    + oracle.comparisonReport());
            if (oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success
                    success) {
                checkEq("null", success.resultAtom(),
                    "the entry main publishes the null result");
            }

            List<SemanticRuntimeModel.TraceEvent> factoryEvents =
                traceEvents(oracle, SemanticOpKind.CLASS_FACTORY);
            List<SemanticRuntimeModel.TraceEvent> defaultEvents =
                traceEvents(oracle, SemanticOpKind.CLASS_DEFAULT);
            List<SemanticRuntimeModel.TraceEvent> readEvents =
                traceEvents(oracle, SemanticOpKind.FIELD_READ);

            // One factory transfer per construction: a START/SUCCESS pair
            // whose events parent to the triggering caller CLASS_NEW in the
            // entry module and carry the owner module attribution.
            checkEq(4, factoryEvents.size(),
                "the oracle emits one START/SUCCESS pair per factory transfer "
                    + "(two constructions); got " + factoryEvents.size());
            if (factoryEvents.size() == 4) {
                checkEq(List.of(SemanticRuntimeModel.Phase.START,
                        SemanticRuntimeModel.Phase.SUCCESS,
                        SemanticRuntimeModel.Phase.START,
                        SemanticRuntimeModel.Phase.SUCCESS),
                    factoryEvents.stream()
                        .map(SemanticRuntimeModel.TraceEvent::phase).toList(),
                    "the two factory transfers each emit a START/SUCCESS pair in "
                        + "construction order");
                for (int i = 0; i < 4; i++) {
                    SemanticRuntimeModel.TraceEvent event = factoryEvents.get(i);
                    SemanticOp caller = constructions.get(i / 2);
                    checkEq(OWNER.path(), event.module(),
                        "the factory event carries the owner module attribution");
                    check(event.parentOp() != null
                            && event.parentOp().equals(caller.opId()),
                        "the factory event parents to the triggering caller "
                            + "CLASS_NEW: " + event.text());
                    check(event.parentOp() != null
                            && APP.equals(event.parentOp().module()),
                        "the parent CLASS_NEW lives in the entry module");
                }
            }

            // One CLASS_DEFAULT child execution pair per (construction,
            // defaulted field) the factory transfer applies: the empty
            // literal omits both fields (both defaults run, in the owner's
            // scope), the provided literal provides both (its transfer
            // skips the provided fields' defaults). The detached default
            // ops carry no static parent (the K-D12 detached-op shape) and
            // run inside their triggering factory transfer.
            checkEq(4, defaultEvents.size(),
                "the oracle emits one START/SUCCESS pair per (construction, "
                    + "defaulted field) the transfer applies; got "
                    + defaultEvents.size());
            for (SemanticRuntimeModel.TraceEvent event : defaultEvents) {
                checkEq(OWNER.path(), event.module(),
                    "every CLASS_DEFAULT event carries the owner module attribution");
            }
            checkEq(1L, defaultEvents.stream()
                    .filter(event -> event.phase()
                        == SemanticRuntimeModel.Phase.SUCCESS)
                    .filter(event -> "int:10115".equals(event.output()))
                    .count(),
                "the owner-scope zip default (the owner's computed default block, "
                    + "10115) is observable");
            checkEq(1L, defaultEvents.stream()
                    .filter(event -> event.phase()
                        == SemanticRuntimeModel.Phase.SUCCESS)
                    .filter(event -> "str:berlin".equals(event.output()))
                    .count(),
                "the owner-scope city default is observable");
            if (factoryEvents.size() == 4 && defaultEvents.size() == 4) {
                long factoryStart = factoryEvents.get(0).sequence();
                long factorySuccess = factoryEvents.get(1).sequence();
                for (SemanticRuntimeModel.TraceEvent event : defaultEvents) {
                    check(event.sequence() > factoryStart
                            && event.sequence() < factorySuccess,
                        "the CLASS_DEFAULT event runs inside its triggering "
                            + "factory transfer: " + event.text());
                }
            }

            // The field reads observe the constructed values: the empty
            // literal's owner-scope defaults and the provided literal's
            // overlay.
            checkEq(List.of("int:10115", "str:berlin", "int:9", "str:munich"),
                readEvents.stream()
                    .filter(event -> event.phase()
                        == SemanticRuntimeModel.Phase.SUCCESS)
                    .map(SemanticRuntimeModel.TraceEvent::output).toList(),
                "the oracle's field reads publish the constructed values");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static List<SemanticRuntimeModel.TraceEvent> traceEvents(
            SemanticRuntimeModel.ConsumerRun run, SemanticOpKind kind) {
        List<SemanticRuntimeModel.TraceEvent> events = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.kind() == kind) {
                events.add(event);
            }
        }
        return events;
    }

    // =========================================================================
    // 3. Both production artifacts under the real toolchains
    // =========================================================================

    private static void testProductionArtifacts() throws Exception {
        System.out.println("-- the production artifacts: the JVM class constructs "
            + "through the owner's factory and its field reads observe the "
            + "constructed values under javac/java; the LuaJIT chunk stages with "
            + "byte-identical repeated staging, and its execution outcome is "
            + "asserted or the surfaced seam is recorded --");
        Fixture fixture = compileFixture();
        Path luaOut = fixture.root().resolve("out-luajit");
        Path luaOutRepeat = fixture.root().resolve("out-luajit-repeat");
        Path jvmOut = fixture.root().resolve("out-jvm");
        Path jvmOutRepeat = fixture.root().resolve("out-jvm-repeat");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null,
                "the probe lowers for the production drive: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            OwnerFacts facts = ownerFacts(fixture, result);
            if (facts == null) {
                return;
            }

            // (a) LuaJIT: one chunk named for the entry module plus the
            // unchanged deployment copies; the staged set is byte-identical
            // on a repeated run.
            Map<String, String> luaTree = emitAndPublish(fixture, Backend.LUAJIT,
                luaOut, "app.lua");
            Map<String, String> luaTreeRepeat = emitAndPublish(fixture, Backend.LUAJIT,
                luaOutRepeat, "app.lua");
            checkEq(luaTree, luaTreeRepeat,
                "the staged LuaJIT project artifact set is byte-identical on a "
                    + "repeated run");
            check(luaTree.containsKey("app.lua"),
                "the LuaJIT staged set carries the one project artifact");
            check(luaTree.containsKey("deal/runtime.lua"),
                "the LuaJIT staged set carries the unchanged runtime deployment "
                    + "copy");
            check(luaTree.keySet().stream()
                    .anyMatch(path -> path.startsWith("std/")),
                "the LuaJIT staged set carries the unchanged stdlib deployment "
                    + "copies");
            check(luaTree.keySet().stream()
                    .noneMatch(path -> path.endsWith(".deal.map.json")),
                "the LuaJIT staged set carries no source-map sidecar");

            String luaArtifact = Files.readString(luaOut.resolve("app.lua"),
                StandardCharsets.UTF_8);
            int forwardReferences = 0;
            List<String> forwardReferenceEvidence = new ArrayList<>();
            for (SemanticOp op : ofKind(
                    result.project().modules().get(OWNER),
                    SemanticOpKind.CLASS_DEFAULT)) {
                String reference = "pcall(D" + op.opId().id() + ")";
                String declaration = "local function D" + op.opId().id() + "()";
                int referenceAt = luaArtifact.indexOf(reference);
                int declarationAt = luaArtifact.indexOf(declaration);
                if (referenceAt >= 0 && declarationAt > referenceAt) {
                    forwardReferences++;
                    forwardReferenceEvidence.add(op.opId() + " referenced at "
                        + referenceAt + " before its declaration at " + declarationAt);
                }
            }

            writeFileIn(luaOut, "vertical_probe.lua", LUA_DRIVER);
            ProcessOutcome luaRun = runProcess(List.of("luajit", "vertical_probe.lua"),
                luaOut);
            if (luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK")) {
                check(true,
                    "the LuaJIT production artifact constructs the imported "
                        + "instances through the owner's factory and its field-read "
                        + "guard holds under real luajit");
                checkEq("", luaRun.stderr(),
                    "the production LuaJIT chunk publishes no trace protocol");
                checkEq(0, forwardReferences,
                    "no function body references a detached class-default function "
                        + "before its declaration any more");
            } else if (forwardReferences > 0
                    && luaRun.stderr().contains("attempt to call a nil value")) {
                recordFinding("the LuaJIT production artifact cannot execute the "
                    + "owner-scope default transfer: the emitter declares the "
                    + "detached class-default functions as chunk-level `local "
                    + "function D<opId>` AFTER the function factories whose bodies "
                    + "call `pcall(D<opId>)`, so the reference resolves to a nil "
                    + "global (the factory-name locals are pre-declared for exactly "
                    + "this reason; the detached-default locals are not). The "
                    + "failing seam is the LuaJIT emitter's detached class-default "
                    + "emission order (deal/codegen/lua/LuaSemanticEmitter.java, the "
                    + "project preamble: factories, then the detached defaults). "
                    + "Emitted-text evidence: " + forwardReferenceEvidence
                    + "; runtime evidence: exit " + luaRun.exitCode() + ", stderr '"
                    + luaRun.stderr().replace("\n", "\\n") + "'. The landing fix "
                    + "belongs to the emitter (pre-declare the detached-default "
                    + "locals beside the factory names and assign them instead of "
                    + "re-declaring them with `local function`); a landed-fix "
                    + "candidate was validated against this very drive outside the "
                    + "leaf's change set and makes the full LuaJIT artifact drive "
                    + "pass, but this verification leaf records the finding and "
                    + "changes no production file.");
            } else {
                fail("the LuaJIT production artifact failed for a reason other than "
                    + "the recorded detached-default forward-reference seam: exit="
                    + luaRun.exitCode() + " " + luaRun.output());
            }

            // (b) JVM: one class source, no deployment copy; the real
            // javac --release 25 -proc:none + java run drives the module
            // walks and the driver re-invokes the exported construction
            // probe through the published export surface.
            Map<String, String> jvmTree = emitAndPublish(fixture, Backend.JVM,
                jvmOut, "App.java");
            Map<String, String> jvmTreeRepeat = emitAndPublish(fixture, Backend.JVM,
                jvmOutRepeat, "App.java");
            checkEq(jvmTree, jvmTreeRepeat,
                "the staged JVM project artifact set is byte-identical on a "
                    + "repeated run");
            checkEq(Set.of("App.java"), jvmTree.keySet(),
                "the JVM staged set is the one project artifact and nothing else");

            String classpath = absoluteClasspath();
            Path classes = fixture.root().resolve("jvm-classes");
            Files.createDirectories(classes);
            writeFileIn(jvmOut, "VerticalProbe.java", JVM_DRIVER);
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmOut.resolve("App.java").toAbsolutePath().toString(),
                jvmOut.resolve("VerticalProbe.java").toAbsolutePath().toString()),
                jvmOut);
            checkEq(0, javacRun.exitCode(),
                "the JVM production artifact compiles with javac --release 25 "
                    + "-proc:none: " + javacRun.output());
            if (javacRun.exitCode() == 0) {
                ProcessOutcome jvmRun = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "VerticalProbe"), jvmOut);
                checkEq(0, jvmRun.exitCode(),
                    "the JVM production artifact constructs the imported instances "
                        + "through the owner's factory and its field reads observe "
                        + "the constructed values under real java: " + jvmRun.output());
                check(jvmRun.stdout().contains("PROBE-OK"),
                    "the JVM driver's construction probe re-invocation all holds: "
                        + jvmRun.stdout().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * One production-arm drive into a fresh root, published; returns the
     * published tree (path → Base64 content) so a repeated run compares
     * byte-for-byte. The artifact path is asserted against the pinned
     * target path before publishing.
     */
    private static Map<String, String> emitAndPublish(Fixture fixture,
            Backend backend, Path out, String expectedArtifact) throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = emit(fixture, backend, stager);
            check(result.emitted(), "the " + backend + " production run emits: "
                + result.diagnostics());
            if (!result.emitted()) {
                return Map.of();
            }
            checkEq(expectedArtifact, result.artifactRelativePath(),
                "the " + backend + " artifact is the entry module's target path");
            stager.publish();
        } finally {
            stager.discard();
        }
        return snapshotTree(out);
    }

    /** The published tree of one root: relative path → Base64 content. */
    private static Map<String, String> snapshotTree(Path root) throws Exception {
        Map<String, String> snapshot = new TreeMap<>();
        if (!Files.exists(root)) {
            return snapshot;
        }
        try (var walk = Files.walk(root)) {
            for (Path file : walk.sorted().toList()) {
                if (Files.isRegularFile(file)) {
                    snapshot.put(root.relativize(file).toString().replace('\\', '/'),
                        Base64.getEncoder().encodeToString(Files.readAllBytes(file)));
                }
            }
        }
        return snapshot;
    }

    // =========================================================================
    // 4. The recorded owner-resolution namespace boundary
    // =========================================================================

    /**
     * The conventional root/module layout (root {@code src}, modules
     * {@code owner.deal}/{@code app.deal}) through the same drive: the
     * checker-valid literal still lowers to {@code CLASS_NEW(SHARED_FACTORY)},
     * but the landed owner resolution derives the owner module from the
     * class descriptor namespace ({@code @src/Address} → module {@code src}),
     * which is not the owner's module identity ({@code owner}) — the oracle
     * rejects the run as a producer defect and the production arm fails
     * closed with E6005 and stages nothing. Pinned and recorded as a
     * finding, never repaired here.
     */
    private static void testRecordedOwnerResolutionBoundary() throws Exception {
        System.out.println("-- the conventional root/module layout: the class "
            + "descriptor namespace is not the module identity, so the landed "
            + "owner resolution fails closed; recorded as a finding --");
        Fixture fixture = compileFixture("src");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(!result.hasErrors() && result.project() != null,
                "the conventional-layout probe still lowers through the one project "
                    + "entry with zero RETAINED_ABI_DEFERRED: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            ClassId ownerClassId = null;
            for (SemanticOp op : ofKind(app, SemanticOpKind.CLASS_NEW)) {
                if (op.payload() instanceof KindPayload.ClassNewPayload payload
                        && payload.defaultOwner() == DefaultOwner.SHARED_FACTORY) {
                    ownerClassId = payload.classId();
                }
            }
            check(ownerClassId != null,
                "the conventional-layout literal lowers CLASS_NEW(SHARED_FACTORY)");
            if (ownerClassId == null) {
                return;
            }
            checkEq("src", ownerClassId.modulePath(),
                "the class descriptor namespace is the configured root text");
            check(!ownerClassId.modulePath().equals(OWNER.path()),
                "the class descriptor namespace is not the owner module identity");
            recordFinding("the landed owner resolution derives a SHARED_FACTORY "
                + "owner module as new ModuleId(payload.classId().modulePath()) — "
                + "the class descriptor namespace — in the semantic oracle and both "
                + "emitters, so it resolves the owner only when that namespace "
                + "equals the module identity. In the conventional root/module "
                + "layout (root 'src', module 'owner.deal') the class identity is "
                + ownerClassId.text() + " while the module identity is '"
                + OWNER.path() + "', and the drive fails closed there: the oracle "
                + "rejects the run as a producer defect naming owner module 'src', "
                + "and the production arm returns E6005 SHARED_EMITTER_COVERAGE and "
                + "stages nothing. The failing seam is the consumers' owner-module "
                + "resolution (the semantic oracle and both emitters); the landing "
                + "fix belongs to them (or to the fact channel that supplies the "
                + "owner module identity), never to a second fact producer. The "
                + "probe's identity-coherent layout is the boundary's evidence.");

            // The oracle's producer defect: the owner module derived from the
            // class namespace has no registry in the closure.
            try {
                SemanticOracle.executeProjectInits(result.project(),
                    result.tables(), result.registries(), null);
                fail("the oracle should reject the conventional-layout run (the "
                    + "owner module derived from the class namespace is not in the "
                    + "closure)");
            } catch (IllegalStateException rejection) {
                check(rejection.getMessage() != null
                        && rejection.getMessage().contains("has no ClassFactoryRegistry"),
                    "the oracle rejects the conventional layout with its "
                        + "owner-resolution producer defect: "
                        + rejection.getMessage());
            }

            // The production arm fails closed and stages nothing.
            Path out = fixture.root().resolve("out-arm");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result arm;
            try {
                arm = emit(fixture, Backend.LUAJIT, stager);
                check(stager.stagedSet().relativePaths().isEmpty(),
                    "the conventional-layout production arm stages nothing");
            } finally {
                stager.discard();
            }
            check(!arm.emitted(), "the conventional-layout production arm fails "
                + "closed: " + arm.diagnostics());
            check(arm.firstDiagnostic() != null
                    && "E6005".equals(arm.firstDiagnostic().code())
                    && arm.firstDiagnostic().message()
                        .contains(ProductionProjectEmission.SHARED_EMITTER_COVERAGE),
                "the conventional-layout arm returns the mapped E6005 "
                    + "SHARED_EMITTER_COVERAGE: " + arm.diagnostics());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Drivers
    // =========================================================================

    /**
     * The LuaJIT driver: the production chunk returns the entry module's
     * surface, the load-time module walks run the constructions and their
     * field-read guards, and the driver re-invokes the exported entry
     * function through the published surface.
     */
    private static final String LUA_DRIVER = """
        local surfaces = dofile("app.lua")
        assert(type(surfaces) == "table",
          "the production chunk returns the entry module's surface")
        local entry = surfaces["main"]
        assert(type(entry) == "table" and entry.__kind == "function"
          and type(entry.f) == "function",
          "the entry surface publishes the imported-class construction probe")
        entry.f()
        print("PROBE-OK")
        """;

    /**
     * The JVM driver: {@code App.main} drives the module walks (the
     * constructions and their field-read guards) and the driver
     * re-invokes the exported entry function through the published
     * surface.
     */
    private static final String JVM_DRIVER = """
        public final class VerticalProbe {
          public static void main(String[] args) {
            App.main(new String[0]);
            deal.codegen.jvm.JvmRuntime.Table surface =
                App.EXPORT_SURFACES.get("app");
            Object entry = surface.read("main");
            if (!(entry instanceof deal.codegen.jvm.JvmRuntime.FunctionValue fn)) {
              throw new IllegalStateException(
                  "the entry surface publishes the imported-class construction "
                      + "probe");
            }
            fn.fn.invoke(new Object[0]);
            System.out.println("PROBE-OK");
          }
        }
        """;

    // =========================================================================
    // Helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n")
                + " stderr=" + stderr.replace("\n", "\\n");
        }
    }

    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(java.io.File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(java.io.File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir)
            throws Exception {
        Path stderrFile = Files.createTempFile(workDir, "stderr", ".txt");
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new ProcessOutcome(exit, stdout, stderr);
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(Comparator.reverseOrder()).forEach(entry -> {
                        try {
                            Files.deleteIfExists(entry);
                        } catch (java.io.IOException ignored) {
                            // best effort
                        }
                    });
                }
            }
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== In-Project Imported-Class Construction Vertical "
            + "Tests (ISSUE-0644) ===\n");
        testLoweringAndClassNewFacts();
        testOracleEvents();
        testProductionArtifacts();
        testRecordedOwnerResolutionBoundary();
        System.out.println();
        System.out.println("Recorded findings: " + findings.size());
        for (String finding : findings) {
            System.out.println("  - " + finding);
        }
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== In-Project Imported-Class Construction Vertical "
            + "Tests Passed ===");
    }
}
