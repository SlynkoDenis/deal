package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.ffi.FfiCdefBundle;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.test.conformance.CorpusFfi;
import deal.test.conformance.SidecarExpectations;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0663: the typed FFI crossings and the class-value carrier
 * projection ({@code luajit-ffi-load-emission-and-typed-crossings} F3/F4;
 * {@code luajit-ffi-shared-emission-and-jvm-rejection} F3; the FFI typed
 * call and value-read contract and the carrier projection contract;
 * sequencing step 2).
 *
 * <ol>
 *   <li>the scalar fixtures {@code ffi/012}, {@code ffi/013},
 *       {@code ffi/014}, {@code ffi/048}, {@code ffi/049},
 *       {@code ffi/050} and the pointer fixture {@code ffi/020} compile
 *       through the production arm with the corpus's production FFI
 *       metadata and execute under {@code luajit} with the sidecar-pinned
 *       {@code runtime-ok} transcripts (empty stdout and stderr, exit
 *       0);</li>
 *   <li>the emitted crossing positions: the {@code DEAL_TO_HOST} +
 *       {@code HOST_PARAMETER} cells run in one-based order, the loaded
 *       wrapper is invoked through its {@code .f} convention with the
 *       trailing literal span triplet, and the single {@code HOST_TO_DEAL}
 *       + {@code HOST_SYNC_RETURN} cell runs at the call origin — no new
 *       boundary kind and no conversion code in the artifact (the ABI
 *       conversions stay owned by {@code deal/runtime.lua});</li>
 *   <li>the failure fixtures {@code ffi/022}–{@code ffi/024} raise
 *       {@code FFI_NULL_STRING}, {@code FFI_INVALID_UTF8}, and
 *       {@code FFI_NULL_POINTER} at the call expression with the
 *       sidecar-pinned message and origin;</li>
 *   <li>the class-value carrier projection: the class parameter cell
 *       accepts the chunk representation (and fails every other value with
 *       the pinned E8010 text, never E8001), the chunk-to-wrapper
 *       projection runs post-cell and allocates fresh (the wrapper
 *       observes the runtime representation, the program's own value is
 *       untouched and re-projected per crossing), and the wrapper-to-chunk
 *       projection runs before the crossing's events (one heap value per
 *       class-typed crossing — the trace stream's class atoms are one
 *       identity);</li>
 *   <li>no null mapping exists inside the bridge, no {@code CLASS_DEFAULT}
 *       child or conversion code is emitted for an FFI crossing, and the
 *       closed {@code BoundaryKind} set keeps its landed members.</li>
 * </ol>
 */
public class FfiTypedCrossingTest {

    private static int passed = 0;
    private static int failed = 0;

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

    // =========================================================================
    // The corpus fixtures of this slice
    // =========================================================================

    private static final String CORPUS_FFI_DIR = "test/conformance/backend-runtime/ffi";
    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String NATIVE = "candidate/native";
    private static final String NATIVE_DOTTED = "candidate.native";
    private static final String HANDLE_DESC = "@$external/candidate/native/Handle";

    /** One corpus FFI fixture of the production drive. */
    private record CorpusCase(String name) {

        String corpusFixture() {
            return CORPUS_FFI_DIR + "/" + name + ".deal";
        }

        String sidecar() {
            return CORPUS_FFI_DIR + "/" + name + ".expect.json";
        }
    }

    /** The scalar and pointer fixtures of the typed-crossing drive. */
    private static final List<CorpusCase> RUNTIME_OK_CASES = List.of(
        new CorpusCase("012-ffi-double-roundtrip"),
        new CorpusCase("013-ffi-boolean-roundtrip"),
        new CorpusCase("014-ffi-string-utf8-parameter"),
        new CorpusCase("048-ffi-int32-minimum-roundtrip"),
        new CorpusCase("049-ffi-void-null-return"),
        new CorpusCase("050-ffi-borrowed-string-copy"),
        new CorpusCase("020-ffi-pointer-token"));

    /** The call-site failure fixtures of the six-code family. */
    private static final List<CorpusCase> RUNTIME_ERROR_CASES = List.of(
        new CorpusCase("022-ffi-null-string"),
        new CorpusCase("023-ffi-invalid-utf8"),
        new CorpusCase("024-ffi-null-pointer"));

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
        Path root,
        Path sourceRoot,
        String specifier,
        String dotted,
        int headerLinesStripped,
        String strippedApp,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** Compiles one corpus FFI fixture project through the real frontend. */
    private static Fixture compileCorpus(CorpusCase corpusCase) throws Exception {
        String rawFixture = Files.readString(
            Path.of(corpusCase.corpusFixture()), StandardCharsets.UTF_8);
        return compileWith(corpusCase.name(), rawFixture, Map.of());
    }

    /**
     * Materializes the corpus declaration plus one application source and
     * compiles the project through the real frontend. The classification
     * headers are stripped from both sources (the production metadata and
     * the emitted spans use the stripped coordinates).
     */
    private static Fixture compileWith(String name, String rawFixture,
            Map<String, String> extraSources) throws Exception {
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT, NATIVE);
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + NATIVE + "'");
        }
        String declaration = Files.readString(CONFORMANCE_ROOT
            .resolve(CorpusFfi.FFI_DIR).resolve(wiring.declarationCorpusPath()),
            StandardCharsets.UTF_8);
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT, NATIVE,
            SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException(
                "the corpus declaration of '" + NATIVE + "' does not validate: "
                    + module.validationDiagnostics());
        }
        String app = ConformanceHarnessMetadata.stripClassificationHeaders(
            rawFixture);
        int stripped = rawFixture.split("\n", -1).length
            - app.split("\n", -1).length;
        Path root = Files.createTempDirectory("ffi-typed-crossing");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("native.d.deal"),
            ConformanceHarnessMetadata.stripClassificationHeaders(declaration),
            StandardCharsets.UTF_8);
        for (Map.Entry<String, String> extra : extraSources.entrySet()) {
            Path target = src.resolve(extra.getKey());
            Files.createDirectories(target.getParent());
            Files.writeString(target, extra.getValue(), StandardCharsets.UTF_8);
        }
        Files.writeString(src.resolve(name + ".deal"), app, StandardCharsets.UTF_8);
        Path entry = src.resolve(name + ".deal").toAbsolutePath();
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(NATIVE, src.resolve("native.d.deal").toAbsolutePath().toString());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry,
            root.resolve("out"), false, false, false, false, Backend.LUAJIT,
            externals, List.of(src.toAbsolutePath()), null, null,
            harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null
                || built.index() == null || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the FFI fixture '" + name
                + "' did not build: " + detail + " / " + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        externCModules.put(new ModuleId(NATIVE_DOTTED), module.generatedModule());
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(NATIVE));
        }
        return new Fixture(root, src, NATIVE, NATIVE_DOTTED, stripped, app,
            built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), externCModules, identities);
    }

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

    /** Runs the production arm with the fixture's own metadata. */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            PublicationStager stager) throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(), fixture.sourceRoot().toString(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), Backend.LUAJIT, false,
            deal.distribution.DistributionHome.forManifestDirectory(
                fixture.sourceRoot().toString()),
            stager);
    }

    /** One published production artifact. */
    private record Artifact(String name, String text) {
    }

    /** Emits one fixture, publishes it, and returns the artifact. */
    private static Artifact emitAndPublish(Fixture fixture, Path out)
            throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = emit(fixture, stager);
            if (result.emitted()) {
                stager.publish();
            }
        } finally {
            stager.discard();
        }
        if (!result.emitted()) {
            throw new IllegalStateException("the FFI fixture artifact did not emit: "
                + result.diagnostics());
        }
        String name = result.artifactRelativePath();
        return new Artifact(name,
            Files.readString(out.resolve(name), StandardCharsets.UTF_8));
    }

    // =========================================================================
    // 1. The scalar and pointer fixtures through the production artifact
    // =========================================================================

    private static void testScalarAndPointerDrive() throws Exception {
        System.out.println("-- the scalar and pointer FFI fixtures execute "
            + "through the production artifact under luajit --");
        for (CorpusCase corpusCase : RUNTIME_OK_CASES) {
            Fixture fixture = compileCorpus(corpusCase);
            Path out = fixture.root().resolve("out-prod");
            try {
                Artifact emitted = emitAndPublish(fixture, out);
                String artifact = emitted.text();
                SidecarExpectations.RuntimeExpectation.Executed expectation =
                    luajitExpectation(corpusCase);
                checkEq("runtime-ok", expectation.mode(),
                    corpusCase.name() + " is a runtime-ok fixture");
                check(artifact.contains("__exportSurfaces[\"" + NATIVE_DOTTED
                        + "\"] = __exportSurfaces[\"" + NATIVE_DOTTED
                        + "\"] or __rt.load_ffi("),
                    "the artifact loads the FFI module through load_ffi: "
                        + corpusCase.name());
                check(artifact.contains("__exportSurfaces[\"" + NATIVE_DOTTED
                        + "\"][\""),
                    "the crossing resolves the loaded surface entry: "
                        + corpusCase.name());
                ProcessOutcome run = runProcess(
                    List.of("luajit", emitted.name()), out, Map.of());
                check(run.exitCode() == expectation.exitCode(),
                    corpusCase.name() + " exit code matches the sidecar: exit="
                        + run.exitCode() + " stderr=" + escaped(run.stderr()));
                checkEq(new String(expectation.stdout(), StandardCharsets.UTF_8),
                    run.stdout(), corpusCase.name() + " stdout transcript");
                checkEq(new String(expectation.stderr(), StandardCharsets.UTF_8),
                    run.stderr(), corpusCase.name() + " stderr transcript");
            } finally {
                deleteRecursively(fixture.root());
            }
        }

        // The drives resolve the real loaded surface: the same fixture with
        // a broken library wiring fails on the load instead of passing.
        Fixture broken = compileCorpus(RUNTIME_OK_CASES.get(0));
        Path brokenOut = broken.root().resolve("out-missing-library");
        try {
            Path missing = broken.root().resolve("libcandidate_missing.so");
            PublicationStager stager = PublicationStager.forRoot(brokenOut);
            ProductionProjectEmission.Result result;
            try {
                result = ProductionProjectEmission.run(productionInvocation(),
                    broken.checkedProject(), broken.index(), broken.manifests(),
                    broken.surface(), broken.declarationIdentities(),
                    Map.of(new ModuleId(NATIVE_DOTTED),
                        withMissingLibrary(broken.externCModules()
                            .get(new ModuleId(NATIVE_DOTTED)), missing)),
                    broken.sourceRoot().toString(),
                    BuiltinErrorDeclaration.synthesized(
                        broken.checkedProject().modules().get(0).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                    Set.of(), Backend.LUAJIT, false,
                    deal.distribution.DistributionHome.forManifestDirectory(
                        broken.sourceRoot().toString()),
                    stager);
                if (result.emitted()) {
                    stager.publish();
                }
            } finally {
                stager.discard();
            }
            check(result.emitted(),
                "the broken-library fixture still compiles and emits: "
                    + result.diagnostics());
            if (result.emitted()) {
                Files.writeString(brokenOut.resolve("broken-probe.lua"),
                    failureProbe(result.artifactRelativePath()),
                    StandardCharsets.UTF_8);
                ProcessOutcome run = runProcess(List.of("luajit", "broken-probe.lua"),
                    brokenOut, Map.of("DEAL_DEFER_MAIN", "1"));
                check(run.exitCode() == 0
                        && run.stdout().contains("ERR|FFI_LIBRARY_LOAD|"),
                    "the drive fails on a broken load: exit=" + run.exitCode()
                        + " stdout=" + escaped(run.stdout())
                        + " stderr=" + escaped(run.stderr()));

            }
        } finally {
            deleteRecursively(broken.root());
        }
    }

    /** One generated module whose native library text names a missing file. */
    private static FfiGeneratedModule withMissingLibrary(FfiGeneratedModule module,
            Path missing) {
        FfiCdefBundle bundle = module.cdefBundle();
        return new FfiGeneratedModule(module.modulePath(), module.descriptor(),
            new FfiCdefBundle(bundle.bundleDigest(), bundle.identityDigest(),
                bundle.fullContent(), bundle.entries(), bundle.nativeLibraryKind(),
                missing.toAbsolutePath().toString(), bundle.functions(),
                bundle.classes()),
            module.plans(), module.bindings());
    }

    // =========================================================================
    // 2. The emitted crossing positions
    // =========================================================================

    private static final String ADD_APP = """
        import * as native from "candidate/native"

        export function main(): null {
          let sum: int = native.ffi_add(2, 3)
          if (sum !== 5) {
            throw { code: "TEST_FAIL", message: "ffi add" }
          }
          return null
        }
        """;

    private static void testEmittedCrossingPositions() throws Exception {
        System.out.println("-- the emitted crossing positions: the ordered "
            + "parameter cells, the .f invocation, and the return cell --");
        Fixture fixture = compileWith("ffi-typed-add", ADD_APP, Map.of());
        Path out = fixture.root().resolve("out-prod");
        try {
            // The lowered IR: DEAL_TO_HOST + HOST_PARAMETER cells in
            // one-based order and one HOST_TO_DEAL + HOST_SYNC_RETURN cell
            // at the call origin — the landed closed shapes.
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the ffi_add fixture lowers: " + lowered.diagnostics());
                return;
            }
            Map<deal.semantic.ir.OpId, SemanticOp> opsById = new LinkedHashMap<>();
            for (LoweredModuleUnit unit : lowered.project().modules().values()) {
                for (SemanticOp op : unit.ops()) {
                    opsById.put(op.opId(), op);
                }
            }
            SemanticOp addCall = null;
            List<SemanticOp> parameterCells = new ArrayList<>();
            SemanticOp returnCell = null;
            for (SemanticOp op : opsById.values()) {
                if (op.kind() != SemanticOpKind.CALL
                        || !(op.payload() instanceof KindPayload.CallPayload call)
                        || !(call.callee()
                            instanceof KindPayload.CallCallee.Static staticCallee)
                        || !(staticCallee.binding()
                            instanceof FunctionExecutionBinding.HostFunction host)
                        || !host.exportName().equals("ffi_add")) {
                    continue;
                }
                addCall = op;
                for (deal.semantic.ir.OpId boundaryId : call.parameterBoundaryOpIds()) {
                    parameterCells.add(opsById.get(boundaryId));
                }
                returnCell = opsById.get(call.returnBoundaryOpId());
            }
            check(addCall != null, "the ffi_add CALL lowers as a HostFunction call");
            if (addCall == null || returnCell == null) {
                fail("the ffi_add crossing boundaries lower");
                return;
            }
            checkEq(2, parameterCells.size(),
                "one DEAL_TO_HOST parameter cell per declared parameter");
            List<RuntimeDescriptor> parameterDescriptors = new ArrayList<>();
            for (SemanticOp cell : parameterCells) {
                KindPayload.BoundaryPayload boundary =
                    (KindPayload.BoundaryPayload) cell.payload();
                parameterDescriptors.add(boundary.descriptor());
                checkEq(BoundaryKind.DEAL_TO_HOST, boundary.kind(),
                    "the parameter cell is a DEAL_TO_HOST boundary");
                checkEq(FailurePolicyId.HOST_PARAMETER, cell.failurePolicy(),
                    "the parameter cell carries the HOST_PARAMETER policy");
                checkEq(addCall.origin().span(), cell.origin().span(),
                    "the parameter cell carries the call span");
            }
            checkEq(List.of(RuntimeDescriptor.Int.INSTANCE,
                    RuntimeDescriptor.Int.INSTANCE), parameterDescriptors,
                "the parameter cells carry the declared descriptors in order");
            KindPayload.BoundaryPayload returnBoundary =
                (KindPayload.BoundaryPayload) returnCell.payload();
            checkEq(BoundaryKind.HOST_TO_DEAL, returnBoundary.kind(),
                "the return cell is a HOST_TO_DEAL boundary");
            checkEq(FailurePolicyId.HOST_SYNC_RETURN, returnCell.failurePolicy(),
                "the return cell carries the HOST_SYNC_RETURN policy");
            checkEq(addCall.origin().span(), returnCell.origin().span(),
                "the return cell runs at the call origin");

            Artifact emitted = emitAndPublish(fixture, out);
            String artifact = emitted.text();
            int callLineNumber = lineOfCall(fixture.strippedApp(), "native.ffi_add");
            int callColumn = columnOfCall(fixture.strippedApp(), "native.ffi_add");
            String fileText = fixture.sourceRoot().resolve("ffi-typed-add.deal")
                .toAbsolutePath().toString();
            int firstCell = artifact.indexOf("pcall(__hostParamCell, \"int\", 1, ");
            int secondCell = artifact.indexOf("pcall(__hostParamCell, \"int\", 2, ");
            int invocation = artifact.indexOf(
                "__exportSurfaces[\"" + NATIVE_DOTTED + "\"][\"ffi_add\"].f, "
                    + "__hbT[1], __hbT[2], \"" + fileText + "\", " + callLineNumber
                    + ", " + callColumn + ")");
            int returnCellText = artifact.indexOf(
                "pcall(__hostReturnCell, \"int\", __resT, \"" + fileText + ":"
                    + callLineNumber + ":" + callColumn + "\", false)");
            check(firstCell >= 0, "the one-based first parameter cell is emitted");
            check(secondCell > firstCell,
                "the parameter cells are emitted in one-based order");
            check(invocation > secondCell,
                "the loaded wrapper is invoked after both parameter cells with "
                    + "the argument table and the literal span triplet");
            check(returnCellText > invocation,
                "the return cell runs after the invocation at the call origin");
            check(artifact.contains("__hbT[1] = __hostProjectArg(\"int\", nil, __chkB)"),
                "the post-cell parameter projection runs for every parameter");
            check(!artifact.contains("ffi.cast") && !artifact.contains("ffi.new")
                    && !artifact.contains("ffi.copy") && !artifact.contains("ffi.string")
                    && !artifact.contains("cdef("),
                "the artifact carries no ABI conversion or cdef text (the "
                    + "conversions stay runtime-owned)");
            String crossing = artifact.substring(
                artifact.lastIndexOf("__hbT = {}",
                    artifact.indexOf("__exportSurfaces[\"" + NATIVE_DOTTED
                        + "\"][\"ffi_add\"].f")),
                returnCellText);
            check(!crossing.contains("CLASS_DEFAULT")
                    && !crossing.contains("CLASS_NEW")
                    && !crossing.contains("class_plan_"),
                "the crossing emits no CLASS_DEFAULT child, no construction "
                    + "code, and no conversion code");

            ProcessOutcome run = runProcess(
                List.of("luajit", emitted.name()), out, Map.of());
            check(run.exitCode() == 0 && run.stdout().isEmpty()
                    && run.stderr().isEmpty(),
                "the two-parameter fixture executes clean: exit="
                    + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));

            // The closed boundary-kind set and its reserved names stay
            // landed: this slice introduces no boundary kind.
            checkEq(25, BoundaryKind.values().length,
                "the closed BoundaryKind set keeps its landed member count");
            check(BoundaryKind.RESERVED_NAMES.equals(List.of(
                    "BYTE_ELEMENT_ASSIGNMENT", "C_FFI_TO_DEAL", "DEAL_TO_C_FFI")),
                "the reserved boundary names are unchanged");
            check(java.util.Arrays.asList(BoundaryKind.values()).contains(
                    BoundaryKind.DEAL_TO_HOST)
                    && java.util.Arrays.asList(BoundaryKind.values()).contains(
                        BoundaryKind.HOST_TO_DEAL),
                "the FFI crossings use the landed HOST boundary kinds");
            check(!artifact.contains("ffi.cast") && !artifact.contains("__rt.ffi_converters"),
                "no conversion code is emitted into the chunk");

            // The runtime keeps the ABI conversion authority.
            String runtime = Files.readString(Path.of("deal", "runtime.lua"),
                StandardCharsets.UTF_8);
            for (String row : List.of("ffi_converters.outbound",
                    "ffi_converters.inbound", "kind == \"C_POINTER\"",
                    "kind == \"C_STRUCT\"", "FFI_INVALID_STRING")) {
                check(runtime.contains(row),
                    "the runtime still owns '" + row + "'");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static int lineOfCall(String source, String callee) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(callee)) {
                return i + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + callee + "'");
    }

    private static int columnOfCall(String source, String callee) {
        String[] lines = source.split("\n", -1);
        for (String line : lines) {
            int at = line.indexOf(callee);
            if (at >= 0) {
                return at + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + callee + "'");
    }

    // =========================================================================
    // 3. The call-site failures keep their codes and origins
    // =========================================================================

    private static void testFailureCodesAtCallExpression() throws Exception {
        System.out.println("-- the call-site FFI failures keep their codes and "
            + "the call-expression origin --");
        for (CorpusCase corpusCase : RUNTIME_ERROR_CASES) {
            Fixture fixture = compileCorpus(corpusCase);
            Path out = fixture.root().resolve("out-prod");
            try {
                Artifact emittedArtifact = emitAndPublish(fixture, out);
                SidecarExpectations.RuntimeExpectation.Executed expectation =
                    luajitExpectation(corpusCase);
                check(expectation.isRuntimeError(),
                    corpusCase.name() + " is a runtime-error fixture");
                SidecarExpectations.ErrorExpectation error = expectation.error();
                check(error != null && error.pinsSpan(),
                    corpusCase.name() + " pins the error span");
                if (error == null) {
                    continue;
                }
                Files.writeString(out.resolve("probe.lua"),
                    failureProbe(emittedArtifact.name()), StandardCharsets.UTF_8);
                ProcessOutcome run = runProcess(List.of("luajit", "probe.lua"),
                    out, Map.of("DEAL_DEFER_MAIN", "1"));
                check(run.exitCode() == 0,
                    corpusCase.name() + " failure probe runs: exit="
                        + run.exitCode() + " " + escaped(run.stderr()));
                if (run.exitCode() != 0) {
                    continue;
                }
                String[] parts = run.stdout().trim().split("\\|", -1);
                checkEq("ERR", parts[0], corpusCase.name() + " raises a DEAL error");
                if (!"ERR".equals(parts[0])) {
                    continue;
                }
                checkEq(error.code(), parts[1],
                    corpusCase.name() + " pinned code");
                checkEq(error.message(), parts[2],
                    corpusCase.name() + " pinned message");
                checkEq(String.valueOf(error.line() - fixture.headerLinesStripped()),
                    parts[4], corpusCase.name() + " pinned origin line (rebased)");
                checkEq(String.valueOf(error.column()), parts[5],
                    corpusCase.name() + " pinned origin column");
                check(parts[3].endsWith(corpusCase.name() + ".deal"),
                    corpusCase.name() + " pinned origin file: " + parts[3]);
                // The origin is the call expression inside the stripped
                // source.
                String callSource = fixture.strippedApp().split("\n", -1)[
                    error.line() - fixture.headerLinesStripped() - 1];
                check(callSource.lastIndexOf("native.") + 1 == error.column(),
                    corpusCase.name() + " origin column is the call expression: "
                        + callSource);
                // The production terminal frames the pinned code.
                ProcessOutcome terminal = runProcess(
                    List.of("luajit", emittedArtifact.name()), out, Map.of());
                check(terminal.exitCode() == expectation.exitCode()
                        && terminal.stdout().startsWith(
                            "DEAL_ERROR_CODE: " + error.code() + "\n"),
                    corpusCase.name() + " terminal frames the pinned code: exit="
                        + terminal.exitCode() + " stdout="
                        + escaped(terminal.stdout()));
            } finally {
                deleteRecursively(fixture.root());
            }
        }
    }

    /** The LuaJIT failure probe of one artifact (the deferred entry). */
    private static String failureProbe(String artifactName) {
        return """
            local function fail(message)
              print("PROBE-FAIL|" .. message)
              os.exit(1)
            end
            local surface = dofile("%s")
            if type(surface) ~= "table" then fail("the chunk returns no surface") end
            local ok, err = __dealMain()
            if ok then fail("the module init succeeded") end
            if type(err) ~= "table" or err.code == nil then
              fail("the raised value is not a runtime error table")
            end
            local message = err.message or err.m
            local file, line, column = err.file, err.line, err.column
            if err.o ~= nil then
              local f, l, c = tostring(err.o):match("^(.*):(%%d+):(%%d+)$")
              file, line, column = f, l, c
            end
            print("ERR|" .. tostring(err.code) .. "|" .. tostring(message)
              .. "|" .. tostring(file) .. "|" .. tostring(line) .. "|"
              .. tostring(column))
            """.formatted(artifactName);
    }

    /** The pinned LuaJIT execution expectation of one corpus sidecar. */
    private static SidecarExpectations.RuntimeExpectation.Executed
            luajitExpectation(CorpusCase corpusCase) throws Exception {
        String json = Files.readString(Path.of(corpusCase.sidecar()),
            StandardCharsets.UTF_8);
        SidecarExpectations.StructuredExpectationSidecar sidecar =
            SidecarExpectations.StructuredExpectationSidecar.parse(json);
        SidecarExpectations.RuntimeExpectation expectation =
            sidecar.byBackend().get("luajit");
        if (!(expectation
                instanceof SidecarExpectations.RuntimeExpectation.Executed executed)) {
            throw new IllegalStateException("the LuaJIT sidecar of "
                + corpusCase.name() + " is not an executed expectation: " + json);
        }
        return executed;
    }

    // =========================================================================
    // 4. The class-value carrier projection
    // =========================================================================

    private static final CorpusCase POINTER_CASE =
        new CorpusCase("020-ffi-pointer-token");

    private static void testClassCarrierProjection() throws Exception {
        System.out.println("-- the class-value carrier projection: the chunk "
            + "shape at the cell, the fresh wrapper-facing copy, and the "
            + "chunk-facing return projection --");
        Fixture fixture = compileCorpus(POINTER_CASE);
        Path out = fixture.root().resolve("out-prod");
        try {
            Artifact emitted = emitAndPublish(fixture, out);
            String artifact = emitted.text();

            // The real loaded surface, observed through spies around the
            // loaded wrappers: the wrapper sees the runtime representation
            // with the pointer carried, the program's value stays the
            // chunk representation and is re-projected per crossing.
            Files.writeString(out.resolve("projection-probe.lua"),
                projectionProbe(emitted.name()), StandardCharsets.UTF_8);
            ProcessOutcome spy = runProcess(
                List.of("luajit", "projection-probe.lua"), out,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(spy.exitCode() == 0 && spy.stdout().contains("PROBE-OK"),
                "the wrapper-facing projection drive passes: exit="
                    + spy.exitCode() + " stdout=" + escaped(spy.stdout())
                    + " stderr=" + escaped(spy.stderr()));

            // The chunk-side boundary of the program's own value requires
            // the chunk representation (__c + __id), so the drive's success
            // proves the wrapper-to-chunk projection ran.
            check(artifact.contains("__bcheck(\"" + HANDLE_DESC
                    + "\", \"class\", "),
                "the chunk-side class boundary requires the chunk shape");

            // The emitted cells and projections, driven directly on the
            // artifact's own prelude: the class parameter cell accepts the
            // chunk shape and fails every other value with the pinned E8010
            // text (never E8001); the projections allocate fresh values.
            Files.writeString(out.resolve("cell-probe.lua"),
                cellProbe(emitted.name(),
                    "020-ffi-pointer-token"), StandardCharsets.UTF_8);
            ProcessOutcome cells = runProcess(
                List.of("luajit", "cell-probe.lua"), out, Map.of());
            check(cells.exitCode() == 0,
                "the emitted-cell drive runs: exit=" + cells.exitCode() + " "
                    + escaped(cells.stderr()));
            if (cells.exitCode() == 0) {
                Map<String, String> lines = probeLines(cells.stdout());
                checkEq("OK", lines.get("param-chunk"),
                    "the class parameter cell accepts the chunk representation");
                checkEq("OK", lines.get("param-chunk-identity"),
                    "the accepted value is the program's own value, unchanged");
                checkEq("E8010;" + HANDLE_DESC + ";@src.app/Box",
                    lines.get("param-wrong-identity"),
                    "a class value of another identity fails E8010 with the "
                        + "carried identity");
                check(lines.get("param-wrong-identity-message") != null
                        && lines.get("param-wrong-identity-message").startsWith(
                            "parameter 1 type mismatch: expected instance of "
                                + HANDLE_DESC + ", got @src.app/Box"),
                    "the wrong-identity message carries both identities: "
                        + lines.get("param-wrong-identity-message"));
                checkEq("E8010;" + HANDLE_DESC + ";number",
                    lines.get("param-non-class"),
                    "a non-class value fails E8010 with the kind token");
                checkEq("parameter 1 type mismatch: expected class instance",
                    lines.get("param-non-class-message"),
                    "the non-class message is the pinned class-instance text");
                checkEq("E8010;" + HANDLE_DESC + ";null",
                    lines.get("param-null"),
                    "an absent value at a class position fails E8010, never a "
                        + "null mapping");
                checkEq("OK", lines.get("param-int"),
                    "a non-class position keeps the landed cell");
                checkEq("E8010;int;string", lines.get("param-int-mismatch"),
                    "a non-class mismatch keeps the landed E8010 projection");
                checkEq("OK", lines.get("param-runtime-shape"),
                    "the cell also accepts the wrapper-facing representation");
                checkEq("OK", lines.get("return-chunk"),
                    "the return cell accepts the chunk representation");
                checkEq("E8010;" + HANDLE_DESC + ";@src.app/Box",
                    lines.get("return-wrong-identity"),
                    "the return cell rejects a foreign identity");
                checkEq("fresh", lines.get("project-fresh"),
                    "the chunk-to-wrapper projection allocates a fresh value");
                checkEq("class;" + HANDLE_DESC, lines.get("project-shape"),
                    "the projection carries the declared identity text");
                checkEq("ptr-carried", lines.get("project-ptr"),
                    "the projection carries the token's pointer");
                checkEq("source-unchanged", lines.get("project-source"),
                    "the projection mutates neither input");
                checkEq("pass-through", lines.get("project-runtime"),
                    "an already wrapper-facing value passes through");
                checkEq("fields", lines.get("deal-fields"),
                    "the wrapper-to-chunk projection takes the runtime "
                        + "instance's own field set");
                checkEq("pass-through", lines.get("deal-chunk"),
                    "an already chunk-facing value passes through");
                checkEq("guard", lines.get("deal-guard"),
                    "a foreign wrapper identity fails the projection closed");
                checkEq("nested", lines.get("deal-nested"),
                    "a nested pointer field is projected by the same rule");
                checkEq("nested", lines.get("project-nested"),
                    "the outbound nested pointer field is projected too");
                check(!cells.stdout().contains("E8001"),
                    "the class-typed cells emit no E8001 projection");
            }

            // No null mapping and no conversion code inside the bridge.
            String prelude = artifact.substring(
                artifact.indexOf("local function __hostClassIdOf("),
                artifact.indexOf("local function __hostFnParam("));
            check(!prelude.contains("__NULL"),
                "the class-value bridge carries no null mapping");
            check(!prelude.contains("ffi.") && !prelude.contains("__rt.check_type"),
                "the class-value bridge performs no ABI conversion and no "
                    + "runtime matcher call");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The wrapper-facing projection probe of one artifact. */
    private static String projectionProbe(String artifactName) {
        return """
            package.path = "./?.lua;./std/?.lua;" .. package.path
            local rt = require("deal.runtime")
            local seen = {args = {}}
            local realLoader = rt.load_ffi
            rt.load_ffi = function(...)
              local surface = realLoader(...)
              local rawNew = surface["ffi_handle_new"].f
              surface["ffi_handle_new"].f = function(...)
                local raw = rawNew(...)
                seen.raw = raw
                return raw
              end
              local rawValue = surface["ffi_handle_value"].f
              surface["ffi_handle_value"].f = function(value, ...)
                seen.args[#seen.args + 1] = value
                return rawValue(value, ...)
              end
              local rawFree = surface["ffi_handle_free"].f
              surface["ffi_handle_free"].f = function(value, ...)
                seen.args[#seen.args + 1] = value
                return rawFree(value, ...)
              end
              return surface
            end
            local surface = dofile("%s")
            local ok, err = __dealMain()
            if not ok then
              print("PROBE-FAIL|" .. tostring(err and err.code) .. "|"
                .. tostring(err and err.m))
              os.exit(1)
            end
            local function fail(message)
              print("PROBE-FAIL|" .. message)
              os.exit(1)
            end
            if seen.raw == nil or seen.raw.__kind ~= "class"
                or seen.raw.__classname ~= "%s"
                or seen.raw.__ptr == nil or seen.raw.__c ~= nil then
              fail("the loaded wrapper did not return the runtime shape")
            end
            if #seen.args ~= 2 then fail("the crossings did not run twice") end
            for i, arg in ipairs(seen.args) do
              if arg == nil or arg.__kind ~= "class"
                  or arg.__classname ~= "%s" or arg.__c ~= nil
                  or arg.__f ~= nil or arg.__ptr ~= seen.raw.__ptr then
                fail("the wrapper-facing projection of argument " .. i
                  .. " is not the runtime shape with the carried pointer")
              end
            end
            if seen.args[1] == seen.args[2] then
              fail("the projections reused one wrapper-facing value")
            end
            print("PROBE-OK")
            """.formatted(artifactName, HANDLE_DESC, HANDLE_DESC);
    }

    /**
     * The emitted-cell probe: the artifact's own prelude is loaded with a
     * drive appended in the same chunk scope, so the emitted helpers run
     * unmodified. The artifact tail (the entry-surface return) is replaced
     * by the drive.
     */
    private static String cellProbe(String artifactName, String entryModule) {
        return """
            package.path = "./?.lua;./std/?.lua;" .. package.path
            local text = io.open("%s"):read("*a")
            text = text:gsub("%%s*$", "")
            local tail = 'return __exportSurfaces["%s"]'
            assert(text:sub(-#tail) == tail, "the artifact tail is the surface return")
            local probe = [==[
            local function outcome(label, ok, value)
              if not ok then
                if type(value) == "table" then
                  print(label .. "|" .. tostring(value.code) .. "|"
                    .. tostring(value.e) .. "|" .. tostring(value.a))
                  print(label .. "-message|" .. tostring(value.m))
                else
                  print(label .. "|RAW|" .. tostring(value))
                end
                return
              end
              print(label .. "|OK|")
            end
            local h = {__c = true, __id = "@$external/candidate/native/Handle",
                       __f = {}, __p = {}}
            local other = {__c = true, __id = "@src.app/Box", __f = {}, __p = {}}
            local ptr = {}
            h.__ptr = ptr
            local ok, value = pcall(__hostParamCell, "@$external/candidate/native/Handle",
              1, h, "probe:1:1")
            outcome("param-chunk", ok, value)
            if ok and value == h then print("param-chunk-identity|OK|") end
            ok, value = pcall(__hostParamCell, "@$external/candidate/native/Handle",
              1, other, "probe:1:1")
            outcome("param-wrong-identity", ok, value)
            ok, value = pcall(__hostParamCell, "@$external/candidate/native/Handle",
              1, 5, "probe:1:1")
            outcome("param-non-class", ok, value)
            ok, value = pcall(__hostParamCell, "@$external/candidate/native/Handle",
              1, nil, "probe:1:1")
            outcome("param-null", ok, value)
            ok, value = pcall(__hostParamCell, "int", 1, 5, "probe:1:1")
            outcome("param-int", ok, value)
            ok, value = pcall(__hostParamCell, "int", 1, "x", "probe:1:1")
            outcome("param-int-mismatch", ok, value)
            local runtimeShape = {__kind = "class",
              __classname = "@$external/candidate/native/Handle", __ptr = ptr}
            ok, value = pcall(__hostParamCell, "@$external/candidate/native/Handle",
              1, runtimeShape, "probe:1:1")
            outcome("param-runtime-shape", ok, value)
            ok, value = pcall(__hostReturnCell, "@$external/candidate/native/Handle",
              h, "probe:1:1", false)
            outcome("return-chunk", ok, value)
            ok, value = pcall(__hostReturnCell, "@$external/candidate/native/Handle",
              other, "probe:1:1", false)
            outcome("return-wrong-identity", ok, value)
            local projected = __hostClassProject(
              "@$external/candidate/native/Handle", h)
            print("project-fresh|" .. (projected ~= h and "fresh" or "reused") .. "|")
            print("project-shape|" .. tostring(projected.__kind) .. ";"
              .. tostring(projected.__classname) .. "|")
            print("project-ptr|" .. (projected.__ptr == ptr and "ptr-carried"
              or "lost") .. "|")
            print("project-source|" .. ((h.__kind == nil and h.__classname == nil)
              and "source-unchanged" or "mutated") .. "|")
            local again = __hostClassProject(
              "@$external/candidate/native/Handle", runtimeShape)
            print("project-runtime|" .. (again == runtimeShape and "pass-through"
              or "copied") .. "|")
            local nested = {__c = true, __id = "@$external/candidate/native/Pair",
              __f = {left = 1, handle = h}, __p = {left = true, handle = true}}
            local nestedProjected = __hostClassProject(
              "@$external/candidate/native/Pair", nested)
            print("project-nested|" .. ((nestedProjected.handle.__kind == "class"
              and nestedProjected.handle.__ptr == ptr) and "nested" or "flat") .. "|")
            local runtimeInstance = {left = 7, right = 9,
              __kind = "class", __classname = "@$external/candidate/native/Pair"}
            local dealt = __hostDealProject("@$external/candidate/native/Pair",
              runtimeInstance, "probe:1:1")
            print("deal-fields|" .. ((dealt.__c == true and dealt.__f.left == 7
              and dealt.__p.right == true and dealt.__kind == nil)
              and "fields" or "missing") .. "|")
            local dealtAgain = __hostDealProject("@$external/candidate/native/Pair",
              dealt, "probe:1:1")
            print("deal-chunk|" .. (dealtAgain == dealt and "pass-through"
              or "copied") .. "|")
            ok, value = pcall(__hostDealProject, "@$external/candidate/native/Pair",
              {__kind = "class", __classname = "@src.app/Box"}, "probe:1:1")
            print("deal-guard|" .. ((not ok and type(value) == "table"
              and value.code == "E8010") and "guard" or "accepted") .. "|")
            local nestedRuntime = {handle = runtimeShape, __kind = "class",
              __classname = "@$external/candidate/native/Pair"}
            local nestedDealt = __hostDealProject(
              "@$external/candidate/native/Pair", nestedRuntime, "probe:1:1")
            print("deal-nested|" .. ((nestedDealt.__f.handle.__c == true
              and nestedDealt.__f.handle.__ptr == ptr) and "nested" or "flat") .. "|")
            ]==]
            local chunk = assert(load(text:sub(1, #text - #tail) .. probe, "cell-probe"))
            chunk()
            """.formatted(artifactName, entryModule);
    }

    /** The probe lines of one {@code label|...} transcript. */
    private static Map<String, String> probeLines(String stdout) {
        Map<String, String> lines = new LinkedHashMap<>();
        for (String line : stdout.split("\n")) {
            int at = line.indexOf('|');
            if (at < 0) {
                continue;
            }
            String label = line.substring(0, at);
            String rest = line.substring(at + 1);
            if (rest.endsWith("|")) {
                rest = rest.substring(0, rest.length() - 1);
            }
            lines.put(label, rest.replace("|", ";"));
        }
        return lines;
    }

    // =========================================================================
    // 5. The trace identity of a class-typed crossing
    // =========================================================================

    private static void testClassCrossingTraceIdentity() throws Exception {
        System.out.println("-- one heap value per class-typed crossing: the "
            + "trace stream's class atoms are one identity --");
        Fixture fixture = compileCorpus(POINTER_CASE);
        Path out = fixture.root().resolve("out-prod");
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the pointer fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            // The traced crossings of the fixture: the ffi_handle_new CALL
            // with its return boundary, and the parameter cells of the two
            // values-passing calls.
            Map<String, SemanticOp> hostCalls = new LinkedHashMap<>();
            Map<deal.semantic.ir.OpId, SemanticOp> opsById = new LinkedHashMap<>();
            for (LoweredModuleUnit unit : project.modules().values()) {
                for (SemanticOp op : unit.ops()) {
                    opsById.put(op.opId(), op);
                }
            }
            for (SemanticOp op : opsById.values()) {
                if (op.kind() == SemanticOpKind.CALL
                        && op.payload() instanceof KindPayload.CallPayload call
                        && call.callee()
                            instanceof KindPayload.CallCallee.Static staticCallee
                        && staticCallee.binding()
                            instanceof FunctionExecutionBinding.HostFunction host) {
                    hostCalls.put(host.exportName(), op);
                }
            }
            SemanticOp newCall = hostCalls.get("ffi_handle_new");
            SemanticOp valueCall = hostCalls.get("ffi_handle_value");
            SemanticOp freeCall = hostCalls.get("ffi_handle_free");
            check(newCall != null && valueCall != null && freeCall != null,
                "the pointer fixture lowers its three host calls");
            if (newCall == null || valueCall == null || freeCall == null) {
                return;
            }
            String newReturnKey = opKey(((KindPayload.CallPayload) newCall.payload())
                .returnBoundaryOpId());
            String valueParamKey = opKey(((KindPayload.CallPayload) valueCall.payload())
                .parameterBoundaryOpIds().get(0));
            String freeParamKey = opKey(((KindPayload.CallPayload) freeCall.payload())
                .parameterBoundaryOpIds().get(0));

            String chunk = LuaSemanticEmitter.emitProject(project,
                lowered.tables(), lowered.registries(), fixture.surface());
            Files.createDirectories(out);
            Files.writeString(out.resolve("trace.lua"), chunk, StandardCharsets.UTF_8);
            Files.createDirectories(out.resolve("deal"));
            Files.copy(Path.of("deal", "runtime.lua"),
                out.resolve("deal/runtime.lua"));
            Files.writeString(out.resolve("trace-probe.lua"),
                traceProbe("trace.lua"), StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(
                List.of("luajit", "trace-probe.lua"), out,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the trace-mode FFI drive runs: exit=" + run.exitCode() + " "
                    + escaped(run.stdout()) + " " + escaped(run.stderr()));
            if (run.exitCode() != 0) {
                return;
            }
            Map<String, TraceLine> trace = parseTrace(run.stderr());
            TraceLine returnStart = trace.get(newReturnKey + "|START");
            TraceLine returnSuccess = trace.get(newReturnKey + "|SUCCESS");
            TraceLine callSuccess = trace.get(opKey(newCall.opId()) + "|SUCCESS");
            TraceLine valueStart = trace.get(valueParamKey + "|START");
            TraceLine valueSuccess = trace.get(valueParamKey + "|SUCCESS");
            TraceLine freeStart = trace.get(freeParamKey + "|START");
            TraceLine freeSuccess = trace.get(freeParamKey + "|SUCCESS");
            check(returnStart != null && valueStart != null
                    && returnStart.inputs().size() == 1,
                "the class-typed crossings carry their boundary events");
            if (returnStart == null || returnSuccess == null || callSuccess == null
                    || valueStart == null || valueSuccess == null
                    || freeStart == null || freeSuccess == null) {
                return;
            }
            String returned = returnStart.inputs().get(0);
            check(returned.startsWith("ref:"),
                "the return boundary's START atomizes a heap value: " + returned);
            checkEq(returned, returnSuccess.output(),
                "the return boundary observes one heap value");
            checkEq(returned, callSuccess.output(),
                "the published call result is that same value");
            checkEq(returned, valueStart.inputs().get(0),
                "the parameter cell sees the program's own value");
            checkEq(returned, valueSuccess.output(),
                "the parameter cell returns that value unchanged");
            checkEq(returned, freeStart.inputs().get(0),
                "the second crossing sees the same one heap value");
            checkEq(returned, freeSuccess.output(),
                "the second crossing returns that value unchanged");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** One parsed trace line: the phase and the atoms. */
    private record TraceLine(String phase, String kind, List<String> inputs,
                             String output) {
    }

    private static String opKey(deal.semantic.ir.OpId id) {
        return id.module().path() + "#" + id.id();
    }

    /** Parses the {@code T|} trace stream into op+phase keyed lines. */
    private static Map<String, TraceLine> parseTrace(String stderr) {
        Map<String, TraceLine> lines = new LinkedHashMap<>();
        for (String line : stderr.split("\n")) {
            if (!line.startsWith("T|")) {
                continue;
            }
            String[] parts = line.split("\\|", -1);
            if (parts.length < 8) {
                continue;
            }
            int outputAt = -1;
            for (int i = 8; i < parts.length; i++) {
                if (parts[i].startsWith("=>")) {
                    outputAt = i;
                    break;
                }
            }
            List<String> inputs = new ArrayList<>();
            int inputEnd = outputAt < 0 ? parts.length : outputAt;
            for (int i = 8; i < inputEnd; i++) {
                if (!parts[i].isEmpty() && !parts[i].startsWith("!")) {
                    inputs.add(parts[i]);
                }
            }
            String output = outputAt < 0 ? null
                : parts[outputAt].substring("=>".length());
            lines.put(parts[3] + "|" + parts[4],
                new TraceLine(parts[4], parts[5], inputs, output));
        }
        return lines;
    }

    /**
     * The trace-mode FFI drive: the scenario seam publishes the loaded
     * surface (the trace session's landed convention) and the deferred
     * entry walk runs the crossings.
     */
    private static String traceProbe(String artifactName) {
        return """
            package.path = "./?.lua;./std/?.lua;" .. package.path
            local ffi = require("ffi")
            local handle = ffi.new("int[1]")
            __exportSurfaces = {
              ["%s"] = {
                ffi_handle_new = {__kind = "function", sig = "(int)->%s",
                  f = function(v, file, line, column)
                    return {__kind = "class", __classname = "%s",
                            __ptr = handle}
                  end},
                ffi_handle_value = {__kind = "function", sig = "(%s)->int",
                  f = function(v, file, line, column) return 31 end},
                ffi_handle_free = {__kind = "function", sig = "(%s)->null",
                  f = function(v, file, line, column)
                    return require("deal.runtime").__NULL
                  end},
              },
            }
            local surface = dofile("%s")
            local ok, err = __dealMain()
            if not ok then
              print("PROBE-FAIL|" .. tostring(err and err.code) .. "|"
                .. tostring(err and err.m))
              os.exit(1)
            end
            print("PROBE-OK")
            """.formatted(NATIVE_DOTTED, HANDLE_DESC, HANDLE_DESC, HANDLE_DESC,
                HANDLE_DESC, artifactName);
    }

    // =========================================================================
    // The gate
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI Typed Crossing Tests (ISSUE-0663) ===");
        System.out.println();
        testScalarAndPointerDrive();
        testEmittedCrossingPositions();
        testFailureCodesAtCallExpression();
        testClassCarrierProjection();
        testClassCrossingTraceIdentity();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Typed Crossing Tests Passed ===");
    }

    // =========================================================================
    // Process and filesystem helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir,
            Map<String, String> environment) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.environment().putAll(environment);
        builder.redirectErrorStream(false);
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        return new ProcessOutcome(exit, stdout, stderr);
    }

    private static String escaped(String text) {
        return text == null ? "null" : text.replace("\n", "\\n");
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            try (Stream<Path> walk = Files.walk(dir)) {
                for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
                    Files.deleteIfExists(path);
                }
            }
        } catch (Exception e) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }
}
