package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.ValueId;
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
 * ISSUE-0665: the extern-C value-position read drive
 * ({@code luajit-ffi-load-emission-and-typed-crossings} F5 and the FFI
 * typed call and value-read contract; {@code luajit-ffi-shared-emission-and-
 * jvm-rejection} F1/F3/F5; {@code semantic-ir-construct-coverage-cutover}
 * K2; the epic's sequencing step 4).
 *
 * <ol>
 *   <li><b>The lowering shape.</b> {@code let f: (…) => … =
 *       native.<export>; f(args)} lowers through the reads child's
 *       exactly-one {@code EXPORT_READ} per source occurrence plus its
 *       exactly-one {@code HostFunction(resolvedModule, exportName,
 *       descriptor)} registration keyed by the read result's allocation
 *       identity; the invocation is the static {@code CALL(INDIRECT)}
 *       whose {@code CallCallee.Static} binding is that registration, with
 *       the closed host cells ({@code DEAL_TO_HOST}+{@code HOST_PARAMETER}
 *       per argument, {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} on the
 *       call) — identical to the direct {@code CALL(HOST)} of the same
 *       export. No {@code CallCallee.Dynamic} and no
 *       {@code HostFunctionValue} registration exists, and no site
 *       re-produces, re-registers, or re-checks the read.</li>
 *   <li><b>The production artifact under luajit.</b> The corpus
 *       declaration {@code candidate/native} compiles through the
 *       production arm with the corpus's production FFI metadata and the
 *       artifact executes under {@code luajit} with the pinned
 *       {@code runtime-ok} transcript; the artifact publishes the loaded
 *       table through the emitted {@code __rt.load_ffi} prelude (T1) and
 *       the read publishes that loaded surface entry
 *       ({@code __exportHostValue}), which the indirect call resolves
 *       through the loaded wrapper's {@code .f} convention. A spy
 *       installed on the loaded entry observes exactly the invocation,
 *       so the surface is resolved through the load and never
 *       re-materialized; a torn load (the load line removed) fails
 *       loudly, never silently.</li>
 *   <li><b>The failing export.</b> A value-position read of a failing
 *       export (the corpus {@code ffi_null_string}) keeps the pinned
 *       code, message, and the call-expression origin, and the direct
 *       call of the same export produces the identical code and
 *       message.</li>
 *   <li><b>The oracle.</b> Both drives execute through the oracle's seamed
 *       host surface with the same call arguments, effects, outcomes, and
 *       (for the failure) origin as the artifact.</li>
 *   <li><b>The declaration negatives.</b> An async extern-C declaration
 *       stays a compile-time E7002 rejection (the corpus
 *       {@code candidate/invalid-async} companion), and the drive closure
 *       carries no async start and no dynamic callee.</li>
 * </ol>
 */
public class FfiValueReadInvocationTest {

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

    public static void main(String[] args) throws Exception {
        testLoweringShape();
        testDirectCallParity();
        testProductionDriveAndSpy();
        testFailingExport();
        testOracleParity();
        testAsyncDeclarationNegative();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Value-Position Read Invocation Tests Passed ===");
    }

    // =========================================================================
    // The corpus surface
    // =========================================================================

    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String FFI_SPECIFIER = "candidate/native";
    private static final String FFI_DOTTED = "candidate.native";
    private static final String FFI_MODULE_KEY = "ffi:@$external/candidate/native";

    /** The declared scalar exports the value-position drive reads. */
    private static final List<String> SCALAR_EXPORTS = List.of(
        "ffi_add", "ffi_half", "ffi_not", "ffi_echo", "ffi_identity_int",
        "ffi_noop");

    // =========================================================================
    // The drive sources
    // =========================================================================

    /**
     * The value-position drive: every scalar corpus export is read into a
     * typed binding first and invoked through that binding, and each
     * result is checked. {@code main} delegates to {@code test_read}, so
     * the plain production run exercises the whole drive (the pinned
     * {@code runtime-ok} transcript) and the spy probe can invoke the
     * same export a second time against a spied loaded entry.
     */
    private static final String VALUE_READ_SOURCE = """
        import * as native from "candidate/native";

        export function test_read(): null {
          let add: (a: int, b: int) => int = native.ffi_add;
          let half: (value: number) => number = native.ffi_half;
          let negate: (value: boolean) => boolean = native.ffi_not;
          let echo: (value: string) => string = native.ffi_echo;
          let identity: (value: int) => int = native.ffi_identity_int;
          let noop: () => null = native.ffi_noop;
          if (add(20, 22) !== 42) {
            throw { code: "TEST_FAIL", message: "ffi_add value-position read" };
          }
          if (half(5.0) !== 2.5) {
            throw { code: "TEST_FAIL", message: "ffi_half value-position read" };
          }
          if (!negate(false)) {
            throw { code: "TEST_FAIL", message: "ffi_not value-position read" };
          }
          if (echo("hello") !== "hello") {
            throw { code: "TEST_FAIL", message: "ffi_echo value-position read" };
          }
          if (identity(-2147483648) !== -2147483648) {
            throw { code: "TEST_FAIL", message: "ffi_identity_int value-position read" };
          }
          if (noop() !== null) {
            throw { code: "TEST_FAIL", message: "ffi_noop value-position read" };
          }
          return null;
        }

        export function main(): null {
          return test_read();
        }
        """;

    /** The direct-call companion of the same scalar exports. */
    private static final String DIRECT_CALL_SOURCE = """
        import * as native from "candidate/native";

        export function main(): null {
          if (native.ffi_add(20, 22) !== 42) {
            throw { code: "TEST_FAIL", message: "ffi_add direct call" };
          }
          if (native.ffi_half(5.0) !== 2.5) {
            throw { code: "TEST_FAIL", message: "ffi_half direct call" };
          }
          if (!native.ffi_not(false)) {
            throw { code: "TEST_FAIL", message: "ffi_not direct call" };
          }
          if (native.ffi_echo("hello") !== "hello") {
            throw { code: "TEST_FAIL", message: "ffi_echo direct call" };
          }
          if (native.ffi_identity_int(-2147483648) !== -2147483648) {
            throw { code: "TEST_FAIL", message: "ffi_identity_int direct call" };
          }
          if (native.ffi_noop() !== null) {
            throw { code: "TEST_FAIL", message: "ffi_noop direct call" };
          }
          return null;
        }
        """;

    /**
     * The failing value-position reads: the read then the call raise at the
     * call expression (one per inbound conversion direction).
     */
    private static final String FAILING_NULL_READ_SOURCE = """
        import * as native from "candidate/native";

        export function main(): null {
          let f: () => string = native.ffi_null_string;
          let value: string = f();
          return null;
        }
        """;

    /** The failing direct call of the same export (the texts/parity companion). */
    private static final String FAILING_NULL_DIRECT_SOURCE = """
        import * as native from "candidate/native";

        export function main(): null {
          let value: string = native.ffi_null_string();
          return null;
        }
        """;

    /** The invalid-UTF-8 value-position read (the second pinned failure code). */
    private static final String FAILING_UTF8_READ_SOURCE = """
        import * as native from "candidate/native";

        export function main(): null {
          let f: () => string = native.ffi_invalid_utf8;
          let value: string = f();
          return null;
        }
        """;

    /** The failing direct call of the invalid-UTF-8 export. */
    private static final String FAILING_UTF8_DIRECT_SOURCE = """
        import * as native from "candidate/native";

        export function main(): null {
          let value: string = native.ffi_invalid_utf8();
          return null;
        }
        """;

    /**
     * One pinned failing export: the value-position source, its direct-call
     * companion (the same export called directly), the corpus sidecar that
     * pins the code/message, and the two call-expression snippets.
     */
    private record FailureCase(String exportName, String readSource,
            String directSource, String sidecar, String readCallSnippet,
            String directCallSnippet) {
    }

    private static final List<FailureCase> FAILURE_CASES = List.of(
        new FailureCase("ffi_null_string", FAILING_NULL_READ_SOURCE,
            FAILING_NULL_DIRECT_SOURCE, "022-ffi-null-string.expect.json",
            "f()", "native.ffi_null_string()"),
        new FailureCase("ffi_invalid_utf8", FAILING_UTF8_READ_SOURCE,
            FAILING_UTF8_DIRECT_SOURCE, "023-ffi-invalid-utf8.expect.json",
            "f()", "native.ffi_invalid_utf8()"));

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
        Path root,
        Path sourceRoot,
        String entryName,
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

    /** Compiles one synthetic app against the corpus declaration. */
    private static Fixture compile(String entryName, String appSource)
            throws Exception {
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT,
            FFI_SPECIFIER);
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + FFI_SPECIFIER + "'");
        }
        String declaration = Files.readString(CONFORMANCE_ROOT
            .resolve(CorpusFfi.FFI_DIR).resolve(wiring.declarationCorpusPath()),
            StandardCharsets.UTF_8);
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT,
            FFI_SPECIFIER, SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException("the corpus declaration of '"
                + FFI_SPECIFIER + "' does not validate: "
                + module.validationDiagnostics());
        }
        Path root = Files.createTempDirectory("ffi-value-read");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("native.d.deal"),
            ConformanceHarnessMetadata.stripClassificationHeaders(declaration),
            StandardCharsets.UTF_8);
        Files.writeString(src.resolve(entryName + ".deal"),
            ConformanceHarnessMetadata.stripClassificationHeaders(appSource),
            StandardCharsets.UTF_8);
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(FFI_SPECIFIER,
            src.resolve("native.d.deal").toAbsolutePath().toString());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(entryName + ".deal").toAbsolutePath(),
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
            throw new IllegalStateException("the FFI value-read fixture '"
                + entryName + "' did not build: " + detail + " / "
                + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        externCModules.put(new ModuleId(FFI_DOTTED), module.generatedModule());
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(FFI_SPECIFIER));
        }
        return new Fixture(root, src, entryName, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            externCModules, identities);
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

    /** Runs the production arm and publishes its one staged artifact. */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Path out) throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        try {
            ProductionProjectEmission.Result result =
                ProductionProjectEmission.run(productionInvocation(),
                    fixture.checkedProject(), fixture.index(), fixture.manifests(),
                    fixture.surface(), fixture.declarationIdentities(),
                    fixture.externCModules(), fixture.sourceRoot().toString(),
                    BuiltinErrorDeclaration.synthesized(
                        fixture.checkedProject().modules().get(0).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT,
                        IntrinsicKind.NUMBER_CONVERT),
                    Set.of(), Backend.LUAJIT, false,
                    deal.distribution.DistributionHome.forManifestDirectory(
                        fixture.sourceRoot().toString()),
                    stager);
            if (result.emitted()) {
                stager.publish();
            }
            return result;
        } finally {
            stager.discard();
        }
    }

    // =========================================================================
    // The IR readers
    // =========================================================================

    private static LoweredModuleUnit entryUnit(ExecutableLoweredProject project) {
        return project.modules().get(project.entryModule());
    }

    private static List<SemanticOp> opsOfKind(LoweredModuleUnit unit,
            SemanticOpKind kind) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                ops.add(op);
            }
        }
        return ops;
    }

    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit,
            ValueId value) {
        return unit.functionBindings().get(
            new FunctionAllocationIdentity(value.id()));
    }

    /** The unit's import registrations (HostFunction/ExternalFunction). */
    private static List<FunctionExecutionBinding> importRegistrations(
            LoweredModuleUnit unit) {
        List<FunctionExecutionBinding> imports = new ArrayList<>();
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.HostFunction
                    || binding instanceof FunctionExecutionBinding.ExternalFunction) {
                imports.add(binding);
            }
        }
        return imports;
    }

    private static boolean carriesDynamicCallee(ExecutableLoweredProject project) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                KindPayload payload = op.payload();
                if (payload instanceof KindPayload.CallPayload call
                        && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                    return true;
                }
                if (payload instanceof KindPayload.AsyncStartPayload start
                        && start.callee() instanceof KindPayload.CallCallee.Dynamic) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The unit's host CALL ops that consume a transferred binding. */
    private static List<SemanticOp> hostCallsOf(LoweredModuleUnit unit,
            String exportName) {
        List<SemanticOp> calls = new ArrayList<>();
        for (SemanticOp op : opsOfKind(unit, SemanticOpKind.CALL)) {
            KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
            if (!(payload.callee() instanceof KindPayload.CallCallee.Static staticCallee)) {
                continue;
            }
            if (staticCallee.binding() instanceof FunctionExecutionBinding.HostFunction host
                    && host.exportName().equals(exportName)) {
                calls.add(op);
            }
        }
        return calls;
    }

    /** The declared cell descriptors+policies of one export's invocation. */
    private static List<String> cellSignature(LoweredModuleUnit unit,
            String exportName) {
        List<String> cells = new ArrayList<>();
        for (SemanticOp call : hostCallsOf(unit, exportName)) {
            KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
            cells.add("binding=" + ((KindPayload.CallCallee.Static) payload.callee())
                .binding() + " signature=" + payload.signature().canonicalSpecText());
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = unit.ops().stream()
                    .filter(candidate -> candidate.opId().equals(boundaryId))
                    .findFirst().orElseThrow();
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                cells.add("param " + boundaryPayload.descriptor().canonicalSpecText()
                    + " " + boundaryPayload.kind() + " " + boundary.failurePolicy());
            }
            SemanticOp returnBoundary = unit.ops().stream()
                .filter(candidate -> candidate.opId().equals(
                    payload.returnBoundaryOpId()))
                .findFirst().orElse(null);
            if (returnBoundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnBoundary.payload();
                cells.add("return " + boundaryPayload.descriptor().canonicalSpecText()
                    + " " + boundaryPayload.kind()
                    + " " + returnBoundary.failurePolicy());
            }
        }
        return cells;
    }

    private static int occurrences(String text, String needle) {
        int count = 0;
        for (int at = text.indexOf(needle); at >= 0;
                at = text.indexOf(needle, at + needle.length())) {
            count++;
        }
        return count;
    }

    private static String lineOf(String source, int oneBasedLine) {
        String[] lines = source.split("\n", -1);
        return oneBasedLine >= 1 && oneBasedLine <= lines.length
            ? lines[oneBasedLine - 1] : "";
    }

    /** The one-based line:column of a snippet's first occurrence. */
    private static int[] originOf(String source, String snippet) {
        int at = source.indexOf(snippet);
        if (at < 0) {
            throw new IllegalStateException("the source carries no '" + snippet + "'");
        }
        int line = 1;
        int lineStart = 0;
        for (int i = 0; i < at; i++) {
            if (source.charAt(i) == '\n') {
                line++;
                lineStart = i + 1;
            }
        }
        return new int[] {line, at - lineStart + 1};
    }

    // =========================================================================
    // 1. The lowering shape
    // =========================================================================

    private static void testLoweringShape() throws Exception {
        System.out.println("-- the value-position read: one EXPORT_READ and one "
            + "HostFunction registration per occurrence, consumed by the static "
            + "CALL(INDIRECT) --");
        Fixture fixture = compile("app", VALUE_READ_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the value-position drive lowers: " + result.diagnostics());
                return;
            }
            checkEq(1, result.project().modules().size(),
                "the drive lowers and validates the one entry unit (the extern-C "
                    + "declaration lowers as the host-shaped import)");
            ExecutableLoweredProject project = result.project();
            check(!carriesDynamicCallee(project),
                "the value-position drive produces no CallCallee.Dynamic shape "
                    + "(the read's HostFunction registration is statically consumed)");
            LoweredModuleUnit unit = entryUnit(project);

            List<SemanticOp> reads = opsOfKind(unit, SemanticOpKind.EXPORT_READ);
            checkEq(SCALAR_EXPORTS.size(), reads.size(),
                "the drive carries exactly one EXPORT_READ per read occurrence");
            checkEq(0, unit.functionBindings().values().stream()
                    .filter(binding -> binding
                        instanceof FunctionExecutionBinding.HostFunctionValue)
                    .toList().size(),
                "no HostFunctionValue registration exists (the read consumer is the "
                    + "static HostFunction registration)");

            Map<String, FunctionExecutionBinding> readBindings = new LinkedHashMap<>();
            for (SemanticOp read : reads) {
                KindPayload.ExportReadPayload payload =
                    (KindPayload.ExportReadPayload) read.payload();
                checkEq(FFI_DOTTED, payload.module().path(),
                    "the read names the loaded extern-C module");
                FunctionExecutionBinding binding = bindingOf(unit, payload.value());
                check(binding instanceof FunctionExecutionBinding.HostFunction host
                        && host.hostModuleId().equals(payload.module())
                        && host.exportName().equals(payload.name())
                        && host.descriptor().equals(payload.descriptor()),
                    "exactly one HostFunction(resolved module, export, descriptor) "
                        + "registration is keyed by the read result's allocation "
                        + "identity for '" + payload.name() + "'; got " + binding);
                readBindings.put(payload.name(), binding);
            }
            checkEq(Set.copyOf(SCALAR_EXPORTS), readBindings.keySet(),
                "the reads name the corpus scalar exports");

            List<FunctionExecutionBinding> registrations = importRegistrations(unit);
            checkEq(SCALAR_EXPORTS.size(), registrations.size(),
                "the drive carries exactly one import registration per read and "
                    + "nothing else (no re-registration); got " + registrations);

            int consumed = 0;
            for (String exportName : SCALAR_EXPORTS) {
                List<SemanticOp> calls = hostCallsOf(unit, exportName);
                checkEq(1, calls.size(), "the read of '" + exportName
                    + "' is invoked exactly once through its registration");
                if (calls.size() != 1) {
                    continue;
                }
                SemanticOp call = calls.get(0);
                KindPayload.CallPayload payload =
                    (KindPayload.CallPayload) call.payload();
                checkEq(CallMode.INDIRECT, payload.mode(),
                    "the read invocation '" + exportName + "' is CALL(INDIRECT)");
                checkEq(readBindings.get(exportName), payload.callee()
                        instanceof KindPayload.CallCallee.Static staticCallee
                            ? staticCallee.binding() : null,
                    "the invocation of '" + exportName + "' consumes exactly the "
                        + "read's registration (never a re-materialized read)");
                consumed++;
                RuntimeDescriptor.Func descriptor =
                    (RuntimeDescriptor.Func) ((FunctionExecutionBinding.HostFunction)
                        readBindings.get(exportName)).descriptor();
                checkEq(descriptor.paramTypes().size(),
                    payload.parameterBoundaryOpIds().size(),
                    "the invocation of '" + exportName
                        + "' carries one parameter boundary per declared parameter");
                for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                    SemanticOp boundary = unit.ops().stream()
                        .filter(candidate -> candidate.opId().equals(boundaryId))
                        .findFirst().orElseThrow();
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) boundary.payload();
                    checkEq(BoundaryKind.DEAL_TO_HOST,
                        boundaryPayload.kind(),
                        "the parameter cell of '" + exportName
                            + "' is the host DEAL_TO_HOST boundary");
                    checkEq(FailurePolicyId.HOST_PARAMETER,
                        boundary.failurePolicy(),
                        "the parameter cell of '" + exportName
                            + "' carries the HOST_PARAMETER policy");
                }
                SemanticOp returnBoundary = unit.ops().stream()
                    .filter(candidate -> candidate.opId().equals(
                        payload.returnBoundaryOpId()))
                    .findFirst().orElse(null);
                check(returnBoundary != null,
                    "the invocation of '" + exportName + "' carries its return cell");
                if (returnBoundary != null) {
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) returnBoundary.payload();
                    checkEq(BoundaryKind.HOST_TO_DEAL,
                        boundaryPayload.kind(),
                        "the return cell of '" + exportName
                            + "' is the host HOST_TO_DEAL boundary");
                    checkEq(FailurePolicyId.HOST_SYNC_RETURN,
                        returnBoundary.failurePolicy(),
                        "the return cell of '" + exportName
                            + "' carries the HOST_SYNC_RETURN policy");
                }
            }
            checkEq(SCALAR_EXPORTS.size(), consumed,
                "every read is consumed exactly once by its invocation");
            for (SemanticOp op : unit.ops()) {
                check(op.kind() != SemanticOpKind.ASYNC_START,
                    "the extern-C drive carries no ASYNC_START (async declarations "
                        + "never lower)");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The direct-call parity
    // =========================================================================

    private static void testDirectCallParity() throws Exception {
        System.out.println("-- the value-position read's cells match the direct "
            + "CALL(HOST) cells, and both resolve the one loaded surface entry --");
        Fixture read = compile("app", VALUE_READ_SOURCE);
        Fixture direct = compile("app", DIRECT_CALL_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult readResult = lower(read);
            SemanticLowerer.ProjectLoweringResult directResult = lower(direct);
            if (readResult.project() == null || directResult.project() == null) {
                fail("the parity fixtures lower: " + readResult.diagnostics()
                    + " / " + directResult.diagnostics());
                return;
            }
            LoweredModuleUnit readUnit = entryUnit(readResult.project());
            LoweredModuleUnit directUnit = entryUnit(directResult.project());
            for (String exportName : SCALAR_EXPORTS) {
                checkEq(cellSignature(directUnit, exportName),
                    cellSignature(readUnit, exportName),
                    "the value-position read of '" + exportName
                        + "' carries the direct call's cells (descriptors and "
                        + "policies)");
            }

            Path readOut = read.root().resolve("out-read");
            Path directOut = direct.root().resolve("out-direct");
            ProductionProjectEmission.Result readEmission = emit(read, readOut);
            ProductionProjectEmission.Result directEmission = emit(direct, directOut);
            check(readEmission.emitted() && directEmission.emitted(),
                "both parity fixtures emit: " + readEmission.diagnostics() + " / "
                    + directEmission.diagnostics());
            if (!readEmission.emitted() || !directEmission.emitted()) {
                return;
            }
            String readLua = Files.readString(readOut.resolve("app.lua"),
                StandardCharsets.UTF_8);
            String directLua = Files.readString(directOut.resolve("app.lua"),
                StandardCharsets.UTF_8);
            for (String exportName : SCALAR_EXPORTS) {
                String target = "pcall(__exportSurfaces[\"" + FFI_DOTTED + "\"][\""
                    + exportName + "\"].f";
                checkEq(1, occurrences(readLua, target),
                    "the value-position invocation of '" + exportName
                        + "' resolves the loaded surface entry through the wrapper's "
                        + ".f convention");
                checkEq(1, occurrences(directLua, target),
                    "the direct call of '" + exportName
                        + "' resolves the same loaded surface entry");
                checkEq(1, occurrences(readLua, "= __exportHostValue(\""
                        + FFI_DOTTED + "\", \"" + exportName + "\")"),
                    "the read of '" + exportName
                        + "' publishes the loaded surface entry once");
            }
            checkEq(occurrences(readLua, "__rt.load_ffi("),
                occurrences(directLua, "__rt.load_ffi("),
                "both forms emit the same single FFI load");
            checkEq(1, occurrences(readLua, "__rt.load_ffi("),
                "the extern-C module loads exactly once per program");
        } finally {
            deleteRecursively(read.root());
            deleteRecursively(direct.root());
        }
    }

    // =========================================================================
    // 3. The production artifact, the load, and the spy
    // =========================================================================

    private static void testProductionDriveAndSpy() throws Exception {
        System.out.println("-- the drive executes the production artifact under "
            + "luajit through the emitted load_ffi surface (T1) --");
        Fixture fixture = compile("app", VALUE_READ_SOURCE);
        Path out = fixture.root().resolve("out-prod");
        try {
            ProductionProjectEmission.Result result = emit(fixture, out);
            check(result.emitted(),
                "the FFI value-position drive emits one project artifact: "
                    + result.diagnostics());
            if (!result.emitted()) {
                return;
            }
            checkEq("app.lua", result.artifactRelativePath(),
                "the one project artifact is named for the entry module");
            String artifact = Files.readString(out.resolve("app.lua"),
                StandardCharsets.UTF_8);

            // T1: the emitted load carries the compile's generated metadata
            // and the import statement's span; the drive's surface is the
            // loaded table, never a seeded substitute.
            check(artifact.contains("__exportSurfaces[\"" + FFI_DOTTED + "\"] = "
                    + "__exportSurfaces[\"" + FFI_DOTTED + "\"] or "
                    + "__rt.load_ffi(\"" + FFI_MODULE_KEY + "\", "
                    + "{ bundleDigest = \""),
                "the artifact publishes the loaded table through the load_ffi "
                    + "prelude with the generated module key and bundle");
            check(artifact.contains("local __ffi_bindings_1 = { moduleKey = \""
                    + FFI_MODULE_KEY + "\","),
                "the bindings literal comes from the generated metadata");
            check(artifact.contains("nativeLibrary = { kind = \"ABSOLUTE_PATH\", "
                    + "loaderText = \""),
                "the bundle literal carries the loaded native-library text");
            check(artifact.contains(", \"" + fixture.sourceRoot().resolve("app.deal")
                    .toAbsolutePath() + "\", 1, 1)"),
                "the load carries the import statement's span triplet");
            check(!artifact.contains("require(\"candidate"),
                "no provider require line is emitted");
            check(!artifact.contains("ffi.C") && !artifact.contains("cdef("),
                "the artifact carries no ffi.C/cdef text");
            checkEq(1, occurrences(artifact, "__rt.load_ffi("),
                "the extern-C module loads exactly once per program");

            // The runtime-ok transcript of the corpus declaration's loaded
            // surface: the drive runs to completion with no output.
            ProcessOutcome plainRun = runProcess(List.of("luajit", "app.lua"), out);
            check(plainRun.exitCode() == 0 && plainRun.stdout().isEmpty()
                    && plainRun.stderr().isEmpty(),
                "the drive executes the artifact under luajit with the pinned "
                    + "runtime-ok transcript: exit=" + plainRun.exitCode()
                    + " stdout=" + escaped(plainRun.stdout())
                    + " stderr=" + escaped(plainRun.stderr()));

            // The spy: the loaded surface entry is what the read publishes
            // and the invocation resolves, at execution time.
            Files.writeString(out.resolve("spy.lua"), """
                local chunk = dofile("app.lua")
                local ok, err = __dealMain()
                if not ok then
                  print("PROBE-FAIL|init|" .. tostring(err.code or err.m or err))
                  os.exit(1)
                end
                local entry = __exportSurfaces["candidate.native"]["ffi_add"]
                if type(entry) ~= "table" or type(entry.f) ~= "function" then
                  print("PROBE-FAIL|no loaded entry")
                  os.exit(1)
                end
                local calls = 0
                local realF = entry.f
                entry.f = function(...)
                  calls = calls + 1
                  return realF(...)
                end
                local test = __exportSurfaces["app"]["test_read"]
                if type(test) ~= "table" or type(test.f) ~= "function" then
                  print("PROBE-FAIL|no test export")
                  os.exit(1)
                end
                local ok2, err2 = pcall(test.f)
                if not ok2 then
                  print("PROBE-FAIL|read|" .. tostring(err2.code or err2.m
                    or err2.message or err2))
                  os.exit(1)
                end
                if calls ~= 1 then
                  print("PROBE-FAIL|calls=" .. calls)
                  os.exit(1)
                end
                print("PROBE-OK")
                """, StandardCharsets.UTF_8);
            ProcessOutcome spyRun = runProcess(List.of("luajit", "spy.lua"), out,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(spyRun.exitCode() == 0 && spyRun.stdout().contains("PROBE-OK"),
                "the read publishes the loaded surface entry and the invocation "
                    + "resolves that same entry (the spy observed exactly one "
                    + "call): exit=" + spyRun.exitCode() + " stdout="
                    + escaped(spyRun.stdout()) + " stderr="
                    + escaped(spyRun.stderr()));

            // A torn load fails loudly: the read resolves no entry and the
            // declared row rejects the missing value instead of a silent
            // call.
            String torn = artifact.replace(
                "__exportSurfaces[\"" + FFI_DOTTED + "\"] = "
                    + "__exportSurfaces[\"" + FFI_DOTTED + "\"] or "
                    + "__rt.load_ffi(", "__tornFFILoad = __rt.load_ffi(");
            check(!torn.equals(artifact), "the torn-load seed replaces the load");
            if (!torn.equals(artifact)) {
                Files.writeString(out.resolve("torn.lua"), torn,
                    StandardCharsets.UTF_8);
                ProcessOutcome tornRun = runProcess(List.of("luajit", "torn.lua"),
                    out);
                checkEq(1, tornRun.exitCode(),
                    "a drive whose load is broken exits with a failure");
                checkEq("DEAL_ERROR_CODE: E8001\n", tornRun.stdout(),
                    "the broken load surfaces the read's missing-entry row "
                        + "loudly instead of a silent call: stderr="
                        + escaped(tornRun.stderr()));
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The failing export
    // =========================================================================

    private static void testFailingExport() throws Exception {
        System.out.println("-- a failing export keeps the pinned code, text, and "
            + "the call-expression origin in value position --");
        for (FailureCase failureCase : FAILURE_CASES) {
            SidecarExpectations.ErrorExpectation pinned =
                pinnedError(failureCase.sidecar());
            Fixture read = compile("app", failureCase.readSource());
            Path readOut = read.root().resolve("out-read");
            try {
                ProductionProjectEmission.Result result = emit(read, readOut);
                check(result.emitted(), "the failing value-position drive of '"
                    + failureCase.exportName() + "' emits: "
                    + result.diagnostics());
                if (result.emitted()) {
                    check(readOut.resolve("app.lua").toFile().isFile(),
                        "the failing drive stages its one project artifact");
                    ProcessOutcome run = runProcess(List.of("luajit", "app.lua"),
                        readOut);
                    checkEq(1, run.exitCode(), "the failing value-position drive of '"
                        + failureCase.exportName() + "' exits 1");
                    checkEq("DEAL_ERROR_CODE: " + pinned.code() + "\n",
                        run.stdout(),
                        "the failing drive publishes the pinned DEAL_ERROR_CODE "
                            + "terminal");
                    check(run.stderr().isEmpty(),
                        "the failing drive writes no stderr: "
                            + escaped(run.stderr()));

                    int[] origin = originOf(failureCase.readSource(),
                        failureCase.readCallSnippet());
                    check(lineOf(failureCase.readSource(), origin[0])
                            .contains(failureCase.readCallSnippet()),
                        "the expected origin is the call expression");
                    Files.writeString(readOut.resolve("probe.lua"),
                        failureProbe("app.lua"), StandardCharsets.UTF_8);
                    ProcessOutcome probe = runProcess(List.of("luajit", "probe.lua"),
                        readOut, Map.of("DEAL_DEFER_MAIN", "1"));
                    check(probe.exitCode() == 0 && probe.stdout().startsWith("ERR|"),
                        "the failing drive's error probe runs: "
                            + escaped(probe.stdout()) + escaped(probe.stderr()));
                    String[] parts = probe.stdout().trim().split("\\|", -1);
                    if (parts.length >= 4 && "ERR".equals(parts[0])) {
                        checkEq(pinned.code(), parts[1],
                            "the value-position failure of '"
                                + failureCase.exportName()
                                + "' keeps the pinned code");
                        checkEq(pinned.message(), parts[2],
                            "the value-position failure of '"
                                + failureCase.exportName()
                                + "' keeps the pinned message");
                        checkEq(read.sourceRoot().resolve("app.deal")
                                .toAbsolutePath() + ":" + origin[0] + ":"
                                + origin[1], parts[3],
                            "the value-position failure of '"
                                + failureCase.exportName()
                                + "' carries the call-expression origin");
                    } else {
                        fail("the failing drive's probe output is malformed: "
                            + escaped(probe.stdout()));
                    }
                }
            } finally {
                deleteRecursively(read.root());
            }

            Fixture direct = compile("app", failureCase.directSource());
            Path directOut = direct.root().resolve("out-direct");
            try {
                ProductionProjectEmission.Result result = emit(direct, directOut);
                check(result.emitted(), "the failing direct drive of '"
                    + failureCase.exportName() + "' emits: "
                    + result.diagnostics());
                if (result.emitted()) {
                    Files.writeString(directOut.resolve("probe.lua"),
                        failureProbe("app.lua"), StandardCharsets.UTF_8);
                    ProcessOutcome probe = runProcess(List.of("luajit", "probe.lua"),
                        directOut, Map.of("DEAL_DEFER_MAIN", "1"));
                    String[] parts = probe.stdout().trim().split("\\|", -1);
                    if (parts.length >= 4 && "ERR".equals(parts[0])) {
                        checkEq(pinned.code(), parts[1],
                            "the direct call of '" + failureCase.exportName()
                                + "' keeps the same pinned code");
                        checkEq(pinned.message(), parts[2],
                            "the direct call of '" + failureCase.exportName()
                                + "' keeps the same pinned message");
                        int[] origin = originOf(failureCase.directSource(),
                            failureCase.directCallSnippet());
                        checkEq(direct.sourceRoot().resolve("app.deal")
                                .toAbsolutePath() + ":" + origin[0] + ":"
                                + origin[1], parts[3],
                            "the direct call of '" + failureCase.exportName()
                                + "' carries its own call-expression origin");
                    } else {
                        fail("the failing direct drive's probe output is "
                            + "malformed: " + escaped(probe.stdout()));
                    }
                }
            } finally {
                deleteRecursively(direct.root());
            }
        }
    }

    /** The pinned runtime-error expectation of one corpus FFI sidecar. */
    private static SidecarExpectations.ErrorExpectation pinnedError(String sidecar)
            throws Exception {
        String json = Files.readString(Path.of(
            "test/conformance/backend-runtime/ffi/" + sidecar),
            StandardCharsets.UTF_8);
        SidecarExpectations.StructuredExpectationSidecar parsed =
            SidecarExpectations.StructuredExpectationSidecar.parse(json);
        SidecarExpectations.RuntimeExpectation expectation =
            parsed.byBackend().get("luajit");
        if (!(expectation
                instanceof SidecarExpectations.RuntimeExpectation.Executed executed)
                || executed.error() == null) {
            throw new IllegalStateException("the corpus sidecar '" + sidecar
                + "' carries no LuaJIT runtime-error expectation: " + json);
        }
        return executed.error();
    }

    /**
     * The deferred-main failure probe: the raised error projected to
     * {@code ERR|code|message|origin} (the canonical DEAL carrier's
     * {@code m}/{@code o} fields, the provider carrier's
     * {@code message}/{@code file:line:column}).
     */
    private static String failureProbe(String artifactName) {
        return """
            local chunk = dofile("%s")
            local ok, err = __dealMain()
            if ok then
              print("ERR|-|the module init succeeded|-")
              os.exit(0)
            end
            if type(err) ~= "table" then
              print("ERR|-|not a runtime error table|-")
              os.exit(0)
            end
            local code = err.code or "-"
            local message = err.m or err.message or "-"
            local origin = err.o
            if origin == nil then
              origin = tostring(err.file) .. ":" .. tostring(err.line) .. ":"
                .. tostring(err.column)
            end
            print("ERR|" .. code .. "|" .. message .. "|" .. origin)
            """.formatted(artifactName);
    }

    // =========================================================================
    // 5. The oracle
    // =========================================================================

    /** The oracle's seamed loaded surface and host terminals of the drive. */
    private static SemanticOracle.HostResponder driveResponder(
            List<String> calls, Map<String, String[]> failures) {
        return new SemanticOracle.HostResponder() {
            private final Map<String, SemanticOracle.Value> entries =
                new LinkedHashMap<>();

            @Override
            public SemanticOracle.Value loadedExport(ModuleId module, String export,
                    RuntimeDescriptor descriptor) {
                return entries.computeIfAbsent(module.path() + "." + export,
                    key -> descriptor instanceof RuntimeDescriptor.Func signature
                        ? new SemanticOracle.Value.HostEntryValue(signature)
                        : new SemanticOracle.Value.IntrinsicValue("host:" + key));
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                calls.add(export + "(" + args.size() + ")");
                if (failures.containsKey(export)) {
                    String[] failure = failures.get(export);
                    return new SyncOutcome.Thrown(failure[0], failure[1]);
                }
                return switch (export) {
                    case "ffi_add" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(
                            ((SemanticOracle.Value.IntValue) args.get(0)).value()
                                + ((SemanticOracle.Value.IntValue) args.get(1))
                                    .value()));
                    case "ffi_half" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.NumValue(2.5));
                    case "ffi_not" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.BoolValue(true));
                    case "ffi_echo" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.StrValue("hello"));
                    case "ffi_identity_int" -> new SyncOutcome.Returned(args.get(0));
                    case "ffi_noop" -> new SyncOutcome.Returned(
                        SemanticOracle.Value.NullValue.INSTANCE);
                    default -> throw new IllegalStateException(
                        "the drive scripts no host terminal for " + export);
                };
            }
        };
    }

    private static void testOracleParity() throws Exception {
        System.out.println("-- the oracle executes the same drive with the same "
            + "calls, outcomes, and origin --");
        Map<String, String[]> failures = new LinkedHashMap<>();
        for (FailureCase failureCase : FAILURE_CASES) {
            SidecarExpectations.ErrorExpectation pinned =
                pinnedError(failureCase.sidecar());
            failures.put(failureCase.exportName(),
                new String[] {pinned.code(), pinned.message()});
        }
        Fixture fixture = compile("app", VALUE_READ_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the oracle drive lowers: " + result.diagnostics());
            } else {
                List<String> calls = new ArrayList<>();
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.executeProjectInits(result.project(),
                        result.tables(), result.registries(),
                        driveResponder(calls, failures));
                check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                    "the oracle's value-position drive succeeds: "
                        + run.terminal());
                checkEq(List.of("ffi_add(2)", "ffi_half(1)", "ffi_not(1)",
                        "ffi_echo(1)", "ffi_identity_int(1)", "ffi_noop(0)"),
                    calls,
                    "the oracle executes each value-position call once through "
                        + "the read's registration");
                List<String> hostCalls = new ArrayList<>();
                List<String> hostReturns = new ArrayList<>();
                for (SemanticRuntimeModel.EffectEvent effect : run.effects()) {
                    switch (effect.kind()) {
                        case HOST_CALL -> hostCalls.add(effect.text());
                        case HOST_RETURN -> hostReturns.add(effect.text());
                        default -> {
                        }
                    }
                }
                for (String exportName : SCALAR_EXPORTS) {
                    check(hostCalls.contains(FFI_DOTTED + "." + exportName),
                        "the oracle records the host call of '" + exportName + "'");
                    check(hostReturns.stream().anyMatch(text -> text.startsWith(
                            FFI_DOTTED + "." + exportName + "=")),
                        "the oracle records the host return of '" + exportName + "'");
                }
            }
        } finally {
            deleteRecursively(fixture.root());
        }

        for (FailureCase failureCase : FAILURE_CASES) {
            SidecarExpectations.ErrorExpectation pinned =
                pinnedError(failureCase.sidecar());
            Fixture failing = compile("app", failureCase.readSource());
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(failing);
                if (result.project() == null) {
                    fail("the failing oracle drive of '"
                        + failureCase.exportName() + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                List<String> calls = new ArrayList<>();
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.executeProjectInits(result.project(),
                        result.tables(), result.registries(),
                        driveResponder(calls, failures));
                checkEq(List.of(failureCase.exportName() + "(0)"), calls,
                    "the oracle executes the failing value-position call of '"
                        + failureCase.exportName() + "' once");
                check(run.terminal()
                        instanceof SemanticRuntimeModel.Terminal.DealFailure,
                    "the oracle's failing drive reports a DEAL failure: "
                        + run.terminal());
                if (run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                        failure) {
                    int[] origin = originOf(failureCase.readSource(),
                        failureCase.readCallSnippet());
                    checkEq(pinned.code(), failure.error().code(),
                        "the oracle keeps the pinned code of '"
                            + failureCase.exportName() + "'");
                    checkEq(pinned.message(), failure.error().message(),
                        "the oracle keeps the pinned message of '"
                            + failureCase.exportName() + "'");
                    checkEq(failing.sourceRoot().resolve("app.deal")
                            .toAbsolutePath() + ":" + origin[0] + ":"
                            + origin[1],
                        failure.error().origin(),
                        "the oracle keeps the call-expression origin of '"
                            + failureCase.exportName() + "'");
                }
            } finally {
                deleteRecursively(failing.root());
            }
        }
    }

    // =========================================================================
    // 6. The declaration negatives
    // =========================================================================

    private static void testAsyncDeclarationNegative() throws Exception {
        System.out.println("-- an async extern-C declaration stays a compile-time "
            + "E7002 rejection (never an async value-position form) --");
        Path root = Files.createTempDirectory("ffi-async-negative");
        Path src = root.resolve("src");
        try {
            Files.createDirectories(src);
            String declaration = Files.readString(Path.of(
                "test/conformance/backend-runtime/ffi/support/invalid-async.d.deal"),
                StandardCharsets.UTF_8);
            Files.writeString(src.resolve("invalid-async.d.deal"),
                ConformanceHarnessMetadata.stripClassificationHeaders(declaration),
                StandardCharsets.UTF_8);
            Files.writeString(src.resolve("app.deal"), """
                import * as invalid from "candidate/invalid-async"

                export function main(): null {
                  return null
                }
                """, StandardCharsets.UTF_8);
            Map<String, String> externals = new LinkedHashMap<>();
            externals.put("candidate/invalid-async",
                src.resolve("invalid-async.d.deal").toAbsolutePath().toString());
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("app.deal").toAbsolutePath(), root.resolve("out"),
                false, false, false, false, Backend.LUAJIT, externals,
                List.of(src.toAbsolutePath()), null, null, harnessInvocation());
            boolean compiled = orchestrator.compile();
            check(!compiled, "the async extern-C declaration fails the compile");
            List<CompilerDiagnostic> diagnostics = orchestrator.diagnostics();
            check(diagnostics.stream().anyMatch(d -> "E7002".equals(d.code())
                    && d.message().contains("async function declaration 'invalidAsync'")
                    && d.message().contains("must be synchronous")),
                "the async declaration is rejected with the pinned E7002 text at "
                    + "the declaration: " + diagnostics);
            checkEq(0, diagnostics.stream()
                    .filter(d -> "error".equals(d.severity()))
                    .filter(d -> !"E7002".equals(d.code()))
                    .toList().size(),
                "the async declaration rejection is the only compile error");
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // Process helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir)
            throws Exception {
        return runProcess(command, workDir, Map.of());
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir,
            Map<String, String> environment) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.environment().putAll(environment);
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
