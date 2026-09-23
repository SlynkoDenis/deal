package deal.test;

import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ModuleRoute;
import deal.semantic.RequirementManifestResult;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalExecutionOwner;
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
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;

/**
 * ISSUE-0649: the read-value integration verification leaf — the
 * consolidated three-consumer probe matrix, the per-unit multi-chunk
 * resolution probe, the exactly-one-binding and both-directions binding
 * invariants, the negative seeds through the production arm, and the
 * emission-agreement/determinism assertions (design source
 * {@code module-export-reads-and-in-project-class-construction}
 * Verification 1 (consolidated), 3, 5, 7, 8 and the Failure and
 * operations section; the read execution and export-read contracts;
 * {@code semantic-ir-construct-coverage-cutover} K2/K9;
 * {@code luajit-jvm-single-lowering-production-cutover} C2).
 *
 * <p>This is the cluster's integration verification leaf: its scenarios
 * exercise the full composition of the four read slices (the oracle
 * surface registry, the compiled read realization, the spec-stdlib
 * callables, and the host/FFI read arm) and fail if any of them is
 * broken.</p>
 *
 * <ol>
 *   <li><b>The consolidated probe matrix.</b> One probe project whose
 *       entry reads a compiled companion's declared function export
 *       twice and a {@code std.console} and {@code std.string} export
 *       into function-typed bindings runs through
 *       {@link SemanticLowerer#lowerProject}, the composed project gate,
 *       the three-consumer differential matrix, and
 *       {@link ProductionProjectEmission} for LuaJIT and JVM under the
 *       real toolchains ({@code luajit}; {@code javac --release 25
 *       -proc:none} + {@code java}). No placeholder text remains in
 *       either artifact, the read operations agree event-for-event
 *       across the three consumers, and two reads of one export yield
 *       the identical object reference.</li>
 *   <li><b>The exactly-one binding and both-directions invariant
 *       (V3).</b> For each function-typed read kind (COMPILED / STDLIB /
 *       HOST) the unit carries exactly one registration keyed by the
 *       read result's allocation identity with the expected shape and
 *       owner; a doctored duplicate registration fails at registration
 *       time; a doctored zero registration fails the closed gate with
 *       {@code R-FUNCTION-BINDING}. After a COMPILED read the
 *       owner-side registration of the published value stays the
 *       owner's {@code LoweredBody} (the read never re-keys it), the
 *       read-side registration stays addressable by the read result's
 *       identity, and a doctored read-time re-keying of the shared value
 *       is rejected by the closed gate.</li>
 *   <li><b>The negative seeds (V5).</b> A non-exported member read, an
 *       alias with no resolved import fact, a STDLIB member outside the
 *       closed catalog, a STDLIB descriptor mismatch, and a
 *       class-descriptor read each produce E6005
 *       {@code CONSTRUCT_UNLOWERED} through the production arm, stage
 *       nothing, and leave the previous artifact set byte-identical.</li>
 *   <li><b>Emission agreement and determinism (V7).</b> For the probe,
 *       the trace-mode and production emissions carry the identical read
 *       operation — the emission bodies are byte-identical except the
 *       mode-parameterized terminal/protocol surfaces — and a repeated
 *       emission is byte-identical in each mode on both targets.</li>
 *   <li><b>Per-unit multi-chunk resolution (V8).</b> The partial drive
 *       (only the entry artifact initialized) projects the absent-slot
 *       value identically in all three consumers ({@code missing}); the
 *       owner module's per-unit artifact publishes into the
 *       program-scoped registry and the entry module's per-unit
 *       artifact then resolves the published value — the identical
 *       object for two reads, and the identical memoized catalog
 *       callable across two per-unit classes/chunks — proving the
 *       per-unit class/chunk resolves the program's surface, not a
 *       session-local map; and the per-unit sessions of both targets
 *       emit the same read operation in trace and production mode.</li>
 *   <li><b>Pin retargeting and registration.</b> No test file is
 *       removed, the focused read mains and the affected pins stay
 *       registered in {@code tools/gate-manifest.sh}, and the
 *       previously pinned value-read E6005 assertions now assert the
 *       realized behavior.</li>
 * </ol>
 */
public class ReadValueIntegrationVerificationTest {

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
        check(Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // The fixtures
    // =========================================================================

    private static final ModuleId APP = new ModuleId("app");
    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId CONSOLE_MODULE = new ModuleId("std.console");
    private static final ModuleId STRING_MODULE = new ModuleId("std.string");
    private static final String COMPILED_NAME = "tag";
    private static final String CONSOLE_ROW = "log";
    private static final String ALGORITHM_ROW = "length";
    private static final String CONSOLE_TEXT = "hello";

    private static final String LIB_SOURCE = """
        export function tag(v: int): string {
          return "t"
        }
        """;

    /**
     * The consolidated probe: two compiled reads of one declared export
     * plus the console value read, the algorithmic row read, and the
     * console callee read (the direct {@code STDLIB_CALL} arm).
     */
    private static final String COMPOSITION_APP_SOURCE = """
        import * as lib from "./lib"
        import * as console from "std/console"
        import * as str from "std/string"

        export function main(): null {
          let f: (v: int) => string = lib.tag
          let g: (v: int) => string = lib.tag
          let h: (x: string) => null = console.log
          let k: (s: string) => int = str.length
          console.log("hello")
          return null
        }
        """;

    /** The source line of each composition read (declaration order). */
    private static final int COMPILED_READ_LINE = 6;
    private static final int COMPILED_READ_SECOND_LINE = 7;
    private static final int CONSOLE_VALUE_LINE = 8;
    private static final int ALGORITHM_VALUE_LINE = 9;
    private static final int CONSOLE_CALLEE_LINE = 10;

    /** The three function-typed read kinds in one project (V3). */
    private static final ModuleId HOST_MODULE = new ModuleId("host.probe");
    private static final String HOST_DECLARATION_SOURCE = """
        export function ping(): string;
        """;
    private static final String THREE_KINDS_APP_SOURCE = """
        import * as lib from "./lib"
        import * as console from "std/console"
        import * as probe from "host/probe"

        export function main(): null {
          let f: (v: int) => string = lib.tag
          let g: (x: string) => null = console.log
          let p: () => string = probe.ping
          return null
        }
        """;

    /** The class-descriptor seed (a class used as a value). */
    private static final String POINT_LIB_SOURCE = """
        export class Point {
          x: int = 0
        }
        """;
    private static final String CLASS_READ_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let p: lib.Point = lib.Point
          return null
        }
        """;

    /** The project-local std console declaration of the out-of-catalog seed. */
    private static final String OUT_OF_CATALOG_STD_CONSOLE = """
        export function log(s: string): null;
        export function localMarker(): string;
        """;
    private static final String OUT_OF_CATALOG_APP_SOURCE = """
        import * as console from "std/console"

        export function main(): null {
          let m: () => string = console.localMarker
          return null
        }
        """;

    /** The project-local std console declaration of the descriptor-mismatch seed. */
    private static final String MISMATCH_STD_CONSOLE = """
        export function log(x: int): null;
        export function error(x: string): null;
        """;
    private static final String MISMATCH_APP_SOURCE = """
        import * as console from "std/console"

        export function main(): null {
          let g: (x: int) => null = console.log
          return null
        }
        """;

    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        DistributionHome distributionHome) {
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** The release-owned production invocation this leaf's units are driven with. */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources,
            Map<String, String> externals, Path stdlibRoot) throws Exception {
        Path root = Files.createTempDirectory("read-value-iv");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Map<String, String> resolvedExternals = new LinkedHashMap<>();
        for (Map.Entry<String, String> external : externals.entrySet()) {
            resolvedExternals.put(external.getKey(),
                root.resolve(external.getValue()).toAbsolutePath().toString());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        // The harness invocation (COMMON_SHADOW) keeps the harness arm:
        // the fixtures' subject is the project lowering entry and the
        // production arm, never the retained route dispatch. A fixture
        // whose harness arm fails still publishes its checked project
        // (the production arm's subject).
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, resolvedExternals,
            List.of(src.toAbsolutePath()), stdlibRoot, null, harnessInvocation());
        orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : surface.moduleIds()) {
            String specifier = null;
            for (String candidate : externals.keySet()) {
                if (candidate.replace('/', '.').equals(declarationModule.path())
                        || candidate.equals(declarationModule.path())) {
                    specifier = candidate;
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            surface, externCModules, identities,
            DistributionHome.forManifestDirectory(src.toString()));
    }

    private static Fixture compositionFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", LIB_SOURCE);
        sources.put("src/app.deal", COMPOSITION_APP_SOURCE);
        return compileProject(sources, Map.of(), null);
    }

    private static Fixture threeKindsFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", LIB_SOURCE);
        sources.put("src/probe.d.deal", HOST_DECLARATION_SOURCE);
        sources.put("src/app.deal", THREE_KINDS_APP_SOURCE);
        return compileProject(sources, Map.of("host/probe", "src/probe.d.deal"), null);
    }

    private static Fixture classReadFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", POINT_LIB_SOURCE);
        sources.put("src/app.deal", CLASS_READ_APP_SOURCE);
        return compileProject(sources, Map.of(), null);
    }

    private static Fixture compiledReadFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", LIB_SOURCE);
        sources.put("src/app.deal", COMPOSITION_APP_SOURCE);
        return compileProject(sources, Map.of(), null);
    }

    /**
     * The stdlib override fixtures: the project root carries a local
     * {@code std/console.d.deal} the checker and the read arm share (the
     * declaration is the declared-export fact channel, the closed catalog
     * remains the resolution authority).
     */
    private static Fixture stdlibOverrideFixture(String declaration, String appSource)
            throws Exception {
        Path root = Files.createTempDirectory("read-value-iv-stdlib");
        Path src = root.resolve("src");
        writeFileIn(root, "std/console.d.deal", declaration);
        writeFileIn(root, "src/app.deal", appSource);
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(src.toAbsolutePath()), root, null, harnessInvocation());
        orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            String harness = String.valueOf(orchestrator.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the stdlib override fixture did not build: "
                + detail + " / " + harness);
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), new LinkedHashMap<>(),
            new LinkedHashMap<>(), DistributionHome.forManifestDirectory(
                src.toString()));
    }

    // =========================================================================
    // Lowering, emission, and op helpers
    // =========================================================================

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(), BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    private static SemanticIrValidator.ComparisonFacts facts(Fixture fixture) {
        return new SemanticIrValidator.ComparisonFacts(
            fixture.index().interfaceIndexDigest(), SemanticProfile.DEAL_V1_2_INT32,
            productionInvocation().capabilityRegistryHash());
    }

    /** One production-arm run of one fixture (the P9 pattern). */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager, boolean sourceMapExplicit)
            throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(), BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, sourceMapExplicit, fixture.distributionHome(), stager);
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

    private static List<SemanticOp> readsOf(LoweredModuleUnit unit) {
        return opsOfKind(unit, SemanticOpKind.EXPORT_READ);
    }

    private static KindPayload.ExportReadPayload payloadOf(SemanticOp read) {
        return (KindPayload.ExportReadPayload) read.payload();
    }

    private static ValueId readValue(SemanticOp read) {
        return payloadOf(read).value();
    }

    private static FunctionAllocationIdentity readKey(SemanticOp read) {
        return new FunctionAllocationIdentity(readValue(read).id());
    }

    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit,
                                                      SemanticOp read) {
        return unit.functionBindings().get(readKey(read));
    }

    /** The number of registrations keyed by the read's result identity. */
    private static int registrationsOf(LoweredModuleUnit unit, SemanticOp read) {
        int count = 0;
        for (FunctionAllocationIdentity key : unit.functionBindings().keySet()) {
            if (key.equals(readKey(read))) {
                count++;
            }
        }
        return count;
    }

    /** The read of one module/export at one source line, or null. */
    private static SemanticOp readAt(List<SemanticOp> reads, ModuleId module, String name,
                                     int line) {
        for (SemanticOp read : reads) {
            KindPayload.ExportReadPayload payload = payloadOf(read);
            if (payload.module().equals(module) && payload.name().equals(name)
                    && read.origin().span() != null
                    && read.origin().span().startLine() == line) {
                return read;
            }
        }
        return null;
    }

    private static SemanticOp publishOpOf(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                return op;
            }
        }
        return null;
    }

    /** The MODULE_EXPORT boundary child of one publication op, or null. */
    private static SemanticOp exportBoundaryOf(LoweredModuleUnit unit, OpId publishOp) {
        for (SemanticOp candidate : unit.ops()) {
            if (candidate.kind() != SemanticOpKind.BOUNDARY) {
                continue;
            }
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) candidate.payload();
            if (publishOp.equals(candidate.origin().parentOpId())
                    && payload.kind() == deal.semantic.ir.BoundaryKind.MODULE_EXPORT) {
                return candidate;
            }
        }
        return null;
    }

    private static StdlibFunctionCatalog.Entry rowOf(String modulePath, String exportName) {
        return StdlibFunctionCatalog.lookup(modulePath, exportName)
            .orElseThrow(() -> new IllegalStateException(
                "no catalog row for " + modulePath + "." + exportName));
    }

    private static RuntimeDescriptor.Func rowDescriptorOf(String modulePath,
                                                          String exportName) {
        return rowOf(modulePath, exportName).declaredDescriptor();
    }

    private static String luaStdlibEntryCall(String modulePath, String exportName) {
        StdlibFunctionCatalog.Entry row = rowOf(modulePath, exportName);
        return "__stdlibEntry(\"" + modulePath + "\", \"" + exportName + "\", \""
            + row.function().name() + "\", \""
            + descriptorText(row.declaredDescriptor()) + "\", \""
            + row.declaredDescriptor().canonicalSpecText() + "\")";
    }

    private static String jvmStdlibCarrierCall(String modulePath, String exportName) {
        StdlibFunctionCatalog.Entry row = rowOf(modulePath, exportName);
        return "JvmRuntime.stdlibCallable(\"" + modulePath + "\", \"" + exportName
            + "\", \"" + row.function().name() + "\", \""
            + descriptorText(row.declaredDescriptor()) + "\", \""
            + row.declaredDescriptor().canonicalSpecText() + "\")";
    }

    private static String descriptorText(RuntimeDescriptor descriptor) {
        if (descriptor instanceof RuntimeDescriptor.Null) {
            return "null";
        }
        if (descriptor instanceof RuntimeDescriptor.Boolean) {
            return "boolean";
        }
        if (descriptor instanceof RuntimeDescriptor.Int) {
            return "int";
        }
        if (descriptor instanceof RuntimeDescriptor.Number) {
            return "number";
        }
        if (descriptor instanceof RuntimeDescriptor.String) {
            return "string";
        }
        if (descriptor instanceof RuntimeDescriptor.Table) {
            return "table";
        }
        if (descriptor instanceof RuntimeDescriptor.Class cls) {
            return cls.classId().text();
        }
        if (descriptor instanceof RuntimeDescriptor.Array array) {
            return "array(" + descriptorText(array.element()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
            return "nullable(" + descriptorText(nullable.inner()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Func func) {
            StringBuilder params = new StringBuilder();
            for (RuntimeDescriptor param : func.paramTypes()) {
                if (params.length() > 0) {
                    params.append(',');
                }
                params.append(descriptorText(param));
            }
            return "function(" + params + ";" + descriptorText(func.returnType()) + ")";
        }
        return "unknown";
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int at = text.indexOf(needle);
        while (at >= 0) {
            count++;
            at = text.indexOf(needle, at + needle.length());
        }
        return count;
    }

    // =========================================================================
    // Trace helpers
    // =========================================================================

    private static String successAtomOf(SemanticRuntimeModel.ConsumerRun run, OpId op) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op)
                    && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                return event.output();
            }
        }
        return null;
    }

    private static List<String> successAtomsOf(SemanticRuntimeModel.ConsumerRun run,
                                               List<SemanticOp> reads) {
        List<String> atoms = new ArrayList<>();
        for (SemanticOp read : reads) {
            atoms.add(successAtomOf(run, read.opId()));
        }
        return atoms;
    }

    /** The START input atom of one boundary op in a run, or null. */
    private static String startInputAtomOf(SemanticRuntimeModel.ConsumerRun run, OpId op) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op)
                    && event.phase() == SemanticRuntimeModel.Phase.START
                    && !event.inputs().isEmpty()) {
                return event.inputs().get(0);
            }
        }
        return null;
    }

    /**
     * The SUCCESS output atoms of the given read ops in a LuaJIT trace
     * stream, in stream order.
     */
    private static List<String> luaReadAtoms(String stderr, List<String> readOps) {
        List<String> atoms = new ArrayList<>();
        for (String line : stderr.split("\n")) {
            String[] fields = line.split("\\|", -1);
            if (fields.length < 9 || !"T".equals(fields[0])
                    || !"SUCCESS".equals(fields[4])) {
                continue;
            }
            if (!readOps.contains(fields[3])) {
                continue;
            }
            for (int i = 8; i < fields.length; i++) {
                if (fields[i].startsWith("=>")) {
                    atoms.add(fields[i].substring(2));
                }
            }
        }
        return atoms;
    }

    /** The publication boundary's input atom of the owner module, or null. */
    private static String luaPublicationAtom(String stderr, String modulePath,
            LoweredModuleUnit libUnit) {
        SemanticOp publish = publishOpOf(libUnit);
        SemanticOp boundary = publish == null ? null : exportBoundaryOf(libUnit,
            publish.opId());
        if (boundary == null) {
            return null;
        }
        String key = modulePath + "#" + boundary.opId().id();
        for (String line : stderr.split("\n")) {
            String[] fields = line.split("\\|", -1);
            if (fields.length < 9 || !"T".equals(fields[0])
                    || !"START".equals(fields[4]) || !"BOUNDARY".equals(fields[5])
                    || !key.equals(fields[3])) {
                continue;
            }
            for (int i = 8; i < fields.length; i++) {
                if (!fields[i].startsWith("=>")) {
                    return fields[i];
                }
            }
        }
        return null;
    }

    // =========================================================================
    // 1. The consolidated probe matrix
    // =========================================================================

    static void testConsolidatedProbeMatrix() throws Exception {
        System.out.println("-- the consolidated probe matrix: the compiled and stdlib "
            + "read probes as one composition through the oracle and both production "
            + "artifacts --");
        Fixture fixture = compositionFixture();
        Path workspace = Files.createTempDirectory("read-value-iv-matrix");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the consolidated probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(Optional.empty(), SemanticIrValidator.validate(project, facts(fixture)),
                "the consolidated lowered project passes the closed project gate");
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            checkEq(List.of(LIB, APP), List.copyOf(project.modules().keySet()),
                "the closure carries the compiled companion then the entry module");
            if (appUnit == null || libUnit == null) {
                return;
            }
            List<SemanticOp> reads = readsOf(appUnit);
            checkEq(5, reads.size(),
                "the entry unit carries exactly one EXPORT_READ per source occurrence "
                    + "(two compiled reads, the console value read, the algorithmic row "
                    + "read, and the console callee read)");
            SemanticOp compiled1 = readAt(reads, LIB, COMPILED_NAME, COMPILED_READ_LINE);
            SemanticOp compiled2 = readAt(reads, LIB, COMPILED_NAME,
                COMPILED_READ_SECOND_LINE);
            SemanticOp consoleValue = readAt(reads, CONSOLE_MODULE, CONSOLE_ROW,
                CONSOLE_VALUE_LINE);
            SemanticOp algorithm = readAt(reads, STRING_MODULE, ALGORITHM_ROW,
                ALGORITHM_VALUE_LINE);
            SemanticOp consoleCallee = readAt(reads, CONSOLE_MODULE, CONSOLE_ROW,
                CONSOLE_CALLEE_LINE);
            check(compiled1 != null && compiled2 != null && consoleValue != null
                    && algorithm != null && consoleCallee != null,
                "the composition carries the five expected reads per position");
            if (compiled1 == null || compiled2 == null || consoleValue == null
                    || algorithm == null || consoleCallee == null) {
                return;
            }

            // The payloads and the exactly-one registrations per kind.
            checkEq("(int)->string",
                payloadOf(compiled1).descriptor().canonicalSpecText(),
                "the compiled read carries the companion's declared descriptor");
            for (SemanticOp read : List.of(compiled1, compiled2)) {
                check(bindingOf(appUnit, read)
                        instanceof FunctionExecutionBinding.ExternalFunction external
                        && external.moduleId().equals(LIB)
                        && external.exportName().equals(COMPILED_NAME)
                        && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                    "the compiled read registers exactly one ExternalFunction(lib, tag, "
                        + "SHARED_BODY); got " + bindingOf(appUnit, read));
                checkEq(1, registrationsOf(appUnit, read),
                    "exactly one registration is keyed by the compiled read's result "
                        + "identity");
            }
            for (SemanticOp read : List.of(consoleValue, algorithm, consoleCallee)) {
                ModuleId module = payloadOf(read).module();
                RuntimeDescriptor.Func row = rowDescriptorOf(module.path(),
                    payloadOf(read).name());
                check(payloadOf(read).descriptor().equals(row),
                    "the stdlib read carries the catalog row's declared descriptor "
                        + row.canonicalSpecText() + "; got "
                        + payloadOf(read).descriptor().canonicalSpecText());
                check(bindingOf(appUnit, read)
                        instanceof FunctionExecutionBinding.HostFunction host
                        && host.hostModuleId().equals(module)
                        && host.exportName().equals(payloadOf(read).name())
                        && host.descriptor().equals(row),
                    "the stdlib read registers exactly one HostFunction with the catalog "
                        + "row; got " + bindingOf(appUnit, read));
                checkEq(1, registrationsOf(appUnit, read),
                    "exactly one registration is keyed by the stdlib read's result "
                        + "identity");
            }
            checkEq(1, opsOfKind(appUnit, SemanticOpKind.STDLIB_CALL).size(),
                "the console callee position keeps the landed direct STDLIB_CALL arm");

            // The owner-side registration of the published value stays the
            // owner's LoweredBody; no read registration is keyed by it.
            SemanticOp publish = publishOpOf(libUnit);
            check(publish != null, "the companion publishes its declared export");
            if (publish == null) {
                return;
            }
            ValueId publishedValue =
                ((KindPayload.ExportPublishPayload) publish.payload()).value();
            check(libUnit.functionBindings()
                    .get(new FunctionAllocationIdentity(publishedValue.id()))
                    instanceof FunctionExecutionBinding.LoweredBody,
                "the owner-side registration of the published value is the owner's "
                    + "LoweredBody, keyed by the published value's creation identity");
            check(appUnit.functionBindings().keySet().stream()
                    .noneMatch(key -> key.id() == publishedValue.id()),
                "no read registration is keyed by the shared published value's identity");

            // The oracle: the publication atom is the read atom (no fresh
            // allocation), the two reads of one export publish the identical
            // value, and the placeholder atom is gone.
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the consolidated project drive succeeds: " + run.terminal());
            checkEq(List.of(CONSOLE_TEXT), run.effects().stream()
                    .map(SemanticRuntimeModel.EffectEvent::text).toList(),
                "exactly one console effect with the direct arm's text projection");
            SemanticOp exportBoundary = exportBoundaryOf(libUnit, publish.opId());
            String publicationAtom = exportBoundary == null ? null
                : startInputAtomOf(run, exportBoundary.opId());
            check(publicationAtom != null && publicationAtom.startsWith("ref:"),
                "the companion's publication atom is the published value's creation "
                    + "allocation; got " + publicationAtom);
            checkEq(publicationAtom, successAtomOf(run, compiled1.opId()),
                "the first compiled read publishes the owner's published value "
                    + "(no fresh allocation)");
            checkEq(publicationAtom, successAtomOf(run, compiled2.opId()),
                "the second compiled read publishes the identical value");
            checkEq(successAtomOf(run, consoleValue.opId()),
                successAtomOf(run, consoleCallee.opId()),
                "two stdlib reads of one cataloged export publish the identical "
                    + "callable");
            check(!Objects.equals(successAtomOf(run, algorithm.opId()),
                    successAtomOf(run, consoleValue.opId())),
                "the algorithmic row's callable is distinct");
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                check(event.output() == null || !event.output().startsWith("export:"),
                    "no export:<module>.<name> placeholder atom remains in the oracle "
                        + "trace: " + event.output());
            }

            // The three-consumer differential matrix: every read's identity
            // is compared event-for-event.
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project, result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.success(
                        "consolidated compiled + stdlib reads", List.of(CONSOLE_TEXT),
                        "null"),
                    workspace.resolve("matrix"));
            check(verdict.pass(), "the consolidated probe's three consumers agree "
                + "event-for-event:\n" + verdict.report());
            if (verdict.pass()) {
                for (SemanticRuntimeModel.ConsumerRun consumerRun : verdict.runs()) {
                    List<String> compiledAtoms = successAtomsOf(consumerRun,
                        List.of(compiled1, compiled2));
                    checkEq(2, compiledAtoms.size(),
                        consumerRun.consumer() + " executes both compiled reads");
                    check(compiledAtoms.size() == 2
                            && compiledAtoms.get(0) != null
                            && compiledAtoms.get(0).equals(compiledAtoms.get(1))
                            && compiledAtoms.get(0).startsWith("ref:"),
                        consumerRun.consumer() + " publishes the identical published "
                            + "value for both compiled reads; got " + compiledAtoms);
                    List<String> stdlibAtoms = successAtomsOf(consumerRun,
                        List.of(consoleValue, consoleCallee));
                    check(stdlibAtoms.size() == 2 && stdlibAtoms.get(0) != null
                            && stdlibAtoms.get(0).equals(stdlibAtoms.get(1))
                            && stdlibAtoms.get(0).startsWith("ref:"),
                        consumerRun.consumer() + " publishes the identical catalog "
                            + "callable for both console reads; got " + stdlibAtoms);
                }
            }

            // The production artifacts: the emitted read resolves the
            // surface, no placeholder remains, and the real toolchains run.
            verifyProductionArtifacts(fixture, result, reads, workspace);
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /** The production artifacts of the consolidated probe under the real toolchains. */
    private static void verifyProductionArtifacts(Fixture fixture,
            SemanticLowerer.ProjectLoweringResult result, List<SemanticOp> reads,
            Path workspace) throws Exception {
        Path luaOut = fixture.root().resolve("out-lua");
        PublicationStager luaStager = PublicationStager.forRoot(luaOut);
        ProductionProjectEmission.Result luaResult;
        try {
            luaResult = emit(fixture, Backend.LUAJIT, luaStager, false);
            luaStager.publish();
        } catch (Exception exception) {
            luaStager.discard();
            throw exception;
        } finally {
            luaStager.discard();
        }
        check(luaResult.emitted(), "the consolidated LuaJIT production arm emits: "
            + luaResult.diagnostics());
        if (!luaResult.emitted()) {
            return;
        }
        Path luaArtifact = luaOut.resolve(luaResult.artifactRelativePath());
        String luaText = Files.readString(luaArtifact, StandardCharsets.UTF_8);
        String compiledReadText = "__exportValue(\"lib\", \"tag\")";
        String consoleEntryCall = luaStdlibEntryCall("std.console", CONSOLE_ROW);
        String algorithmEntryCall = luaStdlibEntryCall("std.string", ALGORITHM_ROW);
        for (SemanticOp read : reads) {
            long id = readValue(read).id();
            String expected = "S.v" + id + " = " + compiledReadText;
            if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                expected = "S.v" + id + " = " + consoleEntryCall;
            } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                expected = "S.v" + id + " = " + algorithmEntryCall;
            }
            checkEq(1, countOccurrences(luaText, expected),
                "the production LuaJIT artifact carries the surface-resolving read: "
                    + expected);
            check(!luaText.contains("S.v" + id + " = __intrinsicFn()"),
                "the production LuaJIT artifact carries no placeholder read for slot "
                    + id);
        }
        check(!luaText.contains("export:lib.tag") && !luaText.contains("export:std."),
            "the production LuaJIT artifact carries no placeholder token");

        Path luaProbe = workspace.resolve("consolidated-lua-probe.lua");
        Files.writeString(luaProbe, consolidatedLuaProbe(luaArtifact),
            StandardCharsets.UTF_8);
        ProcessOutcome luaRun = runProcess(List.of("luajit",
            luaProbe.toAbsolutePath().toString()), workspace);
        check(luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK")
                && countOccurrences(luaRun.stdout(), CONSOLE_TEXT) == 1,
            "the consolidated LuaJIT chunk resolves both read kinds and writes exactly "
                + "one console effect; exit=" + luaRun.exitCode() + " stdout="
                + luaRun.stdout().replace("\n", "\\n") + " stderr="
                + luaRun.stderr().replace("\n", "\\n"));

        Path jvmOut = fixture.root().resolve("out-jvm");
        PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
        ProductionProjectEmission.Result jvmResult;
        try {
            jvmResult = emit(fixture, Backend.JVM, jvmStager, false);
            jvmStager.publish();
        } finally {
            jvmStager.discard();
        }
        check(jvmResult.emitted(), "the consolidated JVM production arm emits: "
            + jvmResult.diagnostics());
        if (!jvmResult.emitted()) {
            return;
        }
        Path jvmSource = jvmOut.resolve(jvmResult.artifactRelativePath());
        String jvmText = Files.readString(jvmSource, StandardCharsets.UTF_8);
        String consoleCarrierCall = jvmStdlibCarrierCall("std.console", CONSOLE_ROW);
        String algorithmCarrierCall = jvmStdlibCarrierCall("std.string", ALGORITHM_ROW);
        for (SemanticOp read : reads) {
            long id = readValue(read).id();
            String expected = "v" + id + " = exportSurface(\"lib\").read(\"tag\");";
            if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                expected = "v" + id + " = " + consoleCarrierCall + ";";
            } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                expected = "v" + id + " = " + algorithmCarrierCall + ";";
            }
            checkEq(1, countOccurrences(jvmText, expected),
                "the production JVM artifact carries the uniform surface read: "
                    + expected);
            check(!jvmText.contains("v" + id + " = new JvmRuntime.Intrinsic()"),
                "the production JVM artifact carries no placeholder read for slot "
                    + id);
        }
        check(!jvmText.contains("export:lib.tag") && !jvmText.contains("export:std."),
            "the production JVM artifact carries no placeholder token");

        String driver = "ReadValueConsolidatedProbe";
        Files.writeString(jvmOut.resolve(driver + ".java"),
            consolidatedJvmProbeSource(JvmBackend.classNameFor(APP.path()), reads),
            StandardCharsets.UTF_8);
        Path classes = jvmOut.resolve("classes");
        Files.createDirectories(classes);
        String classpath = absoluteClasspath();
        ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
            "-proc:none", "-cp", classpath, "-d", classes.toString(),
            jvmSource.toAbsolutePath().toString(),
            jvmOut.resolve(driver + ".java").toAbsolutePath().toString()),
            fixture.root());
        checkEq(0, javacRun.exitCode(),
            "the consolidated JVM artifact compiles with javac --release 25 -proc:none: "
                + javacRun.output());
        if (javacRun.exitCode() != 0) {
            return;
        }
        ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
            classpath + File.pathSeparator + classes, driver), fixture.root());
        check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK"),
            "the consolidated JVM artifact's read slots resolve the published carrier "
                + "and the catalog carriers; exit=" + javaRun.exitCode() + " stdout="
                + javaRun.stdout().replace("\n", "\\n") + " stderr="
                + javaRun.stderr().replace("\n", "\\n"));
    }

    /** The consolidated LuaJIT production probe: both read kinds' resolved entries. */
    private static String consolidatedLuaProbe(Path artifact) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __surface = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if type(__surface) ~= \"table\" then __fail(\"the production chunk "
            + "returned \"..type(__surface)) end\n");
        lua.append("local __lib = __exportSurfaces[\"lib\"]\n");
        lua.append("if __lib == nil then __fail(\"no lib surface\") end\n");
        lua.append("local __tag = __lib[\"tag\"]\n");
        lua.append("if type(__tag) ~= \"table\" then __fail(\"no compiled "
            + "publication\") end\n");
        lua.append("if __tag.__val == nil then __fail(\"no published __val\") end\n");
        lua.append("if __tag.__val ~= __tag.__val then __fail(\"unstable __val\") end\n");
        lua.append("if type(__tag.f) ~= \"function\" then __fail(\"no retained-caller "
            + ".f projection\") end\n");
        lua.append("local __ok, __value = pcall(__tag.f, 1)\n");
        lua.append("if not __ok or __value ~= \"t\" then __fail(\"the retained-caller "
            + ".f projection calls the module function; got \"..tostring(__value)) "
            + "end\n");
        lua.append("local __log = __exportSurfaces[\"std.console\"]"
            + "[\"log\"]\n");
        lua.append("if type(__log) ~= \"table\" or __log.__sid ~= \"CONSOLE_LOG\" then "
            + "__fail(\"no cataloged console callable\") end\n");
        lua.append("if __stdlibEntries[\"std.console\"..string.char(1)..\"log\"] ~= "
            + "__log then __fail(\"the console surface entry is not the memoized "
            + "callable\") end\n");
        lua.append("local __len = __exportSurfaces[\"std.string\"]"
            + "[\"length\"]\n");
        lua.append("if type(__len) ~= \"table\" or __len.__sig ~= ")
            .append(luaString("function(string;int)")).append(" then __fail(\"no "
            + "cataloged algorithmic callable\") end\n");
        lua.append("if __len.__val ~= nil then __fail(\"unexpected __val on a stdlib "
            + "entry\") end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /** The consolidated JVM production probe: both read kinds' resolved objects. */
    private static String consolidatedJvmProbeSource(String className,
            List<SemanticOp> reads) {
        SemanticOp compiled1 = reads.get(0);
        SemanticOp compiled2 = reads.get(1);
        SemanticOp consoleRead = null;
        SemanticOp algorithmRead = null;
        for (SemanticOp read : reads) {
            if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                consoleRead = read;
            } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                algorithmRead = read;
            }
        }
        long compiledId1 = readValue(compiled1).id();
        long compiledId2 = readValue(compiled2).id();
        long consoleId = readValue(consoleRead).id();
        long algorithmId = readValue(algorithmRead).id();
        StringBuilder source = new StringBuilder();
        source.append("public class ReadValueConsolidatedProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(className).append(".main(new String[0]);\n");
        source.append("    Object compiled1 = ").append(className).append(".v")
            .append(compiledId1).append(";\n");
        source.append("    Object compiled2 = ").append(className).append(".v")
            .append(compiledId2).append(";\n");
        source.append("    Object published = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"lib\").entries.get(\"tag\");\n");
        source.append("    check(").append(className).append(".EXPORT_SURFACES == "
            + "deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES, \"the class-level field view "
            + "is the runtime-hosted program-scoped registry\");\n");
        source.append("    check(compiled1 != null && compiled1 == compiled2 && "
            + "compiled1 == published, \"the two compiled reads resolve the owner's "
            + "published carrier object; got \" + compiled1 + \" and \" + compiled2);\n");
        source.append("    check(published instanceof deal.codegen.jvm."
            + "JvmRuntime.FunctionValue, \"the published entry is the "
            + "JvmRuntime.FunctionValue carrier; got \" + published);\n");
        source.append("    Object value = ((deal.codegen.jvm.JvmRuntime.FunctionValue) "
            + "published).fn.invoke(new Object[] {1L});\n");
        source.append("    check(\"t\".equals(value), \"the retained-caller .fn "
            + "projection still calls the module function; got \" + value);\n");
        source.append("    Object consoleRead = ").append(className).append(".v")
            .append(consoleId).append(";\n");
        source.append("    Object consoleEntry = deal.codegen.jvm.JvmRuntime."
            + "EXPORT_SURFACES.get(\"std.console\").entries.get(\"log\");\n");
        source.append("    check(consoleRead == consoleEntry, \"the console read "
            + "resolves the catalog carrier of the surface; got \" + consoleRead);\n");
        source.append("    check(consoleRead instanceof deal.codegen.jvm.JvmRuntime."
            + "StdlibFunctionValue callable && \"CONSOLE_LOG\".equals(callable.rowId) "
            + "&& \"function(string;null)\".equals(callable.signature), \"the console "
            + "carrier carries the row tag and the declared signature; got \" + "
            + "consoleRead);\n");
        source.append("    check(consoleRead == deal.codegen.jvm.JvmRuntime."
            + "stdlibCallable(\"std.console\", \"log\", \"CONSOLE_LOG\", "
            + "\"function(string;null)\", \"(string)->null\"), \"the console read is "
            + "the memoized catalog callable; got \" + consoleRead);\n");
        source.append("    Object algorithmRead = ").append(className).append(".v")
            .append(algorithmId).append(";\n");
        source.append("    Object algorithmEntry = deal.codegen.jvm.JvmRuntime."
            + "EXPORT_SURFACES.get(\"std.string\").entries.get(\"length\");\n");
        source.append("    check(algorithmRead == algorithmEntry "
            + "&& algorithmEntry instanceof deal.codegen.jvm.JvmRuntime."
            + "StdlibFunctionValue row && \"STRING_LENGTH\".equals(row.rowId), "
            + "\"the algorithmic read resolves the memoized row callable; got \" + "
            + "algorithmRead);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 2. The exactly-one binding and both-directions invariant (V3)
    // =========================================================================

    static void testBindingDisciplineAcrossKinds() throws Exception {
        System.out.println("-- V3: one registration per function-typed read kind and the "
            + "both-directions binding invariant --");
        Fixture fixture = threeKindsFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the three-kind probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(Optional.empty(), SemanticIrValidator.validate(project, facts(fixture)),
                "the three-kind lowered project passes the closed project gate");
            LoweredModuleUnit appUnit = project.modules().get(APP);
            List<SemanticOp> reads = readsOf(appUnit);
            checkEq(3, reads.size(),
                "the entry unit carries one read per kind (COMPILED / STDLIB / HOST)");
            SemanticOp compiledRead = readAt(reads, LIB, COMPILED_NAME, 6);
            SemanticOp stdlibRead = readAt(reads, CONSOLE_MODULE, CONSOLE_ROW, 7);
            SemanticOp hostRead = readAt(reads, HOST_MODULE, "ping", 8);
            check(compiledRead != null && stdlibRead != null && hostRead != null,
                "the three-kind fixture carries the three expected reads");
            if (compiledRead == null || stdlibRead == null || hostRead == null) {
                return;
            }
            check(bindingOf(appUnit, compiledRead)
                    instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.moduleId().equals(LIB)
                    && external.exportName().equals(COMPILED_NAME)
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                "exactly one ExternalFunction(SHARED_BODY) registration with the "
                    + "expected owner; got " + bindingOf(appUnit, compiledRead));
            RuntimeDescriptor.Func consoleRow = rowDescriptorOf("std.console", CONSOLE_ROW);
            check(bindingOf(appUnit, stdlibRead)
                    instanceof FunctionExecutionBinding.HostFunction stdlibHost
                    && stdlibHost.hostModuleId().equals(CONSOLE_MODULE)
                    && stdlibHost.exportName().equals(CONSOLE_ROW)
                    && stdlibHost.descriptor().equals(consoleRow),
                "exactly one HostFunction(std.console, log, row descriptor) "
                    + "registration; got " + bindingOf(appUnit, stdlibRead));
            check(bindingOf(appUnit, hostRead)
                    instanceof FunctionExecutionBinding.HostFunction hostHost
                    && hostHost.hostModuleId().equals(payloadOf(hostRead).module())
                    && hostHost.exportName().equals("ping")
                    && hostHost.descriptor().canonicalSpecText().equals("()->string"),
                "exactly one HostFunction(host declaration, ping) registration; got "
                    + bindingOf(appUnit, hostRead));
            for (SemanticOp read : reads) {
                checkEq(1, registrationsOf(appUnit, read),
                    "exactly one registration is keyed by the read's result identity ("
                        + payloadOf(read).module() + "." + payloadOf(read).name() + ")");
            }

            // The doctored duplicate registration fails at registration time
            // and never overwrites the first binding (per kind).
            duplicateRegistrationSeed("COMPILED", LIB, COMPILED_NAME,
                payloadOf(compiledRead).descriptor(), Map.of(LIB, ModuleRoute.SHARED), true);
            duplicateRegistrationSeed("STDLIB", CONSOLE_MODULE, CONSOLE_ROW,
                consoleRow, Map.of(), false);
            duplicateRegistrationSeed("HOST", payloadOf(hostRead).module(), "ping",
                payloadOf(hostRead).descriptor(), Map.of(), false);

            // A doctored zero registration fails the closed gate per kind.
            zeroRegistrationSeed(appUnit, compiledRead, facts(fixture), "COMPILED");
            zeroRegistrationSeed(appUnit, stdlibRead, facts(fixture), "STDLIB");
            zeroRegistrationSeed(appUnit, hostRead, facts(fixture), "HOST");
        } finally {
            deleteRecursively(fixture.root());
        }

        // The both-directions invariant after a COMPILED read (the
        // consolidated compiled + stdlib project): the owner-side
        // registration of the published value stays the owner's
        // LoweredBody, the read-side registration stays addressable by the
        // read result's identity, and a doctored re-keying of the shared
        // value fails the closed gate.
        Fixture composition = compositionFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(composition);
            if (result.project() == null) {
                fail("the both-directions probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            SemanticOp publish = publishOpOf(libUnit);
            SemanticOp read = readAt(readsOf(appUnit), LIB, COMPILED_NAME,
                COMPILED_READ_LINE);
            check(publish != null && read != null,
                "the both-directions probe carries the publication and the read");
            if (publish == null || read == null) {
                return;
            }
            ValueId publishedValue =
                ((KindPayload.ExportPublishPayload) publish.payload()).value();
            check(libUnit.functionBindings()
                    .get(new FunctionAllocationIdentity(publishedValue.id()))
                    instanceof FunctionExecutionBinding.LoweredBody,
                "the owner-side runtime resolution of the published value stays the "
                    + "owner's LoweredBody (the read never re-keys the value)");
            check(bindingOf(appUnit, read)
                    instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                "the read-side registration stays addressable by the read result's "
                    + "allocation identity; got " + bindingOf(appUnit, read));

            // The doctored read-time re-keying of the shared value: the
            // read's registration moved onto the published value's identity.
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> doctored =
                new LinkedHashMap<>(appUnit.functionBindings());
            doctored.remove(readKey(read));
            doctored.put(new FunctionAllocationIdentity(publishedValue.id()),
                new FunctionExecutionBinding.ExternalFunction(LIB, COMPILED_NAME,
                    (RuntimeDescriptor.Func) payloadOf(read).descriptor(),
                    ExternalExecutionOwner.SHARED_BODY));
            LoweredModuleUnit mutated = new LoweredModuleUnit(appUnit.formatVersion(),
                appUnit.semanticProfile(), appUnit.moduleId(), appUnit.interfaceHash(),
                appUnit.loweringContextHash(), appUnit.requiredCapabilities(),
                appUnit.constructCoverage(), appUnit.classLayouts(), appUnit.functions(),
                appUnit.moduleInit(), appUnit.exportPlan(), doctored, appUnit.ops());
            Optional<CompilerDiagnostic> failure =
                SemanticIrValidator.validate(mutated, facts(composition));
            check(failure.isPresent()
                    && failure.get().message().contains("R-FUNCTION-BINDING"),
                "a doctored re-keying of the shared value (the read's registration moved "
                    + "onto the published value's identity) fails the closed gate with "
                    + "R-FUNCTION-BINDING; got "
                    + (failure.isEmpty() ? "no diagnostic" : failure.get().message()));

            // Both directions in one successful oracle run: the published
            // value's identity and the read's identity resolve to distinct
            // registrations of distinct units, and the run's read atom is
            // the published value's own creation atom.
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the both-directions probe drive succeeds: " + run.terminal());
            SemanticOp boundary = exportBoundaryOf(libUnit, publish.opId());
            String publicationAtom = boundary == null ? null
                : startInputAtomOf(run, boundary.opId());
            checkEq(publicationAtom, successAtomOf(run, read.opId()),
                "the read publishes the published value's identity (the owner-side "
                    + "runtime resolution is unchanged by the read)");
        } finally {
            deleteRecursively(composition.root());
        }
    }

    /** The duplicate-registration seed: rejected at registration time, never overwritten. */
    private static void duplicateRegistrationSeed(String what, ModuleId moduleId,
            String exportName, RuntimeDescriptor descriptor, Map<ModuleId, ModuleRoute> routes,
            boolean compiledImport) {
        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        ValueId value = new ValueId(99_000 + registrationSeedSequence++);
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(value.id());
        KindPayload.ExportReadPayload payload =
            new KindPayload.ExportReadPayload(moduleId, exportName, descriptor, value);
        FunctionBindingRegistry.FunctionValueImportFacts facts = compiledImport
            ? new FunctionBindingRegistry.FunctionValueImportFacts(null, moduleId,
                exportName, descriptor)
            : new FunctionBindingRegistry.FunctionValueImportFacts(moduleId, null,
                exportName, descriptor);
        registry.registerHostOrExternalImportWithRoutes(identity, payload, facts, routes);
        FunctionExecutionBinding first = registry.bindings().get(identity);
        check(first != null && registry.size() == 1,
            "the " + what + " read registers one binding: " + first);
        boolean rejected = false;
        try {
            registry.registerHostOrExternalImportWithRoutes(identity, payload, facts,
                routes);
        } catch (IllegalStateException expected) {
            rejected = true;
        }
        check(rejected, "the " + what + " duplicate registration is rejected at "
            + "registration time");
        check(registry.size() == 1 && registry.bindings().get(identity) == first,
            "the " + what + " first registration is never overwritten; got "
                + registry.bindings());
        check(compiledImport
                ? first instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY
                : first instanceof FunctionExecutionBinding.HostFunction host
                    && host.hostModuleId().equals(moduleId)
                    && host.exportName().equals(exportName),
            "the " + what + " first registration keeps the expected imported shape; "
                + "got " + first);
    }

    /** The per-run registration-seed identity sequence (deterministic, fresh keys). */
    private static int registrationSeedSequence = 1;

    /** The zero-registration seed: the read result loses its key, the gate rejects. */
    private static void zeroRegistrationSeed(LoweredModuleUnit unit, SemanticOp read,
            SemanticIrValidator.ComparisonFacts facts, String what) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> doctored =
            new LinkedHashMap<>(unit.functionBindings());
        doctored.remove(readKey(read));
        LoweredModuleUnit mutated = new LoweredModuleUnit(unit.formatVersion(),
            unit.semanticProfile(), unit.moduleId(), unit.interfaceHash(),
            unit.loweringContextHash(), unit.requiredCapabilities(),
            unit.constructCoverage(), unit.classLayouts(), unit.functions(),
            unit.moduleInit(), unit.exportPlan(), doctored, unit.ops());
        Optional<CompilerDiagnostic> failure = SemanticIrValidator.validate(mutated, facts);
        check(failure.isPresent()
                && failure.get().message().contains("R-FUNCTION-BINDING"),
            "the " + what + " function-typed read with zero registrations fails the "
                + "closed gate with R-FUNCTION-BINDING; got "
                + (failure.isEmpty() ? "no diagnostic" : failure.get().message()));
    }

    // =========================================================================
    // 3. The negative seeds through the production arm (V5)
    // =========================================================================

    static void testNegativeSeedsThroughProductionArm() throws Exception {
        System.out.println("-- V5: the five read-domain negative seeds through the "
            + "production arm (E6005, nothing staged, the previous artifact set "
            + "byte-identical) --");

        // (a) A non-exported member read: the resolved alias's checker module
        // symbol does not declare the member.
        Fixture nonExported = compiledReadFixture();
        try {
            CheckedProjectInput doctored = doctorEntryExports(nonExported, "lib",
                Map.of());
            Fixture seed = new Fixture(nonExported.root(), doctored, nonExported.index(),
                nonExported.manifests(), nonExported.surface(),
                nonExported.externCModules(), nonExported.declarationIdentities(),
                nonExported.distributionHome());
            assertProductionSeed(seed, "the non-exported member read",
                List.of("lib", "tag", "not a declared export"));
        } finally {
            deleteRecursively(nonExported.root());
        }

        // (b) An alias with no resolved import fact.
        Fixture unresolved = compiledReadFixture();
        try {
            CheckedProjectInput doctored = doctorEntryImports(unresolved);
            Fixture seed = new Fixture(unresolved.root(), doctored, unresolved.index(),
                unresolved.manifests(), unresolved.surface(),
                unresolved.externCModules(), unresolved.declarationIdentities(),
                unresolved.distributionHome());
            assertProductionSeed(seed, "the unresolved-alias read",
                List.of("resolved import fact", "lib"));
        } finally {
            deleteRecursively(unresolved.root());
        }

        // (c) A STDLIB member outside the closed catalog: the project-local
        // declaration carries a marker export the catalog does not name.
        Fixture outOfCatalog = stdlibOverrideFixture(OUT_OF_CATALOG_STD_CONSOLE,
            OUT_OF_CATALOG_APP_SOURCE);
        try {
            assertProductionSeed(outOfCatalog, "the out-of-catalog stdlib read",
                List.of("std.console", "localMarker",
                    "outside the closed stdlib catalog"));
        } finally {
            deleteRecursively(outOfCatalog.root());
        }

        // (d) A STDLIB descriptor mismatch: the checked descriptor differs
        // from the catalog row's declared descriptor.
        Fixture mismatch = stdlibOverrideFixture(MISMATCH_STD_CONSOLE,
            MISMATCH_APP_SOURCE);
        try {
            assertProductionSeed(mismatch, "the stdlib descriptor mismatch read",
                List.of("std.console", "(int)->null", "(string)->null"));
        } finally {
            deleteRecursively(mismatch.root());
        }

        // (e) A class-descriptor read (a class used as a value).
        Fixture classRead = classReadFixture();
        try {
            assertProductionSeed(classRead, "the class-descriptor read",
                List.of("lib.Point", "class-descriptor read"));
        } finally {
            deleteRecursively(classRead.root());
        }
    }

    /**
     * One negative seed through the production arm: the exact E6005
     * {@code CONSTRUCT_UNLOWERED}, nothing staged, and the previous
     * artifact set byte-identical.
     */
    private static void assertProductionSeed(Fixture fixture, String what,
            List<String> tokens) throws Exception {
        // The lowering itself also fails closed with no project.
        SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
        check(lowered.hasErrors() && lowered.project() == null,
            what + " fails closed with no project at lowering");
        if (!lowered.hasErrors()) {
            fail(what + " lowers");
            return;
        }
        CompilerDiagnostic loweringDiagnostic = lowered.diagnostics().get(0);
        check("E6005".equals(loweringDiagnostic.code())
                && loweringDiagnostic.message()
                    .contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
            what + " reports E6005 CONSTRUCT_UNLOWERED at lowering: "
                + loweringDiagnostic);

        Path out = fixture.root().resolve("out-arm");
        writeFileIn(out, "app.lua", "-- previous artifact\n");
        writeFileIn(out, "deal/runtime.lua", "-- previous runtime\n");
        writeFileIn(out, "std/console.lua", "-- previous stdlib\n");
        Map<String, String> before = snapshotTree(out);
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = emit(fixture, Backend.LUAJIT, stager, false);
        } finally {
            stager.discard();
        }
        check(!result.emitted(), what + " fails closed through the production arm");
        CompilerDiagnostic diagnostic = result.firstDiagnostic();
        check(diagnostic != null && "E6005".equals(diagnostic.code())
                && diagnostic.message().contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
            what + " reports E6005 CONSTRUCT_UNLOWERED through the production arm: "
                + result.diagnostics());
        if (diagnostic != null) {
            for (String token : tokens) {
                check(diagnostic.message().contains(token),
                    what + " names '" + token + "': " + diagnostic.message());
            }
        }
        check(stager.stagedSet().relativePaths().isEmpty(),
            what + " stages nothing through the production arm");
        check(before.equals(snapshotTree(out)),
            what + " leaves the previous artifact set byte-identical");
    }

    /** The G3 doctored fact: the alias's checker module symbol loses the member. */
    private static CheckedProjectInput doctorEntryExports(Fixture fixture, String alias,
            Map<String, deal.types.Type> exports) {
        CheckedProjectInput project = fixture.checkedProject();
        List<CheckedModuleInput> modules = new ArrayList<>();
        for (CheckedModuleInput module : project.modules()) {
            if (!module.moduleId().equals(project.entryModule())) {
                modules.add(module);
                continue;
            }
            FunctionDeclaration main = functionNamed(module.ast(), "main");
            if (main == null) {
                fail("the entry module declares main");
                return project;
            }
            SymbolTable scope = module.checks().scopeMap().get(main.body());
            if (scope == null) {
                fail("the entry main body carries a checker scope");
                return project;
            }
            Symbol original = module.checks().symbolTable().resolve(alias);
            if (!(original instanceof Symbol.ModuleSymbol moduleSymbol)) {
                fail("alias '" + alias + "' resolves to a checker module symbol");
                return project;
            }
            scope.define(alias, new Symbol.ModuleSymbol(alias, exports,
                moduleSymbol.importSpan()));
            modules.add(new CheckedModuleInput(module.moduleId(), module.sourceId(),
                module.sourcePath(), module.ast(), module.checks(), module.imports(),
                module.exports(), module.kind()));
        }
        return new CheckedProjectInput(project.invocation(), project.entryModule(),
            modules, project.releaseStateHash());
    }

    /** The unresolved-alias doctored fact: the entry module keeps no import fact. */
    private static CheckedProjectInput doctorEntryImports(Fixture fixture) {
        CheckedProjectInput project = fixture.checkedProject();
        List<CheckedModuleInput> modules = new ArrayList<>();
        for (CheckedModuleInput module : project.modules()) {
            if (!module.moduleId().equals(project.entryModule())) {
                modules.add(module);
                continue;
            }
            modules.add(new CheckedModuleInput(module.moduleId(), module.sourceId(),
                module.sourcePath(), module.ast(), module.checks(), List.of(),
                module.exports(), module.kind()));
        }
        return new CheckedProjectInput(project.invocation(), project.entryModule(),
            modules, project.releaseStateHash());
    }

    private static FunctionDeclaration functionNamed(ProgramNode program, String name) {
        for (StatementNode statement : program.statements()) {
            StatementNode declared = statement instanceof ExportDeclaration export
                ? export.declaration() : statement;
            if (declared instanceof FunctionDeclaration function
                    && function.name().equals(name)) {
                return function;
            }
        }
        return null;
    }

    // =========================================================================
    // 4. Emission agreement and determinism (V7)
    // =========================================================================

    static void testEmissionAgreementAndDeterminism() throws Exception {
        System.out.println("-- V7: the trace-mode and production emissions carry the "
            + "identical read operation and repeat byte-identically --");
        Fixture fixture = compositionFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the emission probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            List<SemanticOp> reads = readsOf(project.modules().get(APP));
            String traceLua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            String productionLua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            checkEq(traceLua, LuaSemanticEmitter.emitProject(project, result.tables(),
                    result.registries()),
                "the repeated trace-mode LuaJIT project emission is byte-identical");
            checkEq(productionLua, LuaSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(), fixture.surface()),
                "the repeated production LuaJIT project emission is byte-identical");

            // The read operation is textually the same surface lookup in both
            // modes (per read, per kind).
            String compiledReadText = "__exportValue(\"lib\", \"tag\")";
            String consoleEntryCall = luaStdlibEntryCall("std.console", CONSOLE_ROW);
            String algorithmEntryCall = luaStdlibEntryCall("std.string", ALGORITHM_ROW);
            for (SemanticOp read : reads) {
                long id = readValue(read).id();
                String expected = "S.v" + id + " = " + compiledReadText;
                if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                    expected = "S.v" + id + " = " + consoleEntryCall;
                } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                    expected = "S.v" + id + " = " + algorithmEntryCall;
                }
                checkEq(1, countOccurrences(traceLua, expected),
                    "the trace-mode read operation is the surface lookup: " + expected);
                checkEq(1, countOccurrences(productionLua, expected),
                    "the production read operation is the identical surface lookup: "
                        + expected);
            }

            // The mode-parameterized surfaces: everything before the mode
            // terminal (and outside the trace protocol/flag) is byte-identical.
            checkEq(luaEmissionBody(traceLua), luaEmissionBody(productionLua),
                "the two LuaJIT mode emissions share one body except the mode flag, "
                    + "the trace protocol, and the mode terminal");
            check(traceLua.contains("local __traceMode = true"),
                "the trace-mode LuaJIT emission carries the trace mode flag");
            check(productionLua.contains("local __traceMode = false"),
                "the production LuaJIT emission carries the production mode flag");
            check(traceLua.contains("io.stderr:write(\"R|success|null\\n\")")
                    && !traceLua.contains("DEAL_ERROR_CODE"),
                "the trace-mode terminal is the R| protocol terminal");
            check(productionLua.contains("print(\"DEAL_ERROR_CODE: \"..__mainErr.code)")
                    && !productionLua.contains("R|success|null"),
                "the production terminal is the DEAL_ERROR_CODE terminal");
            check(productionLua.endsWith("return __exportSurfaces[\"app\"]\n"),
                "the production chunk returns the entry module's surface");

            // The JVM sessions: the identical read operation, repeated
            // emissions byte-identical, and the mode surfaces pinned.
            JvmSemanticEmitter.EmissionResult traceJvm = JvmSemanticEmitter.emitProject(
                project, result.tables(), result.registries());
            JvmSemanticEmitter.EmissionResult productionJvm =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), JvmBackend.classNameFor(APP.path()),
                    fixture.surface());
            checkEq(traceJvm.source(), JvmSemanticEmitter.emitProject(project,
                    result.tables(), result.registries()).source(),
                "the repeated trace-mode JVM project emission is byte-identical");
            checkEq(productionJvm.source(), JvmSemanticEmitter.emitProductionProject(
                    project, result.tables(), result.registries(),
                    JvmBackend.classNameFor(APP.path()), fixture.surface()).source(),
                "the repeated production JVM project emission is byte-identical");
            String consoleCarrierCall = jvmStdlibCarrierCall("std.console", CONSOLE_ROW);
            String algorithmCarrierCall = jvmStdlibCarrierCall("std.string",
                ALGORITHM_ROW);
            for (SemanticOp read : reads) {
                long id = readValue(read).id();
                String expected = "v" + id + " = exportSurface(\"lib\").read(\"tag\");";
                if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                    expected = "v" + id + " = " + consoleCarrierCall + ";";
                } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                    expected = "v" + id + " = " + algorithmCarrierCall + ";";
                }
                checkEq(1, countOccurrences(traceJvm.source(), expected),
                    "the trace-mode JVM read operation is the surface lookup: "
                        + expected);
                checkEq(1, countOccurrences(productionJvm.source(), expected),
                    "the production JVM read operation is the identical surface "
                        + "lookup: " + expected);
            }
            checkEq(jvmEmissionBody(traceJvm.source()),
                jvmEmissionBody(productionJvm.source()),
                "the two JVM mode emissions share one body except the mode flag, the "
                    + "trace protocol, and the mode terminal");
            check(traceJvm.source().contains("JvmRuntime.setTraceEnabled(true)")
                    && traceJvm.source().contains("System.err.println(\"R|success|null\")"),
                "the trace-mode JVM emission carries the trace mode and protocol");
            check(productionJvm.source().contains("JvmRuntime.setTraceEnabled(false)")
                    && productionJvm.source().contains("DEAL_ERROR_CODE")
                    && !productionJvm.source().contains("R|success|null"),
                "the production JVM emission carries the production mode and terminal");

            // The per-unit sessions of both targets emit the same read
            // operation in trace and production mode (V8c).
            LoweredModuleUnit appUnit = project.modules().get(APP);
            StructuredBodyTable appTable = result.tables().get(APP);
            String perUnitTraceLua = LuaSemanticEmitter.emitModule(appUnit, appTable);
            String perUnitProductionLua = LuaSemanticEmitter.emitProductionModule(appUnit,
                appTable, true);
            JvmSemanticEmitter.EmissionResult perUnitTraceJvm =
                JvmSemanticEmitter.emitModule(appUnit, appTable);
            JvmSemanticEmitter.EmissionResult perUnitProductionJvm =
                JvmSemanticEmitter.emitProductionModule(appUnit, appTable, true,
                    JvmBackend.classNameFor(APP.path()));
            for (SemanticOp read : reads) {
                long id = readValue(read).id();
                String luaExpected = "S.v" + id + " = " + compiledReadText;
                String jvmExpected = "v" + id + " = exportSurface(\"lib\").read(\"tag\");";
                if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                    luaExpected = "S.v" + id + " = " + consoleEntryCall;
                    jvmExpected = "v" + id + " = " + consoleCarrierCall + ";";
                } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                    luaExpected = "S.v" + id + " = " + algorithmEntryCall;
                    jvmExpected = "v" + id + " = " + algorithmCarrierCall + ";";
                }
                checkEq(1, countOccurrences(perUnitTraceLua, luaExpected),
                    "the per-unit trace-mode LuaJIT session emits the read: "
                        + luaExpected);
                checkEq(1, countOccurrences(perUnitProductionLua, luaExpected),
                    "the per-unit production LuaJIT session emits the same read: "
                        + luaExpected);
                checkEq(1, countOccurrences(perUnitTraceJvm.source(), jvmExpected),
                    "the per-unit trace-mode JVM session emits the read: " + jvmExpected);
                checkEq(1, countOccurrences(perUnitProductionJvm.source(), jvmExpected),
                    "the per-unit production JVM session emits the same read: "
                        + jvmExpected);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The common body of one LuaJIT project emission: every line up to the
     * mode terminal, with the mode flag canonicalized and the
     * production-only event-helper no-ops dropped — the
     * mode-parameterized surfaces are exactly the flag, the trace
     * protocol, and the terminal.
     */
    private static List<String> luaEmissionBody(String text) {
        List<String> lines = new ArrayList<>();
        for (String line : text.split("\n", -1)) {
            if (line.startsWith("if os.getenv(\"DEAL_DEFER_MAIN\")")) {
                break;
            }
            if (line.startsWith("local __traceMode = ")) {
                lines.add("local __traceMode = <mode>");
                continue;
            }
            if (line.equals("__ev = function() end")
                    || line.equals("__normalizeEvent = function() end")) {
                continue;
            }
            lines.add(line);
        }
        return lines;
    }

    /**
     * The common body of one JVM project emission: every line up to the
     * {@code main} declaration, with the class name and the trace-enabled
     * flag canonicalized, the trace-protocol statements dropped, and the
     * production-only host ABI seam block dropped — the
     * mode-parameterized surfaces are exactly the class-name spelling, the
     * flag, the trace protocol, the host ABI seam, and the terminal.
     */
    private static List<String> jvmEmissionBody(String text) {
        List<String> lines = new ArrayList<>();
        boolean hostAbi = false;
        for (String line : text.split("\n", -1)) {
            if (line.equals("  public static void main(String[] args) {")) {
                break;
            }
            if (line.startsWith("public final class ")) {
                lines.add("public final class <entry> {");
                continue;
            }
            if (line.startsWith("  // ---- JVM host ABI surface")) {
                // The production-only seam block: drop it with its
                // leading blank line.
                if (!lines.isEmpty() && lines.get(lines.size() - 1).isEmpty()) {
                    lines.remove(lines.size() - 1);
                }
                hostAbi = true;
                continue;
            }
            if (hostAbi) {
                if (line.startsWith("  static ") && line.contains("FunctionValue ")) {
                    hostAbi = false;
                } else {
                    continue;
                }
            }
            if (line.contains("JvmRuntime.ev(")) {
                continue;
            }
            if (line.trim().startsWith("JvmRuntime.setTraceEnabled(")) {
                lines.add("    JvmRuntime.setTraceEnabled(<mode>);");
                continue;
            }
            lines.add(line);
        }
        return lines;
    }

    // =========================================================================
    // 5. The per-unit multi-chunk resolution probe (V8)
    // =========================================================================

    static void testPerUnitMultiChunkResolution() throws Exception {
        System.out.println("-- V8: the absent-slot projection in all three consumers "
            + "and the per-unit program-scoped registry resolution --");
        Fixture fixture = compositionFixture();
        Path workspace = Files.createTempDirectory("read-value-iv-per-unit");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the per-unit probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            List<SemanticOp> reads = readsOf(appUnit);
            List<String> readOps = new ArrayList<>();
            for (SemanticOp read : reads) {
                readOps.add(read.opId().module().path() + "#" + read.opId().id());
            }

            // (a) The absent-slot projection: the partial drive (only the
            // entry module/artifact initialized) projects the same
            // canonical absent atom in all three consumers.
            SemanticRuntimeModel.ConsumerRun partial = SemanticOracle.execute(project,
                result.tables(), result.registries(), null);
            List<String> partialAtoms = new ArrayList<>();
            for (SemanticOp read : reads) {
                String atom = successAtomOf(partial, read.opId());
                if (atom != null) {
                    partialAtoms.add(atom);
                }
            }
            checkEq(List.of("missing"), partialAtoms,
                "the oracle's partial drive projects the absent-slot value for the "
                    + "compiled read (Value.MissingValue, atomizing as missing)");
            check(partial.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                    failure && "E8001".equals(failure.error().code()),
                "the oracle's partial drive fails at the function-typed binding boundary "
                    + "(the absent-slot value is never an invocation target): "
                    + partial.terminal());

            Path luaChunk = workspace.resolve("app.lua");
            Files.writeString(luaChunk, LuaSemanticEmitter.emitModule(appUnit,
                result.tables().get(APP)), StandardCharsets.UTF_8);
            Path luaAbsentDriver = workspace.resolve("absent.lua");
            Files.writeString(luaAbsentDriver,
                "dofile(" + luaString(luaChunk.toAbsolutePath().toString()) + ")\n",
                StandardCharsets.UTF_8);
            ProcessOutcome luaAbsent = runProcess(List.of("luajit",
                luaAbsentDriver.toAbsolutePath().toString()), workspace);
            checkEq(0, luaAbsent.exitCode(),
                "the entry-only per-unit LuaJIT chunk runs: " + luaAbsent.output());
            checkEq(List.of("missing"),
                luaReadAtoms(luaAbsent.stderr(), List.of(readOps.get(0))),
                "the entry-only per-unit LuaJIT chunk projects the __MISSING sentinel");

            JvmSemanticEmitter.EmissionResult appEmission = JvmSemanticEmitter.emitModule(
                appUnit, result.tables().get(APP));
            Path appSource = workspace.resolve(appEmission.className() + ".java");
            Files.writeString(appSource, appEmission.source(), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            String absentDriver = "ReadValueAbsentProbe";
            Files.writeString(workspace.resolve(absentDriver + ".java"),
                absentProbeSource(appEmission.className(), reads), StandardCharsets.UTF_8);
            ProcessOutcome absentCompile = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                appSource.toAbsolutePath().toString(),
                workspace.resolve(absentDriver + ".java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, absentCompile.exitCode(),
                "the entry-only per-unit JVM class compiles: " + absentCompile.output());
            if (absentCompile.exitCode() == 0) {
                ProcessOutcome absentRun = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, absentDriver), workspace);
                checkEq(0, absentRun.exitCode(),
                    "the entry-only per-unit JVM class runs: " + absentRun.output());
                check(absentRun.stdout().contains("PROBE-OK")
                        && absentRun.stdout().contains("atom=missing"),
                    "the entry-only per-unit JVM class projects JvmRuntime.MISSING, "
                        + "atomizing as missing; stdout="
                        + absentRun.stdout().replace("\n", "\\n") + " stderr="
                        + absentRun.stderr().replace("\n", "\\n"));
            }

            // (b) The program-scoped registry: the owner chunk publishes,
            // then the entry chunk resolves the published value — the
            // identical object for two reads — and both chunks resolve the
            // identical memoized catalog callable.
            Path libChunk = workspace.resolve("lib.lua");
            Files.writeString(libChunk, LuaSemanticEmitter.emitModule(libUnit,
                result.tables().get(LIB)), StandardCharsets.UTF_8);
            Path perUnitDriver = workspace.resolve("per-unit.lua");
            StringBuilder lua = new StringBuilder();
            lua.append("local __libOk, __libErr = pcall(dofile, ")
                .append(luaString(libChunk.toAbsolutePath().toString())).append(")\n");
            lua.append("if not __libOk then print(\"PROBE-FAIL: \"..tostring(__libErr)) "
                + "os.exit(1) end\n");
            lua.append("local __libMainOk, __libMainErr = pcall(__dealMain)\n");
            lua.append("if not __libMainOk then print(\"PROBE-FAIL: \"..tostring("
                + "__libMainErr)) os.exit(1) end\n");
            lua.append("local __appOk, __appErr = pcall(dofile, ")
                .append(luaString(luaChunk.toAbsolutePath().toString())).append(")\n");
            lua.append("if not __appOk then print(\"PROBE-FAIL: \"..tostring(__appErr)) "
                + "os.exit(1) end\n");
            lua.append("local __ok, __err = pcall(__dealMain)\n");
            lua.append("if not __ok then print(\"PROBE-FAIL: \"..tostring(__err)) "
                + "os.exit(1) end\n");
            lua.append("if __exportSurfaces[\"lib\"][\"tag\"].__val == nil then "
                + "print(\"PROBE-FAIL: no published value\") os.exit(1) end\n");
            lua.append("local __first = __stdlibEntries[\"std.console\""
                + "..string.char(1)..\"log\"]\n");
            lua.append("local __second = __exportSurfaces[\"std.console\"]"
                + "[\"log\"]\n");
            lua.append("if __first == nil or __first ~= __second then "
                + "print(\"PROBE-FAIL: the catalog callable is not program-scoped\") "
                + "os.exit(1) end\n");
            lua.append("print(\"PROBE-OK\")\n");
            Files.writeString(perUnitDriver, lua.toString(), StandardCharsets.UTF_8);
            ProcessOutcome perUnitRun = runProcessWithEnv(List.of("luajit",
                perUnitDriver.toAbsolutePath().toString()), workspace,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(perUnitRun.exitCode() == 0 && perUnitRun.stdout().contains("PROBE-OK"),
                "the two-chunk per-unit LuaJIT drive resolves the program-scoped "
                    + "registry and the memoized callable: exit=" + perUnitRun.exitCode()
                    + " stdout=" + perUnitRun.stdout().replace("\n", "\\n") + " stderr="
                    + perUnitRun.stderr().replace("\n", "\\n"));
            String publicationAtom = luaPublicationAtom(perUnitRun.stderr(), LIB.path(),
                libUnit);
            List<String> atoms = luaReadAtoms(perUnitRun.stderr(),
                List.of(readOps.get(0), readOps.get(1)));
            check(publicationAtom != null && publicationAtom.startsWith("ref:"),
                "the owner chunk's publication atom is observable: " + publicationAtom);
            check(atoms.size() == 2 && atoms.get(0).equals(atoms.get(1))
                    && atoms.get(0).equals(publicationAtom),
                "the per-unit entry chunk resolves the owner chunk's published value "
                    + "(the program-scoped registry, not a session-local map); got "
                    + atoms + " vs " + publicationAtom);

            // The JVM per-unit drive: the owner class publishes first, then
            // the entry class resolves the identical published object, the
            // identical carrier for two reads, and the runtime-hosted
            // catalog callable.
            JvmSemanticEmitter.EmissionResult libEmission =
                JvmSemanticEmitter.emitModule(libUnit, result.tables().get(LIB));
            Path libSource = workspace.resolve(libEmission.className() + ".java");
            Files.writeString(libSource, libEmission.source(), StandardCharsets.UTF_8);
            String registryDriver = "ReadValueRegistryProbe";
            Files.writeString(workspace.resolve(registryDriver + ".java"),
                perUnitProbeSource(libEmission.className(), appEmission.className(),
                    reads),
                StandardCharsets.UTF_8);
            ProcessOutcome registryCompile = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                libSource.toAbsolutePath().toString(),
                appSource.toAbsolutePath().toString(),
                workspace.resolve(registryDriver + ".java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, registryCompile.exitCode(),
                "the per-unit JVM classes compile with javac --release 25 -proc:none: "
                    + registryCompile.output());
            if (registryCompile.exitCode() == 0) {
                ProcessOutcome registryRun = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, registryDriver), workspace);
                check(registryRun.exitCode() == 0
                        && registryRun.stdout().contains("PROBE-OK"),
                    "the per-unit JVM classes resolve the owner class's published value "
                        + "through the runtime-hosted registry and the memoized callable; "
                        + "exit=" + registryRun.exitCode() + " stdout="
                        + registryRun.stdout().replace("\n", "\\n") + " stderr="
                        + registryRun.stderr().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /** The entry-only JVM probe: the first read projects the MISSING sentinel. */
    private static String absentProbeSource(String appClass, List<SemanticOp> reads) {
        long id = readValue(reads.get(0)).id();
        StringBuilder source = new StringBuilder();
        source.append("public class ReadValueAbsentProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    try {\n");
        source.append("      ").append(appClass).append(".dealMain();\n");
        source.append("      check(false, \"the entry-only drive fails at the "
            + "function-typed binding boundary\");\n");
        source.append("    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n");
        source.append("      check(\"E8001\".equals(e.code), \"the binding boundary "
            + "raises the pinned E8001; got \" + e.code);\n");
        source.append("    }\n");
        source.append("    Object absent = ").append(appClass).append(".v").append(id)
            .append(";\n");
        source.append("    check(absent == deal.codegen.jvm.JvmRuntime.MISSING, \"the "
            + "entry-only read projects the absent-slot sentinel; got \" + absent);\n");
        source.append("    String atom = deal.codegen.jvm.JvmRuntime.atom(absent, "
            + "\"null\");\n");
        source.append("    check(\"missing\".equals(atom), \"the absent-slot sentinel "
            + "atomizes as missing; got \" + atom);\n");
        source.append("    System.out.println(\"atom=\" + atom);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    /**
     * The JVM per-unit registry probe: the owner class publishes, the entry
     * class resolves the published object for both compiled reads and the
     * memoized catalog callables for the stdlib reads.
     */
    private static String perUnitProbeSource(String libClass, String appClass,
            List<SemanticOp> reads) {
        long compiledId1 = readValue(reads.get(0)).id();
        long compiledId2 = readValue(reads.get(1)).id();
        long consoleId = -1;
        long algorithmId = -1;
        for (SemanticOp read : reads) {
            if (payloadOf(read).module().equals(CONSOLE_MODULE)) {
                consoleId = readValue(read).id();
            } else if (payloadOf(read).module().equals(STRING_MODULE)) {
                algorithmId = readValue(read).id();
            }
        }
        StringBuilder source = new StringBuilder();
        source.append("public class ReadValueRegistryProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(libClass).append(".dealMain();\n");
        source.append("    ").append(appClass).append(".dealMain();\n");
        source.append("    Object read1 = ").append(appClass).append(".v")
            .append(compiledId1).append(";\n");
        source.append("    Object read2 = ").append(appClass).append(".v")
            .append(compiledId2).append(";\n");
        source.append("    Object published = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"lib\").entries.get(\"tag\");\n");
        source.append("    check(").append(appClass).append(".EXPORT_SURFACES == "
            + "deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES, \"the class-level field view "
            + "is the runtime-hosted program-scoped registry\");\n");
        source.append("    check(read1 != null && read1 == read2 && read1 == published, "
            + "\"the per-unit entry class resolves the owner class's published value "
            + "for both reads; got \" + read1 + \" and \" + read2);\n");
        source.append("    Object consoleRead = ").append(appClass).append(".v")
            .append(consoleId).append(";\n");
        source.append("    check(consoleRead == deal.codegen.jvm.JvmRuntime."
            + "stdlibCallable(\"std.console\", \"log\", \"CONSOLE_LOG\", "
            + "\"function(string;null)\", \"(string)->null\"), \"the per-unit console "
            + "read is the runtime-hosted memoized callable; got \" + consoleRead);\n");
        source.append("    check(consoleRead == deal.codegen.jvm.JvmRuntime."
            + "STDLIB_CALLABLES.get(\"std.console\" + (char) 1 + \"log\"), "
            + "\"the callable registry is program-scoped; got \" + consoleRead);\n");
        source.append("    Object algorithmRead = ").append(appClass).append(".v")
            .append(algorithmId).append(";\n");
        source.append("    check(algorithmRead == deal.codegen.jvm.JvmRuntime."
            + "STDLIB_CALLABLES.get(\"std.string\" + (char) 1 + \"length\"), "
            + "\"the algorithmic callable is the runtime-hosted memoized entry; got \" "
            + "+ algorithmRead);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 6. Pin retargeting and registration
    // =========================================================================

    static void testPinsAndRegistration() throws Exception {
        System.out.println("-- the pin retargeting and the gate-manifest registration --");
        Path root = repoRoot();
        if (root == null) {
            fail("the repository root is discoverable from the test process");
            return;
        }
        String manifest = Files.readString(root.resolve("tools/gate-manifest.sh"),
            StandardCharsets.UTF_8);
        List<String> focusedMains = List.of(
            "ImportMemberReadArmTest", "CompiledExportReadRealizationTest",
            "StdlibExportReadRealizationTest", "HostExportReadRealizationTest",
            "ReadValueIntegrationVerificationTest");
        for (String mainClass : focusedMains) {
            check(Files.isRegularFile(root.resolve("test/" + mainClass + ".java")),
                "the focused read main " + mainClass + ".java stays in the tree");
            check(manifest.contains("deal.test." + mainClass),
                "the focused read main " + mainClass
                    + " is registered in tools/gate-manifest.sh");
        }
        List<String> pins = List.of(
            "ModuleExportSurfaceTest", "LuaProductionProjectEmissionTest",
            "JvmProductionProjectEmissionTest", "StdlibCallLoweringTest",
            "ModuleSystemTest", "ProductionProjectEmissionTest",
            "AsyncStartAwaitIntegrationTest");
        for (String pin : pins) {
            check(Files.isRegularFile(root.resolve("test/" + pin + ".java")),
                "the retargeted pin " + pin + ".java stays in the tree (none deleted)");
            check(manifest.contains("deal.test." + pin),
                "the retargeted pin " + pin
                    + " stays registered in tools/gate-manifest.sh");
        }
        // The landed async-entry matrix stays registered (the partial drive's
        // read projection is this leaf's absent-slot assertion).
        check(manifest.contains("deal.test.AsyncStartAwaitIntegrationTest"),
            "the landed async-entry matrix stays registered in tools/gate-manifest.sh");

        // The previously pinned value-read E6005 assertions now assert the
        // realized behavior: the stdlib value read lowers to a validated
        // unit through the call machine and the read's invocation lowers the
        // landed CALL(INDIRECT) with the Static binding. No lowerer-side
        // invocation guard is asserted there.
        String stdlibCall = Files.readString(
            root.resolve("test/StdlibCallLoweringTest.java"), StandardCharsets.UTF_8);
        check(stdlibCall.contains("the fixture lowers to a validated unit through the "
                + "call machine"),
            "the stdlib value-read pin asserts the realized lowering (unit produced)");
        check(stdlibCall.contains("exactly one EXPORT_READ is produced for the read "
                + "occurrence"),
            "the stdlib value-read pin asserts the produced EXPORT_READ");
        check(stdlibCall.contains("lowers CALL(INDIRECT) with the Static "),
            "the stdlib value-read pin asserts the realized invocation shape");
        check(stdlibCall.contains("exactly one HostFunction(std.console, log, row "
                + "descriptor)"),
            "the stdlib value-read pin asserts the exactly-one registration");
        check(!stdlibCall.contains("the stdlib value read fails closed")
                && !stdlibCall.contains("the value read fails lowering"),
            "no lowerer-side value-read guard assertion remains in the pin");

        // The same-slice emitter-side guard stays asserted where the
        // emission is driven (the project-session ownership guard), and the
        // read arm's own invocation pin asserts the realized call-machine
        // shape rather than a lowerer-side invocation guard.
        String compiledRead = Files.readString(
            root.resolve("test/CompiledExportReadRealizationTest.java"),
            StandardCharsets.UTF_8);
        check(compiledRead.contains("SHARED_EMITTER_COVERAGE")
                && compiledRead.contains("stages nothing"),
            "the same-slice emitter-side SHARED_EMITTER_COVERAGE guard stays asserted "
                + "where emission is driven");
        String importArm = Files.readString(
            root.resolve("test/ImportMemberReadArmTest.java"), StandardCharsets.UTF_8);
        check(importArm.contains("The typed-binding invocation of the read value lowers "
                + "through the"),
            "the read-arm pin asserts the realized typed-binding invocation, never a "
                + "lowerer-side invocation guard");
        for (String leaf : List.of("ImportMemberReadArmTest",
                "CompiledExportReadRealizationTest", "StdlibExportReadRealizationTest",
                "HostExportReadRealizationTest")) {
            check(!Files.readString(root.resolve("test/" + leaf + ".java"),
                    StandardCharsets.UTF_8).contains("invocation guard"),
                "no lowerer-side invocation guard is asserted in " + leaf);
        }
    }

    /** The repository root of the running test process (the gate manifest's home). */
    private static Path repoRoot() {
        Path dir = Path.of("").toAbsolutePath();
        while (dir != null) {
            if (Files.isRegularFile(dir.resolve("tools/gate-manifest.sh"))
                    && Files.isDirectory(dir.resolve("deal"))) {
                return dir;
            }
            dir = dir.getParent();
        }
        return null;
    }

    // =========================================================================
    // Process and filesystem helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n") + " stderr="
                + stderr.replace("\n", "\\n");
        }
    }

    private static ProcessOutcome runProcess(List<String> command, Path workspace)
            throws Exception {
        return runProcessWithEnv(command, workspace, Map.of());
    }

    private static ProcessOutcome runProcessWithEnv(List<String> command, Path workspace,
            Map<String, String> environment) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workspace.toFile());
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

    /** The build-output classpath of this test process. */
    private static String absoluteClasspath() {
        String classpath = System.getProperty("java.class.path", "build");
        List<String> entries = new ArrayList<>();
        for (String entry : classpath.split(File.pathSeparator)) {
            entries.add(Path.of(entry).toAbsolutePath().normalize().toString());
        }
        return String.join(File.pathSeparator, entries);
    }

    private static String luaString(String text) {
        return "\"" + text.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    /** A recursive byte snapshot of one tree (the staging assertions). */
    private static Map<String, String> snapshotTree(Path root) throws Exception {
        Map<String, String> snapshot = new TreeMap<>();
        if (!Files.exists(root)) {
            return snapshot;
        }
        try (var paths = Files.walk(root)) {
            for (Path path : paths.sorted().toList()) {
                if (Files.isRegularFile(path)) {
                    snapshot.put(root.relativize(path).toString(),
                        Arrays.toString(Files.readAllBytes(path)));
                }
            }
        }
        return snapshot;
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path root) {
        if (root == null || !Files.exists(root)) {
            return;
        }
        try (var paths = Files.walk(root)) {
            paths.sorted(java.util.Comparator.reverseOrder()).forEach(path -> {
                try {
                    Files.deleteIfExists(path);
                } catch (java.io.IOException ignored) {
                    // best effort
                }
            });
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    // =========================================================================
    // Driver
    // =========================================================================

    public static void main(String[] args) throws Exception {
        testConsolidatedProbeMatrix();
        testBindingDisciplineAcrossKinds();
        testNegativeSeedsThroughProductionArm();
        testEmissionAgreementAndDeterminism();
        testPerUnitMultiChunkResolution();
        testPinsAndRegistration();
        System.out.println();
        System.out.println("ReadValueIntegrationVerificationTest: " + passed
            + " passed, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
