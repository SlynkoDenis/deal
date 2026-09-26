package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.distribution.DistributionHome;
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
import deal.semantic.RequirementManifestResult;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0647: the spec-stdlib import-read realization across the three
 * consumers (design source
 * {@code module-export-reads-and-in-project-class-construction} M4, the
 * cataloged stdlib callable contract, and M3's STDLIB branch;
 * {@code semantic-ir-construct-coverage-cutover} K2 and K7;
 * {@code luajit-jvm-single-lowering-production-cutover} C2).
 *
 * <ol>
 *   <li><b>The emitted read.</b> A probe project whose entry reads a
 *       {@code std.console} export (value and callee positions) and a
 *       {@code std.string} algorithmic row into function-typed bindings
 *       lowers through the one project entry and validates. Both project
 *       sessions emit the same read operation parameterized only by the
 *       mode flag: the LuaJIT read is the one memoized catalog callable
 *       accessor ({@code __stdlibEntry}) and the JVM read is the memoized
 *       {@code JvmRuntime.stdlibCallable} carrier; the STDLIB placeholder
 *       text never appears. One surface entry per catalog row of each
 *       imported STDLIB module exists, in catalog order, with the row's
 *       canonical spec text.</li>
 *   <li><b>The row invoker.</b> The direct {@code STDLIB_CALL} arm and the
 *       cataloged callable share one realization: the direct arm runs
 *       {@code __stdlibInvoke}/{@code JvmRuntime.stdlibInvoke} (the console
 *       rows' single-effect write factored out of the statement-level
 *       inline emission), and no second algorithm authority exists.</li>
 *   <li><b>The oracle read realization (M3's STDLIB branch).</b> The read
 *       publishes the closed catalog row's memoized callable
 *       ({@code Value.StdlibCallableValue}), carrying the row's declared
 *       signature — the function-typed binding boundary admits it and the
 *       run succeeds. Two reads of one cataloged export publish the
 *       identical value; the read arm's registration keys it once at its
 *       creation and a read never re-keys the value-keyed map (a doctored
 *       differing registration fails the run closed). An out-of-catalog
 *       member and a descriptor mismatch are fail-closed producer
 *       defects.</li>
 *   <li><b>The direct arm's observable.</b> Exactly one console effect
 *       write on the row's channel with the direct arm's text projection,
 *       the null result, and the call-expression origin — in all three
 *       consumers.</li>
 *   <li><b>The three-consumer matrix.</b> The probe runs through the
 *       semantic oracle and both shared artifacts under the real
 *       toolchains; every read's SUCCESS atom agrees event-for-event.</li>
 *   <li><b>The production artifacts.</b> The production arm stages one
 *       project artifact per target; the LuaJIT chunk runs under
 *       {@code luajit} and the JVM class compiles with
 *       {@code javac --release 25 -proc:none} and runs under
 *       {@code java}. The emitted read resolves the surface entry, the
 *       two reads yield the identical carrier object (the surface entry
 *       itself), the carried signature is the row's declared signature,
 *       and the direct console call writes exactly one effect.</li>
 *   <li><b>The per-unit sessions.</b> A per-unit session emits the same
 *       surface-resolving read in trace and production mode.</li>
 *   <li><b>The compared read values.</b> A checker-valid
 *       function-identity comparison of stdlib read values
 *       ({@code console.log === console.log} and
 *       {@code console.log === console.error}) lowers and validates, and
 *       runs through the oracle and both production artifacts: the
 *       cataloged callable is integrated into the oracle's closed
 *       comparison operand view as the memoized allocation's identity
 *       (two reads of one row compare equal, two distinct rows compare
 *       unequal), the artifacts compare the identical memoized object,
 *       and the effects the comparisons gate are the same in all three
 *       consumers.</li>
 * </ol>
 */
public class StdlibExportReadRealizationTest {

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
    // The fixture: a one-module project reading two stdlib modules
    // =========================================================================

    private static final ModuleId APP = new ModuleId("app");
    private static final ModuleId CONSOLE_MODULE = new ModuleId("std.console");
    private static final ModuleId STRING_MODULE = new ModuleId("std.string");
    private static final String CONSOLE_ROW = "log";
    private static final String ALGORITHM_ROW = "length";
    private static final String CONSOLE_SIG = "function(string;null)";
    private static final String CONSOLE_SPEC = "(string)->null";
    private static final String ALGORITHM_SIG = "function(string;int)";
    private static final String ALGORITHM_SPEC = "(string)->int";
    private static final String CONSOLE_TEXT = "hello";
    /** The source line of the direct {@code console.log("hello")} call. */
    private static final int CONSOLE_CALL_LINE = 7;

    private static final String APP_SOURCE = """
        import * as console from "std/console"
        import * as str from "std/string"

        export function main(): null {
          let f: (x: string) => null = console.log
          let g: (s: string) => int = str.length
          console.log("hello")
          return null
        }
        """;

    // The combined composition (T2 + T3 + this leaf): a compiled read and a
    // stdlib read in one project.

    private static final ModuleId COMPANION = new ModuleId("lib");
    private static final String COMPANION_SOURCE = """
        export function tag(v: int): string {
          return "t";
        }
        """;
    private static final String COMPANION_SPEC = "(int)->string";
    private static final String COMBINED_SOURCE = """
        import * as lib from "./lib"
        import * as console from "std/console"
        import * as str from "std/string"

        export function main(): null {
          let f: (v: int) => string = lib.tag
          let g: (x: string) => null = console.log
          let h: (s: string) => int = str.length
          console.log("hello")
          return null
        }
        """;

    // The compared read values (the review-cycle correction): a
    // function-identity comparison over the cataloged callables.

    private static final String COMPARISON_SOURCE = """
        import * as console from "std/console"

        export function main(): null {
          let same: boolean = console.log === console.log
          let different: boolean = console.log === console.error
          if (same) {
            console.log("same")
          }
          if (different) {
            console.log("different")
          }
          return null
        }
        """;
    /** The source line of {@code console.log === console.log}. */
    private static final int SAME_COMPARISON_LINE = 4;
    /** The source line of {@code console.log === console.error}. */
    private static final int DIFFERENT_COMPARISON_LINE = 5;
    private static final String SAME_EFFECT = "same";
    private static final String DIFFERENT_EFFECT = "different";

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

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources) throws Exception {
        Path root = Files.createTempDirectory("stdlib-read-probe");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), new LinkedHashMap<>(),
            new LinkedHashMap<>(),
            DistributionHome.forManifestDirectory(src.toString()));
    }

    private static Fixture stdlibFixture() throws Exception {
        return compileProject(new LinkedHashMap<>(Map.of("src/app.deal", APP_SOURCE)));
    }

    private static Fixture combinedFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", COMPANION_SOURCE);
        sources.put("src/app.deal", COMBINED_SOURCE);
        return compileProject(sources);
    }

    private static Fixture comparisonFixture() throws Exception {
        return compileProject(
            new LinkedHashMap<>(Map.of("src/app.deal", COMPARISON_SOURCE)));
    }

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

    // =========================================================================
    // Op helpers
    // =========================================================================

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

    private static KindPayload.ExportReadPayload readPayload(SemanticOp read) {
        return (KindPayload.ExportReadPayload) read.payload();
    }

    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit, ValueId value) {
        return unit.functionBindings().get(new FunctionAllocationIdentity(value.id()));
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

    /** The catalog rows of one stdlib module in catalog order. */
    private static List<StdlibFunctionCatalog.Entry> catalogRowsOf(String modulePath) {
        List<StdlibFunctionCatalog.Entry> rows = new ArrayList<>();
        for (StdlibFunctionCatalog.Entry row : StdlibFunctionCatalog.entries()) {
            if (row.modulePath().equals(modulePath)) {
                rows.add(row);
            }
        }
        return rows;
    }

    // =========================================================================
    // 1. The emitted read and the catalog surface population
    // =========================================================================

    static void testEmittedReadOperation() throws Exception {
        System.out.println("-- the emitted stdlib read: both project sessions carry the "
            + "memoized catalog callable --");
        Fixture fixture = stdlibFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(!result.hasErrors() && result.project() != null,
                "the probe project lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(Optional.empty(), SemanticIrValidator.validate(project, facts(fixture)),
                "the lowered project passes the closed project gate");
            LoweredModuleUnit appUnit = project.modules().get(APP);
            check(appUnit != null, "the closure carries the entry module");
            if (appUnit == null) {
                return;
            }
            Map<ModuleId, StructuredBodyTable> tables = result.tables();
            Map<ModuleId, deal.semantic.ir.ClassFactoryRegistry> registries =
                result.registries();

            // The three reads: two of the console row (value + callee
            // positions) and one of the algorithmic row.
            List<SemanticOp> reads = readsOf(appUnit);
            checkEq(3, reads.size(),
                "the entry unit carries exactly one EXPORT_READ per source occurrence");
            int consoleReads = 0;
            int algorithmReads = 0;
            for (SemanticOp read : reads) {
                KindPayload.ExportReadPayload payload = readPayload(read);
                if (payload.module().equals(CONSOLE_MODULE)) {
                    consoleReads++;
                    checkEq(CONSOLE_ROW, payload.name(),
                        "the console read names the cataloged row");
                    checkEq(CONSOLE_SPEC, payload.descriptor().canonicalSpecText(),
                        "the console read carries the row's declared descriptor");
                    check(bindingOf(appUnit, payload.value())
                            instanceof FunctionExecutionBinding.HostFunction host
                            && host.hostModuleId().equals(CONSOLE_MODULE)
                            && host.exportName().equals(CONSOLE_ROW)
                            && host.descriptor().equals(payload.descriptor()),
                        "exactly one HostFunction(std.console, log, row descriptor) "
                            + "registration keyed by the read's result identity; got "
                            + bindingOf(appUnit, payload.value()));
                } else {
                    check(payload.module().equals(STRING_MODULE)
                            && payload.name().equals(ALGORITHM_ROW),
                        "the algorithmic read names std.string/length; got "
                            + payload.module() + "/" + payload.name());
                    algorithmReads++;
                    checkEq(ALGORITHM_SPEC, payload.descriptor().canonicalSpecText(),
                        "the algorithmic read carries the row's declared descriptor");
                    check(bindingOf(appUnit, payload.value())
                            instanceof FunctionExecutionBinding.HostFunction host
                            && host.hostModuleId().equals(STRING_MODULE)
                            && host.exportName().equals(ALGORITHM_ROW),
                        "the algorithmic read registers HostFunction(std.string, length) "
                            + "through the host-export seam; got "
                            + bindingOf(appUnit, payload.value()));
                }
            }
            checkEq(2, consoleReads, "two console reads (value and callee positions)");
            checkEq(1, algorithmReads, "one algorithmic read");
            checkEq(1, opsOfKind(appUnit, SemanticOpKind.STDLIB_CALL).size(),
                "the cataloged call-callee arm keeps its landed STDLIB_CALL");

            // The LuaJIT emission: the memoized accessor read, the catalog
            // surface population in catalog order, and the shared row
            // invoker of the direct arm.
            String traceLua = LuaSemanticEmitter.emitProject(project, tables, registries);
            String productionLua = LuaSemanticEmitter.emitProductionProject(project,
                tables, registries, fixture.surface());
            String consoleEntryCall = "__stdlibEntry(\"std.console\", \"log\", "
                + "\"CONSOLE_LOG\", \"" + CONSOLE_SIG + "\", \"" + CONSOLE_SPEC + "\")";
            String algorithmEntryCall = "__stdlibEntry(\"std.string\", \"length\", "
                + "\"STRING_LENGTH\", \"" + ALGORITHM_SIG + "\", \"" + ALGORITHM_SPEC + "\")";
            check(traceLua.contains("local function __stdlibEntry(module, name, sid, sig, "
                    + "csig)"),
                "the prelude carries the one memoized catalog callable accessor");
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                String expected = "S.v" + id + " = " + consoleEntryCall;
                if (readPayload(read).module().equals(STRING_MODULE)) {
                    expected = "S.v" + id + " = " + algorithmEntryCall;
                }
                checkEq(1, countOccurrences(traceLua, expected),
                    "the trace-mode stdlib read publishes the memoized catalog callable: "
                        + expected);
                checkEq(1, countOccurrences(productionLua, expected),
                    "the production read operation is the identical catalog accessor: "
                        + expected);
                check(!traceLua.contains("S.v" + id + " = __intrinsicFn("),
                    "the stdlib read is never the landed residual carrier arm");
            }
            checkEq(traceLua, LuaSemanticEmitter.emitProject(project, tables, registries),
                "the repeated trace-mode project emission is byte-identical");

            // The whole-surface population: one entry per catalog row of each
            // imported STDLIB module, in catalog order.
            List<StdlibFunctionCatalog.Entry> importedRows = new ArrayList<>();
            importedRows.addAll(catalogRowsOf(CONSOLE_MODULE.path()));
            importedRows.addAll(catalogRowsOf(STRING_MODULE.path()));
            check(importedRows.size() > 2,
                "the fixture imports the console and string groups");
            int populationOrder = -1;
            for (StdlibFunctionCatalog.Entry row : importedRows) {
                String line = "__exportSurfaces[\"" + row.modulePath() + "\"][\""
                    + row.exportName() + "\"] = __stdlibEntry(\"" + row.modulePath()
                    + "\", \"" + row.exportName() + "\", \""
                    + row.function().name() + "\", \""
                    + descriptorText(row.declaredDescriptor()) + "\", \""
                    + row.declaredDescriptor().canonicalSpecText() + "\")";
                checkEq(1, countOccurrences(traceLua, line),
                    "the trace-mode surface carries one memoized entry per catalog row: "
                        + line);
                checkEq(1, countOccurrences(productionLua, line),
                    "the production surface carries the same entry: " + line);
                int at = traceLua.indexOf(line);
                check(at > populationOrder,
                    "the surface entries are populated in catalog order: " + line);
                populationOrder = at;
            }

            // The row invoker: the direct STDLIB_CALL arm runs the same
            // realization the cataloged callable's __fn does.
            SemanticOp stdlibCall = opsOfKind(appUnit, SemanticOpKind.STDLIB_CALL).get(0);
            String directCall = "S.v" + ((ValueId) stdlibCall.result()).id()
                + " = __stdlibInvoke(\"CONSOLE_LOG\"";
            checkEq(1, countOccurrences(traceLua, directCall),
                "the direct console arm runs the shared row invoker: " + directCall);
            check(traceLua.contains("local function __stdlibInvoke(fn, opKey, digest, "
                    + "parent, origin, ...)"),
                "the prelude carries the one row invoker");
            check(traceLua.contains("return __stdlib(fn, opKey, digest, parent, origin, "
                    + "...)"),
                "the row invoker delegates every algorithmic row to the one algorithm "
                    + "authority");
            check(traceLua.contains("__consoleEffect(\"STDOUT\", __consoleText(...))"),
                "the console rows' single-effect write is factored into the row invoker");

            // The JVM emission: the memoized program-scoped carrier accessor,
            // the surface population, and the shared row invoker.
            JvmSemanticEmitter.EmissionResult traceJvm = JvmSemanticEmitter.emitProject(
                project, tables, registries);
            JvmSemanticEmitter.EmissionResult productionJvm =
                JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                    JvmBackend.classNameFor(APP.path()), fixture.surface());
            String consoleCarrierCall = "JvmRuntime.stdlibCallable(\"std.console\", "
                + "\"log\", \"CONSOLE_LOG\", \"" + CONSOLE_SIG + "\", \"" + CONSOLE_SPEC
                + "\")";
            String algorithmCarrierCall = "JvmRuntime.stdlibCallable(\"std.string\", "
                + "\"length\", \"STRING_LENGTH\", \"" + ALGORITHM_SIG + "\", \""
                + ALGORITHM_SPEC + "\")";
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                String expected = "v" + id + " = " + consoleCarrierCall + ";";
                if (readPayload(read).module().equals(STRING_MODULE)) {
                    expected = "v" + id + " = " + algorithmCarrierCall + ";";
                }
                checkEq(1, countOccurrences(traceJvm.source(), expected),
                    "the trace-mode JVM stdlib read publishes the memoized carrier: "
                        + expected);
                checkEq(1, countOccurrences(productionJvm.source(), expected),
                    "the production JVM read operation is the identical carrier accessor: "
                        + expected);
                check(!traceJvm.source().contains("v" + id
                        + " = JvmRuntime.intrinsic("),
                    "the stdlib read is never the landed JVM residual carrier arm");
            }
            for (StdlibFunctionCatalog.Entry row : importedRows) {
                String expected = "exportSurface(\"" + row.modulePath() + "\").write(\""
                    + row.exportName() + "\", " + "JvmRuntime.stdlibCallable(\""
                    + row.modulePath() + "\", \"" + row.exportName() + "\", \""
                    + row.function().name() + "\", \""
                    + descriptorText(row.declaredDescriptor()) + "\", \""
                    + row.declaredDescriptor().canonicalSpecText() + "\"));";
                checkEq(1, countOccurrences(traceJvm.source(), expected),
                    "the JVM surface carries one memoized entry per catalog row: "
                        + expected);
                checkEq(1, countOccurrences(productionJvm.source(), expected),
                    "the production JVM surface carries the same entry: " + expected);
            }
            checkEq(productionJvm.source(), JvmSemanticEmitter.emitProductionProject(
                    project, tables, registries, JvmBackend.classNameFor(APP.path()),
                    fixture.surface()).source(),
                "the repeated production project emission is byte-identical");

            // The per-unit sessions: the same surface-resolving read in both
            // modes (no project input, no placeholder).
            String perUnitTraceLua = LuaSemanticEmitter.emitModule(appUnit,
                tables.get(APP));
            String perUnitProductionLua = LuaSemanticEmitter.emitProductionModule(appUnit,
                tables.get(APP), true);
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                check(perUnitTraceLua.contains("S.v" + id + " = __stdlibEntry("),
                    "the per-unit LuaJIT trace session emits the catalog accessor read");
                check(perUnitProductionLua.contains("S.v" + id + " = __stdlibEntry("),
                    "the per-unit LuaJIT production session emits the same read");
            }
            JvmSemanticEmitter.EmissionResult perUnitTraceJvm =
                JvmSemanticEmitter.emitModule(appUnit, tables.get(APP));
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                check(perUnitTraceJvm.source().contains("v" + id
                        + " = JvmRuntime.stdlibCallable("),
                    "the per-unit JVM session emits the catalog carrier read");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
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

    // =========================================================================
    // 2. The oracle read realization, the memoization, and the keying invariant
    // =========================================================================

    static void testOracleReadRealization() throws Exception {
        System.out.println("-- the oracle: the memoized catalog callable, the carried "
            + "signature, and the value-keyed invariant --");
        Fixture fixture = stdlibFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            List<SemanticOp> reads = readsOf(appUnit);
            SemanticOp stdlibCall = opsOfKind(appUnit, SemanticOpKind.STDLIB_CALL).get(0);

            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the full project drive succeeds: " + run.terminal());

            // The direct arm's observable: exactly one console effect write on
            // the row's channel with the direct arm's text projection, and the
            // null result.
            checkEq(List.of(CONSOLE_TEXT), run.effects().stream()
                    .map(SemanticRuntimeModel.EffectEvent::text).toList(),
                "exactly one console effect with the direct arm's text projection");
            checkEq(1, run.effects().size(), "exactly one effect write per console call");
            String callAtom = null;
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                if (event.op().equals(stdlibCall.opId())
                        && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                    callAtom = event.output();
                }
            }
            checkEq("null", callAtom, "the console row's result is the null value");
            check(stdlibCall.origin().span() != null
                    && stdlibCall.origin().sourceId().endsWith("app.deal")
                    && stdlibCall.origin().span().startLine() == CONSOLE_CALL_LINE,
                "the direct call op carries the call-expression origin (line "
                    + CONSOLE_CALL_LINE + "); got " + stdlibCall.origin());

            // The read value crosses the function-typed VARIABLE_ASSIGNMENT
            // boundaries of the two `let` types: the boundary carries the row's
            // declared descriptor, so a callable whose carried signature was
            // the reading site's (or the retired ()->number placeholder's)
            // would fail E8010 here. The successful run above is therefore the
            // carried-signature evidence of the oracle realization.
            List<RuntimeDescriptor.Func> functionBoundaries = new ArrayList<>();
            for (SemanticOp op : appUnit.ops()) {
                if (op.kind() != SemanticOpKind.BOUNDARY) {
                    continue;
                }
                KindPayload.BoundaryPayload boundary = (KindPayload.BoundaryPayload) op.payload();
                if ((boundary.kind() == deal.semantic.ir.BoundaryKind.VARIABLE_DECLARATION
                        || boundary.kind()
                            == deal.semantic.ir.BoundaryKind.VARIABLE_ASSIGNMENT)
                        && boundary.descriptor() instanceof RuntimeDescriptor.Func func) {
                    functionBoundaries.add(func);
                }
            }
            check(functionBoundaries.contains(rowDescriptorOf(CONSOLE_MODULE.path(),
                    CONSOLE_ROW)),
                "the console read crosses a function-typed binding boundary carrying the "
                    + "row's declared signature: " + functionBoundaries);
            check(functionBoundaries.contains(rowDescriptorOf(STRING_MODULE.path(),
                    ALGORITHM_ROW)),
                "the algorithmic read crosses a function-typed binding boundary carrying "
                    + "the row's declared signature: " + functionBoundaries);

            // The memoization: the two console reads publish one identical
            // value, distinct from the algorithmic row's callable.
            String consoleAtom = null;
            String algorithmAtom = null;
            int consoleReadAtoms = 0;
            for (SemanticOp read : reads) {
                for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                    if (!event.op().equals(read.opId())
                            || event.phase() != SemanticRuntimeModel.Phase.SUCCESS) {
                        continue;
                    }
                    if (readPayload(read).module().equals(CONSOLE_MODULE)) {
                        consoleReadAtoms++;
                        if (consoleAtom == null) {
                            consoleAtom = event.output();
                        } else {
                            checkEq(consoleAtom, event.output(),
                                "two reads of one cataloged export publish the identical "
                                    + "callable value");
                        }
                    } else {
                        algorithmAtom = event.output();
                    }
                }
            }
            checkEq(2, consoleReadAtoms, "both console reads execute");
            check(consoleAtom != null && consoleAtom.startsWith("ref:"),
                "the read's trace SUCCESS atom is the callable's allocation: "
                    + consoleAtom);
            check(algorithmAtom != null && algorithmAtom.startsWith("ref:")
                    && !algorithmAtom.equals(consoleAtom),
                "the algorithmic row's callable is a distinct value: " + algorithmAtom);
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                check(event.output() == null || !event.output().startsWith("export:"),
                    "no export:<module>.<name> placeholder atom remains in the oracle "
                        + "trace: " + event.output());
            }

            // The read arm's own registration keys the created callable once;
            // a doctored second read whose registration differs from the
            // first's fails the run closed (a read never re-keys the
            // value-keyed map).
            ValueId firstConsole = null;
            ValueId secondConsole = null;
            for (SemanticOp read : reads) {
                if (!readPayload(read).module().equals(CONSOLE_MODULE)) {
                    continue;
                }
                if (firstConsole == null) {
                    firstConsole = readPayload(read).value();
                } else if (secondConsole == null) {
                    secondConsole = readPayload(read).value();
                }
            }
            check(firstConsole != null && secondConsole != null,
                "the fixture carries two console read identities");
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> doctored =
                new LinkedHashMap<>(appUnit.functionBindings());
            doctored.put(new FunctionAllocationIdentity(secondConsole.id()),
                new FunctionExecutionBinding.HostFunction(CONSOLE_MODULE, "error",
                    (RuntimeDescriptor.Func) rowDescriptorOf(CONSOLE_MODULE.path(),
                        "error")));
            LoweredModuleUnit mutated = new LoweredModuleUnit(appUnit.formatVersion(),
                appUnit.semanticProfile(), appUnit.moduleId(), appUnit.interfaceHash(),
                appUnit.loweringContextHash(), appUnit.requiredCapabilities(),
                appUnit.constructCoverage(), appUnit.classLayouts(), appUnit.functions(),
                appUnit.moduleInit(), appUnit.exportPlan(), doctored, appUnit.ops());
            RuntimeException rekeyed = null;
            try {
                SemanticOracle.executeProjectInits(
                    new ExecutableLoweredProject(project.semanticProfile(),
                        project.interfaceIndex(), Map.of(APP, mutated), APP),
                    result.tables(), Map.of(APP, result.registries().get(APP)), null);
            } catch (RuntimeException expected) {
                rekeyed = expected;
            }
            check(rekeyed instanceof IllegalStateException
                    && rekeyed.getMessage().contains("re-keys"),
                "a doctored second read whose registration differs fails the run closed "
                    + "with the value-keyed invariant; got "
                    + (rekeyed == null ? "no failure" : rekeyed.getMessage()));

            // A doctored read descriptor that differs from the catalog row's
            // declared descriptor is a fail-closed producer defect.
            RuntimeDescriptor.Func driftedDescriptor = rowDescriptorOf(
                STRING_MODULE.path(), ALGORITHM_ROW);
            List<SemanticOp> driftedOps = new ArrayList<>();
            for (SemanticOp op : appUnit.ops()) {
                if (op == reads.get(0)) {
                    KindPayload.ExportReadPayload payload = readPayload(op);
                    KindPayload.ExportReadPayload driftedPayload =
                        new KindPayload.ExportReadPayload(payload.module(), payload.name(),
                            driftedDescriptor, payload.value());
                    deal.semantic.ir.OperationContractSnapshot driftedContract =
                        new deal.semantic.ir.OperationContractSnapshot(
                            op.contract().version(), op.kind(), driftedDescriptor,
                            op.operandTypes(), op.contract().selector(), driftedPayload,
                            op.failurePolicy(), op.contract().referencedSemanticIds(),
                            op.contract().canonicalDigest());
                    driftedOps.add(new SemanticOp(op.opId(), op.kind(), op.origin(),
                        op.result(), driftedDescriptor, op.operands(), op.operandTypes(),
                        driftedPayload, op.failurePolicy(), driftedContract));
                } else {
                    driftedOps.add(op);
                }
            }
            LoweredModuleUnit drifted = new LoweredModuleUnit(appUnit.formatVersion(),
                appUnit.semanticProfile(), appUnit.moduleId(), appUnit.interfaceHash(),
                appUnit.loweringContextHash(), appUnit.requiredCapabilities(),
                appUnit.constructCoverage(), appUnit.classLayouts(), appUnit.functions(),
                appUnit.moduleInit(), appUnit.exportPlan(), appUnit.functionBindings(),
                driftedOps);
            RuntimeException descriptorDrift = null;
            try {
                SemanticOracle.executeProjectInits(
                    new ExecutableLoweredProject(project.semanticProfile(),
                        project.interfaceIndex(), Map.of(APP, drifted), APP),
                    result.tables(), Map.of(APP, result.registries().get(APP)), null);
            } catch (RuntimeException expected) {
                descriptorDrift = expected;
            }
            check(descriptorDrift instanceof IllegalStateException
                    && descriptorDrift.getMessage().contains("declares"),
                "a doctored read descriptor that differs from the catalog row is a "
                    + "fail-closed producer defect; got "
                    + (descriptorDrift == null ? "no failure"
                        : descriptorDrift.getMessage()));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static RuntimeDescriptor.Func rowDescriptorOf(String modulePath, String export) {
        return StdlibFunctionCatalog.lookup(modulePath, export).orElseThrow()
            .declaredDescriptor();
    }

    // =========================================================================
    // 2b. The combined composition: a compiled read and a stdlib read in one
    // =========================================================================

    static void testCombinedComposition() throws Exception {
        System.out.println("-- the combined composition: a compiled read and a stdlib "
            + "read in one project through the oracle and both production artifacts --");
        Fixture fixture = combinedFixture();
        Path workspace = Files.createTempDirectory("stdlib-read-combined");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the combined project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(Optional.empty(), SemanticIrValidator.validate(project, facts(fixture)),
                "the combined lowered project passes the closed project gate");
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(COMPANION);
            check(libUnit != null, "the closure carries the compiled companion");
            if (libUnit == null) {
                return;
            }
            List<SemanticOp> reads = readsOf(appUnit);
            checkEq(4, reads.size(),
                "the entry unit carries one read per source occurrence (the compiled "
                    + "companion, the two stdlib value reads, and the stdlib callee "
                    + "read)");
            SemanticOp compiledRead = readAt(reads, COMPANION, "tag", 6);
            SemanticOp consoleValueRead = readAt(reads, CONSOLE_MODULE, CONSOLE_ROW, 7);
            SemanticOp algorithmRead = readAt(reads, STRING_MODULE, ALGORITHM_ROW, 8);
            SemanticOp consoleCalleeRead = readAt(reads, CONSOLE_MODULE, CONSOLE_ROW, 9);
            check(compiledRead != null && consoleValueRead != null && algorithmRead != null
                    && consoleCalleeRead != null,
                "the combined fixture carries the four expected reads");
            if (compiledRead == null || consoleValueRead == null || algorithmRead == null
                    || consoleCalleeRead == null) {
                return;
            }
            checkEq(COMPANION_SPEC, readPayload(compiledRead).descriptor()
                    .canonicalSpecText(),
                "the compiled read carries the companion's declared descriptor");
            check(bindingOf(appUnit, readPayload(compiledRead).value())
                    instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.moduleId().equals(COMPANION)
                    && external.executionOwner()
                        == deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY,
                "the compiled read registers ExternalFunction(lib, tag, SHARED_BODY); got "
                    + bindingOf(appUnit, readPayload(compiledRead).value()));
            for (SemanticOp read : List.of(consoleValueRead, consoleCalleeRead,
                    algorithmRead)) {
                check(bindingOf(appUnit, readPayload(read).value())
                        instanceof FunctionExecutionBinding.HostFunction,
                    "every stdlib read registers exactly one HostFunction: " + read.opId());
            }

            // The oracle: the compiled read resolves the owner's published
            // value, the stdlib reads resolve the memoized catalog callables.
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the combined project drive succeeds: " + run.terminal());
            checkEq(List.of(CONSOLE_TEXT), run.effects().stream()
                    .map(SemanticRuntimeModel.EffectEvent::text).toList(),
                "exactly one console effect with the direct arm's text projection");
            SemanticOp publish = opsOfKind(libUnit, SemanticOpKind.EXPORT_PUBLISH).get(0);
            SemanticOp exportBoundary = null;
            for (SemanticOp candidate : libUnit.ops()) {
                if (candidate.kind() == SemanticOpKind.BOUNDARY
                        && publish.opId().equals(candidate.origin().parentOpId())
                        && ((KindPayload.BoundaryPayload) candidate.payload()).kind()
                            == deal.semantic.ir.BoundaryKind.MODULE_EXPORT) {
                    exportBoundary = candidate;
                }
            }
            check(exportBoundary != null,
                "the companion's publication carries its MODULE_EXPORT child");
            String publicationAtom = null;
            if (exportBoundary != null) {
                for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                    if (event.op().equals(exportBoundary.opId())
                            && event.phase() == SemanticRuntimeModel.Phase.START
                            && !event.inputs().isEmpty()) {
                        publicationAtom = event.inputs().get(0);
                    }
                }
            }
            check(publicationAtom != null && publicationAtom.startsWith("ref:"),
                "the companion's publication atom is the published value's creation "
                    + "allocation; got " + publicationAtom);
            checkEq(publicationAtom, successAtomOf(run, compiledRead.opId()),
                "the compiled read publishes the owner's published value (no fresh "
                    + "allocation)");
            checkEq(successAtomOf(run, consoleValueRead.opId()),
                successAtomOf(run, consoleCalleeRead.opId()),
                "two stdlib reads of one cataloged export publish the identical callable");
            check(!java.util.Objects.equals(successAtomOf(run, algorithmRead.opId()),
                    successAtomOf(run, consoleValueRead.opId())),
                "the algorithmic row's callable is distinct");

            // The three-consumer matrix and both production artifacts under the
            // real toolchains: every assertion above fails if the compiled read
            // arm, the program-scoped registry, or the catalog carriers break.
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project, result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.success(
                        "combined compiled + stdlib reads", List.of(CONSOLE_TEXT),
                        "null"),
                    workspace.resolve("matrix"));
            check(verdict.pass(), "the combined probe's three consumers agree "
                + "event-for-event:\n" + verdict.report());

            Path luaOut = fixture.root().resolve("combined-lua");
            PublicationStager luaStager = PublicationStager.forRoot(luaOut);
            ProductionProjectEmission.Result luaResult;
            try {
                luaResult = emit(fixture, Backend.LUAJIT, luaStager, false);
                luaStager.publish();
            } finally {
                luaStager.discard();
            }
            check(luaResult.emitted(), "the combined LuaJIT production arm emits: "
                + luaResult.diagnostics());
            if (luaResult.emitted()) {
                Path luaProbe = fixture.root().resolve("combined-lua-probe.lua");
                Files.writeString(luaProbe, combinedLuaProbe(
                    luaOut.resolve(luaResult.artifactRelativePath())),
                    StandardCharsets.UTF_8);
                ProcessOutcome luaRun = runProcess(List.of("luajit",
                    luaProbe.toAbsolutePath().toString()), fixture.root());
                check(luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK")
                        && countOccurrences(luaRun.stdout(), CONSOLE_TEXT) == 1,
                    "the combined LuaJIT chunk resolves both read kinds and writes "
                        + "exactly one console effect; exit=" + luaRun.exitCode()
                        + " stdout=" + luaRun.stdout().replace("\n", "\\n") + " stderr="
                        + luaRun.stderr().replace("\n", "\\n"));
            }

            Path jvmOut = fixture.root().resolve("combined-jvm");
            PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
            ProductionProjectEmission.Result jvmResult;
            try {
                jvmResult = emit(fixture, Backend.JVM, jvmStager, false);
                jvmStager.publish();
            } finally {
                jvmStager.discard();
            }
            check(jvmResult.emitted(), "the combined JVM production arm emits: "
                + jvmResult.diagnostics());
            if (!jvmResult.emitted()) {
                return;
            }
            Path jvmSource = jvmOut.resolve(jvmResult.artifactRelativePath());
            String driver = "CombinedReadsProductionProbe";
            Files.writeString(jvmOut.resolve(driver + ".java"),
                combinedProbeSource(JvmBackend.classNameFor(APP.path()), compiledRead,
                    consoleValueRead),
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
                "the combined JVM artifact compiles with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() == 0) {
                ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, driver), fixture.root());
                check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK")
                        && countOccurrences(javaRun.stdout(), CONSOLE_TEXT) == 1,
                    "the combined JVM artifact's read slots resolve the published "
                        + "carrier and the catalog carrier; exit=" + javaRun.exitCode()
                        + " stdout=" + javaRun.stdout().replace("\n", "\\n") + " stderr="
                        + javaRun.stderr().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /** The read of one module/export at one source line, or null. */
    private static SemanticOp readAt(List<SemanticOp> reads, ModuleId module, String name,
                                     int line) {
        for (SemanticOp read : reads) {
            KindPayload.ExportReadPayload payload = readPayload(read);
            if (payload.module().equals(module) && payload.name().equals(name)
                    && read.origin().span() != null
                    && read.origin().span().startLine() == line) {
                return read;
            }
        }
        return null;
    }

    /** The SUCCESS output atom of one op in a run, or null. */
    private static String successAtomOf(SemanticRuntimeModel.ConsumerRun run, OpId op) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op)
                    && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                return event.output();
            }
        }
        return null;
    }

    /** The combined LuaJIT production probe: both read kinds' resolved entries. */
    private static String combinedLuaProbe(Path artifact) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __surface = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if type(__surface) ~= \"table\" then __fail(\"the production chunk "
            + "returned \"..type(__surface)) end\n");
        lua.append("local __tag = __exportSurfaces[\"lib\"][\"tag\"]\n");
        lua.append("if type(__tag) ~= \"table\" then __fail(\"no compiled "
            + "publication\") end\n");
        lua.append("if __tag.__val == nil then __fail(\"no published __val\") end\n");
        lua.append("if type(__tag.f) ~= \"function\" then __fail(\"no retained-caller "
            + ".f projection\") end\n");
        lua.append("local __log = __exportSurfaces[\"std.console\"][\"log\"]\n");
        lua.append("if type(__log) ~= \"table\" or __log.__sid ~= \"CONSOLE_LOG\" then "
            + "__fail(\"no cataloged console callable\") end\n");
        lua.append("if __stdlibEntries[\"std.console\"..string.char(1)..\"log\"] ~= "
            + "__log then __fail(\"the console surface entry is not the memoized "
            + "callable\") end\n");
        lua.append("local __len = __exportSurfaces[\"std.string\"][\"length\"]\n");
        lua.append("if type(__len) ~= \"table\" or __len.__sig ~= ")
            .append(luaString(ALGORITHM_SIG)).append(" then __fail(\"no cataloged "
            + "algorithmic callable\") end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /** The combined JVM production probe: both read slots' resolved objects. */
    private static String combinedProbeSource(String className, SemanticOp compiledRead,
                                              SemanticOp consoleValueRead) {
        long compiledId = ((ValueId) compiledRead.result()).id();
        long consoleId = ((ValueId) consoleValueRead.result()).id();
        StringBuilder source = new StringBuilder();
        source.append("public class CombinedReadsProductionProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(className).append(".main(new String[0]);\n");
        source.append("    Object compiled = ").append(className).append(".v")
            .append(compiledId).append(";\n");
        source.append("    Object published = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"lib\").entries.get(\"tag\");\n");
        source.append("    check(compiled == published, \"the compiled read resolves the "
            + "owner's published carrier; got \" + compiled + \" vs \" + published);\n");
        source.append("    Object stdlibRead = ").append(className).append(".v")
            .append(consoleId).append(";\n");
        source.append("    Object stdlibEntry = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"std.console\").entries.get(\"log\");\n");
        source.append("    check(stdlibRead == stdlibEntry, \"the stdlib read resolves the "
            + "catalog carrier of the surface; got \" + stdlibRead);\n");
        source.append("    check(stdlibRead instanceof deal.codegen.jvm.JvmRuntime."
            + "StdlibFunctionValue callable && \"CONSOLE_LOG\".equals(callable.rowId) "
            + "&& \"").append(CONSOLE_SIG).append("\".equals(callable.signature), "
            + "\"the catalog carrier carries the row tag and the declared "
            + "signature; got \" + stdlibRead);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 2c. The compared read values: the cataloged callable is a comparison
    //     operand in all three consumers
    // =========================================================================

    /**
     * The review-cycle correction (review MR-0519 cycle 1, finding 1): the
     * new {@code Value.StdlibCallableValue} is integrated into the oracle's
     * closed comparison operand view. A checker-valid function-identity
     * comparison of stdlib read values ({@code console.log === console.log}
     * lowers to {@code REFERENCE_EQ}; {@code ComparisonSelectorLowering})
     * lowers and validates, so the oracle must compare the memoized
     * callables by their allocation identity — exactly as both artifacts
     * compare the identical memoized object. The probe drives that program
     * through the oracle and both production artifacts under the real
     * toolchains: two reads of one row compare equal, two distinct rows
     * compare unequal, and the effects the comparisons gate are the same in
     * all three consumers.
     */
    static void testStdlibCallableComparison() throws Exception {
        System.out.println("-- the compared stdlib read values: the memoized catalog "
            + "callable is a comparison operand in the oracle and both artifacts --");
        Fixture fixture = comparisonFixture();
        Path workspace = Files.createTempDirectory("stdlib-read-comparison");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(!result.hasErrors() && result.project() != null,
                "the comparison project lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(Optional.empty(), SemanticIrValidator.validate(project, facts(fixture)),
                "the comparison project passes the closed project gate");
            LoweredModuleUnit appUnit = project.modules().get(APP);
            check(appUnit != null, "the closure carries the entry module");
            if (appUnit == null) {
                return;
            }
            List<SemanticOp> sameReads = readsAt(readsOf(appUnit), CONSOLE_MODULE,
                CONSOLE_ROW, SAME_COMPARISON_LINE);
            List<SemanticOp> distinctReads = readsAt(readsOf(appUnit), CONSOLE_MODULE,
                "error", DIFFERENT_COMPARISON_LINE);
            checkEq(2, sameReads.size(),
                "`console.log === console.log` carries one catalog read per side");
            checkEq(1, distinctReads.size(),
                "the distinct-row comparison reads console.error");
            if (sameReads.size() != 2 || distinctReads.size() != 1) {
                return;
            }
            List<SemanticOp> comparedReads = new ArrayList<>(sameReads);
            comparedReads.addAll(distinctReads);
            SemanticOp sameComparison = null;
            SemanticOp differentComparison = null;
            int referenceEqualities = 0;
            for (SemanticOp op : opsOfKind(appUnit, SemanticOpKind.BINARY)) {
                KindPayload.BinaryPayload payload = (KindPayload.BinaryPayload) op.payload();
                if (payload.selector() != deal.semantic.ir.BinarySelector.REFERENCE_EQ) {
                    continue;
                }
                referenceEqualities++;
                int line = op.origin().span().startLine();
                if (line == SAME_COMPARISON_LINE) {
                    sameComparison = op;
                } else if (line == DIFFERENT_COMPARISON_LINE) {
                    differentComparison = op;
                }
            }
            checkEq(2, referenceEqualities,
                "both function-identity comparisons lower to REFERENCE_EQ");
            check(sameComparison != null && differentComparison != null,
                "the two comparisons carry their source-line origins");
            if (sameComparison == null || differentComparison == null) {
                return;
            }

            // The oracle: the cataloged callable is a comparison operand and
            // the memoized identity decides the outcome.
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle admits the cataloged callable as a comparison operand: "
                    + run.terminal());
            checkEq(List.of(SAME_EFFECT), run.effects().stream()
                    .map(SemanticRuntimeModel.EffectEvent::text).toList(),
                "exactly one effect: `same` is written and `different` is not — the "
                    + "identical row compares equal and two distinct rows compare "
                    + "unequal in the oracle");
            String sameAtom = successAtomOf(run, sameReads.get(0).opId());
            checkEq(sameAtom, successAtomOf(run, sameReads.get(1).opId()),
                "the two reads of one catalog row publish the identical callable value");
            check(sameAtom != null && sameAtom.startsWith("ref:"),
                "the compared callable is the memoized allocation: " + sameAtom);
            check(!java.util.Objects.equals(sameAtom,
                    successAtomOf(run, distinctReads.get(0).opId())),
                "the second row's callable is a distinct value");
            checkEq("bool:true", successAtomOf(run, sameComparison.opId()),
                "identity over two reads of one row is true in the oracle");
            checkEq("bool:false", successAtomOf(run, differentComparison.opId()),
                "identity over two distinct rows is false in the oracle");

            // Both emitters read the memoized carrier for every compared
            // occurrence: the second read value is never re-materialized.
            String traceLua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            String productionLua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            JvmSemanticEmitter.EmissionResult traceJvm = JvmSemanticEmitter.emitProject(
                project, result.tables(), result.registries());
            JvmSemanticEmitter.EmissionResult productionJvm =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), JvmBackend.classNameFor(APP.path()),
                    fixture.surface());
            for (SemanticOp read : comparedReads) {
                long id = ((ValueId) read.result()).id();
                checkEq(1, countOccurrences(traceLua, "S.v" + id
                        + " = __stdlibEntry(\""),
                    "the trace-mode LuaJIT read is the memoized catalog accessor");
                checkEq(1, countOccurrences(productionLua, "S.v" + id
                        + " = __stdlibEntry(\""),
                    "the production LuaJIT read is the identical accessor");
                check(!traceLua.contains("S.v" + id + " = __intrinsicFn("),
                    "the compared read is never the residual carrier arm");
                checkEq(1, countOccurrences(traceJvm.source(),
                        "v" + id + " = JvmRuntime.stdlibCallable(\""),
                    "the trace-mode JVM read is the memoized catalog carrier");
                checkEq(1, countOccurrences(productionJvm.source(),
                        "v" + id + " = JvmRuntime.stdlibCallable(\""),
                    "the production JVM read is the identical carrier accessor");
            }

            // The three-consumer matrix: the comparison operation, its
            // operands' atoms, the effects, and the terminal agree.
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project, result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.success(
                        "compared stdlib read values", List.of(SAME_EFFECT), "null"),
                    workspace.resolve("matrix"));
            check(verdict.pass(), "the comparison probe's three consumers agree "
                + "event-for-event:\n" + verdict.report());

            // The LuaJIT production artifact: the chunk's own comparisons
            // gate the effects (one `same`, no `different`).
            Path luaOut = fixture.root().resolve("comparison-lua");
            PublicationStager luaStager = PublicationStager.forRoot(luaOut);
            ProductionProjectEmission.Result luaResult;
            try {
                luaResult = emit(fixture, Backend.LUAJIT, luaStager, false);
                luaStager.publish();
            } finally {
                luaStager.discard();
            }
            check(luaResult.emitted(), "the comparison LuaJIT production arm emits: "
                + luaResult.diagnostics());
            if (!luaResult.emitted()) {
                return;
            }
            Path luaArtifact = luaOut.resolve(luaResult.artifactRelativePath());
            String lua = Files.readString(luaArtifact);
            for (SemanticOp read : comparedReads) {
                check(!lua.contains("S.v" + ((ValueId) read.result()).id()
                        + " = __intrinsicFn("),
                    "the LuaJIT artifact carries no residual carrier read");
            }
            Path luaProbe = fixture.root().resolve("comparison-lua-probe.lua");
            Files.writeString(luaProbe, comparisonLuaProbe(luaArtifact),
                StandardCharsets.UTF_8);
            ProcessOutcome luaRun = runProcess(List.of("luajit",
                luaProbe.toAbsolutePath().toString()), fixture.root());
            check(luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK")
                    && countOccurrences(luaRun.stdout(), SAME_EFFECT) == 1
                    && !luaRun.stdout().contains(DIFFERENT_EFFECT),
                "the LuaJIT chunk compares the identical memoized callable (one `same` "
                    + "effect, no `different` effect) and its surface entries are the "
                    + "memoized carriers; exit=" + luaRun.exitCode() + " stdout="
                    + luaRun.stdout().replace("\n", "\\n") + " stderr="
                    + luaRun.stderr().replace("\n", "\\n"));

            // The JVM production artifact: the artifact's own comparison
            // slots hold the identity outcomes.
            Path jvmOut = fixture.root().resolve("comparison-jvm");
            PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
            ProductionProjectEmission.Result jvmResult;
            try {
                jvmResult = emit(fixture, Backend.JVM, jvmStager, false);
                jvmStager.publish();
            } finally {
                jvmStager.discard();
            }
            check(jvmResult.emitted(), "the comparison JVM production arm emits: "
                + jvmResult.diagnostics());
            if (!jvmResult.emitted()) {
                return;
            }
            Path jvmSource = jvmOut.resolve(jvmResult.artifactRelativePath());
            String jvmText = Files.readString(jvmSource);
            for (SemanticOp read : comparedReads) {
                check(!jvmText.contains("v" + ((ValueId) read.result()).id()
                        + " = JvmRuntime.intrinsic("),
                    "the JVM artifact carries no residual carrier read");
            }
            String driver = "StdlibComparisonProductionProbe";
            Files.writeString(jvmOut.resolve(driver + ".java"),
                comparisonProbeSource(JvmBackend.classNameFor(APP.path()),
                    (ValueId) sameComparison.result(),
                    (ValueId) differentComparison.result()),
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
                "the comparison JVM artifact compiles with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() == 0) {
                ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, driver), fixture.root());
                check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK")
                        && countOccurrences(javaRun.stdout(), SAME_EFFECT) == 1
                        && !javaRun.stdout().contains(DIFFERENT_EFFECT),
                    "the JVM artifact's comparison slots hold the memoized identity "
                        + "outcomes (true/false) and its effect write is `same` only; "
                        + "exit=" + javaRun.exitCode() + " stdout="
                        + javaRun.stdout().replace("\n", "\\n") + " stderr="
                        + javaRun.stderr().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /** The reads of one module/export at one source line. */
    private static List<SemanticOp> readsAt(List<SemanticOp> reads, ModuleId module,
                                            String name, int line) {
        List<SemanticOp> matched = new ArrayList<>();
        for (SemanticOp read : reads) {
            KindPayload.ExportReadPayload payload = readPayload(read);
            if (payload.module().equals(module) && payload.name().equals(name)
                    && read.origin().span() != null
                    && read.origin().span().startLine() == line) {
                matched.add(read);
            }
        }
        return matched;
    }

    /** The comparison LuaJIT probe: the surface entries are the memoized carriers. */
    private static String comparisonLuaProbe(Path artifact) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __surface = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if type(__surface) ~= \"table\" then __fail(\"the production chunk "
            + "returned \"..type(__surface)) end\n");
        lua.append("local __log = __exportSurfaces[\"std.console\"][\"log\"]\n");
        lua.append("local __err = __exportSurfaces[\"std.console\"][\"error\"]\n");
        lua.append("if __log == nil or __err == nil then __fail(\"no catalog surface "
            + "entries\") end\n");
        lua.append("if __stdlibEntries[\"std.console\"..string.char(1)..\"log\"] ~= "
            + "__log then __fail(\"the log surface entry is not the memoized "
            + "callable\") end\n");
        lua.append("if __stdlibEntries[\"std.console\"..string.char(1)..\"error\"] ~= "
            + "__err then __fail(\"the error surface entry is not the memoized "
            + "callable\") end\n");
        lua.append("if __log == __err then __fail(\"one callable for two rows\") end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /** The comparison JVM probe: the artifact's own comparison outcomes. */
    private static String comparisonProbeSource(String className, ValueId sameResult,
                                                ValueId differentResult) {
        StringBuilder source = new StringBuilder();
        source.append("public class StdlibComparisonProductionProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(className).append(".main(new String[0]);\n");
        source.append("    check(Boolean.TRUE.equals(").append(className).append(".v")
            .append(sameResult.id()).append("), \"console.log === console.log is true "
            + "in the artifact; got \" + ").append(className).append(".v")
            .append(sameResult.id()).append(");\n");
        source.append("    check(Boolean.FALSE.equals(").append(className).append(".v")
            .append(differentResult.id()).append("), \"console.log === console.error "
            + "is false in the artifact; got \" + ").append(className).append(".v")
            .append(differentResult.id()).append(");\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 3. The three-consumer matrix over the probe project
    // =========================================================================

    static void testThreeConsumerProjectMatrix() throws Exception {
        System.out.println("-- the probe project runs through the oracle and both shared "
            + "artifacts under the real toolchains --");
        Fixture fixture = stdlibFixture();
        Path workspace = Files.createTempDirectory("stdlib-read-matrix");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            List<SemanticOp> reads = readsOf(project.modules().get(APP));
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project, result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.success("stdlib export read",
                        List.of(CONSOLE_TEXT), "null"),
                    workspace);
            check(verdict.pass(), "the three consumers agree event-for-event (the "
                + "catalog callables' identity included):\n" + verdict.report());
            if (!verdict.pass()) {
                return;
            }
            for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                List<String> atoms = new ArrayList<>();
                for (SemanticOp read : reads) {
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.op().equals(read.opId())
                                && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                            atoms.add(event.output());
                        }
                    }
                }
                checkEq(3, atoms.size(), run.consumer() + " executes all three reads");
                check(atoms.size() == 3 && atoms.get(0).equals(atoms.get(2))
                        && atoms.get(0).startsWith("ref:")
                        && !atoms.get(0).equals(atoms.get(1)),
                    run.consumer() + " publishes the identical console callable for both "
                        + "reads (and a distinct algorithmic callable); got " + atoms);
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The production artifacts under the real toolchains
    // =========================================================================

    static void testProductionArtifacts() throws Exception {
        System.out.println("-- the production arm stages one project artifact per target; "
            + "both run under the real toolchains --");
        Fixture fixture = stdlibFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            List<SemanticOp> reads = readsOf(appUnit);
            SemanticOp stdlibCall = opsOfKind(appUnit, SemanticOpKind.STDLIB_CALL).get(0);
            SemanticOp consoleValueRead = null;
            for (SemanticOp read : reads) {
                if (readPayload(read).module().equals(CONSOLE_MODULE)
                        && read.origin().span() != null
                        && read.origin().span().startLine()
                            != stdlibCall.origin().span().startLine()) {
                    consoleValueRead = read;
                }
            }
            check(consoleValueRead != null, "the fixture carries the value-position "
                + "console read");

            Path luaOut = fixture.root().resolve("out-lua");
            writeFileIn(luaOut, "app.lua", "-- previous artifact\n");
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
            check(luaResult.emitted(), "the LuaJIT production arm emits: "
                + luaResult.diagnostics());
            if (!luaResult.emitted()) {
                return;
            }
            Path luaArtifact = luaOut.resolve(luaResult.artifactRelativePath());
            String lua = Files.readString(luaArtifact);
            for (SemanticOp read : reads) {
                check(!lua.contains("S.v" + ((ValueId) read.result()).id()
                        + " = __intrinsicFn("),
                    "the production LuaJIT artifact carries no residual carrier read");
            }
            check(!lua.contains("export:std.console"),
                "the production LuaJIT artifact carries no placeholder token");
            check(lua.contains("__exportSurfaces[\"std.console\"][\"log\"] = "
                    + "__stdlibEntry(\"std.console\", \"log\", \"CONSOLE_LOG\", \""
                    + CONSOLE_SIG + "\", \"" + CONSOLE_SPEC + "\")"),
                "the production artifact populates the console surface entry");

            Path luaProbe = fixture.root().resolve("lua-probe.lua");
            Files.writeString(luaProbe, luaProductionProbe(luaArtifact),
                StandardCharsets.UTF_8);
            ProcessOutcome luaRun = runProcess(List.of("luajit",
                luaProbe.toAbsolutePath().toString()), fixture.root());
            check(luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK"),
                "the production LuaJIT chunk resolves the catalog callable and writes "
                    + "exactly one console effect: exit=" + luaRun.exitCode() + " stdout="
                    + luaRun.stdout().replace("\n", "\\n") + " stderr="
                    + luaRun.stderr().replace("\n", "\\n"));

            Path jvmOut = fixture.root().resolve("out-jvm");
            writeFileIn(jvmOut, "App.java", "// previous artifact\n");
            PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
            ProductionProjectEmission.Result jvmResult;
            try {
                jvmResult = emit(fixture, Backend.JVM, jvmStager, false);
                jvmStager.publish();
            } finally {
                jvmStager.discard();
            }
            check(jvmResult.emitted(), "the JVM production arm emits: "
                + jvmResult.diagnostics());
            if (!jvmResult.emitted()) {
                return;
            }
            Path jvmSource = jvmOut.resolve(jvmResult.artifactRelativePath());
            String jvmText = Files.readString(jvmSource);
            for (SemanticOp read : reads) {
                check(!jvmText.contains("v" + ((ValueId) read.result()).id()
                        + " = JvmRuntime.intrinsic("),
                    "the production JVM artifact carries no residual carrier read");
            }
            check(!jvmText.contains("export:std.console"),
                "the production JVM artifact carries no placeholder token");
            check(jvmText.contains("JvmRuntime.stdlibCallable(\"std.console\", \"log\", "
                    + "\"CONSOLE_LOG\", \"" + CONSOLE_SIG + "\", \"" + CONSOLE_SPEC
                    + "\");"),
                "the production JVM artifact carries the catalog carrier accessor");

            String driver = "StdlibReadProductionProbe";
            Files.writeString(jvmOut.resolve(driver + ".java"),
                productionProbeSource(JvmBackend.classNameFor(APP.path()), reads,
                    consoleValueRead),
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
                "the production JVM artifact compiles with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
                classpath + File.pathSeparator + classes, driver), fixture.root());
            check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK"),
                "the production JVM artifact's read value is the memoized catalog "
                    + "carrier and its direct console call writes one effect; exit="
                    + javaRun.exitCode() + " stdout="
                    + javaRun.stdout().replace("\n", "\\n") + " stderr="
                    + javaRun.stderr().replace("\n", "\\n"));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager, boolean sourceMapExplicit)
            throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            fixture.distributionHome().manifestDirectoryText(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, sourceMapExplicit, fixture.distributionHome(), stager);
    }

    /** The production LuaJIT probe: the surface entries, the memoization, the effect. */
    private static String luaProductionProbe(Path artifact) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __surface = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if type(__surface) ~= \"table\" then __fail(\"the production chunk "
            + "returned \"..type(__surface)) end\n");
        lua.append("local __console = __exportSurfaces[\"std.console\"]\n");
        lua.append("if __console == nil then __fail(\"no std.console surface\") end\n");
        lua.append("local __log = __console[\"log\"]\n");
        lua.append("if type(__log) ~= \"table\" then __fail(\"no log entry\") end\n");
        lua.append("if __log.__sid ~= \"CONSOLE_LOG\" then __fail(\"row tag \".."
            + "tostring(__log.__sid)) end\n");
        lua.append("if __log.__sig ~= ").append(luaString(CONSOLE_SIG))
            .append(" then __fail(\"carried signature \"..tostring(__log.__sig)) end\n");
        lua.append("if __log.__csig ~= ").append(luaString(CONSOLE_SPEC))
            .append(" then __fail(\"canonical spec \"..tostring(__log.__csig)) end\n");
        lua.append("if __log.__fid ~= nil then __fail(\"frame id\") end\n");
        lua.append("local __key = \"std.console\"..string.char(1)..\"log\"\n");
        lua.append("if __stdlibEntries[__key] ~= __log then __fail(\"the surface entry "
            + "is not the memoized callable\") end\n");
        lua.append("local __str = __exportSurfaces[\"std.string\"]\n");
        lua.append("if __str == nil or __str[\"length\"] == nil then __fail(\"no string "
            + "surface entry\") end\n");
        lua.append("if __str[\"length\"].__sig ~= ").append(luaString(ALGORITHM_SIG))
            .append(" then __fail(\"algorithm signature \"..tostring("
                + "__str[\"length\"].__sig)) end\n");
        lua.append("if __log == __str[\"length\"] then __fail(\"one callable for two "
            + "rows\") end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /** The production JVM probe: the read slots, the carrier, and the effect. */
    private static String productionProbeSource(String className, List<SemanticOp> reads,
            SemanticOp consoleValueRead) {
        long valueId = ((ValueId) consoleValueRead.result()).id();
        long algorithmId = -1;
        for (SemanticOp read : reads) {
            if (readPayload(read).module().equals(STRING_MODULE)) {
                algorithmId = ((ValueId) read.result()).id();
            }
        }
        StringBuilder source = new StringBuilder();
        source.append("public class StdlibReadProductionProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(className).append(".main(new String[0]);\n");
        source.append("    Object read = ").append(className).append(".v")
            .append(valueId).append(";\n");
        source.append("    Object other = ").append(className).append(".v")
            .append(algorithmId).append(";\n");
        source.append("    Object surfaceEntry = deal.codegen.jvm.JvmRuntime"
            + ".EXPORT_SURFACES.get(\"std.console\").entries.get(\"log\");\n");
        source.append("    check(read instanceof deal.codegen.jvm.JvmRuntime."
            + "StdlibFunctionValue, \"the read value is the catalog carrier; got \" "
            + "+ read);\n");
        source.append("    check(surfaceEntry == read, \"the two reads (and the surface "
            + "entry) are the identical object; got \" + read + \" vs \" + surfaceEntry);\n");
        source.append("    check(other != read, \"the algorithmic row is a distinct "
            + "carrier\");\n");
        source.append("    deal.codegen.jvm.JvmRuntime.StdlibFunctionValue callable = "
            + "(deal.codegen.jvm.JvmRuntime.StdlibFunctionValue) read;\n");
        source.append("    check(\"CONSOLE_LOG\".equals(callable.rowId), \"the row tag; "
            + "got \" + callable.rowId);\n");
        source.append("    check(\"").append(CONSOLE_SIG).append("\".equals(callable."
            + "signature), \"the carried signature is the row's declared signature; got "
            + "\" + callable.signature);\n");
        source.append("    check(\"").append(CONSOLE_SPEC).append("\".equals(callable."
            + "spec), \"the carried canonical spec text; got \" + callable.spec);\n");
        source.append("    check(callable.fid == null, \"the carrier carries a null "
            + "frame id\");\n");
        source.append("    check(deal.codegen.jvm.JvmRuntime.stdlibCallable(\"std.console\""
            + ", \"log\", \"CONSOLE_LOG\", \"").append(CONSOLE_SIG).append("\", \"")
            .append(CONSOLE_SPEC).append("\") == read, \"the accessor memoizes per "
            + "program\");\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // Trace parsing and process helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n") + " stderr="
                + stderr.replace("\n", "\\n");
        }
    }

    private static ProcessOutcome runProcess(List<String> command, Path workspace)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workspace.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        return new ProcessOutcome(exit, stdout, stderr);
    }

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
        testEmittedReadOperation();
        testOracleReadRealization();
        testCombinedComposition();
        testStdlibCallableComparison();
        testThreeConsumerProjectMatrix();
        testProductionArtifacts();
        System.out.println();
        System.out.println("StdlibExportReadRealizationTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
