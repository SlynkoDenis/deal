package deal.module;

import deal.ast.*;
import deal.checker.*;
import deal.codegen.Backend;
import deal.codegen.SourceMapGenerator;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.HostModuleDeclarations;
import deal.codegen.js.JsBackend;
import deal.codegen.lua.LuaBackend;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.identity.CanonicalModuleIdentity;
import deal.identity.ProjectModuleIdentity;
import deal.ir.IrDumper;
import deal.lexer.*;
import deal.project.ConfiguredModuleRoot;
import deal.project.ExternalEntry;
import deal.project.NormalizedDeclarationPath;
import deal.project.OutputConfigResolver;
import deal.project.ProjectContext;
import deal.project.ProjectDeploymentIdentity;
import deal.project.ProjectLocator;
import deal.project.NativeLibraryRef;
import deal.project.ProtectedPathOps;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticFormatter;
import deal.diagnostics.DiagnosticOrder;
import deal.diagnostics.DiagnosticRange;
import deal.diagnostics.DiagnosticStructuredOutput;
import deal.descriptors.CanonicalRuntimeTypeDescriptor;
import deal.distribution.DistributionHome;
import deal.ffi.FfiDeclarationValidator;
import deal.ffi.FfiGeneratedModule;
import deal.ffi.LuaFfiBindingGenerator;
import deal.identity.CanonicalClassIdentity;
import deal.publication.PublicationStager;
import deal.parser.*;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuilder;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.LoweringSupport;
import deal.semantic.MigrationPlanner;
import deal.semantic.ModuleFact;
import deal.semantic.ModuleRoute;
import deal.semantic.ModuleRoutePlan;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.RoutePlanResult;
import deal.semantic.ArtifactOwner;
import deal.semantic.CheckedModuleInput;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.StagedArtifact;
import deal.semantic.StagedArtifactSet;
import deal.semantic.TargetAbiValidator;
import deal.semantic.TargetModuleAbi;
import deal.semantic.Target;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FieldInterface;
import deal.semantic.ir.FunctionSignatureAbi;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SyncInvocationEntry;
import deal.types.Type;
import deal.types.Types;

import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import deal.diagnostics.DiagnosticCode;
import java.util.*;

/**
 * Orchestrates multi-module compilation: discovery, parsing, type checking,
 * and code generation for an entire DEAL project.
 *
 * <p>Pipeline phases:
 * <ol>
 *   <li>Discovery: resolve entry module, parse it, find imports, parse
 *       imported modules, repeat depth-first until all modules parsed</li>
 *   <li>Signature extraction: extract export signatures from each parsed
 *       module (lightweight, no full type checking)</li>
 *   <li>Dependency graph: build graph from import relationships, topological
 *       sort, detect circular runtime dependencies</li>
 *   <li>Type checking: in topological order, run Pass 1 (NameResolver) and
 *       Pass 2 (TypeChecker) on each module</li>
 *   <li>Code generation: emit .lua files for each module and copy runtime</li>
 * </ol>
 */
public final class CompilationOrchestrator {

    private final Path entryFile;
    private final Path outputRoot;
    private final boolean verbose;
    private final boolean dumpIr;
    private final boolean sourceMap;

    /**
     * True when {@code --source-map} was explicitly requested, distinct
     * from {@link #sourceMap} (which is also derived from {@code --dump-ir}
     * because IR hardening enables source maps with it). The JVM
     * source-map warning fires only on the explicit request, never on a
     * {@code --dump-ir}-derived one (ISSUE-0091 rework).
     */
    private final boolean sourceMapExplicit;
    private final Backend backend;

    /**
     * The single immutable exact-v1.2 project context governing this
     * compilation (design source
     * {@code strict-project-context-resolution-identity} D1/D7): the
     * production constructor consumes the context published by
     * {@link ProjectLocator}; the test-only isolated-phase constructors
     * synthesize one from their legacy inputs. The context is the single
     * authority for module roots, externals declarations, the stdlib
     * surface, the output path, and the private deployment identity —
     * the legacy {@code moduleRoots}/{@code stdlibDir} fields and the
     * {@code externalsDeclarations}/{@code externalsModulePaths} maps
     * are gone.
     */
    private final ProjectContext context;

    /**
     * True when the compilation's context was authored from a
     * {@code deal.json} manifest (the production
     * {@link ProjectContext}-taking constructor — CLI, the production
     * orchestrator path, and project-level conformance); false for the
     * test-only isolated-phase constructors whose context is
     * synthesized from the harness's own declarations map (parent D10:
     * those APIs may omit {@code ProjectContext}, and their externals
     * map cannot carry {@code nativeLibrary}). The v1.2 C FFI manifest
     * policy's {@code nativeLibrary} authoring rule
     * (docs/spec-v1.2.md:1891 — "a C FFI entry must include
     * nativeLibrary") is enforced exactly on manifest-authored
     * contexts; the synthesized test-only entries are the harness's
     * authority channel and count as manifest-backed.
     */
    private final boolean manifestAuthoredContext;

    /**
     * The T6 source resolver over {@link #context}: every import — and
     * the entry file via {@link SourceModuleResolver#resolveEntryFile} —
     * resolves through its pinned rules (importer-relative first,
     * externals declaration authority, configured roots then the pinned
     * stdlib surface, the 6-module filter, file-keyed E2009; no CWD
     * module fallback), and every successfully resolved source receives
     * one private {@link SourceModuleLocation}.
     */
    private final SourceModuleResolver sourceResolver;

    /**
     * The T7 identity assembly over {@link #context}: class declarations
     * are gated through
     * {@link ModuleIdentityAssembly#gateClassDeclaration} (the
     * unconditional E2010 for a class in an identity-less source) and
     * required public class identities through
     * {@link ModuleIdentityAssembly#requireClassIdentity}.
     */
    private final ModuleIdentityAssembly identityAssembly;

    /**
     * The published {@link SourceModuleLocation} per module source path
     * (keyed by the location's {@code normalizedSourcePath}), in
     * first-publication order.
     */
    private final Map<String, SourceModuleLocation> locations =
        new LinkedHashMap<>();

    /**
     * The release-owned compiler invocation resolved at compile start
     * (foundation F1/F8): every compile carries exactly one purpose,
     * profile, release state, and derived release-state hash. Public
     * builds resolve PUBLIC_BUILD through
     * {@link CompilerProfileProvider}; the verbose report prints the
     * recorded facts but the recording location is the invocation's
     * immutable {@code releaseStateHash} field.
     */
    private final CompilerInvocation invocation;

    /**
     * The foundation-phase result built once per compile (ISSUE-0288):
     * after phase 3 succeeds, {@link CheckedProjectBuilder} consumes the
     * orchestrator's module map in {@code buildCheckOrder} and produces
     * exactly one checked project input and one project interface index.
     * {@code null} before the foundation phase runs (or when a
     * pre-foundation phase failed).
     */
    private CheckedProjectBuildResult checkedProjectBuild;

    /**
     * The requirement-manifest foundation result of this compile
     * (ISSUE-0289): exactly one manifest per implementation module in
     * dependency order computed by {@link LoweringSupport} after the
     * checked project and interface index (foundation F3/F8) —
     * {@code null} before the manifest phase runs or when a preceding
     * phase failed. The support's E6005 diagnostics (an inconsistent
     * checked/interface fact, never a crash) are merged into
     * {@link #diagnostics()}.
     */
    private RequirementManifestResult requirementManifests;

    /**
     * The route-plan foundation result of this compile (ISSUE-0290): one
     * {@code ModuleRoutePlan} for the compile's target after the
     * manifests — {@code null} before the route-plan phase runs, when a
     * preceding phase failed, or for the JS backend (the closed
     * route-plan target axis is LUAJIT|JVM, foundation F4). Planner
     * E6005 diagnostics (fact defects, never a crash) are also merged
     * into {@link #diagnostics()}.
     */
    private RoutePlanResult routePlan;

    /**
     * The ISSUE-0239 E10 per-route emission counters of this compile:
     * {@code semanticEmissionCount} modules were SHARED-routed and
     * emitted from validated semantic IR by the shared emitter;
     * {@code retainedEmissionCount} modules were LEGACY-routed and
     * emitted by the retained backend. Both are zero before phase 4 and
     * read-only after it.
     */
    private int semanticEmissionCount = 0;
    private int retainedEmissionCount = 0;

    /**
     * The project-wide semantic-id allocator of the shared route
     * (ISSUE-0239 E10): one allocator over the dependency-ordered
     * implementation modules, created at the first SHARED lowering.
     */
    private SemanticIdAllocator sharedAllocator;

    /**
     * The lowered callees' recorded {@code EXTERNAL_ENTRY} op ids by
     * module, filled in dependency order as SHARED modules lower
     * (ISSUE-0239 E10: the caller-side {@code externalEntryRef}
     * resolution).
     */
    private final Map<ModuleId, Map<String, OpId>> sharedCalleeEntries =
        new HashMap<>();

    /**
     * The emitted SHARED-owner ABI manifests of this compile (ISSUE-0239
     * E10): one per SHARED-routed module, validated against the staged
     * set and the interface index before publication.
     */
    private final List<TargetModuleAbi> emittedSharedAbis = new ArrayList<>();

    private final Map<String, ModuleInfo> modules = new LinkedHashMap<>();
    private final List<CompilerDiagnostic> diagnostics = new ArrayList<>();
    private boolean hasErrors = false;

    /**
     * The dependency (check/initialization) order of this
     * compilation, in module-path form — the one shared ordering
     * algorithm of {@link ModuleDependencyGraph#initializationOrder}
     * (Kahn over the import edges in module discovery order with the
     * remaining cycle members appended at a stuck step). Phase 2
     * derives the type-checking order from it; the runtime dependency
     * graph phase (ISSUE-0543) republishes the identical order as the
     * initialization order after graph success. The extern-C metadata
     * phase orders imported provider references by it. Empty before
     * phase 2.
     */
    private List<String> dependencyOrder = List.of();

    /**
     * The validated extern-C metadata published by the FFI phase
     * (ISSUE-0162): dotted module path &rarr; the generated module
     * inputs (descriptor, cdef bundle, retained plans, forward
     * bindings). Populated only for the LuaJIT backend after successful
     * validation; empty for JVM/JS and on any validation failure — a
     * failed validation or an incapable backend publishes no metadata
     * and no partial artifact.
     */
    private final Map<String, FfiGeneratedModule> ffiGenerations =
        new LinkedHashMap<>();

    /**
     * The compilation's declaration surface (ISSUE-0630, design source
     * {@code project-lowering-entry-and-registration-seeds} D3): one
     * immutable fact record per host and extern-C declaration module the
     * compilation imports, produced once at the start of phase 4 before
     * any emission arm runs. Null before phase 4 and on a producer
     * defect (an unrepresentable declared class field type), where the
     * compile carries the first E6005 and publishes nothing.
     */
    private HostDeclarationSurface hostDeclarationSurface;

    /**
     * The compiler-default planning result of this compile (ISSUE-0541,
     * {@code provider-versioned-default-plans} D1): module source path
     * &rarr; the planned classes (one {@link CompilerClassDefaultPlan}
     * per plan-bearing class plus the ordered provisional
     * {@link DefaultResourceOccurrence} list), in planning order —
     * dependency order over the implementation modules and extern-C
     * declaration modules. Plans stay compiler-internal until the
     * dependency graph succeeds: this epic publishes them nowhere (no
     * lowerer, no FFI descriptor, no artifact). Empty before the
     * planning phase runs, when a preceding phase failed, or when
     * planning produced error-level diagnostics.
     */
    private final Map<String, List<PlannedDefaultClass>>
        plannedDefaultClasses = new LinkedHashMap<>();

    /**
     * The dependency graph's published result of this compile
     * (ISSUE-0543): the completed plans — every plan's
     * {@code runtimeDependencies} filled with the final digest-bearing
     * records and the serializer-completed entry content preserved —
     * keyed by module source path in planning order. Populated only
     * after the graph phase succeeded; empty on E2005 and on any
     * preceding failure (a failed graph publishes no plan).
     */
    private final Map<String, List<PlannedDefaultClass>>
        completedDefaultPlans = new LinkedHashMap<>();

    /**
     * The merged final digest-bearing runtime dependency records of
     * this compile (ISSUE-0543): ordinary RUNTIME_USE records in
     * first-occurrence order followed by the per-plan
     * DEFERRED_DEFAULT_BINDING records, structurally deduplicated.
     * Empty before the graph phase runs or when the graph rejected the
     * compilation (E2005 publishes no dependency record).
     */
    private List<RuntimeImportDependency> runtimeDependencies =
        List.of();

    /**
     * The JVM codegen pass-1 results of this compile (ISSUE-0374 profile
     * plumb observability): module source path → the
     * {@link JvmBackend.JvmCodegenResult} the backend generated for every
     * module it accepted — including the backend's recorded int32 mode,
     * the real stored backend state the profile plumb selected
     * ({@link #invocation()}'s semantic profile → {@link
     * JvmBackend#generate}). Read-only; empty before the JVM codegen
     * phase runs or when the backend rejected every module. A pass-2
     * class-name collision does not remove a pass-1 entry (it only
     * blocks the artifact write).
     */
    private final Map<String, JvmBackend.JvmCodegenResult> jvmGeneratedResults =
        new LinkedHashMap<>();

    /**
     * The LuaJIT codegen results of this compile (ISSUE-0544 lowering
     * observability, the JVM {@code jvmGeneratedResults} precedent):
     * module source path &rarr; the {@link LuaBackend.GenerationResult}
     * the backend generated for every module it accepted — including the
     * realized {@code RuntimeClassDefaultPlan}s the lowering epic
     * consumed. Read-only; empty before the LuaJIT codegen phase runs
     * or when the backend rejected every module.
     */
    private final Map<String, LuaBackend.GenerationResult>
        luaGeneratedResults = new LinkedHashMap<>();

    /**
     * The JavaScript codegen results of this compile (ISSUE-0544
     * lowering observability, the JVM {@code jvmGeneratedResults}
     * precedent): module source path &rarr; the
     * {@link JsBackend.JsCodegenResult} the backend generated for every
     * module it accepted — including the realized
     * {@code RuntimeClassDefaultPlan}s the lowering epic consumed.
     * Read-only; empty before the JS codegen phase runs or when the
     * backend rejected every module.
     */
    private final Map<String, JsBackend.JsCodegenResult>
        jsGeneratedResults = new LinkedHashMap<>();

    /**
     * The {@code --diagnostics-json} output path, or {@code null} when the
     * structured document was not requested. When set, the orchestrator
     * writes the {@link DiagnosticStructuredOutput} document for every
     * compilation — successful or failed — without changing the exit code;
     * a write failure is a deterministic compiler I/O diagnostic on
     * stderr with exit 1 (D8, parent D11 I/O discipline).
     */
    private final Path diagnosticsJsonPath;

    /**
     * The pinned three-tier distribution resolver of this compilation's
     * project (ISSUE-0457,
     * {@code release-distribution-packaging-and-discovery} D3): the
     * runtime and stdlib deployment copies resolve their sources
     * through it in the pinned order — project-local surface first,
     * then the language distribution (classpath resources, then the
     * {@code DEAL_HOME} filesystem layout), then the checkout CWD dev
     * fallback.
     */
    private final DistributionHome distributionHome;

    /**
     * The transactional whole-project publication stager of the running
     * {@link #compile()} call (design source
     * {@code whole-project-artifact-publication} D1-D6): every output
     * byte — phase-4 module artifacts, the runtime/stdlib deployment
     * copies, the IR dumps, and the source-map sidecars — is staged
     * into its per-invocation staging tree and atomically swapped into
     * the live output root by the publish step; nothing writes the live
     * root except that step. {@code null} outside a {@code compile()}
     * call.
     */
    private PublicationStager stager;

    /**
     * The first staging write failure of the running compile (D4): when
     * set, nothing is published, the stage tree is removed in
     * {@link #compile()}, the diagnostics report is unchanged, and the
     * pinned deterministic compiler I/O diagnostic
     * {@code deal: cannot publish artifacts to '<root>': <reason>} is
     * printed on stderr with exit 1.
     */
    private IOException pendingStageFailure;

    // Host externals (ISSUE-0082, host-module-abi D5, file-keyed since
    // ISSUE-0269): the externals declarations live in
    // ProjectContext.externals (raw import specifier → validated
    // ExternalEntry). A resolved source whose canonical URI equals an
    // entry's declaration path carries ExternalModule(that key)
    // regardless of the import spelling — the classification recorded on
    // each SourceModuleLocation by the T6 resolver; the dotted
    // typing/class-identity name for an externals module is derived from
    // the raw specifier (the legacy externalsModulePaths behavior).

    private static final class ModuleInfo {
        final String sourcePath;
        final String modulePath;
        final boolean isDeclarationFile;
        final SourceModuleLocation location;
        ProgramNode rawAst;
        Map<String, Type> exports;
        SymbolTable symbolTable;
        CheckResult checkResult;
        ParseResult parseResult;
        NameResolver nameResolver;

        ModuleInfo(String sourcePath, String modulePath, boolean isDeclarationFile,
                   SourceModuleLocation location) {
            this.sourcePath = sourcePath;
            this.modulePath = modulePath;
            this.isDeclarationFile = isDeclarationFile;
            this.location = location;
        }
    }

    /**
     * Production entry point (ISSUE-0269 migration, design source
     * {@code strict-project-context-resolution-identity} D7 + Failure and
     * operations): the orchestrator consumes the immutable validated
     * {@link ProjectContext} published by {@link ProjectLocator} plus the
     * compilation options. The backend is the context's effective backend
     * ({@code "luajit"} | {@code "jvm"} | {@code "js"} — the strict
     * backend set), the
     * output root is the context's classified
     * {@link OutputConfigResolver.OutputRef} (created only in the write
     * phase), and module roots, externals declarations, the stdlib
     * surface, and the private deployment identity are the context's
     * validated values. No {@code DealConfig}, no implicit
     * entry-directory root, no CWD bare-lookup fallback, and no lossy
     * {@code computeModulePath} participate: module naming derives from
     * the T5/T6 classification (the dotted root-relative path, the
     * externals raw specifier with {@code /} → {@code .}, the pinned
     * stdlib module name) and the private {@code deploymentModuleId} for
     * unclassified sources.
     *
     * @param context the validated immutable project context
     * @param entryFile the entry source file (absolute normalized
     *                  lexical path — the same path text the T6
     *                  entry-file seam publishes)
     * @param verbose verbose phase/timing output
     * @param dumpIr produce IR dump files
     * @param sourceMap produce source-map sidecars
     * @param sourceMapExplicit true when {@code --source-map} was
     *                         explicitly requested (distinct from the
     *                         {@code --dump-ir}-derived flag)
     * @param diagnosticsJsonPath the {@code --diagnostics-json} output
     *                            path, or null
     * @param invocation the release-owned compiler invocation
     */
    public CompilationOrchestrator(ProjectContext context, Path entryFile,
                                    boolean verbose, boolean dumpIr,
                                    boolean sourceMap, boolean sourceMapExplicit,
                                    Path diagnosticsJsonPath,
                                    CompilerInvocation invocation) {
        this.invocation = java.util.Objects.requireNonNull(invocation,
            "invocation must not be null");
        this.context = java.util.Objects.requireNonNull(context, "context");
        this.manifestAuthoredContext = true;
        this.backend = backendOf(context.backend());
        this.entryFile = entryFile.toAbsolutePath().normalize();
        this.outputRoot = Path.of(context.outputPath().absoluteNormalizedPath());
        this.verbose = verbose;
        this.dumpIr = dumpIr;
        this.sourceMap = sourceMap;
        this.sourceMapExplicit = sourceMapExplicit;
        this.diagnosticsJsonPath = diagnosticsJsonPath;
        this.distributionHome = DistributionHome.forManifestDirectory(
            context.manifestDirectory());
        this.sourceResolver = new SourceModuleResolver(context);
        this.identityAssembly = new ModuleIdentityAssembly(context);
    }

    /**
     * Test-only isolated-phase constructor (parent D10: isolated phase
     * APIs may omit {@link ProjectContext}; CLI, the production
     * orchestrator path, and project-level conformance may not). The
     * legacy inputs — explicit module roots, a stdlib-directory hint,
     * an externals declarations map (raw import specifier → declaration
     * path text), the backend, and the output root — are synthesized
     * into an internal {@link ProjectContext} so every compilation still
     * flows through the one {@link SourceModuleResolver} +
     * {@link ModuleIdentityAssembly} pipeline. Production code never
     * constructs these overloads.
     */
    public CompilationOrchestrator(Path entryFile, Path outputRoot, boolean verbose,
                                    Map<String, String> externalsDeclarations,
                                    List<Path> moduleRoots, Path stdlibDir) {
        this(entryFile, outputRoot, verbose, false, false, Backend.LUAJIT,
            externalsDeclarations, moduleRoots, stdlibDir);
    }

    /** Test-only isolated-phase overload; see the 6-argument form. */
    public CompilationOrchestrator(Path entryFile, Path outputRoot, boolean verbose,
                                    boolean dumpIr,
                                    Map<String, String> externalsDeclarations,
                                    List<Path> moduleRoots, Path stdlibDir) {
        this(entryFile, outputRoot, verbose, dumpIr, false, Backend.LUAJIT,
            externalsDeclarations, moduleRoots, stdlibDir);
    }

    /** Test-only isolated-phase overload; see the 6-argument form. */
    public CompilationOrchestrator(Path entryFile, Path outputRoot, boolean verbose,
                                    boolean dumpIr, boolean sourceMap,
                                    Map<String, String> externalsDeclarations,
                                    List<Path> moduleRoots, Path stdlibDir) {
        this(entryFile, outputRoot, verbose, dumpIr, sourceMap, Backend.LUAJIT,
            externalsDeclarations, moduleRoots, stdlibDir);
    }

    /**
     * Test-only isolated-phase overload with an explicit backend (the
     * JS-backend harnesses pass {@link Backend#JS} for test-local
     * compilations without a manifest); see the 6-argument form. LuaJIT
     * remains the default: the overloads above delegate with
     * {@link Backend#LUAJIT}.
     */
    public CompilationOrchestrator(Path entryFile, Path outputRoot, boolean verbose,
                                    boolean dumpIr, boolean sourceMap, Backend backend,
                                    Map<String, String> externalsDeclarations,
                                    List<Path> moduleRoots, Path stdlibDir) {
        this(entryFile, outputRoot, verbose, dumpIr, sourceMap, sourceMap,
            backend, externalsDeclarations, moduleRoots, stdlibDir);
    }

    /**
     * Test-only isolated-phase overload; see the 6-argument form.
     * {@code sourceMapExplicit} distinguishes the explicit
     * {@code --source-map} request from the effective {@code sourceMap}
     * flag (also derived from {@code --dump-ir}).
     */
    public CompilationOrchestrator(Path entryFile, Path outputRoot, boolean verbose,
                                    boolean dumpIr, boolean sourceMap,
                                    boolean sourceMapExplicit, Backend backend,
                                    Map<String, String> externalsDeclarations,
                                    List<Path> moduleRoots, Path stdlibDir) {
        this(entryFile, outputRoot, verbose, dumpIr, sourceMap,
            sourceMapExplicit, backend, externalsDeclarations, moduleRoots,
            stdlibDir, null, defaultInvocation());
    }

    /**
     * The canonical test-only isolated-phase constructor: synthesizes the
     * internal {@link ProjectContext} from the legacy inputs (see
     * {@link #synthesizeContext}) and installs the one
     * {@link SourceModuleResolver} + {@link ModuleIdentityAssembly}
     * pipeline. With the structured-output path set (D8),
     * {@link #compile()} writes the {@link DiagnosticStructuredOutput}
     * document for every compilation — successful or failed — without
     * changing the exit code; a write failure is a deterministic
     * compiler I/O diagnostic on stderr with exit 1.
     */
    public CompilationOrchestrator(Path entryFile, Path outputRoot, boolean verbose,
                                    boolean dumpIr, boolean sourceMap,
                                    boolean sourceMapExplicit, Backend backend,
                                    Map<String, String> externalsDeclarations,
                                    List<Path> moduleRoots, Path stdlibDir,
                                    Path diagnosticsJsonPath,
                                    CompilerInvocation invocation) {
        this.invocation = java.util.Objects.requireNonNull(invocation,
            "invocation must not be null");
        this.context = synthesizeContext(entryFile, outputRoot, backend,
            externalsDeclarations, moduleRoots, stdlibDir);
        this.manifestAuthoredContext = false;
        this.backend = backend;
        this.entryFile = entryFile.toAbsolutePath().normalize();
        this.outputRoot = outputRoot.toAbsolutePath().normalize();
        this.verbose = verbose;
        this.dumpIr = dumpIr;
        this.sourceMap = sourceMap;
        this.sourceMapExplicit = sourceMapExplicit;
        this.diagnosticsJsonPath = diagnosticsJsonPath;
        this.distributionHome = DistributionHome.forManifestDirectory(
            context.manifestDirectory());
        this.sourceResolver = new SourceModuleResolver(context);
        this.identityAssembly = new ModuleIdentityAssembly(context);
    }

    /**
     * The strict effective backend of a published context
     * ({@code "luajit"} → {@link Backend#LUAJIT}, {@code "jvm"} →
     * {@link Backend#JVM}, {@code "js"} → {@link Backend#JS}); any
     * other text is a defensive programming error for a validated
     * context (the strict backend set is closed) and fails with
     * {@link IllegalArgumentException}.
     */
    private static Backend backendOf(String backendText) {
        return switch (backendText) {
            case "luajit" -> Backend.LUAJIT;
            case "jvm" -> Backend.JVM;
            case "js" -> Backend.JS;
            default -> throw new IllegalArgumentException(
                "unsupported effective backend: " + backendText);
        };
    }

    /**
     * Synthesizes the internal {@link ProjectContext} of a test-only
     * isolated-phase constructor (no {@code ProjectContext} input, parent
     * D10): the given module roots become {@link ConfiguredModuleRoot}s
     * through the D4 root conversion (no existence requirement;
     * longest-existing-directory-prefix symlink resolution) with a
     * deterministic representable {@code configuredText} derived from the
     * root's absolute path components (test setups have no manifest
     * spelling); the externals declarations map becomes
     * {@link ExternalEntry} records with normalized declaration paths;
     * the stdlib surface is probed (stdlib-directory hint first, then the
     * entry directory, then the process CWD) and the six spec-listed
     * declaration files under the surface are canonicalized; the output
     * is classified from the given output root; and the private
     * deployment identity is a deterministic synthetic value over the
     * entry directory (test-only compilations carry no manifest bytes).
     * Deterministic for unchanged inputs.
     */
    private static ProjectContext synthesizeContext(Path entryFile, Path outputRoot,
            Backend backend, Map<String, String> externalsDeclarations,
            List<Path> moduleRoots, Path stdlibDir) {
        Path entryDir = entryFile.toAbsolutePath().normalize().getParent();
        String entryDirText = entryDir.toString();

        List<ConfiguredModuleRoot> roots = new ArrayList<>();
        for (Path root : moduleRoots) {
            String rootText = root.toAbsolutePath().normalize().toString();
            ProtectedPathOps.PathResult converted =
                ProtectedPathOps.normalizePrefixResolved(rootText);
            String absolute = converted instanceof ProtectedPathOps.PathResult.Success success
                ? success.resolvedPath().toString()
                : rootText;
            roots.add(new ConfiguredModuleRoot(
                configuredRootTextOf(Path.of(absolute)), absolute, null));
        }

        String surface = probeLegacySurface(stdlibDir, entryDir);
        List<String> stdlibDeclarationFiles =
            resolveSurfaceDeclarationFiles(surface);

        Map<String, ExternalEntry> externals = new LinkedHashMap<>();
        if (externalsDeclarations != null) {
            for (Map.Entry<String, String> entry
                    : externalsDeclarations.entrySet()) {
                Path declaration = Path.of(entry.getValue());
                if (!declaration.isAbsolute()) {
                    declaration = entryDir.resolve(declaration);
                }
                externals.put(entry.getKey(), new ExternalEntry(entry.getKey(),
                    new NormalizedDeclarationPath(
                        declaration.normalize().toString(), null),
                    null, null));
            }
        }

        OutputConfigResolver.OutputRef output = new OutputConfigResolver.OutputRef(
            OutputConfigResolver.Source.MANIFEST,
            outputRoot.isAbsolute() ? OutputConfigResolver.Kind.ABSOLUTE_PATH
                : OutputConfigResolver.Kind.MANIFEST_RELATIVE_PATH,
            outputRoot.toString(),
            outputRoot.toAbsolutePath().normalize().toString(), null);

        return new ProjectContext(
            entryDir.resolve("deal.json").normalize().toString(),
            entryDirText,
            entryDirText,
            "1.2",
            roots,
            output,
            backend.cliName(),
            externals,
            "1.2",
            surface,
            stdlibDeclarationFiles,
            syntheticDeploymentIdentity(entryDir));
    }

    /**
     * The deterministic representable {@code configuredText} of a
     * synthesized root: the root path's final component (no manifest
     * spelling exists for a test-only context, and the text only feeds
     * the T7 representability gates and the compilation's
     * class-identity index — the pre-ISSUE-0269 configured-root-text
     * fallback for a config-less compile kept byte-identical). A
     * degenerate root (filesystem root or a relative input) falls back
     * to the pinned {@code "project"} text.
     */
    private static String configuredRootTextOf(Path absoluteRoot) {
        Path fileName = absoluteRoot.getFileName();
        return fileName == null || fileName.toString().isEmpty()
            ? "project" : fileName.toString();
    }

    /**
     * The legacy stdlib-surface probe of a synthesized context: the
     * stdlib-directory hint (the legacy "parent of std/" value) first,
     * then {@code <entryDirectory>/std}, then the process-CWD
     * {@code std} directory; absence is a value (null), never an error.
     * The returned path is fully symlink-resolved when present.
     */
    private static String probeLegacySurface(Path stdlibDir, Path entryDir) {
        Optional<Path> hinted = ProtectedPathOps.probeDirectory(
            stdlibDir == null ? entryDir.resolve("std")
                : stdlibDir.resolve("std"));
        if (hinted.isPresent()) {
            return hinted.get().toString();
        }
        Optional<Path> local = ProtectedPathOps.probeDirectory(
            entryDir.resolve("std"));
        if (local.isPresent()) {
            return local.get().toString();
        }
        Optional<Path> distribution = ProtectedPathOps.probeDirectory(
            Path.of("").toAbsolutePath().resolve("std"));
        return distribution.map(Path::toString).orElse(null);
    }

    /**
     * The six spec-listed stdlib declaration files under a resolved
     * surface, each fully symlink-resolved (the
     * {@link ProjectContext#stdlibDeclarationFiles()} derivation of a
     * synthesized context); missing/non-regular/unresolvable files are
     * omitted, and an absent surface yields the empty list.
     */
    private static List<String> resolveSurfaceDeclarationFiles(String surface) {
        List<String> files = new ArrayList<>();
        if (surface == null) {
            return files;
        }
        for (String module : ProjectLocator.SPEC_STDLIB_MODULES) {
            Path pinned = Path.of(surface).resolve(module + ".d.deal");
            if (!Files.isRegularFile(pinned)) {
                continue;
            }
            try {
                files.add(pinned.toRealPath().toString());
            } catch (IOException ignored) {
                // No canonical path: no resolved source can equal it.
            }
        }
        return files;
    }

    /**
     * The deterministic synthetic deployment identity of a test-only
     * context: the {@code file:} URI of a synthesized manifest path
     * under the entry directory plus SHA-256 over the empty manifest
     * byte array (test-only compilations carry no manifest bytes).
     */
    private static ProjectDeploymentIdentity syntheticDeploymentIdentity(
            Path entryDir) {
        ProtectedPathOps.UriResult uri = ProtectedPathOps.toFileUri(
            entryDir.resolve("deal.json"));
        String uriText = uri instanceof ProtectedPathOps.UriResult.Success success
            ? success.uri().toString()
            : "file:" + entryDir.resolve("deal.json");
        // The pinned module identity-digest facility (the closed compiler
        // SHA-256 registry owns every digest site; this synthesized
        // test-only identity reuses it rather than a second digest
        // implementation).
        return new ProjectDeploymentIdentity(uriText,
            IdentityDigests.sha256Hex(new byte[0]));
    }

    /**
     * The default release-owned invocation used by every constructor that
     * is not given one explicitly: {@code PUBLIC_BUILD} resolved through
     * {@link CompilerProfileProvider} from
     * {@link ReleaseConfiguration#CURRENT_RELEASE_STATE} and the release
     * capability registry (A2 — the single release-owned selection
     * point; the release state is {@code V1_2_ACTIVE} after the E12
     * activation release action, so the derived public profile is
     * {@code DEAL_V1_2_INT32} and production SHARED routing is eligible
     * for the promoted capability × target pairs, foundation F1/F4).
     * is the only invocation constructor — the orchestrator never
     * constructs an invocation itself.
     */
    private static CompilerInvocation defaultInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /**
     * The release-owned compiler invocation of this compile: exactly one
     * purpose/profile/release state with the derived release-state hash
     * recorded (foundation F1) — resolved before checking/lowering and
     * recorded verbatim on every invocation, verbose or not.
     *
     * @return the immutable invocation record
     */
    public CompilerInvocation invocation() {
        return invocation;
    }

    /**
     * Read-only view of {@link #jvmGeneratedResults}: the backend's
     * generated JVM artifact records of this compile keyed by module
     * source path (ISSUE-0374 profile plumb observability).
     *
     * @return the pass-1 accepted module results; empty before the JVM
     *         codegen phase runs
     */
    public Map<String, JvmBackend.JvmCodegenResult> jvmGeneratedResults() {
        return Collections.unmodifiableMap(jvmGeneratedResults);
    }

    /**
     * The checked-project foundation result of this compile (ISSUE-0288):
     * exactly one checked project input and one project interface index
     * built in dependency order after phase 3 succeeds — {@code null} before the foundation phase runs or when
     * a pre-foundation phase failed. The builder's E6005 diagnostics (a
     * fact defect, never a crash) are also merged into
     * {@link #diagnostics()}.
     *
     * @return the build result, or {@code null} when the foundation phase
     *         did not run
     */
    public CheckedProjectBuildResult checkedProject() {
        return checkedProjectBuild;
    }

    /**
     * The requirement-manifest foundation result of this compile
     * (ISSUE-0289): one {@code SemanticRequirementManifest} per
     * implementation module in dependency order — {@code null} before the
     * manifest phase runs or when a preceding phase failed.
     *
     * @return the manifest result, or {@code null} when the phase did not
     *         run
     */
    public RequirementManifestResult requirementManifests() {
        return requirementManifests;
    }

    /**
     * The route-plan foundation result of this compile (ISSUE-0290):
     * exactly one deterministic {@code ModuleRoutePlan} for the
     * compile's target in dependency order — {@code null} before the
     * route-plan phase runs, when a preceding phase failed, or when the
     * backend is JS (no closed route-plan target exists for JS in this
     * epic; the phase is skipped and the retained JS path is
     * untouched).
     *
     * @return the route-plan result, or {@code null} when the phase did
     *         not run
     */
    public RoutePlanResult routePlan() {
        return routePlan;
    }

    /**
     * The number of SHARED-routed modules emitted from validated
     * semantic IR in phase 4 of this compile (ISSUE-0239 E10) — zero
     * before the codegen phase runs.
     *
     * @return the semantic-emission count
     */
    public int semanticEmissionCount() {
        return semanticEmissionCount;
    }

    /**
     * The number of LEGACY-routed modules emitted by the retained
     * backend in phase 4 of this compile (ISSUE-0239 E10) — zero before
     * the codegen phase runs.
     *
     * @return the retained-emission count
     */
    public int retainedEmissionCount() {
        return retainedEmissionCount;
    }

    // =========================================================================
    // Public API
    // =========================================================================

    public boolean compile() throws IOException {
        // Transactional publication (whole-project-artifact-publication
        // D1-D6): one fresh staging stager per compile; the stage tree
        // and the per-root lock are created lazily at the first staged
        // write (an IR dump in phase 1/3, or a phase-4 artifact) and
        // the staged set is atomically swapped into the live output
        // root only when the compilation succeeded.
        stager = PublicationStager.forRoot(outputRoot);
        pendingStageFailure = null;
        boolean success;
        try {
            success = compileInternal();
            if (success) {
                try {
                    stager.publish();
                } catch (IOException publishFailure) {
                    // Publish-step I/O failure (D4): the stager already
                    // restored/cleaned per D2; report the pinned
                    // deterministic compiler I/O diagnostic on stderr
                    // with exit 1.
                    System.err.println("deal: cannot publish artifacts to '"
                        + outputRoot + "': " + publishFailure.getMessage());
                    success = false;
                }
            }
        } finally {
            if (!stager.published()) {
                // Any failure (or no publish) removes the stage tree and
                // releases the per-root lock: the prior live set is
                // untouched (an absent prior set stays absent) and no
                // staging residue survives.
                stager.discard();
            }
            stager = null;
        }
        if (pendingStageFailure != null) {
            // Staging write failure (D4): nothing published, diagnostics
            // report unchanged, pinned deterministic compiler I/O
            // diagnostic on stderr with exit 1.
            System.err.println("deal: cannot publish artifacts to '"
                + outputRoot + "': " + pendingStageFailure.getMessage());
            success = false;
        }

        // Structured output (D8): the document is written for every
        // compilation — successful or failed — when --diagnostics-json
        // was requested, without changing the exit code; it is a
        // caller-requested report outside the published set. A write
        // failure is a deterministic compiler I/O diagnostic on stderr
        // with exit 1; no raw path exception escapes (parent D11 I/O
        // discipline).
        if (diagnosticsJsonPath != null) {
            try {
                // D1 (deterministic-diagnostics): the document receives
                // the canonical report-ordered list; the internal
                // emission-order collection is unchanged.
                Files.writeString(diagnosticsJsonPath,
                    DiagnosticStructuredOutput.toJson(
                        DiagnosticOrder.canonical(diagnostics)));
            } catch (IOException e) {
                System.err.println("deal: cannot write diagnostics JSON to '"
                    + diagnosticsJsonPath + "': " + e.getMessage());
                return false;
            }
        }
        return success;
    }

    /** The compilation pipeline proper; see {@link #compile()}. */
    private boolean compileInternal() throws IOException {
        long startTime = System.currentTimeMillis();

        // The invocation was resolved at compile start (F1/F8); the
        // verbose report prints the recorded facts. The recording
        // location is the invocation's immutable releaseStateHash field —
        // present on every invocation, verbose or not.
        if (verbose) {
            System.out.println("Purpose: " + invocation.purpose());
            System.out.println("Semantic profile: " + invocation.semanticProfile());
            System.out.println("Release state: " + invocation.releaseState());
            System.out.println("Release-state hash: " + invocation.releaseStateHash());
        }

        log("Phase 0: Module discovery and parsing");
        discoverAndParse();
        if (hasErrors) { printDiagnostics(); return false; }

        log("Phase 1: Export signature extraction");
        extractSignatures();
        if (hasErrors) { printDiagnostics(); return false; }

        // DEAL v1.2 selected-entry rule: the entry module must export
        // non-async main() with signature (): null.  The backend invokes
        // main() from that module.
        validateEntryMain();

        log("Phase 2: Dependency graph and ordering");
        List<String> checkOrder = buildCheckOrder();
        if (checkOrder == null) { printDiagnostics(); return false; }
        this.dependencyOrder = List.copyOf(checkOrder);

        log("Phase 3: Type checking (" + checkOrder.size() + " modules)");
        typeCheckAll(checkOrder);
        if (hasErrors) { printDiagnostics(); return false; }

        // Foundation phase (F2/F8): after phase 3 succeeds, the builder
        // produces exactly one CheckedProjectInput and one
        // ProjectInterfaceIndex per compile in dependency order. The
        // builder is strictly read-only over the checked facts; its E6005
        // diagnostics fail the compile exactly like frontend errors.
        log("Phase 3.5: Checked project and interface index");
        buildCheckedProject(checkOrder);
        if (hasErrors) { printDiagnostics(); return false; }

        // Foundation phase (F3/F8): after the checked project and index,
        // LoweringSupport computes exactly one SemanticRequirementManifest
        // per implementation module in dependency order (the closed
        // capability claims — the superseded four-part
        // STDLIB_TIME_CONFLICT trigger is retired since K7 — plus the
        // constructCoverage rows). Read-only over the checked facts; its
        // E6005 diagnostics fail the compile exactly like frontend errors.
        log("Phase 3.6: Semantic requirement manifests");
        computeRequirementManifests();
        if (hasErrors) { printDiagnostics(); return false; }

        // Foundation phase (F4/F8): after the manifests, MigrationPlanner
        // produces exactly one deterministic ModuleRoutePlan for the
        // compile's target in dependency order (closed routing rules, the
        // closed E6005-vs-LEGACY-reroute split, plan-time TargetModuleAbi
        // records). Read-only over the checked facts; its E6005
        // diagnostics fail the compile exactly like frontend errors. The
        // JS backend has no closed route-plan target in this epic, so the
        // phase is skipped and the retained JS path is untouched.
        // ISSUE-0643 (design source
        // production-project-emission-and-atomic-cutover P4): the
        // release-owned production invocation skips phase 3.7 entirely —
        // the production arm consults no route plan, so no plan is
        // computed and the route-plan view stays null. Every other
        // LuaJIT/JVM invocation (the harness purposes and the test-only
        // PUBLIC_BUILD records that are not the release-owned record)
        // keeps the phase and the harness arm.
        log("Phase 3.7: Route plan");
        if (productionArmApplies()) {
            log("  Route plan skipped: the release-owned production invocation"
                + " emits one project artifact");
        } else {
            planRoutesForCompile();
            if (hasErrors) { printDiagnostics(); return false; }
        }

        // Default planning phase (ISSUE-0541, design source
        // provider-versioned-default-plans D1-D4): after checking and
        // declaration analysis, before serialization and the graph —
        // one CompilerClassDefaultPlan per plan-bearing class
        // (implementation classes planned by DefaultSemanticPlanner,
        // C-struct classes planned by DeclarationSemanticAnalyzer),
        // resolution/type-checking in the declaring lexical/import
        // context, the complete typed evaluator IR walk, and the two
        // plan-shape gates (E4001 declaration shape, E3020 sync
        // evaluators). Host-declared classes are exempt and produce no
        // plan. No evaluator is invoked and no library is loaded; no
        // digest is computed and no dependency edge or graph runs
        // (the serializer and graph epics own those).
        log("Phase 3.8: Default planning and declaration default analysis");
        planDefaultClasses();
        if (hasErrors) { printDiagnostics(); return false; }

        // Runtime dependency graph phase (ISSUE-0543, design source
        // provider-versioned-default-plans D1/D7/D8): after planning,
        // before FFI validation and codegen — the digest-free SCC pass
        // merges the ordinary runtime-use edges (RUNTIME_USE) with the
        // planner's default edges (DEFERRED_DEFAULT_BINDING) over the
        // one RuntimeImportDependency carrier; a runtime SCC reports
        // E2005 with a note per runtime edge and publishes no plan,
        // FFI metadata, or artifact. Only an acyclic pass requests the
        // provider digests (the serializer, with the ordinary
        // occurrences demanded), publishes the final digest-bearing
        // dependency records, completes every plan's
        // runtimeDependencies, and fixes the initialization order.
        // No evaluator is invoked and no library is loaded here.
        log("Phase 3.85: Runtime dependency graph and plan publication");
        evaluateDependencyGraph();
        if (hasErrors) { printDiagnostics(); return false; }

        // FFI phase (ISSUE-0162, design source
        // deal-v1.2-directives-and-c-ffi-declarations D4/D7/D8): after
        // semantic/graph success, validate every extern-C declaration
        // module (E7002 policy), reject the C FFI on an incapable
        // backend (JVM: E6006 FFI_UNSUPPORTED_BACKEND at @extern-c)
        // before any artifact write, and publish the validated
        // metadata/bundle/bindings on LuaJIT for later runtime loading.
        // Validation never evaluates defaults; a failed validation or
        // an incapable backend publishes no metadata and no artifact.
        log("Phase 3.9: C FFI declaration validation and metadata");
        validateCffiDeclarations();
        if (hasErrors) { printDiagnostics(); return false; }

        log("Phase 4: Code generation");
        // Declaration surface (ISSUE-0630, design source
        // project-lowering-entry-and-registration-seeds D3 and the
        // declaration-surface contract): phase-4 input data, produced
        // once per compile over every host and extern-C declaration
        // module the compilation imports, before any emission arm runs.
        // A producer defect (a declared class field type with no runtime
        // representation) fails the compile through the descriptor path
        // with the first E6005 and publishes nothing.
        hostDeclarationSurface = produceHostDeclarationSurface();
        if (hasErrors) { printDiagnostics(); return false; }
        codegenAll();
        if (hasErrors) { printDiagnostics(); return false; }

        long elapsed = System.currentTimeMillis() - startTime;
        System.out.println("Compilation successful: " + modules.size() + " module(s)");
        if (verbose) {
            System.out.println("Total time: " + elapsed + "ms");
        }
        return true;
    }

    public List<CompilerDiagnostic> diagnostics() {
        return Collections.unmodifiableList(diagnostics);
    }

    // =========================================================================
    // Phase 0: Discovery and parsing
    // =========================================================================

    private void discoverAndParse() throws IOException {
        long phaseStart = System.currentTimeMillis();
        String entrySourcePath = entryFile.toString();
        Queue<String> pending = new ArrayDeque<>();
        pending.add(entrySourcePath);

        while (!pending.isEmpty()) {
            String sourcePath = pending.poll();
            if (modules.containsKey(sourcePath)) continue;

            // The location of this source: imports carry their published
            // T6 location through the pending queue; the entry file is
            // published through the resolver's entry-file seam.
            SourceModuleLocation location = locations.get(sourcePath);
            if (location == null) {
                SourceModuleResolver.ResolveResult entryResult =
                    sourceResolver.resolveEntryFile(sourcePath,
                        Span.synthetic(sourcePath));
                if (entryResult instanceof SourceModuleResolver.ResolveResult.Failure f) {
                    diagnostics.add(f.diagnostic());
                    hasErrors = true;
                    continue;
                }
                location = ((SourceModuleResolver.ResolveResult.Resolved)
                    entryResult).location();
                locations.put(sourcePath, location);
            }

            Path file = Path.of(sourcePath);
            if (!Files.exists(file)) {
                // Anchorless site (D5): the queue holds no import
                // declaration for a vanished file, so the diagnostic is
                // synthetic with a note naming the unresolved path.
                syntheticError(DiagnosticCode.E2003,
                    "Module not found: " + sourcePath, sourcePath,
                    "missing anchor: unresolved module path '"
                        + sourcePath + "'");
                continue;
            }

            long modStart = System.currentTimeMillis();
            boolean isDecl = sourcePath.endsWith(".d.deal");

            String source;
            try {
                source = Files.readString(file);
            } catch (IOException e) {
                // Anchorless site (D5): no import declaration span is
                // available for the unreadable queue file, so the
                // diagnostic is synthetic with a note naming the
                // unreadable path.
                syntheticError(DiagnosticCode.E2003,
                    "Cannot read module: " + sourcePath + " ("
                        + e.getMessage() + ")", sourcePath,
                    "missing anchor: unreadable module path '"
                        + sourcePath + "'");
                continue;
            }

            LexResult lex = new Lexer(source, sourcePath).tokenize();
            diagnostics.addAll(lex.diagnostics());
            if (hasLexErrors(lex)) {
                hasErrors = true;
                continue;
            }

            // Phase-0 parsing is profile-aware (signed-int32 foundation
            // I1): under DEAL_V1_2_INT32 the E1036 int32 gate and the
            // -2147483648 immediate-token special case apply; the legacy
            // parse contract is unchanged otherwise. The lexer's
            // directive events flow in through the events-carrying
            // constructor (fixed-name-directive-events D1), so
            // file-directive evaluation and declaration binding run
            // exactly as in production.
            Parser parser = new Parser(lex.tokens(), sourcePath,
                invocation.semanticProfile(), lex.directiveEvents());
            ParseResult parseResult = parser.parse();
            diagnostics.addAll(parseResult.diagnostics());
            if (parseResult.hasErrors()) {
                hasErrors = true;
            }

            // Post-parse v1.2 module shape validation: imports precede all
            // non-import declarations, top level holds only
            // import/function/class/export, imports and exports are not
            // nested statements, and implementation files have no bodyless
            // (external) function declarations.
            List<CompilerDiagnostic> shapeDiags =
                ModuleShapeValidator.validate(parseResult.program(), sourcePath, isDecl);
            diagnostics.addAll(shapeDiags);
            if (shapeDiags.stream().anyMatch(d -> "error".equals(d.severity()))) {
                hasErrors = true;
            }

            // The internal module name derives from the T5/T6
            // classification: the dotted root-relative path for a
            // ProjectModule, the externals raw specifier with '/' → '.',
            // the pinned stdlib module name, and the private
            // deploymentModuleId for an unclassified source (the lossy
            // computeModulePath dotted fallbacks are retired).
            ModuleInfo info = new ModuleInfo(sourcePath,
                modulePathFor(location), isDecl, location);
            info.rawAst = parseResult.program();
            info.parseResult = parseResult;
            modules.put(sourcePath, info);

            // T7 class-declaration gate (rule (d)): a class in a source
            // with no public module identity — an out-of-root relative
            // source, a rooted non-externals .d.deal, or a non-spec
            // .d.deal inside the std directory — is E2010 at the class
            // name span unconditionally at the declaration, before any
            // class/export/default/FFI metadata or artifact is
            // published. Run only for a cleanly parsed module so partial
            // ASTs never fabricate gates.
            if (!parseResult.hasErrors() && parseResult.program() != null) {
                for (StatementNode stmt : parseResult.program().statements()) {
                    ClassDeclaration cd = classDeclarationOf(stmt);
                    if (cd == null) {
                        continue;
                    }
                    ModuleIdentityAssembly.DeclarationResult gate =
                        identityAssembly.gateClassDeclaration(location,
                            cd.name(), classSpanOf(cd, sourcePath));
                    if (gate instanceof ModuleIdentityAssembly.DeclarationResult.Failure f) {
                        diagnostics.add(f.diagnostic());
                        hasErrors = true;
                    }
                }
            }

            long modElapsed = System.currentTimeMillis() - modStart;
            log("  Parsed: " + sourcePath + " (" + modElapsed + "ms)");

            // Process imports for discovery through the T6 resolver's
            // pinned rules (importer-relative first, externals authority,
            // configured roots then the pinned stdlib surface, the
            // 6-module filter, file-keyed E2009; no CWD fallback). A
            // failed resolution merges its E2003/E2009 at the import
            // span and fails the compile; a resolved source queues its
            // lexical path and publishes its location once.
            for (StatementNode stmt : parseResult.program().statements()) {
                if (stmt instanceof ImportDeclaration imp) {
                    SourceModuleResolver.ResolveResult result =
                        sourceResolver.resolve(info.sourcePath,
                            imp.modulePath(), imp.span());
                    if (result instanceof SourceModuleResolver.ResolveResult.Resolved r) {
                        String target = r.location().normalizedSourcePath();
                        locations.putIfAbsent(target, r.location());
                        if (!modules.containsKey(target)) {
                            pending.add(target);
                        }
                    } else {
                        diagnostics.add(
                            ((SourceModuleResolver.ResolveResult.Failure) result)
                                .diagnostic());
                        hasErrors = true;
                    }
                }
            }
        }

        long phaseElapsed = System.currentTimeMillis() - phaseStart;
        if (verbose) {
            System.out.println("  Phase 0 total: " + phaseElapsed + "ms");
        }
    }

    /**
     * The class declaration of a top-level statement, direct or
     * exported (v1.2 module top level holds only
     * import/function/class/export).
     */
    private static ClassDeclaration classDeclarationOf(StatementNode stmt) {
        if (stmt instanceof ClassDeclaration cd) {
            return cd;
        }
        if (stmt instanceof ExportDeclaration ed
                && ed.declaration() instanceof ClassDeclaration cd) {
            return cd;
        }
        return null;
    }

    /**
     * The pinned class-name anchor of a class declaration: the
     * declaration's span (the convention of E4006's class diagnostics),
     * or the canonical synthetic span for a declaration without one.
     */
    private static Span classSpanOf(ClassDeclaration cd, String sourcePath) {
        return cd.span() != null ? cd.span() : Span.synthetic(sourcePath);
    }

    /**
     * The internal module name of a published source location, derived
     * from its T5/T6 classification (never the lossy
     * {@code computeModulePath} dotted path): {@code std.<module>} for a
     * {@code BuiltinModule} source (pinned module order), the externals
     * raw import specifier with {@code /} → {@code .} for an
     * {@code ExternalModule} source (the legacy externalsModulePaths
     * behavior), the dotted root-relative path (suffix stripped) for a
     * {@code ProjectModule} source, and the private
     * {@code deploymentModuleId} for an unclassified source.
     */
    private String modulePathFor(SourceModuleLocation location) {
        CanonicalModuleIdentity classification = location.moduleClassification();
        if (classification instanceof CanonicalModuleIdentity.BuiltinModule) {
            String stem = stdlibModuleStemOf(location);
            if (stem != null) {
                return "std." + stem;
            }
        } else if (classification instanceof CanonicalModuleIdentity.ExternalModule external) {
            return external.rawImportSpecifier().replace('/', '.');
        } else if (classification instanceof CanonicalModuleIdentity.ProjectModule project) {
            Path rootPath = Path.of(
                project.projectIdentity().normalizedRootPath());
            Path sourcePath = Path.of(location.normalizedSourcePath());
            String relative = rootPath.relativize(sourcePath).toString();
            return stripSourceSuffix(relative).replace('/', '.')
                .replace('\\', '.');
        }
        return location.deploymentModuleId();
    }

    /**
     * The stdlib module stem ({@code console}...{@code time}) of a
     * {@code BuiltinModule} source: derived from the canonical resolved
     * file's stem, restricted to the six pinned names (a partial
     * surface — e.g. a test-only surface holding a subset of the six
     * files — keeps the stem-to-name mapping exact; a positional list
     * index would misname partial surfaces).
     */
    private String stdlibModuleStemOf(SourceModuleLocation location) {
        Path canonicalPath = canonicalPathOf(location);
        if (canonicalPath == null || canonicalPath.getFileName() == null) {
            return null;
        }
        String name = canonicalPath.getFileName().toString();
        if (!name.endsWith(".d.deal")) {
            return null;
        }
        String stem = name.substring(0, name.length() - ".d.deal".length());
        return ModuleIdentityResolver.SPEC_STDLIB_MODULE_NAMES.contains(stem)
            ? stem : null;
    }

    /**
     * The lexical absolute path of a canonical resolved-source URI
     * (no filesystem access), or null for a non-{@code file:} URI.
     */
    private static Path canonicalPathOf(SourceModuleLocation location) {
        try {
            Path path = Path.of(URI.create(
                location.semanticModuleIdentity().canonicalResolvedSourceUri()));
            return path.normalize();
        } catch (IllegalArgumentException e) {
            return null;
        }
    }

    /**
     * Strips the {@code .deal}/{@code .d.deal} source suffix of one
     * relative path text.
     */
    private static String stripSourceSuffix(String path) {
        if (path.endsWith(".d.deal")) {
            return path.substring(0, path.length() - ".d.deal".length());
        }
        if (path.endsWith(".deal")) {
            return path.substring(0, path.length() - ".deal".length());
        }
        return path;
    }

    private boolean hasLexErrors(LexResult lex) {
        return lex.diagnostics().stream().anyMatch(d -> "error".equals(d.severity()));
    }

    // =========================================================================
    // Phase 1: Signature extraction
    // =========================================================================

    private void extractSignatures() {
        long phaseStart = System.currentTimeMillis();

        for (ModuleInfo info : modules.values()) {
            long modStart = System.currentTimeMillis();

            // Build import alias → module path mapping for qualified type
            // resolution in export signatures (e.g., V.Vec → "cc_class".Vec).
            Map<String, String> importAliasMap = new HashMap<>();
            if (info.rawAst != null) {
                for (StatementNode stmt : info.rawAst.statements()) {
                    if (stmt instanceof ImportDeclaration imp) {
                        String resolvedSource = resolveImportPath(
                            imp.modulePath(), Path.of(info.sourcePath),
                            imp.span());
                        if (resolvedSource != null) {
                            ModuleInfo imported = modules.get(resolvedSource);
                            if (imported != null) {
                                importAliasMap.put(imp.alias(), imported.modulePath);
                            }
                        }
                    }
                }
            }

            ExportExtractor extractor = new ExportExtractor(info.modulePath,
                info.isDeclarationFile, modulePathClassification()::get);
            extractor.setImportModulePaths(importAliasMap);
            info.exports = extractor.extract(info.rawAst);
            List<CompilerDiagnostic> exportDiags = extractor.diagnostics();
            diagnostics.addAll(exportDiags);
            if (exportDiags.stream().anyMatch(
                    d -> "error".equals(d.severity()))) {
                hasErrors = true;
            }

            // T7 required-identity routing (D6 (a)/(b)/(c)): every class
            // declaration — exported or not — requires its public class
            // identity here. The LuaJIT backend emits a class tag (and
            // therefore the canonical descriptor projection) for every
            // class declaration in an emitted module, and an
            // unrepresentable identity must fail E2010 at the class name
            // span before any metadata or artifact is published — never
            // escape as a backend-dependent raw exception at descriptor
            // emission (the JVM backend compiles a non-exported class
            // without a tag, so gating every class makes the behavior
            // backend-independent). The assembled identity is registered
            // in the compilation's CanonicalClassIdentityIndex; an
            // unrepresentable identity (reserved first root component,
            // forbidden characters, ambiguous containment, an
            // unrepresentable externals specifier, a builtin class other
            // than Error) is E2010 at the class name span. The
            // unconditional identity-less rule (d) already fired in
            // phase 0, whose failure aborts the compile before this
            // phase runs, so an identity-less source is never re-gated
            // here.
            if (info.rawAst != null) {
                for (StatementNode stmt : info.rawAst.statements()) {
                    ClassDeclaration cd = classDeclarationOf(stmt);
                    if (cd == null) {
                        continue;
                    }
                    ModuleIdentityAssembly.ClassIdentityResult required =
                        identityAssembly.requireClassIdentity(info.location,
                            cd.name(), classSpanOf(cd, info.sourcePath));
                    if (required instanceof ModuleIdentityAssembly.ClassIdentityResult.Failure f) {
                        diagnostics.add(f.diagnostic());
                        hasErrors = true;
                    }
                }
            }

            // IR dump for declaration files
            if (dumpIr && info.isDeclarationFile && info.rawAst != null) {
                try {
                    String irText = IrDumper.dump(info.rawAst, info.symbolTable,
                        info.modulePath, buildCanonicalIdentitySurface());
                    if (!irText.isEmpty()) {
                        writeIrDump(info.modulePath, irText);
                    }
                } catch (Exception e) {
                    // Anchorless site (D5/D6): an IR-dump failure has no
                    // source construct anchor; the note names the failed
                    // module path.
                    diagnostics.add(e6001IrDumpFailure(info.sourcePath,
                        e.getMessage()));
                    hasErrors = true;
                }
            }

            long modElapsed = System.currentTimeMillis() - modStart;
            log("  Signatures extracted: " + info.sourcePath + " (" + modElapsed + "ms)");
        }

        long phaseElapsed = System.currentTimeMillis() - phaseStart;
        if (verbose) {
            System.out.println("  Phase 1 total: " + phaseElapsed + "ms");
        }
    }

    /**
     * DEAL v1.2 selected-entry rule: when a compiler invocation selects an
     * entry module, that module must export {@code main} with non-async
     * signature {@code (): null}; the backend invokes {@code main()} from
     * that module.
     *
     * <p>Emitted diagnostics (ISSUE-0269 D7 re-registration):</p>
     * <ul>
     *   <li>{@code E2012} — the entry module does not export {@code main}</li>
     *   <li>{@code E2011} — {@code main} exists but is async or does not
     *       have signature {@code (): null}</li>
     * </ul>
     */
    private void validateEntryMain() {
        ModuleInfo entry = modules.get(entryFile.toString());
        if (entry == null) return; // discovery already reported E2003

        String file = entry.sourcePath;
        // E2012/E2011 anchor at the entry program span (D5): SOURCE-exact
        // at the program start via the T2 program-span obligation,
        // including the empty/whitespace-only entry case
        // (file,1,1,1,1,0,0,0,SOURCE).
        Span programSpan = entry.rawAst != null ? entry.rawAst.span() : null;

        Type mainType = entry.exports != null
            ? entry.exports.get("main") : null;
        if (mainType == null) {
            if (programSpan != null) {
                error(DiagnosticCode.E2012,
                    "Entry module must export 'main' with non-async signature '(): null'",
                    programSpan);
            } else {
                syntheticError(DiagnosticCode.E2012,
                    "Entry module must export 'main' with non-async signature '(): null'",
                    file,
                    "missing anchor: entry program span for module '" + file + "'");
            }
            return;
        }

        boolean validMain = mainType instanceof Type.Func f
            && f.paramTypes().isEmpty()
            && !f.isAsync()
            && f.returnType() instanceof Type.Null;
        if (!validMain) {
            if (programSpan != null) {
                error(DiagnosticCode.E2011,
                    "Entry module 'main' must have non-async signature '(): null'",
                    programSpan);
            } else {
                syntheticError(DiagnosticCode.E2011,
                    "Entry module 'main' must have non-async signature '(): null'",
                    file,
                    "missing anchor: entry program span for module '" + file + "'");
            }
        }
    }

    // =========================================================================
    // Phase 2: Dependency graph and topological ordering
    // ... (unchanged)
    // =========================================================================

    /**
     * Phase-2 module ordering for type checking: the one shared
     * initialization-order algorithm over the import-declaration edge
     * structure ({@link ModuleDependencyGraph#initializationOrder} —
     * Kahn in module discovery order; when no module is ready, exactly
     * the remaining cycle members are appended in discovery order and
     * the sweep resumes, so an importer never precedes its imported
     * module). Every import cycle orders here: type-only cycles are
     * legal and impose no order, and runtime-cycle rejection moved to
     * the post-checking dependency graph phase (ISSUE-0543) — the
     * digest-free SCC pass over the merged ordinary + default runtime
     * edges, where the resolved semantic resource identities and the
     * planner's default edges exist.
     */
    private List<String> buildCheckOrder() {
        Map<String, Set<String>> deps = new LinkedHashMap<>();
        for (Map.Entry<String, ModuleInfo> entry : modules.entrySet()) {
            String sourcePath = entry.getKey();
            ModuleInfo info = entry.getValue();
            Set<String> imports = new LinkedHashSet<>();
            for (StatementNode stmt : info.rawAst.statements()) {
                if (stmt instanceof ImportDeclaration imp) {
                    String resolved = resolveImportPath(imp.modulePath(),
                        Path.of(sourcePath), imp.span());
                    if (resolved != null && modules.containsKey(resolved)) {
                        imports.add(resolved);
                    }
                }
            }
            deps.put(sourcePath, imports);
        }
        return ModuleDependencyGraph.initializationOrder(
            new ArrayList<>(modules.keySet()), deps);
    }

    /**
     * Builds the E2005 runtime-cycle diagnostic with the D5 anchor chain
     * (public static so the fallback chain is directly pinnable; the
     * graph epic, ISSUE-0543, is the production owner of this helper —
     * {@link ModuleDependencyGraph} builds the per-runtime-SCC E2005
     * diagnostics with the per-edge notes through it):
     * <ul>
     *   <li>the import declaration span of the first cycle module that
     *       targets another cycle member,</li>
     *   <li>falling back to that module's program span,</li>
     *   <li>then to the canonical synthetic shape
     *       {@code (file,1,1,1,1,0,0,0,SYNTHETIC)} plus an anchor note
     *       naming the cycle edge
     *       ({@code missing anchor: import declaration closing the module
     *       cycle a -> b -> a}) (D5/D6).</li>
     * </ul>
     */
    public static CompilerDiagnostic e2005Diagnostic(List<String> cycle,
            Map<String, Map<String, Span>> edgeSpans,
            Map<String, Span> programSpans, String message) {
        Set<String> cycleSet = new LinkedHashSet<>(cycle);
        // The chain applies to the first cycle module that targets
        // another cycle member: its import declaration span, falling back
        // to that module's program span. Modules without a cycle-member
        // edge are skipped entirely; when no module has a usable anchor,
        // the result is the canonical synthetic shape plus the
        // cycle-edge-naming note.
        Span anchor = null;
        for (String sourcePath : cycle) {
            boolean targetsCycleMember = false;
            Span edgeSpan = null;
            Map<String, Span> edges = edgeSpans.get(sourcePath);
            if (edges != null) {
                for (Map.Entry<String, Span> edge : edges.entrySet()) {
                    if (cycleSet.contains(edge.getKey())) {
                        targetsCycleMember = true;
                        if (edge.getValue() != null) {
                            edgeSpan = edge.getValue();
                            break;
                        }
                    }
                }
            }
            if (!targetsCycleMember) {
                continue;
            }
            anchor = edgeSpan != null ? edgeSpan : programSpans.get(sourcePath);
            break;
        }
        if (anchor != null) {
            return CompilerDiagnostic.error(DiagnosticCode.E2005, message,
                anchor);
        }
        String file = cycle.isEmpty() ? "" : cycle.get(0);
        return CompilerDiagnostic.syntheticError(DiagnosticCode.E2005, message,
            file,
            "missing anchor: import declaration closing the module cycle "
                + String.join(" -> ", cycle));
    }

    /**
     * Builds the E6001 IR-dump-failure diagnostic (public static so the
     * synthetic contract is directly pinnable): an IR-dump failure has no
     * source construct anchor, so the diagnostic carries the canonical
     * synthetic shape {@code (file,1,1,1,1,0,0,0,SYNTHETIC)} plus an
     * anchor note naming the failed module path (D5/D6).
     */
    public static CompilerDiagnostic e6001IrDumpFailure(String sourcePath,
                                                         String failureMessage) {
        return CompilerDiagnostic.syntheticError(DiagnosticCode.E6001,
            "IR dump failed for " + sourcePath + ": " + failureMessage,
            sourcePath,
            "missing anchor: IR dump path for module '" + sourcePath + "'");
    }

    // =========================================================================
    // Phase 3.5: Checked project and interface index (foundation, ISSUE-0288)
    // =========================================================================

    /**
     * Runs the checked-project foundation after phase 3: packages the
     * orchestrator's module facts in {@code buildCheckOrder} (source
     * paths, dotted module paths, ASTs, Phase-3-corrected export maps,
     * checked facts, the spec-stdlib classification, and the resolved
     * imports) and hands them to {@link CheckedProjectBuilder}. Builder
     * E6005 diagnostics merge into {@link #diagnostics()} and fail the
     * compile; a failed build leaves {@link #checkedProject()} null.
     */
    private void buildCheckedProject(List<String> checkOrder) {
        List<ModuleFact> facts = new ArrayList<>(checkOrder.size());
        for (String sourcePath : checkOrder) {
            ModuleInfo info = modules.get(sourcePath);
            if (info == null) {
                continue; // defensive: buildCheckOrder names only discovered modules
            }
            facts.add(toModuleFact(info));
        }
        ModuleInfo entryInfo = modules.get(entryFile.toString());
        if (entryInfo == null) {
            return; // defensive: phase 3 gates the entry module earlier
        }
        CheckedProjectBuildResult result = CheckedProjectBuilder.build(
            invocation, new ModuleId(entryInfo.modulePath), facts);
        this.checkedProjectBuild = result;
        diagnostics.addAll(result.diagnostics());
        if (result.hasErrors()) {
            hasErrors = true;
            log("  Checked project build failed: " + result.diagnostics());
        }
    }

    /**
     * Runs the requirement-manifest foundation after the checked project
     * and interface index (ISSUE-0289): hands the checked project and the
     * index to {@link LoweringSupport}, which computes one manifest per
     * implementation module in dependency order — the closed capability
     * claims (the superseded four-part {@code STDLIB_TIME_CONFLICT}
     * detector is retired since K7: the cataloged-call arm claims
     * {@code STDLIB_SEMANTICS}) and the reachable-construct coverage
     * rows. Support E6005 diagnostics merge into
     * {@link #diagnostics()} and fail the compile; a failed computation
     * leaves {@link #requirementManifests()} null.
     */
    private void computeRequirementManifests() {
        CheckedProjectBuildResult checked = this.checkedProjectBuild;
        if (checked == null || checked.hasErrors()) {
            return; // a pre-manifest phase failure already gates the compile
        }
        RequirementManifestResult result = LoweringSupport.computeManifests(
            invocation, checked.input(), checked.index());
        this.requirementManifests = result;
        diagnostics.addAll(result.diagnostics());
        if (result.hasErrors()) {
            hasErrors = true;
            log("  Requirement manifest computation failed: " + result.diagnostics());
        }
    }
    /**
     * Runs the route-plan foundation after the manifests (ISSUE-0290):
     * hands the checked project, the interface index, the manifests, the
     * capability registry the invocation recorded, and the compile's
     * target to {@link MigrationPlanner} — one deterministic plan per
     * target over the closed routing rules (F4). The planner's F1/F7
     * guard requires the registry digest to equal the invocation's
     * recorded digest, so the registry is resolved from the invocation:
     * the promoted release registry (E12's committed derivation — the
     * production route set, F4 rule 4 eligible for promoted
     * capability × target pairs) or the all-{@code SHADOW} release
     * default (the internal harnesses' recorded registry — F4 rule 4
     * ineligible, all-LEGACY); any other digest fails the planner guard
     * (a producer-defect wiring defect, never an E6005 class). Planner
     * E6005 diagnostics merge into {@link #diagnostics()} and fail the
     * compile. The JS backend skips the phase: the closed route-plan
     * target axis is {@code LUAJIT|JVM} (foundation F4/F5), and no
     * closed target exists for JS in this epic.
     */
    private void planRoutesForCompile() {
        CheckedProjectBuildResult checked = this.checkedProjectBuild;
        if (checked == null || checked.hasErrors()) {
            return; // a pre-planner phase failure already gates the compile
        }
        if (this.requirementManifests == null || this.requirementManifests.hasErrors()) {
            return; // a pre-planner phase failure already gates the compile
        }
        Target target = switch (this.backend) {
            case LUAJIT -> Target.LUAJIT;
            case JVM -> Target.JVM;
            case JS -> null;
        };
        if (target == null) {
            return; // JS: no closed route-plan target in this epic
        }
        RoutePlanResult result = MigrationPlanner.planRoutes(
            invocation, registryForInvocation(invocation),
            checked.input(), checked.index(),
            this.requirementManifests.manifests(), target, Set.of());
        this.routePlan = result;
        diagnostics.addAll(result.diagnostics());
        if (result.hasErrors()) {
            hasErrors = true;
            log("  Route planning failed: " + result.diagnostics());
        }
    }

    /**
     * Resolves the capability registry the invocation recorded (F1/F7
     * discipline): the promoted release registry when the invocation
     * records its digest (the production path — {@code Main} and
     * {@link #defaultInvocation()}), or the all-{@code SHADOW} release
     * default when the invocation records that digest (the internal
     * harnesses' explicit invocations — lanes, conformance seam,
     * regression purposes). Any other digest leaves the invocation's own
     * mismatch for the planner's defensive guard, which rejects it as a
     * producer-defect wiring error.
     */
    private static CapabilityRegistry registryForInvocation(
            CompilerInvocation invocation) {
        String recorded = invocation.capabilityRegistryHash();
        CapabilityRegistry release = ReleaseConfiguration.releaseCapabilityRegistry();
        if (release.capabilityRegistryHash().equals(recorded)) {
            return release;
        }
        CapabilityRegistry releaseDefault = CapabilityRegistry.releaseRegistry();
        if (releaseDefault.capabilityRegistryHash().equals(recorded)) {
            return releaseDefault;
        }
        return release;
    }

    // =========================================================================
    // Phase 3.8: C FFI declaration validation and metadata (ISSUE-0162)
    // =========================================================================

    /**
     * The read-only view of the validated extern-C metadata: dotted
     * module path &rarr; generated module inputs (descriptor, cdef
     * bundle, retained plans, forward bindings). Populated only for the
     * LuaJIT backend after successful validation; empty for JVM/JS and
     * on any validation failure.
     *
     * @return the generated FFI modules (unmodifiable)
     */
    public Map<String, FfiGeneratedModule> ffiGenerations() {
        return Collections.unmodifiableMap(ffiGenerations);
    }

    /**
     * The extern-C metadata phase: runs after semantic/graph success
     * (phases 0–3.7) and before any artifact write (phase 4).
     *
     * <p>Per extern-C declaration module in the graph:</p>
     * <ol>
     *   <li>validate the declaration policy (E7002: sync functions,
     *       export/C names, ABI parameter/return allowlists, same-file
     *       class references, required/defaulted source-order struct
     *       fields, pointer emptiness/non-constructibility) — never
     *       evaluating defaults;</li>
     *   <li>on an incapable backend (JVM) emit E6006 containing
     *       {@code FFI_UNSUPPORTED_BACKEND} at the {@code @extern-c}
     *       directive range after validation and before artifacts;</li>
     *   <li>on LuaJIT publish the validated immutable descriptor plus
     *       the generated cdef bundle, retained plans, and forward
     *       bindings for later runtime loading.</li>
     * </ol>
     *
     * <p>A failed validation or an incapable backend publishes no
     * metadata and no partial artifact (the compile stops before phase
     * 4). The JS backend keeps its pinned import-site E6006 arm
     * (ISSUE-0169 skeleton) and does not run this phase.</p>
     */
    // =========================================================================
    // Phase 3.8: Default planning and declaration default analysis (ISSUE-0541)
    // =========================================================================

    /**
     * Runs the shared default planning pipeline over every plan-bearing
     * module in dependency order: implementation modules through
     * {@link DefaultSemanticPlanner}, extern-C declaration modules
     * through {@link DeclarationSemanticAnalyzer}. Host-declared
     * (non-extern-C declaration) classes are exempt and produce no
     * plan. Error-level diagnostics fail the compile and publish no
     * plan; success stores the plans and their provisional occurrence
     * data in {@link #plannedDefaultClasses()} only — nothing is
     * published to lowerers, the FFI descriptor stage, or artifacts
     * (the graph epic owns publication), no digest is computed, no
     * evaluator is invoked, and no library is loaded.
     */
    private void planDefaultClasses() {
        // The planning epics require public class identity for every
        // plan-bearing class and the canonical descriptor encoder
        // resolves class atoms through the assembly index: register the
        // intrinsic Error projection and every class declaration of
        // every implementation module (phase 1 registered the
        // top-level classes; nested classes join idempotently here)
        // before any entry encodes a descriptor.
        identityAssembly.intrinsicErrorIdentity();
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile || info.checkResult == null) {
                continue;
            }
            for (Map.Entry<ClassDeclaration, SymbolTable> entry
                    : info.checkResult.classScopes().entrySet()) {
                ModuleIdentityAssembly.ClassIdentityResult required =
                    identityAssembly.requireClassIdentity(info.location,
                        entry.getKey().name(), entry.getKey().span());
                if (required
                        instanceof ModuleIdentityAssembly.ClassIdentityResult
                            .Failure f) {
                    diagnostics.add(f.diagnostic());
                    hasErrors = true;
                }
            }
        }
        if (hasErrors) {
            return;
        }

        CanonicalRuntimeTypeDescriptor descriptors =
            new CanonicalRuntimeTypeDescriptor(identityAssembly.index());
        Map<String, CanonicalModuleIdentity> classification =
            modulePathClassification();
        ModuleResolverImpl moduleResolver = new ModuleResolverImpl(modules,
            diagnostics);

        for (String sourcePath : dependencyOrder) {
            ModuleInfo info = modules.get(sourcePath);
            if (info == null || info.rawAst == null
                    || info.location == null) {
                continue;
            }
            Map<String, DefaultPlanImport> imports =
                defaultPlanImportsOf(info);
            if (info.isDeclarationFile) {
                if (!isExternCModuleInfo(info)) {
                    // Host-declared classes are exempt from the plan
                    // gates and produce no plan (the host supplies
                    // <C>_defaults at load).
                    continue;
                }
                DefaultDeclarationModuleInput input =
                    new DefaultDeclarationModuleInput(
                        info.sourcePath, info.modulePath, info.rawAst,
                        info.location, imports, descriptors,
                        moduleResolver, classification);
                DeclarationSemanticAnalyzer.Result result =
                    DeclarationSemanticAnalyzer.analyze(input,
                        identityAssembly);
                diagnostics.addAll(result.diagnostics());
                if (result.hasErrors()) {
                    hasErrors = true;
                } else {
                    plannedDefaultClasses.put(info.sourcePath,
                        result.plannedClasses());
                }
                continue;
            }
            if (info.checkResult == null || info.nameResolver == null) {
                continue; // defensive: checked facts always exist here
            }
            DefaultPlanModuleInput input = new DefaultPlanModuleInput(
                info.sourcePath, info.modulePath, info.rawAst,
                info.location, info.checkResult, info.nameResolver,
                imports, descriptors, classification);
            DefaultSemanticPlanner.Result result =
                DefaultSemanticPlanner.plan(input, identityAssembly);
            diagnostics.addAll(result.diagnostics());
            if (result.hasErrors()) {
                hasErrors = true;
            } else {
                plannedDefaultClasses.put(info.sourcePath,
                    result.plannedClasses());
            }
        }
    }

    /**
     * The import surface of one module: import alias &rarr; the
     * provider's read-only planning snapshot (source path, dotted
     * module path, parsed program, resolved location, extracted export
     * map, symbol table when available, and the declaration/extern-C
     * flags), insertion-ordered by the module's import declarations.
     */
    private Map<String, DefaultPlanImport> defaultPlanImportsOf(
            ModuleInfo info) {
        Map<String, DefaultPlanImport> imports = new LinkedHashMap<>();
        if (info.rawAst == null) {
            return imports;
        }
        for (StatementNode stmt : info.rawAst.statements()) {
            if (!(stmt instanceof ImportDeclaration imp)) {
                continue;
            }
            String resolvedSource = resolveImportPath(imp.modulePath(),
                Path.of(info.sourcePath), imp.span());
            if (resolvedSource == null) {
                continue; // the E2003/E2009 was already reported
            }
            ModuleInfo imported = modules.get(resolvedSource);
            if (imported == null || imported.rawAst == null
                    || imported.location == null) {
                continue;
            }
            imports.put(imp.alias(), new DefaultPlanImport(
                imported.sourcePath, imported.modulePath, imported.rawAst,
                imported.location,
                imported.exports != null ? imported.exports : Map.of(),
                imported.symbolTable, imported.isDeclarationFile,
                isExternCModuleInfo(imported)));
        }
        return imports;
    }

    /**
     * The planning result of the current compile: module source path
     * &rarr; the planned classes with their provisional occurrence
     * data, in planning order. Read-only; empty before the planning
     * phase runs, when a preceding phase failed, when planning
     * produced error-level diagnostics, or when the dependency graph
     * rejected the compilation (E2005 publishes no plan — the
     * provisional plans are discarded).
     */
    public Map<String, List<PlannedDefaultClass>> plannedDefaultClasses() {
        return Collections.unmodifiableMap(plannedDefaultClasses);
    }

    /**
     * The dependency graph's published completed plans of this compile
     * (ISSUE-0543): module source path &rarr; the planned classes with
     * every plan's {@code runtimeDependencies} completed with the final
     * digest-bearing records and the serializer-completed entry content
     * preserved, in planning order. Read-only; empty before the graph
     * phase runs, when a preceding phase failed, or when the graph
     * rejected the compilation (E2005 publishes no plan).
     */
    public Map<String, List<PlannedDefaultClass>> completedDefaultPlans() {
        return Collections.unmodifiableMap(completedDefaultPlans);
    }

    /**
     * The LuaJIT codegen results keyed by module source path (the
     * {@link #jvmGeneratedResults()} accessor's Lua mirror, ISSUE-0544):
     * each entry carries the backend's realized runtime default plans
     * for the module. Read-only; empty before the LuaJIT codegen phase.
     */
    public Map<String, LuaBackend.GenerationResult>
            luaGeneratedResults() {
        return Collections.unmodifiableMap(luaGeneratedResults);
    }

    /**
     * The JS codegen results keyed by module source path (the
     * {@link #jvmGeneratedResults()} accessor's JS mirror, ISSUE-0544):
     * each entry carries the backend's realized runtime default plans
     * for the module. Read-only; empty before the JS codegen phase.
     */
    public Map<String, JsBackend.JsCodegenResult> jsGeneratedResults() {
        return Collections.unmodifiableMap(jsGeneratedResults);
    }

    /**
     * The completed default plans of this compile keyed by module path
     * (ISSUE-0544, the lowering epic's backend seam): module path
     * &rarr; the module's completed {@link PlannedDefaultClass} list in
     * planning order. Built from {@link #completedDefaultPlans()} (keyed
     * by module source path) so the three backends consume one uniform
     * plan surface — each backend keys its own module's plans by its
     * module path and the JVM backend additionally resolves imported
     * providers' plans through the imported module paths. Empty before
     * the graph phase succeeds or when it published no plan.
     */
    public Map<String, List<PlannedDefaultClass>>
            completedPlansByModulePath() {
        Map<String, List<PlannedDefaultClass>> byModulePath =
            new LinkedHashMap<>();
        for (ModuleInfo info : modules.values()) {
            List<PlannedDefaultClass> plans =
                completedDefaultPlans.get(info.sourcePath);
            if (plans != null && !plans.isEmpty()) {
                byModulePath.put(info.modulePath, plans);
            }
        }
        return Collections.unmodifiableMap(byModulePath);
    }

    /**
     * The merged final digest-bearing runtime dependency records of
     * this compile (ISSUE-0543): ordinary {@code RUNTIME_USE} records
     * in first-occurrence order followed by the per-plan
     * {@code DEFERRED_DEFAULT_BINDING} records, structurally
     * deduplicated. Read-only; empty before the graph phase runs or
     * when the graph rejected the compilation.
     */
    public List<RuntimeImportDependency> runtimeDependencies() {
        return List.copyOf(runtimeDependencies);
    }

    /**
     * The initialization order of this compile (ISSUE-0543): module
     * source paths in dependency order preserving first-import
     * declaration order — the one shared ordering algorithm of
     * {@link ModuleDependencyGraph#initializationOrder} (the phase-2
     * check order derives from it, and the graph phase republishes the
     * identical order after success). Read-only; empty before phase 2.
     */
    public List<String> dependencyOrder() {
        return List.copyOf(dependencyOrder);
    }

    /**
     * The canonical serializer input surface of this compile
     * (ISSUE-0542): module source path &rarr; the read-only per-module
     * facts {@link DefaultSemanticSerializer} consumes alongside
     * {@link #plannedDefaultClasses()} — checked facts and the name
     * resolver for implementation modules, the module resolver and the
     * export map for declaration modules, the import surface, the
     * canonical descriptor encoder, and the module-identity
     * classification. Read-only; a data seam only — this epic wires
     * no serializer phase: the graph epic (ISSUE-0543) owns the
     * orchestrator phase that invokes the serializer after its
     * digest-free SCC pass. No digest is computed, no graph runs, and
     * nothing is published here.
     */
    public Map<String, DefaultSerializerModuleInput>
            defaultSerializerModuleInputs() {
        Map<String, DefaultSerializerModuleInput> inputs =
            new LinkedHashMap<>();
        if (identityAssembly == null) {
            return Collections.unmodifiableMap(inputs);
        }
        CanonicalRuntimeTypeDescriptor descriptors =
            new CanonicalRuntimeTypeDescriptor(identityAssembly.index());
        Map<String, CanonicalModuleIdentity> classification =
            modulePathClassification();
        ModuleResolverImpl moduleResolver = new ModuleResolverImpl(modules,
            diagnostics);
        for (ModuleInfo info : modules.values()) {
            if (info.rawAst == null || info.location == null) {
                continue;
            }
            // Defensive: the serializer is only invoked after a
            // successful planning phase, so modules whose checked
            // facts never completed (a failed compile) stay outside
            // the seam — the serializer input contract requires the
            // exact declaration/implementation fact split.
            if (!info.isDeclarationFile
                    && (info.checkResult == null
                        || info.nameResolver == null)) {
                continue;
            }
            inputs.put(info.sourcePath, new DefaultSerializerModuleInput(
                info.sourcePath, info.modulePath, info.rawAst,
                info.location,
                info.isDeclarationFile ? null : info.checkResult,
                info.isDeclarationFile ? null : info.nameResolver,
                defaultPlanImportsOf(info),
                info.exports != null ? info.exports : Map.of(),
                descriptors, classification,
                info.isDeclarationFile ? moduleResolver : null,
                info.isDeclarationFile, isExternCModuleInfo(info)));
        }
        return Collections.unmodifiableMap(inputs);
    }

    /**
     * Phase 3.85 (ISSUE-0543, design source
     * {@code provider-versioned-default-plans} D1/D7/D8): the runtime
     * dependency graph and plan publication — the digest-free SCC
     * pass merges the ordinary runtime-use edges ({@code RUNTIME_USE},
     * the complete typed evaluator IR walk of every function body)
     * with the planner's default edges
     * ({@code DEFERRED_DEFAULT_BINDING}) over the one
     * {@link RuntimeImportDependency} carrier; a strongly connected
     * component containing at least one runtime edge reports E2005
     * with a note per runtime edge carrying
     * {@code (reason, from &rarr; to, sourceRange)} and publishes no
     * plan, FFI metadata, or artifact (the provisional plans are
     * discarded). Only an acyclic pass requests the provider digests —
     * the serializer completes every default's {@code runtimeResources}
     * and additionally demands the ordinary occurrences' provider
     * digests — publishes the final digest-bearing dependency records
     * and the completed plans, and fixes the initialization order. No
     * evaluator is invoked and no library is loaded.
     */
    private void evaluateDependencyGraph() {
        Map<String, ModuleDependencyGraph.ModuleInput> inputs =
            new LinkedHashMap<>();
        for (Map.Entry<String, ModuleInfo> entry : modules.entrySet()) {
            String sourcePath = entry.getKey();
            ModuleInfo info = entry.getValue();
            if (info.rawAst == null || info.location == null) {
                continue;
            }
            if (!info.isDeclarationFile
                    && (info.checkResult == null
                        || info.nameResolver == null)) {
                continue;
            }
            inputs.put(sourcePath, new ModuleDependencyGraph.ModuleInput(
                info.sourcePath, info.modulePath, info.rawAst,
                info.location,
                info.isDeclarationFile ? null : info.checkResult,
                info.isDeclarationFile ? null : info.nameResolver,
                defaultPlanImportsOf(info), modulePathClassification(),
                info.isDeclarationFile));
        }
        // The E2005 anchor chain inputs: each module's import-edge
        // spans and program span.
        Map<String, Map<String, Span>> edgeSpans = new LinkedHashMap<>();
        Map<String, Span> programSpans = new LinkedHashMap<>();
        for (Map.Entry<String, ModuleInfo> entry : modules.entrySet()) {
            String sourcePath = entry.getKey();
            ModuleInfo info = entry.getValue();
            Map<String, Span> spans = new LinkedHashMap<>();
            if (info.rawAst != null) {
                for (StatementNode stmt : info.rawAst.statements()) {
                    if (stmt instanceof ImportDeclaration imp) {
                        String resolved = resolveImportPath(
                            imp.modulePath(), Path.of(sourcePath),
                            imp.span());
                        if (resolved != null
                                && modules.containsKey(resolved)) {
                            spans.put(resolved, imp.span());
                        }
                    }
                }
                if (info.rawAst.span() != null) {
                    programSpans.put(sourcePath, info.rawAst.span());
                }
            }
            edgeSpans.put(sourcePath, spans);
        }

        ModuleDependencyGraph.DigestFreeResult free =
            ModuleDependencyGraph.digestFreePass(inputs,
                plannedDefaultClasses, edgeSpans, programSpans);
        if (free.failed()) {
            // E2005: a runtime SCC — publish no plan, no FFI metadata,
            // and no artifact; the provisional plans are discarded.
            diagnostics.addAll(free.diagnostics());
            hasErrors = true;
            plannedDefaultClasses.clear();
            runtimeDependencies = List.of();
            return;
        }
        // Acyclic: request the provider digests now — the serializer
        // completes every default's runtimeResources and additionally
        // demands the ordinary occurrences' provider digests.
        DefaultSemanticSerializer.Result serialized =
            DefaultSemanticSerializer.serialize(
                defaultSerializerModuleInputs(), plannedDefaultClasses,
                free.ordinaryOccurrences());
        diagnostics.addAll(serialized.diagnostics());
        if (serialized.hasErrors()) {
            hasErrors = true;
            plannedDefaultClasses.clear();
            runtimeDependencies = List.of();
            return;
        }
        ModuleDependencyGraph.PublishedGraph published =
            ModuleDependencyGraph.finalizeGraph(free,
                plannedDefaultClasses, serialized.serializedClasses(),
                serialized.providerDigests());
        completedDefaultPlans.putAll(published.completedPlans());
        runtimeDependencies = published.runtimeDependencies();
        dependencyOrder = free.initializationOrder();
        log("  Runtime graph: " + runtimeDependencies.size()
            + " dependency edge(s); initialization order "
            + dependencyOrder.size() + " module(s)");
    }

    private void validateCffiDeclarations() {
        if (backend == Backend.JS) {
            return;
        }
        // The validator keys graph-order lookups by dotted module path
        // (the import-surface key space), while {@code dependencyOrder}
        // is the phase-2 check order of absolute source paths: translate
        // the order into the validator's key space so every imported
        // reference receives its real dependency-order position instead
        // of a degenerate constant.
        List<String> ffiDependencyOrder = dependencyOrder.stream()
            .map(modules::get)
            .filter(Objects::nonNull)
            .map(info -> info.modulePath)
            .toList();
        CanonicalRuntimeTypeDescriptor descriptorEncoder =
            new CanonicalRuntimeTypeDescriptor(identityAssembly.index());
        for (ModuleInfo info : modules.values()) {
            if (!isExternCModuleInfo(info)) {
                continue;
            }
            String canonicalExternalIdentity = canonicalExternalIdentityOf(info);
            if (canonicalExternalIdentity == null) {
                // Defensive: an extern-C module that is not
                // externals-listed has no native library and no public
                // module identity — the E2010 library/manifest policy
                // belongs to the config epic (ISSUE-0111); this phase
                // publishes no metadata for it.
                continue;
            }
            NativeLibraryRef nativeLibrary = nativeLibraryOf(info);
            FfiDeclarationValidator.Result result =
                FfiDeclarationValidator.validate(
                    info.rawAst, info.modulePath, info.location,
                    canonicalExternalIdentity, identityAssembly,
                    descriptorEncoder,
                    nativeLibrary == null ? null
                        : nativeLibrary.kind().name(),
                    nativeLibrary == null ? null
                        : nativeLibrary.loaderText(),
                    ffiDependencyOrder, importTargetsOf(info));
            diagnostics.addAll(result.diagnostics());
            if (result.hasErrors()) {
                hasErrors = true;
                continue;
            }
            if (backend == Backend.JVM) {
                // Backend capability rejection (D8): after semantic/
                // declaration validation, before any artifact write.
                deal.diagnostics.DiagnosticRange externCRange =
                    info.rawAst.fileDirectives().externCRange();
                diagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6006,
                    "JVM backend: C FFI (@extern-c) declarations are not"
                        + " supported (FFI_UNSUPPORTED_BACKEND)",
                    externCRange != null ? externCRange
                        : deal.diagnostics.DiagnosticRange.synthetic(
                            info.sourcePath)));
                hasErrors = true;
                continue;
            }
            // LuaJIT: the validated descriptor is accepted for later
            // runtime loading; the generator produces the loader inputs
            // (cells before any plan content; imported references in
            // graph order; no evaluator ever invoked).
            LuaFfiBindingGenerator.GeneratedBindings generated =
                LuaFfiBindingGenerator.generate(result.descriptor(),
                    result.importedFunctions(), result.importedClassPlans());
            ffiGenerations.put(info.modulePath, new FfiGeneratedModule(
                info.modulePath, result.descriptor(),
                generated.cdefBundle(), generated.plans(),
                generated.bindings()));
        }
    }

    /** True for a parsed extern-C declaration module. */
    private static boolean isExternCModuleInfo(ModuleInfo info) {
        return info.isDeclarationFile && info.rawAst != null
            && info.rawAst.fileDirectives().externC();
    }

    /**
     * The canonical external module identity text of an externals-listed
     * module ({@code @$external/&lt;rawImportSpecifier&gt;}), or null
     * when the module has no external classification.
     */
    private String canonicalExternalIdentityOf(ModuleInfo info) {
        CanonicalModuleIdentity identity = classifyModuleIdentity(info);
        if (identity instanceof CanonicalModuleIdentity.ExternalModule ext) {
            return "@$external/" + ext.rawImportSpecifier();
        }
        return null;
    }

    /** The externals entry's classified native library, or null. */
    private NativeLibraryRef nativeLibraryOf(ModuleInfo info) {
        CanonicalModuleIdentity identity = classifyModuleIdentity(info);
        if (identity instanceof CanonicalModuleIdentity.ExternalModule ext) {
            ExternalEntry entry = context.externals().get(
                ext.rawImportSpecifier());
            return entry == null ? null : entry.nativeLibrary();
        }
        return null;
    }

    /**
     * The resolved import surface of one module: import alias &rarr;
     * the provider's dotted module path and extracted export map (the
     * extern-C metadata phase resolves default-expression provider
     * references through it).
     */
    private Map<String, FfiDeclarationValidator.ImportTarget> importTargetsOf(
            ModuleInfo info) {
        Map<String, FfiDeclarationValidator.ImportTarget> targets =
            new LinkedHashMap<>();
        if (info.rawAst == null) {
            return targets;
        }
        for (StatementNode stmt : info.rawAst.statements()) {
            if (!(stmt instanceof ImportDeclaration imp)) {
                continue;
            }
            String resolvedSource = resolveImportPath(imp.modulePath(),
                Path.of(info.sourcePath), imp.span());
            if (resolvedSource == null) {
                continue;
            }
            ModuleInfo imported = modules.get(resolvedSource);
            if (imported == null) {
                continue;
            }
            targets.put(imp.alias(), new FfiDeclarationValidator.ImportTarget(
                imported.modulePath,
                imported.exports != null ? imported.exports : Map.of()));
        }
        return targets;
    }


    /**
     * Packages one orchestrator module's read-only facts for the builder:
     * the resolved imports in source order re-run through the same import
     * resolution the discovery/typing phases used ({@code resolveImportPath}
     * plus the externals maps — the try-variant emits no diagnostics; an
     * unresolvable import would have failed the compile with E2003 before
     * this phase).
     */
    private ModuleFact toModuleFact(ModuleInfo info) {
        List<ModuleFact.ImportFact> imports = new ArrayList<>();
        if (info.rawAst != null) {
            for (StatementNode stmt : info.rawAst.statements()) {
                if (stmt instanceof ImportDeclaration imp) {
                    // The same T6 resolution the discovery/typing phases
                    // used, re-run without diagnostics (an unresolvable
                    // import would have failed the compile with
                    // E2003/E2009 before this phase).
                    SourceModuleResolver.ResolveResult result =
                        sourceResolver.resolve(info.sourcePath,
                            imp.modulePath(), imp.span());
                    if (result instanceof SourceModuleResolver.ResolveResult.Resolved r) {
                        imports.add(new ModuleFact.ImportFact(imp.alias(),
                            imp.modulePath(),
                            r.location().normalizedSourcePath()));
                    }
                }
            }
        }
        return new ModuleFact(info.sourcePath, new ModuleId(info.modulePath),
            info.isDeclarationFile, isSpecStdlibModuleInfo(info), info.rawAst,
            info.exports != null ? info.exports : Map.of(),
            info.symbolTable, info.checkResult, imports);
    }

    // =========================================================================
    // Phase 3: Type checking
    // =========================================================================

    private void typeCheckAll(List<String> order) {
        long phaseStart = System.currentTimeMillis();
        ModuleResolverImpl resolver = new ModuleResolverImpl(modules, diagnostics);

        for (String sourcePath : order) {
            ModuleInfo info = modules.get(sourcePath);
            if (info.isDeclarationFile) continue;

            long modStart = System.currentTimeMillis();

            NameResolver nr = new NameResolver(info.modulePath, resolver,
                new HashSet<>(), modulePathClassification()::get);
            info.nameResolver = nr;
            SymbolTable symTable = nr.resolve(info.rawAst);
            info.symbolTable = symTable;

            // F1 fix: Rebuild exports with correctly resolved types from name
            // resolution.  The ExportExtractor in Phase 1 uses import aliases
            // for qualified types (e.g., "V" instead of "cc_class"), which are
            // local to the exporting module and meaningless to downstream
            // importers.  After name resolution, we know the correct module
            // paths and can produce accurate export types.
            Map<String, Type> correctedExports = new LinkedHashMap<>();
            for (StatementNode stmt : info.rawAst.statements()) {
                if (stmt instanceof ExportDeclaration exp) {
                    String exportName = null;
                    if (exp.declaration() instanceof FunctionDeclaration fd) {
                        exportName = fd.name();
                    } else if (exp.declaration() instanceof ClassDeclaration cd) {
                        exportName = cd.name();
                    }
                    if (exportName != null) {
                        Symbol sym = symTable.resolve(exportName);
                        if (sym != null) {
                            if (sym instanceof Symbol.FunctionSymbol fs) {
                                correctedExports.put(exportName, fs.funcType());
                            } else if (sym instanceof Symbol.ClassSymbol cs) {
                                correctedExports.put(exportName,
                                    Types.classType(cs.name(), cs.identity()));
                            }
                        }
                    }
                }
            }

            // D6: Append synthetic C$fromJson and C$toJson exports for @jsonable
            // classes.  These are added after the symbol-table-based correction
            // so that synthetic entries are present in the final export map
            // consumed by downstream modules.
            for (StatementNode stmt : info.rawAst.statements()) {
                if (stmt instanceof ExportDeclaration exp
                        && exp.declaration() instanceof ClassDeclaration cd
                        && cd.isJsonable()) {
                    Symbol clsSym = symTable.resolve(cd.name());
                    if (clsSym instanceof Symbol.ClassSymbol cs) {
                        Type clsType = Types.classType(cs.name(), cs.identity());

                        // C$fromJson: (string) -> C | null
                        Type.Func fromJsonType = new Type.Func(
                            List.of(Type.String.INSTANCE),
                            Types.nullable(clsType));
                        correctedExports.put(cd.name() + "$fromJson", fromJsonType);

                        // C$toJson: (C) -> string
                        Type.Func toJsonType = new Type.Func(
                            List.of(clsType),
                            Type.String.INSTANCE);
                        correctedExports.put(cd.name() + "$toJson", toJsonType);
                    }
                }
            }

            info.exports = correctedExports;

            List<CompilerDiagnostic> nameDiags = nr.diagnostics();
            diagnostics.addAll(nameDiags);
            if (hasNameErrors(nameDiags)) {
                hasErrors = true;
                long modElapsed = System.currentTimeMillis() - modStart;
                log("  Checked: " + sourcePath + " (name resolution error, " + modElapsed + "ms)");
                continue;
            }

            CheckResult result = TypeChecker.check(info.modulePath, symTable,
                nr, info.rawAst);
            info.checkResult = result;
            diagnostics.addAll(result.diagnostics());
            if (result.hasErrors()) {
                hasErrors = true;
            }

            // IR dump for full modules (after type checking, before codegen)
            if (dumpIr && !result.hasErrors() && info.rawAst != null) {
                try {
                    String irText = IrDumper.dump(info.rawAst, result,
                        info.modulePath, buildCanonicalIdentitySurface());
                    if (!irText.isEmpty()) {
                        writeIrDump(info.modulePath, irText);
                    }
                } catch (Exception e) {
                    // Anchorless site (D5/D6): the note names the failed
                    // module path.
                    diagnostics.add(e6001IrDumpFailure(info.sourcePath,
                        e.getMessage()));
                    hasErrors = true;
                }
            }

            long modElapsed = System.currentTimeMillis() - modStart;
            log("  Checked: " + sourcePath + " (" + modElapsed + "ms)");
        }

        long phaseElapsed = System.currentTimeMillis() - phaseStart;
        if (verbose) {
            System.out.println("  Phase 3 total: " + phaseElapsed + "ms");
        }
    }

    private boolean hasNameErrors(List<CompilerDiagnostic> diags) {
        return diags.stream().anyMatch(d -> "error".equals(d.severity()));
    }

    // =========================================================================
    // Phase 4: Code generation
    // =========================================================================

    /**
     * Phase-4 dispatch (ISSUE-0643; design source
     * {@code production-project-emission-and-atomic-cutover} P4/P5):
     * {@link Backend#LUAJIT}/{@link Backend#JVM} with the release-owned
     * production invocation ({@link #productionArmApplies()}) runs the
     * production project emission arm — one lowering, one project
     * artifact, no route plan; every other LuaJIT/JVM invocation runs
     * the unchanged harness arm (phase 3.7 route planning, the
     * per-module route dispatch, the retained loops and counters, the
     * mixed-edge validation, and the per-module production emission);
     * {@link Backend#JS} keeps its untouched pipeline.
     *
     * <p>The dispatch reads no routing, planner, registry,
     * retained-backend, or retained-counter surface itself: those live
     * in the harness arms this method only selects.</p>
     */
    private void codegenAll() throws IOException {
        long phaseStart = System.currentTimeMillis();
        try {
            if (productionArmApplies()) {
                emitProductionProject();
            } else if (backend == Backend.JVM) {
                // JVM use site (ISSUE-0091): emit one .java module class per
                // module. Import resolution and the Lua runtime copies are
                // LuaJIT-specific and skipped here.
                codegenAllJvm();
            } else if (backend == Backend.JS) {
                // JS use site (ISSUE-0247 core slice, js-backend-emitter D3):
                // codegenAllJs() replaces the ISSUE-0189 staging guard with the
                // two-pass emitter plus the runtime/stdlib deployment copies.
                codegenAllJs();
            } else {
                codegenAllLua();
            }
        } catch (IOException stagingFailure) {
            // A staging write failure (D4): nothing is published, the
            // stage tree is removed by compile(), the diagnostics report
            // is unchanged, and the pinned deterministic compiler I/O
            // diagnostic is printed with exit 1.
            stageFailure(stagingFailure);
        }

        long phaseElapsed = System.currentTimeMillis() - phaseStart;
        if (verbose) {
            System.out.println("  Phase 4 total: " + phaseElapsed + "ms");
        }
    }

    /**
     * True exactly for a LuaJIT/JVM compile whose recorded invocation is
     * the release-owned production invocation (P4): the phase-4 dispatch
     * then runs the production arm and skips phase 3.7. The JS arm is
     * separate and untouched.
     */
    private boolean productionArmApplies() {
        if (backend != Backend.LUAJIT && backend != Backend.JVM) {
            return false;
        }
        return isProductionInvocation(invocation);
    }

    /**
     * The identity-based production-invocation predicate (P4; design
     * source {@code production-project-emission-and-atomic-cutover}):
     * true exactly for the record
     * {@code CompilerProfileProvider.resolve(ReleaseConfiguration
     * .CURRENT_RELEASE_STATE, ReleaseConfiguration
     * .releaseCapabilityRegistry())} — the record {@code deal.Main}
     * resolves and {@link #defaultInvocation()} returns. The test is
     * record identity (purpose, semantic profile, release state,
     * capability-registry digest, and the derived release-state hash),
     * never a purpose-only test, so a test-only {@code PUBLIC_BUILD}
     * invocation that records another release state or another registry
     * digest keeps the harness arm.
     *
     * @param invocation the compile's recorded invocation; non-null
     * @return whether the compile is the release-owned production
     *         invocation
     */
    public static boolean isProductionInvocation(CompilerInvocation invocation) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        return invocation.equals(defaultInvocation());
    }

    /**
     * The LuaJIT harness arm of phase 4 (the unchanged per-module route
     * dispatch): the canonical identity surface, the SHARED-routed
     * modules lowered to validated semantic IR and emitted through the
     * shared emitter, the retained backend for every other module, the
     * runtime/stdlib deployment copies, and the mixed-edge validation.
     * No within-run fallback exists: a shared lowering/emission failure
     * fails the compile and publishes nothing.
     */
    private void codegenAllLua() throws IOException {
        // Lua use site (emitter page D1): the LuaJIT emitter consumes
        // the same per-compilation canonical identity surface the JS
        // arm builds — one identity index over the module-path
        // classification plus the intrinsic builtin Error module.
        // Every descriptor the Lua emitter writes resolves through
        // it; the local legacy dialect producer is retired.
        ModuleIdentityResolver.IdentityIndex identityIndex =
            buildCanonicalIdentitySurface();
        // ISSUE-0239 E10 dispatch: the ModuleRoutePlan selects the
        // emitter per module — SHARED-routed modules lower to
        // validated semantic IR and emit through the shared
        // emitter; LEGACY-routed modules keep the retained
        // backend. No within-run fallback exists: a shared
        // lowering/emission failure fails the compile and
        // publishes nothing.
        for (CheckedModuleInput checked : sharedModulesInDependencyOrder()) {
            emitSharedLuaModule(checked);
        }
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile) continue;
            if (routeOf(info) == ModuleRoute.SHARED) continue;
            codegenLuaModule(info, identityIndex);
            retainedEmissionCount++;
        }
        copyRuntimeLibrary();
        copyStdlibModules();
        validateMixedEdges();
    }

    /**
     * The release-owned production arm of phase 4 (P5/P6): exactly one
     * {@link ProductionProjectEmission#run} over the compile's declared
     * inputs — the C9 source-map warning, the one project lowering, the
     * pre-emission closure guard, the one production emission, and the
     * one staged project artifact plus the unchanged LuaJIT deployment
     * copies — then the one project emission record
     * ({@link #semanticEmissionCount}; the retained counter stays zero
     * and the per-module backend-result views stay empty). A lowering,
     * guard, or emission failure merges its first E6005 diagnostic and
     * stages nothing: the unchanged publication transaction then
     * preserves the previous artifact set byte-for-byte.
     */
    private void emitProductionProject() throws IOException {
        CheckedProjectBuildResult checked = checkedProjectBuild;
        if (checked == null || checked.hasErrors() || checked.input() == null
                || checked.index() == null) {
            throw new IllegalStateException("the production arm runs after a"
                + " successful checked-project build (producer defect)");
        }
        if (requirementManifests == null || requirementManifests.hasErrors()
                || requirementManifests.manifests() == null) {
            throw new IllegalStateException("the production arm runs after a"
                + " successful manifest phase (producer defect)");
        }
        if (hostDeclarationSurface == null) {
            throw new IllegalStateException("the production arm runs after a"
                + " successful declaration surface (producer defect)");
        }
        ProductionProjectEmission.Result result = ProductionProjectEmission.run(
            invocation, checked.input(), checked.index(),
            requirementManifests.manifests(), hostDeclarationSurface,
            declarationModuleIdentities(), externCGeneratedModules(),
            context.manifestDirectory(),
            builtinErrorDeclaration(checked.input()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, sourceMapExplicit, distributionHome, stager);
        if (result.emitted()) {
            semanticEmissionCount++;
            log("  Generated (production project emission): "
                + outputRoot.resolve(result.artifactRelativePath()));
        } else {
            diagnostics.addAll(result.diagnostics());
            hasErrors = true;
            log("  Production project emission failed: "
                + result.diagnostics());
        }
    }

    /**
     * The compilation's declaration-module identity map: the public
     * canonical identity of every declaration module the declaration
     * surface covers, keyed by module identity (the one project
     * lowering's registration-seed and class-identity input). The
     * identity is the compilation's single module-path classification
     * — the externals-listed declaration module's identity is the
     * externals key exactly as written.
     */
    private Map<ModuleId, CanonicalModuleIdentity> declarationModuleIdentities() {
        Map<String, CanonicalModuleIdentity> classification =
            modulePathClassification();
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : hostDeclarationSurface.moduleIds()) {
            CanonicalModuleIdentity identity =
                classification.get(declarationModule.path());
            if (identity != null) {
                identities.put(declarationModule, identity);
            }
        }
        return identities;
    }

    /**
     * The validated extern-C generated modules of this compile keyed by
     * module identity (the one project lowering's FFI registration-seed
     * input; empty when the compile imports no extern-C declaration).
     */
    private Map<ModuleId, FfiGeneratedModule> externCGeneratedModules() {
        Map<ModuleId, FfiGeneratedModule> generatedModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : ffiGenerations.entrySet()) {
            generatedModules.put(new ModuleId(generated.getKey()),
                generated.getValue());
        }
        return generatedModules;
    }

    /**
     * The compiler-owned builtin {@code Error} declaration of this
     * compile: the entry module's synthesized declaration — the same
     * one authority the checker's root binding derives from
     * ({@link BuiltinErrorDeclaration#synthesized}), so the builtin
     * layout seed is never derived from source text, a host
     * declaration, or an interface-index entry.
     */
    private static BuiltinErrorDeclaration builtinErrorDeclaration(
            CheckedProjectInput checkedProject) {
        for (CheckedModuleInput module : checkedProject.modules()) {
            if (module.moduleId().equals(checkedProject.entryModule())) {
                return BuiltinErrorDeclaration.synthesized(module.ast().span());
            }
        }
        throw new IllegalStateException("the checked project carries no entry"
            + " module (producer defect)");
    }

    /**
     * Records the first staging write failure of the compile (D4): it
     * sets the error state so the compile stops at the next phase
     * boundary, and {@link #compile()} renders the pinned deterministic
     * compiler I/O diagnostic.
     */
    private void stageFailure(IOException failure) {
        if (pendingStageFailure == null) {
            pendingStageFailure = failure;
        }
        hasErrors = true;
    }

    // =========================================================================
    // Phase 4 shared-route emission (ISSUE-0239 E10): the ModuleRoutePlan
    // selects semantic or retained emission per module with no within-run
    // fallback
    // =========================================================================

    /**
     * The production route of one implementation module (ISSUE-0239
     * E10): the plan's entry for the module, or {@code LEGACY} when the
     * compile's backend has no closed route-plan target (JS), the plan
     * phase did not produce, or the module is absent from the plan — a
     * defensive LEGACY selection over incomplete plan facts only, never
     * a within-run reroute of a SHARED plan entry.
     *
     * @param info the implementation module; non-null
     * @return the planned route ({@code LEGACY} when no SHARED entry exists)
     */
    private ModuleRoute routeOf(ModuleInfo info) {
        if (routePlan == null || routePlan.hasErrors() || routePlan.plan() == null) {
            return ModuleRoute.LEGACY;
        }
        ModuleRoute route = routePlan.plan().entries().get(new ModuleId(info.modulePath));
        return route == null ? ModuleRoute.LEGACY : route;
    }

    /**
     * The SHARED-routed implementation modules in the checked project's
     * dependency order (ISSUE-0239 E10) — the lowering/emission order of
     * the shared route (never the discovery-map insertion order, which
     * is entry-first).
     *
     * @return the shared modules in dependency order
     */
    private List<CheckedModuleInput> sharedModulesInDependencyOrder() {
        List<CheckedModuleInput> shared = new ArrayList<>();
        if (checkedProjectBuild == null || checkedProjectBuild.hasErrors()
                || checkedProjectBuild.input() == null) {
            return shared;
        }
        for (CheckedModuleInput checked : checkedProjectBuild.input().modules()) {
            if (routePlan == null || routePlan.hasErrors() || routePlan.plan() == null) {
                continue;
            }
            if (routePlan.plan().entries().get(checked.moduleId()) == ModuleRoute.SHARED) {
                shared.add(checked);
            }
        }
        return shared;
    }

    /** The requirement manifest of one implementation module (E10). */
    private SemanticRequirementManifest manifestOf(ModuleId moduleId) {
        if (requirementManifests == null || requirementManifests.hasErrors()
                || requirementManifests.manifests() == null) {
            return null;
        }
        for (SemanticRequirementManifest manifest : requirementManifests.manifests()) {
            if (manifest.moduleId().equals(moduleId)) {
                return manifest;
            }
        }
        return null;
    }

    /**
     * Lowers one SHARED-routed module through the full-program E7 walk
     * (ISSUE-0239 E10): the dependency-ordered project allocator, the
     * already-lowered callees' recorded {@code EXTERNAL_ENTRY} op ids,
     * and the plan's route facts. The unit is validated by the lowerer;
     * a failure is the returned E6005 — never a reroute.
     */
    private SemanticLowerer.FullProgramE7Result lowerSharedModule(
            CheckedModuleInput module) {
        if (sharedAllocator == null) {
            List<ModuleId> order = checkedProjectBuild.input().modules().stream()
                .map(CheckedModuleInput::moduleId).toList();
            sharedAllocator = SemanticIdAllocator.over(order);
        }
        SemanticRequirementManifest manifest = manifestOf(module.moduleId());
        if (manifest == null) {
            throw new IllegalStateException("shared module '" + module.moduleId()
                + "' has no requirement manifest (producer defect)");
        }
        return SemanticLowerer.lowerModuleFullProgramE7(
            module, invocation.semanticProfile(), manifest.constructCoverage(),
            checkedProjectBuild.index().interfaceIndexDigest(),
            invocation.capabilityRegistryHash(), sharedAllocator,
            routePlan.plan().entries(), sharedCalleeEntries, Set.of());
    }

    /** True iff the module's source path is the selected entry file. */
    private boolean isEntryModule(CheckedModuleInput checked) {
        for (Map.Entry<String, ModuleInfo> entry : modules.entrySet()) {
            if (entry.getValue().modulePath.equals(checked.moduleId().path())) {
                return Path.of(entry.getValue().sourcePath).toAbsolutePath()
                    .normalize().equals(entryFile.toAbsolutePath().normalize());
            }
        }
        return false;
    }

    /**
     * Emits one SHARED-routed module through the shared LuaJIT emitter
     * into the staging tree (ISSUE-0239 E10) and records its emitted ABI
     * manifest. A lowering/emission failure merges E6005 and fails the
     * compile — no artifact stages for the module and nothing publishes.
     */
    private void emitSharedLuaModule(CheckedModuleInput checked) throws IOException {
        SemanticLowerer.FullProgramE7Result lowered = lowerSharedModule(checked);
        if (lowered.lowering().hasErrors()) {
            diagnostics.addAll(lowered.lowering().diagnostics());
            hasErrors = true;
            log("  Shared lowering failed for " + checked.moduleId() + ": "
                + lowered.lowering().diagnostics());
            return;
        }
        sharedCalleeEntries.put(checked.moduleId(), lowered.externalEntries());
        String artifactPath = checked.moduleId().path().replace('.', '/') + ".lua";
        String source;
        try {
            source = LuaSemanticEmitter.emitProductionModule(
                lowered.lowering().unit(), lowered.lowering().table(),
                isEntryModule(checked));
        } catch (IllegalStateException emitterGap) {
            failSharedEmission(checked.moduleId().path(), emitterGap);
            return;
        }
        Path stageOutputPath = stager.stagePath(artifactPath);
        Files.writeString(stageOutputPath, source, StandardCharsets.UTF_8);
        recordSharedAbi(checked.moduleId(), lowered, artifactPath, "exports");
        semanticEmissionCount++;
        log("  Generated (shared semantic IR): " + outputRoot.resolve(artifactPath));
    }

    /**
     * Emits one SHARED-routed module through the shared JVM emitter into
     * the staging tree (ISSUE-0239 E10) under the retained layout's
     * class name, and records its emitted ABI manifest. A
     * lowering/emission failure merges E6005 and fails the compile.
     */
    private void emitSharedJvmModule(CheckedModuleInput checked) throws IOException {
        SemanticLowerer.FullProgramE7Result lowered = lowerSharedModule(checked);
        if (lowered.lowering().hasErrors()) {
            diagnostics.addAll(lowered.lowering().diagnostics());
            hasErrors = true;
            log("  Shared lowering failed for " + checked.moduleId() + ": "
                + lowered.lowering().diagnostics());
            return;
        }
        sharedCalleeEntries.put(checked.moduleId(), lowered.externalEntries());
        String className = JvmBackend.classNameFor(checked.moduleId().path());
        JvmSemanticEmitter.EmissionResult emission;
        try {
            emission = JvmSemanticEmitter.emitProductionModule(
                lowered.lowering().unit(), lowered.lowering().table(),
                isEntryModule(checked), className);
        } catch (IllegalStateException emitterGap) {
            failSharedEmission(checked.moduleId().path(), emitterGap);
            return;
        }
        Path stageOutputPath = stager.stagePath(className + ".java");
        Files.writeString(stageOutputPath, emission.source(), StandardCharsets.UTF_8);
        recordSharedAbi(checked.moduleId(), lowered, className + ".java", "main");
        semanticEmissionCount++;
        log("  Generated (shared semantic IR): "
            + outputRoot.resolve(className + ".java"));
    }

    /**
     * The fail-closed emitter-coverage gate (ISSUE-0239 E10): an op kind
     * outside the shared emitters' closed production set is E6005 —
     * never a crash, never a within-run reroute, and the failed module
     * stages no artifact (the publication transaction then preserves
     * the prior set).
     */
    private void failSharedEmission(String modulePath, IllegalStateException gap) {
        diagnostics.add(deal.semantic.ir.FailureContractRegistry.e6005(
            new deal.semantic.ir.LoweringFailureDetail(modulePath,
                deal.semantic.ir.SemanticCapability.MODULES,
                "SHARED_EMITTER_COVERAGE",
                invocation.semanticProfile(),
                deal.semantic.ir.LoweredModuleUnit.FORMAT_VERSION,
                "CompilationOrchestrator SHARED_EMITTER_COVERAGE ("
                    + gap.getMessage() + ")")));
        hasErrors = true;
        log("  Shared emission failed for " + modulePath + ": " + gap.getMessage());
    }

    /**
     * Records the emitted SHARED-owner ABI manifest of one module
     * (ISSUE-0239 E10): the planner-owned class facts copied from the
     * index, the exported descriptors from the unit's
     * {@code EXPORT_PUBLISH} payloads, one sync-invocation entry per
     * export (the recorded {@code EXTERNAL_ENTRY} op id, or the entry
     * delegation's wrapper name for {@code main}), one wrapper ABI per
     * function export, and the staged load key/initialization entry.
     */
    private void recordSharedAbi(ModuleId moduleId,
                                 SemanticLowerer.FullProgramE7Result lowered,
                                 String loadKey, String initializationEntry) {
        ExternalModuleInterface indexEntry =
            checkedProjectBuild.index().modules().get(moduleId);
        if (indexEntry == null) {
            throw new IllegalStateException("shared module '" + moduleId
                + "' has no interface index entry (producer defect)");
        }
        Map<String, RuntimeDescriptor> descriptors = new LinkedHashMap<>();
        Map<String, SyncInvocationEntry> syncEntries = new LinkedHashMap<>();
        Map<String, FunctionSignatureAbi> wrappers = new LinkedHashMap<>();
        Map<String, OpId> entries = lowered.externalEntries();
        for (SemanticOp op : lowered.lowering().unit().ops()) {
            if (op.kind() != SemanticOpKind.EXPORT_PUBLISH) {
                continue;
            }
            KindPayload.ExportPublishPayload payload =
                (KindPayload.ExportPublishPayload) op.payload();
            descriptors.put(payload.name(), payload.descriptor());
            OpId entryOpId = entries.get(payload.name());
            if (entryOpId != null) {
                syncEntries.put(payload.name(),
                    new SyncInvocationEntry.ExternalEntry(entryOpId));
            } else {
                // main: the ENTRY_INVOKE delegation owns its invocation
                // shape; the retained-layout wrapper name stands in.
                syncEntries.put(payload.name(),
                    new SyncInvocationEntry.AbiWrapper(payload.name()));
            }
            if (payload.descriptor() instanceof RuntimeDescriptor.Func func) {
                wrappers.put(payload.name(), new FunctionSignatureAbi(
                    payload.name(), func.canonicalSpecText()));
            }
        }
        Map<ClassId, ClassFactoryId> factoryAbi = new LinkedHashMap<>();
        Map<ClassId, List<FieldInterface>> layoutAbi = new LinkedHashMap<>();
        for (ClassInterface classEntry : indexEntry.classes()) {
            factoryAbi.put(classEntry.classId(), classEntry.constructionEntry());
            layoutAbi.put(classEntry.classId(), classEntry.fields());
        }
        Target target = backend == Backend.JVM ? Target.JVM : Target.LUAJIT;
        emittedSharedAbis.add(new TargetModuleAbi(moduleId, target,
            ArtifactOwner.SHARED, invocation.semanticProfile(), factoryAbi,
            layoutAbi, descriptors, loadKey, initializationEntry, wrappers,
            syncEntries, List.of()));
    }

    /**
     * Stage-time mixed-edge validation (ISSUE-0239 E10): every emitted
     * SHARED ABI manifest and the plan's plan-time retained records are
     * validated against the staged set and the interface index before
     * publication. A failure is E6005 — nothing publishes and the prior
     * live set stays untouched (the publication transaction owns the
     * all-or-nothing swap).
     */
    private void validateMixedEdges() throws IOException {
        if (emittedSharedAbis.isEmpty()) {
            return;
        }
        if (routePlan == null || routePlan.hasErrors() || routePlan.plan() == null) {
            throw new IllegalStateException("shared ABI manifests exist without a "
                + "route plan (producer defect)");
        }
        List<StagedArtifact> staged = new ArrayList<>();
        for (deal.publication.Artifact artifact : stager.stagedSet().artifacts()) {
            staged.add(new StagedArtifact(artifact.relativePath(),
                artifact.content()));
        }
        StagedArtifactSet stagedSet = new StagedArtifactSet(staged);
        List<TargetModuleAbi> abiEdges = new ArrayList<>(routePlan.plan().abiEdges());
        abiEdges.addAll(emittedSharedAbis);
        Optional<CompilerDiagnostic> failure = TargetAbiValidator.validate(
            stagedSet, routePlan.plan(), abiEdges,
            checkedProjectBuild.index(), invocation.semanticProfile());
        if (failure.isPresent()) {
            diagnostics.add(failure.get());
            hasErrors = true;
            log("  Mixed-edge validation failed: " + failure.get());
        }
    }

    /**
     * Lua use site: emits the module via {@link LuaBackend}, with the
     * resolved import map, host-module declarations, and the compilation's
     * canonical descriptor service (emitter page D1 — the same surface
     * codegenAllJs builds and consumes).
     */
    private void codegenLuaModule(ModuleInfo info,
                                  ModuleIdentityResolver.IdentityIndex identityIndex)
            throws IOException {
        long modStart = System.currentTimeMillis();

        Map<String, String> importResolutions = new HashMap<>();
        Map<String, Map<String, Type>> hostModules = new HashMap<>();
        // Extern-C imports (emitter page D6): raw import path -> the
        // metadata phase's generated module (descriptor, cdef bundle,
        // retained plans, forward bindings); the emitted import routes
        // through __rt.load_ffi and never through load_host or a raw
        // require.
        Map<String, FfiGeneratedModule> ffiModules = new HashMap<>();
        for (StatementNode stmt : info.rawAst.statements()) {
            if (stmt instanceof ImportDeclaration imp) {
                String resolvedSource = resolveImportPath(imp.modulePath(),
                    Path.of(info.sourcePath), imp.span());
                if (resolvedSource != null) {
                    ModuleInfo imported = modules.get(resolvedSource);
                    if (imported != null) {
                        importResolutions.put(imp.modulePath(),
                            imported.modulePath);
                        // Host modules (ISSUE-0082, host-module-abi D5):
                        // declaration files that are not spec stdlib
                        // modules load through __rt.load_host with the
                        // raw import path verbatim as the require key.
                        // An effective extern-C declaration with published
                        // FFI metadata is an FFI module instead (emitter
                        // page D6): it loads through __rt.load_ffi and is
                        // never a host module.
                        if (imported.isDeclarationFile
                                && !isSpecStdlibModuleInfo(imported)) {
                            FfiGeneratedModule ffi =
                                ffiGenerations.get(imported.modulePath);
                            if (imported.rawAst != null
                                    && imported.rawAst.fileDirectives()
                                        .externC()
                                    && ffi != null) {
                                ffiModules.put(imp.modulePath(), ffi);
                            } else {
                                hostModules.put(imp.modulePath(),
                                    imported.exports != null
                                        ? imported.exports : Map.of());
                            }
                        }
                    }
                }
            }
        }

        // The staging sink (whole-project-artifact-publication D1/D5):
        // the same module-relative path, resolved inside the staging
        // tree. The backend writes the artifact and its sidecar there;
        // the live publication paths are passed only for the sidecar's
        // path-string computation, so the per-invocation stage-tree
        // nonce (on-disk names only) never enters artifact content.
        String filePath = info.modulePath.replace('.', '/') + ".lua";
        Path liveOutputPath = outputRoot.resolve(filePath);
        Path stageOutputPath = stager.stagePath(filePath);

        // v1.2 entry contract: the selected entry module must export a
        // non-async main(): null and the backend invokes main() from that
        // module. Only the LuaJIT entry module gets the entry treatment
        // here — the JVM backend owns its own entry handling (JVM work is
        // out of scope for this slice).
        boolean isEntry = Path.of(info.sourcePath).toAbsolutePath().normalize()
            .equals(entryFile.toAbsolutePath().normalize());

        // Use the result-returning variant to produce both the .lua file
        // and the .deal.map.json sidecar (when --source-map is active),
        // and to surface backend diagnostics: a backend rejection
        // (E6004 entry contract; rest parameters are rejected earlier by
        // the parser with E1047) fails the compilation and writes no
        // artifact, mirroring the JVM backend's
        // no-artifact-on-rejection contract. info.modulePath is the same
        // value seeded into NameResolver, so emitted class identity tags
        // stay byte-identical to the checker's descriptors
        // (runtime-class-identity D2(0)).
        LuaBackend.GenerationResult gen = LuaBackend.generateToFile(
            info.rawAst, info.checkResult, info.sourcePath, info.modulePath,
            stager.stageTree(), stageOutputPath, outputRoot, liveOutputPath,
            sourceMap, importResolutions, hostModules, ffiModules,
            context.manifestDirectory(),
            isEntry, identityIndex, invocation.semanticProfile(),
            completedPlansByModulePath());
        // Native ranged backend list (T12): the backend emits
        // CompilerDiagnostic entries directly, so the orchestrator merge
        // needs no boundary conversion — real spans keep their exact
        // scalar offsets and synthetic anchors keep their notes.
        List<CompilerDiagnostic> backendDiags = gen.diagnostics();
        diagnostics.addAll(backendDiags);
        boolean backendError = backendDiags.stream()
            .anyMatch(d -> "error".equals(d.severity()));
        if (backendError) {
            hasErrors = true;
            log("  LuaJIT backend rejected " + info.modulePath + ": "
                + gen.diagnostics());
            return;
        }
        luaGeneratedResults.put(info.sourcePath, gen);

        long modElapsed = System.currentTimeMillis() - modStart;
        log("  Generated: " + liveOutputPath + " (" + modElapsed + "ms)");
    }

    /**
     * JVM use site (ISSUE-0091, ISSUE-0096, ISSUE-0100): emits one {@code
     * <ClassName>.java} module class per module, with the per-module import
     * resolution map (raw import path → imported module path) built exactly
     * like the LuaJIT use site — only non-declaration modules are entries.
     * Imports of declaration files that are not spec stdlib modules become
     * HOST modules (ISSUE-0100, host-module-abi D5): their declared export
     * map flows into the backend's hostModules parameter, which emits the
     * load-time-validated host wrappers. Backend diagnostics (E6000 for
     * out-of-slice constructs — including unsupported host export shapes,
     * at the import statement itself) fail the compilation with
     * the standard diagnostic report; no artifact is written for a module
     * the backend rejects. Class names are derived from the full module
     * path ({@code app/main} → {@code AppMain}), and a collision between
     * two modules mapping to the same class name (e.g. a case-only
     * difference) is an E6000 error — never a silent artifact overwrite.
     */

    /** Per-module JVM import context (ISSUE-0096/ISSUE-0100/ISSUE-0109):
     * import resolutions, imported class declarations, host-module
     * declarations, and the imported modules' declared-boundary surfaces
     * (ISSUE-0603 D6: the exported {@code FunctionDeclaration} nodes plus
     * each imported module's source path) for one module — the same
     * discovery the JVM use site builds. Shared by the ISSUE-0301
     * shape-collection pre-pass and the per-module codegen pass. */
    private record JvmImportContext(
            Map<String, String> importResolutions,
            Map<String, Map<String, ClassDeclaration>> importedClasses,
            Map<String, Map<String, Type>> hostModules,
            Map<String, Map<String, List<HostModuleDeclarations.HostField>>>
                hostClassDeclarations,
            Map<String, JvmBackend.ImportedModuleSurface> importedSurfaces) {}

    /** The externals identity specifier of a declaration module (the
     * module-identity layer's classification raw import specifier), or
     * null when the module carries no externals classification. */
    private static String externalsSpecifierOf(ModuleInfo info) {
        if (info.location == null) {
            return null;
        }
        return info.location.moduleClassification()
            instanceof CanonicalModuleIdentity.ExternalModule ext
            ? ext.rawImportSpecifier() : null;
    }

    /** Builds the per-module JVM import context for {@code info}. */
    private JvmImportContext jvmImportContextOf(ModuleInfo info) {
        // Import resolutions (ISSUE-0096): raw import path → module
        // path of the imported COMPILED module. Declaration files
        // become host modules (ISSUE-0100). ISSUE-0109: the same
        // discovery pass collects each imported module's class
        // declarations (module path → name → declaration).
        Map<String, String> importResolutions = new HashMap<>();
        Map<String, Map<String, ClassDeclaration>> importedClasses =
            new HashMap<>();
        Map<String, Map<String, Type>> hostModules = new HashMap<>();
        // Host-class declarations (ISSUE-0303, jvm-v12-host-abi-completion
        // D4): the declared class exports' field records with their
        // orchestrator-resolved types — the JVM backend synthesizes the
        // shared $DealRt record classes from them.
        Map<String, Map<String, List<HostModuleDeclarations.HostField>>>
            hostClassDeclarations = new HashMap<>();
        // Declared-boundary surfaces (ISSUE-0603 D6,
        // jvm-canonical-error-snapshot-convergence): every imported
        // compiled module's exported FunctionDeclaration nodes — whose
        // parameter/return type annotations carry the spans the
        // declared-boundary origins name — plus the module's source
        // path, so the importing artifact can emit the callee's declared
        // parameter/return boundary origin, imported companions
        // included.
        Map<String, JvmBackend.ImportedModuleSurface> importedSurfaces =
            new HashMap<>();
        for (StatementNode stmt : info.rawAst.statements()) {
            if (stmt instanceof ImportDeclaration imp) {
                String resolvedSource = resolveImportPath(imp.modulePath(),
                    Path.of(info.sourcePath), imp.span());
                if (resolvedSource != null) {
                    ModuleInfo imported = modules.get(resolvedSource);
                    if (imported == null) {
                        continue;
                    }
                    if (imported.isDeclarationFile) {
                        if (!isSpecStdlibModuleInfo(imported)) {
                            HostModuleDeclarations declared =
                                hostDeclarationsOf(imported);
                            // Host-module wiring (ISSUE-0100/ISSUE-0303):
                            // the alias-keyed export map keeps the raw
                            // import specifier (the emitted load-time
                            // presence check and the wrapper ABI key on
                            // it), while the declared class-field records
                            // key on the declaration module's externals
                            // identity specifier — the compilation's
                            // typing/class-identity name the synthesized
                            // records, their canonical identity text, and
                            // every class-typed lookup project. The two
                            // spellings coincide for an exact-key
                            // externals entry; a derived conformance
                            // context may carry the dotted typing name
                            // first (the corpus externals-identity
                            // convention), and the export map stays
                            // reachable under both spellings.
                            String identitySpecifier =
                                externalsSpecifierOf(imported);
                            hostModules.put(imp.modulePath(),
                                declared.exports());
                            hostClassDeclarations.put(
                                identitySpecifier == null
                                    ? imp.modulePath()
                                    : identitySpecifier,
                                declared.classFields());
                            if (identitySpecifier != null
                                    && !identitySpecifier.equals(
                                        imp.modulePath())) {
                                hostModules.put(identitySpecifier,
                                    declared.exports());
                            }
                        }
                    } else {
                        importResolutions.put(imp.modulePath(),
                            imported.modulePath);
                        Map<String, ClassDeclaration> classes =
                            new LinkedHashMap<>();
                        for (StatementNode importedStmt
                                : imported.rawAst.statements()) {
                            ClassDeclaration cd = null;
                            if (importedStmt instanceof ClassDeclaration c) {
                                cd = c;
                            } else if (importedStmt instanceof ExportDeclaration ed
                                    && ed.declaration() instanceof ClassDeclaration c) {
                                cd = c;
                            }
                            if (cd != null) {
                                classes.putIfAbsent(cd.name(), cd);
                            }
                        }
                        importedClasses.put(imported.modulePath, classes);
                        // D6: the imported module's exported function
                        // declarations (the declared-boundary annotation
                        // spans) plus its source path.
                        Map<String, FunctionDeclaration> functions =
                            new LinkedHashMap<>();
                        for (StatementNode importedStmt
                                : imported.rawAst.statements()) {
                            FunctionDeclaration fd = null;
                            if (importedStmt instanceof FunctionDeclaration f) {
                                fd = f;
                            } else if (importedStmt instanceof ExportDeclaration ed
                                    && ed.declaration() instanceof FunctionDeclaration f) {
                                fd = f;
                            }
                            if (fd != null) {
                                functions.putIfAbsent(fd.name(), fd);
                            }
                        }
                        importedSurfaces.put(imported.modulePath,
                            new JvmBackend.ImportedModuleSurface(functions,
                                imported.sourcePath));
                    }
                }
            }
        }
        return new JvmImportContext(importResolutions, importedClasses,
            hostModules, hostClassDeclarations, importedSurfaces);
    }

    private void codegenAllJvm() throws IOException {
        if (sourceMapExplicit) {
            // Source-map sidecars (.deal.map.json) are produced only by the
            // LuaJIT emitter; surface that to the CLI user instead of
            // silently producing no sidecars (ISSUE-0091 rework round 3).
            // Fired only when --source-map was explicitly requested: a
            // --dump-ir-derived sourceMap flag (IR hardening enables source
            // maps with dumps) must not print the warning.
            System.err.println("Warning: --source-map produces no source-map "
                + "sidecars with the JVM backend (source maps are "
                + "LuaJIT-only)");
        }
        // Canonical identity surface (canonical identity carriage,
        // descriptor-identity-propagation D1/D2): the ONE
        // per-compilation identity index over the module-path
        // classification — the same surface the checker consumed — so
        // every class descriptor the JVM backend emits resolves through
        // {@code index.descriptorTextFor(identity)} byte-for-byte from
        // the classified identities (no second Type-to-text producer
        // exists).
        ModuleIdentityResolver.IdentityIndex identityIndex =
            buildCanonicalIdentitySurface();
        // Compilation-wide class-declaration identity surface (ISSUE-0301
        // D4 shared-scope emission): canonical class identity → declaring
        // module path for every class of every checked project module.
        // The entry module's shared-scope wrapper pre-registration
        // resolves a collected shape's class reference through this map
        // when the declaring module is one the entry does not import
        // directly (its own importAliases/importedClasses maps cannot
        // name it), so the wrapper's invoke signature always references
        // the real declaring module's emitted class. Deterministic:
        // module order, then source order per module; the first
        // declaration of an identity wins. Host declarations are
        // excluded (their class exports resolve to the shared
        // $DealRt synthesized records — jvm-v12-host-abi-completion
        // D4 — collected in the projectHostClasses union below, never
        // through a module-emitted class).
        Map<CanonicalClassIdentity, String> classDeclaringModules =
            new LinkedHashMap<>();
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile) continue;
            CanonicalModuleIdentity moduleIdentity =
                classifyModuleIdentity(info);
            if (moduleIdentity == null) continue;
            for (StatementNode stmt : info.rawAst.statements()) {
                ClassDeclaration cd = null;
                if (stmt instanceof ClassDeclaration c) {
                    cd = c;
                } else if (stmt instanceof ExportDeclaration ed
                        && ed.declaration() instanceof ClassDeclaration c) {
                    cd = c;
                }
                if (cd != null) {
                    classDeclaringModules.putIfAbsent(
                        new CanonicalClassIdentity(moduleIdentity,
                            cd.name()),
                        info.modulePath);
                }
            }
        }
        // Pre-codegen collection pass (ISSUE-0301 D4, the shared
        // runtime value surface): walk every checked module's types and
        // collect the closed project-wide shape set — function-signature
        // shapes, nested/function/bytes array element shapes — so the
        // selected entry module's shared $DealRt scope carries every
        // shape any module references. Deterministic: module dependency
        // order (the modules map), then source order per module.
        //
        // ISSUE-0303 (jvm-v12-host-abi-completion D4): host-class-typed
        // shapes join the union — the declared host classes emit their
        // synthesized record classes in the shared $DealRt scope (the
        // project-wide host-class union collected right below), so a
        // wrapper may reference a host-class record exactly like any
        // other shared carrier.
        List<Type> sharedShapes = new ArrayList<>();
        Set<Type> seenShapes = new LinkedHashSet<>();
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile) continue;
            JvmImportContext ctx = jvmImportContextOf(info);
            for (Type shape : JvmBackend.collectShapes(info.rawAst,
                    info.checkResult, info.sourcePath, info.modulePath,
                    ctx.importResolutions, ctx.importedClasses,
                    ctx.hostModules, ctx.hostClassDeclarations,
                    invocation.semanticProfile(),
                    identityIndex, identityIndex.moduleIdentityLookup())) {
                if (seenShapes.add(shape)) {
                    sharedShapes.add(shape);
                }
            }
        }
        List<Type> projectShapes = List.copyOf(sharedShapes);

        // Project-wide host-class declaration union (ISSUE-0303,
        // jvm-v12-host-abi-completion D4): raw import specifier → class
        // name → declared field records, deterministic (module order,
        // then per-module import order, then declaration order). The
        // entry module's shared $DealRt scope emits one synthesized
        // record class per declared host class — the single emission
        // point, keyed by the specifier + class name, never by a hash
        // iteration.
        Map<String, Map<String, List<HostModuleDeclarations.HostField>>>
            projectHostClasses = new LinkedHashMap<>();
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile) continue;
            JvmImportContext ctx = jvmImportContextOf(info);
            for (Map.Entry<String,
                    Map<String, List<HostModuleDeclarations.HostField>>> e
                    : ctx.hostClassDeclarations.entrySet()) {
                Map<String, List<HostModuleDeclarations.HostField>>
                    classes = projectHostClasses.computeIfAbsent(
                        e.getKey(), k -> new LinkedHashMap<>());
                for (Map.Entry<String,
                        List<HostModuleDeclarations.HostField>> c
                        : e.getValue().entrySet()) {
                    classes.putIfAbsent(c.getKey(), c.getValue());
                }
            }
        }

        // Pass 1: generate every module and merge diagnostics. Rejected
        // modules write no artifact.
        List<ModuleInfo> cleanModules = new ArrayList<>();
        Map<ModuleInfo, JvmBackend.JvmCodegenResult> results = new LinkedHashMap<>();
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile) continue;
            if (routeOf(info) == ModuleRoute.SHARED) {
                continue; // ISSUE-0239 E10: emitted by the shared emitter
            }
            JvmImportContext ctx = jvmImportContextOf(info);
            boolean isEntry = info.sourcePath.equals(entryFile.toString());
            // ISSUE-0374 profile plumb: the backend derives its
            // backend-wide int mode from the invocation's project-wide
            // semantic profile — never from a static flag, a system
            // property, or any source/CLI/environment surface.
            // v1.2 identity carriage (descriptor-identity-propagation
            // D1/D2): the compilation's identity index and module-path
            // classification flow in; every class descriptor the backend
            // emits resolves through index.descriptorTextFor(identity).
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                info.rawAst, info.checkResult, info.sourcePath, info.modulePath,
                ctx.importResolutions, ctx.importedClasses, ctx.hostModules,
                ctx.hostClassDeclarations,
                isEntry, isEntry, identityIndex,
                identityIndex.moduleIdentityLookup(),
                invocation.semanticProfile(), projectShapes,
                classDeclaringModules, projectHostClasses,
                completedPlansByModulePath(), ctx.importedSurfaces);
            for (CompilerDiagnostic d : res.diagnostics()) {
                diagnostics.add(d);
                hasErrors = true;
            }
            if (res.hasErrors()) {
                log("  JVM backend rejected " + info.modulePath + ": "
                    + res.diagnostics());
                continue;
            }
            cleanModules.add(info);
            results.put(info, res);
            jvmGeneratedResults.put(info.sourcePath, res);
        }

        // Pass 2: write artifacts for clean modules, rejecting class-name
        // collisions instead of silently overwriting an earlier module's
        // artifact.
        Map<String, String> classOwners = new LinkedHashMap<>();
        for (ModuleInfo info : cleanModules) {
            JvmBackend.JvmCodegenResult res = results.get(info);
            String className = res.className();
            String previousOwner = classOwners.putIfAbsent(className, info.modulePath);
            if (previousOwner != null) {
                // Anchorless site (D5/D6): the note names the colliding
                // modules and class name.
                syntheticError(DiagnosticCode.E6000,
                    "JVM backend: modules '" + previousOwner + "' and '"
                        + info.modulePath + "' both derive the class name '"
                        + className + "' (rename one module)",
                    info.sourcePath,
                    "missing anchor: module class-name collision between '"
                        + previousOwner + "' and '" + info.modulePath
                        + "' (class '" + className + "')");
                continue;
            }
            // The staging sink (whole-project-artifact-publication
            // D1/D5): the same module-relative path inside the staging
            // tree; the live root is written only by the publish step.
            Path stageOutputPath = stager.stagePath(className + ".java");
            Files.writeString(stageOutputPath, res.source());
            retainedEmissionCount++;
            log("  Generated: " + outputRoot.resolve(className + ".java"));
        }
        // ISSUE-0239 E10: SHARED-routed modules lower to validated
        // semantic IR and emit through the shared JVM emitter — no
        // within-run fallback: a shared lowering/emission failure fails
        // the compile and publishes nothing.
        for (CheckedModuleInput checked : sharedModulesInDependencyOrder()) {
            emitSharedJvmModule(checked);
        }
        validateMixedEdges();
    }

    /**
     * The per-compilation canonical identity surface (emitter page D1;
     * js-v12-completion-architecture D3): one identity index over the
     * module-path classification, consumed by the Lua and JS emitters'
     * descriptor services.  The intrinsic builtin Error classification
     * (the checker's empty module path) and every known module join the
     * map; a module the classification cannot give a public identity
     * (an out-of-root relative source) stays absent — class-free code
     * remains valid, and a class there fails closed at descriptor
     * production (the pinned invariant violation).
     */
    private ModuleIdentityResolver.IdentityIndex buildCanonicalIdentitySurface() {
        return ModuleIdentityResolver.buildIndex(modulePathClassification());
    }

    /**
     * The compilation's module-path classification (the module-identity
     * layer's single classification map): every known module path plus
     * the intrinsic builtin Error module path.  The checker, the export
     * extractor, the IR dumper, and the backends all obtain class
     * identities exclusively from this surface (v1.2 identity carriage,
     * descriptor-identity-propagation D1) — never from dotted-path
     * reconstruction.
     */
    private Map<String, CanonicalModuleIdentity> modulePathClassification() {
        Map<String, CanonicalModuleIdentity> modulePathIdentities =
            new HashMap<>();
        modulePathIdentities.put("", CanonicalModuleIdentity.BuiltinModule.INSTANCE);
        for (ModuleInfo info : modules.values()) {
            CanonicalModuleIdentity identity = classifyModuleIdentity(info);
            if (identity != null) {
                modulePathIdentities.put(info.modulePath, identity);
            }
        }
        return modulePathIdentities;
    }

    /**
     * JS use site (ISSUE-0247 core slice, js-backend-emitter D3): the JVM
     * two-pass model — pass 1 generates every module and merges
     * diagnostics, pass 2 writes one {@code <modulePath with '/' for
     * '.'>.js} artifact per clean module — plus the LuaJIT
     * deployment-copy precedent (copyJsRuntimeLibrary/
     * copyStdlibJsModules). The per-module import classification mirrors
     * the LuaJIT use site (codegenLuaModule): a resolved non-declaration
     * module is a project import, a resolved declaration file that is not
     * a spec stdlib module is a host module. Backend diagnostics (E6004
     * for an invalid entry module main at this slice; later slices add
     * the E6000/E6006 rejection table) fail the compilation with the
     * standard report; no artifact is written for a rejected module. The
     * dot→slash artifact mapping is injective over the module-path
     * domain, so no class-name-collision gate is needed (unlike
     * codegenAllJvm's). The deployment copies run unconditionally at the
     * end of phase 4 (Lua deployment parity). js-v12-source-maps D1:
     * the explicit --source-map warning retired — the effective
     * sourceMap flag (explicit or --dump-ir-derived) drives the
     * per-module .deal.map.json sidecar writes in pass 2 instead.
     */
    private void codegenAllJs() throws IOException {
        // Canonical identity surface (js-v12-completion-architecture D3):
        // the shared per-compilation surface both emitter arms consume.
        ModuleIdentityResolver.IdentityIndex identityIndex =
            buildCanonicalIdentitySurface();

        // Pass 1: generate every module and merge diagnostics. Rejected
        // modules write no artifact.
        List<ModuleInfo> cleanModules = new ArrayList<>();
        Map<ModuleInfo, JsBackend.JsCodegenResult> results =
            new LinkedHashMap<>();
        for (ModuleInfo info : modules.values()) {
            if (info.isDeclarationFile) continue;
            // Import classification (the LuaJIT use-site shape,
            // codegenLuaModule): raw import path → module path of the
            // imported COMPILED module; declaration files that are not
            // spec stdlib modules become host modules with their declared
            // export map.
            Map<String, String> importResolutions = new HashMap<>();
            // Host modules (ISSUE-0328, js-v12-host-abi-completion D1):
            // the raw import path carries the declared export map PLUS
            // the declaration AST's class-field records with their
            // orchestrator-resolved field types — the emitter renders
            // the loadHost declared map (functions as canonical
            // declared descriptors, classes as the canonical identity
            // plus the field-descriptor array) from this record.
            Map<String, HostModuleDeclarations> hostModules =
                new HashMap<>();
            // Extern-C imports (fixed-name-directive-events D9): raw
            // import paths whose resolved module is a declaration file
            // with effective FileDirectives.externC — the re-keyed JS
            // E6006 FFI_UNSUPPORTED_BACKEND arm keys on this set at the
            // import statement.
            Set<String> externCImports = new HashSet<>();
            if (info.rawAst != null) {
                for (StatementNode stmt : info.rawAst.statements()) {
                    if (stmt instanceof ImportDeclaration imp) {
                        String resolvedSource = resolveImportPath(imp.modulePath(),
                            Path.of(info.sourcePath), imp.span());
                        if (resolvedSource != null) {
                            ModuleInfo imported = modules.get(resolvedSource);
                            if (imported != null) {
                                importResolutions.put(imp.modulePath(),
                                    imported.modulePath);
                                // Host modules: declaration files that are
                                // not spec stdlib modules (the LuaJIT use
                                // site's classification, verbatim).
                                if (imported.isDeclarationFile
                                        && !isSpecStdlibModuleInfo(imported)) {
                                    hostModules.put(imp.modulePath(),
                                        hostDeclarationsOf(imported));
                                }
                                if (imported.isDeclarationFile
                                        && imported.rawAst != null
                                        && imported.rawAst.fileDirectives()
                                            .externC()) {
                                    externCImports.add(imp.modulePath());
                                }
                            }
                        }
                    }
                }
            }
            boolean isEntry = info.sourcePath.equals(entryFile.toString());
            // js-v12-source-maps D2: the effective sourceMap flag
            // (explicit --source-map or --dump-ir-derived) attaches a
            // mapping recorder to the generation — the optional
            // SourceMapGenerator parameter (the Lua generateResult
            // precedent). A rejected module never serializes its
            // recorder: pass 2 runs for clean modules only.
            // ISSUE-0374 profile plumb (js-v12-int32-bytes D2): the
            // backend derives its backend-wide int mode from the
            // invocation's project-wide semantic profile — never from a
            // static flag, a system property, or any source/CLI/
            // environment surface. Under DEAL_V1_2_INT32 every emitted
            // module calls $rt.setInt32Mode(true) immediately after the
            // runtime $require; LEGACY_SAFE_INT emits no selector.
            JsBackend.JsCodegenResult res = JsBackend.generate(
                info.rawAst, info.checkResult, info.sourcePath, info.modulePath,
                importResolutions, hostModules, externCImports, isEntry,
                identityIndex, identityIndex.moduleIdentityLookup(),
                sourceMap ? new SourceMapGenerator() : null,
                invocation.semanticProfile(),
                completedPlansByModulePath());
            // Native ranged backend list (T12): the backend emits
            // CompilerDiagnostic entries directly, so the orchestrator
            // merge needs no boundary conversion — real spans keep their
            // exact scalar offsets and synthetic anchors keep their notes.
            List<CompilerDiagnostic> backendDiags = res.diagnostics();
            diagnostics.addAll(backendDiags);
            if (backendDiags.stream()
                    .anyMatch(d -> "error".equals(d.severity()))) {
                hasErrors = true;
            }
            if (res.hasErrors()) {
                log("  JavaScript backend rejected " + info.modulePath + ": "
                    + res.diagnostics());
                continue;
            }
            cleanModules.add(info);
            results.put(info, res);
            jsGeneratedResults.put(info.sourcePath, res);
        }

        // Pass 2: write artifacts for clean modules only. With the
        // effective sourceMap flag, each clean module additionally
        // writes its .deal.map.json sidecar (js-v12-source-maps D1):
        // one <modulePath with '/' for '.'>.deal.map.json next to the
        // artifact, serialized from the module's recorded mappings via
        // SourceMapGenerator.toJson with the same project-relative
        // source/generated path strings the Lua arm passes. A clean
        // statement-less module (an empty or comment-only source)
        // writes its sidecar with an empty mappings array — every
        // clean module gets exactly one sidecar, so no hasMappings()
        // gate may skip the write. A rejected module writes no .js
        // and no sidecar (the two-pass no-partial-artifact contract).
        for (ModuleInfo info : cleanModules) {
            JsBackend.JsCodegenResult res = results.get(info);
            // The staging sink (whole-project-artifact-publication
            // D1/D5): the same module-relative paths inside the staging
            // tree; the live publication path feeds only the sidecar's
            // path-string computation, so the per-invocation stage-tree
            // nonce (on-disk names only) never enters artifact content.
            String artifactRel = res.modulePath().replace('.', '/') + ".js";
            Path liveArtifactPath = outputRoot.resolve(artifactRel);
            Path stageOutputPath = stager.stagePath(artifactRel);
            Files.writeString(stageOutputPath, res.source());
            log("  Generated: " + liveArtifactPath);

            if (sourceMap && res.sourceMap() != null) {
                String[] paths = sourceMapSidecarPaths(info.sourcePath,
                    outputRoot, liveArtifactPath);
                String mapJson = res.sourceMap().toJson(paths[0], paths[1]);
                Path stageMapPath = stager.stagePath(
                    res.modulePath().replace('.', '/')
                        + ".deal.map.json");
                Files.writeString(stageMapPath, mapJson);
                log("  Source map: " + outputRoot.resolve(
                    res.modulePath().replace('.', '/')
                        + ".deal.map.json"));
            }
        }

        copyJsRuntimeLibrary();
        copyStdlibJsModules();
    }

    /**
     * The compilation's declaration surface (ISSUE-0630, design source
     * {@code project-lowering-entry-and-registration-seeds} D3): the one
     * immutable fact record per host and extern-C declaration module the
     * compilation imports, with the declared exports, the per-class field
     * records in declaration order with their resolved declared types,
     * and the per-class declaration kind. Produced once per compile at
     * the start of phase 4; the retained host consumers read the host
     * projection of this surface.
     *
     * @return the produced surface, or null when production failed (the
     *         compile carries the first E6005 and publishes nothing)
     */
    public HostDeclarationSurface hostDeclarationSurface() {
        return hostDeclarationSurface;
    }

    /**
     * Produces the declaration surface over every host and extern-C
     * declaration module of the compilation (the spec stdlib declaration
     * modules keep their {@code BuiltinModule} classification and are not
     * host declarations). A producer defect — the first declared class
     * field whose resolved declared type has no runtime representation —
     * merges its E6005 into the compile's diagnostics and yields no
     * surface.
     *
     * @return the produced surface, or null on a producer defect
     */
    private HostDeclarationSurface produceHostDeclarationSurface() {
        List<HostDeclarationSurface.DeclarationFacts> facts =
            new ArrayList<>();
        for (ModuleInfo info : modules.values()) {
            if (!info.isDeclarationFile || info.rawAst == null
                    || isSpecStdlibModuleInfo(info)) {
                continue;
            }
            facts.add(declarationFactsOf(info));
        }
        HostDeclarationSurface.Production production =
            HostDeclarationSurface.produce(facts);
        if (production.hasErrors()) {
            diagnostics.addAll(production.diagnostics());
            hasErrors = true;
            return null;
        }
        log("  Declaration surface: " + facts.size()
            + " declaration module(s)");
        return production.surface();
    }

    /**
     * The declaration facts of one declaration module: the declared
     * export map (the phase-1 {@link ExportExtractor} output for a
     * declaration file, in declaration order), the per-class field
     * records in declaration order with their resolved declared types,
     * and the declaration kind ({@code EXTERN_C} for a module the
     * metadata phase classifies extern-C, {@code HOST} otherwise). The
     * field types resolve in the declaring module's own context through
     * an {@link ExportExtractor} seeded with the compilation's
     * module-path classification and the declaration's resolved import
     * aliases — the exact resolution the retained host consumers read.
     */
    private HostDeclarationSurface.DeclarationFacts declarationFactsOf(
            ModuleInfo imported) {
        Map<String, String> importAliasMap = new HashMap<>();
        for (StatementNode stmt : imported.rawAst.statements()) {
            if (stmt instanceof ImportDeclaration imp) {
                String resolved = resolveImportPath(imp.modulePath(),
                    Path.of(imported.sourcePath));
                if (resolved != null) {
                    ModuleInfo target = modules.get(resolved);
                    if (target != null) {
                        importAliasMap.put(imp.alias(),
                            target.modulePath);
                    }
                }
            }
        }
        // v1.2 identity carriage (ISSUE-0303 D4): the extractor is
        // seeded with the compilation's module-path classification, so
        // the host-class field types carry the canonical externals
        // identity (ExternalModule(rawImportSpecifier) — the manifest
        // key as written), never the standalone dotted-path default.
        // The JVM synthesized record emission keys on the externals
        // projection, exactly like the checker's host-class symbols.
        ExportExtractor extractor = new ExportExtractor(
            imported.modulePath, true, modulePathClassification()::get);
        extractor.setImportModulePaths(importAliasMap);
        extractor.extract(imported.rawAst);
        Map<String, HostDeclarationSurface.DeclaredClass> classes =
            new LinkedHashMap<>();
        HostDeclarationSurface.DeclarationKind kind = isExternCModuleInfo(imported)
            ? HostDeclarationSurface.DeclarationKind.EXTERN_C
            : HostDeclarationSurface.DeclarationKind.HOST;
        for (StatementNode stmt : imported.rawAst.statements()) {
            ClassDeclaration cd = classDeclarationOf(stmt);
            if (cd == null) {
                continue;
            }
            List<HostDeclarationSurface.DeclaredField> fields =
                new ArrayList<>();
            for (ClassField cf : cd.fields()) {
                fields.add(new HostDeclarationSurface.DeclaredField(
                    cf, extractor.resolveFieldType(cf.type())));
            }
            classes.putIfAbsent(cd.name(),
                new HostDeclarationSurface.DeclaredClass(
                    cd.name(), kind, fields));
        }
        Map<String, Type> declaredExports = imported.exports != null
            ? imported.exports : Map.of();
        return new HostDeclarationSurface.DeclarationFacts(
            new ModuleId(imported.modulePath), kind, declaredExports,
            classes);
    }

    /**
     * The ISSUE-0328 host-module declaration record for one imported
     * declaration file (js-v12-host-abi-completion D1): the declared
     * export map plus, per class export name, the declaration AST's
     * {@link ClassField} records with their resolved declared types.
     * A declaration file never runs the phase-3 name-resolver pass, so
     * the field types resolve structurally through an
     * {@link ExportExtractor} over the declaration's own AST — the
     * same resolution the declaration's export signatures use — with
     * the declaration's import aliases mapped exactly like the
     * phase-1 extraction. A same-module class field type (e.g.
     * {@code endpoint: Endpoint} in {@code cfg.d.deal}) therefore
     * resolves to the declaring module's class identity, which the
     * JS emitter's descriptor service projects to the canonical
     * {@code @$external/&lt;specifier&gt;/&lt;ClassName&gt;} atom.
     *
     * <p>The facts are the host projection of the compilation's one
     * declaration surface (ISSUE-0630): the resolution runs once per
     * declaration module at the surface's production, so the retained
     * JS/JVM declared maps keep byte-identical facts.</p>
     */
    private HostModuleDeclarations hostDeclarationsOf(
            ModuleInfo imported) {
        HostDeclarationSurface.DeclarationFacts facts = hostDeclarationSurface
            .require(new ModuleId(imported.modulePath));
        Map<String, List<HostModuleDeclarations.HostField>> classFields =
            new LinkedHashMap<>();
        for (Map.Entry<String, HostDeclarationSurface.DeclaredClass> entry
                : facts.classes().entrySet()) {
            List<HostModuleDeclarations.HostField> fields =
                new ArrayList<>();
            for (HostDeclarationSurface.DeclaredField field
                    : entry.getValue().fields()) {
                fields.add(new HostModuleDeclarations.HostField(
                    field.declaration(), field.type()));
            }
            classFields.put(entry.getKey(), fields);
        }
        return new HostModuleDeclarations(facts.exports(), classFields);
    }

    /**
     * The source/generated path pair passed to
     * {@link SourceMapGenerator#toJson} for a JS sidecar — the exact
     * strings the Lua arm passes (LuaBackend.generateToFile's
     * project-relative normalization, mirrored verbatim): the source
     * path and the generated artifact path relativized against the
     * project root inferred as {@code outputRoot/../..} when the
     * relativization stays inside the project; otherwise the fallback
     * pair — the raw source path and the output-root-relative
     * generated path.
     */
    private static String[] sourceMapSidecarPaths(String sourcePath,
                                                  Path outputRoot,
                                                  Path outputPath) {
        String relSourcePath = sourcePath;
        String relGeneratedPath = outputRoot.relativize(outputPath).toString();

        try {
            Path absOutputRoot = outputRoot.toAbsolutePath().normalize();
            Path projectRoot = absOutputRoot.resolve("..").resolve("..").normalize();
            Path absSource = Path.of(sourcePath).toAbsolutePath();

            Path srcRel = projectRoot.relativize(absSource);
            if (!srcRel.startsWith("..")) {
                relSourcePath = srcRel.toString();
            }

            Path genRel = projectRoot.relativize(outputPath.toAbsolutePath());
            if (!genRel.startsWith("..")) {
                relGeneratedPath = genRel.toString();
            }
        } catch (IllegalArgumentException e) {
            // Keep fallback paths if relativization fails
        }

        return new String[] { relSourcePath, relGeneratedPath };
    }

    /**
     * True when the module is a spec-listed stdlib declaration module:
     * its published classification is
     * {@link CanonicalModuleIdentity.BuiltinModule} — the file-keyed
     * stdlib predicate over the six pinned declaration files under the
     * resolved {@code ProjectContext.stdlibSurfacePath} (D6 (1);
     * ISSUE-0269). Stdlib imports stay on the trusted raw-require path
     * (ISSUE-0082, host-module-abi D5(5)); a same-named file outside
     * the pinned surface is not builtin.
     */
    private boolean isSpecStdlibModuleInfo(ModuleInfo info) {
        return info.location.moduleClassification()
            instanceof CanonicalModuleIdentity.BuiltinModule;
    }

    private void copyRuntimeLibrary() throws IOException {
        // Whole-set semantics (whole-project-artifact-publication D3/D6):
        // the runtime copy always stages fresh from the resolved
        // distribution surface — the pinned three-tier order
        // (ISSUE-0457, D3): classpath resources, then the DEAL_HOME
        // filesystem layout, then the checkout CWD dev fallback
        // (no project-local location is pinned for the runtime) — and
        // the whole-set swap replaces any earlier bytes; no skip of an
        // existing destination remains.
        Optional<DistributionHome.ResolvedSource> runtime =
            stager.stageRuntimeCopy("deal/runtime.lua", distributionHome);
        if (runtime.isPresent()) {
            log("  Copied runtime: " + outputRoot.resolve("deal/runtime.lua")
                + " (" + runtime.get().tier() + ")");
            return;
        }

        // Anchorless site (D5/D6): the note names the missing runtime
        // library path.
        syntheticError(DiagnosticCode.E6000,
            "Runtime library not found: deal/runtime.lua", "",
            "missing anchor: runtime library path 'deal/runtime.lua'");
    }

    /**
     * Copies the spec-listed stdlib .lua implementation files to the
     * output. The module list is derived from the 6 spec-listed stdlib
     * modules. Each copy source resolves through {@link
     * DistributionHome} in the pinned three-tier order (ISSUE-0457,
     * {@code release-distribution-packaging-and-discovery} D3) —
     * project-local surface first, then the language distribution
     * (classpath resources, then the {@code DEAL_HOME} filesystem
     * layout), then the checkout CWD dev fallback — so a v1.2 project
     * shipping a local {@code std/} override stages its own bytes and
     * an out-of-checkout compile stages the distribution's bytes. A
     * module absent at every tier is skipped silently (unchanged).
     */
    private void copyStdlibModules() throws IOException {
        for (String stdlibModule : StdlibModuleResolver.SPEC_STDLIB_MODULES) {
            // Whole-set semantics (whole-project-artifact-publication
            // D3/D6): each stdlib copy stages fresh from the resolved
            // distribution surface — project-local surface first, then
            // the language distribution, then the checkout CWD dev
            // fallback — so a project-local std/ override stages its
            // own bytes and no skip of an existing destination remains.
            String name = stdlibModule.substring("std/".length());
            Optional<DistributionHome.ResolvedSource> source =
                stager.stageStdlibCopy(name, "lua", distributionHome);
            if (source.isEmpty()) {
                continue;
            }
            log("  Copied stdlib: " + stdlibModule + " ("
                + source.get().tier() + ")");
        }
    }

    /**
     * JS deployment copy (js-backend-emitter D10): copies deal/runtime.js
     * to <output>/deal/runtime.js — the resolved distribution surface,
     * else E6000 — staged fresh every compile (whole-set semantics; no
     * destination skip). The mirror of copyRuntimeLibrary with the .js
     * spelling.
     */
    private void copyJsRuntimeLibrary() throws IOException {
        // Whole-set semantics (whole-project-artifact-publication D3/D6):
        // the runtime copy always stages fresh from the resolved
        // distribution surface — the pinned three-tier order
        // (ISSUE-0457, D3) — and the whole-set swap replaces any
        // earlier bytes; no skip of an existing destination remains.
        Optional<DistributionHome.ResolvedSource> runtime =
            stager.stageRuntimeCopy("deal/runtime.js", distributionHome);
        if (runtime.isPresent()) {
            log("  Copied runtime: " + outputRoot.resolve("deal/runtime.js")
                + " (" + runtime.get().tier() + ")");
            return;
        }

        // Anchorless site (D5/D6): the note names the missing runtime
        // library path.
        syntheticError(DiagnosticCode.E6000,
            "Runtime library not found: deal/runtime.js", "",
            "missing anchor: runtime library path 'deal/runtime.js'");
    }

    /**
     * Copies the spec-listed stdlib .js implementation files to the
     * output (the module list is derived from the 6 spec-listed stdlib
     * modules). Each copy source resolves through {@link
     * DistributionHome} in the pinned three-tier order (ISSUE-0457) —
     * project-local surface first, then the language distribution
     * (classpath resources, then the {@code DEAL_HOME} filesystem
     * layout), then the checkout CWD dev fallback; a missing source for
     * a module is skipped silently. Staged fresh every compile
     * (whole-set semantics). The mirror of copyStdlibModules with the
     * .js spelling (js-backend-emitter D10).
     */
    private void copyStdlibJsModules() throws IOException {
        for (String stdlibModule : StdlibModuleResolver.SPEC_STDLIB_MODULES) {
            // Whole-set semantics (whole-project-artifact-publication
            // D3/D6): each stdlib copy stages fresh from the resolved
            // distribution surface — project-local surface first, then
            // the language distribution, then the checkout CWD dev
            // fallback — and no skip of an existing destination remains.
            String name = stdlibModule.substring("std/".length());
            Optional<DistributionHome.ResolvedSource> source =
                stager.stageStdlibCopy(name, "js", distributionHome);
            if (source.isEmpty()) {
                continue;
            }
            log("  Copied stdlib: " + stdlibModule + " ("
                + source.get().tier() + ")");
        }
    }

    // =========================================================================
    // IR dump helper
    // =========================================================================

    /**
     * Stages an IR dump string into the publication staging tree (D1/D5):
     * the file is placed at {@code <outputRoot>/<module-path>.ir.txt}
     * after a successful publish, and appears atomically with the set —
     * dumps of a failed compilation are discarded with the stage tree
     * and never reach the live root (today's phases 1/3 dumps wrote the
     * live root directly). A staging write failure records the pinned
     * publish diagnostic (D4); the {@link IrDumper} failure diagnostic
     * (E6001) stays with the callers' exception handling.
     */
    private void writeIrDump(String modulePath, String irText) {
        if (pendingStageFailure != null) {
            return; // a staging failure already recorded: nothing more stages
        }
        String filePath = modulePath.replace('.', '/') + ".ir.txt";
        try {
            stager.stage(filePath, irText.getBytes(StandardCharsets.UTF_8));
        } catch (IOException stagingFailure) {
            stageFailure(stagingFailure);
            return;
        }
        log("  IR dumped: " + outputRoot.resolve(filePath));
    }

    // =========================================================================
    // Import resolution
    // =========================================================================

    /**
     * Resolves an import path to a source file.  Emits E2003 if
     * resolution fails; without an import declaration span the re-emission
     * is synthetic with an anchor note naming the import path (D5).
     *
     * @return the resolved source path, or {@code null} if not found
     */
    /**
     * Resolves an import path to a source file through the T6 resolver
     * (the pinned five rules — no legacy buildCandidates, no CWD
     * bare-lookup fallback, no classpath module fallback). A failed
     * resolution merges its E2003/E2009 diagnostic at the canonical
     * synthetic shape plus anchor note when no import declaration span
     * is available.
     *
     * @return the resolved source path (the location's
     *         {@code normalizedSourcePath}), or {@code null} if not found
     */
    public String resolveImportPath(String importPath, Path fromFile) {
        return resolveImportPath(importPath, fromFile, null);
    }

    /**
     * Resolves an import path to a source file through the T6 resolver,
     * anchoring any failure diagnostic at the given import declaration
     * span when present, falling back to the canonical synthetic shape
     * plus the anchor note (D5).
     */
    private String resolveImportPath(String importPath, Path fromFile,
                                      Span importSpan) {
        Span anchor = importSpan != null
            ? importSpan : Span.synthetic(fromFile.toString());
        SourceModuleResolver.ResolveResult result =
            sourceResolver.resolve(fromFile.toString(), importPath, anchor);
        if (result instanceof SourceModuleResolver.ResolveResult.Resolved r) {
            locations.putIfAbsent(r.location().normalizedSourcePath(),
                r.location());
            return r.location().normalizedSourcePath();
        }
        CompilerDiagnostic failure =
            ((SourceModuleResolver.ResolveResult.Failure) result).diagnostic();
        String key = fromFile + "|" + importPath;
        if (reportedResolveFailures.add(key)) {
            diagnostics.add(failure);
            hasErrors = true;
        }
        return null;
    }

    /**
     * The import-resolution failures already merged into
     * {@link #diagnostics()} (importer path ‖ specifier), so a
     * re-resolution of the same import in a later phase never
     * duplicates a diagnostic.
     */
    private final Set<String> reportedResolveFailures = new HashSet<>();

    // =========================================================================
    // Canonical module-identity classification (js-v12-completion-architecture D3)
    // =========================================================================

    /**
     * The canonical public module identity of one compiled module, per
     * the identity layer's classification (design source
     * {@code strict-project-context-resolution-identity} D6):
     * externals-listed declarations carry
     * {@code ExternalModule(rawImportSpecifier)} (the manifest key
     * exactly as written), spec stdlib modules carry
     * {@code BuiltinModule}, and a configured root-contained source
     * module carries {@code ProjectModule(configuredRootText,
     * relativeModuleComponents)} — the T6 resolver's file-keyed
     * classification published on the module's
     * {@link SourceModuleLocation} (ISSUE-0269; the legacy
     * specifier-keyed externalsDeclarations/externalsModulePaths maps
     * and the lossy bestRootIndex computation are retired).
     * {@code null} means the module has no public identity (an
     * out-of-root relative source): class-free code stays valid, and a
     * class there fails closed at descriptor production.
     */
    private CanonicalModuleIdentity classifyModuleIdentity(ModuleInfo info) {
        if (info.location == null) {
            return null;
        }
        return info.location.moduleClassification();
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private void log(String msg) {
        if (verbose) System.out.println(msg);
    }

    private void error(DiagnosticCode code, String message, DiagnosticRange range) {
        diagnostics.add(CompilerDiagnostic.error(code, message, range));
        hasErrors = true;
    }

    /** Span overload: {@code span.range()}; a SYNTHETIC conversion
     * appends the mandatory D4 anchor note. */
    private void error(DiagnosticCode code, String message, Span span) {
        diagnostics.add(CompilerDiagnostic.error(code, message, span));
        hasErrors = true;
    }

    /** Explicit synthetic factory with a construct-naming anchor note (D6). */
    private void syntheticError(DiagnosticCode code, String message, String file,
                                String missingAnchorNote) {
        diagnostics.add(CompilerDiagnostic.syntheticError(code, message, file,
            missingAnchorNote));
        hasErrors = true;
    }

    /**
     * Delegates printing to the canonical formatter (D8) over the D1
     * canonical report order (deterministic-diagnostics): the stderr
     * diagnostic blocks appear in the canonical total order while the
     * internal collection order is unchanged; the error/warning summary
     * counts are computed over the internal list exactly as before.
     */
    private void printDiagnostics() {
        for (CompilerDiagnostic d : DiagnosticOrder.canonical(diagnostics)) {
            System.err.println(DiagnosticFormatter.format(d));
        }
        long errorCount = diagnostics.stream()
            .filter(d -> "error".equals(d.severity())).count();
        long warnCount = diagnostics.stream()
            .filter(d -> "warning".equals(d.severity())).count();
        System.err.println(errorCount + " error(s), " + warnCount + " warning(s)");
    }

    // =========================================================================
    // ModuleResolverImpl
    // =========================================================================

    final class ModuleResolverImpl implements ModuleResolver {

        private final Map<String, ModuleInfo> modules;
        /**
         * The lazily built name resolvers over declaration-file modules
         * (keyed by dotted module path): declaration files skip the
         * phase-3 name-resolution pass, so a cross-module class-field
         * type annotation declared by a host declaration resolves
         * through a resolver built on demand over the declaration's own
         * AST (ISSUE-0328 — the frontend's shared host-class symbol
         * synthesis). Each resolver is cached before its
         * {@link NameResolver#resolve} completes so declaration-only
         * import cycles terminate.
         */
        private final Map<String, NameResolver> declarationResolvers =
            new HashMap<>();

        ModuleResolverImpl(Map<String, ModuleInfo> modules,
                           List<CompilerDiagnostic> diagnostics) {
            this.modules = modules;
        }

        @Override
        public Map<String, Type> resolveModule(String modulePath,
                                                String importingModule,
                                                Set<String> modulesInProgress)
                throws ModuleNotFoundException,
                    CffiImportWithoutNativeLibraryException {
            // Direct internal-name match first: the checker passes dotted
            // module paths carried by Type.Class values (e.g. an
            // externals module's "host.x\y"), which are internal names,
            // never import specifiers.
            for (ModuleInfo info : modules.values()) {
                if (info.modulePath.equals(modulePath)) {
                    return cffiManifestCheckedExports(info, modulePath);
                }
            }
            // Otherwise modulePath is the import specifier exactly as
            // written (e.g. "./lib", "std/console", "host/cfg");
            // importingModule is the importing module's internal dotted
            // module name. The T6 resolver derives the resolved source
            // from the importer's source path, so the importer must be
            // located by its internal name first.
            String importerSource = sourcePathForInternalName(importingModule);
            if (importerSource == null && modules.containsKey(importingModule)) {
                // Defensive: an importingModule spelled as a source path.
                importerSource = importingModule;
            }
            if (importerSource == null) {
                throw new ModuleNotFoundException(
                    "Module not found: " + modulePath);
            }
            SourceModuleResolver.ResolveResult result = sourceResolver.resolve(
                importerSource, modulePath, Span.synthetic(importerSource));
            if (result instanceof SourceModuleResolver.ResolveResult.Resolved r) {
                ModuleInfo target = modules.get(
                    r.location().normalizedSourcePath());
                if (target != null) {
                    return cffiManifestCheckedExports(target, modulePath);
                }
            }
            throw new ModuleNotFoundException("Module not found: " + modulePath);
        }

        /**
         * The v1.2 C FFI manifest policy (docs/spec-v1.2.md:1891): a C
         * FFI declaration file — a {@code .d.deal} file whose effective
         * {@link FileDirectives#externC()} holds — may only be imported
         * through a {@code deal.json} externals entry that declares the
         * file with a classified {@code nativeLibrary}. The resolved
         * target's module classification is
         * {@code ExternalModule(rawImportSpecifier)} exactly when an
         * externals entry declares the file (file-keyed,
         * {@code ModuleIdentityResolver} D6 rule (2)); no entry at all
         * is always the invalid-manifest-policy rejection, and a
         * manifest-authored entry without {@code nativeLibrary} is the
         * rejection too (the test-only isolated-phase constructors
         * synthesize their entries from the harness's declarations map,
         * which cannot carry {@code nativeLibrary}, and their entries
         * count as backed — see {@link #cffiManifestBacked(ModuleInfo)}).
         * The checker maps the exception to E2010 at the import span
         * ({@code deal/checker/NameResolver.java},
         * {@code processImport}) — the production emission site behind
         * the promoted conformance pin.
         */
        private Map<String, Type> cffiManifestCheckedExports(
                ModuleInfo target, String importSpecifier)
                throws CffiImportWithoutNativeLibraryException {
            if (target.isDeclarationFile && target.rawAst != null
                    && target.rawAst.fileDirectives().externC()
                    && !cffiManifestBacked(target)) {
                throw new CffiImportWithoutNativeLibraryException(
                    importSpecifier);
            }
            return target.exports != null ? target.exports : Map.of();
        }

        /**
         * True when the externals entry that declares the target
         * (file-keyed classification) satisfies the v1.2 C FFI manifest
         * policy; false when no entry declares the file, or when a
         * manifest-authored entry omits {@code nativeLibrary}.
         *
         * <p>The {@code nativeLibrary} authoring rule
         * (docs/spec-v1.2.md:1891 — "a C FFI entry must include
         * nativeLibrary") applies to manifest-authored contexts: the
         * production locator path parses the entry's classified
         * {@code nativeLibrary}, and an entry that omits it is the
         * E2010 invalid-manifest-policy rejection. The test-only
         * isolated-phase constructors synthesize their externals
         * entries from the harness's declarations map, which cannot
         * carry {@code nativeLibrary}; there the harness's explicit
         * entry is the authority channel and counts as backed.</p>
         */
        private boolean cffiManifestBacked(ModuleInfo target) {
            CanonicalModuleIdentity classification = target.location == null
                ? null : target.location.moduleClassification();
            if (!(classification
                    instanceof CanonicalModuleIdentity.ExternalModule ext)) {
                return false;
            }
            ExternalEntry entry = context.externals().get(
                ext.rawImportSpecifier());
            if (entry == null) {
                return false;
            }
            return manifestAuthoredContext
                ? entry.nativeLibrary() != null
                : true;
        }

        /**
         * The source path of the module whose internal dotted name is
         * {@code internalName}, or null.
         */
        private String sourcePathForInternalName(String internalName) {
            for (ModuleInfo info : modules.values()) {
                if (info.modulePath.equals(internalName)) {
                    return info.sourcePath;
                }
            }
            return null;
        }

        @Override
        public Symbol.ClassSymbol resolveClassSymbol(String className,
                                                      String modulePath,
                                                      String importingModule)
                throws ModuleNotFoundException {
            for (ModuleInfo info : modules.values()) {
                if (info.modulePath.equals(modulePath)) {
                    if (info.symbolTable != null) {
                        Symbol sym = info.symbolTable.resolve(className);
                        if (sym instanceof Symbol.ClassSymbol cs) return cs;
                        return null;
                    }
                    // Host declaration synthesis (ISSUE-0328,
                    // js-v12-host-abi-completion D3): a declaration
                    // file carries no symbol table, so its declared
                    // classes synthesize as ClassSymbols straight from
                    // the declaration AST — DEAL-side construction and
                    // field reads of a declared host class type-check
                    // against the declaration's field records, and the
                    // checker's cross-module field-type resolution runs
                    // against the declaring module's own context (the
                    // resolveTypeNodeInModule override below).
                    for (StatementNode stmt : info.rawAst.statements()) {
                        ClassDeclaration cd = null;
                        if (stmt instanceof ClassDeclaration c) {
                            cd = c;
                        } else if (stmt instanceof ExportDeclaration ed
                                && ed.declaration()
                                    instanceof ClassDeclaration c) {
                            cd = c;
                        }
                        if (cd != null && cd.name().equals(className)) {
                            CanonicalModuleIdentity moduleIdentity =
                                classifyModuleIdentity(info);
                            if (moduleIdentity == null) {
                                throw new IllegalStateException(
                                    "no canonical public module identity for"
                                        + " host declaration module '"
                                        + info.modulePath
                                        + "': its declared classes can never"
                                        + " carry an identity (internal"
                                        + " invariant violation)");
                            }
                            return new Symbol.ClassSymbol(cd.name(),
                                cd.fields(), info.modulePath,
                                new CanonicalClassIdentity(moduleIdentity,
                                    cd.name()));
                        }
                    }
                    return null;
                }
            }
            return null;
        }

        @Override
        public Symbol.ClassSymbol resolveClassSymbol(String className,
                CanonicalModuleIdentity declaringModule,
                String importingModule)
                throws ModuleNotFoundException {
            // v1.2 identity carriage: imported classes carry the declaring
            // source's identity; route on the module-identity
            // classification (the same single classifier the identity
            // surface consumes).
            for (ModuleInfo info : modules.values()) {
                CanonicalModuleIdentity identity =
                    classifyModuleIdentity(info);
                if (identity == null || !identity.equals(declaringModule)) {
                    continue;
                }
                if (info.symbolTable != null) {
                    Symbol sym = info.symbolTable.resolve(className);
                    if (sym instanceof Symbol.ClassSymbol cs) return cs;
                    // Two files in one directory share the module
                    // identity; the declaring file's table may live in a
                    // later module — keep scanning.
                    continue;
                }
                // Host declaration synthesis (the modulePath-keyed path's
                // counterpart): declared classes of an externals-listed
                // declaration carry the externals identity.
                for (StatementNode stmt : info.rawAst.statements()) {
                    ClassDeclaration cd = null;
                    if (stmt instanceof ClassDeclaration c) {
                        cd = c;
                    } else if (stmt instanceof ExportDeclaration ed
                            && ed.declaration()
                                instanceof ClassDeclaration c) {
                        cd = c;
                    }
                    if (cd != null && cd.name().equals(className)) {
                        return new Symbol.ClassSymbol(cd.name(),
                            cd.fields(), info.modulePath,
                            new CanonicalClassIdentity(identity,
                                cd.name()));
                    }
                }
                // Two files in one directory share the module identity;
                // keep scanning for the declaring module.
                continue;
            }
            return null;
        }

        @Override
        public boolean isFunctionExportedFromModule(
                CanonicalModuleIdentity declaringModule,
                String functionName, String importingModule)
                throws ModuleNotFoundException {
            // v1.2 identity carriage: route on the module-identity
            // classification; the declaring module's exports map answers
            // the jsonable synthetic-export queries.
            for (ModuleInfo info : modules.values()) {
                CanonicalModuleIdentity identity =
                    classifyModuleIdentity(info);
                if (identity != null && identity.equals(declaringModule)
                        && info.exports != null
                        && info.exports.containsKey(functionName)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Resolves a type node against the owning module's own
         * name-resolved scope — the phase-3 dependency order guarantees
         * the owner's {@link #typeCheckAll} turn (and therefore its
         * {@code NameResolver}) completed before any importer checks,
         * so the importer's cross-module class-field type annotations
         * (e.g. {@code children: Child[]} declared in a companion)
         * resolve against the declaring module instead of silently
         * falling back to the importing module's scope where the bare
         * class name is unknown ({@code Type.Error} facts). An
         * unresolved owner type ({@code Type.Error}) returns
         * {@code null} so the caller keeps its documented local
         * fallback; a declaration-file owner has no name resolver and
         * returns {@code null} the same way.
         */
        @Override
        public Type resolveTypeNodeInModule(TypeNode typeNode,
                                            String modulePath,
                                            String importingModule)
                throws ModuleNotFoundException {
            for (ModuleInfo info : modules.values()) {
                if (info.modulePath.equals(modulePath)) {
                    if (info.nameResolver != null) {
                        Type resolved =
                            info.nameResolver.resolveTypeNode(typeNode);
                        return resolved == Type.Error.INSTANCE
                            ? null : resolved;
                    }
                    // Declaration-file owner (ISSUE-0328): resolve
                    // through the lazily built resolver over the
                    // declaration's own AST, so a bare same-module
                    // class name inside a host class field type
                    // resolves against the declaring module — never
                    // against the importing module's scope.
                    Type resolved = declarationResolver(info)
                        .resolveTypeNode(typeNode);
                    return resolved == Type.Error.INSTANCE
                        ? null : resolved;
                }
            }
            return null;
        }

        /**
         * The cached name resolver over one declaration-file module,
         * built on demand (ISSUE-0328 host-class symbol synthesis).
         * The resolver is cached before its resolve completes so
         * declaration-only import cycles terminate; its own import
         * resolution runs through this same module resolver.
         */
        private NameResolver declarationResolver(ModuleInfo info) {
            NameResolver cached = declarationResolvers.get(info.modulePath);
            if (cached != null) {
                return cached;
            }
            // v1.2 identity carriage: the declaration's classes carry the
            // compilation's classification identities (externals/builtin),
            // never the standalone dotted-path default — the synthesized
            // host-class field types must carry the same identity the
            // host-class symbols carry.
            NameResolver built = new NameResolver(info.modulePath, this,
                new HashSet<>(), modulePathClassification()::get);
            declarationResolvers.put(info.modulePath, built);
            built.resolve(info.rawAst);
            return built;
        }
    }
}
