package deal.module;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.publication.PublicationStager;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticCapability;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The one self-contained production project emission unit (ISSUE-0642;
 * design source
 * {@code production-project-emission-and-atomic-cutover} P5/P6/P7/P9/P11
 * and the production-arm, source-map, and fail-closed producer-guard
 * contracts; {@code luajit-jvm-single-lowering-production-cutover}
 * C3/C4/C5/C7/C8/C9).
 *
 * <p>One compile through this unit does exactly:</p>
 *
 * <ol>
 *   <li>the C9 source-map warning (the pinned per-target text on stderr,
 *       once, before emission, only for an explicit {@code --source-map}
 *       request) — no sidecar is ever staged by this unit;</li>
 *   <li>the closure guard's whole-closure step over the closure's
 *       resolved import facts, before the lowering: every HOST-kind
 *       declaration import is realized — the {@code HOST} declaration
 *       kind by the emitted host load of the module init walk
 *       (ISSUE-0656) and the {@code EXTERN_C} declaration kind by the
 *       emitted {@code __rt.load_ffi} prelude selected from this
 *       slice's FFI emission input — so the step carries no HOST-kind
 *       shape and the same code path admits both declaration kinds. Its
 *       stable {@code HOST_MODULE_IMPORT} E6005 {@code
 *       SHARED_EMITTER_COVERAGE} producer, its whole-closure property,
 *       and its pre-lowering position stay landed (a superseded shape
 *       is replaced, never deleted); {@code STDLIB}/{@code COMPILED}
 *       imports pass;</li>
 *   <li>exactly one project lowering over the compile's declared inputs
 *       (the invocation, the checked project and interface index, the
 *       requirement manifests, the declaration surface, the declaration
 *       module identities, the extern-C generated modules, the builtin
 *       {@code Error} declaration, the conversion intrinsics, and the
 *       production callback set); a failing lowering returns the first
 *       E6005 and stages nothing;</li>
 *   <li>exactly one emission per target: the LuaJIT production project
 *       chunk (one chunk named for the entry module, staged at the entry
 *       module path with {@code '.'} replaced by {@code '/'} plus
 *       {@code .lua}) — carrying the compile's FFI emission input (the
 *       extern-C generated-module metadata and the manifest-directory
 *       text) so an extern-C declaration import emits its
 *       {@code __rt.load_ffi} prelude at the owning
 *       {@code MODULE_IMPORT} — or the JVM production project class (one
 *       {@code public final class}, staged at
 *       {@code JvmBackend.classNameFor(entryModule.path()) + ".java"});
 *       the JVM production entry takes no FFI emission input (a JVM
 *       compile never publishes FFI metadata); an emitter gap (an op
 *       outside the landed production set, an extern-C import without
 *       generated metadata, an unserializable generated module, or a
 *       provider gap) maps to E6005 {@code SHARED_EMITTER_COVERAGE} and
 *       stages nothing — the provider gap through its typed signal, so
 *       the E6005 detail names the consuming (emitting) module, the
 *       extern-C import statement's origin, the raw specifier, the
 *       resolved declaration module, and the offending provider alias
 *       and module;</li>
 *   <li>the unchanged LuaJIT runtime/stdlib deployment copies, staged
 *       from the resolved distribution surface after the one project
 *       artifact (a missing runtime is the pinned E6000); the JVM target
 *       stages no deployment copy, exactly as before.</li>
 * </ol>
 *
 * <p><b>Unreachability.</b> This unit reads no routing state, no
 * capability registry, no planner, no retained backend {@code generate*}
 * entry point, and no retained emission counter: it depends on the
 * frontend's checked facts, the one lowering, the two production
 * emitters, the distribution resolver, and the staging surface only. A
 * lowering, guard, or emission failure stages nothing and leaves the
 * previous artifact set untouched (the caller's unchanged publication
 * transaction owns the atomic swap); there is no retry and no fallback
 * to a retained emitter.</p>
 */
public final class ProductionProjectEmission {

    /** The registered rule ID of every emitter-coverage failure. */
    public static final String SHARED_EMITTER_COVERAGE = "SHARED_EMITTER_COVERAGE";

    /**
     * The stable guard detail token of the narrowed extern-C
     * declaration-import remnant (ISSUE-0656;
     * {@code host-module-load-and-host-call-realization} H6 and the
     * extern-C remnant contract).
     */
    public static final String HOST_MODULE_IMPORT = "HOST_MODULE_IMPORT";

    /**
     * The stable detail token of the FFI provider-gap outcome (the
     * extern-C load emission's binding step; design source
     * {@code plan-evaluator-provider-binding-surface} P4 and the
     * provider-gap fail-closed contract): a wrapper-incapable provider or
     * an import alias naming two provider modules fails the compile closed
     * with one E6005 {@code SHARED_EMITTER_COVERAGE} whose detail names the
     * consuming module, the extern-C import statement's origin, the
     * import's raw specifier, the resolved declaration module, and the
     * offending provider alias and module path.
     */
    public static final String FFI_PROVIDER_GAP = "FFI_PROVIDER_GAP";

    /** The pinned C9 warning of the LuaJIT target (printed verbatim). */
    public static final String WARNING_LUAJIT =
        "Warning: --source-map produces no source-map sidecars with the LuaJIT"
            + " project emission (source maps are LuaJIT/JVM-unavailable in this"
            + " release)";

    /** The pinned C9 warning of the JVM target (printed verbatim). */
    public static final String WARNING_JVM =
        "Warning: --source-map produces no source-map sidecars with the JVM"
            + " project emission (source maps are LuaJIT/JVM-unavailable in this"
            + " release)";

    /** The unchanged LuaJIT runtime deployment copy source name. */
    private static final String RUNTIME_LUA = "deal/runtime.lua";

    private ProductionProjectEmission() {
        // Static production entry only; no instances.
    }

    /** The two outcomes of one production arm run. */
    public enum Outcome {
        /** The one project artifact (and the LuaJIT copies) staged. */
        EMITTED,
        /** Nothing staged; the carried E6005/E6000 is the compile failure. */
        FAILED
    }

    /**
     * The outcome of one production arm run: {@link Outcome#EMITTED} with
     * the one staged project artifact's relative path and no diagnostic,
     * or {@link Outcome#FAILED} with exactly the first diagnostic and no
     * staged artifact.
     *
     * @param outcome               the run outcome; non-null
     * @param diagnostics           the compile-failing diagnostics (empty
     *                              exactly on success); non-null
     * @param artifactRelativePath  the one staged project artifact's
     *                              relative path; null exactly on failure
     */
    public record Result(
            Outcome outcome,
            List<CompilerDiagnostic> diagnostics,
            String artifactRelativePath) {

        public Result {
            Objects.requireNonNull(outcome, "outcome must not be null");
            Objects.requireNonNull(diagnostics, "diagnostics must not be null");
            diagnostics = List.copyOf(diagnostics);
            if (outcome == Outcome.EMITTED
                    && (!diagnostics.isEmpty() || artifactRelativePath == null)) {
                throw new IllegalArgumentException(
                    "an emitted production run carries the one project artifact"
                        + " path and no diagnostic");
            }
            if (outcome == Outcome.FAILED
                    && (diagnostics.isEmpty() || artifactRelativePath != null)) {
                throw new IllegalArgumentException(
                    "a failed production run carries at least one diagnostic and"
                        + " no artifact path");
            }
        }

        /** Whether the run staged the one project artifact. */
        public boolean emitted() {
            return outcome == Outcome.EMITTED;
        }

        /** The first diagnostic, or {@code null} when the run emitted. */
        public CompilerDiagnostic firstDiagnostic() {
            return diagnostics.isEmpty() ? null : diagnostics.get(0);
        }
    }

    /**
     * Runs the production arm for one release-owned production compile:
     * the C9 warning, the closure guard's whole-closure step (both
     * HOST-kind declaration kinds admitted and realized) over the
     * closure's resolved import facts, the one project lowering, the one
     * emission, the one staged project
     * artifact, and the unchanged LuaJIT deployment copies. The caller
     * (the phase-4 dispatch) owns the arm selection, the emission record,
     * and the publication transaction; this unit stages artifacts only.
     *
     * @param invocation                  the release-owned production
     *                                    invocation (the lowering
     *                                    profile/registry guard);
     *                                    non-null
     * @param checkedProject              the checked implementation
     *                                    closure in dependency order;
     *                                    non-null
     * @param interfaceIndex              the project interface index;
     *                                    non-null
     * @param requirementManifests        the per-module requirement
     *                                    manifests; non-null
     * @param declarationSurface          the declaration surface covering
     *                                    every declaration import;
     *                                    non-null
     * @param declarationModuleIdentities the compile's module-path
     *                                    classification keyed by module
     *                                    identity; non-null
     * @param externCModules              the validated extern-C generated
     *                                    modules; non-null
     * @param manifestDirectory           the compile's manifest-directory
     *                                    text (the base of
     *                                    manifest-relative native-library
     *                                    loader-text resolution and the
     *                                    second FFI emission input)
     *                                    non-null
     * @param builtinError                the compiler-owned builtin
     *                                    {@code Error} declaration;
     *                                    non-null
     * @param conversionIntrinsics        the closed conversion intrinsics;
     *                                    non-null
     * @param callbackExports             the production callback set
     *                                    (empty for the production arm);
     *                                    non-null
     * @param backend                     the compile's target, LuaJIT or
     *                                    JVM; non-null
     * @param sourceMapExplicit           whether {@code --source-map} was
     *                                    explicitly requested (the C9
     *                                    warning fires exactly then;
     *                                    a {@code --dump-ir}-derived flag
     *                                    prints nothing)
     * @param distributionHome            the deployment-copy source
     *                                    resolver of this compile;
     *                                    non-null
     * @param stager                      the compile's staging surface;
     *                                    non-null
     * @return the run outcome
     * @throws IOException              on a staging write failure (the
     *                                  caller's pinned publication
     *                                  diagnostic owns it; nothing
     *                                  publishes)
     * @throws IllegalArgumentException when the backend is not
     *                                  {@code LUAJIT} or {@code JVM} (the
     *                                  JS arm is a separate, unchanged
     *                                  pipeline)
     */
    public static Result run(
            CompilerInvocation invocation,
            CheckedProjectInput checkedProject,
            ProjectInterfaceIndex interfaceIndex,
            List<SemanticRequirementManifest> requirementManifests,
            HostDeclarationSurface declarationSurface,
            Map<ModuleId, CanonicalModuleIdentity> declarationModuleIdentities,
            Map<ModuleId, FfiGeneratedModule> externCModules,
            String manifestDirectory,
            BuiltinErrorDeclaration builtinError,
            List<IntrinsicKind> conversionIntrinsics,
            Set<String> callbackExports,
            Backend backend,
            boolean sourceMapExplicit,
            DistributionHome distributionHome,
            PublicationStager stager) throws IOException {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(checkedProject, "checkedProject must not be null");
        Objects.requireNonNull(interfaceIndex, "interfaceIndex must not be null");
        Objects.requireNonNull(requirementManifests,
            "requirementManifests must not be null");
        Objects.requireNonNull(declarationSurface,
            "declarationSurface must not be null");
        Objects.requireNonNull(declarationModuleIdentities,
            "declarationModuleIdentities must not be null");
        Objects.requireNonNull(externCModules, "externCModules must not be null");
        Objects.requireNonNull(manifestDirectory,
            "manifestDirectory must not be null");
        Objects.requireNonNull(builtinError, "builtinError must not be null");
        Objects.requireNonNull(conversionIntrinsics,
            "conversionIntrinsics must not be null");
        Objects.requireNonNull(callbackExports, "callbackExports must not be null");
        Objects.requireNonNull(backend, "backend must not be null");
        Objects.requireNonNull(distributionHome, "distributionHome must not be null");
        Objects.requireNonNull(stager, "stager must not be null");
        if (backend != Backend.LUAJIT && backend != Backend.JVM) {
            throw new IllegalArgumentException(
                "the production project emission targets LuaJIT or JVM only; got "
                    + backend);
        }

        // (1) The C9 disposition: the pinned warning once, before emission,
        // only for an explicit --source-map request; this unit never stages
        // a .deal.map.json sidecar.
        if (sourceMapExplicit) {
            System.err.println(backend == Backend.JVM ? WARNING_JVM : WARNING_LUAJIT);
        }

        // (2) The closure guard's whole-closure step: every HOST-kind
        // declaration import of a checked closure is realized — the HOST
        // declaration kind by the emitted host load of the module init
        // walk (ISSUE-0656/H6), the EXTERN_C declaration kind by the
        // emitted __rt.load_ffi prelude selected from this slice's FFI
        // emission input (F1/F2) — so the step carries no HOST-kind shape
        // and the same code path admits both. The step keeps its
        // pre-lowering position and its whole-closure property: it reads
        // the closure's resolved import facts plus the declaration
        // surface, so a residual shape could never be masked by a
        // construct whose lowering fails first. An import the surface
        // does not cover is the lowering's DECLARATION_SURFACE_INCOMPLETE
        // agreement; this guard never defaults a missing fact. The stable
        // HOST_MODULE_IMPORT E6005 SHARED_EMITTER_COVERAGE producer stays
        // landed (a superseded shape is replaced, never deleted).
        Optional<CompilerDiagnostic> hostImport =
            hostImportGuard(checkedProject, declarationSurface, invocation);
        if (hostImport.isPresent()) {
            return new Result(Outcome.FAILED, List.of(hostImport.get()), null);
        }

        // (3) The one project lowering over the compile's declared inputs.
        // A failure returns the lowering's first E6005 and stages nothing;
        // no retry and no fallback exist.
        SemanticLowerer.ProjectLoweringResult lowering = SemanticLowerer.lowerProject(
            invocation, checkedProject, interfaceIndex, requirementManifests,
            declarationSurface, declarationModuleIdentities, externCModules,
            builtinError, conversionIntrinsics, callbackExports);
        if (lowering.hasErrors()) {
            return new Result(Outcome.FAILED, lowering.diagnostics(), null);
        }
        ExecutableLoweredProject project = lowering.project();

        // (4) The one emission per target, then the one staged project
        // artifact. An emitter gap is E6005 SHARED_EMITTER_COVERAGE and
        // stages nothing.
        String artifactRelativePath;
        String artifactSource;
        if (backend == Backend.JVM) {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission;
            try {
                emission = JvmSemanticEmitter.emitProductionProject(project,
                    lowering.tables(), lowering.registries(), className,
                    declarationSurface);
            } catch (IllegalStateException emitterGap) {
                return new Result(Outcome.FAILED,
                    List.of(sharedEmitterCoverage(project.entryModule().path(),
                        emitterGap, invocation)), null);
            }
            artifactRelativePath = className + ".java";
            artifactSource = emission.source();
        } else {
            String source;
            try {
                source = LuaSemanticEmitter.emitProductionProject(project,
                    lowering.tables(), lowering.registries(),
                    declarationSurface,
                    new FfiEmissionInput(externCModules, manifestDirectory));
            } catch (IllegalStateException emitterGap) {
                return new Result(Outcome.FAILED,
                    List.of(sharedEmitterCoverage(project.entryModule().path(),
                        emitterGap, invocation)), null);
            }
            artifactRelativePath =
                project.entryModule().path().replace('.', '/') + ".lua";
            artifactSource = source;
        }
        stager.stage(artifactRelativePath,
            artifactSource.getBytes(StandardCharsets.UTF_8));

        // (5) The unchanged LuaJIT deployment copies, staged from the
        // resolved distribution surface after the one project artifact. A
        // missing runtime is the pinned E6000; an absent stdlib module is
        // skipped silently (unchanged omission semantics). The JVM target
        // stages no deployment copy.
        if (backend == Backend.LUAJIT) {
            Optional<DistributionHome.ResolvedSource> runtime =
                stager.stageRuntimeCopy(RUNTIME_LUA, distributionHome);
            if (runtime.isEmpty()) {
                return new Result(Outcome.FAILED,
                    List.of(runtimeLibraryMissing()), null);
            }
            for (String stdlibModule : StdlibModuleResolver.SPEC_STDLIB_MODULES) {
                stager.stageStdlibCopy(
                    stdlibModule.substring("std/".length()), "lua",
                    distributionHome);
            }
        }
        return new Result(Outcome.EMITTED, List.of(), artifactRelativePath);
    }

    /**
     * The closure guard's whole-closure step over the closure's resolved
     * import facts: after the calls child realized the {@code HOST}
     * declaration kind (ISSUE-0656/H6) and this slice admits the
     * {@code EXTERN_C} declaration kind, the guard carries no HOST-kind
     * shape — every HOST-kind module import of a checked closure is
     * realized by an emitted load, {@code __rt.load_host} for the
     * {@code HOST} declaration kind and {@code __rt.load_ffi} for the
     * {@code EXTERN_C} one (the latter selected from this slice's FFI
     * emission input) — so the same code path admits both and no import
     * fails the closure here. The step, its whole-closure property, its
     * pre-lowering position, the stable {@link #HOST_MODULE_IMPORT}
     * token, and the E6005 {@code SHARED_EMITTER_COVERAGE} producer stay
     * landed (a superseded shape is replaced, never deleted). An import
     * whose resolved module carries no declaration-surface entry is not
     * classified here: the lowering's
     * {@code DECLARATION_SURFACE_INCOMPLETE} agreement step fails such a
     * closure closed (producer defect), so the guard never defaults a
     * missing fact. A {@code STDLIB}/{@code COMPILED} import passes;
     * their {@code MODULE_IMPORT} no-op is the landed realization (the
     * closure's own module walks realize a compiled dependency, and the
     * runtime supplies the stdlib surface).
     */
    private static Optional<CompilerDiagnostic> hostImportGuard(
            CheckedProjectInput checkedProject,
            HostDeclarationSurface declarationSurface,
            CompilerInvocation invocation) {
        for (CheckedModuleInput module : checkedProject.modules()) {
            for (ResolvedImport importFact : module.imports()) {
                if (importFact.kind() != ExternalModuleKind.HOST) {
                    continue;
                }
                if (!declarationSurface.modules()
                        .containsKey(importFact.resolvedModuleId())) {
                    // An uncovered declaration import: the lowering's
                    // declaration-fact agreement reports it; this guard
                    // never defaults a missing fact.
                    continue;
                }
                // A covered HOST-kind import is realized by an emitted
                // load — the HOST declaration kind by ISSUE-0656's host
                // load, the EXTERN_C declaration kind by this slice's FFI
                // load — so no HOST-kind shape remains and no import
                // fails the closure here.
            }
        }
        return Optional.empty();
    }

    /**
     * The retained E6005 {@code SHARED_EMITTER_COVERAGE} text of the
     * closure guard's stable {@link #HOST_MODULE_IMPORT} outcome (the
     * emitting module, the import's raw specifier, and the resolved
     * module). After the calls child's realization (ISSUE-0656/H6) and
     * this slice's extern-C admission the guard carries no HOST-kind
     * shape; the producer stays landed (a superseded shape is replaced,
     * never deleted).
     */
    private static CompilerDiagnostic hostModuleImportFailure(ModuleId emitting,
            String rawSpecifier, String resolvedModulePath,
            CompilerInvocation invocation) {
        return FailureContractRegistry.e6005(new LoweringFailureDetail(
            emitting.path(), SemanticCapability.MODULES, SHARED_EMITTER_COVERAGE,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "ProductionProjectEmission " + SHARED_EMITTER_COVERAGE + " "
                + HOST_MODULE_IMPORT + " (emitting module '" + emitting.path()
                + "', import '" + rawSpecifier + "' resolved to '"
                + resolvedModulePath + "')"));
    }

    /**
     * The fail-closed mapping of a production emitter gap: an op outside
     * the landed production emission set is E6005
     * {@code SHARED_EMITTER_COVERAGE} — never a crash, never a fallback
     * to a retained emitter, and no artifact stages. A typed
     * {@link LuaSemanticEmitter.FfiProviderGap} keeps the provider-gap
     * detail (P4): the detail's module is the consuming (emitting) module
     * of the extern-C import — the module whose {@code MODULE_IMPORT}
     * carries it, never the entry module — and the detail's origin carries
     * the import statement's origin, the raw specifier, the resolved
     * declaration module, and the offending provider alias and module.
     * Every other gap keeps the entry-module detail and the generic gap
     * text.
     */
    private static CompilerDiagnostic sharedEmitterCoverage(
            String entryModulePath, IllegalStateException gap,
            CompilerInvocation invocation) {
        if (gap instanceof LuaSemanticEmitter.FfiProviderGap providerGap) {
            return FailureContractRegistry.e6005(new LoweringFailureDetail(
                providerGap.consumingModulePath(), SemanticCapability.MODULES,
                SHARED_EMITTER_COVERAGE, invocation.semanticProfile(),
                LoweredModuleUnit.FORMAT_VERSION,
                "ProductionProjectEmission " + SHARED_EMITTER_COVERAGE + " "
                    + FFI_PROVIDER_GAP + " (" + providerGap.getMessage()
                    + ")"));
        }
        return FailureContractRegistry.e6005(new LoweringFailureDetail(
            entryModulePath, SemanticCapability.MODULES, SHARED_EMITTER_COVERAGE,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "ProductionProjectEmission " + SHARED_EMITTER_COVERAGE + " ("
                + gap.getMessage() + ")"));
    }

    /**
     * The pinned missing-runtime E6000 of the LuaJIT deployment copies
     * (unchanged text and shape: an anchorless synthetic error with the
     * runtime path note).
     */
    private static CompilerDiagnostic runtimeLibraryMissing() {
        return CompilerDiagnostic.syntheticError(DiagnosticCode.E6000,
            "Runtime library not found: " + RUNTIME_LUA, "",
            "missing anchor: runtime library path '" + RUNTIME_LUA + "'");
    }
}
