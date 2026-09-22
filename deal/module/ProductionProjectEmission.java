package deal.module;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.publication.PublicationStager;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;

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
 *   <li>exactly one project lowering over the compile's declared inputs
 *       (the invocation, the checked project and interface index, the
 *       requirement manifests, the declaration surface, the declaration
 *       module identities, the extern-C generated modules, the builtin
 *       {@code Error} declaration, the conversion intrinsics, and the
 *       production callback set); a failing lowering returns the first
 *       E6005 and stages nothing;</li>
 *   <li>the pre-emission closure guard over the validated project's
 *       closed op walk — a whole-closure property independent of
 *       execution: a HOST-kind module import and a cross-module async
 *       call fail closed with E6005 {@code SHARED_EMITTER_COVERAGE} and
 *       their stable detail token, naming the import (its raw specifier
 *       and its resolved module) or the call (the emitting module, the
 *       callee module, and the export name); {@code STDLIB}/{@code
 *       COMPILED} imports and same-module async calls stay accepted;</li>
 *   <li>exactly one emission per target: the LuaJIT production project
 *       chunk (one chunk named for the entry module, staged at the entry
 *       module path with {@code '.'} replaced by {@code '/'} plus
 *       {@code .lua}) or the JVM production project class (one {@code
 *       public final class}, staged at
 *       {@code JvmBackend.classNameFor(entryModule.path()) + ".java"}); an
 *       emitter gap (an op outside the landed production set) maps to
 *       E6005 {@code SHARED_EMITTER_COVERAGE} and stages nothing;</li>
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

    /** The stable guard detail token of a HOST-kind module import. */
    public static final String HOST_MODULE_IMPORT = "HOST_MODULE_IMPORT";

    /** The stable guard detail token of a cross-module async call. */
    public static final String EXTERNAL_ASYNC_CALL = "EXTERNAL_ASYNC_CALL";

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
     * the C9 warning, the one project lowering, the pre-emission closure
     * guard, the one emission, the one staged project artifact, and the
     * unchanged LuaJIT deployment copies. The caller (the phase-4
     * dispatch) owns the arm selection, the emission record, and the
     * publication transaction; this unit stages artifacts only.
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

        // (2) The one project lowering over the compile's declared inputs.
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

        // (3) The pre-emission closure guard over the validated project's
        // closed op walk: a whole-closure property, independent of whether
        // the containing body executes.
        Optional<CompilerDiagnostic> guardFailure =
            closureGuard(project, invocation);
        if (guardFailure.isPresent()) {
            return new Result(Outcome.FAILED, List.of(guardFailure.get()), null);
        }

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
                    lowering.tables(), lowering.registries(), className);
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
                    lowering.tables(), lowering.registries());
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
     * The pre-emission closure guard over the validated project's closed
     * op walk (every module's ops, payload-owned children included), in
     * dependency order and op order: the first of the two guarded shapes
     * wins — a HOST-kind module import, then a cross-module async call —
     * and every other op, including {@code STDLIB}/{@code COMPILED}
     * imports and same-module async calls, passes.
     */
    private static Optional<CompilerDiagnostic> closureGuard(
            ExecutableLoweredProject project, CompilerInvocation invocation) {
        for (Map.Entry<ModuleId, LoweredModuleUnit> unit
                : project.modules().entrySet()) {
            ModuleId emitting = unit.getKey();
            for (SemanticOp op : unit.getValue().ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                    KindPayload.ModuleImportPayload payload =
                        (KindPayload.ModuleImportPayload) op.payload();
                    if (payload.kind() == ModuleImportKind.HOST) {
                        return Optional.of(hostModuleImportFailure(
                            emitting, payload, invocation));
                    }
                } else if (op.kind() == SemanticOpKind.ASYNC_START) {
                    KindPayload.AsyncStartPayload payload =
                        (KindPayload.AsyncStartPayload) op.payload();
                    if (payload.externalAsyncLink() != null) {
                        return Optional.of(externalAsyncCallFailure(
                            emitting, payload, invocation));
                    }
                }
            }
        }
        return Optional.empty();
    }

    /**
     * Guard 1: a HOST-kind module import (a host or extern-C declaration
     * import) has no production emission arm — the host load and its
     * load-time presence check belong to the calls and FFI children — so
     * the whole closure fails closed.
     */
    private static CompilerDiagnostic hostModuleImportFailure(ModuleId emitting,
            KindPayload.ModuleImportPayload payload, CompilerInvocation invocation) {
        return FailureContractRegistry.e6005(new LoweringFailureDetail(
            emitting.path(), SemanticCapability.MODULES, SHARED_EMITTER_COVERAGE,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "ProductionProjectEmission " + SHARED_EMITTER_COVERAGE + " "
                + HOST_MODULE_IMPORT + " (emitting module '" + emitting.path()
                + "', import '" + payload.rawSpecifier() + "' resolved to '"
                + payload.resolvedModule().path() + "')"));
    }

    /**
     * Guard 2: a cross-module async call (an {@code ASYNC_START} carrying
     * the statically resolved external async linkage) references a
     * per-module async-entry surface the one-chunk project layout does
     * not contain, so the whole closure fails closed.
     */
    private static CompilerDiagnostic externalAsyncCallFailure(ModuleId emitting,
            KindPayload.AsyncStartPayload payload, CompilerInvocation invocation) {
        ExternalAsyncLink link = payload.externalAsyncLink();
        return FailureContractRegistry.e6005(new LoweringFailureDetail(
            emitting.path(), SemanticCapability.CALLS, SHARED_EMITTER_COVERAGE,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "ProductionProjectEmission " + SHARED_EMITTER_COVERAGE + " "
                + EXTERNAL_ASYNC_CALL + " (emitting module '" + emitting.path()
                + "', callee module '" + link.calleeModuleId().path()
                + "', export '" + link.exportName() + "')"));
    }

    /**
     * The fail-closed mapping of a production emitter gap: an op outside
     * the landed production emission set is E6005
     * {@code SHARED_EMITTER_COVERAGE} — never a crash, never a fallback
     * to a retained emitter, and no artifact stages.
     */
    private static CompilerDiagnostic sharedEmitterCoverage(String modulePath,
            IllegalStateException gap, CompilerInvocation invocation) {
        return FailureContractRegistry.e6005(new LoweringFailureDetail(
            modulePath, SemanticCapability.MODULES, SHARED_EMITTER_COVERAGE,
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
