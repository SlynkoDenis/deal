package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.ModuleRoute;
import deal.semantic.ModuleRoutePlan;
import deal.semantic.SemanticLowerer;
import deal.semantic.Target;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The registry child's tests (ISSUE-0447 sequencing item 4): the
 * {@code FunctionExecutionBinding} registry —
 * {@code LoweredModuleUnit.functionBindings} keyed by
 * {@link FunctionAllocationIdentity} with exactly one registration per
 * producing allocation for the five closed binding shapes — and this
 * epic's minimal in-epic ownership of the host/external function-value
 * materialization seam (the classification of host/external
 * function-value producing sites and the {@code HostFunction}/
 * {@code ExternalFunction}/{@code HostFunctionValue} registrations over
 * member-read/export-read op facts and {@code HOST_TO_DEAL}
 * boundary-op facts at the IR level, explicitly without producing
 * member-read/module lowering and without producing any
 * {@code BOUNDARY} op).
 *
 * <p><b>Coverage.</b></p>
 * <ul>
 *   <li>a closure lowering registers exactly one {@code LoweredBody}
 *       keyed by the {@code CLOSURE_NEW} result identity (combined with
 *       the closure child — fails if it breaks);</li>
 *   <li>a mutual-recursion group lowering registers one
 *       {@code LoweredBody} per member keyed by each pre-assigned
 *       identity (combined with the group child — fails if it breaks);</li>
 *   <li>seam tests (self-contained, IR level): a
 *       {@code MemberReadPayload}/{@code ExportReadPayload} record with
 *       host-module facts registers {@code HostFunction
 *       {hostModuleId, exportName, descriptor}}; the same with
 *       cross-module facts plus a {@code ModuleRoutePlan} record whose
 *       callee route is shared registers {@code ExternalFunction
 *       {moduleId, exportName, descriptor, SHARED_BODY}}; with a
 *       retained-ABI route record registers {@code RETAINED_ABI}; a
 *       {@code HOST_TO_DEAL} {@code BoundaryPayload} fact record
 *       (constructed as the pinned schema shape, not produced or
 *       executed) with a function-typed descriptor registers
 *       {@code HostFunctionValue {hostModuleId,
 *       materializingBoundaryOpId, descriptor}} naming exactly that
 *       boundary op id;</li>
 *   <li>producer-fact classification: the seam marks host/external
 *       producing sites with the facts the shape-map child's import-read
 *       arm consumes (the {@code FunctionValueMaterialization}
 *       records keyed by the produced allocation identity);</li>
 *   <li>the adapter registration seam: {@code FUNCTION_ADAPT} →
 *       {@code AdapterBinding {adaptOpId, captureMode, sourceRef,
 *       sourceSignature, targetSignature}} (the registration function
 *       consumed at the adapter-creation site — the shape-map child's
 *       production);</li>
 *   <li>negatives: duplicate-key registration rejected at registration
 *       time; a function-typed materialization without its producer
 *       facts (or with mismatched facts, a non-function descriptor, a
 *       missing route record, or a foreign payload) is not silently
 *       skipped — the seam fails explicitly;</li>
 *   <li>non-production assertions: units produced by this child's own
 *       tests contain no {@code BOUNDARY} ops, the lowered units carry
 *       no {@code MEMBER_READ}/{@code EXPORT_READ} op production path
 *       (a module member access still fails closed with the pinned
 *       E6005), and the map is immutable after lowering with identical
 *       iteration order across runs;</li>
 *   <li>determinism: a fixed lowering yields the same map with
 *       identical iteration order across runs and byte-identical
 *       {@code deal.semantic-ir/1} dumps.</li>
 * </ul>
 */
public class FunctionBindingRegistryTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    /** True iff the seam call throws; records a failure when it does not. */
    private static boolean throwsWhen(Runnable action, String message) {
        try {
            action.run();
            check(false, message + " (no exception was thrown)");
            return false;
        } catch (RuntimeException expected) {
            check(true, message + ": " + expected.getClass().getSimpleName());
            return true;
        }
    }

    // =========================================================================
    // Fixed invocation facts
    // =========================================================================

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new ExternalModuleInterface(MODULE, ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    /** A fixed () => null function descriptor for the seam tests. */
    private static final RuntimeDescriptor.Func NULL_FUNC =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);

    /** A fixed (int) => int function descriptor for the adapter seam test. */
    private static final RuntimeDescriptor.Func INT_FUNC =
        new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Int.INSTANCE),
            RuntimeDescriptor.Int.INSTANCE);

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    // =========================================================================
    // Checked-source slices and the entry-point drivers
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        return checkSlice(source, null);
    }

    private static CheckedSlice checkSlice(String source, ModuleResolver resolver) {
        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver("test.deal", resolver);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check("test.deal", symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(),
            "the slice checks cleanly: " + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of("test.deal"), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    private static SemanticLowerer.ClosureCoreResult lowerClosureSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleClosureCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    private static SemanticLowerer.GroupCoreResult lowerGroupSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleGroupCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    private static List<SemanticOp> ofKind(List<SemanticOp> ops, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    /** True iff the unit's produced op list carries no op of the named kinds. */
    private static boolean noOpsOfKind(LoweredModuleUnit unit, SemanticOpKind... kinds) {
        for (SemanticOp op : unit.ops()) {
            for (SemanticOpKind kind : kinds) {
                if (op.kind() == kind) {
                    return false;
                }
            }
        }
        return true;
    }

    /** The group facts entry of a declared member name. */
    private static SemanticLowerer.GroupMemberFacts member(
            SemanticLowerer.GroupFacts group, String name) {
        List<SemanticLowerer.GroupMemberFacts> matches = new ArrayList<>();
        for (SemanticLowerer.GroupMemberFacts member : group.members()) {
            if (member.name().equals(name)) {
                matches.add(member);
            }
        }
        check(matches.size() == 1, "exactly one member-facts record for '" + name
            + "'; got " + matches.size());
        return matches.size() == 1 ? matches.get(0) : null;
    }

    /** A fixed ModuleRoutePlan with the given entries (empty shadow set, no bytes exceptions, no ABI edges). */
    private static ModuleRoutePlan plan(Map<ModuleId, ModuleRoute> entries) {
        String hash = "0".repeat(64);
        return new ModuleRoutePlan(Target.LUAJIT, entries, Set.of(), Set.of(), List.of(),
            hash, "plan-" + hash.substring(0, 16));
    }

    // =========================================================================
    // Tests
    // =========================================================================

    /**
     * Closure lowering through the registry seam: every
     * {@code CLOSURE_NEW} result registers exactly one
     * {@code LoweredBody} keyed by the allocation identity equal to the
     * result value id (B5), in production order (registration order —
     * deterministic map iteration), and the produced unit carries no
     * {@code BOUNDARY}, {@code MEMBER_READ}, or {@code EXPORT_READ} op
     * (this child's non-production boundary).
     */
    static void testClosureRegistrationKeysExactlyClosureNewResultIdentities() {
        System.out.println("-- closure lowering: one LoweredBody per CLOSURE_NEW keyed by "
            + "the result identity, in registration order --");

        SemanticLowerer.ClosureCoreResult result = lowerClosureSlice("""
            function f(): null {}
            function g(): null {}
            function h(): null {
              let k = function(): null {};
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> closureNews = ofKind(unit.ops(), SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 4, "four CLOSURE_NEW ops (f, g, h, k's expression); got "
            + closureNews.size());
        check(unit.functionBindings().size() == closureNews.size() + 2,
            "one functionBinding per closure (registry one-to-one) plus the two "
                + "producer-less intrinsic seed registrations (ISSUE-0632): "
                + unit.functionBindings().size() + " bindings for " + closureNews.size()
                + " closures");
        // The key set is exactly the CLOSURE_NEW result identities plus the
        // two intrinsic seed keys (the producer-less conversion intrinsics).
        List<FunctionAllocationIdentity> keys = new ArrayList<>(
            unit.functionBindings().keySet());
        List<FunctionAllocationIdentity> seedKeys = new ArrayList<>();
        List<FunctionAllocationIdentity> closureKeys = new ArrayList<>();
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction) {
                seedKeys.add(entry.getKey());
            } else {
                closureKeys.add(entry.getKey());
            }
        }
        check(seedKeys.size() == 2, "the registry carries the two intrinsic seed keys; "
            + "got " + seedKeys);
        List<FunctionAllocationIdentity> resultIdentities = new ArrayList<>();
        for (SemanticOp closureNew : closureNews) {
            resultIdentities.add(
                new FunctionAllocationIdentity(((ValueId) closureNew.result()).id()));
        }
        check(closureKeys.size() == resultIdentities.size()
                && new java.util.LinkedHashSet<>(closureKeys).equals(
                    new java.util.LinkedHashSet<>(resultIdentities)),
            "the map's non-seed keys are exactly the CLOSURE_NEW result identities "
                + "(registry one-to-one); got " + closureKeys + " for " + resultIdentities);
        for (SemanticOp closureNew : closureNews) {
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) closureNew.payload();
            FunctionAllocationIdentity key =
                new FunctionAllocationIdentity(((ValueId) closureNew.result()).id());
            check(unit.functionBindings().get(key)
                    instanceof FunctionExecutionBinding.LoweredBody body
                    && body.functionId().equals(payload.function())
                    && body.blockId().equals(payload.binding().blockId()),
                "the binding of " + key + " is LoweredBody {functionId, blockId} equal to "
                    + "the CLOSURE_NEW payload's binding fields");
        }
        // Deterministic registration order: the ops list holds [f, g, h]
        // at its head (the CLOSURE_NEW ops of the module-level
        // declarations, declaration order) and k's expression closure
        // last (inside h's flushed body ops); the registry map iterates
        // in the walk's registration order — f, g, then k (registered
        // during h's body walk, which precedes h's own CLOSURE_NEW),
        // then h.
        check(closureNews.size() == 4, "four CLOSURE_NEW ops to order");
        if (closureNews.size() == 4) {
            FunctionAllocationIdentity fKey = new FunctionAllocationIdentity(
                ((ValueId) closureNews.get(0).result()).id());
            FunctionAllocationIdentity gKey = new FunctionAllocationIdentity(
                ((ValueId) closureNews.get(1).result()).id());
            FunctionAllocationIdentity hKey = new FunctionAllocationIdentity(
                ((ValueId) closureNews.get(2).result()).id());
            FunctionAllocationIdentity kKey = new FunctionAllocationIdentity(
                ((ValueId) closureNews.get(3).result()).id());
            check(closureKeys.equals(List.of(fKey, gKey, kKey, hKey)),
                "the map iterates in the walk's deterministic registration order "
                    + "[f, g, k, h] (a nested closure registers during its enclosing "
                    + "body walk, before the enclosing closure); got " + keys);
            check(keys.size() == 6 && keys.subList(0, 2).equals(seedKeys),
                "the two intrinsic seeds are registered first (they are seeded before "
                    + "the hoisted names, ISSUE-0632); got " + keys);
        }
        // Non-production boundary: no BOUNDARY/MEMBER_READ/EXPORT_READ op.
        check(noOpsOfKind(unit, SemanticOpKind.BOUNDARY, SemanticOpKind.MEMBER_READ,
                SemanticOpKind.EXPORT_READ),
            "the closure unit carries no BOUNDARY/MEMBER_READ/EXPORT_READ op (this child "
                + "produces none)");
        // The unit's map is immutable after lowering.
        check(throwsWhen(() -> unit.functionBindings().put(
                    new FunctionAllocationIdentity(999),
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                        new BlockId(1))),
                "the unit's functionBindings map is immutable after lowering"),
            "the unit's functionBindings map is immutable after lowering");
    }

    /**
     * Group lowering through the registry seam: a mutual-recursion SCC
     * registers one {@code LoweredBody} per member keyed by each
     * pre-assigned allocation identity (B4/B5), in declaration order,
     * and the size-1 sibling closure registers through the same map.
     */
    static void testGroupRegistrationOneLoweredBodyPerMember() {
        System.out.println("-- group lowering: one LoweredBody per member keyed by each "
            + "pre-assigned identity --");

        SemanticLowerer.GroupCoreResult result = lowerGroupSlice("""
            function f(): null {
              let gRef = g;
            }
            function g(): null {
              let fRef = f;
            }
            function h(): null {}
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> groups = ofKind(unit.ops(), SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(groups.size() == 1, "exactly one RECURSIVE_GROUP_INIT op; got " + groups.size());
        check(result.groups().size() == 1, "exactly one group-facts record; got "
            + result.groups().size());
        if (groups.size() != 1 || result.groups().size() != 1) {
            return;
        }
        SemanticLowerer.GroupFacts group = result.groups().get(0);
        check(group.members().size() == 2, "exactly two members; got " + group.members().size());
        SemanticLowerer.GroupMemberFacts f = member(group, "f");
        SemanticLowerer.GroupMemberFacts g = member(group, "g");
        if (f == null || g == null) {
            return;
        }
        List<SemanticOp> closureNews = ofKind(unit.ops(), SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 1, "exactly one CLOSURE_NEW (the size-1 sibling h); got "
            + closureNews.size());
        check(unit.functionBindings().size() == 5,
            "three bindings: one LoweredBody per member plus h's closure plus the two "
                + "intrinsic seeds (ISSUE-0632); got "
                + unit.functionBindings().size());
        // One LoweredBody per member keyed by the pre-assigned identity.
        FunctionAllocationIdentity fKey = new FunctionAllocationIdentity(f.identity().id());
        FunctionAllocationIdentity gKey = new FunctionAllocationIdentity(g.identity().id());
        check(unit.functionBindings().get(fKey)
                instanceof FunctionExecutionBinding.LoweredBody fBody
                && fBody.functionId().equals(f.functionId())
                && fBody.blockId().equals(f.bodyBlock()),
            "f's binding is LoweredBody {functionId, blockId} keyed by f's pre-assigned "
                + "identity " + fKey);
        check(unit.functionBindings().get(gKey)
                instanceof FunctionExecutionBinding.LoweredBody gBody
                && gBody.functionId().equals(g.functionId())
                && gBody.blockId().equals(g.bodyBlock()),
            "g's binding is LoweredBody {functionId, blockId} keyed by g's pre-assigned "
                + "identity " + gKey);
        // h's closure registers like any closure.
        FunctionAllocationIdentity hKey = closureNews.isEmpty() ? null
            : new FunctionAllocationIdentity(((ValueId) closureNews.get(0).result()).id());
        if (hKey != null) {
            KindPayload.ClosureNewPayload hPayload =
                (KindPayload.ClosureNewPayload) closureNews.get(0).payload();
            check(unit.functionBindings().get(hKey)
                    instanceof FunctionExecutionBinding.LoweredBody hBody
                    && hBody.functionId().equals(hPayload.function()),
                "h's closure binding is LoweredBody keyed by its CLOSURE_NEW result identity");
        }
        // Iteration order: the two intrinsic seeds first (they are seeded
        // before the hoisted names, ISSUE-0632), then declaration order f, g, h.
        List<FunctionAllocationIdentity> keys = new ArrayList<>(
            unit.functionBindings().keySet());
        check(keys.size() == 5 && keys.get(2).equals(fKey) && keys.get(3).equals(gKey)
                && hKey != null && keys.get(4).equals(hKey),
            "the map iterates in declaration order [f, g, h] after the two intrinsic "
                + "seed keys; got " + keys);
        check(noOpsOfKind(unit, SemanticOpKind.BOUNDARY, SemanticOpKind.MEMBER_READ,
                SemanticOpKind.EXPORT_READ),
            "the group unit carries no BOUNDARY/MEMBER_READ/EXPORT_READ op (this child "
                + "produces none)");
    }

    /**
     * Seam (self-contained, IR level): a {@code MemberReadPayload} record
     * with host-module facts registers {@code HostFunction {hostModuleId,
     * exportName, descriptor}} keyed by the produced allocation identity
     * and classifies the site as {@code HOST_EXPORT} — the producer fact
     * the shape-map child's import-read arm consumes.
     */
    static void testMemberReadHostFactsRegisterHostFunction() {
        System.out.println("-- seam: member-read + host facts registers HostFunction --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(7);
        ModuleId host = new ModuleId("host");
        KindPayload.MemberReadPayload payload =
            new KindPayload.MemberReadPayload(new ValueId(11), "g");
        FunctionBindingRegistry.FunctionValueImportFacts facts =
            new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "g", NULL_FUNC);
        FunctionBindingRegistry.FunctionValueMaterialization classification =
            registry.registerHostOrExternalImport(identity, payload, facts, null);

        check(registry.size() == 1 && registry.containsKey(identity),
            "exactly one registration keyed by the produced allocation identity");
        check(registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.HostFunction hostBinding
                && hostBinding.hostModuleId().equals(host)
                && hostBinding.exportName().equals("g")
                && hostBinding.descriptor().equals(NULL_FUNC),
            "the binding is HostFunction {hostModuleId, exportName, descriptor}");
        check(classification.identity().equals(identity)
                && classification.source()
                    == FunctionBindingRegistry.FunctionValueMaterializationSource.HOST_EXPORT
                && classification.moduleId().equals(host)
                && classification.exportName().equals("g")
                && classification.descriptor().equals(NULL_FUNC)
                && classification.producingOpKind() == SemanticOpKind.MEMBER_READ
                && classification.materializingBoundaryOpId() == null,
            "the classification marks the site HOST_EXPORT with the export facts and "
                + "producing op kind MEMBER_READ: " + classification);
        check(registry.materializationOf(identity).isPresent()
                && registry.materializationOf(identity).get().equals(classification),
            "materializationOf resolves the producer fact by the produced identity");
        check(registry.materializations().equals(List.of(classification)),
            "the materialization list records exactly the one classification in "
                + "registration order");
    }

    /**
     * Seam (self-contained, IR level): an {@code ExportReadPayload}
     * record with host-module facts registers {@code HostFunction} with
     * producing op kind {@code EXPORT_READ}.
     */
    static void testExportReadHostFactsRegisterHostFunction() {
        System.out.println("-- seam: export-read + host facts registers HostFunction --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(21);
        ModuleId host = new ModuleId("host");
        KindPayload.ExportReadPayload payload = new KindPayload.ExportReadPayload(host, "pick",
            NULL_FUNC, new ValueId(21));
        FunctionBindingRegistry.FunctionValueImportFacts facts =
            new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "pick", NULL_FUNC);
        FunctionBindingRegistry.FunctionValueMaterialization classification =
            registry.registerHostOrExternalImport(identity, payload, facts, null);

        check(registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.HostFunction hostBinding
                && hostBinding.hostModuleId().equals(host)
                && hostBinding.exportName().equals("pick")
                && hostBinding.descriptor().equals(NULL_FUNC),
            "the binding is HostFunction {hostModuleId, exportName, descriptor}");
        check(classification.source()
                    == FunctionBindingRegistry.FunctionValueMaterializationSource.HOST_EXPORT
                && classification.producingOpKind() == SemanticOpKind.EXPORT_READ,
            "the classification marks the export-read site HOST_EXPORT with producing op "
                + "kind EXPORT_READ: " + classification);
    }

    /**
     * Seam (self-contained, IR level): cross-module facts plus a
     * {@code ModuleRoutePlan} record whose callee route is shared
     * register {@code ExternalFunction {moduleId, exportName,
     * descriptor, SHARED_BODY}}.
     */
    static void testCrossModuleSharedRouteRegistersExternalFunctionSharedBody() {
        System.out.println("-- seam: cross-module + shared route registers ExternalFunction "
            + "SHARED_BODY --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(30);
        ModuleId lib = new ModuleId("lib");
        KindPayload.MemberReadPayload payload =
            new KindPayload.MemberReadPayload(new ValueId(12), "pick");
        FunctionBindingRegistry.FunctionValueImportFacts facts =
            new FunctionBindingRegistry.FunctionValueImportFacts(null, lib, "pick", NULL_FUNC);
        ModuleRoutePlan plan = plan(Map.of(lib, ModuleRoute.SHARED));
        FunctionBindingRegistry.FunctionValueMaterialization classification =
            registry.registerHostOrExternalImport(identity, payload, facts, plan);

        check(registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.ExternalFunction external
                && external.moduleId().equals(lib)
                && external.exportName().equals("pick")
                && external.descriptor().equals(NULL_FUNC)
                && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
            "the binding is ExternalFunction {moduleId, exportName, descriptor, SHARED_BODY} "
                + "(the shared callee route resolves SHARED_BODY from the plan record)");
        check(classification.source()
                    == FunctionBindingRegistry.FunctionValueMaterializationSource.EXTERNAL_IMPORT
                && classification.moduleId().equals(lib)
                && classification.producingOpKind() == SemanticOpKind.MEMBER_READ,
            "the classification marks the site EXTERNAL_IMPORT with the imported module "
                + "facts: " + classification);
    }

    /**
     * Seam (self-contained, IR level): cross-module facts plus a
     * retained-ABI route record register {@code ExternalFunction {…,
     * RETAINED_ABI}}.
     */
    static void testCrossModuleRetainedAbiRouteRegistersExternalFunctionRetainedAbi() {
        System.out.println("-- seam: cross-module + retained-ABI route registers "
            + "ExternalFunction RETAINED_ABI --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(31);
        ModuleId lib = new ModuleId("lib");
        KindPayload.ExportReadPayload payload = new KindPayload.ExportReadPayload(lib, "pick",
            NULL_FUNC, new ValueId(31));
        FunctionBindingRegistry.FunctionValueImportFacts facts =
            new FunctionBindingRegistry.FunctionValueImportFacts(null, lib, "pick", NULL_FUNC);
        ModuleRoutePlan plan = plan(Map.of(lib, ModuleRoute.LEGACY));
        FunctionBindingRegistry.FunctionValueMaterialization classification =
            registry.registerHostOrExternalImport(identity, payload, facts, plan);

        check(registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.ExternalFunction external
                && external.executionOwner() == ExternalExecutionOwner.RETAINED_ABI,
            "the binding is ExternalFunction with RETAINED_ABI (the retained-ABI callee "
                + "route resolves RETAINED_ABI from the plan record)");
        check(classification.producingOpKind() == SemanticOpKind.EXPORT_READ,
            "the classification's producing op kind is EXPORT_READ");
    }

    /**
     * Seam (self-contained, IR level): a {@code HOST_TO_DEAL}
     * {@code BoundaryPayload} fact record (constructed as the pinned
     * schema shape, not produced or executed) with a function-typed
     * descriptor registers {@code HostFunctionValue {hostModuleId,
     * materializingBoundaryOpId, descriptor}} naming exactly that
     * boundary op id — the correlation id the conformance page's
     * {@code HostFunctionValueRef} resolves.
     */
    static void testHostToDealBoundaryFactsRegisterHostFunctionValue() {
        System.out.println("-- seam: HOST_TO_DEAL boundary facts register "
            + "HostFunctionValue naming exactly the boundary op id --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        ModuleId host = new ModuleId("host");
        OpId boundaryOpId = new OpId(host, 99);
        KindPayload.BoundaryPayload boundaryPayload = new KindPayload.BoundaryPayload(
            BoundaryKind.HOST_TO_DEAL, NULL_FUNC, new ValueId(40),
            new BoundaryRealization.RuntimeValidation("host-check-1"));
        FunctionBindingRegistry.FunctionValueMaterialization classification =
            registry.registerHostFunctionValue(new FunctionAllocationIdentity(40),
                boundaryPayload, boundaryOpId, host);

        check(registry.size() == 1, "exactly one registration for the crossing");
        check(registry.bindings().get(new FunctionAllocationIdentity(40))
                instanceof FunctionExecutionBinding.HostFunctionValue hostValue
                && hostValue.hostModuleId().equals(host)
                && hostValue.materializingBoundaryOpId().equals(boundaryOpId)
                && hostValue.descriptor().equals(NULL_FUNC),
            "the binding is HostFunctionValue {hostModuleId, materializingBoundaryOpId, "
                + "descriptor} naming exactly the boundary op id " + boundaryOpId);
        check(classification.source()
                    == FunctionBindingRegistry.FunctionValueMaterializationSource.HOST_VALUE
                && classification.exportName() == null
                && classification.producingOpKind() == SemanticOpKind.BOUNDARY
                && classification.materializingBoundaryOpId().equals(boundaryOpId),
            "the classification marks the crossing HOST_VALUE with the materializing "
                + "boundary op id: " + classification);
    }

    /**
     * The adapter registration seam: {@code FUNCTION_ADAPT} →
     * {@code AdapterBinding {adaptOpId, captureMode, sourceRef,
     * sourceSignature, targetSignature}} — the registration function
     * consumed at the adapter-creation site (the shape-map child's
     * production).
     */
    static void testAdapterRegistrationSeam() {
        System.out.println("-- adapter registration seam: AdapterBinding fields --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(50);
        OpId adaptOpId = new OpId(MODULE, 3);
        CaptureMode mode = CaptureMode.SHARED_CELL;
        AdaptSourceRef sourceRef = new AdaptSourceRef.SharedCell(new BindingId(1), 0);
        RuntimeDescriptor.Func targetSignature = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            RuntimeDescriptor.Int.INSTANCE);
        registry.registerAdapter(identity, adaptOpId, mode, sourceRef, INT_FUNC,
            targetSignature);

        check(registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.AdapterBinding adapter
                && adapter.adaptOpId().equals(adaptOpId)
                && adapter.captureMode() == mode
                && adapter.sourceRef().equals(sourceRef)
                && adapter.sourceSignature().equals(INT_FUNC)
                && adapter.targetSignature().equals(targetSignature),
            "the binding is AdapterBinding {adaptOpId, captureMode, sourceRef, "
                + "sourceSignature, targetSignature} with the adapter-creation facts");
    }

    /**
     * The five closed binding shapes in one registry, one registration
     * per producing allocation, keyed by identity.
     */
    static void testFiveClosedShapesInOneRegistry() {
        System.out.println("-- the five closed binding shapes in one registry --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        registry.registerClosure(new FunctionAllocationIdentity(1), new FunctionId(1),
            new BlockId(1));
        registry.registerGroupMember(new FunctionAllocationIdentity(2), new FunctionId(2),
            new BlockId(2));
        registry.registerAdapter(new FunctionAllocationIdentity(3), new OpId(MODULE, 3),
            CaptureMode.VALUE, new AdaptSourceRef.Value(new ValueId(9)), INT_FUNC, INT_FUNC);
        registry.registerHostOrExternalImport(new FunctionAllocationIdentity(4),
            new KindPayload.MemberReadPayload(new ValueId(11), "g"),
            new FunctionBindingRegistry.FunctionValueImportFacts(new ModuleId("host"), null,
                "g", NULL_FUNC),
            null);
        registry.registerHostOrExternalImport(new FunctionAllocationIdentity(5),
            new KindPayload.MemberReadPayload(new ValueId(12), "pick"),
            new FunctionBindingRegistry.FunctionValueImportFacts(null, new ModuleId("lib"),
                "pick", NULL_FUNC),
            plan(Map.of(new ModuleId("lib"), ModuleRoute.SHARED)));
        registry.registerHostFunctionValue(new FunctionAllocationIdentity(6),
            new KindPayload.BoundaryPayload(BoundaryKind.HOST_TO_DEAL, NULL_FUNC,
                new ValueId(6), new BoundaryRealization.RuntimeValidation("c")),
            new OpId(new ModuleId("host"), 99), new ModuleId("host"));

        check(registry.size() == 6, "six registrations, one per producing allocation; got "
            + registry.size());
        check(registry.bindings().get(new FunctionAllocationIdentity(1))
                instanceof FunctionExecutionBinding.LoweredBody,
            "key 1 resolves a LoweredBody (CLOSURE_NEW)");
        check(registry.bindings().get(new FunctionAllocationIdentity(2))
                instanceof FunctionExecutionBinding.LoweredBody,
            "key 2 resolves a LoweredBody (RECURSIVE_GROUP_INIT member)");
        check(registry.bindings().get(new FunctionAllocationIdentity(3))
                instanceof FunctionExecutionBinding.AdapterBinding,
            "key 3 resolves an AdapterBinding (FUNCTION_ADAPT)");
        check(registry.bindings().get(new FunctionAllocationIdentity(4))
                instanceof FunctionExecutionBinding.HostFunction,
            "key 4 resolves a HostFunction (host import)");
        check(registry.bindings().get(new FunctionAllocationIdentity(5))
                instanceof FunctionExecutionBinding.ExternalFunction,
            "key 5 resolves an ExternalFunction (cross-module import)");
        check(registry.bindings().get(new FunctionAllocationIdentity(6))
                instanceof FunctionExecutionBinding.HostFunctionValue,
            "key 6 resolves a HostFunctionValue (host crossing)");
        check(registry.materializations().size() == 3,
            "three materialization classifications (the two import sites and the host "
                + "crossing); got " + registry.materializations().size());
    }

    /**
     * Duplicate-key registration is rejected by the registry at
     * registration time (fail closed, never overwritten): the second
     * registration throws and the original binding stays intact.
     */
    static void testDuplicateKeyRejectedAtRegistrationTime() {
        System.out.println("-- duplicate-key registration rejected at registration time --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(60);
        registry.registerClosure(identity, new FunctionId(1), new BlockId(1));
        check(registry.size() == 1, "one registration before the duplicate attempt");
        check(throwsWhen(() -> registry.registerClosure(identity, new FunctionId(2),
                    new BlockId(2)),
                "a duplicate closure registration is rejected at registration time"),
            "a duplicate closure registration is rejected at registration time");
        check(throwsWhen(() -> registry.registerGroupMember(identity, new FunctionId(2),
                    new BlockId(2)),
                "a duplicate registration across producer kinds is rejected"),
            "a duplicate registration across producer kinds is rejected");
        check(throwsWhen(() -> registry.registerAdapter(identity, new OpId(MODULE, 3),
                    CaptureMode.VALUE, new AdaptSourceRef.Value(new ValueId(9)), INT_FUNC,
                    INT_FUNC),
                "a duplicate adapter registration is rejected"),
            "a duplicate adapter registration is rejected");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(identity,
                    new KindPayload.MemberReadPayload(new ValueId(11), "g"),
                    new FunctionBindingRegistry.FunctionValueImportFacts(new ModuleId("host"),
                        null, "g", NULL_FUNC),
                    null),
                "a duplicate host-import registration is rejected"),
            "a duplicate host-import registration is rejected");
        check(throwsWhen(() -> registry.registerHostFunctionValue(identity,
                    new KindPayload.BoundaryPayload(BoundaryKind.HOST_TO_DEAL, NULL_FUNC,
                        new ValueId(60), new BoundaryRealization.RuntimeValidation("c")),
                    new OpId(new ModuleId("host"), 99), new ModuleId("host")),
                "a duplicate host-value registration is rejected"),
            "a duplicate host-value registration is rejected");
        check(registry.size() == 1
                && registry.bindings().get(identity)
                    instanceof FunctionExecutionBinding.LoweredBody original
                && original.functionId().equals(new FunctionId(1))
                && original.blockId().equals(new BlockId(1)),
            "the original registration stays intact after every rejected duplicate "
                + "(fail closed, never overwritten)");
    }

    /**
     * A function-typed materialization without its producer facts is not
     * silently skipped — the seam fails explicitly: missing facts,
     * facts without a producer module id, a non-function fact
     * descriptor, payload/facts mismatches, a foreign payload record,
     * and a cross-module import without a route record for the callee
     * all raise.
     */
    static void testMissingOrMismatchedProducerFactsFailExplicitly() {
        System.out.println("-- missing/mismatched producer facts fail explicitly --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        ModuleId host = new ModuleId("host");
        ModuleId lib = new ModuleId("lib");
        KindPayload.MemberReadPayload member =
            new KindPayload.MemberReadPayload(new ValueId(11), "g");

        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70), member, null, null),
                "null producer facts fail explicitly (never silently skipped)"),
            "null producer facts fail explicitly (never silently skipped)");
        check(throwsWhen(() -> new FunctionBindingRegistry.FunctionValueImportFacts(null,
                    null, "g", NULL_FUNC),
                "facts without a producer module id fail explicitly"),
            "facts without a producer module id fail explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70), member,
                    new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "g",
                        RuntimeDescriptor.Int.INSTANCE),
                    null),
                "a non-function fact descriptor fails explicitly"),
            "a non-function fact descriptor fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70), member,
                    new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "x",
                        NULL_FUNC),
                    null),
                "a member-read key/facts export-name mismatch fails explicitly"),
            "a member-read key/facts export-name mismatch fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.ExportReadPayload(lib, "pick", NULL_FUNC,
                        new ValueId(70)),
                    new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "pick",
                        NULL_FUNC),
                    null),
                "an export-read module/facts module mismatch fails explicitly"),
            "an export-read module/facts module mismatch fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.ExportReadPayload(host, "other", NULL_FUNC,
                        new ValueId(70)),
                    new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "pick",
                        NULL_FUNC),
                    null),
                "an export-read name/facts export-name mismatch fails explicitly"),
            "an export-read name/facts export-name mismatch fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.ExportReadPayload(host, "pick", INT_FUNC,
                        new ValueId(70)),
                    new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "pick",
                        NULL_FUNC),
                    null),
                "an export-read descriptor/facts descriptor mismatch fails explicitly"),
            "an export-read descriptor/facts descriptor mismatch fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.ArrayLengthPayload(new ValueId(11)),
                    new FunctionBindingRegistry.FunctionValueImportFacts(host, null, "g",
                        NULL_FUNC),
                    null),
                "a foreign payload record (not member-read/export-read) fails explicitly"),
            "a foreign payload record (not member-read/export-read) fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70), member,
                    new FunctionBindingRegistry.FunctionValueImportFacts(null, lib, "g",
                        NULL_FUNC),
                    plan(Map.of())),
                "a cross-module import without a route record for the callee fails "
                    + "explicitly"),
            "a cross-module import without a route record for the callee fails explicitly");
        check(throwsWhen(() -> registry.registerHostOrExternalImport(
                    new FunctionAllocationIdentity(70), member,
                    new FunctionBindingRegistry.FunctionValueImportFacts(null, lib, "g",
                        NULL_FUNC),
                    null),
                "a cross-module import without a plan fails explicitly"),
            "a cross-module import without a plan fails explicitly");
        check(throwsWhen(() -> registry.registerHostFunctionValue(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.BoundaryPayload(BoundaryKind.DEAL_TO_HOST, NULL_FUNC,
                        new ValueId(70), new BoundaryRealization.RuntimeValidation("c")),
                    new OpId(host, 99), host),
                "a non-HOST_TO_DEAL boundary kind fails explicitly"),
            "a non-HOST_TO_DEAL boundary kind fails explicitly");
        check(throwsWhen(() -> registry.registerHostFunctionValue(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.BoundaryPayload(BoundaryKind.HOST_TO_DEAL,
                        RuntimeDescriptor.Int.INSTANCE, new ValueId(70),
                        new BoundaryRealization.RuntimeValidation("c")),
                    new OpId(host, 99), host),
                "a non-function boundary descriptor fails explicitly"),
            "a non-function boundary descriptor fails explicitly");
        check(throwsWhen(() -> registry.registerHostFunctionValue(
                    new FunctionAllocationIdentity(70),
                    new KindPayload.BoundaryPayload(BoundaryKind.HOST_TO_DEAL, NULL_FUNC,
                        new ValueId(71), new BoundaryRealization.RuntimeValidation("c")),
                    new OpId(host, 99), host),
                "a boundary input that is not the produced identity fails explicitly"),
            "a boundary input that is not the produced identity fails explicitly");
        check(registry.size() == 0 && registry.materializations().isEmpty(),
            "every rejected materialization leaves the registry untouched (no partial "
                + "registration, no silent skip)");
    }

    /**
     * Registry-level immutability and determinism: the snapshot map is
     * unmodifiable and insertion-ordered, and two registries built with
     * the same registration sequence iterate identically.
     */
    static void testRegistrySnapshotImmutabilityAndIterationOrder() {
        System.out.println("-- registry snapshot: unmodifiable, insertion-ordered --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity first = new FunctionAllocationIdentity(80);
        FunctionAllocationIdentity second = new FunctionAllocationIdentity(81);
        registry.registerClosure(first, new FunctionId(1), new BlockId(1));
        registry.registerGroupMember(second, new FunctionId(2), new BlockId(2));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> snapshot =
            registry.bindings();
        check(new ArrayList<>(snapshot.keySet()).equals(List.of(first, second)),
            "the snapshot iterates in registration (insertion) order");
        check(throwsWhen(() -> snapshot.put(new FunctionAllocationIdentity(82),
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(3),
                        new BlockId(3))),
                "the snapshot map is unmodifiable"),
            "the snapshot map is unmodifiable");
        check(snapshot.size() == 2,
            "the snapshot still holds exactly the two registrations");

        FunctionBindingRegistry replay = new FunctionBindingRegistry();
        replay.registerClosure(first, new FunctionId(1), new BlockId(1));
        replay.registerGroupMember(second, new FunctionId(2), new BlockId(2));
        check(new ArrayList<>(replay.bindings().keySet()).equals(
                new ArrayList<>(snapshot.keySet()))
                && new ArrayList<>(replay.bindings().values()).equals(
                    new ArrayList<>(snapshot.values())),
            "the same registration sequence yields the same map with identical iteration "
                + "order across registry instances");
    }

    /**
     * Non-production boundary (negative): this child adds no
     * member-read/export-read op production path — a module member
     * access of a function-typed import still fails closed with the
     * pinned E6005 {@code CONSTRUCT_UNLOWERED}, and no unit is produced.
     */
    static void testNoMemberReadOrExportReadProductionPath() {
        System.out.println("-- no member-read/export-read production path: module member "
            + "access still fails closed --");

        StubModuleResolver resolver = new StubModuleResolver();
        resolver.register("stub/host",
            Map.of("g", new Type.Func(List.of(), Type.Null.INSTANCE)));
        CheckedSlice slice = checkSlice("""
            import * as host from "stub/host";
            function f(): null {
              let h: () => null = host.g;
            }
            """, resolver);
        if (slice == null) {
            return;
        }
        SemanticLowerer.ClosureCoreResult result = SemanticLowerer.lowerModuleClosureCore(
            moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
        check(result.lowering().unit() == null && result.lowering().hasErrors(),
            "the member-access slice produces no unit (fail closed)");
        if (result.lowering().hasErrors()) {
            CompilerDiagnostic diagnostic = result.lowering().diagnostics().get(0);
            check("E6005".equals(diagnostic.code())
                    && diagnostic.message().contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
                "the member access converts to E6005 CONSTRUCT_UNLOWERED (this child added "
                    + "no MEMBER_READ/EXPORT_READ production path): " + diagnostic);
        }
    }

    /**
     * Determinism: lowering the same checked module twice through fresh
     * allocators yields the same registry map with identical iteration
     * order and byte-identical validated unit dumps (B9/D10).
     */
    static void testDeterminism() {
        System.out.println("-- determinism: same map, identical iteration order, "
            + "byte-identical dumps --");

        String source = """
            function f(): null {
              let gRef = g;
            }
            function g(): null {
              let fRef = f;
            }
            function h(): null {}
            """;
        SemanticLowerer.GroupCoreResult first = lowerGroupSlice(source);
        SemanticLowerer.GroupCoreResult second = lowerGroupSlice(source);
        if (first == null || second == null
                || first.lowering().hasErrors() || second.lowering().hasErrors()
                || first.lowering().unit() == null || second.lowering().unit() == null) {
            fail("the slice lowers to validated units on both runs");
            return;
        }
        check(new ArrayList<>(
                first.lowering().unit().functionBindings().keySet()).equals(
                    new ArrayList<>(
                        second.lowering().unit().functionBindings().keySet())),
            "the two runs produce the same registry keys in the identical iteration order");
        check(new ArrayList<>(
                first.lowering().unit().functionBindings().values()).equals(
                    new ArrayList<>(
                        second.lowering().unit().functionBindings().values())),
            "the two runs produce the same registry bindings in the identical iteration "
                + "order");
        String firstDump = SemanticIrDumper.dumpModuleText(first.lowering().unit());
        String secondDump = SemanticIrDumper.dumpModuleText(second.lowering().unit());
        check(firstDump.equals(secondDump),
            "repeated lowering produces byte-identical deal.semantic-ir/1 dumps");
        check(Arrays.equals(SemanticIrDumper.dumpModule(first.lowering().unit()),
                SemanticIrDumper.dumpModule(second.lowering().unit())),
            "the dump bytes are identical");
    }

    // =========================================================================
    // Driver
    // =========================================================================

    public static void main(String[] args) {
        testClosureRegistrationKeysExactlyClosureNewResultIdentities();
        testGroupRegistrationOneLoweredBodyPerMember();
        testMemberReadHostFactsRegisterHostFunction();
        testExportReadHostFactsRegisterHostFunction();
        testCrossModuleSharedRouteRegistersExternalFunctionSharedBody();
        testCrossModuleRetainedAbiRouteRegistersExternalFunctionRetainedAbi();
        testHostToDealBoundaryFactsRegisterHostFunctionValue();
        testAdapterRegistrationSeam();
        testFiveClosedShapesInOneRegistry();
        testDuplicateKeyRejectedAtRegistrationTime();
        testMissingOrMismatchedProducerFactsFailExplicitly();
        testRegistrySnapshotImmutabilityAndIterationOrder();
        testNoMemberReadOrExportReadProductionPath();
        testDeterminism();
        System.out.println();
        System.out.println("FunctionBindingRegistryTest: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
