package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
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
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The recursive-group child's lowering tests (ISSUE-0446 sequencing item
 * 3): per-scope SCC partition over function declarations and one
 * {@code RECURSIVE_GROUP_INIT} op per size>=2 SCC with the
 * declaration-ordered member {@code {bindings, functions}} payload,
 * pre-assigned unique member allocation identities, module-init-top
 * placement for module-level groups and first-member-position placement
 * for nested-scope groups, member loads resolving to the group op as the
 * producing allocation at generation 0 with no separate
 * {@code BINDING_ALLOC}/{@code BINDING_INIT}, member bodies lowering
 * like any function body with captures (B3), and size-1 SCCs —
 * self-recursive declarations included — lowering as {@code CLOSURE_NEW}
 * + {@code BINDING_INIT} at the declaration position — driven through
 * the child's public lowering entry point
 * ({@link SemanticLowerer#lowerModuleGroupCore}) with the produced
 * units validated by the closed validator and the address-chain
 * protocol under the pinned E6-gate activation.
 *
 * <p><b>Coverage.</b></p>
 * <ul>
 *   <li>a mutual-recursion pair lowers to exactly one group op with
 *       declaration-ordered member lists and unique pre-assigned member
 *       identities;</li>
 *   <li>a self-recursive function lowers to {@code CLOSURE_NEW} +
 *       {@code BINDING_INIT} with no group op;</li>
 *   <li>a module-level group's op sits at module-init top;</li>
 *   <li>a nested-scope group's op sits at the first member's declaration
 *       position;</li>
 *   <li>member references inside member bodies resolve to
 *       {@code {binding, generation 0}} with the group op as the
 *       producing allocation; no member has a separate ALLOC/INIT;</li>
 *   <li>an unreferenced sibling declaration is not grouped (minimal SCC
 *       partition);</li>
 *   <li>a module-level group whose member body captures a later-declared
 *       module function resolves the capture to the hoisted ALLOC and
 *       the group op still precedes the capturing closure site
 *       (combined with the binding-core and closure children — fails if
 *       either earlier module is broken);</li>
 *   <li>determinism: repeated lowering produces byte-identical dumps;</li>
 *   <li>fail-closed negatives: a foreign statement inside a member body
 *       and the legacy profile guard convert to the pinned E6005.</li>
 * </ul>
 */
public class RecursiveGroupLoweringTest {

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

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    // =========================================================================
    // Checked-source slices and the entry-point driver
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver("test.deal", null);
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

    private static SemanticLowerer.GroupCoreResult lowerSlice(String source) {
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

    /** The binding facts entry of a declared name (registered exactly once). */
    private static SemanticLowerer.BindingCoreBinding fact(
            SemanticLowerer.BindingCoreFacts facts, String name) {
        List<SemanticLowerer.BindingCoreBinding> matches = new ArrayList<>();
        for (SemanticLowerer.BindingCoreBinding binding : facts.bindings()) {
            if (binding.name().equals(name)) {
                matches.add(binding);
            }
        }
        check(matches.size() == 1, "exactly one BindingId registered for '" + name
            + "'; got " + matches.size());
        return matches.size() == 1 ? matches.get(0) : null;
    }

    private static int indexOf(List<SemanticOp> ops, OpId opId) {
        for (int i = 0; i < ops.size(); i++) {
            if (ops.get(i).opId().equals(opId)) {
                return i;
            }
        }
        fail("op " + opId + " not found in the produced op list");
        return -1;
    }

    /** True iff any produced op of the kind names the given binding. */
    private static boolean anyOpNames(List<SemanticOp> ops, SemanticOpKind kind,
                                      BindingId binding) {
        for (SemanticOp op : ops) {
            switch (op.payload()) {
                case KindPayload.BindingAllocPayload alloc -> {
                    if (kind == SemanticOpKind.BINDING_ALLOC
                            && alloc.binding().equals(binding)) {
                        return true;
                    }
                }
                case KindPayload.BindingInitPayload init -> {
                    if (kind == SemanticOpKind.BINDING_INIT
                            && init.binding().equals(binding)) {
                        return true;
                    }
                }
                case KindPayload.BindingLoadPayload load -> {
                    if (kind == SemanticOpKind.BINDING_LOAD
                            && load.binding().equals(binding)) {
                        return true;
                    }
                }
                case KindPayload.BindingStorePayload store -> {
                    if (kind == SemanticOpKind.BINDING_STORE
                            && store.binding().equals(binding)) {
                        return true;
                    }
                }
                default -> { }
            }
        }
        return false;
    }

    // =========================================================================
    // Tests
    // =========================================================================

    /**
     * A mutual-recursion pair lowers to exactly one {@code RECURSIVE_GROUP_INIT}
     * op with declaration-ordered member {@code {bindings, functions}}
     * lists and unique pre-assigned member identities; the op has no
     * result slot; no member carries a separate ALLOC/INIT; member loads
     * inside member bodies name {@code {binding, generation 0}} and
     * publish the member identity; member incarnations record the group
     * op as their producing allocation with {@code SHARED_CELL} cells;
     * and the module-level group op sits at module-init top.
     */
    static void testMutualRecursionPairLowersToOneGroupOp() {
        System.out.println("-- mutual recursion: one group op, declaration-ordered members, "
            + "pre-assigned identities, module-init-top placement --");

        SemanticLowerer.GroupCoreResult result = lowerSlice("""
            function f(): null {
              let gRef: () => null = g;
            }
            function g(): null {
              let fRef: () => null = f;
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        if (f == null || g == null) {
            return;
        }

        // Exactly one group op; no CLOSURE_NEW.
        List<SemanticOp> groups = ofKind(ops, SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(groups.size() == 1, "exactly one RECURSIVE_GROUP_INIT op; got " + groups.size());
        check(ofKind(ops, SemanticOpKind.CLOSURE_NEW).isEmpty(),
            "no CLOSURE_NEW op for group members");
        if (groups.size() != 1) {
            return;
        }
        SemanticOp groupOp = groups.get(0);
        check(groupOp.result() == null && groupOp.resultType() == null,
            "the group op has no result slot (the bindings are the observable effect)");
        KindPayload.RecursiveGroupInitPayload payload =
            (KindPayload.RecursiveGroupInitPayload) groupOp.payload();
        check(payload.bindings().equals(List.of(f.binding(), g.binding())),
            "the group payload carries the member bindings in declaration order "
                + "[f, g]; got " + payload.bindings());
        check(payload.functions().size() == 2,
            "the group payload carries exactly two member functions; got "
                + payload.functions().size());

        // The GroupFacts record: declaration-ordered members, unique
        // pre-assigned identities.
        check(result.groups().size() == 1,
            "exactly one group-facts record; got " + result.groups().size());
        if (result.groups().size() != 1) {
            return;
        }
        SemanticLowerer.GroupFacts groupFacts = result.groups().get(0);
        check(groupFacts.opId().equals(groupOp.opId()),
            "the group-facts record names the produced group op");
        check(groupFacts.members().size() == 2,
            "exactly two member-facts records; got " + groupFacts.members().size());
        if (groupFacts.members().size() != 2) {
            return;
        }
        SemanticLowerer.GroupMemberFacts fMember = groupFacts.members().get(0);
        SemanticLowerer.GroupMemberFacts gMember = groupFacts.members().get(1);
        check(fMember.name().equals("f") && fMember.binding().equals(f.binding()),
            "the first member fact is f with f's binding");
        check(gMember.name().equals("g") && gMember.binding().equals(g.binding()),
            "the second member fact is g with g's binding");
        check(!fMember.identity().equals(gMember.identity()),
            "member identities are unique per member");
        Set<Long> identityIds = new HashSet<>();
        for (SemanticLowerer.GroupMemberFacts member : groupFacts.members()) {
            identityIds.add(member.identity().id());
        }
        check(identityIds.size() == 2, "all member identities distinct; got " + identityIds);

        // Member incarnations: generation 0, the group op as producing
        // allocation, SHARED_CELL, module-init scope, no separate
        // ALLOC/INIT op.
        for (SemanticLowerer.BindingCoreBinding member : List.of(f, g)) {
            check(member.incarnations().size() == 1,
                "member '" + member.name() + "' has exactly one incarnation; got "
                    + member.incarnations().size());
            if (member.incarnations().size() != 1) {
                continue;
            }
            SemanticLowerer.BindingCoreIncarnation incarnation = member.incarnations().get(0);
            check(incarnation.generation() == 0,
                "member '" + member.name() + "' incarnation generation 0");
            check(incarnation.producer() == SemanticLowerer.BindingProducer.RECURSIVE_GROUP_INIT,
                "member '" + member.name() + "' resolves to the group op as its producing "
                    + "allocation; got " + incarnation.producer());
            check(incarnation.cellKind() == BindingCellKind.SHARED_CELL,
                "member '" + member.name() + "' cell is SHARED_CELL by construction; got "
                    + incarnation.cellKind());
            check(incarnation.scope().equals(unit.moduleInit().initBlock()),
                "member '" + member.name() + "' incarnation sits in the module-init block");
            check(!anyOpNames(ops, SemanticOpKind.BINDING_ALLOC, member.binding()),
                "member '" + member.name() + "' has no separate BINDING_ALLOC");
            check(!anyOpNames(ops, SemanticOpKind.BINDING_INIT, member.binding()),
                "member '" + member.name() + "' has no separate BINDING_INIT");
        }

        // Member references inside member bodies resolve to
        // {binding, generation 0} and publish the member identity.
        SemanticOp fLoad = null;
        SemanticOp gLoad = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
            KindPayload.BindingLoadPayload load = (KindPayload.BindingLoadPayload) op.payload();
            if (load.binding().equals(g.binding()) && load.generation() == 0) {
                fLoad = op;
            }
            if (load.binding().equals(f.binding()) && load.generation() == 0) {
                gLoad = op;
            }
        }
        check(fLoad != null, "f's body load of g names {g, generation 0}");
        check(gLoad != null, "g's body load of f names {f, generation 0}");
        if (fLoad != null) {
            check(fLoad.result() != null && fLoad.result().equals(gMember.identity()),
                "f's load of g publishes g's pre-assigned member identity");
        }
        if (gLoad != null) {
            check(gLoad.result() != null && gLoad.result().equals(fMember.identity()),
                "g's load of f publishes f's pre-assigned member identity");
        }

        // One LoweredBody registration per member keyed by the member
        // identity; the LoweredFunction records carry the bodies.
        check(unit.functionBindings().get(new FunctionAllocationIdentity(
                    fMember.identity().id()))
                instanceof FunctionExecutionBinding.LoweredBody fBody
                && fBody.functionId().equals(fMember.functionId())
                && fBody.blockId().equals(fMember.bodyBlock()),
            "f's LoweredBody registration keyed by f's member identity");
        check(unit.functionBindings().get(new FunctionAllocationIdentity(
                    gMember.identity().id()))
                instanceof FunctionExecutionBinding.LoweredBody gBody
                && gBody.functionId().equals(gMember.functionId())
                && gBody.blockId().equals(gMember.bodyBlock()),
            "g's LoweredBody registration keyed by g's member identity");
        LoweredFunction fRecord = unit.functions().get(fMember.functionId());
        LoweredFunction gRecord = unit.functions().get(gMember.functionId());
        check(fRecord != null && fRecord.captureBindings().equals(List.of(g.binding())),
            "f's LoweredFunction record carries captures = [g] (capture-by-binding, B3)");
        check(gRecord != null && gRecord.captureBindings().equals(List.of(f.binding())),
            "g's LoweredFunction record carries captures = [f] (capture-by-binding, B3)");
        check(fMember.captures().size() == 1
                && fMember.captures().get(0).binding().equals(g.binding())
                && fMember.captures().get(0).producer()
                    == SemanticLowerer.BindingProducer.RECURSIVE_GROUP_INIT,
            "f's member-fact capture of g resolves to the group op as the producing "
                + "allocation");
        check(gMember.captures().size() == 1
                && gMember.captures().get(0).binding().equals(f.binding())
                && gMember.captures().get(0).producer()
                    == SemanticLowerer.BindingProducer.RECURSIVE_GROUP_INIT,
            "g's member-fact capture of f resolves to the group op as the producing "
                + "allocation");

        // Module-init-top placement: the group op precedes every
        // declaration-position op (no closures here, so assert the group
        // op follows the module-init-top intrinsic seeds and precedes
        // every body op).
        int groupIndex = indexOf(ops, groupOp.opId());
        check(groupIndex >= 0, "the group op appears in the produced op list");
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BINDING_ALLOC
                    && op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && alloc.scope().equals(unit.moduleInit().initBlock())
                    && indexOf(ops, op.opId()) > groupIndex) {
                fail("a module-init-block ALLOC op follows the group op — the group op "
                    + "is not at module-init top: " + op.opId());
                break;
            }
        }
        check(groupFacts.block().equals(unit.moduleInit().initBlock()),
            "the group op sits in the module-init block");
    }

    /**
     * A self-recursive function is a size-1 SCC: it lowers as
     * {@code CLOSURE_NEW} + {@code BINDING_INIT} at the declaration
     * position with no group op.
     */
    static void testSelfRecursiveFunctionLowersToClosureNew() {
        System.out.println("-- self-recursion: CLOSURE_NEW + BINDING_INIT, no group op --");

        SemanticLowerer.GroupCoreResult result = lowerSlice("""
            function f(): null {
              let self: () => null = f;
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        if (f == null) {
            return;
        }
        check(ofKind(ops, SemanticOpKind.RECURSIVE_GROUP_INIT).isEmpty(),
            "no group op for a size-1 SCC");
        check(result.groups().isEmpty(), "no group-facts record for a size-1 SCC");
        List<SemanticOp> closures = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closures.size() == 1, "exactly one CLOSURE_NEW for the self-recursive "
            + "declaration; got " + closures.size());
        boolean initCommitsName = false;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.binding().equals(f.binding())
                    && op.result() == null) {
                initCommitsName = true;
            }
        }
        check(initCommitsName, "the BINDING_INIT commits the closure identity to the name "
            + "binding at the declaration position");
        check(anyOpNames(ops, SemanticOpKind.BINDING_ALLOC, f.binding()),
            "the self-recursive declaration keeps its hoisted name ALLOC (B1)");
    }

    /**
     * A nested-scope mutual-recursion pair lowers to one group op at the
     * first member's declaration position: the op follows the statements
     * before the first member and precedes the statements after it, and
     * the member incarnations sit in the enclosing body block.
     */
    static void testNestedScopeGroupAtFirstMemberPosition() {
        System.out.println("-- nested-scope group: first-member declaration position --");

        SemanticLowerer.GroupCoreResult result = lowerSlice("""
            function outer(): null {
              let before: int = 1;
              function f(): null {
                let gRef: () => null = g;
              }
              function g(): null {
                let fRef: () => null = f;
              }
              let after: int = 2;
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding outer = fact(result.bindingFacts(), "outer");
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        SemanticLowerer.BindingCoreBinding before = fact(result.bindingFacts(), "before");
        SemanticLowerer.BindingCoreBinding after = fact(result.bindingFacts(), "after");
        if (outer == null || f == null || g == null || before == null || after == null) {
            return;
        }
        List<SemanticOp> groups = ofKind(ops, SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(groups.size() == 1, "exactly one nested-scope group op; got " + groups.size());
        if (groups.size() != 1) {
            return;
        }
        SemanticOp groupOp = groups.get(0);
        int groupIndex = indexOf(ops, groupOp.opId());
        int beforeIndex = -1;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.binding().equals(before.binding())) {
                beforeIndex = indexOf(ops, op.opId());
            }
        }
        int afterIndex = -1;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_ALLOC)) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && alloc.binding().equals(after.binding())) {
                afterIndex = indexOf(ops, op.opId());
            }
        }
        check(beforeIndex >= 0 && groupIndex > beforeIndex,
            "the group op follows the statements before the first member");
        check(afterIndex >= 0 && groupIndex < afterIndex,
            "the group op precedes the statements after the first member");

        // The member incarnations sit in outer's body block (the group
        // op's block), not in the module-init block.
        SemanticLowerer.BindingCoreIncarnation fIncarnation = f.incarnations().get(0);
        SemanticLowerer.BindingCoreIncarnation gIncarnation = g.incarnations().get(0);
        if (fIncarnation.scope().equals(unit.moduleInit().initBlock())) {
            fail("nested member f's incarnation must not sit in the module-init block");
        }
        if (gIncarnation.scope().equals(unit.moduleInit().initBlock())) {
            fail("nested member g's incarnation must not sit in the module-init block");
        }
        check(fIncarnation.generation() == 0
                && fIncarnation.producer() == SemanticLowerer.BindingProducer.RECURSIVE_GROUP_INIT,
            "nested member f resolves to the group op at generation 0");
        check(gIncarnation.generation() == 0
                && gIncarnation.producer() == SemanticLowerer.BindingProducer.RECURSIVE_GROUP_INIT,
            "nested member g resolves to the group op at generation 0");
        check(result.groups().size() == 1
                && result.groups().get(0).block().equals(fIncarnation.scope())
                && result.groups().get(0).block().equals(gIncarnation.scope()),
            "the group op's block equals the members' incarnation scope (outer's body block)");
        // outer's own body block equals the members' scope (the
        // declaration-position placement is inside outer's body).
        BlockId outerBody = null;
        for (SemanticLowerer.ClosureFacts closure : result.closures()) {
            if (closure.captures().isEmpty()) {
                outerBody = closure.bodyBlock();
            }
        }
        check(outerBody != null && outerBody.equals(fIncarnation.scope()),
            "the members sit in outer's body block");
    }

    /**
     * An unreferenced sibling declaration is not grouped: the mutual
     * pair forms the only group, the sibling lowers as CLOSURE_NEW, and
     * the group payload names exactly the two members.
     */
    static void testUnreferencedSiblingNotGrouped() {
        System.out.println("-- minimal SCC partition: an unreferenced sibling stays out --");

        SemanticLowerer.GroupCoreResult result = lowerSlice("""
            function f(): null {
              let gRef: () => null = g;
            }
            function g(): null {
              let fRef: () => null = f;
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
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        SemanticLowerer.BindingCoreBinding h = fact(result.bindingFacts(), "h");
        if (f == null || g == null || h == null) {
            return;
        }
        List<SemanticOp> groups = ofKind(ops, SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(groups.size() == 1, "exactly one group op; got " + groups.size());
        if (groups.size() != 1) {
            return;
        }
        KindPayload.RecursiveGroupInitPayload payload =
            (KindPayload.RecursiveGroupInitPayload) groups.get(0).payload();
        check(payload.bindings().equals(List.of(f.binding(), g.binding())),
            "the group payload names exactly [f, g]; got " + payload.bindings());
        List<SemanticOp> closures = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closures.size() == 1, "exactly one CLOSURE_NEW for the unreferenced sibling h; "
            + "got " + closures.size());
        if (closures.size() == 1) {
            check(closures.get(0).payload() instanceof KindPayload.ClosureNewPayload closure
                    && unit.functions().get(closure.function()) != null,
                "h's CLOSURE_NEW carries h's LoweredFunction record");
        }
        check(anyOpNames(ops, SemanticOpKind.BINDING_ALLOC, h.binding()),
            "h keeps its hoisted name ALLOC (not a group member)");
    }

    /**
     * Combined with the binding-core and closure children: a module-level
     * group whose member body captures a later-declared module function
     * resolves the capture to the hoisted ALLOC and the group op still
     * precedes the capturing closure site (B1/B3/B4).
     */
    static void testGroupMemberBodyCapturesLaterDeclaredModuleFunction() {
        System.out.println("-- module-level group + later-declared module function capture: "
            + "hoisted ALLOC resolution, group op before the closure site --");

        SemanticLowerer.GroupCoreResult result = lowerSlice("""
            function f(): null {
              let h: () => null = function(): null {
                let copy: () => null = laterFn;
              };
              let gRef: () => null = g;
            }
            function g(): null {
              let fRef: () => null = f;
            }
            function laterFn(): null {}
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        SemanticLowerer.BindingCoreBinding laterFn = fact(result.bindingFacts(), "laterFn");
        if (f == null || g == null || laterFn == null) {
            return;
        }
        List<SemanticOp> groups = ofKind(ops, SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(groups.size() == 1, "exactly one group op for {f, g}; got " + groups.size());
        if (groups.size() != 1) {
            return;
        }
        SemanticOp groupOp = groups.get(0);
        KindPayload.RecursiveGroupInitPayload payload =
            (KindPayload.RecursiveGroupInitPayload) groupOp.payload();
        check(payload.bindings().equals(List.of(f.binding(), g.binding())),
            "the group payload names [f, g] in declaration order");

        // laterFn stays a size-1 SCC: CLOSURE_NEW at the declaration
        // position reusing the hoist-time pre-allocated identity.
        List<SemanticOp> closures = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closures.size() == 2, "two CLOSURE_NEWs (h and laterFn); got " + closures.size());
        SemanticOp laterClosure = null;
        for (SemanticOp op : closures) {
            if (op.payload() instanceof KindPayload.ClosureNewPayload closure
                    && closure.captures().isEmpty()
                    && op.result() != null) {
                laterClosure = op;
            }
        }
        check(laterClosure != null, "laterFn's CLOSURE_NEW found");

        // The capture resolution: the nested closure h captures laterFn
        // at the hoisted ALLOC; the detaching-chain propagation records
        // laterFn in f's member captures too.
        List<SemanticLowerer.ClosureCapture> hCapture = null;
        for (SemanticLowerer.ClosureFacts facts : result.closures()) {
            if (facts.captures().size() == 1
                    && facts.captures().get(0).binding().equals(laterFn.binding())) {
                hCapture = facts.captures();
            }
        }
        check(hCapture != null, "h's closure captures [laterFn]");
        if (hCapture != null) {
            check(hCapture.get(0).generation() == 0
                    && hCapture.get(0).producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC
                    && hCapture.get(0).scope().equals(unit.moduleInit().initBlock()),
                "h's capture of laterFn resolves to the hoisted module-init ALLOC");
        }
        SemanticLowerer.GroupMemberFacts fMember = null;
        if (result.groups().size() == 1 && result.groups().get(0).members().size() == 2) {
            fMember = result.groups().get(0).members().get(0);
        }
        check(fMember != null && fMember.captures().size() == 2,
            "f's member captures record laterFn and g (the detaching chain); got "
                + (fMember == null ? "no member facts" : fMember.captures()));
        if (fMember != null && fMember.captures().size() == 2) {
            SemanticLowerer.ClosureCapture laterFnCapture = null;
            for (SemanticLowerer.ClosureCapture capture : fMember.captures()) {
                if (capture.binding().equals(laterFn.binding())) {
                    laterFnCapture = capture;
                }
            }
            check(laterFnCapture != null && laterFnCapture.generation() == 0
                    && laterFnCapture.producer()
                        == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                "f's capture of laterFn resolves to the hoisted ALLOC at generation 0");
        }

        // The group op precedes the capturing closure site (h's
        // CLOSURE_NEW) in the op list.
        if (laterClosure != null) {
            check(indexOf(ops, groupOp.opId()) < indexOf(ops, laterClosure.opId()),
                "the group op precedes the capturing closure site");
        }

        // The load of laterFn inside h's body publishes the hoisted
        // identity that laterFn's own CLOSURE_NEW reuses.
        if (laterClosure != null) {
            boolean loadPublishes = false;
            for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
                if (op.payload() instanceof KindPayload.BindingLoadPayload load
                        && load.binding().equals(laterFn.binding())
                        && op.result() != null && op.result().equals(laterClosure.result())) {
                    loadPublishes = true;
                }
            }
            check(loadPublishes,
                "the load of laterFn publishes the identity laterFn's CLOSURE_NEW reuses");
        }
    }

    /**
     * Two disjoint module-level groups emit at module-init top in
     * declaration order of their first members.
     */
    static void testMultipleModuleLevelGroupsInDeclarationOrder() {
        System.out.println("-- multiple module-level groups: declaration order --");

        SemanticLowerer.GroupCoreResult result = lowerSlice("""
            function a(): null {
              let bRef: () => null = b;
            }
            function b(): null {
              let aRef: () => null = a;
            }
            function c(): null {
              let dRef: () => null = d;
            }
            function d(): null {
              let cRef: () => null = c;
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding a = fact(result.bindingFacts(), "a");
        SemanticLowerer.BindingCoreBinding b = fact(result.bindingFacts(), "b");
        SemanticLowerer.BindingCoreBinding c = fact(result.bindingFacts(), "c");
        SemanticLowerer.BindingCoreBinding d = fact(result.bindingFacts(), "d");
        if (a == null || b == null || c == null || d == null) {
            return;
        }
        List<SemanticOp> groups = ofKind(ops, SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(groups.size() == 2, "exactly two group ops; got " + groups.size());
        if (groups.size() != 2) {
            return;
        }
        KindPayload.RecursiveGroupInitPayload first =
            (KindPayload.RecursiveGroupInitPayload) groups.get(0).payload();
        KindPayload.RecursiveGroupInitPayload second =
            (KindPayload.RecursiveGroupInitPayload) groups.get(1).payload();
        check(first.bindings().equals(List.of(a.binding(), b.binding())),
            "the first group op carries [a, b] in declaration order");
        check(second.bindings().equals(List.of(c.binding(), d.binding())),
            "the second group op carries [c, d] in declaration order");
        check(indexOf(ops, groups.get(0).opId()) < indexOf(ops, groups.get(1).opId()),
            "the group ops sit at module-init top in declaration order of their first "
                + "members");
        check(result.groups().size() == 2,
            "two group-facts records; got " + result.groups().size());
    }

    /**
     * Determinism: lowering the same checked module twice through fresh
     * allocators produces byte-identical validated unit dumps (B9/D10).
     */
    static void testDeterminism() {
        System.out.println("-- determinism: byte-identical dumps across repeated lowering --");

        String source = """
            function f(): null {
              let gRef: () => null = g;
              let self: () => null = f;
            }
            function g(): null {
              let fRef: () => null = f;
            }
            function h(): null {}
            """;
        SemanticLowerer.GroupCoreResult first = lowerSlice(source);
        SemanticLowerer.GroupCoreResult second = lowerSlice(source);
        if (first == null || second == null
                || first.lowering().hasErrors() || second.lowering().hasErrors()
                || first.lowering().unit() == null || second.lowering().unit() == null) {
            fail("the slice lowers to validated units on both runs");
            return;
        }
        String firstDump = SemanticIrDumper.dumpModuleText(first.lowering().unit());
        String secondDump = SemanticIrDumper.dumpModuleText(second.lowering().unit());
        check(firstDump.equals(secondDump),
            "repeated lowering produces byte-identical deal.semantic-ir/1 dumps");
        check(first.lowering().unit().ops().size() == second.lowering().unit().ops().size(),
            "repeated lowering produces the same op count");
    }

    /**
     * Fail-closed negatives: a foreign statement inside a member body
     * converts to the pinned E6005 {@code CONSTRUCT_UNLOWERED}; the
     * legacy profile guard converts to E6005
     * {@code LOWER_LEGACY_PROFILE_REJECTED}.
     */
    static void testFailClosedNegatives() {
        System.out.println("-- fail-closed negatives: foreign member-body statement, "
            + "legacy profile guard --");

        SemanticLowerer.GroupCoreResult foreign = lowerSlice("""
            function f(): null {
              g();
            }
            function g(): null {
              let fRef: () => null = f;
            }
            """);
        if (foreign == null) {
            fail("the foreign-statement slice checks");
            return;
        }
        check(foreign.lowering().unit() == null && foreign.lowering().hasErrors(),
            "a call inside a member body fails closed (no unit)");
        if (foreign.lowering().hasErrors()) {
            CompilerDiagnostic diagnostic = foreign.lowering().diagnostics().get(0);
            check("E6005".equals(diagnostic.code())
                    && diagnostic.message().contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
                "the foreign member-body statement converts to E6005 CONSTRUCT_UNLOWERED: "
                    + diagnostic);
        }

        CheckedSlice slice = checkSlice("""
            function f(): null {
              let gRef: () => null = g;
            }
            function g(): null {
              let fRef: () => null = f;
            }
            """);
        if (slice == null) {
            fail("the profile-guard slice checks");
            return;
        }
        SemanticLowerer.GroupCoreResult legacy = SemanticLowerer.lowerModuleGroupCore(
            moduleOf(slice), SemanticProfile.LEGACY_SAFE_INT, Map.of(), INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
        check(legacy.lowering().unit() == null && legacy.lowering().hasErrors(),
            "a LEGACY_SAFE_INT lowering request produces no unit");
        if (legacy.lowering().hasErrors()) {
            CompilerDiagnostic diagnostic = legacy.lowering().diagnostics().get(0);
            check("E6005".equals(diagnostic.code())
                    && diagnostic.message().contains(
                        SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED),
                "the legacy profile converts to E6005 LOWER_LEGACY_PROFILE_REJECTED: "
                    + diagnostic);
        }
    }

    // =========================================================================
    // Driver
    // =========================================================================

    public static void main(String[] args) {
        testMutualRecursionPairLowersToOneGroupOp();
        testSelfRecursiveFunctionLowersToClosureNew();
        testNestedScopeGroupAtFirstMemberPosition();
        testUnreferencedSiblingNotGrouped();
        testGroupMemberBodyCapturesLaterDeclaredModuleFunction();
        testMultipleModuleLevelGroupsInDeclarationOrder();
        testDeterminism();
        testFailClosedNegatives();
        System.out.println();
        System.out.println("RecursiveGroupLoweringTest: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
