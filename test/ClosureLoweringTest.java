package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
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
import deal.semantic.ir.FailurePolicyId;
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
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.ValueId;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * The closure child's lowering tests (ISSUE-0445 sequencing item 2):
 * {@code CLOSURE_NEW}/{@code LoweredFunction} for every function
 * expression and every size-1 non-group function declaration,
 * capture-by-binding resolution at the detaching op's creation site
 * recursively along the detaching chain, captures of later-declared
 * module functions resolving to the hoisted module-init ALLOC, and the
 * closure-capture arm of the B2 {@code SHARED_CELL} cell-kind upgrade —
 * driven through the child's public lowering entry point
 * ({@link SemanticLowerer#lowerModuleClosureCore}) with the produced
 * units validated by the closed validator, the address-chain protocol,
 * and the claiming seam under the pinned E6-gate activation.
 *
 * <p><b>Coverage.</b></p>
 * <ul>
 *   <li>capture lists in first-reference order with the resolved
 *       generation, producer, and producing-allocation block of each
 *       capture ({@code ClosureCapture});</li>
 *   <li>the doubly-nested capture chain of
 *       {@code test/conformance/backend-runtime/closures/nested-closure-mutation.deal}
 *       (runtime-ok across luajit/jvm/js) lowered in its window shape —
 *       the fixture's {@code return}/{@code call} statements are the
 *       control-flow and call epics' windows, so the equivalent
 *       window-legal shape pins the same detaching chain: the inner
 *       closure's capture of {@code x} resolves to {@code x}'s producing
 *       ALLOC/INIT in {@code test_nested_closure_mutation}'s body while
 *       the intermediate closure {@code make} records
 *       {@code captures = [x]} (B9 R2(ii): the inner closure's creation
 *       site lies inside make's body, so the chain closes inner-body
 *       capture → make's body capture → the R1 step);</li>
 *   <li>captures of later-declared module functions resolving to the
 *       hoisted module-init ALLOC (B1; docs/spec-v1.2.md:1217-1221) with
 *       function-identity preservation on the load (the load publishes
 *       the pre-allocated hoist-time identity the declaration-position
 *       {@code CLOSURE_NEW} reuses);</li>
 *   <li>a closure created inside a for body capturing the per-iteration
 *       incarnation (generation 1) with the counter incarnation staying
 *       {@code DIRECT} (combined with the binding-core child: fails if
 *       the two-incarnation map is broken);</li>
 *   <li>narrowed flow types never captured: capture entries are
 *       {@code BindingId}s carrying no type, and the IR carries the
 *       declared descriptors only;</li>
 *   <li>the closure-capture arm of the B2 cell-kind iff:
 *       closure-captured incarnations {@code SHARED_CELL} (payloads
 *       re-derived through the single derivation — including hoisted
 *       module-function ALLOCs and self-recursive own names),
 *       uncaptured locals {@code DIRECT}, reassignable-uncaptured
 *       locals {@code DIRECT} with the {@code mutable} flag recorded
 *       independently;</li>
 *   <li>the {@code LoweredBody} registration seam: exactly one
 *       {@code functionBindings} entry per closure keyed by its
 *       allocation identity, the identity equal to the
 *       {@code CLOSURE_NEW} result value id;</li>
 *   <li>determinism: capture lists, FunctionId/BlockId allocation, and
 *       unit dumps byte-identical across repeated lowering;</li>
 *   <li>fail-closed negatives: function expressions stay foreign in the
 *       binding-core child's window; a function-typed load of a dynamic
 *       value (a parameter) fails closed as the registry child's
 *       resolution (B5); foreign body statements and the legacy profile
 *       guard convert to the pinned E6005.</li>
 * </ul>
 */
public class ClosureLoweringTest {

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

    private static SemanticLowerer.ClosureCoreResult lowerSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleClosureCore(moduleOf(slice),
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

    /** The closure facts record of a produced {@code CLOSURE_NEW} by function name's facts. */
    private static SemanticLowerer.ClosureFacts closureOf(
            List<SemanticLowerer.ClosureFacts> closures, SemanticOp closureNew) {
        KindPayload.ClosureNewPayload payload =
            (KindPayload.ClosureNewPayload) closureNew.payload();
        List<SemanticLowerer.ClosureFacts> matches = new ArrayList<>();
        for (SemanticLowerer.ClosureFacts facts : closures) {
            if (facts.functionId().equals(payload.function())) {
                matches.add(facts);
            }
        }
        check(matches.size() == 1,
            "exactly one closure-facts record for CLOSURE_NEW " + closureNew.opId()
                + "; got " + matches.size());
        return matches.size() == 1 ? matches.get(0) : null;
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

    /** The CLOSURE_NEW op of a lowered function, by its FunctionId. */
    private static SemanticOp closureNewOf(List<SemanticOp> ops, FunctionId functionId) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.CLOSURE_NEW
                    && op.payload() instanceof KindPayload.ClosureNewPayload payload
                    && payload.function().equals(functionId)) {
                matches.add(op);
            }
        }
        check(matches.size() == 1, "exactly one CLOSURE_NEW for FunctionId " + functionId
            + "; got " + matches.size());
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

    // =========================================================================
    // Tests
    // =========================================================================

    /**
     * A closure capturing two enclosing locals: the capture list carries
     * the bindings in first-reference order, each capture resolves to the
     * dominant incarnation at the creation site (generation 0, the
     * enclosing body block, producer BINDING_ALLOC), the payload and the
     * {@code LoweredFunction} record agree, exactly one
     * {@code LoweredBody} binding is registered per closure keyed by the
     * allocation identity (equal to the CLOSURE_NEW result id), and the
     * captured cells upgrade to {@code SHARED_CELL} while the
     * uncaptured locals stay {@code DIRECT}.
     */
    static void testClosureCapturesEnclosingLocalsInFirstReferenceOrder() {
        System.out.println("-- captures: first-reference order, resolved generation, "
            + "registry one-to-one --");

        SemanticLowerer.ClosureCoreResult result = lowerSlice("""
            function outer(): null {
              let x: int = 1;
              let y: int = 2;
              let h: () => null = function(): null {
                let a: int = y;
                let b: int = x;
              };
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
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        SemanticLowerer.BindingCoreBinding y = fact(result.bindingFacts(), "y");
        SemanticLowerer.BindingCoreBinding h = fact(result.bindingFacts(), "h");
        if (x == null || y == null || h == null) {
            return;
        }

        // Exactly three closures: outer, h (and none other); h's CLOSURE_NEW
        // carries the ordered captures [y, x].
        List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 2, "one CLOSURE_NEW per function declaration/expression "
            + "(outer + h); got " + closureNews.size());
        if (closureNews.size() != 2) {
            return;
        }
        SemanticOp hClosure = null;
        for (SemanticOp op : closureNews) {
            if (!(op.payload() instanceof KindPayload.ClosureNewPayload payload)) {
                fail("CLOSURE_NEW payload shape (producer defect)");
                continue;
            }
            if (payload.captures().contains(y.binding())) {
                hClosure = op;
            }
        }
        check(hClosure != null, "h's CLOSURE_NEW found (its captures include y)");
        if (hClosure == null) {
            return;
        }
        KindPayload.ClosureNewPayload hPayload =
            (KindPayload.ClosureNewPayload) hClosure.payload();
        check(hPayload.captures().equals(List.of(y.binding(), x.binding())),
            "captures = [y, x] in first-reference order; got " + hPayload.captures());
        check(hClosure.result() != null
                && hClosure.resultType() instanceof RuntimeDescriptor.Func func
                && func.equals(new RuntimeDescriptor.Func(List.of(),
                    RuntimeDescriptor.Null.INSTANCE)),
            "h's CLOSURE_NEW result type is the exact declared signature () -> null");

        // The LoweredFunction record agrees with the payload.
        LoweredFunction hFunction = unit.functions().get(hPayload.function());
        check(hFunction != null, "the unit's functions map records h's LoweredFunction");
        if (hFunction != null) {
            check(hFunction.functionId().equals(hPayload.function())
                    && hFunction.descriptor().equals(hPayload.signature())
                    && hFunction.captures().equals(hPayload.captures())
                    && hFunction.body().equals(hPayload.binding().blockId()),
                "LoweredFunction {functionId, descriptor, captures, body} equals the "
                    + "CLOSURE_NEW payload fields");
        }

        // The closure facts: each capture resolved at the creation site.
        SemanticLowerer.ClosureFacts hFacts = closureOf(result.closures(), hClosure);
        if (hFacts != null) {
            check(hFacts.captures().size() == 2, "h resolves exactly two captures");
            if (hFacts.captures().size() == 2) {
                SemanticLowerer.ClosureCapture first = hFacts.captures().get(0);
                SemanticLowerer.ClosureCapture second = hFacts.captures().get(1);
                BlockId outerBody = x.incarnations().get(0).scope();
                check(first.binding().equals(y.binding()) && first.generation() == 0
                        && first.scope().equals(outerBody)
                        && first.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                    "the first capture resolves y to generation 0 in outer's body block "
                        + "via its producing ALLOC: " + first);
                check(second.binding().equals(x.binding()) && second.generation() == 0
                        && second.scope().equals(outerBody)
                        && second.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                    "the second capture resolves x to generation 0 in outer's body block "
                        + "via its producing ALLOC: " + second);
            }
        }

        // Registry one-to-one: exactly one LoweredBody per closure, keyed
        // by the allocation identity equal to the result value id.
        int hBindings = 0;
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.LoweredBody body
                    && body.functionId().equals(hPayload.function())) {
                hBindings++;
            }
        }
        check(hBindings == 1, "exactly one LoweredBody registration for h; got " + hBindings);
        check(unit.functionBindings().containsKey(
                new FunctionAllocationIdentity(((ValueId) hClosure.result()).id())),
            "h's binding is keyed by the allocation identity equal to the result value id");
        check(unit.functionBindings().size() == closureNews.size() + 2,
            "one functionBinding per closure (registry one-to-one) plus the two "
                + "producer-less intrinsic seed registrations (ISSUE-0632): "
                + unit.functionBindings().size() + " bindings for " + closureNews.size()
                + " closures");
        int intrinsicSeeds = 0;
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.IntrinsicFunction) {
                intrinsicSeeds++;
            }
        }
        check(intrinsicSeeds == 2, "the two intrinsic seeds are registered "
            + "(ISSUE-0632); got " + intrinsicSeeds);

        // Cell kinds: captured x/y SHARED_CELL; uncaptured a, b, h DIRECT.
        check(x.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "x is SHARED_CELL (closure-captured)");
        check(y.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "y is SHARED_CELL (closure-captured)");
        check(h.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "h is DIRECT (uncaptured)");
        SemanticLowerer.BindingCoreBinding a = fact(result.bindingFacts(), "a");
        SemanticLowerer.BindingCoreBinding b = fact(result.bindingFacts(), "b");
        if (a != null) {
            check(a.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
                "a is DIRECT (declared inside the closure body)");
        }
        if (b != null) {
            check(b.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
                "b is DIRECT (declared inside the closure body)");
        }
        // The rewritten ALLOC payloads carry the final derived kinds.
        List<SemanticOp> allocs = ofKind(ops, SemanticOpKind.BINDING_ALLOC);
        int xShared = 0;
        int yShared = 0;
        for (SemanticOp op : allocs) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc) {
                if (alloc.binding().equals(x.binding())) {
                    xShared += alloc.cellKind() == BindingCellKind.SHARED_CELL ? 1 : 0;
                } else if (alloc.binding().equals(y.binding())) {
                    yShared += alloc.cellKind() == BindingCellKind.SHARED_CELL ? 1 : 0;
                }
            }
        }
        check(xShared == 1 && yShared == 1,
            "x's and y's ALLOC payloads carry the re-derived SHARED_CELL kind "
                + "(x: " + xShared + ", y: " + yShared + ")");
    }

    /**
     * The doubly-nested capture chain of
     * {@code test/conformance/backend-runtime/closures/nested-closure-mutation.deal}
     * (runtime-ok across luajit/jvm/js) in its window-legal shape: the
     * fixture's {@code return}/{@code call} statements belong to the
     * control-flow and call epics' windows, so the equivalent window
     * shape — a nested function declaration {@code make} whose body
     * creates the inner closure — pins the same detaching chain. The
     * inner closure's capture of {@code x} resolves through make's body
     * (where {@code x} is itself no local) to {@code x}'s producing
     * ALLOC/INIT in {@code test_nested_closure_mutation}'s body, and
     * the same reference is a free binding of make's own body region —
     * the {@code CLOSURE_NEW} creation site of the inner closure sits
     * inside make's body — so make's capture set carries {@code x} too
     * (B9 R2(ii): the chain is inner-body capture → make's body capture
     * → the closing R1 step in test's body).
     */
    static void testDoublyNestedCaptureAlongDetachingChain() {
        System.out.println("-- doubly-nested capture: nested-closure-mutation.deal chain "
            + "(window shape) --");

        SemanticLowerer.ClosureCoreResult result = lowerSlice("""
            function test_nested_closure_mutation(): null {
              let x: int = 1;
              function make(): null {
                let inner: () => null = function(): null {
                  let y: int = x;
                };
              }
              x = 9;
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        List<SemanticOp> ops = result.lowering().unit().ops();
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        SemanticLowerer.BindingCoreBinding make = fact(result.bindingFacts(), "make");
        if (x == null || make == null) {
            return;
        }

        List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 3,
            "one CLOSURE_NEW per function (test_nested_closure_mutation, make, inner); got "
                + closureNews.size());
        if (closureNews.size() != 3) {
            return;
        }
        // Creation order is deterministic: test_nested_closure_mutation
        // (module-level declaration) first, make (declaration inside
        // test's body) second, inner (function expression inside make's
        // body) third — inner's CLOSURE_NEW is emitted into make's body
        // buffer, which flushes after make's declaration pair.
        SemanticOp testClosureNew = closureNews.get(0);
        SemanticOp makeClosureNew = closureNews.get(1);
        SemanticOp innerClosureNew = closureNews.get(2);
        KindPayload.ClosureNewPayload testPayload =
            (KindPayload.ClosureNewPayload) testClosureNew.payload();
        KindPayload.ClosureNewPayload makePayload =
            (KindPayload.ClosureNewPayload) makeClosureNew.payload();
        KindPayload.ClosureNewPayload innerPayload =
            (KindPayload.ClosureNewPayload) innerClosureNew.payload();
        check(testPayload.captures().isEmpty(),
            "test_nested_closure_mutation's CLOSURE_NEW payload carries no captures");
        check(makePayload.captures().equals(List.of(x.binding())),
            "make's CLOSURE_NEW payload carries captures = [x] (the inner closure's "
                + "creation site lies inside make's body, so x is a free binding of "
                + "make's body region too — B9 R2(ii)); got " + makePayload.captures());
        check(innerPayload.captures().equals(List.of(x.binding())),
            "inner's CLOSURE_NEW payload carries captures = [x]");

        // The closure facts records agree with the payloads: make records
        // captures = [x], inner records captures = [x].
        SemanticLowerer.ClosureFacts testFacts = closureOf(result.closures(), testClosureNew);
        SemanticLowerer.ClosureFacts makeFacts = closureOf(result.closures(), makeClosureNew);
        SemanticLowerer.ClosureFacts innerFacts = closureOf(result.closures(), innerClosureNew);
        if (testFacts == null || makeFacts == null || innerFacts == null) {
            return;
        }
        check(testFacts.captures().isEmpty(),
            "test_nested_closure_mutation's closure facts record no captures");
        check(makeFacts.captures().size() == 1
                && makeFacts.captures().get(0).binding().equals(x.binding()),
            "make's closure facts record captures = [x] (detaching-chain propagation)");
        check(innerFacts.captures().size() == 1
                && innerFacts.captures().get(0).binding().equals(x.binding()),
            "inner's closure facts record captures = [x]");

        BlockId enclosingBody = x.incarnations().get(0).scope();
        SemanticLowerer.ClosureCapture makeCapture = makeFacts.captures().get(0);
        SemanticLowerer.ClosureCapture innerCapture = innerFacts.captures().get(0);
        check(makeCapture.generation() == 0
                && makeCapture.scope().equals(enclosingBody)
                && makeCapture.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
            "make's capture of x resolves along the detaching chain to x's producing "
                + "ALLOC in test_nested_closure_mutation's body (generation 0, scope "
                + enclosingBody + "): " + makeCapture);
        check(makeCapture.binding().equals(x.binding()),
            "make's capture names x's BindingId (capture by binding, never a copied value)");
        check(innerCapture.generation() == 0
                && innerCapture.scope().equals(enclosingBody)
                && innerCapture.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
            "inner's capture of x resolves along the detaching chain to x's producing "
                + "ALLOC in test_nested_closure_mutation's body (generation 0, scope "
                + enclosingBody + "): " + innerCapture);
        check(innerCapture.binding().equals(x.binding()),
            "the capture names x's BindingId (capture by binding, never a copied value)");

        // The load inside inner's body names {x, 0} — the chain-closing
        // incarnation.
        List<SemanticOp> loads = ofKind(ops, SemanticOpKind.BINDING_LOAD);
        int xLoads = 0;
        for (SemanticOp op : loads) {
            if (op.payload() instanceof KindPayload.BindingLoadPayload load
                    && load.binding().equals(x.binding())
                    && load.generation() == 0) {
                xLoads++;
            }
        }
        check(xLoads == 1, "exactly one generation-0 load of x (inside inner's body); got "
            + xLoads);

        // Cell kinds: x SHARED_CELL; make DIRECT (its own name is never
        // captured — make's capture list names x, not make itself).
        check(x.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "x is SHARED_CELL (captured by the inner closure through the chain)");
        check(make.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "make is DIRECT (its own name is never captured — the chain terminates at x)");
    }

    /**
     * Transitive propagation across deeper detaching chains (B9 R2(ii)):
     * a closure created inside a nested detached body registers its
     * capture into every enclosing open body whose capture border the
     * resolution lies outside — triple nesting propagates {@code x}
     * (declared in {@code outer}) through {@code mid}'s and
     * {@code inner}'s capture lists, while a binding declared inside
     * {@code mid}'s own body ({@code z}) stays out of {@code mid}'s
     * captures (it is mid's own scope chain, so the chain closes there).
     */
    static void testTransitivelyNestedCapturePropagation() {
        System.out.println("-- transitive detaching-chain propagation: triple nesting --");

        SemanticLowerer.ClosureCoreResult result = lowerSlice("""
            function outer(): null {
              let x: int = 1;
              function mid(): null {
                let z: int = 2;
                function inner(): null {
                  let a: int = x;
                  let b: int = z;
                }
              }
              x = 9;
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        List<SemanticOp> ops = result.lowering().unit().ops();
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        SemanticLowerer.BindingCoreBinding z = fact(result.bindingFacts(), "z");
        if (x == null || z == null) {
            return;
        }
        List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 3,
            "one CLOSURE_NEW per function (outer, mid, inner); got " + closureNews.size());
        if (closureNews.size() != 3) {
            return;
        }
        // Creation order: outer (module-level) first, mid (inside outer's
        // body) second, inner (inside mid's body) third.
        SemanticOp outerClosureNew = closureNews.get(0);
        SemanticOp midClosureNew = closureNews.get(1);
        SemanticOp innerClosureNew = closureNews.get(2);
        KindPayload.ClosureNewPayload outerPayload =
            (KindPayload.ClosureNewPayload) outerClosureNew.payload();
        KindPayload.ClosureNewPayload midPayload =
            (KindPayload.ClosureNewPayload) midClosureNew.payload();
        KindPayload.ClosureNewPayload innerPayload =
            (KindPayload.ClosureNewPayload) innerClosureNew.payload();
        check(outerPayload.captures().isEmpty(),
            "outer's CLOSURE_NEW payload carries no captures (x is outer's own local)");
        check(midPayload.captures().equals(List.of(x.binding())),
            "mid's CLOSURE_NEW payload carries captures = [x] (transitive propagation; z "
                + "is mid's own local, so it never enters mid's captures)");
        check(innerPayload.captures().equals(List.of(x.binding(), z.binding())),
            "inner's CLOSURE_NEW payload carries captures = [x, z] in first-reference "
                + "order; got " + innerPayload.captures());

        SemanticLowerer.ClosureFacts outerFacts = closureOf(result.closures(), outerClosureNew);
        SemanticLowerer.ClosureFacts midFacts = closureOf(result.closures(), midClosureNew);
        SemanticLowerer.ClosureFacts innerFacts = closureOf(result.closures(), innerClosureNew);
        if (outerFacts == null || midFacts == null || innerFacts == null) {
            return;
        }
        check(outerFacts.captures().isEmpty(),
            "outer's closure facts record no captures");
        check(midFacts.captures().size() == 1
                && midFacts.captures().get(0).binding().equals(x.binding()),
            "mid's closure facts record captures = [x] (transitive propagation)");
        check(innerFacts.captures().size() == 2
                && innerFacts.captures().get(0).binding().equals(x.binding())
                && innerFacts.captures().get(1).binding().equals(z.binding()),
            "inner's closure facts record captures = [x, z] in first-reference order");
        if (midFacts.captures().size() == 1 && innerFacts.captures().size() == 2) {
            BlockId outerBody = x.incarnations().get(0).scope();
            BlockId midBody = z.incarnations().get(0).scope();
            SemanticLowerer.ClosureCapture midCapture = midFacts.captures().get(0);
            SemanticLowerer.ClosureCapture innerX = innerFacts.captures().get(0);
            SemanticLowerer.ClosureCapture innerZ = innerFacts.captures().get(1);
            check(midCapture.generation() == 0 && midCapture.scope().equals(outerBody)
                    && midCapture.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                "mid's capture of x resolves to x's producing ALLOC in outer's body: "
                    + midCapture);
            check(innerX.generation() == 0 && innerX.scope().equals(outerBody)
                    && innerX.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                "inner's capture of x resolves through the chain to x's producing ALLOC "
                    + "in outer's body: " + innerX);
            check(innerZ.generation() == 0 && innerZ.scope().equals(midBody)
                    && innerZ.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                "inner's capture of z resolves to z's producing ALLOC in mid's body "
                    + "(the chain closes in mid's own scope): " + innerZ);
        }

        // Cell kinds: x SHARED_CELL; z SHARED_CELL (captured by inner);
        // mid DIRECT (its own name is never captured).
        check(x.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "x is SHARED_CELL (captured through the chain)");
        check(z.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "z is SHARED_CELL (captured by inner)");
        SemanticLowerer.BindingCoreBinding mid = fact(result.bindingFacts(), "mid");
        if (mid != null) {
            check(mid.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
                "mid is DIRECT (its own name is never captured)");
        }
    }

    /**
     * A closure capturing a later-declared module function: the capture
     * resolves to the hoisted module-init ALLOC (B1; docs/spec-v1.2.md
     * :1217-1221), the hoisted ALLOC upgrades to {@code SHARED_CELL},
     * and the function-typed load inside the earlier closure body
     * publishes the pre-allocated hoist-time identity that the
     * declaration-position {@code CLOSURE_NEW} reuses (loads preserve
     * allocation identity — R-FUNCTION-BINDING holds by construction).
     */
    static void testCaptureOfLaterDeclaredModuleFunctionResolvesToHoistedAlloc() {
        System.out.println("-- later-declared module function: hoisted ALLOC resolution and "
            + "identity preservation --");

        SemanticLowerer.ClosureCoreResult result = lowerSlice("""
            function first(): null {
              let h: () => null = function(): null {
                let copy: () => null = laterFn;
              };
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
        SemanticLowerer.BindingCoreBinding laterFn = fact(result.bindingFacts(), "laterFn");
        SemanticLowerer.BindingCoreBinding first = fact(result.bindingFacts(), "first");
        if (laterFn == null || first == null) {
            return;
        }
        BlockId moduleInitBlock = first.incarnations().get(0).scope();

        // laterFn's incarnation sits in the module-init block (hoisted).
        check(laterFn.incarnations().size() == 1
                && laterFn.incarnations().get(0).generation() == 0
                && laterFn.incarnations().get(0).scope().equals(moduleInitBlock),
            "laterFn's ALLOC is hoisted to the module-init block at generation 0");
        check(laterFn.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "the hoisted ALLOC upgraded to SHARED_CELL (captured by h)");

        // The capture resolution: h captures laterFn at the hoisted
        // ALLOC, and — h's creation site lies inside first's body — the
        // detaching-chain propagation records laterFn in first's captures
        // too (B9 R2(ii): the chain closes h's body capture → first's
        // body capture → the R1 step at the hoisted module-init ALLOC).
        List<SemanticLowerer.ClosureFacts> laterFnCapturers = new ArrayList<>();
        for (SemanticLowerer.ClosureFacts facts : result.closures()) {
            if (facts.captures().size() == 1
                    && facts.captures().get(0).binding().equals(laterFn.binding())) {
                laterFnCapturers.add(facts);
            }
        }
        check(laterFnCapturers.size() == 2,
            "exactly two closure-facts records carry captures = [laterFn] (h and first, "
                + "the detaching-chain propagation); got " + laterFnCapturers.size());
        for (SemanticLowerer.ClosureFacts facts : laterFnCapturers) {
            SemanticLowerer.ClosureCapture capture = facts.captures().get(0);
            check(capture.generation() == 0
                    && capture.scope().equals(moduleInitBlock)
                    && capture.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                "each chain capture of laterFn resolves to the hoisted ALLOC (generation "
                    + "0, module-init block): " + capture);
        }
        int laterFnPayloadCaptures = 0;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.CLOSURE_NEW)) {
            if (op.payload() instanceof KindPayload.ClosureNewPayload payload
                    && payload.captures().equals(List.of(laterFn.binding()))) {
                laterFnPayloadCaptures++;
            }
        }
        check(laterFnPayloadCaptures == 2,
            "two CLOSURE_NEW payloads carry captures = [laterFn] (h's and first's); got "
                + laterFnPayloadCaptures);

        // Identity preservation: the load of laterFn inside h's body
        // publishes the same result identity as laterFn's own CLOSURE_NEW
        // (the hoist-time pre-allocated identity).
        List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        SemanticOp laterClosure = null;
        for (SemanticOp op : closureNews) {
            if (op.payload() instanceof KindPayload.ClosureNewPayload payload
                    && op.result() != null) {
                // laterFn's closure: its body block carries no statements
                // and its result identity equals the hoisted pre-allocation.
                for (SemanticOp load : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
                    if (load.payload() instanceof KindPayload.BindingLoadPayload loadPayload
                            && loadPayload.binding().equals(laterFn.binding())
                            && load.result() != null && load.result().equals(op.result())) {
                        laterClosure = op;
                    }
                }
            }
        }
        check(laterClosure != null,
            "laterFn's CLOSURE_NEW reuses the pre-allocated hoist-time result identity "
                + "(a load of laterFn publishes the same identity)");
        if (laterClosure != null) {
            check(unit.functionBindings().containsKey(
                    new FunctionAllocationIdentity(((ValueId) laterClosure.result()).id())),
                "laterFn's binding is keyed by the shared allocation identity");
            int matching = 0;
            for (FunctionAllocationIdentity identity : unit.functionBindings().keySet()) {
                if (identity.id() == ((ValueId) laterClosure.result()).id()) {
                    matching++;
                }
            }
            check(matching == 1, "exactly one binding per allocation identity");
            // The load of laterFn carries the declared function descriptor.
            for (SemanticOp load : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
                if (load.payload() instanceof KindPayload.BindingLoadPayload loadPayload
                        && loadPayload.binding().equals(laterFn.binding())) {
                    check(load.resultType() instanceof RuntimeDescriptor.Func func
                            && func.equals(new RuntimeDescriptor.Func(List.of(),
                                RuntimeDescriptor.Null.INSTANCE)),
                        "the load of laterFn carries the declared signature descriptor "
                            + "() -> null");
                }
            }
        }

        // Ordering: the hoisted ALLOC precedes first's CLOSURE_NEW (the
        // forward reference validates at module-init completion, B9).
        List<SemanticOp> allocs = ofKind(ops, SemanticOpKind.BINDING_ALLOC);
        OpId hoistedAlloc = null;
        for (SemanticOp op : allocs) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && alloc.binding().equals(laterFn.binding())) {
                hoistedAlloc = op.opId();
            }
        }
        check(hoistedAlloc != null, "laterFn's hoisted ALLOC op found");
        if (hoistedAlloc != null) {
            boolean allClosuresAfter = true;
            for (SemanticOp op : closureNews) {
                if (indexOf(ops, op.opId()) < indexOf(ops, hoistedAlloc)) {
                    allClosuresAfter = false;
                }
            }
            check(allClosuresAfter,
                "the hoisted ALLOC precedes every CLOSURE_NEW in the op list");
        }
    }

    /**
     * A closure created inside a for body captures the per-iteration
     * incarnation (generation 1, the body block's ALLOC) — combined with
     * the binding-core child's two-incarnation map: the counter
     * incarnation stays {@code DIRECT} and the per-iteration incarnation
     * is {@code SHARED_CELL} (pinned), body loads name generation 1.
     */
    static void testForBodyClosureCapturesPerIterationIncarnation() {
        System.out.println("-- for-body closure: per-iteration incarnation (generation 1) --");

        SemanticLowerer.ClosureCoreResult result = lowerSlice("""
            function outer(): null {
              for (let i = 0; i < 3; i = i + 1) {
                let f: () => null = function(): null {
                  let y: int = i;
                };
              }
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        List<SemanticOp> ops = result.lowering().unit().ops();
        SemanticLowerer.BindingCoreBinding i = fact(result.bindingFacts(), "i");
        if (i == null) {
            return;
        }
        check(i.incarnations().size() == 2,
            "the two-incarnation map holds (counter + per-iteration); got "
                + i.incarnations().size());
        if (i.incarnations().size() != 2) {
            return;
        }
        SemanticLowerer.BindingCoreIncarnation counter = i.incarnations().get(0);
        SemanticLowerer.BindingCoreIncarnation perIteration = i.incarnations().get(1);
        check(counter.generation() == 0 && counter.cellKind() == BindingCellKind.DIRECT,
            "the counter incarnation is generation 0, DIRECT (not captured)");
        check(perIteration.generation() == 1
                && perIteration.cellKind() == BindingCellKind.SHARED_CELL,
            "the per-iteration incarnation is generation 1, SHARED_CELL (pinned)");

        // The capture resolves to generation 1 in the body block.
        SemanticLowerer.ClosureFacts fFacts = null;
        for (SemanticLowerer.ClosureFacts facts : result.closures()) {
            if (facts.captures().size() == 1
                    && facts.captures().get(0).binding().equals(i.binding())) {
                fFacts = facts;
            }
        }
        check(fFacts != null, "f's closure facts found (captures = [i])");
        if (fFacts != null) {
            SemanticLowerer.ClosureCapture capture = fFacts.captures().get(0);
            check(capture.generation() == 1
                    && capture.scope().equals(perIteration.scope())
                    && capture.producer() == SemanticLowerer.BindingProducer.BINDING_ALLOC,
                "the capture resolves the per-iteration incarnation (generation 1, body "
                    + "block): " + capture);
        }
        // The load inside f's body names {i, 1}.
        int gen1Loads = 0;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
            if (op.payload() instanceof KindPayload.BindingLoadPayload load
                    && load.binding().equals(i.binding())
                    && load.generation() == 1) {
                gen1Loads++;
            }
        }
        check(gen1Loads == 1, "exactly one generation-1 load of i (inside f's body); got "
            + gen1Loads);
        // The counter's generation-0 loads (condition/update) stay
        // generation 0.
        int gen0Loads = 0;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
            if (op.payload() instanceof KindPayload.BindingLoadPayload load
                    && load.binding().equals(i.binding())
                    && load.generation() == 0) {
                gen0Loads++;
            }
        }
        check(gen0Loads >= 2,
            "the condition/update counter loads name generation 0; got " + gen0Loads);
    }

    /**
     * Narrowed flow types are never captured: the capture list carries
     * {@code BindingId}s only (no type payload exists per capture), the
     * {@code LoweredFunction}/{@code CLOSURE_NEW} carry the declared
     * signature descriptor only, and a load of a nullable binding inside
     * the body carries the declared nullable descriptor (never a
     * narrowed one — {@code NullNarrowing} state is checker-local,
     * docs/spec-v1.2.md:1137-1144).
     */
    static void testNarrowedFlowTypesNeverCaptured() {
        System.out.println("-- narrowed flow types: capture entries are BindingIds, declared "
            + "descriptors only --");

        SemanticLowerer.ClosureCoreResult result = lowerSlice("""
            function outer(): null {
              let x: int | null = 1;
              let h: () => null = function(): null {
                let y: int | null = x;
              };
            }
            """);
        if (result == null || result.lowering().hasErrors() || result.lowering().unit() == null) {
            if (result != null) {
                fail("the slice lowers to a validated unit: " + result.lowering().diagnostics());
            }
            return;
        }
        List<SemanticOp> ops = result.lowering().unit().ops();
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        if (x == null) {
            return;
        }
        List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        boolean sawCapture = false;
        for (SemanticOp op : closureNews) {
            if (!(op.payload() instanceof KindPayload.ClosureNewPayload payload)) {
                continue;
            }
            if (!payload.captures().contains(x.binding())) {
                continue;
            }
            sawCapture = true;
            // The captures slot is a List<BindingId>: exactly one entry
            // for x, carrying no type and no narrowed variant.
            check(payload.captures().stream()
                    .filter(x.binding()::equals).count() == 1,
                "exactly one capture entry for x (no narrowed-type duplicate)");
            LoweredFunction function =
                result.lowering().unit().functions().get(payload.function());
            check(function != null && function.captures().equals(payload.captures()),
                "the LoweredFunction repeats the BindingId capture list verbatim");
            check(function != null && function.descriptor()
                    .equals(new RuntimeDescriptor.Func(List.of(),
                        RuntimeDescriptor.Null.INSTANCE)),
                "the LoweredFunction carries the declared signature descriptor only");
        }
        check(sawCapture, "h captures x exactly once");
        // The load of x inside the body carries the declared nullable
        // descriptor (?int), never a narrowed type.
        int nullableLoads = 0;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_LOAD)) {
            if (op.payload() instanceof KindPayload.BindingLoadPayload load
                    && load.binding().equals(x.binding())
                    && op.resultType() instanceof RuntimeDescriptor.Nullable nullable
                    && nullable.inner().equals(RuntimeDescriptor.Int.INSTANCE)) {
                nullableLoads++;
            }
        }
        check(nullableLoads == 1,
            "the load of x carries the declared ?int descriptor; got " + nullableLoads);
    }

    /**
     * The closure-capture arm of the B2 cell-kind iff: captures upgrade
     * the incarnation they resolve to; uncaptured and reassignable-
     * uncaptured locals stay {@code DIRECT} with the {@code mutable}
     * flag recorded independently; a store inside the body captures the
     * cell (capture by binding — later assignments observed through the
     * cell); self-recursive own names capture the hoisted/nested ALLOC
     * and upgrade it; and an intrinsic reference captures the intrinsic
     * cell.
     */
    static void testCellKindClosureCaptureArm() {
        System.out.println("-- B2 closure-capture arm: SHARED_CELL iff captured --");

        // (a) Reassignable-uncaptured local stays DIRECT with mutable=true.
        SemanticLowerer.ClosureCoreResult uncaptured = lowerSlice("""
            function outer(): null {
              let x: int = 1;
              x = 2;
            }
            """);
        if (uncaptured != null && !uncaptured.lowering().hasErrors()) {
            SemanticLowerer.BindingCoreBinding x = fact(uncaptured.bindingFacts(), "x");
            if (x != null) {
                check(x.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                        && x.incarnations().get(0).mutable(),
                    "reassignable-uncaptured x is DIRECT with mutable=true");
            }
        } else if (uncaptured != null) {
            fail("(a) lowers: " + uncaptured.lowering().diagnostics());
        }

        // (b) A store inside the closure body captures the cell.
        SemanticLowerer.ClosureCoreResult storeCapture = lowerSlice("""
            function outer(): null {
              let x: int = 1;
              let h: () => null = function(): null {
                x = 2;
              };
              x = 9;
            }
            """);
        if (storeCapture != null && !storeCapture.lowering().hasErrors()) {
            SemanticLowerer.BindingCoreBinding x = fact(storeCapture.bindingFacts(), "x");
            if (x != null) {
                check(x.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
                    "a store-only reference upgrades x to SHARED_CELL (capture by binding)");
            }
            boolean hCapturesX = false;
            for (SemanticLowerer.ClosureFacts facts : storeCapture.closures()) {
                for (SemanticLowerer.ClosureCapture capture : facts.captures()) {
                    if (capture.binding().equals(x.binding())) {
                        hCapturesX = true;
                    }
                }
            }
            check(hCapturesX, "h's capture list names x's cell (the store reference)");
        } else if (storeCapture != null) {
            fail("(b) lowers: " + storeCapture.lowering().diagnostics());
        }

        // (c) Self-recursion: the own name is a capture resolving to the
        // hoisted ALLOC; the hoisted ALLOC upgrades; the CLOSURE_NEW is
        // the immediate commit before BINDING_INIT.
        SemanticLowerer.ClosureCoreResult selfRecursion = lowerSlice("""
            function f(): null {
              let g: () => null = f;
            }
            """);
        if (selfRecursion != null && !selfRecursion.lowering().hasErrors()) {
            List<SemanticOp> ops = selfRecursion.lowering().unit().ops();
            SemanticLowerer.BindingCoreBinding f = fact(selfRecursion.bindingFacts(), "f");
            if (f != null) {
                check(f.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
                    "f's hoisted ALLOC upgrades to SHARED_CELL (own-name capture)");
                List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
                check(closureNews.size() == 1, "exactly one CLOSURE_NEW (size-1 SCC)");
                if (closureNews.size() == 1) {
                    KindPayload.ClosureNewPayload payload =
                        (KindPayload.ClosureNewPayload) closureNews.get(0).payload();
                    check(payload.captures().equals(List.of(f.binding())),
                        "the own name is a capture entry (size-1 SCC own-name arm)");
                    int closureIndex = indexOf(ops, closureNews.get(0).opId());
                    boolean initImmediatelyAfter = closureIndex + 1 < ops.size()
                        && ops.get(closureIndex + 1).kind() == SemanticOpKind.BINDING_INIT
                        && ops.get(closureIndex + 1).payload()
                            instanceof KindPayload.BindingInitPayload init
                        && init.binding().equals(f.binding());
                    check(initImmediatelyAfter,
                        "BINDING_INIT is the immediate commit after the CLOSURE_NEW "
                            + "(B4: no call observes a half-published value)");
                }
            }
        } else if (selfRecursion != null) {
            fail("(c) lowers: " + selfRecursion.lowering().diagnostics());
        }

        // (d) Nested self-recursion: g's body load of g resolves g's
        // nested-scope ALLOC (at the declaration position in outer's
        // body) and upgrades it.
        SemanticLowerer.ClosureCoreResult nestedSelf = lowerSlice("""
            function outer(): null {
              function g(): null {
                let copy: () => null = g;
              }
            }
            """);
        if (nestedSelf != null && !nestedSelf.lowering().hasErrors()) {
            SemanticLowerer.BindingCoreBinding g = fact(nestedSelf.bindingFacts(), "g");
            if (g != null) {
                check(g.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
                    "g's nested-scope ALLOC upgrades to SHARED_CELL (own-name capture)");
            }
        } else if (nestedSelf != null) {
            fail("(d) lowers: " + nestedSelf.lowering().diagnostics());
        }
    }

    /**
     * Determinism: repeated lowering of the same checked module produces
     * identical capture lists, closure facts, binding facts, and
     * byte-identical unit dumps (ids and payload fields included).
     */
    static void testDeterminism() {
        System.out.println("-- determinism: identical captures, FunctionId/BlockId "
            + "allocation, byte-identical dumps --");

        String source = """
            function first(): null {
              let h: () => null = function(): null {
                let copy: () => null = laterFn;
              };
            }
            function laterFn(): null {}
            """;
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return;
        }
        SemanticLowerer.ClosureCoreResult firstRun = SemanticLowerer.lowerModuleClosureCore(
            moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
        SemanticLowerer.ClosureCoreResult secondRun = SemanticLowerer.lowerModuleClosureCore(
            moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
        check(firstRun != null && !firstRun.lowering().hasErrors()
                && secondRun != null && !secondRun.lowering().hasErrors(),
            "both runs lower to validated units");
        if (firstRun == null || firstRun.lowering().hasErrors()
                || secondRun == null || secondRun.lowering().hasErrors()) {
            return;
        }
        check(firstRun.closures().equals(secondRun.closures()),
            "two runs produce identical closure facts (capture lists, FunctionIds, "
                + "BlockIds, resolved generations)");
        check(firstRun.bindingFacts().equals(secondRun.bindingFacts()),
            "two runs produce identical binding facts (cell kinds included)");
        byte[] firstDump = SemanticIrDumper.dumpModule(firstRun.lowering().unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(secondRun.lowering().unit());
        check(Arrays.equals(firstDump, secondDump),
            "two runs produce byte-identical unit dumps");
    }

    /**
     * Fail-closed negatives: a function expression stays foreign in the
     * binding-core child's window; a function-typed load of a dynamic
     * value (a parameter) fails closed as the registry child's
     * resolution (B5); foreign body statements and the legacy profile
     * guard convert to the pinned E6005.
     */
    static void testFailClosedNegatives() {
        System.out.println("-- fail-closed negatives --");

        // (a) The binding-core entry (ISSUE-0444) still rejects function
        // expressions: closure production is the closure child's.
        CheckedSlice slice = checkSlice("let h: () => null = function(): null {};");
        if (slice != null) {
            SemanticLowerer.BindingCoreResult foreign = SemanticLowerer.lowerModuleBindingCore(
                moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH,
                REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
            check(foreign != null && foreign.lowering().hasErrors()
                    && foreign.lowering().unit() == null,
                "a function expression fails hard in the binding-core window with no unit");
            if (foreign != null && foreign.lowering().hasErrors()) {
                CompilerDiagnostic diagnostic = foreign.lowering().diagnostics().get(0);
                check("E6005".equals(diagnostic.code())
                        && diagnostic.diagnosticCode() == DiagnosticCode.E6005
                        && diagnostic.message().contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
                    "the foreign function expression converts to E6005 CONSTRUCT_UNLOWERED");
            }
        }

        // (b) A function-typed load of a parameter inside a closure body
        // fails closed: the parameter's cell value identity is dynamic
        // (the registry child's resolution, B5).
        SemanticLowerer.ClosureCoreResult parameterLoad = lowerSlice("""
            function outer(g: () => null): null {
              let h: () => null = function(): null {
                let copy: () => null = g;
              };
            }
            """);
        if (parameterLoad != null) {
            check(parameterLoad.lowering().hasErrors() && parameterLoad.lowering().unit() == null,
                "the dynamic function-value load fails hard with no unit");
            if (parameterLoad.lowering().hasErrors()) {
                check(parameterLoad.lowering().diagnostics().get(0).message()
                        .contains(SemanticLowerer.CONSTRUCT_UNLOWERED)
                        && parameterLoad.lowering().diagnostics().get(0).message()
                            .contains("registry child"),
                    "the parameter load names the registry child's resolution (B5): "
                        + parameterLoad.lowering().diagnostics().get(0).message());
            }
        }

        // (c) A foreign body statement (if) fails hard.
        SemanticLowerer.ClosureCoreResult ifStatement = lowerSlice("""
            function outer(): null {
              if (true) {}
            }
            """);
        if (ifStatement != null) {
            check(ifStatement.lowering().hasErrors() && ifStatement.lowering().unit() == null,
                "an if statement inside a body fails hard with no unit");
            if (ifStatement.lowering().hasErrors()) {
                check(ifStatement.lowering().diagnostics().get(0).message()
                        .contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
                    "the if statement names CONSTRUCT_UNLOWERED");
            }
        }

        // (d) The I3 profile guard applies to the closure entry point too.
        CheckedSlice simple = checkSlice("let a = 1;");
        if (simple != null) {
            SemanticLowerer.ClosureCoreResult legacy = SemanticLowerer.lowerModuleClosureCore(
                moduleOf(simple), SemanticProfile.LEGACY_SAFE_INT, Map.of(), INTERFACE_HASH,
                REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
            check(legacy != null && legacy.lowering().hasErrors()
                    && legacy.lowering().unit() == null
                    && legacy.bindingFacts().bindings().isEmpty()
                    && legacy.closures().isEmpty(),
                "a LEGACY_SAFE_INT closure request fails hard with no unit and no facts");
            if (legacy != null && legacy.lowering().hasErrors()) {
                check(legacy.lowering().diagnostics().get(0).message()
                        .contains(SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED),
                    "the legacy profile rejection names the pinned profile-guard rule");
            }
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Closure Lowering Test (ISSUE-0445 closure child) ===\n");

        testClosureCapturesEnclosingLocalsInFirstReferenceOrder();
        testDoublyNestedCaptureAlongDetachingChain();
        testTransitivelyNestedCapturePropagation();
        testCaptureOfLaterDeclaredModuleFunctionResolvesToHoistedAlloc();
        testForBodyClosureCapturesPerIterationIncarnation();
        testNarrowedFlowTypesNeverCaptured();
        testCellKindClosureCaptureArm();
        testDeterminism();
        testFailClosedNegatives();

        System.out.println("\nClosure lowering: " + passed + " passed, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
