package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.BindingImmutabilityAnalysis;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.ValueId;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * The immutability-proof child's tests (ISSUE-0448 sequencing item 5):
 * conservative {@code BindingImmutabilityProof} production from checker
 * facts (design B7) — a binding incarnation carries the closed proof iff
 * no assignment to that binding occurs anywhere in its enclosing scope
 * after its declaration; intrinsic {@code int}/{@code number} bindings
 * always carry the proof. Driven through the child's public lowering
 * entry point
 * ({@link SemanticLowerer#lowerModuleImmutabilityCore}) — the group-core
 * walk (the same walk the registry child's {@code functionBindings}
 * registrations populate, B5) with the assignment analysis active.
 *
 * <p><b>Coverage.</b></p>
 * <ul>
 *   <li>a local never assigned after its declaration → proof recorded at
 *       generation 0; a local assigned later in its scope → no proof
 *       (the resolved assignment fact names the defeated
 *       {@code {binding, generation}});</li>
 *   <li>an assignment anywhere in the enclosing scope after the
 *       declaration — a nested block included — defeats the proof
 *       (conservative: position relative to any adaptation site carries
 *       no weight);</li>
 *   <li>a parameter never assigned → proof; a parameter assigned in the
 *       function body → no proof;</li>
 *   <li>the for-let counter incarnation (the update assignment resolves
 *       to generation 0) → no proof, while the per-iteration incarnation
 *       (generation 1, no assignment resolves to it) → proof — combined
 *       with the binding-core child's two-incarnation map (fails if the
 *       incarnation map is broken);</li>
 *   <li>a module-level function name assigned anywhere in the module →
 *       no proof; an unassigned module-level function name → proof;</li>
 *   <li>intrinsic {@code int}/{@code number} bindings → proof always
 *       (builtin, unassignable);</li>
 *   <li>proof records name the dominant {@code {binding, generation}}:
 *       shadowed same-named bindings carry distinct per-binding records
 *       and the for-let's two generations carry distinct records;</li>
 *   <li>a closure-body assignment to a captured binding defeats the
 *       captured binding's proof (capture-by-binding reassignment, B3);</li>
 *   <li>repeated analysis of the same checked module yields identical
 *       proof and assignment records;</li>
 *   <li>registry combination: a module with closures, a recursive group,
 *       and an unassigned local produces the local's proof record while
 *       the unit's {@code functionBindings} map remains complete and
 *       key-unique per the registry child's obligations (fails if the
 *       registry module is broken).</li>
 * </ul>
 */
public class BindingImmutabilityProofTest {

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

    private static SemanticLowerer.ImmutabilityCoreResult lowerSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleImmutabilityCore(moduleOf(slice),
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

    /** The binding-core facts record of the declared name (exactly one). */
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

    /**
     * A lowered-and-validated result for the named test, or {@code null}
     * when the frontend or the lowering failed (already recorded).
     */
    private static SemanticLowerer.ImmutabilityCoreResult loweredResult(String source,
                                                                        String what) {
        SemanticLowerer.ImmutabilityCoreResult result = lowerSlice(source);
        if (result == null) {
            return null;
        }
        check(result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + " lowers to a validated unit: "
                + (result.lowering() == null ? "null" : result.lowering().diagnostics()));
        if (result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return null;
        }
        return result;
    }

    // =========================================================================
    // Tests
    // =========================================================================

    /**
     * A local never assigned after its declaration: the proof record
     * names exactly the dominant incarnation at generation 0.
     */
    static void testLocalUnassignedCarriesProof() {
        System.out.println("-- local never assigned: proof at generation 0 --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let x: int = 1;
              let y: int = x;
            }
            """, "the unassigned-local slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        if (x == null) {
            return;
        }
        check(x.incarnations().size() == 1
                && x.incarnations().get(0).generation() == 0,
            "x has exactly one incarnation at generation 0");
        check(result.proofFacts().proven(x.binding(), 0),
            "x carries a proof at generation 0");
        BindingImmutabilityProof proof = result.proofFacts().proofOf(x.binding(), 0)
            .orElse(null);
        if (proof != null) {
            check(proof.binding().equals(x.binding()) && proof.generation() == 0,
                "the proof record names the dominant {binding, generation} = {x, 0}");
        }
        check(result.proofFacts().assignments().isEmpty(),
            "no assignment fact was recorded for the slice (INIT is not an assignment)");
    }

    /**
     * A local assigned later in its scope: the assignment defeats the
     * proof and the resolved assignment fact names the defeated
     * {@code {binding, generation}}.
     */
    static void testLocalAssignedLaterCarriesNoProof() {
        System.out.println("-- local assigned later in the scope: no proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let x: int = 1;
              x = 2;
            }
            """, "the assigned-local slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        if (x == null) {
            return;
        }
        check(!result.proofFacts().proven(x.binding(), 0),
            "x carries no proof after the assignment");
        check(result.proofFacts().proofOf(x.binding(), 0).isEmpty(),
            "no proof record exists for {x, 0}");
        List<BindingImmutabilityAnalysis.BindingAssignment> assignments =
            result.proofFacts().assignments();
        check(assignments.size() == 1,
            "exactly one resolved assignment fact; got " + assignments.size());
        if (assignments.size() == 1) {
            BindingImmutabilityAnalysis.BindingAssignment assignment = assignments.get(0);
            check(assignment.name().equals("x")
                    && assignment.binding().equals(x.binding())
                    && assignment.generation() == 0,
                "the assignment fact names {x, x's binding, generation 0}");
        }
    }

    /**
     * An assignment anywhere in the enclosing scope after the
     * declaration — a nested block included — defeats the proof
     * (conservative: the assignment's position carries no weight).
     */
    static void testAssignmentInNestedBlockDefeatsProof() {
        System.out.println("-- assignment in a nested block of the scope: no proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let x: int = 1;
              {
                x = 2;
              }
            }
            """, "the nested-block-assignment slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        if (x == null) {
            return;
        }
        check(!result.proofFacts().proven(x.binding(), 0),
            "the nested-block assignment defeats x's proof (any assignment in the "
                + "enclosing scope after the declaration)");
    }

    /**
     * A parameter never assigned in its function body carries the proof.
     */
    static void testParameterUnassignedCarriesProof() {
        System.out.println("-- parameter never assigned: proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(a: int): null {
              let y: int = a;
            }
            """, "the unassigned-parameter slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding a = fact(result.bindingFacts(), "a");
        if (a == null) {
            return;
        }
        check(a.incarnations().size() == 1 && a.incarnations().get(0).generation() == 0,
            "the parameter a has exactly one incarnation at generation 0");
        check(result.proofFacts().proven(a.binding(), 0),
            "the unassigned parameter a carries a proof at generation 0");
    }

    /**
     * A parameter assigned in its function body: no proof.
     */
    static void testParameterAssignedCarriesNoProof() {
        System.out.println("-- parameter assigned in the body: no proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(a: int): null {
              a = 3;
            }
            """, "the assigned-parameter slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding a = fact(result.bindingFacts(), "a");
        if (a == null) {
            return;
        }
        check(!result.proofFacts().proven(a.binding(), 0),
            "the body assignment defeats the parameter a's proof");
        List<BindingImmutabilityAnalysis.BindingAssignment> assignments =
            result.proofFacts().assignments();
        check(assignments.size() == 1 && assignments.get(0).binding().equals(a.binding())
                && assignments.get(0).generation() == 0,
            "the resolved assignment fact names {a, a's binding, generation 0}");
    }

    /**
     * The for-let two-incarnation map (the binding-core child): the
     * update assignment resolves to the counter (generation 0) and
     * defeats its proof, while the per-iteration incarnation (generation
     * 1 — no assignment resolves to it) keeps its proof.
     */
    static void testForLetCounterNoProofPerIterationProof() {
        System.out.println("-- for-let: counter (generation 0) no proof, per-iteration "
            + "(generation 1) proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            for (let i = 0; i < 3; i = i + 1) {
              let z = i;
            }
            """, "the for-let slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding i = fact(result.bindingFacts(), "i");
        SemanticLowerer.BindingCoreBinding z = fact(result.bindingFacts(), "z");
        if (i == null || z == null) {
            return;
        }
        // The binding-core child's two-incarnation map (fails if broken).
        check(i.incarnations().size() == 2,
            "exactly two incarnations of one BindingId for the for-let counter; got "
                + i.incarnations().size());
        if (i.incarnations().size() != 2) {
            return;
        }
        SemanticLowerer.BindingCoreIncarnation counter = i.incarnations().get(0);
        SemanticLowerer.BindingCoreIncarnation perIteration = i.incarnations().get(1);
        check(counter.generation() == 0 && perIteration.generation() == 1,
            "counter generation 0, per-iteration generation 1");
        check(perIteration.cellKind() == BindingCellKind.SHARED_CELL,
            "the per-iteration incarnation is SHARED_CELL (the closed special case)");

        // The proof records: generation 0 defeated by the update
        // assignment, generation 1 proven.
        check(!result.proofFacts().proven(i.binding(), 0),
            "the counter incarnation (generation 0) carries no proof — the update "
                + "assignment defeats it");
        check(result.proofFacts().proven(i.binding(), 1),
            "the per-iteration incarnation (generation 1) carries the proof — no "
                + "assignment resolves to it");
        check(result.proofFacts().proven(z.binding(), 0),
            "the body local z carries a proof at generation 0");

        // The resolved assignment fact names the dominant incarnation at
        // the update site: {i, generation 0} — never generation 1.
        List<BindingImmutabilityAnalysis.BindingAssignment> assignments =
            result.proofFacts().assignments();
        check(assignments.size() == 1,
            "exactly one resolved assignment fact (the for-let update); got "
                + assignments.size());
        if (assignments.size() == 1) {
            BindingImmutabilityAnalysis.BindingAssignment assignment = assignments.get(0);
            check(assignment.name().equals("i")
                    && assignment.binding().equals(i.binding())
                    && assignment.generation() == 0,
                "the update assignment fact names {i, i's binding, generation 0} — the "
                    + "dominant incarnation at the update site");
        }
    }

    /**
     * A module-level function name never assigned anywhere in the
     * module carries the proof.
     */
    static void testModuleFunctionNameUnassignedCarriesProof() {
        System.out.println("-- module-level function name never assigned: proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function g(): null {}
            function h(): null {
              let x: int = 1;
            }
            """, "the unassigned-function-name slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        SemanticLowerer.BindingCoreBinding h = fact(result.bindingFacts(), "h");
        if (g == null || h == null) {
            return;
        }
        check(result.proofFacts().proven(g.binding(), 0),
            "the unassigned module-level function name g carries a proof at "
                + "generation 0");
        check(result.proofFacts().proven(h.binding(), 0),
            "the unassigned module-level function name h carries a proof at "
                + "generation 0");
        check(result.proofFacts().assignments().isEmpty(),
            "no assignment fact was recorded for the slice");
    }

    /**
     * A module-level function name assigned anywhere in the module (a
     * later function body) carries no proof.
     */
    static void testModuleFunctionNameAssignedCarriesNoProof() {
        System.out.println("-- module-level function name assigned in the module: no proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function g(): null {}
            function h(): null {
              g = function(): null {};
            }
            """, "the assigned-function-name slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        SemanticLowerer.BindingCoreBinding h = fact(result.bindingFacts(), "h");
        if (g == null || h == null) {
            return;
        }
        check(!result.proofFacts().proven(g.binding(), 0),
            "the assignment anywhere in the module defeats the function name g's proof");
        check(result.proofFacts().proven(h.binding(), 0),
            "the unassigned function name h keeps its proof");
        List<BindingImmutabilityAnalysis.BindingAssignment> assignments =
            result.proofFacts().assignments();
        check(assignments.size() == 1
                && assignments.get(0).name().equals("g")
                && assignments.get(0).binding().equals(g.binding())
                && assignments.get(0).generation() == 0,
            "the resolved assignment fact names {g, g's binding, generation 0} — the "
                + "dominant incarnation at the assignment site");
    }

    /**
     * Intrinsic {@code int}/{@code number} bindings always carry the
     * proof (builtin, unassignable).
     */
    static void testIntrinsicBindingsAlwaysProven() {
        System.out.println("-- intrinsic int/number bindings: proof always --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let x: int = 1;
            }
            """, "the intrinsic slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding intBinding = fact(result.bindingFacts(), "int");
        SemanticLowerer.BindingCoreBinding numberBinding = fact(result.bindingFacts(), "number");
        if (intBinding == null || numberBinding == null) {
            return;
        }
        check(result.proofFacts().proven(intBinding.binding(), 0),
            "the intrinsic int binding always carries the proof at generation 0");
        check(result.proofFacts().proven(numberBinding.binding(), 0),
            "the intrinsic number binding always carries the proof at generation 0");
    }

    /**
     * Proof records name the dominant {@code {binding, generation}} per
     * declared name: two shadowed same-named locals carry two distinct
     * per-binding proof records, both at their dominant generation 0.
     */
    static void testShadowedNamesCarryDistinctPerBindingProofs() {
        System.out.println("-- shadowed same-named locals: distinct per-binding proof records --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let x: int = 1;
              {
                let x: int = 2;
              }
            }
            """, "the shadowing slice");
        if (result == null) {
            return;
        }
        List<SemanticLowerer.BindingCoreBinding> xs = new ArrayList<>();
        for (SemanticLowerer.BindingCoreBinding binding : result.bindingFacts().bindings()) {
            if (binding.name().equals("x")) {
                xs.add(binding);
            }
        }
        check(xs.size() == 2, "exactly two x bindings (outer and shadowed inner); got "
            + xs.size());
        if (xs.size() != 2) {
            return;
        }
        BindingId outer = xs.get(0).binding();
        BindingId inner = xs.get(1).binding();
        check(!outer.equals(inner), "the two shadowed bindings carry distinct BindingIds");
        check(result.proofFacts().proven(outer, 0),
            "the outer x carries a proof at generation 0");
        check(result.proofFacts().proven(inner, 0),
            "the inner x carries a proof at generation 0");
        BindingImmutabilityProof outerProof = result.proofFacts().proofOf(outer, 0)
            .orElse(null);
        BindingImmutabilityProof innerProof = result.proofFacts().proofOf(inner, 0)
            .orElse(null);
        if (outerProof != null && innerProof != null) {
            check(outerProof.binding().equals(outer) && innerProof.binding().equals(inner),
                "each proof record names its own binding identity (per-binding records, "
                    + "never by name)");
            check(!outerProof.equals(innerProof),
                "the two shadowed bindings' proof records are distinct");
        }
    }

    /**
     * A closure-body assignment to a captured binding defeats the
     * captured binding's proof (the capture names the cell — later
     * assignments are observable, B3 — so the binding is reassigned
     * within its enclosing scope).
     */
    static void testClosureBodyAssignmentDefeatsCapturedBinding() {
        System.out.println("-- closure-body assignment to a captured binding: no proof --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let x: int = 1;
              let k = function(): null {
                x = 2;
              };
            }
            """, "the closure-assignment slice");
        if (result == null) {
            return;
        }
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        SemanticLowerer.BindingCoreBinding k = fact(result.bindingFacts(), "k");
        if (x == null || k == null) {
            return;
        }
        check(!result.proofFacts().proven(x.binding(), 0),
            "the closure-body assignment defeats the captured binding x's proof");
        check(result.proofFacts().proven(k.binding(), 0),
            "the unassigned closure binding k keeps its proof");
        List<BindingImmutabilityAnalysis.BindingAssignment> assignments =
            result.proofFacts().assignments();
        check(assignments.size() == 1
                && assignments.get(0).name().equals("x")
                && assignments.get(0).binding().equals(x.binding())
                && assignments.get(0).generation() == 0,
            "the resolved assignment fact names {x, x's binding, generation 0} — the "
                + "incarnation the capture resolves to");
    }

    /**
     * Repeated analysis of the same checked module yields identical
     * proof records and identical assignment facts (deterministic,
     * byte-identical lowering's proof half).
     */
    static void testRepeatedAnalysisYieldsIdenticalRecords() {
        System.out.println("-- repeated analysis: identical proof and assignment records --");

        String source = """
            function f(): null {
              let x: int = 1;
              let y: int = x;
              y = 4;
            }
            function g(): null {
              let fRef: () => null = f;
            }
            function h(): null {
              let gRef: () => null = g;
            }
            """;
        SemanticLowerer.ImmutabilityCoreResult first = loweredResult(source,
            "the determinism slice (first lowering)");
        SemanticLowerer.ImmutabilityCoreResult second = loweredResult(source,
            "the determinism slice (second lowering)");
        if (first == null || second == null) {
            return;
        }
        check(first.proofFacts().proofs().equals(second.proofFacts().proofs()),
            "the two analyses derive identical proof records");
        check(first.proofFacts().assignments().equals(second.proofFacts().assignments()),
            "the two analyses record identical assignment facts");
    }

    /**
     * The registry combination (B5): proof analysis runs over the same
     * lowered-unit walk the registry populates — a module with closures,
     * a recursive group, and an unassigned local produces the local's
     * proof record while the unit's {@code functionBindings} map remains
     * complete and key-unique (fails if the registry module is broken).
     */
    static void testRegistryCombinedWalkKeepsRegistryCompleteAndKeyUnique() {
        System.out.println("-- registry combination: proofs plus complete key-unique "
            + "functionBindings over the same walk --");

        SemanticLowerer.ImmutabilityCoreResult result = loweredResult("""
            function f(): null {
              let gRef: () => null = g;
            }
            function g(): null {
              let fRef: () => null = f;
            }
            function h(): null {
              let x: int = 1;
            }
            """, "the registry-combined slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();

        // The unassigned local's proof record (the proof-analysis half).
        SemanticLowerer.BindingCoreBinding x = fact(result.bindingFacts(), "x");
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        if (x == null || f == null || g == null) {
            return;
        }
        check(result.proofFacts().proven(x.binding(), 0),
            "the unassigned local x produces its proof record at generation 0");
        check(result.proofFacts().proven(f.binding(), 0)
                && result.proofFacts().proven(g.binding(), 0),
            "the unassigned group-member names f and g keep their proofs");

        // The recursive group exists (the group child's half).
        check(result.groups().size() == 1,
            "exactly one RECURSIVE_GROUP_INIT facts record (the f/g SCC); got "
                + result.groups().size());
        check(ofKind(unit.ops(), SemanticOpKind.RECURSIVE_GROUP_INIT).size() == 1,
            "exactly one RECURSIVE_GROUP_INIT op; got "
                + ofKind(unit.ops(), SemanticOpKind.RECURSIVE_GROUP_INIT).size());

        // The registry half: complete and key-unique functionBindings —
        // one registration per producing allocation (2 group members + 1
        // closure h = 3) plus the two producer-less intrinsic seed
        // registrations (ISSUE-0632).
        check(unit.functionBindings().size() == 5,
            "the functionBindings map is complete: 2 group members + h's closure = 3 "
                + "registrations plus the two intrinsic seeds; got "
                + unit.functionBindings().size());
        List<FunctionAllocationIdentity> keys =
            new ArrayList<>(unit.functionBindings().keySet());
        check(new LinkedHashSet<>(keys).size() == keys.size(),
            "the functionBindings keys are unique; got " + keys);
        int intrinsicSeeds = 0;
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction) {
                intrinsicSeeds++;
                continue;
            }
            check(entry.getValue() instanceof FunctionExecutionBinding.LoweredBody,
                "every non-seed registration is a LoweredBody binding (key "
                    + entry.getKey() + ")");
        }
        check(intrinsicSeeds == 2, "the two producer-less intrinsic seeds are the only "
            + "non-LoweredBody registrations (ISSUE-0632); got " + intrinsicSeeds);
        // Every group member's pre-assigned identity is a key (the
        // registry child's one LoweredBody per member).
        if (result.groups().size() == 1) {
            for (SemanticLowerer.GroupMemberFacts member : result.groups().get(0).members()) {
                check(unit.functionBindings().containsKey(
                        new FunctionAllocationIdentity(member.identity().id())),
                    "the group member '" + member.name() + "' identity is a registry key");
            }
        }
        // The closure h's CLOSURE_NEW result identity is a key.
        List<SemanticOp> closureNews = ofKind(unit.ops(), SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 1, "exactly one CLOSURE_NEW op (h); got "
            + closureNews.size());
        if (closureNews.size() == 1) {
            check(unit.functionBindings().containsKey(new FunctionAllocationIdentity(
                    ((ValueId) closureNews.get(0).result()).id())),
                "h's CLOSURE_NEW result identity is a registry key");
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Binding Immutability Proof Test (ISSUE-0448 proof child) ===\n");

        testLocalUnassignedCarriesProof();
        testLocalAssignedLaterCarriesNoProof();
        testAssignmentInNestedBlockDefeatsProof();
        testParameterUnassignedCarriesProof();
        testParameterAssignedCarriesNoProof();
        testForLetCounterNoProofPerIterationProof();
        testModuleFunctionNameUnassignedCarriesProof();
        testModuleFunctionNameAssignedCarriesNoProof();
        testIntrinsicBindingsAlwaysProven();
        testShadowedNamesCarryDistinctPerBindingProofs();
        testClosureBodyAssignmentDefeatsCapturedBinding();
        testRepeatedAnalysisYieldsIdenticalRecords();
        testRegistryCombinedWalkKeepsRegistryCompleteAndKeyUnique();

        System.out.println("\nBinding immutability proof: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
