package deal.test;

import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ImportDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.BindingsProductionValidator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.NamespaceRegistration;
import deal.semantic.ir.NamespaceRegistrations;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0633: the import alias-cell list on {@code MODULE_IMPORT} and the
 * per-imported-module namespace registrations
 * ({@code project-lowering-entry-and-registration-seeds} D8, the
 * namespace registration contract, and the import alias-cell contract;
 * {@code semantic-ir-construct-coverage-cutover} K9 item 8/K15 items
 * 1-2 — the recording half).
 *
 * <ol>
 *   <li>the import arm emits, per resolved import declaration, one
 *       {@code MODULE_IMPORT} whose payload names the import's ordered
 *       alias cells, on the typed unit and in the canonical dump, and no
 *       alias cell carries a {@code BINDING_INIT};</li>
 *   <li>the bindings production validator resolves each alias's pinned
 *       initializing write through the payload's explicit cell list and
 *       admits the unit;</li>
 *   <li>{@link NamespaceRegistrations} carries exactly one entry per
 *       distinct resolved imported module of the closure with the ordered
 *       union of the cells its completions name (a unit with two imports
 *       of one module contributes two cells to one entry);</li>
 *   <li>the failure negatives (unresolved alias, double-named cell, a
 *       completion naming a non-alias allocation, an un-named alias cell,
 *       a cell under two modules, a kind disagreement) fail closed with
 *       the first E6005;</li>
 *   <li>the unchanged surfaces: the closed {@code SemanticOpKind} set,
 *       the {@code deal.semantic-ir/1} version text, and the
 *       {@code MODULE_IMPORT} payload key set.</li>
 * </ol>
 */
public class ModuleImportNamespaceRegistrationTest {

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

    private static final ModuleId MAIN = new ModuleId("main");
    private static final ModuleId OTHER = new ModuleId("other");
    private static final ModuleId MATH = new ModuleId("std.math");
    private static final ModuleId CONSOLE = new ModuleId("std.console");
    private static final String MAIN_SOURCE = "main.deal";
    private static final String OTHER_SOURCE = "other.deal";

    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = "a".repeat(64);
    private static final String LOWERING_CONTEXT_HASH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);

    /** Two imports of one module plus one of another: the ordered-cell list. */
    private static final String MAIN_IMPORT_SOURCE = """
        import * as m1 from "std/math"
        import * as m2 from "std/math"
        import * as c from "std/console"
        export function main(): null {}
        """;

    /** The second closure module: its cells append to the existing entries. */
    private static final String OTHER_IMPORT_SOURCE = """
        import * as o1 from "std/console"
        import * as o2 from "std/math"
        """;

    // =========================================================================
    // The checked-slice + full-program-E7 pipeline
    // =========================================================================

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    private static CheckedSlice checkSlice(String source, ModuleId module, String sourceId) {
        LexResult lex = new Lexer(source, sourceId).tokenize();
        ParseResult parse = new Parser(lex.tokens(), sourceId, lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(),
            "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver names = new NameResolver(module.path(), new StubModuleResolver());
        SymbolTable symbols = names.resolve(parse.program());
        check(names.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + names.diagnostics());
        if (!names.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(module.path(), symbols, names,
            parse.program());
        check(checks.diagnostics().isEmpty(),
            "the slice checks cleanly: " + checks.diagnostics());
        if (!checks.diagnostics().isEmpty()) {
            return null;
        }
        return new CheckedSlice(parse.program(), checks);
    }

    /** The resolved import facts of the slice (in declaration order). */
    private static List<ResolvedImport> importsOf(ProgramNode program) {
        List<ResolvedImport> imports = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ImportDeclaration imported) {
                ModuleId resolved = switch (imported.modulePath()) {
                    case "std/math" -> MATH;
                    case "std/console" -> CONSOLE;
                    default -> new ModuleId(imported.modulePath().replace('/', '.'));
                };
                imports.add(new ResolvedImport(imported.alias(), imported.modulePath(),
                    resolved, ExternalModuleKind.STDLIB));
            }
        }
        return imports;
    }

    /** The checked export facts of the slice. */
    private static List<ExportInterface> exportsOf(ProgramNode program) {
        List<ExportInterface> exports = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ExportDeclaration exported
                    && exported.declaration() instanceof FunctionDeclaration function) {
                exports.add(new ExportInterface(function.name(), "function"));
            }
        }
        return exports;
    }

    /** The recorded coverage rows the slice's produced ops satisfy. */
    private static Map<ConstructKind, List<SemanticOpKind>> coverage(ProgramNode program) {
        EnumMap<ConstructKind, List<SemanticOpKind>> coverage =
            new EnumMap<>(ConstructKind.class);
        boolean hasImports = false;
        boolean hasFunctions = false;
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ImportDeclaration) {
                hasImports = true;
            }
            if (statement instanceof FunctionDeclaration) {
                hasFunctions = true;
            }
            if (statement instanceof ExportDeclaration exported
                    && exported.declaration() instanceof FunctionDeclaration) {
                hasFunctions = true;
            }
        }
        if (hasImports) {
            coverage.put(ConstructKind.IMPORT_EXPORT_ENTRY,
                ConstructKind.IMPORT_EXPORT_ENTRY.mappedOpKinds());
        }
        if (hasFunctions) {
            coverage.put(ConstructKind.FUNCTION_DECLARATION_EXPRESSION,
                ConstructKind.FUNCTION_DECLARATION_EXPRESSION.mappedOpKinds());
        }
        return coverage;
    }

    private record Lowered(LoweredModuleUnit unit, StructuredBodyTable table) {
    }

    /**
     * Lowers one slice through the existing full-program E7 entry (the
     * production entry that emits the {@code MODULE_IMPORT} completion);
     * {@code withImports} decides whether the checked input carries the
     * resolved import facts (the unresolved-alias negative passes none).
     */
    private static Lowered lower(String source, ModuleId module, String sourceId,
                                 boolean withImports, SemanticIdAllocator allocator) {
        CheckedSlice slice = checkSlice(source, module, sourceId);
        if (slice == null) {
            return null;
        }
        List<ResolvedImport> imports = withImports ? importsOf(slice.program()) : List.of();
        CheckedModuleInput input = new CheckedModuleInput(module, sourceId, Path.of(sourceId),
            slice.program(), slice.checks(), imports, exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        SemanticLowerer.FullProgramE7Result result =
            SemanticLowerer.lowerModuleFullProgramE7(input, SemanticProfile.DEAL_V1_2_INT32,
                coverage(slice.program()), INTERFACE_HASH, REGISTRY_HASH, allocator, Map.of(),
                Map.of(), Set.of());
        check(result != null && result.lowering() != null,
            "the full-program E7 entry returns a result");
        if (result == null || result.lowering() == null) {
            return null;
        }
        if (result.lowering().hasErrors() || result.lowering().unit() == null) {
            return null;
        }
        return new Lowered(result.lowering().unit(), result.lowering().table());
    }

    private static Lowered lowerOrFail(String source, ModuleId module, String sourceId,
                                       boolean withImports, SemanticIdAllocator allocator,
                                       String what) {
        Lowered lowered = lower(source, module, sourceId, withImports, allocator);
        check(lowered != null, what + " lowers to a validated unit");
        return lowered;
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    /** The module-scope INIT-less {@code BINDING_ALLOC} cells (the import aliases). */
    private static List<BindingId> aliasCells(LoweredModuleUnit unit) {
        List<BindingId> cells = new ArrayList<>();
        Set<BindingId> initialized = new java.util.LinkedHashSet<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingInitPayload init) {
                initialized.add(init.binding());
            }
        }
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && alloc.scope().equals(unit.moduleInit().initBlock())
                    && !initialized.contains(alloc.binding())) {
                cells.add(alloc.binding());
            }
        }
        return cells;
    }

    private static KindPayload.ModuleImportPayload importPayload(SemanticOp op) {
        check(op.payload() instanceof KindPayload.ModuleImportPayload,
            "a MODULE_IMPORT op carries the ModuleImportPayload shape");
        return op.payload() instanceof KindPayload.ModuleImportPayload payload
            ? payload : null;
    }

    // =========================================================================
    // 1. The import arm's explicit alias cells (typed unit + dump)
    // =========================================================================

    private static void testImportArmAliasCells() {
        System.out.println("-- the import arm names the import's ordered alias cells --");

        Lowered lowered = lowerOrFail(MAIN_IMPORT_SOURCE, MAIN, MAIN_SOURCE, true,
            SemanticIdAllocator.over(List.of(MAIN)), "the two-import slice");
        if (lowered == null) {
            return;
        }
        LoweredModuleUnit unit = lowered.unit();
        List<BindingId> aliases = aliasCells(unit);
        check(aliases.size() == 3,
            "the unit carries three import-alias allocations (m1, m2, c) in declaration "
                + "order; got " + aliases);
        List<SemanticOp> imports = ofKind(unit, SemanticOpKind.MODULE_IMPORT);
        check(imports.size() == 3,
            "the import arm emits one MODULE_IMPORT per resolved import declaration; got "
                + imports.size());
        if (aliases.size() != 3 || imports.size() != 3) {
            return;
        }
        for (int i = 0; i < 3; i++) {
            KindPayload.ModuleImportPayload payload = importPayload(imports.get(i));
            if (payload == null) {
                return;
            }
            check(payload.aliasCells().equals(List.of(aliases.get(i))),
                "MODULE_IMPORT " + i + " names exactly its declaration's alias cell "
                    + aliases.get(i) + "; got " + payload.aliasCells());
            check(payload.kind() == ModuleImportKind.STDLIB,
                "MODULE_IMPORT " + i + " carries the resolved kind STDLIB; got "
                    + payload.kind());
        }
        KindPayload.ModuleImportPayload first = importPayload(imports.get(0));
        KindPayload.ModuleImportPayload second = importPayload(imports.get(1));
        KindPayload.ModuleImportPayload third = importPayload(imports.get(2));
        if (first == null || second == null || third == null) {
            return;
        }
        check(first.resolvedModule().equals(MATH) && second.resolvedModule().equals(MATH)
                && third.resolvedModule().equals(CONSOLE),
            "the two std/math imports resolve to one module identity and the console "
                + "import to the other; got " + first.resolvedModule() + ", "
                + second.resolvedModule() + ", " + third.resolvedModule());
        check("std/math".equals(first.rawSpecifier())
                && "std/console".equals(third.rawSpecifier()),
            "the raw specifier as written is carried unchanged");

        // No alias cell ever carries a BINDING_INIT.
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingInitPayload init) {
                check(!aliases.contains(init.binding()),
                    "the import-alias cell " + init.binding()
                        + " carries no BINDING_INIT (the MODULE_IMPORT completion is its "
                        + "pinned initializing write)");
            }
        }

        // The canonical dump carries the payload lists exactly.
        String dump = SemanticIrDumper.dumpModuleText(unit);
        CanonicalJson.Obj root = (CanonicalJson.Obj) CanonicalJson.parse(dump);
        CanonicalJson.Arr ops = (CanonicalJson.Arr) entry(root, "ops");
        int dumpedImports = 0;
        for (CanonicalJson.Value value : ops.items()) {
            CanonicalJson.Obj op = (CanonicalJson.Obj) value;
            if (!"MODULE_IMPORT".equals(((CanonicalJson.Str) entry(op, "kind")).value())) {
                continue;
            }
            CanonicalJson.Obj payload = (CanonicalJson.Obj) entry(op, "payload");
            List<String> keys = payload.entries().stream().map(CanonicalJson.Entry::key)
                .toList();
            check(keys.equals(List.of("aliasCells", "kind", "rawSpecifier", "resolvedModule")),
                "the dumped MODULE_IMPORT payload carries exactly the closed key set plus "
                    + "the one recorded alias-cell list; got " + keys);
            CanonicalJson.Arr cells = (CanonicalJson.Arr) entry(payload, "aliasCells");
            check(cells.items().size() == 1,
                "the dumped MODULE_IMPORT payload names its one cell; got " + cells.items());
            if (cells.items().size() == 1) {
                CanonicalJson.Obj cell = (CanonicalJson.Obj) cells.items().get(0);
                check(cell.entries().stream().map(CanonicalJson.Entry::key).toList()
                        .equals(List.of("id", "type")),
                    "a dumped alias cell is a semantic-id reference {id, type}; got "
                        + cell.entries());
            }
            dumpedImports++;
        }
        check(dumpedImports == 3,
            "the dump carries all three MODULE_IMPORT payloads with their cell lists; got "
                + dumpedImports);
    }

    private static CanonicalJson.Value entry(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        fail("the canonical object carries the key \"" + key + "\"; got "
            + obj.entries().stream().map(CanonicalJson.Entry::key).toList());
        return CanonicalJson.nullValue();
    }

    // =========================================================================
    // 2. The bindings validation resolves through the explicit cell list
    // =========================================================================

    private static void testBindingsValidationOverEmittedUnit() {
        System.out.println("-- the bindings validator resolves the payload cell lists --");

        Lowered lowered = lowerOrFail(MAIN_IMPORT_SOURCE, MAIN, MAIN_SOURCE, true,
            SemanticIdAllocator.over(List.of(MAIN)), "the two-import slice");
        if (lowered == null) {
            return;
        }
        Optional<CompilerDiagnostic> withoutFacts = BindingsProductionValidator.validate(
            lowered.unit(), lowered.table());
        check(withoutFacts.isEmpty(),
            "the emitted unit passes BINDING_INIT_ONCE without any walk facts (the "
                + "completion write resolves from the payload's cell list)"
                + (withoutFacts.isPresent() ? ": " + withoutFacts.get().message() : ""));
        Set<BindingId> cells = new java.util.LinkedHashSet<>(aliasCells(lowered.unit()));
        Optional<CompilerDiagnostic> withFacts = BindingsProductionValidator.validate(
            lowered.unit(), lowered.table(),
            new BindingsProductionValidator.PinnedWriteFacts(Set.of(), cells));
        check(withFacts.isEmpty(),
            "the emitted unit passes with the walk's alias facts supplied as well"
                + (withFacts.isPresent() ? ": " + withFacts.get().message() : ""));
    }

    // =========================================================================
    // 3. The per-imported-module namespace registrations
    // =========================================================================

    private static void testNamespaceRegistrationAssembly() {
        System.out.println("-- one namespace registration per distinct imported module --");

        Lowered main = lowerOrFail(MAIN_IMPORT_SOURCE, MAIN, MAIN_SOURCE, true,
            SemanticIdAllocator.over(List.of(MAIN)), "the two-import slice");
        if (main == null) {
            return;
        }
        List<BindingId> aliases = aliasCells(main.unit());
        if (aliases.size() != 3) {
            return;
        }
        NamespaceRegistrations.Assembly assembly =
            NamespaceRegistrations.assemble(List.of(main.unit()));
        check(!assembly.hasErrors() && assembly.registrations() != null,
            "the assembly over the lowered unit succeeds"
                + (assembly.hasErrors() ? ": " + assembly.diagnostics() : ""));
        if (assembly.hasErrors() || assembly.registrations() == null) {
            return;
        }
        NamespaceRegistrations registrations = assembly.registrations();
        check(registrations.registrations().size() == 2,
            "exactly one entry per distinct imported module (std.math, std.console); got "
                + registrations.registrations().keySet());
        NamespaceRegistration math = registrations.registrationFor(MATH);
        NamespaceRegistration console = registrations.registrationFor(CONSOLE);
        check(math != null && console != null,
            "both imported modules carry a registration");
        if (math == null || console == null) {
            return;
        }
        check(math.kind() == ModuleImportKind.STDLIB
                && console.kind() == ModuleImportKind.STDLIB,
            "each entry carries its completions' closed kind; got " + math.kind() + ", "
                + console.kind());
        check(math.aliasCells().equals(List.of(aliases.get(0), aliases.get(1))),
            "the two imports of one module contribute two cells to one entry in "
                + "declaration order; got " + math.aliasCells());
        check(console.aliasCells().equals(List.of(aliases.get(2))),
            "the console import contributes its one cell; got " + console.aliasCells());
        check(registrations.registrationFor(new ModuleId("std.string")) == null,
            "a module that is not imported carries no registration");
        check(registrations.registrations().keySet().toString()
                .equals("[std.math, std.console]"),
            "the entry order is the first-completion order (dependency order, then "
                + "declaration order); got " + registrations.registrations().keySet());

        // The registration equals the dumped payloads.
        List<BindingId> dumpedMath = new ArrayList<>();
        List<BindingId> dumpedConsole = new ArrayList<>();
        for (SemanticOp op : ofKind(main.unit(), SemanticOpKind.MODULE_IMPORT)) {
            KindPayload.ModuleImportPayload payload = importPayload(op);
            if (payload == null) {
                continue;
            }
            List<BindingId> target = payload.resolvedModule().equals(MATH)
                ? dumpedMath : dumpedConsole;
            target.addAll(payload.aliasCells());
        }
        check(math.aliasCells().equals(dumpedMath)
                && console.aliasCells().equals(dumpedConsole),
            "each entry's cells equal exactly the cells its completions name");

        // The typed registration is read-only.
        try {
            registrations.registrations().put(new ModuleId("x"), math);
            fail("the registration map is unmodifiable");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }
        try {
            math.aliasCells().add(new BindingId(9999));
            fail("a registration's cell list is unmodifiable");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }
    }

    private static void testTwoModuleClosureAssembly() {
        System.out.println("-- the closure-order union across the closure's units --");

        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MAIN, OTHER));
        Lowered main = lowerOrFail(MAIN_IMPORT_SOURCE, MAIN, MAIN_SOURCE, true, allocator,
            "the two-import slice");
        Lowered other = lowerOrFail(OTHER_IMPORT_SOURCE, OTHER, OTHER_SOURCE, true, allocator,
            "the second closure module");
        if (main == null || other == null) {
            return;
        }
        List<BindingId> mainAliases = aliasCells(main.unit());
        List<BindingId> otherAliases = aliasCells(other.unit());
        if (mainAliases.size() != 3 || otherAliases.size() != 2) {
            return;
        }
        NamespaceRegistrations.Assembly assembly =
            NamespaceRegistrations.assemble(List.of(main.unit(), other.unit()));
        check(!assembly.hasErrors() && assembly.registrations() != null,
            "the two-unit assembly succeeds"
                + (assembly.hasErrors() ? ": " + assembly.diagnostics() : ""));
        if (assembly.hasErrors() || assembly.registrations() == null) {
            return;
        }
        NamespaceRegistration math = assembly.registrations().registrationFor(MATH);
        NamespaceRegistration console = assembly.registrations().registrationFor(CONSOLE);
        if (math == null || console == null) {
            fail("both imported modules carry a registration");
            return;
        }
        check(assembly.registrations().registrations().size() == 2,
            "the second unit never creates a second entry for an already imported module; "
                + "got " + assembly.registrations().registrations().keySet());
        check(math.aliasCells().equals(List.of(mainAliases.get(0), mainAliases.get(1),
                otherAliases.get(1))),
            "the macro-ordered union is closure order, then declaration order; got "
                + math.aliasCells());
        check(console.aliasCells().equals(List.of(mainAliases.get(2), otherAliases.get(0))),
            "the console entry unions both units' cells; got " + console.aliasCells());
    }

    // =========================================================================
    // 4. The failure negatives
    // =========================================================================

    private static void testUnresolvedAliasNegative() {
        System.out.println("-- an alias without a resolved import fact --");

        SemanticLowerer.FullProgramE7Result result = lowerResult(MAIN_IMPORT_SOURCE, MAIN,
            MAIN_SOURCE, false, SemanticIdAllocator.over(List.of(MAIN)));
        check(result != null && result.lowering() != null && result.lowering().hasErrors(),
            "the unresolved-alias slice is rejected");
        if (result == null || result.lowering() == null
                || !result.lowering().hasErrors()) {
            return;
        }
        List<CompilerDiagnostic> diagnostics = result.lowering().diagnostics();
        check(diagnostics.size() == 1,
            "the unresolved alias produces exactly one diagnostic; got "
                + diagnostics.size());
        String message = diagnostics.get(0).message();
        check("E6005".equals(diagnostics.get(0).code())
                && message.contains("CONSTRUCT_UNLOWERED")
                && message.contains("without a resolved import fact"),
            "the unresolved alias returns the first E6005 CONSTRUCT_UNLOWERED; got "
                + message);
        check(result.lowering().unit() == null,
            "no unit is produced for the unresolved alias");
    }

    private static SemanticLowerer.FullProgramE7Result lowerResult(String source,
            ModuleId module, String sourceId, boolean withImports,
            SemanticIdAllocator allocator) {
        CheckedSlice slice = checkSlice(source, module, sourceId);
        if (slice == null) {
            return null;
        }
        List<ResolvedImport> imports = withImports ? importsOf(slice.program()) : List.of();
        CheckedModuleInput input = new CheckedModuleInput(module, sourceId, Path.of(sourceId),
            slice.program(), slice.checks(), imports, exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        return SemanticLowerer.lowerModuleFullProgramE7(input, SemanticProfile.DEAL_V1_2_INT32,
            coverage(slice.program()), INTERFACE_HASH, REGISTRY_HASH, allocator, Map.of(),
            Map.of(), Set.of());
    }

    /** One hand-built MODULE_IMPORT op with the given cells. */
    private static SemanticOp importOp(ModuleId module, ModuleImportKind kind,
                                       BindingId... cells) {
        return op(SemanticOpKind.MODULE_IMPORT,
            new KindPayload.ModuleImportPayload(module.path(), module, kind, List.of(cells)),
            null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    /** One hand-built module-scope import-alias ALLOC. */
    private static SemanticOp aliasAlloc(BindingId cell, BlockId moduleBlock) {
        return op(SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(cell, moduleBlock, false,
                BindingCellKind.DIRECT, 0),
            null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static LoweredModuleUnit unit(List<SemanticOp> ops) {
        BlockId moduleBlock = ops.isEmpty() ? new BlockId(0) : null;
        for (SemanticOp op : ops) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc) {
                moduleBlock = alloc.scope();
                break;
            }
        }
        if (moduleBlock == null) {
            moduleBlock = new BlockId(0);
        }
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MAIN, INTERFACE_HASH, LOWERING_CONTEXT_HASH,
            Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), moduleBlock), ExportPlan.empty(), Map.of(), ops);
    }

    private static StructuredBodyTable tableOf(LoweredModuleUnit unit, List<SemanticOp> ops) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        BlockId moduleBlock = unit.moduleInit().initBlock();
        List<OpId> ids = new ArrayList<>();
        for (SemanticOp op : ops) {
            ids.add(op.opId());
            opBlocks.put(op.opId(), moduleBlock);
        }
        blockOps.put(moduleBlock, ids);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    private static void assertValidatorRejects(List<SemanticOp> ops, String what,
                                               String contains) {
        LoweredModuleUnit unit = unit(ops);
        StructuredBodyTable table = tableOf(unit, ops);
        Optional<CompilerDiagnostic> failure =
            BindingsProductionValidator.validate(unit, table);
        check(failure.isPresent(), what + " is rejected by the bindings validator");
        if (failure.isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = failure.get();
        check("E6005".equals(diagnostic.code())
                && diagnostic.message().contains(
                    "validatorRule " + BindingsProductionValidator.BINDING_INIT_ONCE),
            what + " fails the pinned rule BINDING_INIT_ONCE; got " + diagnostic.message());
        check(diagnostic.message().contains(contains),
            what + " names its defect (\"" + contains + "\"); got " + diagnostic.message());

        // The registration assembly fails closed on the same fixture.
        NamespaceRegistrations.Assembly assembly =
            NamespaceRegistrations.assemble(List.of(unit));
        check(assembly.hasErrors() && assembly.registrations() == null,
            what + " also fails the registration assembly closed");
        if (assembly.hasErrors()) {
            check(assembly.diagnostics().size() == 1
                    && "E6005".equals(assembly.diagnostics().get(0).code())
                    && assembly.diagnostics().get(0).message()
                        .contains(NamespaceRegistrations.NAMESPACE_REGISTRATION),
                what + " returns the first E6005 NAMESPACE_REGISTRATION from the assembly; "
                    + "got " + assembly.diagnostics());
        }
    }

    private static void testFailureNegatives() {
        System.out.println("-- the failure negatives (first E6005, fail closed) --");

        // A cell named by two completions of one module.
        assertValidatorRejects(List.of(
                aliasAlloc(new BindingId(1), new BlockId(0)),
                importOp(MATH, ModuleImportKind.STDLIB, new BindingId(1), new BindingId(1))),
            "a cell named by two MODULE_IMPORT completions",
            "named by two MODULE_IMPORT completions");

        // A cell registered under two modules.
        BindingId shared = new BindingId(2);
        assertValidatorRejects(List.of(
                aliasAlloc(shared, new BlockId(0)),
                importOp(MATH, ModuleImportKind.STDLIB, shared),
                importOp(CONSOLE, ModuleImportKind.STDLIB, shared)),
            "a cell registered under two modules",
            "of two modules");

        // A completion naming a non-alias allocation.
        BindingId local = new BindingId(3);
        assertValidatorRejects(List.of(
                aliasAlloc(new BindingId(4), new BlockId(0)),
                op(SemanticOpKind.BINDING_ALLOC,
                    new KindPayload.BindingAllocPayload(local, new BlockId(0), true,
                        BindingCellKind.DIRECT, 0),
                    null, FailurePolicyId.NO_DEAL_FAILURE, null),
                op(SemanticOpKind.BINDING_INIT,
                    new KindPayload.BindingInitPayload(local, 0, new deal.semantic.ir.ValueId(1)),
                    null, FailurePolicyId.NO_DEAL_FAILURE, null),
                importOp(MATH, ModuleImportKind.STDLIB, local),
                importOp(MATH, ModuleImportKind.STDLIB, new BindingId(4))),
            "a completion naming a non-alias allocation",
            "not an import-alias allocation");

        // An alias allocation named by no completion (the unit carries the
        // modules arm through its other completion).
        assertValidatorRejects(List.of(
                aliasAlloc(new BindingId(5), new BlockId(0)),
                aliasAlloc(new BindingId(6), new BlockId(0)),
                importOp(MATH, ModuleImportKind.STDLIB, new BindingId(5))),
            "an import-alias allocation named by no completion",
            "named by no MODULE_IMPORT completion");

        // A completion/entry kind disagreement.
        assertValidatorRejects(List.of(
                aliasAlloc(new BindingId(7), new BlockId(0)),
                aliasAlloc(new BindingId(8), new BlockId(0)),
                importOp(MATH, ModuleImportKind.COMPILED, new BindingId(7)),
                importOp(MATH, ModuleImportKind.STDLIB, new BindingId(8))),
            "a completion/entry kind disagreement",
            "equals its entry's kind");
    }

    private static void testPositiveHandBuiltUnit() {
        System.out.println("-- the hand-built agreement positive --");

        BindingId a1 = new BindingId(11);
        BindingId a2 = new BindingId(12);
        List<SemanticOp> ops = List.of(
            aliasAlloc(a1, new BlockId(0)),
            aliasAlloc(a2, new BlockId(0)),
            importOp(MATH, ModuleImportKind.STDLIB, a1),
            importOp(MATH, ModuleImportKind.STDLIB, a2));
        LoweredModuleUnit unit = unit(ops);
        Optional<CompilerDiagnostic> failure = BindingsProductionValidator.validate(unit,
            tableOf(unit, ops));
        check(failure.isEmpty(), "a unit naming every alias exactly once passes"
            + (failure.isPresent() ? ": " + failure.get().message() : ""));
        NamespaceRegistrations.Assembly assembly =
            NamespaceRegistrations.assemble(List.of(unit));
        check(!assembly.hasErrors() && assembly.registrations() != null
                && assembly.registrations().registrations().size() == 1
                && assembly.registrations().registrationFor(MATH).aliasCells()
                    .equals(List.of(a1, a2)),
            "the assembly of that unit carries one entry with both cells");
    }

    // =========================================================================
    // 5. The unchanged surfaces
    // =========================================================================

    private static void testUnchangedSurfaces() {
        System.out.println("-- the unchanged surfaces --");

        check(SemanticOpKind.values().length == 55,
            "the closed SemanticOpKind set is unchanged (55 kinds); got "
                + SemanticOpKind.values().length);
        check("deal.semantic-ir/1".equals(LoweredModuleUnit.FORMAT_VERSION),
            "the deal.semantic-ir/1 version text is unchanged; got "
                + LoweredModuleUnit.FORMAT_VERSION);
        check(KindPayload.ModuleImportPayload.class.getRecordComponents().length == 4
                && KindPayload.ModuleImportPayload.class.getRecordComponents()[3].getType()
                    == List.class,
            "MODULE_IMPORT carries exactly one new component: the ordered alias-cell list");
        check(KindPayload.ModuleImportPayload.class.getRecordComponents()[0].getType()
                == String.class
                && KindPayload.ModuleImportPayload.class.getRecordComponents()[1].getType()
                    == ModuleId.class
                && KindPayload.ModuleImportPayload.class.getRecordComponents()[2].getType()
                    == ModuleImportKind.class,
            "the three pre-existing MODULE_IMPORT components keep their positions");
        check(KindPayload.ModuleImportPayload.class.getRecordComponents()[3].getName()
                .equals("aliasCells"),
            "the new component is named aliasCells");

        // The no-alias-cell convenience form and its defensive copy.
        KindPayload.ModuleImportPayload bare = new KindPayload.ModuleImportPayload("a",
            new ModuleId("a"), ModuleImportKind.COMPILED);
        check(bare.aliasCells().isEmpty(),
            "absence/empty is the no-alias-cell case");
        try {
            bare.aliasCells().add(new BindingId(0));
            fail("the alias-cell list is defensively copied");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }

        // The closed payload-record set: one record shape per kind.
        Set<Class<?>> shapes = new java.util.HashSet<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            check(kind.payloadClass().isRecord(),
                kind + " still maps to its payload record");
            check(shapes.add(kind.payloadClass()),
                kind + " keeps its distinct payload shape");
        }
        check(shapes.size() == 55,
            "55 distinct payload shapes for the 55 kinds; got " + shapes.size());

        // The canonical payload JSON key set (sorted) of MODULE_IMPORT.
        CanonicalJson.Obj payloadJson = (CanonicalJson.Obj)
            ContractSnapshotCanonicalizer.payloadJson(bare);
        check(payloadJson.entries().stream().map(CanonicalJson.Entry::key).toList()
                .equals(List.of("aliasCells", "kind", "rawSpecifier", "resolvedModule")),
            "the canonical MODULE_IMPORT payload carries exactly the four keys; got "
                + payloadJson.entries().stream().map(CanonicalJson.Entry::key).toList());

        // The registration records.
        NamespaceRegistration registration = new NamespaceRegistration(MATH,
            ModuleImportKind.STDLIB, List.of(new BindingId(1)));
        check(registration.module().equals(MATH) && registration.kind()
            == ModuleImportKind.STDLIB && registration.aliasCells()
                .equals(List.of(new BindingId(1))),
            "NamespaceRegistration carries {module, kind, aliasCells}");
        try {
            new NamespaceRegistrations(Collections.singletonMap(MATH,
                new NamespaceRegistration(CONSOLE, ModuleImportKind.STDLIB, List.of())));
            fail("the registration map key must equal the entry's module");
        } catch (IllegalArgumentException expected) {
            passed++;
        }
        NamespaceRegistrations.Assembly empty =
            NamespaceRegistrations.assemble(List.of());
        check(!empty.hasErrors() && empty.registrations() != null
                && empty.registrations().registrations().isEmpty(),
            "an import-free closure assembles to an empty registration set");
    }

    // =========================================================================
    // Hand-built operation fixtures (T2 payload shapes, T3 digests)
    // =========================================================================

    private static long nextOp = 1000;

    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType, FailurePolicyId policy,
            String digest) {
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, List.of(), null, payload, policy, List.of(), digest);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, FailurePolicyId policy) {
        return op(kind, payload, resultType, policy, null);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OpId opId = new OpId(MAIN, nextOp++);
        OperationContractSnapshot contract = contractFor(kind, payload, resultType, policy,
            "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, policy, digest);
        return new SemanticOp(opId, kind, origin(parent), null, resultType, List.of(),
            List.of(), payload, policy, contract);
    }

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin(MAIN_SOURCE, SourceSpan.synthetic(MAIN_SOURCE),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Running Import Alias Cells / Namespace Registrations Tests "
            + "(ISSUE-0633) ===");

        testUnchangedSurfaces();
        testImportArmAliasCells();
        testBindingsValidationOverEmittedUnit();
        testNamespaceRegistrationAssembly();
        testTwoModuleClosureAssembly();
        testUnresolvedAliasNegative();
        testFailureNegatives();
        testPositiveHandBuiltUnit();

        System.out.println("\nImport alias cells / namespace registrations: " + passed
            + " passed, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
