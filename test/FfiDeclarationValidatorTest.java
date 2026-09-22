package deal.test;

import deal.ast.ProgramNode;
import deal.codegen.Backend;
import deal.descriptors.CanonicalRuntimeTypeDescriptor;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiBindingState;
import deal.ffi.FfiCdefBundle;
import deal.ffi.FfiCdefEntry;
import deal.ffi.FfiClassDescriptor;
import deal.ffi.FfiCompilerClassDefaultPlan;
import deal.ffi.FfiDeclarationValidator;
import deal.ffi.FfiFieldDescriptor;
import deal.ffi.FfiForwardBindings;
import deal.ffi.FfiFunctionDescriptor;
import deal.ffi.FfiGeneratedModule;
import deal.ffi.FfiImportedFunctionReference;
import deal.ffi.FfiModuleDescriptor;
import deal.ffi.FfiType;
import deal.ffi.ForwardFunctionCell;
import deal.ffi.LuaFfiBindingGenerator;
import deal.identity.CanonicalModuleIdentity;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.module.ModuleIdentityAssembly;
import deal.module.SemanticModuleIdentity;
import deal.module.SourceModuleLocation;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.project.OutputConfigResolver;
import deal.project.ProjectContext;
import deal.project.ProjectDeploymentIdentity;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.SemanticProfile;
import deal.types.Type;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The dedicated C FFI declaration-validation, metadata, and
 * forward-binding battery (ISSUE-0162): the validator's policy matrix
 * (sync/export/name/type/class/field/default/pointer E7002 cases with
 * exact ranges), immutable source-ordered descriptor publication with
 * canonical descriptors and behavior-bearing identity, private
 * C-safe name generation with {@code deal_fN} ordinal members and
 * retained cdef text/ownership metadata, the forward-binding state
 * machine and graph-ordered imported references, the
 * no-evaluator-execution discipline, and the orchestrator integration
 * (JVM E6006 FFI_UNSUPPORTED_BACKEND without artifacts; the Lua
 * descriptor accepted for later runtime loading).
 */
public class FfiDeclarationValidatorTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void checkEq(String expected, String actual, String message) {
        check(expected.equals(actual),
            message + " (expected '" + expected + "', got '" + actual + "')");
    }

    // =========================================================================
    // Validator harness
    // =========================================================================

    private static final ProjectDeploymentIdentity DEPLOYMENT =
        new ProjectDeploymentIdentity("file:/test/deal.json", "digest");

    private static ProjectContext contextOf(String backend) {
        return new ProjectContext(
            "/test/deal.json", "/test", "/test", "1.2",
            List.of(),
            new OutputConfigResolver.OutputRef(
                OutputConfigResolver.Source.MANIFEST,
                OutputConfigResolver.Kind.ABSOLUTE_PATH,
                "/test/build", "/test/build", null),
            backend,
            Map.of(), "1.2", null, List.of(), DEPLOYMENT);
    }

    private static final class ValidatorHarness {
        final List<CompilerDiagnostic> diagnostics;
        final FfiDeclarationValidator.Result result;
        final ModuleIdentityAssembly assembly;

        ValidatorHarness(String source, String rawKey, String nativeKind,
                         String nativeLoader,
                         List<String> dependencyOrder,
                         Map<String, FfiDeclarationValidator.ImportTarget> imports) {
            LexResult lex = new Lexer(source, "ffi.d.deal").tokenize();
            check(!lex.hasErrors(), "validator fixture lexes: "
                + lex.diagnostics());
            Parser parser = new Parser(lex.tokens(), "ffi.d.deal",
                lex.directiveEvents());
            ParseResult parseResult = parser.parse();
            check(!parseResult.hasErrors(), "validator fixture parses: "
                + parseResult.diagnostics());
            ProgramNode program = parseResult.program();
            SourceModuleLocation location = new SourceModuleLocation(
                "/test/ffi.d.deal",
                new SemanticModuleIdentity(DEPLOYMENT,
                    "file:/test/ffi.d.deal"),
                "mtest", null,
                new CanonicalModuleIdentity.ExternalModule(rawKey));
            ProjectContext context = contextOf("luajit");
            this.assembly = new ModuleIdentityAssembly(context);
            // Phase-1 parity: every class requires its public identity
            // before the FFI phase runs.
            for (deal.ast.StatementNode stmt : program.statements()) {
                deal.ast.ClassDeclaration cd = null;
                if (stmt instanceof deal.ast.ClassDeclaration c) {
                    cd = c;
                } else if (stmt instanceof deal.ast.ExportDeclaration ed
                        && ed.declaration()
                            instanceof deal.ast.ClassDeclaration c) {
                    cd = c;
                }
                if (cd != null) {
                    assembly.requireClassIdentity(location, cd.name(),
                        cd.span());
                }
            }
            CanonicalRuntimeTypeDescriptor encoder =
                new CanonicalRuntimeTypeDescriptor(assembly.index());
            this.result = FfiDeclarationValidator.validate(
                program, rawKey.replace('/', '.'), location,
                "@$external/" + rawKey, assembly, encoder,
                nativeKind, nativeLoader, dependencyOrder, imports);
            List<CompilerDiagnostic> all = new ArrayList<>(lex.diagnostics());
            all.addAll(parseResult.diagnostics());
            all.addAll(result.diagnostics());
            this.diagnostics = all;
        }
    }

    private static CompilerDiagnostic errorDiag(List<CompilerDiagnostic> diags,
                                                String code) {
        return diags.stream().filter(d -> "error".equals(d.severity())
                && code.equals(d.code())).findFirst().orElse(null);
    }

    private static ValidatorHarness validate(String source, String rawKey) {
        return new ValidatorHarness(source, rawKey, null, null,
            List.of(), Map.of());
    }

    // =========================================================================
    // Validation policy matrix
    // =========================================================================

    private static void testValidFullDeclaration() {
        System.out.println("-- Valid full declaration publishes the descriptor --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Vec2 {
              x: number = 0.0;
              y: number = 1.5;
            }

            export function init(): null;
            export function add(a: int, b: int): int;
            export function cos(x: number): number;
            export function invert(x: boolean): boolean;
            export function logLine(s: string): null;
            export function sum(buf: bytes): int;
            export function length(v: Vec2): number;
            export function midpoint(a: Vec2, b: Vec2): Vec2;
            export function hold(h: Handle): null;
            export function open(): Handle;
            """, "native/math");
        check(!h.result.hasErrors(), "no errors: " + h.diagnostics);
        FfiModuleDescriptor d = h.result.descriptor();
        check(d != null, "descriptor published");
        if (d == null) return;
        checkEq("ffi:@$external/native/math", d.moduleKey(), "module key");
        checkEq("@$external/native/math", d.canonicalExternalModuleIdentity(),
            "canonical external identity");
        check(d.classes().size() == 2
                && "Handle".equals(d.classes().get(0).name())
                && "Vec2".equals(d.classes().get(1).name()),
            "classes source-ordered");
        check(d.functions().size() == 10
                && "init".equals(d.functions().get(0).dealName())
                && "open".equals(d.functions().get(9).dealName()),
            "functions source-ordered");
        FfiFunctionDescriptor add = d.functions().get(1);
        checkEq("add", add.dealName(), "dealName");
        checkEq("add", add.cSymbol(), "cSymbol equals dealName");
        check(add.orderedParams().size() == 2
                && add.orderedParams().get(0).kind() == FfiType.Kind.INT
                && "int".equals(
                    add.orderedParams().get(0).canonicalDescriptor()),
            "int param canonical descriptor");
        check(add.returnType().kind() == FfiType.Kind.INT
                && "int".equals(add.returnType().canonicalDescriptor()),
            "int return canonical descriptor");
        check(add.privateFunctionPointerType().startsWith("deal_ffi_")
                && add.privateFunctionPointerType().endsWith("_fn_0002"),
            "private function pointer typedef name carries digest+ordinal: "
                + add.privateFunctionPointerType());
        FfiClassDescriptor vec2 = d.classes().get(1);
        checkEq("@$external/native/math/Vec2", vec2.canonicalClassIdentity(),
            "Vec2 canonical identity");
        checkEq(vec2.canonicalClassIdentity(), vec2.qualifiedDealDescriptor(),
            "qualified descriptor equals identity atom");
        check(vec2.orderedFields().size() == 2
                && vec2.orderedFields().get(0).fieldOrdinal() == 0
                && vec2.orderedFields().get(1).fieldOrdinal() == 1,
            "struct fields source-ordered ordinals");
        check("number".equals(
                vec2.orderedFields().get(0).type().canonicalDescriptor())
            && "number".equals(
                vec2.orderedFields().get(1).type().canonicalDescriptor()),
            "struct field canonical descriptors");
        check(vec2.compilerDefaultPlan() != null,
            "C_STRUCT carries a compiler default plan");
        FfiCompilerClassDefaultPlan plan = vec2.compilerDefaultPlan();
        check(plan.entries().size() == 2
                && "x".equals(plan.entries().get(0).name())
                && plan.entries().get(0).hasDefaultEvaluator()
                && plan.entries().get(1).hasDefaultEvaluator(),
            "plan entries carry deferred evaluators");
        check(plan.planDigest().matches("[0-9a-f]{64}"), "plan digest is 64 hex");
        check(d.planDigest().matches("[0-9a-f]{64}"), "module plan digest 64 hex");
        check(d.runtimeDefaultPlans().containsKey(
                "@$external/native/math/Vec2"),
            "runtime plans keyed by class identity");
        FfiClassDescriptor handle = d.classes().get(0);
        checkEq("C_POINTER", handle.kind().name(), "pointer kind");
        check(handle.orderedFields().isEmpty()
                && handle.compilerDefaultPlan() == null,
            "pointer carries no fields and no plan");
        // Identity reacts to behavior-bearing content changes.
        ValidatorHarness changed = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Vec2 {
              x: number = 0.0;
              y: number = 2.5;
            }

            export function init(): null;
            export function add(a: int, b: int): int;
            export function cos(x: number): number;
            export function invert(x: boolean): boolean;
            export function logLine(s: string): null;
            export function sum(buf: bytes): int;
            export function length(v: Vec2): number;
            export function midpoint(a: Vec2, b: Vec2): Vec2;
            export function hold(h: Handle): null;
            export function open(): Handle;
            """, "native/math");
        check(!d.planDigest().equals(changed.result.descriptor().planDigest()),
            "a changed default changes the module identity digest");
        check(!vec2.compilerDefaultPlan().planDigest().equals(
                changed.result.descriptor().classes().get(1)
                    .compilerDefaultPlan().planDigest()),
            "a changed default changes the class plan digest");
        check(!d.canonicalPlanContent().equals(
                changed.result.descriptor().canonicalPlanContent()),
            "a changed default changes the canonical content");
        // Immutability.
        try {
            d.classes().add(null);
            check(false, "classes list must be immutable");
        } catch (UnsupportedOperationException expected) {
            check(true, "classes list immutable");
        }
        try {
            d.runtimeDefaultPlans().put("x", null);
            check(false, "plans map must be immutable");
        } catch (UnsupportedOperationException expected) {
            check(true, "plans map immutable");
        }
    }

    private static void testAsyncRejected() {
        System.out.println("-- Async functions are compile-time errors --");
        ValidatorHarness h = validate("""
            // @extern-c

            export async function poll(): int;
            export function ok(): int;
            """, "native/math");
        CompilerDiagnostic d = errorDiag(h.diagnostics, "E7002");
        check(d != null, "E7002 for async function: " + h.diagnostics);
        if (d != null) {
            check(d.range().startLine() == 3, "E7002 at the async function"
                + " declaration line, got " + d.range().startLine());
            check(h.result.descriptor() == null,
                "no descriptor after async rejection");
        }
    }

    private static void testParameterAllowlist() {
        System.out.println("-- Parameter/return allowlist violations --");
        ValidatorHarness h = validate("""
            // @extern-c

            export function bad1(xs: int[]): int;
            export function bad2(x: null): int;
            export function bad3(x: table): int;
            export function bad4(f: (x: int) => int): int;
            """, "native/math");
        List<CompilerDiagnostic> errs = h.diagnostics.stream()
            .filter(d -> "error".equals(d.severity())
                && "E7002".equals(d.code())).toList();
        check(errs.size() == 4, "four E7002 for parameter violations: "
            + h.diagnostics);
        check(h.result.descriptor() == null, "no descriptor after violations");
    }

    private static void testReturnAllowlist() {
        System.out.println("-- Return allowlist violations --");
        ValidatorHarness h = validate("""
            // @extern-c

            export function bad1(): bytes;
            export function bad2(): int[];
            """, "native/math");
        List<CompilerDiagnostic> errs = h.diagnostics.stream()
            .filter(d -> "error".equals(d.severity())
                && "E7002".equals(d.code())).toList();
        check(errs.size() == 2, "two E7002 for return violations: "
            + h.diagnostics);
        CompilerDiagnostic bytes = errorDiag(h.diagnostics, "E7002");
        check(bytes != null && bytes.range().startLine() == 3,
            "bytes return E7002 at the return type line, got "
                + (bytes == null ? "none" : bytes.range().startLine()));
    }

    private static void testSameFileClassReferences() {
        System.out.println("-- Same-file class references --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class Vec2 {
              x: number = 0.0;
              y: number = 0.0;
            }

            class Unmarked {
              x: number = 0.0;
            }

            export function a(v: Vec2): int;
            export function b(v: Unmarked): int;
            export function c(v: Missing): int;
            """, "native/math");
        List<CompilerDiagnostic> errs = h.diagnostics.stream()
            .filter(d -> "error".equals(d.severity())
                && "E7002".equals(d.code())).toList();
        check(errs.size() == 2, "two E7002 (unmarked and missing classes): "
            + h.diagnostics);
    }

    private static void testStructFieldPolicy() {
        System.out.println("-- Struct field policy (required/defaulted/"
            + "allowlist/ordinals) --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class Broken {
              a: number = 0.0;
              b?: number = 0.0;
              c: number;
              s: string = "";
              d: number = 0.0;
              d: number = 1.0;
            }
            """, "native/math");
        List<CompilerDiagnostic> errs = h.diagnostics.stream()
            .filter(d -> "error".equals(d.severity())
                && "E7002".equals(d.code())).toList();
        check(errs.size() == 4,
            "four E7002 (optional, missing default, string field, duplicate): "
                + h.diagnostics);
        check(h.result.descriptor() == null, "no descriptor after violations");
    }

    private static void testStructNestingRejected() {
        System.out.println("-- Struct field nesting rejected --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class Inner {
              x: int = 0;
            }

            // @c-struct
            export class Outer {
              inner: Inner = { x: 0 };
            }
            """, "native/math");
        check(errorDiag(h.diagnostics, "E7002") != null,
            "E7002 for nested @c-struct field: " + h.diagnostics);
    }

    private static void testPointerPolicy() {
        System.out.println("-- Pointer emptiness and non-constructibility --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-pointer
            export class Bad {
              x: int = 0;
            }

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Box {
              ptr: Handle = {};
            }
            """, "native/math");
        List<CompilerDiagnostic> errs = h.diagnostics.stream()
            .filter(d -> "error".equals(d.severity())
                && "E7002".equals(d.code())).toList();
        check(errs.size() == 2, "two E7002 (non-empty pointer, construction): "
            + h.diagnostics);
        CompilerDiagnostic construct = h.diagnostics.stream()
            .filter(d -> "E7002".equals(d.code())
                && d.message().contains("object-literal"))
            .findFirst().orElse(null);
        check(construct != null && construct.range().startLine() == 13,
            "construction E7002 at the object literal, got "
                + (construct == null ? "none" : construct.range().startLine()));
    }

    private static void testPointerDefaultFromProviderIsValid() {
        System.out.println("-- Pointer default from a provider call is valid --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            export function open(): Handle;

            // @c-struct
            export class Box {
              ptr: Handle = open();
            }
            """, "native/math");
        check(!h.result.hasErrors(), "pointer default from provider call valid: "
            + h.diagnostics);
        check(h.result.descriptor() != null, "descriptor published");
    }

    private static void testPointerConstructionIsTypeDirected() {
        System.out.println("-- Pointer construction check is type-directed --");
        // Valid: a @c-struct literal passed as a call argument to a
        // same-file function constructs the struct class, not the
        // pointer class.
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Vec2 {
              x: int = 0;
            }

            export function wrap(v: Vec2): Handle;

            // @c-struct
            export class Box {
              ptr: Handle = wrap({ x: 0 });
            }
            """, "native/math");
        check(!h.result.hasErrors(), "struct literal call argument is valid: "
            + h.diagnostics);
        check(h.result.descriptor() != null, "descriptor published");

        // A struct literal with a pointer-typed property that itself
        // constructs the pointer is still diagnosed at the nested
        // literal (the walk follows the constructed class's field
        // types).
        ValidatorHarness nested = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Holder {
              h: Handle = {};
            }

            export function wrap(h: Holder): Handle;

            // @c-struct
            export class Box {
              ptr: Handle = wrap({ h: {} });
            }
            """, "native/math");
        CompilerDiagnostic nestedDiag = nested.diagnostics.stream()
            .filter(d -> "E7002".equals(d.code())
                && d.message().contains("object-literal")
                && d.range().startLine() == 15)
            .findFirst().orElse(null);
        check(nestedDiag != null, "nested pointer literal inside a struct"
            + " call argument diagnosed at the literal: "
            + nested.diagnostics);

        // A pointer literal passed to a same-file function whose
        // parameter is the pointer class is still diagnosed.
        ValidatorHarness callArg = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            export function wrap(h: Handle): Handle;

            // @c-struct
            export class Box {
              ptr: Handle = wrap({});
            }
            """, "native/math");
        CompilerDiagnostic callArgDiag = errorDiag(callArg.diagnostics,
            "E7002");
        check(callArgDiag != null
                && callArgDiag.message().contains("object-literal"),
            "pointer literal inside a resolved call argument diagnosed: "
                + callArg.diagnostics);
        check(callArgDiag != null && callArgDiag.range().startLine() == 10,
            "call-argument E7002 at the literal, got "
                + (callArgDiag == null ? "none"
                    : callArgDiag.range().startLine()));

        // A pointer literal inside a function-expression body is
        // diagnosed (the walk descends into closure bodies).
        ValidatorHarness closure = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Box {
              ptr: Handle = function(): Handle { return {}; };
            }
            """, "native/math");
        CompilerDiagnostic closureDiag = errorDiag(closure.diagnostics,
            "E7002");
        check(closureDiag != null
                && closureDiag.message().contains("object-literal"),
            "pointer literal inside a closure body diagnosed: "
                + closure.diagnostics);
        check(closureDiag != null
                && closureDiag.range().startLine() == 8,
            "closure E7002 at the literal, got "
                + (closureDiag == null ? "none"
                    : closureDiag.range().startLine()));

        // An imported provider call whose parameter is not the pointer
        // class is never flagged (provider signatures resolve through
        // the import surface).
        Map<String, FfiDeclarationValidator.ImportTarget> imports =
            new LinkedHashMap<>();
        imports.put("prov", new FfiDeclarationValidator.ImportTarget(
            "prov.tools", Map.of("make", new Type.Func(
                List.of(Type.Int.INSTANCE), Type.Int.INSTANCE, false))));
        ValidatorHarness providerCall = new ValidatorHarness("""
            import * as prov from "prov/tools"

            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Box {
              ptr: Handle = prov.make({});
            }
            """, "native/math", null, null, List.of(), imports);
        check(!providerCall.diagnostics.stream().anyMatch(d ->
                "E7002".equals(d.code())
                    && d.message().contains("object-literal")),
            "provider-call argument typed int is never a pointer"
                + " construction: " + providerCall.diagnostics);

        // An unresolvable callee yields no false positive: the
        // literal's constructed class cannot be established.
        ValidatorHarness unknown = validate("""
            // @extern-c

            // @c-pointer
            export class Handle {}

            // @c-struct
            export class Box {
              ptr: Handle = f({ x: 0 });
            }
            """, "native/math");
        check(!unknown.diagnostics.stream().anyMatch(d ->
                "E7002".equals(d.code())
                    && d.message().contains("object-literal")),
            "unresolvable callee argument is never flagged: "
                + unknown.diagnostics);
    }

    private static void testStructFailureSkipsFunctionRowsCleanly() {
        System.out.println("-- Failed struct validation never crashes"
            + " function rows --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class Vec2 {
              x: number;
            }

            export function length(v: Vec2): number;
            export function midpoint(): Vec2;
            """, "native/math");
        CompilerDiagnostic d = errorDiag(h.diagnostics, "E7002");
        check(d != null && d.message().contains("must carry a default"),
            "the class's own E7002 is reported: " + h.diagnostics);
        check(h.result.descriptor() == null,
            "no descriptor after failed struct validation");
        check(h.diagnostics.stream().filter(x ->
                "E7002".equals(x.code())
                    && "error".equals(x.severity())).count() == 1,
            "exactly the class's E7002 (no crash, no spurious function"
                + " errors): " + h.diagnostics);
    }

    private static void testDuplicateExportsAndPlanKeyCollision() {
        System.out.println("-- Duplicate exports and plan-key collisions --");
        ValidatorHarness dup = validate("""
            // @extern-c

            export function f(): int;
            export function f(): int;
            """, "native/math");
        check(errorDiag(dup.diagnostics, "E7002") != null,
            "E7002 for duplicate export: " + dup.diagnostics);

        ValidatorHarness coll = validate("""
            // @extern-c

            // @c-struct
            export class Vec2 {
              x: number = 0.0;
            }

            export function Vec2_plan(): int;
            """, "native/math");
        check(errorDiag(coll.diagnostics, "E7002") != null,
            "E7002 for plan-key collision: " + coll.diagnostics);
    }

    private static void testImportedReferencesFollowGraphOrder() {
        System.out.println("-- Imported references follow graph order --");
        Map<String, FfiDeclarationValidator.ImportTarget> imports =
            new LinkedHashMap<>();
        imports.put("late", new FfiDeclarationValidator.ImportTarget(
            "prov.late", Map.of("seed", new Type.Func(
                List.of(), Type.Int.INSTANCE, false))));
        imports.put("early", new FfiDeclarationValidator.ImportTarget(
            "prov.early", Map.of("seed", new Type.Func(
                List.of(), Type.Int.INSTANCE, false))));
        ValidatorHarness h = new ValidatorHarness("""
            import * as late from "prov/late"
            import * as early from "prov/early"

            // @extern-c

            // @c-struct
            export class Box {
              a: int = late.seed();
              b: int = early.seed();
            }
            """, "native/math", null, null,
            List.of("prov.early", "prov.late"), imports);
        check(!h.result.hasErrors(), "imports valid: " + h.diagnostics);
        List<FfiImportedFunctionReference> refs = h.result.importedFunctions();
        check(refs.size() == 2, "two imported function references");
        if (refs.size() == 2) {
            check("prov.early".equals(refs.get(0).importedModulePath())
                    && "prov.late".equals(refs.get(1).importedModulePath()),
                "references ordered by dependency order: " + refs);
            check(refs.get(0).graphOrder() < refs.get(1).graphOrder(),
                "graph orders ascending");
            check(refs.get(0).canonicalDescriptor().equals("()->int")
                    || refs.get(0).canonicalDescriptor().equals("() -> int"),
                "canonical provider descriptor present: "
                    + refs.get(0).canonicalDescriptor());
            check(refs.get(0).providerContractDigest().matches("[0-9a-f]{64}"),
                "provider contract digest 64 hex");
            check(refs.get(0).sourceRange().startLine() == 9,
                "reference range at the consuming call, got "
                    + refs.get(0).sourceRange().startLine());
            FfiCompilerClassDefaultPlan boxPlan = h.result.descriptor()
                .classes().get(0).compilerDefaultPlan();
            check(boxPlan.canonicalPlanContent().contains("providerDigests")
                    && boxPlan.canonicalPlanContent().contains(
                        refs.get(0).providerContractDigest())
                    && boxPlan.canonicalPlanContent().contains(
                        refs.get(1).providerContractDigest()),
                "plan content carries the provider digests");
            check(boxPlan.semanticDefaultContents().contains("providerDigests"),
                "semantic default content carries provider digests");
        }
        // A changed provider signature changes the digest.
        Map<String, FfiDeclarationValidator.ImportTarget> changed =
            new LinkedHashMap<>();
        changed.put("late", new FfiDeclarationValidator.ImportTarget(
            "prov.late", Map.of("seed", new Type.Func(
                List.of(Type.Int.INSTANCE), Type.Int.INSTANCE, false))));
        changed.put("early", new FfiDeclarationValidator.ImportTarget(
            "prov.early", Map.of("seed", new Type.Func(
                List.of(), Type.Int.INSTANCE, false))));
        ValidatorHarness h2 = new ValidatorHarness("""
            import * as late from "prov/late"
            import * as early from "prov/early"

            // @extern-c

            // @c-struct
            export class Box {
              a: int = late.seed();
              b: int = early.seed();
            }
            """, "native/math", null, null,
            List.of("prov.early", "prov.late"), changed);
        check(!refs.get(0).providerContractDigest().equals(
                h2.result.importedFunctions().get(0)
                    .providerContractDigest())
                || !refs.get(1).providerContractDigest().equals(
                    h2.result.importedFunctions().get(1)
                        .providerContractDigest()),
            "a changed provider signature changes the digest");
        check(!h.result.descriptor().canonicalPlanContent().equals(
                h2.result.descriptor().canonicalPlanContent()),
            "a changed provider changes the module plan identity");
    }

    // =========================================================================
    // Generator: names, cdefs, bindings
    // =========================================================================

    private static FfiModuleDescriptor fullDescriptor(String rawKey,
            String className) {
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class Vec2 {
              x: int = 0;
              y: number = 0.0;
              z: boolean = false;
            }

            export function init(): null;
            export function add(a: int, b: int): int;
            """, rawKey);
        check(!h.result.hasErrors(), "generator fixture valid: " + h.diagnostics);
        return h.result.descriptor();
    }

    private static void testGeneratorBundleAndNames() {
        System.out.println("-- Generator: private names, deal_fN, cdef text --");
        FfiModuleDescriptor d = fullDescriptor("native/math", "Vec2");
        LuaFfiBindingGenerator.GeneratedBindings gen =
            LuaFfiBindingGenerator.generate(d, List.of(), List.of());
        FfiCdefBundle bundle = gen.cdefBundle();
        check(bundle != null, "bundle generated");
        // Struct typedef first, then function typedefs in declaration order.
        check(bundle.entries().size() == 3, "three cdef entries");
        FfiCdefEntry structEntry = bundle.entries().get(0);
        check(structEntry.fullText().startsWith("typedef struct { ")
                && structEntry.fullText().contains("int32_t deal_f0;")
                && structEntry.fullText().contains("double deal_f1;")
                && structEntry.fullText().contains("_Bool deal_f2;"),
            "struct cdef carries source-order deal_fN members: "
                + structEntry.fullText());
        check(structEntry.fullText().contains("deal_ffi_")
                && structEntry.fullText().endsWith("_vec2_t;"),
            "struct typedef name carries digest and sanitized class name: "
                + structEntry.fullText());
        check(structEntry.ownedNames().size() == 1,
            "struct entry owns its typedef name");
        check(structEntry.entryDigest().equals(
                FfiContentDigestSha256(structEntry.fullText())),
            "entry digest is SHA-256 over the full text");
        FfiCdefEntry fnEntry = bundle.entries().get(1);
        check(fnEntry.fullText().equals("typedef void (*"
                + d.functions().get(0).privateFunctionPointerType()
                + ")(void);"),
            "null-return function cdef matches the descriptor fpt: "
                + fnEntry.fullText());
        check(d.functions().get(1).privateFunctionPointerType()
                .endsWith("_fn_0002"),
            "declaration ordinal in the function pointer name");
        check(bundle.fullContent().equals(
                bundle.entries().get(0).fullText() + "\n"
                    + bundle.entries().get(1).fullText() + "\n"
                    + bundle.entries().get(2).fullText() + "\n"),
            "fullContent is the complete canonical entry text");
        check(bundle.bundleDigest().equals(
                FfiContentDigestSha256(bundle.fullContent())),
            "bundle digest is SHA-256 over fullContent");
        check(bundle.bundleDigest().matches("[0-9a-f]{64}"),
            "bundle digest 64 hex");
        check(bundle.functions().size() == 2 && bundle.classes().size() == 1,
            "bundle carries the metadata rows");
        check(gen.plans().containsKey("@$external/native/math/Vec2"),
            "retained plans keyed by class identity");
        // Struct-involved functions carry the anonymous fpt spelling.
        ValidatorHarness structFn = validate("""
            // @extern-c

            // @c-struct
            export class Vec2 {
              x: int = 0;
            }

            export function make(x: int): Vec2;
            """, "native/math");
        FfiFunctionDescriptor make =
            structFn.result.descriptor().functions().get(0);
        check(make.privateFunctionPointerType().contains(" (*)(int32_t)"),
            "struct-return function carries the anonymous fpt spelling: "
                + make.privateFunctionPointerType());
    }

    private static String FfiContentDigestSha256(String text) {
        return CanonicalJson.sha256Hex(text.getBytes(
            java.nio.charset.StandardCharsets.UTF_8));
    }

    private static void testCKeywordSafeNames() {
        System.out.println("-- Generated names tolerate DEAL C keywords --");
        // 'union' and 'switch' are C keywords but not DEAL keywords.
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class union {
              x: int = 0;
            }

            export function switch(): int;
            """, "native/math");
        check(!h.result.hasErrors(), "C-keyword-named declarations valid: "
            + h.diagnostics);
        LuaFfiBindingGenerator.GeneratedBindings gen =
            LuaFfiBindingGenerator.generate(h.result.descriptor(),
                List.of(), List.of());
        String structText = gen.cdefBundle().entries().get(0).fullText();
        check(structText.contains("deal_ffi_")
                && structText.contains("_union_t"),
            "struct typedef prefixed with digest (C-safe): " + structText);
        check(!structText.matches("(?s).*\\bunion\\b.*"),
            "bare C keyword never appears in the cdef: " + structText);
        String fnText = gen.cdefBundle().entries().get(1).fullText();
        check(fnText.contains("deal_ffi_") && fnText.contains("_fn_0001"),
            "function typedef prefixed with digest (C-safe): " + fnText);
    }

    private static void testForwardBindingStateMachine() {
        System.out.println("-- Forward cells: state machine and guards --");
        FfiModuleDescriptor d = fullDescriptor("native/math", "Vec2");
        LuaFfiBindingGenerator.GeneratedBindings gen =
            LuaFfiBindingGenerator.generate(d, List.of(), List.of());
        FfiForwardBindings bindings = gen.bindings();
        checkEq(d.moduleKey(), bindings.moduleKey(), "bindings module key");
        check(bindings.state() == FfiBindingState.UNBOUND,
            "bindings start UNBOUND");
        check(bindings.cells().size() == 2
                && bindings.cells().keySet().contains("init")
                && bindings.cells().keySet().contains("add"),
            "one cell per exported function (cells precede lowering)");
        ForwardFunctionCell cell = bindings.cells().get("add");
        check(cell.state() == FfiBindingState.UNBOUND, "cell starts UNBOUND");
        boolean threw = false;
        try {
            cell.get();
        } catch (ForwardFunctionCell.FfiCellInitializationError expected) {
            threw = true;
        }
        check(threw, "UNBOUND get() raises the initialization signal");
        cell.markBinding();
        check(cell.state() == FfiBindingState.BINDING, "UNBOUND -> BINDING");
        threw = false;
        try {
            cell.markReady("wrapper-add");
        } catch (IllegalStateException expected) {
            threw = true;
        }
        check(!threw, "BINDING -> READY legal");
        check(cell.state() == FfiBindingState.READY, "cell READY");
        checkEq("wrapper-add", cell.get(), "READY get() returns the wrapper");
        threw = false;
        try {
            cell.markFailed("err");
        } catch (IllegalStateException expected) {
            threw = true;
        }
        check(threw, "READY -> FAILED illegal (terminal)");

        ForwardFunctionCell failedCell = new ForwardFunctionCell("fail");
        failedCell.markBinding();
        failedCell.markFailed("cached-error");
        check(failedCell.state() == FfiBindingState.FAILED, "cell FAILED");
        threw = false;
        try {
            failedCell.get();
        } catch (ForwardFunctionCell.FfiCellInitializationError expected) {
            threw = expected.getMessage().contains("cached-error");
        }
        check(threw, "FAILED get() carries the cached error key");

        // Immutability of the bindings surface.
        try {
            bindings.cells().put("x", null);
            check(false, "cells map must be immutable");
        } catch (UnsupportedOperationException expected) {
            check(true, "cells map immutable");
        }
        try {
            bindings.importedFunctions().add(null);
            check(false, "imported functions list must be immutable");
        } catch (UnsupportedOperationException expected) {
            check(true, "imported functions list immutable");
        }
    }

    private static void testNoEvaluatorRunsDuringGeneration() {
        System.out.println("-- No evaluator executes during generation/planning --");
        ValidatorHarness h = validate("""
            // @extern-c

            // @c-struct
            export class Box {
              x: int = ((1 + 2) * 3);
            }
            """, "native/math");
        check(!h.result.hasErrors(), "valid: " + h.diagnostics);
        FfiCompilerClassDefaultPlan plan =
            h.result.descriptor().classes().get(0).compilerDefaultPlan();
        check(plan.entries().get(0).hasDefaultEvaluator(),
            "deferred evaluator present");
        check(plan.entries().get(0).evaluatorContent().contains("binary")
                && plan.entries().get(0).evaluatorContent().contains("call")
                    == false,
            "evaluator content is the canonical structural serialization"
                + " (never executed): " + plan.entries().get(0)
                    .evaluatorContent());
        check(plan.evaluatorImplementationContents().contains("binary"),
            "evaluator implementation content carries the expression");
        check(plan.semanticDefaultContents().contains("semanticResourceIdentityDigest"),
            "semantic default content carries resource identity digests");
        check(!plan.semanticDefaultContents().contains("file:/test"),
            "private source URIs never appear in plan content");
        // The generation itself is pure: repeating yields byte-equal plans.
        LuaFfiBindingGenerator.GeneratedBindings g1 =
            LuaFfiBindingGenerator.generate(h.result.descriptor(),
                List.of(), List.of());
        LuaFfiBindingGenerator.GeneratedBindings g2 =
            LuaFfiBindingGenerator.generate(h.result.descriptor(),
                List.of(), List.of());
        checkEq(g1.cdefBundle().fullContent(), g2.cdefBundle().fullContent(),
            "generation is deterministic");
    }

    // =========================================================================
    // Orchestrator integration
    // =========================================================================

    private static void testOrchestratorJvmRejectsExternC() throws Exception {
        System.out.println("-- Orchestrator: JVM extern-C -> E6006/no artifacts --");
        Path proj = Files.createTempDirectory("ffi-jvm-proj");
        try {
            writeFileIn(proj, "deal.json",
                "{\"languageVersion\": \"1.2\", \"backend\": \"jvm\","
                    + " \"moduleRoots\": [\"src\"]}");
            writeFileIn(proj, "src/math.d.deal", """
                // @extern-c

                // @c-struct
                export class Vec2 {
                  x: number = 0.0;
                }

                export function add(a: int, b: int): int;
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as math from "native/math"
                export function main(): null { return null; }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("build/jvm").toAbsolutePath();
            // Isolated-phase JVM path with the externals declaration.
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, false, Backend.JVM,
                Map.of("native/math",
                    proj.resolve("src/math.d.deal").toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            boolean success = orchestrator.compile();
            check(!success, "JVM extern-C compile fails");
            check(orchestrator.diagnostics().stream().anyMatch(d ->
                    "E6006".equals(d.code()) && "error".equals(d.severity())
                        && d.message().contains("FFI_UNSUPPORTED_BACKEND")),
                "E6006 FFI_UNSUPPORTED_BACKEND: " + orchestrator.diagnostics());
            CompilerDiagnostic e6006 = orchestrator.diagnostics().stream()
                .filter(d -> "E6006".equals(d.code())).findFirst().orElse(null);
            check(e6006 != null && e6006.range().startLine() == 1,
                "E6006 at the @extern-c directive range, got "
                    + (e6006 == null ? "none" : e6006.range().startLine()));
            check(orchestrator.ffiGenerations().isEmpty(),
                "no FFI metadata published on an incapable backend");
            check(!Files.exists(output),
                "no artifact directory written (output stays absent)");
        } finally {
            deleteRecursively(proj);
        }
    }

    private static void testOrchestratorLuaAcceptsDescriptor() throws Exception {
        System.out.println("-- Orchestrator: Lua accepts the descriptor for"
            + " later runtime loading --");
        Path proj = Files.createTempDirectory("ffi-lua-proj");
        try {
            writeFileIn(proj, "deal.json",
                "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\","
                    + " \"moduleRoots\": [\"src\"]}");
            writeFileIn(proj, "src/math.d.deal", """
                // @extern-c

                // @c-pointer
                export class Handle {}

                // @c-struct
                export class Vec2 {
                  x: number = 0.0;
                  y: number = 0.0;
                }

                export function add(a: int, b: int): int;
                export function length(v: Vec2): number;
                export function open(): Handle;
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as math from "native/math"
                export function main(): null { return null; }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("build/lua").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, false, Backend.LUAJIT,
                Map.of("native/math",
                    proj.resolve("src/math.d.deal").toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            boolean success = orchestrator.compile();
            check(success, "Lua extern-C compile succeeds: "
                + orchestrator.diagnostics());
            check(orchestrator.ffiGenerations().size() == 1,
                "one validated FFI module retained");
            FfiGeneratedModule module =
                orchestrator.ffiGenerations().get("native.math");
            check(module != null, "FFI module keyed by dotted module path");
            if (module == null) return;
            checkEq("ffi:@$external/native/math",
                module.descriptor().moduleKey(), "descriptor module key");
            check(module.descriptor().functions().size() == 3,
                "three function rows");
            check(module.descriptor().classes().size() == 2,
                "two class rows");
            check(module.cdefBundle().entries().size() >= 3,
                "cdef bundle with struct + function entries");
            check(module.bindings().cells().size() == 3
                    && module.bindings().state() == FfiBindingState.UNBOUND,
                "forward cells UNBOUND before runtime loading");
            check(module.plans().containsKey(
                    "@$external/native/math/Vec2"),
                "retained struct plan");
            // The generated loader inputs are consistent (module keys
            // match across descriptor/bundle consumer surfaces).
            check(module.descriptor().moduleKey().equals(
                    module.bindings().moduleKey()),
                "descriptor and bindings keys consistent");
        } finally {
            deleteRecursively(proj);
        }
    }

    private static void testOrchestratorLuaFailedValidationPublishesNothing()
            throws Exception {
        System.out.println("-- Orchestrator: failed validation publishes no"
            + " metadata and no artifact --");
        Path proj = Files.createTempDirectory("ffi-bad-proj");
        try {
            writeFileIn(proj, "deal.json",
                "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\","
                    + " \"moduleRoots\": [\"src\"]}");
            writeFileIn(proj, "src/math.d.deal", """
                // @extern-c

                export async function bad(): int;
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as math from "native/math"
                export function main(): null { return null; }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("build/lua").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, false, Backend.LUAJIT,
                Map.of("native/math",
                    proj.resolve("src/math.d.deal").toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            boolean success = orchestrator.compile();
            check(!success, "invalid extern-C fails the compile");
            check(orchestrator.diagnostics().stream().anyMatch(d ->
                    "E7002".equals(d.code()) && "error".equals(d.severity())),
                "E7002 reported: " + orchestrator.diagnostics());
            check(orchestrator.ffiGenerations().isEmpty(),
                "no metadata published on validation failure");
            check(!Files.exists(output),
                "no artifact directory written on validation failure");
        } finally {
            deleteRecursively(proj);
        }
    }

    private static void testOrchestratorFailedStructValidationNoCrash()
            throws Exception {
        System.out.println("-- Orchestrator: failed struct validation yields"
            + " clean E7002 (no raw exception) --");
        Path proj = Files.createTempDirectory("ffi-structfail-proj");
        try {
            writeFileIn(proj, "deal.json",
                "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\","
                    + " \"moduleRoots\": [\"src\"]}");
            writeFileIn(proj, "src/math.d.deal", """
                // @extern-c

                // @c-struct
                export class Vec2 {
                  x: number;
                }

                export function length(v: Vec2): number;
                export function midpoint(): Vec2;
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as math from "native/math"
                export function main(): null { return null; }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("build/lua").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, false, Backend.LUAJIT,
                Map.of("native/math",
                    proj.resolve("src/math.d.deal").toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            boolean success = orchestrator.compile();
            check(!success, "failed struct validation fails the compile");
            check(orchestrator.diagnostics().stream().anyMatch(d ->
                    "E4001".equals(d.code()) && "error".equals(d.severity())
                        && d.message().contains(
                            "Class field without default is not valid")
                        && d.range().startLine() == 5
                        && d.range().startColumn() == 3),
                "E4001 at the field declaration range reported: "
                    + orchestrator.diagnostics());
            check(orchestrator.diagnostics().stream().noneMatch(d ->
                    "E7002".equals(d.code())),
                "the FFI missing-default E7002 never fires (the planner"
                    + " gate precedes the FFI phase): "
                    + orchestrator.diagnostics());
            check(orchestrator.ffiGenerations().isEmpty(),
                "no metadata published on failed struct validation");
            check(!Files.exists(output),
                "no artifact directory written on failed struct"
                    + " validation");
        } finally {
            deleteRecursively(proj);
        }
    }

    private static void testOrchestratorImportedReferencesFollowGraphOrder()
            throws Exception {
        System.out.println("-- Orchestrator: imported references follow graph"
            + " order in production wiring --");
        Path proj = Files.createTempDirectory("ffi-order-proj");
        try {
            writeFileIn(proj, "deal.json",
                "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\","
                    + " \"moduleRoots\": [\"src\"]}");
            // The extern-C module imports late first, but late imports
            // early: the dependency (check) order is early(0), late(1),
            // and the imported references must follow it.
            writeFileIn(proj, "src/math.d.deal", """
                import * as late from "./prov/late"
                import * as early from "./prov/early"

                // @extern-c

                // @c-struct
                export class Box {
                  a: int = late.seed();
                  b: int = early.seed();
                }
                """);
            writeFileIn(proj, "src/prov/early.deal", """
                export function seed(): int { return 1; }
                """);
            writeFileIn(proj, "src/prov/late.deal", """
                import * as early from "./early"
                export function seed(): int { return early.seed() + 1; }
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as math from "native/math"
                export function main(): null { return null; }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("build/lua").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, false, Backend.LUAJIT,
                Map.of("native/math",
                    proj.resolve("src/math.d.deal").toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            boolean success = orchestrator.compile();
            check(success, "Lua extern-C compile succeeds: "
                + orchestrator.diagnostics());
            FfiGeneratedModule module =
                orchestrator.ffiGenerations().get("native.math");
            check(module != null, "FFI module retained");
            if (module == null) return;
            List<FfiImportedFunctionReference> refs =
                module.bindings().importedFunctions();
            check(refs.size() == 2, "two imported function references: "
                + refs);
            if (refs.size() == 2) {
                check("prov.early".equals(refs.get(0).importedModulePath())
                        && "prov.late".equals(refs.get(1)
                            .importedModulePath()),
                    "references in dependency order (early before late): "
                        + refs);
                check(refs.get(0).graphOrder() == 0
                        && refs.get(1).graphOrder() == 1,
                    "non-degenerate graph orders (0, 1): " + refs);
            }
        } finally {
            deleteRecursively(proj);
        }
    }

    private static void writeFileIn(Path root, String rel, String content)
            throws IOException {
        Path path = root.resolve(rel);
        Files.createDirectories(path.getParent());
        Files.writeString(path, content);
    }

    private static void deleteRecursively(Path root) throws IOException {
        if (!Files.exists(root)) {
            return;
        }
        try (var stream = Files.walk(root)) {
            for (Path p : stream.sorted(java.util.Comparator.reverseOrder())
                    .toList()) {
                Files.deleteIfExists(p);
            }
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        testValidFullDeclaration();
        testAsyncRejected();
        testParameterAllowlist();
        testReturnAllowlist();
        testSameFileClassReferences();
        testStructFieldPolicy();
        testStructNestingRejected();
        testPointerPolicy();
        testPointerDefaultFromProviderIsValid();
        testPointerConstructionIsTypeDirected();
        testStructFailureSkipsFunctionRowsCleanly();
        testDuplicateExportsAndPlanKeyCollision();
        testImportedReferencesFollowGraphOrder();
        testGeneratorBundleAndNames();
        testCKeywordSafeNames();
        testForwardBindingStateMachine();
        testNoEvaluatorRunsDuringGeneration();
        testOrchestratorJvmRejectsExternC();
        testOrchestratorLuaAcceptsDescriptor();
        testOrchestratorLuaFailedValidationPublishesNothing();
        testOrchestratorFailedStructValidationNoCrash();
        testOrchestratorImportedReferencesFollowGraphOrder();

        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
