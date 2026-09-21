package deal.test;

import deal.ast.ClassField;
import deal.ast.LiteralExpr;
import deal.ast.LiteralValue;
import deal.ast.NamedType;
import deal.ast.ProgramNode;
import deal.ast.Span;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiCompilerClassDefaultPlan;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedModuleInput;
import deal.semantic.ClassConstructionValidator;
import deal.semantic.ClassRegistrationSeeds;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.LoweringSupport;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ModuleFact;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ClosedSelector;
import deal.types.Type;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The project-level class registration seeds tests (ISSUE-0631; design
 * sources {@code project-lowering-entry-and-registration-seeds} D4-D6 and
 * the registration-seed contract, {@code luajit-jvm-single-lowering-production-cutover}
 * C1's registration list, {@code semantic-ir-construct-coverage-cutover}
 * K9 items 3/6 and K13 item 1).
 *
 * <p>Covered:</p>
 * <ol>
 *   <li>The host declaration seeds derived from the real T1 declaration
 *       surface of a compiled project: per-class layouts with the field
 *       order, {@code DescriptorService.describe} descriptors,
 *       {@code required = !optional} flags, and the
 *       {@code HOST_DEFAULTS} owner member; the seed keys are the
 *       checker-resolved {@code ClassId}s; the seeds are immutable and
 *       deterministic.</li>
 *   <li>The extern-C declaration seeds derived from the real T1 surface
 *       and the real phase-3.9 generated metadata: the plan's ordered
 *       entries and canonical descriptors, {@code required = true}, the
 *       {@code FFI_PLAN} owner member, and the pointer class's empty
 *       layout without a plan entry.</li>
 *   <li>The builtin {@code Error} layout field-by-field, derived from the
 *       checker's synthesized builtin class declaration (the root
 *       {@code Error} binding of a resolved module) and present without
 *       any declaration module.</li>
 *   <li>The negative seeds: a declaration class without a resolvable
 *       {@code ClassId}, an extern-C plan/class mismatch (a declared class
 *       without a plan entry, a plan entry without a class, and a field
 *       name/order/descriptor/optional mismatch), an unrepresentable field
 *       type, and a duplicated {@code ClassId} — each returning the first
 *       E6005 with module, capability, rule, profile, version, and origin,
 *       and no seeds.</li>
 *   <li>The fail-closed consumer arms: a synthetic {@code CLASS_NEW}
 *       carrying each of the three registration owners (and RETAINED_ABI's
 *       never-produced rejection) is rejected by
 *       {@link ClassConstructionValidator} and by each emitter/oracle
 *       owner arm instead of being executed, emitted, or
 *       default-evaluated.</li>
 * </ol>
 */
public class ClassRegistrationSeedsTest {

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

    private static void checkEq(Object expected, Object actual, String message) {
        if (java.util.Objects.equals(expected, actual)) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message + " — expected <"
                + expected + ">, got <" + actual + ">");
        }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static void writeFileIn(Path dir, String rel, String content)
            throws IOException {
        Path file = dir.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
    }

    private static void deleteRecursively(Path dir) {
        if (dir == null || !Files.exists(dir)) return;
        try (var walk = Files.walk(dir)) {
            walk.sorted(Comparator.reverseOrder()).forEach(p -> {
                try {
                    Files.deleteIfExists(p);
                } catch (IOException ignored) {
                }
            });
        } catch (IOException ignored) {
        }
    }

    /** The error-severity diagnostics of one compile. */
    private static List<CompilerDiagnostic> errors(
            CompilationOrchestrator orchestrator) {
        List<CompilerDiagnostic> errors = new ArrayList<>();
        for (CompilerDiagnostic d : orchestrator.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        return errors;
    }

    /** The compiler-owned builtin `Error` declaration (compiler constant). */
    private static BuiltinErrorDeclaration builtinError() {
        return BuiltinErrorDeclaration.synthesized(Span.synthetic("seeds"));
    }

    /** The field names of one layout in declaration order. */
    private static List<String> fieldNames(ClassLayout layout) {
        List<String> names = new ArrayList<>();
        for (ClassLayout.FieldLayout field : layout.fields()) {
            names.add(field.name());
        }
        return names;
    }

    private static void checkField(ClassLayout.FieldLayout field, String name,
                                   RuntimeDescriptor descriptor, boolean required,
                                   DefaultOwner owner, String label) {
        checkEq(name, field.name(), label + ": field name");
        checkEq(descriptor, field.descriptor(),
            label + ": field '" + name + "' descriptor");
        checkEq(required, field.required(),
            label + ": field '" + name + "' required flag");
        checkEq(owner, field.defaultOwner(),
            label + ": field '" + name + "' default owner");
    }

    private static void checkRegistration(ClassRegistrationSeeds seeds,
                                          ClassId classId, DefaultOwner owner,
                                          List<String> fields, String label) {
        ClassRegistrationSeeds.ClassRegistration registration =
            seeds.registrationFor(classId);
        check(registration != null,
            label + ": the registration " + classId + " is present");
        if (registration == null) {
            return;
        }
        checkEq(classId, registration.layout().classId(),
            label + ": the layout carries the registration's class id");
        checkEq(owner, registration.owner(),
            label + ": the class-level owner member");
        checkEq(fields, fieldNames(registration.layout()),
            label + ": the fields in declaration order");
    }

    /** One worded E6005 assertion (code, capability, rule, module, origin). */
    private static void expectE6005(CompilerDiagnostic diagnostic,
                                    String rule, String capability,
                                    String module, String origin, String label) {
        checkEq("E6005", diagnostic.code(), label + ": the failure code");
        String message = diagnostic.message();
        check(message.contains("validatorRule " + rule),
            label + ": the failure names validatorRule " + rule + "; got " + message);
        check(message.contains("capability " + capability),
            label + ": the failure names capability " + capability + "; got " + message);
        check(message.contains("module '" + module + "'"),
            label + ": the failure names module '" + module + "'; got " + message);
        check(message.contains("semanticProfile DEAL_V1_2_INT32"),
            label + ": the failure carries the semantic profile; got " + message);
        check(message.contains("irVersion deal.semantic-ir/1"),
            label + ": the failure carries the IR version; got " + message);
        check(message.contains("origin " + origin),
            label + ": the failure carries the origin " + origin + "; got " + message);
    }

    /** Asserts one failed production: no seeds and exactly one diagnostic. */
    private static CompilerDiagnostic expectFailure(
            ClassRegistrationSeeds.Production production, String label) {
        check(production.hasErrors(), label + ": the production failed");
        check(production.seeds() == null, label + ": the failure yields no seeds");
        checkEq(1, production.diagnostics().size(),
            label + ": exactly the first E6005 is reported");
        if (production.diagnostics().size() != 1) {
            return null;
        }
        return production.diagnostics().get(0);
    }

    // =========================================================================
    // 1. Host declaration seeds from the real T1 declaration surface
    // =========================================================================

    private static final String HOST_DECLARATION = """
        export class Endpoint {
          path: string;
        }

        export class ServerConfig {
          port: int;
          endpoint: Endpoint;
          tags?: string[];
          note?: string | null;
        }

        export function describe(s: ServerConfig): string;

        export function version(): int;
        """;

    private static final ModuleId HOST_MODULE = new ModuleId("host.cfg");

    /** The canonical external identity of the externals specifier. */
    private static CanonicalModuleIdentity external(String specifier) {
        return new CanonicalModuleIdentity.ExternalModule(specifier);
    }

    private static CompilationOrchestrator compileProject(
            Path proj, String entryRelative, String moduleRelative,
            String specifier, Backend backend) throws Exception {
        writeFileIn(proj, "src/app.deal", """
            import * as cfg from "%s"

            export function main(): null {
              return null;
            }
            """.formatted(specifier));
        Path entry = proj.resolve(entryRelative).toAbsolutePath();
        Path output = proj.resolve("out").toAbsolutePath();
        return new CompilationOrchestrator(entry, output, false, false, false,
            backend, Map.of(specifier,
                proj.resolve(moduleRelative).toAbsolutePath().toString()),
            List.of(proj.resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize());
    }

    private static void testHostDeclarationSeeds() throws Exception {
        System.out.println("-- Host declaration class seeds (real T1 surface) --");
        Path proj = Files.createTempDirectory("seeds-host");
        try {
            writeFileIn(proj, "src/cfg.d.deal", HOST_DECLARATION);
            CompilationOrchestrator orchestrator = compileProject(proj,
                "src/app.deal", "src/cfg.d.deal", "host/cfg", Backend.LUAJIT);
            check(orchestrator.compile(),
                "the host-importing project compiles: "
                    + orchestrator.diagnostics());
            HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
            check(surface != null, "the compile produced a declaration surface");
            if (surface == null) {
                return;
            }

            ClassRegistrationSeeds.Production production =
                ClassRegistrationSeeds.produce(surface,
                    Map.of(HOST_MODULE, external("host/cfg")), Map.of(),
                    builtinError());
            check(!production.hasErrors() && production.seeds() != null,
                "the real host declaration surface produces the seeds: "
                    + production.diagnostics());
            if (production.hasErrors() || production.seeds() == null) {
                return;
            }
            ClassRegistrationSeeds seeds = production.seeds();

            ClassId endpointId = new ClassId("$external/host/cfg", "Endpoint");
            ClassId serverConfigId =
                new ClassId("$external/host/cfg", "ServerConfig");
            checkEq(List.of(ClassId.ERROR, endpointId, serverConfigId),
                seeds.classIds(),
                "the builtin Error entry, then one registration per declared"
                    + " class in declaration order");

            // The seed keys are the checker-resolved ClassIds: the
            // declared export types of the surface carry the declared
            // module's canonical class identity, and the seed key is its
            // projection.
            for (String name : List.of("Endpoint", "ServerConfig")) {
                Type exported = surface.require(HOST_MODULE).exports().get(name);
                check(exported instanceof Type.Class,
                    name + ": the declared export carries a class type");
                if (exported instanceof Type.Class classType) {
                    ClassId derived = new ClassId(
                        DescriptorService.semanticModulePath(classType.identity()),
                        classType.name());
                    check(seeds.registrationFor(derived) != null,
                        name + ": the seed key is the checker-resolved ClassId "
                            + derived);
                }
            }

            // Per-class layouts: field order, descriptors, required flags,
            // owner members.
            checkRegistration(seeds, endpointId, DefaultOwner.HOST_DEFAULTS,
                List.of("path"), "Endpoint");
            ClassRegistrationSeeds.ClassRegistration endpoint =
                seeds.registrationFor(endpointId);
            if (endpoint != null) {
                checkField(endpoint.layout().fields().get(0), "path",
                    RuntimeDescriptor.String.INSTANCE, true,
                    DefaultOwner.HOST_DEFAULTS, "Endpoint");
            }

            checkRegistration(seeds, serverConfigId,
                DefaultOwner.HOST_DEFAULTS,
                List.of("port", "endpoint", "tags", "note"), "ServerConfig");
            ClassRegistrationSeeds.ClassRegistration serverConfig =
                seeds.registrationFor(serverConfigId);
            if (serverConfig != null) {
                List<ClassLayout.FieldLayout> fields =
                    serverConfig.layout().fields();
                checkField(fields.get(0), "port", RuntimeDescriptor.Int.INSTANCE,
                    true, DefaultOwner.HOST_DEFAULTS, "ServerConfig");
                checkField(fields.get(1), "endpoint",
                    new RuntimeDescriptor.Class(endpointId), true,
                    DefaultOwner.HOST_DEFAULTS, "ServerConfig");
                checkField(fields.get(2), "tags",
                    new RuntimeDescriptor.Array(RuntimeDescriptor.String.INSTANCE),
                    false, DefaultOwner.HOST_DEFAULTS, "ServerConfig");
                checkField(fields.get(3), "note",
                    new RuntimeDescriptor.Nullable(RuntimeDescriptor.String.INSTANCE),
                    false, DefaultOwner.HOST_DEFAULTS, "ServerConfig");
            }

            // Immutability and determinism.
            boolean immutable = false;
            try {
                seeds.registrations().put(ClassId.ERROR, null);
            } catch (UnsupportedOperationException expected) {
                immutable = true;
            }
            check(immutable, "the registrations map is immutable");
            ClassRegistrationSeeds.Production repeat =
                ClassRegistrationSeeds.produce(surface,
                    Map.of(HOST_MODULE, external("host/cfg")), Map.of(),
                    builtinError());
            checkEq(seeds, repeat.seeds(),
                "the same inputs yield byte-identical seeds");
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 2. Extern-C declaration seeds from the real surface and real plan
    // =========================================================================

    private static final String EXTERN_C_DECLARATION = """
        // @extern-c

        // @c-pointer
        export class Handle {}

        // @c-struct
        export class Vec2 {
          x: number = 0.0;
          y: number = 0.0;
        }

        export function add(a: int, b: int): int;
        """;

    private static final ModuleId EXTERN_C_MODULE = new ModuleId("native.math");

    private static void testExternCDeclarationSeeds() throws Exception {
        System.out.println("-- Extern-C declaration class seeds (real T1"
            + " surface + real plan) --");
        Path proj = Files.createTempDirectory("seeds-extern-c");
        try {
            writeFileIn(proj, "src/math.d.deal", EXTERN_C_DECLARATION);
            CompilationOrchestrator orchestrator = compileProject(proj,
                "src/app.deal", "src/math.d.deal", "native/math",
                Backend.LUAJIT);
            check(orchestrator.compile(),
                "the extern-C-importing project compiles: "
                    + orchestrator.diagnostics());
            FfiGeneratedModule generated =
                orchestrator.ffiGenerations().get("native.math");
            check(generated != null,
                "the extern-C module carries its phase-3.9 generated metadata: "
                    + orchestrator.ffiGenerations().keySet());
            HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
            if (generated == null || surface == null) {
                return;
            }
            ClassId handleId = new ClassId("$external/native/math", "Handle");
            ClassId vec2Id = new ClassId("$external/native/math", "Vec2");
            // Anti-hollow: the real plan is keyed by the class identity the
            // seeds derive, and the pointer class carries no plan entry.
            checkEq("@" + vec2Id.modulePath() + "/Vec2", vec2Id.text(),
                "the derived class identity text");
            check(generated.plans().containsKey(vec2Id.text()),
                "the real generated metadata carries the Vec2 plan under "
                    + vec2Id.text() + ": " + generated.plans().keySet());
            check(!generated.plans().containsKey(handleId.text()),
                "the opaque pointer class carries no plan entry");
            check(generated.descriptor().classes().size() == 2,
                "the generated metadata carries both declared classes: "
                    + generated.descriptor().classes());

            ClassRegistrationSeeds.Production production =
                ClassRegistrationSeeds.produce(surface,
                    Map.of(EXTERN_C_MODULE, external("native/math")),
                    Map.of(EXTERN_C_MODULE, generated), builtinError());
            check(!production.hasErrors() && production.seeds() != null,
                "the real extern-C surface and plan produce the seeds: "
                    + production.diagnostics());
            if (production.hasErrors() || production.seeds() == null) {
                return;
            }
            ClassRegistrationSeeds seeds = production.seeds();
            checkEq(List.of(ClassId.ERROR, handleId, vec2Id), seeds.classIds(),
                "the builtin Error entry, then one registration per declared"
                    + " class in declaration order");

            checkRegistration(seeds, handleId, DefaultOwner.FFI_PLAN, List.of(),
                "Handle (opaque pointer)");
            checkRegistration(seeds, vec2Id, DefaultOwner.FFI_PLAN,
                List.of("x", "y"), "Vec2 (C struct)");
            ClassRegistrationSeeds.ClassRegistration vec2 =
                seeds.registrationFor(vec2Id);
            FfiCompilerClassDefaultPlan plan =
                generated.plans().get(vec2Id.text());
            if (vec2 != null && plan != null) {
                for (int i = 0; i < plan.entries().size(); i++) {
                    FfiCompilerClassDefaultPlan.Entry entry =
                        plan.entries().get(i);
                    checkField(vec2.layout().fields().get(i), entry.name(),
                        RuntimeDescriptor.parseCanonicalText(
                            entry.canonicalDescriptor()),
                        true, DefaultOwner.FFI_PLAN,
                        "Vec2 plan entry " + i);
                    check(!entry.optional(),
                        "the real plan entry is never optional (extern-C"
                            + " struct fields are never optional)");
                }
            }
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 3. The builtin Error layout, derived from the checker's synthesized
    //    declaration
    // =========================================================================

    private static final String SYNTH_SPAN_FILE = "main";

    private static void testBuiltinErrorLayout() {
        System.out.println("-- Builtin Error layout: compiler-owned, derived from"
            + " the checker's synthesized declaration --");

        // Present without any declaration module: never derived from source
        // text, a host declaration, or an interface-index entry.
        HostDeclarationSurface empty =
            HostDeclarationSurface.produce(List.of()).surface();
        ClassRegistrationSeeds.Production production =
            ClassRegistrationSeeds.produce(empty, Map.of(), Map.of(),
                builtinError());
        check(!production.hasErrors() && production.seeds() != null,
            "an empty declaration surface still yields the builtin entry: "
                + production.diagnostics());
        if (production.hasErrors() || production.seeds() == null) {
            return;
        }
        ClassRegistrationSeeds seeds = production.seeds();
        checkEq(List.of(ClassId.ERROR), seeds.classIds(),
            "exactly the builtin Error entry");
        checkEq("@/Error", ClassId.ERROR.text(),
            "the builtin Error class identity text is the schema-pinned @/Error");

        ClassRegistrationSeeds.ClassRegistration error =
            seeds.registrationFor(ClassId.ERROR);
        check(error != null, "the @/Error registration is present");
        if (error == null) {
            return;
        }
        checkEq(DefaultOwner.BUILTIN_DEFAULTS, error.owner(),
            "the builtin Error owner member");
        checkEq(ClassId.ERROR, error.layout().classId(),
            "the layout carries @/Error");
        checkEq(List.of("code", "message"), fieldNames(error.layout()),
            "exactly code and message in declaration order");
        checkEq(2, error.layout().fields().size(),
            "exactly two builtin Error fields");
        if (error.layout().fields().size() == 2) {
            checkField(error.layout().fields().get(0), "code",
                RuntimeDescriptor.String.INSTANCE, true,
                DefaultOwner.BUILTIN_DEFAULTS, "Error");
            checkField(error.layout().fields().get(1), "message",
                RuntimeDescriptor.String.INSTANCE, true,
                DefaultOwner.BUILTIN_DEFAULTS, "Error");
        }

        // The declaration authority: the checker's synthesized declaration.
        BuiltinErrorDeclaration declaration =
            BuiltinErrorDeclaration.synthesized(Span.synthetic(SYNTH_SPAN_FILE));
        checkEq(NameResolver.intrinsicErrorIdentity(), declaration.identity(),
            "the builtin declaration carries the intrinsic @/Error identity");
        checkEq(List.of("code", "message"),
            declaration.fields().stream()
                .map(BuiltinErrorDeclaration.Field::name).toList(),
            "the synthesized declaration's fields in declaration order");
        for (BuiltinErrorDeclaration.Field field : declaration.fields()) {
            checkEq(Type.String.INSTANCE, field.type(),
                field.name() + ": the synthesized resolved declared type");
            check(field.required(),
                field.name() + ": the synthesized field is required-present");
            check(field.declaration().defaultExpr().isPresent(),
                field.name() + ": the synthesized field carries its constant"
                    + " empty-string default");
            if (field.declaration().defaultExpr().isPresent()) {
                check(field.declaration().defaultExpr().get() instanceof LiteralExpr literal
                        && literal.value() instanceof LiteralValue.StringLiteral s
                        && s.value().isEmpty(),
                    field.name() + ": the default is the constant empty string");
            }
        }

        // The checker's root binding carries exactly those fields: the seed
        // derivation and the checker's Error binding share one authority.
        Lexer lexer = new Lexer("let x: int = 1\n", SYNTH_SPAN_FILE);
        deal.lexer.LexResult lex = lexer.tokenize();
        Parser parser = new Parser(lex.tokens(), SYNTH_SPAN_FILE);
        deal.parser.ParseResult parse = parser.parse();
        NameResolver resolver = new NameResolver(SYNTH_SPAN_FILE,
            (ModuleResolver) null);
        SymbolTable symbols = resolver.resolve(parse.program());
        Symbol errorSymbol = symbols.resolve("Error");
        check(errorSymbol instanceof Symbol.ClassSymbol,
            "the resolved module's root scope defines the builtin Error class");
        if (errorSymbol instanceof Symbol.ClassSymbol errorClass) {
            checkEq(NameResolver.intrinsicErrorIdentity(), errorClass.identity(),
                "the root binding carries the intrinsic @/Error identity");
            checkEq(2, errorClass.fields().size(),
                "the root binding carries exactly two fields");
            checkEq(declaration.fields().stream()
                    .map(f -> f.declaration()).toList(),
                errorClass.fields(),
                "the root binding's field records are exactly the synthesized"
                    + " declaration's (same names, flags, declared types, and"
                    + " constant empty-string defaults)");
        }
        // The builtin layout equals the checker declaration's projection.
        BuiltinErrorDeclaration derived = BuiltinErrorDeclaration.synthesized(
            Span.synthetic(SYNTH_SPAN_FILE));
        checkEq(derived.fields().get(0).name(),
            error.layout().fields().get(0).name(),
            "the builtin layout's first field is the declaration's first field");
        checkEq(derived.fields().get(1).name(),
            error.layout().fields().get(1).name(),
            "the builtin layout's second field is the declaration's second field");
    }

    // =========================================================================
    // 4. Negative seeds
    // =========================================================================

    private static void testMissingClassIdNegative() throws Exception {
        System.out.println("-- Negative seed: a declaration class without a"
            + " resolvable ClassId --");
        Path proj = Files.createTempDirectory("seeds-unresolved");
        try {
            writeFileIn(proj, "src/cfg.d.deal", HOST_DECLARATION);
            CompilationOrchestrator orchestrator = compileProject(proj,
                "src/app.deal", "src/cfg.d.deal", "host/cfg", Backend.LUAJIT);
            check(orchestrator.compile(),
                "the host-importing project compiles: "
                    + orchestrator.diagnostics());
            HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
            if (surface == null) {
                return;
            }
            ClassRegistrationSeeds.Production production =
                ClassRegistrationSeeds.produce(surface, Map.of(), Map.of(),
                    builtinError());
            CompilerDiagnostic diagnostic = expectFailure(production,
                "class without resolvable ClassId");
            if (diagnostic == null) {
                return;
            }
            expectE6005(diagnostic,
                ClassRegistrationSeeds.DECLARATION_CLASS_IDENTITY_UNRESOLVED,
                "CLASSES", "host.cfg",
                "ClassRegistrationSeeds"
                    + " DECLARATION_CLASS_IDENTITY_UNRESOLVED",
                "class without resolvable ClassId");
        } finally {
            deleteRecursively(proj);
        }
    }

    private static void testUnrepresentableFieldNegative() {
        System.out.println("-- Negative seed: an unrepresentable declared class"
            + " field type --");
        Span span = Span.synthetic("seeds.decl");
        HostDeclarationSurface.DeclaredField bad =
            new HostDeclarationSurface.DeclaredField(
                new ClassField(span, "bad", false, false,
                    new NamedType(span, "bad"), Optional.empty()),
                Type.Error.INSTANCE);
        ModuleId moduleId = new ModuleId("host.cfg");
        // The fact set is built directly: the declaration-surface producer
        // itself already fails closed for this field (ISSUE-0630's
        // DESCRIPTOR_UNREPRESENTABLE path — asserted right here), and the
        // seeds re-check the surface they consume instead of trusting a
        // foreign producer — this is that defensive arm.
        HostDeclarationSurface.Production viaProducer =
            HostDeclarationSurface.produce(List.of(
                new HostDeclarationSurface.DeclarationFacts(moduleId,
                    HostDeclarationSurface.DeclarationKind.HOST, Map.of(),
                    Map.of("Cfg", new HostDeclarationSurface.DeclaredClass(
                        "Cfg", HostDeclarationSurface.DeclarationKind.HOST,
                        List.of(bad))))));
        check(viaProducer.hasErrors() && viaProducer.surface() == null,
            "the declaration-surface producer fails closed for the same field"
                + " (ISSUE-0630)");
        HostDeclarationSurface surface = new HostDeclarationSurface(
            Map.of(moduleId, new HostDeclarationSurface.DeclarationFacts(
                moduleId, HostDeclarationSurface.DeclarationKind.HOST,
                Map.of(), Map.of("Cfg", new HostDeclarationSurface.DeclaredClass(
                    "Cfg", HostDeclarationSurface.DeclarationKind.HOST,
                    List.of(bad))))));
        ClassRegistrationSeeds.Production production =
            ClassRegistrationSeeds.produce(surface,
                Map.of(moduleId, external("host/cfg")), Map.of(),
                builtinError());
        CompilerDiagnostic diagnostic = expectFailure(production,
            "unrepresentable field");
        if (diagnostic == null) {
            return;
        }
        expectE6005(diagnostic, DescriptorService.DESCRIPTOR_UNREPRESENTABLE,
            "DESCRIPTORS", "host.cfg",
            "DescriptorService DESCRIPTOR_UNREPRESENTABLE",
            "unrepresentable field");
        check(diagnostic.message().contains("declared class field 'Cfg.bad'"),
            "the failure names the first unrepresentable class field: "
                + diagnostic.message());
    }

    private static void testDuplicateClassIdNegative() {
        System.out.println("-- Negative seed: a duplicated ClassId --");
        Span span = Span.synthetic("seeds.decl");
        HostDeclarationSurface.DeclaredClass declared =
            new HostDeclarationSurface.DeclaredClass("C",
                HostDeclarationSurface.DeclarationKind.HOST,
                List.of(new HostDeclarationSurface.DeclaredField(
                    new ClassField(span, "v", false, false,
                        new NamedType(span, "int"), Optional.empty()),
                    Type.Int.INSTANCE)));
        ModuleId first = new ModuleId("host.a");
        ModuleId second = new ModuleId("host.b");
        HostDeclarationSurface surface = HostDeclarationSurface.produce(
            List.of(
                new HostDeclarationSurface.DeclarationFacts(first,
                    HostDeclarationSurface.DeclarationKind.HOST, Map.of(),
                    Map.of("C", declared)),
                new HostDeclarationSurface.DeclarationFacts(second,
                    HostDeclarationSurface.DeclarationKind.HOST, Map.of(),
                    Map.of("C", declared)))).surface();
        Map<ModuleId, CanonicalModuleIdentity> classification = Map.of(
            first, external("host/cfg"), second, external("host/cfg"));
        ClassRegistrationSeeds.Production production =
            ClassRegistrationSeeds.produce(surface, classification, Map.of(),
                builtinError());
        CompilerDiagnostic diagnostic = expectFailure(production,
            "duplicated ClassId");
        if (diagnostic == null) {
            return;
        }
        expectE6005(diagnostic, ClassRegistrationSeeds.DUPLICATE_CLASS_ID,
            "CLASSES", "host.b", "ClassRegistrationSeeds DUPLICATE_CLASS_ID",
            "duplicated ClassId");
        check(diagnostic.message().contains("@$external/host/cfg/C"),
            "the failure names the duplicated class identity: "
                + diagnostic.message());
    }

    // =========================================================================
    // 5. Extern-C plan/class cross-check negatives (real generated metadata)
    // =========================================================================

    private static FfiGeneratedModule withPlans(FfiGeneratedModule real,
            Map<String, FfiCompilerClassDefaultPlan> plans) {
        return new FfiGeneratedModule(real.modulePath(), real.descriptor(),
            real.cdefBundle(), plans, real.bindings());
    }

    private static void testExternCPlanMismatchNegatives() throws Exception {
        System.out.println("-- Negative seeds: extern-C plan/class cross-checks"
            + " (real generated metadata) --");
        Path proj = Files.createTempDirectory("seeds-plan-mismatch");
        try {
            writeFileIn(proj, "src/math.d.deal", EXTERN_C_DECLARATION);
            CompilationOrchestrator orchestrator = compileProject(proj,
                "src/app.deal", "src/math.d.deal", "native/math",
                Backend.LUAJIT);
            check(orchestrator.compile(),
                "the extern-C-importing project compiles: "
                    + orchestrator.diagnostics());
            FfiGeneratedModule real =
                orchestrator.ffiGenerations().get("native.math");
            HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
            if (real == null || surface == null) {
                return;
            }
            String vec2Identity = "@$external/native/math/Vec2";
            FfiCompilerClassDefaultPlan realPlan = real.plans().get(vec2Identity);
            check(realPlan != null, "the real metadata carries the Vec2 plan");
            if (realPlan == null) {
                return;
            }
            Map<ModuleId, CanonicalModuleIdentity> classification =
                Map.of(EXTERN_C_MODULE, external("native/math"));

            // (a) A declared class without a plan entry: the plan removed.
            Map<String, FfiCompilerClassDefaultPlan> removed =
                new LinkedHashMap<>(real.plans());
            removed.remove(vec2Identity);
            CompilerDiagnostic missingPlan = expectFailure(
                ClassRegistrationSeeds.produce(surface, classification,
                    Map.of(EXTERN_C_MODULE, withPlans(real, removed)),
                    builtinError()),
                "plan entry removed");
            if (missingPlan != null) {
                expectE6005(missingPlan, ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "plan entry removed");
            }

            // (b) A plan entry without a class.
            Map<String, FfiCompilerClassDefaultPlan> extra =
                new LinkedHashMap<>(real.plans());
            extra.put("@$external/native/math/Ghost", realPlan);
            CompilerDiagnostic extraPlan = expectFailure(
                ClassRegistrationSeeds.produce(surface, classification,
                    Map.of(EXTERN_C_MODULE, withPlans(real, extra)),
                    builtinError()),
                "plan entry without a class");
            if (extraPlan != null) {
                expectE6005(extraPlan, ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "plan entry without a class");
                check(extraPlan.message().contains(
                        "@$external/native/math/Ghost"),
                    "the failure names the orphan plan entry: "
                        + extraPlan.message());
            }

            // (c) A field-name / order mismatch (the plan entries swapped).
            FfiCompilerClassDefaultPlan swappedPlan = new FfiCompilerClassDefaultPlan(
                realPlan.classIdentityText(),
                List.of(realPlan.entries().get(1), realPlan.entries().get(0)),
                realPlan.canonicalPlanContent(),
                realPlan.semanticDefaultContents(),
                realPlan.evaluatorImplementationContents(),
                realPlan.planDigest());
            Map<String, FfiCompilerClassDefaultPlan> swapped =
                new LinkedHashMap<>(real.plans());
            swapped.put(vec2Identity, swappedPlan);
            CompilerDiagnostic orderMismatch = expectFailure(
                ClassRegistrationSeeds.produce(surface, classification,
                    Map.of(EXTERN_C_MODULE, withPlans(real, swapped)),
                    builtinError()),
                "plan entry order mismatch");
            if (orderMismatch != null) {
                expectE6005(orderMismatch,
                    ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "plan entry order mismatch");
            }

            // (d) A canonical-descriptor mismatch.
            FfiCompilerClassDefaultPlan.Entry first = realPlan.entries().get(0);
            FfiCompilerClassDefaultPlan.Entry wrongDescriptor =
                new FfiCompilerClassDefaultPlan.Entry(first.name(), "int",
                    first.optional(), first.hasDefaultEvaluator(),
                    first.evaluatorContent());
            List<FfiCompilerClassDefaultPlan.Entry> wrongEntries =
                new ArrayList<>(realPlan.entries());
            wrongEntries.set(0, wrongDescriptor);
            FfiCompilerClassDefaultPlan wrongPlan = new FfiCompilerClassDefaultPlan(
                realPlan.classIdentityText(), wrongEntries,
                realPlan.canonicalPlanContent(),
                realPlan.semanticDefaultContents(),
                realPlan.evaluatorImplementationContents(),
                realPlan.planDigest());
            Map<String, FfiCompilerClassDefaultPlan> wrong =
                new LinkedHashMap<>(real.plans());
            wrong.put(vec2Identity, wrongPlan);
            CompilerDiagnostic descriptorMismatch = expectFailure(
                ClassRegistrationSeeds.produce(surface, classification,
                    Map.of(EXTERN_C_MODULE, withPlans(real, wrong)),
                    builtinError()),
                "plan descriptor mismatch");
            if (descriptorMismatch != null) {
                expectE6005(descriptorMismatch,
                    ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "plan descriptor mismatch");
            }

            // (e) An optional plan entry (extern-C struct fields are never
            // optional).
            FfiCompilerClassDefaultPlan.Entry optionalEntry =
                new FfiCompilerClassDefaultPlan.Entry(first.name(),
                    first.canonicalDescriptor(), true, true, "default");
            List<FfiCompilerClassDefaultPlan.Entry> optionalEntries =
                new ArrayList<>(realPlan.entries());
            optionalEntries.set(0, optionalEntry);
            FfiCompilerClassDefaultPlan optionalPlan = new FfiCompilerClassDefaultPlan(
                realPlan.classIdentityText(), optionalEntries,
                realPlan.canonicalPlanContent(),
                realPlan.semanticDefaultContents(),
                realPlan.evaluatorImplementationContents(),
                realPlan.planDigest());
            Map<String, FfiCompilerClassDefaultPlan> optional =
                new LinkedHashMap<>(real.plans());
            optional.put(vec2Identity, optionalPlan);
            CompilerDiagnostic optionalMismatch = expectFailure(
                ClassRegistrationSeeds.produce(surface, classification,
                    Map.of(EXTERN_C_MODULE, withPlans(real, optional)),
                    builtinError()),
                "optional plan entry");
            if (optionalMismatch != null) {
                expectE6005(optionalMismatch,
                    ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "optional plan entry");
            }

            // (f) Missing generated metadata entirely.
            CompilerDiagnostic noMetadata = expectFailure(
                ClassRegistrationSeeds.produce(surface, classification,
                    Map.of(), builtinError()),
                "generated metadata missing");
            if (noMetadata != null) {
                expectE6005(noMetadata, ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "generated metadata missing");
            }
        } finally {
            deleteRecursively(proj);
        }
    }

    /**
     * A declared class without a plan entry, exercised through the real
     * pipeline: an unmarked, non-exported class of an extern-C declaration
     * module is not an FFI class, so the generated metadata carries no row
     * for it while the declaration surface still declares it.
     */
    private static void testDeclaredClassWithoutPlanEntry() throws Exception {
        System.out.println("-- Negative seed: a declared class without a plan"
            + " entry (real pipeline) --");
        Path proj = Files.createTempDirectory("seeds-no-plan");
        try {
            writeFileIn(proj, "src/math.d.deal", """
                // @extern-c

                // @c-struct
                export class Vec2 {
                  x: number = 0.0;
                }

                class Helper {
                  v: int = 0;
                }

                export function add(a: int, b: int): int;
                """);
            CompilationOrchestrator orchestrator = compileProject(proj,
                "src/app.deal", "src/math.d.deal", "native/math",
                Backend.LUAJIT);
            boolean compiled = orchestrator.compile();
            check(compiled,
                "the extern-C-importing project compiles: "
                    + orchestrator.diagnostics());
            if (!compiled) {
                return;
            }
            FfiGeneratedModule generated =
                orchestrator.ffiGenerations().get("native.math");
            HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
            if (generated == null || surface == null) {
                return;
            }
            check(!generated.descriptor().classes().stream()
                    .anyMatch(row -> row.name().equals("Helper")),
                "the generated metadata carries no row for the unmarked class");
            check(surface.require(EXTERN_C_MODULE).declaredClass("Helper") != null,
                "the declaration surface still declares the unmarked class");
            CompilerDiagnostic diagnostic = expectFailure(
                ClassRegistrationSeeds.produce(surface,
                    Map.of(EXTERN_C_MODULE, external("native/math")),
                    Map.of(EXTERN_C_MODULE, generated), builtinError()),
                "declared class without a plan entry");
            if (diagnostic != null) {
                expectE6005(diagnostic, ClassRegistrationSeeds.FFI_PLAN_MISMATCH,
                    "CLASSES", "native.math",
                    "ClassRegistrationSeeds FFI_PLAN_MISMATCH",
                    "declared class without a plan entry");
            }
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 6. The fail-closed consumer arms
    // =========================================================================

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "seeds-main.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();

    private record CheckedSlice(ProgramNode program, SymbolTable symbols,
                                CheckResult checks) {
    }

    private record PipelineSlice(CheckedSlice slice, String interfaceHash,
                                 ExternalModuleInterface ownInterface,
                                 Map<ConstructKind, List<SemanticOpKind>> coverage) {
    }

    private static CheckedSlice checkSlice(String source) {
        Lexer lexer = new Lexer(source, SOURCE_ID);
        deal.lexer.LexResult lex = lexer.tokenize();
        Parser parser = new Parser(lex.tokens(), SOURCE_ID);
        deal.parser.ParseResult parse = parser.parse();
        check(parse.diagnostics().isEmpty(),
            "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver resolver = new NameResolver(MODULE.path(),
            (ModuleResolver) null);
        SymbolTable symbols = resolver.resolve(parse.program());
        check(resolver.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + resolver.diagnostics());
        if (!resolver.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(MODULE.path(), symbols,
            resolver, parse.program());
        check(checks.diagnostics().isEmpty(),
            "the slice checks cleanly: " + checks.diagnostics());
        if (checks.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symbols, checks);
    }

    private static PipelineSlice pipeline(CheckedSlice slice) {
        deal.semantic.CompilerInvocation invocation =
            CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                CapabilityRegistry.releaseRegistry());
        ModuleFact fact = new ModuleFact(SOURCE_ID, MODULE, false, false,
            slice.program(), Map.of(), slice.symbols(), slice.checks(), List.of());
        deal.semantic.CheckedProjectBuildResult built =
            deal.semantic.CheckedProjectBuilder.build(invocation, MODULE,
                List.of(fact));
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            "the checked project builds cleanly: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifests =
            LoweringSupport.computeManifests(invocation, built.input(),
                built.index());
        check(manifests != null && manifests.diagnostics().isEmpty()
                && manifests.manifests() != null
                && manifests.manifests().size() == 1,
            "the foundation detector produces exactly one requirement manifest: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()
                || manifests.manifests() == null
                || manifests.manifests().size() != 1) {
            return null;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage =
            new LinkedHashMap<>(manifests.manifests().get(0).constructCoverage());
        coverage.remove(ConstructKind.IMPORT_EXPORT_ENTRY);
        ExternalModuleInterface own = built.index().modules().get(MODULE);
        check(own != null, "the index carries the module's own interface entry");
        return new PipelineSlice(slice, built.index().interfaceIndexDigest(),
            own, coverage);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID),
            slice.program(), slice.checks(), List.of(), List.of(),
            CheckedModuleKind.IMPLEMENTATION);
    }

    private record ClassSlice(SemanticLowerer.ClassDeclarationCoreResult result,
                              PipelineSlice pipeline) {
    }

    /** The whole-pipeline driver: lexer/parser/checker → lowerModuleClassCore. */
    private static ClassSlice lowerModule(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        PipelineSlice pipeline = pipeline(slice);
        if (pipeline == null) {
            return null;
        }
        SemanticLowerer.ClassDeclarationCoreResult result =
            SemanticLowerer.lowerModuleClassCore(moduleOf(slice),
                SemanticProfile.DEAL_V1_2_INT32, pipeline.coverage(),
                pipeline.interfaceHash(), REGISTRY_HASH,
                pipeline.ownInterface(), SemanticIdAllocator.over(List.of(MODULE)));
        return new ClassSlice(result, pipeline);
    }

    private static OperationContractSnapshot contractFor(SemanticOp op,
            KindPayload payload, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION,
            op.kind(), op.resultType(), op.operandTypes(), selector, payload,
            op.failurePolicy(), List.of(), digest);
    }

    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        String digest = ContractSnapshotCanonicalizer.digest(
            contractFor(op, payload, "placeholder"));
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), contractFor(op, payload, digest));
    }

    private static LoweredModuleUnit unitWithOps(LoweredModuleUnit unit,
                                                 List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    private static List<SemanticOp> replaceOp(LoweredModuleUnit unit,
                                              SemanticOp replacement) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op.opId().equals(replacement.opId()) ? replacement : op);
        }
        return ops;
    }

    private static SemanticOp firstOfKind(LoweredModuleUnit unit,
                                          SemanticOpKind kind) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                return op;
            }
        }
        return null;
    }

    private interface ThrowingRunnable {
        void run();
    }

    private static void expectIllegalState(ThrowingRunnable runnable,
                                           String surface, DefaultOwner owner,
                                           String label) {
        try {
            runnable.run();
            fail(label + ": the " + surface + " accepted defaultOwner "
                + owner + " instead of failing closed");
        } catch (IllegalStateException expected) {
            if (expected.getMessage() == null
                    || !expected.getMessage().contains(owner.name())) {
                fail(label + ": the " + surface + " rejection does not name the"
                    + " owner " + owner + ": " + expected.getMessage());
            } else {
                passed++;
            }
        }
    }

    private static void testFailClosedOwnerArms() {
        System.out.println("-- Fail-closed owner arms: the registration owners"
            + " are rejected by the validator, both emitters, and the oracle --");
        ClassSlice slice = lowerModule("""
            class Point {
              x: int;
            }

            let p: Point = {x: 1}
            """);
        check(slice != null && slice.result() != null
                && slice.result().lowering() != null
                && !slice.result().lowering().hasErrors()
                && slice.result().lowering().unit() != null,
            "the class-literal slice lowers to a validated unit: "
                + (slice == null || slice.result() == null
                    || slice.result().lowering() == null ? "null"
                    : slice.result().lowering().diagnostics()));
        if (slice == null || slice.result() == null
                || slice.result().lowering() == null
                || slice.result().lowering().hasErrors()
                || slice.result().lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = slice.result().lowering().unit();
        StructuredBodyTable table = slice.result().lowering().table();
        ClassFactoryRegistry registry = slice.result().registry();
        JsonDefaultChildTable jsonDefaults = slice.result().jsonDefaults();
        ExternalModuleInterface own = slice.pipeline().ownInterface();

        SemanticOp classNew = firstOfKind(unit, SemanticOpKind.CLASS_NEW);
        check(classNew != null, "the slice lowers one CLASS_NEW op");
        if (classNew == null) {
            return;
        }
        // The seeds are project-level production data, never merged into a
        // unit's own layouts: the unit still carries only its own declared
        // layouts and no builtin Error entry.
        checkEq(java.util.Set.of(new ClassId(MODULE.path(), "Point")),
            unit.classLayouts().keySet(),
            "the unit carries only its own declared layouts");
        check(!unit.classLayouts().containsKey(ClassId.ERROR),
            "the unit's layouts never carry the builtin Error entry (the "
                + "seeds stay project data)");
        KindPayload.ClassNewPayload payload =
            (KindPayload.ClassNewPayload) classNew.payload();

        // Baseline: the untampered unit validates, emits, and executes — so
        // the negatives below are load-bearing.
        check(ClassConstructionValidator.validate(unit, table, registry,
                jsonDefaults, own, Map.of()).isEmpty(),
            "the baseline unit passes the class-construction validator");
        check(!LuaSemanticEmitter.emitModule(unit, table).isEmpty(),
            "the baseline unit emits the LuaJIT artifact");
        check(!JvmSemanticEmitter.emitModule(unit, table).source().isEmpty(),
            "the baseline unit emits the JVM artifact");
        check(SemanticOracle.execute(unit, table).terminal()
                instanceof deal.semantic.SemanticRuntimeModel.Terminal.Success,
            "the baseline unit executes in the oracle");

        for (DefaultOwner owner : List.of(DefaultOwner.HOST_DEFAULTS,
                DefaultOwner.FFI_PLAN, DefaultOwner.BUILTIN_DEFAULTS,
                DefaultOwner.RETAINED_ABI)) {
            SemanticOp tamperedOp = rebuild(classNew,
                new KindPayload.ClassNewPayload(payload.classId(),
                    payload.layout(), payload.providedFields(), owner,
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    payload.fieldBoundaries()));
            LoweredModuleUnit tampered = unitWithOps(unit,
                replaceOp(unit, tamperedOp));

            Optional<CompilerDiagnostic> failure =
                ClassConstructionValidator.validate(tampered, table, registry,
                    jsonDefaults, own, Map.of());
            String label = "owner " + owner;
            check(failure.isPresent(),
                label + ": the class-construction validator rejects the"
                    + " registration owner");
            if (failure.isPresent()) {
                check("E6005".equals(failure.get().code()),
                    label + ": the validator failure is E6005");
                check(failure.get().message().contains(
                        "validatorRule "
                            + ClassConstructionValidator.CONSTRUCTION_COHERENCE),
                    label + ": the validator failure names its rule: "
                        + failure.get().message());
                check(failure.get().message().contains("capability CLASSES")
                        && failure.get().message().contains("module 'main'")
                        && failure.get().message().contains(
                            "origin ClassConstructionValidator"),
                    label + ": the validator failure carries capability,"
                        + " module, and origin: " + failure.get().message());
                check(failure.get().message().contains(owner.name()),
                    label + ": the validator failure names the owner: "
                        + failure.get().message());
            }
            expectIllegalState(() -> LuaSemanticEmitter.emitModule(tampered,
                table), "LuaJIT emitter", owner, label);
            expectIllegalState(() -> JvmSemanticEmitter.emitModule(tampered,
                table), "JVM emitter", owner, label);
            expectIllegalState(() -> SemanticOracle.execute(tampered, table),
                "oracle", owner, label);
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Class Registration Seeds Tests (ISSUE-0631) ===\n");
        testHostDeclarationSeeds();
        testExternCDeclarationSeeds();
        testBuiltinErrorLayout();
        testMissingClassIdNegative();
        testUnrepresentableFieldNegative();
        testDuplicateClassIdNegative();
        testExternCPlanMismatchNegatives();
        testDeclaredClassWithoutPlanEntry();
        testFailClosedOwnerArms();
        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
