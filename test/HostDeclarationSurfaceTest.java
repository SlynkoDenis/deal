package deal.test;

import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.HostDeclarationSurface.DeclarationFacts;
import deal.semantic.HostDeclarationSurface.DeclarationKind;
import deal.semantic.HostDeclarationSurface.DeclaredClass;
import deal.semantic.HostDeclarationSurface.DeclaredField;
import deal.semantic.ir.ModuleId;
import deal.types.Type;
import deal.types.Types;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

/**
 * The declaration surface producer tests (ISSUE-0630; design source
 * {@code project-lowering-entry-and-registration-seeds} D3 and the
 * declaration-surface contract).
 *
 * <p>The producer returns, for every host and extern-C declaration module
 * the compilation imports: the module identity, the declaration kind, the
 * declared export names with their checked types in declaration order,
 * and per declared class its fields in declaration order with the
 * resolved declared type plus the class's declaration kind. The facts
 * are read from the real declaration ASTs through the existing
 * {@code ExportExtractor} resolution seeded with the compilation's
 * module-path classification, and the extern-C module of the battery is a
 * real phase-3.9-validated module carrying its generated metadata
 * ({@code ffiGenerations()}).</p>
 *
 * <p>The retained host consumers keep byte-identical facts: the JS
 * declared map of a host import is pinned verbatim at its pre-ISSUE-0630
 * landing bytes. A declared class field whose resolved type has no
 * runtime representation fails the compile through the existing
 * descriptor path with the first E6005 and no surface, and the surface is
 * never silently partial.</p>
 */
public class HostDeclarationSurfaceTest {

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

    /** The externals identity of a host/extern-C declaration class. */
    private static Type.Class hostClass(String specifier, String name) {
        return Types.classType(name, new CanonicalClassIdentity(
            new CanonicalModuleIdentity.ExternalModule(specifier), name));
    }

    /** The field names of one declared class, in declaration order. */
    private static List<String> fieldNames(DeclaredClass declaredClass) {
        List<String> names = new ArrayList<>();
        for (DeclaredField field : declaredClass.fields()) {
            names.add(field.declaration().name());
        }
        return names;
    }

    /**
     * One declared field's declaration-AST fact tuple: name, optional,
     * nullable, and default-expression presence (the declaration order
     * is the list order).
     */
    private static String fieldFlags(DeclaredField field) {
        return field.declaration().name()
            + "|optional=" + field.declaration().optional()
            + "|nullable=" + field.declaration().nullable()
            + "|hasDefault=" + field.declaration().defaultExpr().isPresent();
    }

    private static List<String> fieldFlags(DeclaredClass declaredClass) {
        List<String> flags = new ArrayList<>();
        for (DeclaredField field : declaredClass.fields()) {
            flags.add(fieldFlags(field));
        }
        return flags;
    }

    /** The resolved declared types of one class, in declaration order. */
    private static List<Type> fieldTypes(DeclaredClass declaredClass) {
        List<Type> types = new ArrayList<>();
        for (DeclaredField field : declaredClass.fields()) {
            types.add(field.type());
        }
        return types;
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

    // =========================================================================
    // 1. A real host declaration module: exports, order, types, classes,
    //    field records, and the host declaration kind.
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

    private static void testHostDeclarationModuleFacts() throws Exception {
        System.out.println("-- Host declaration module facts (LuaJIT) --");
        Path proj = Files.createTempDirectory("host-surface");
        try {
            writeFileIn(proj, "src/cfg.d.deal", HOST_DECLARATION);
            writeFileIn(proj, "src/app.deal", """
                import * as cfg from "host/cfg"

                export function main(): null {
                  return null;
                }
                """);
            // The host module has no implementation on disk: the surface
            // is compile-time declaration data, so no host code could
            // have loaded or executed.
            check(!Files.exists(proj.resolve("src/cfg.deal")),
                "the host declaration has no implementation companion");
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("out").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, Backend.LUAJIT,
                Map.of("host/cfg",
                    proj.resolve("src/cfg.d.deal").toAbsolutePath().toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize());
            check(orchestrator.compile(),
                "the host-importing project compiles: "
                    + orchestrator.diagnostics());

            HostDeclarationSurface surface =
                orchestrator.hostDeclarationSurface();
            check(surface != null, "the compile produced a declaration surface");
            if (surface == null) return;
            checkEq(List.of(new ModuleId("host.cfg")), surface.moduleIds(),
                "the surface covers exactly the imported declaration module");

            DeclarationFacts facts = surface.require(new ModuleId("host.cfg"));
            checkEq(DeclarationKind.HOST, facts.kind(),
                "the host declaration module carries the HOST kind");

            // Declared export names with their checked types in
            // declaration order.
            checkEq(List.of("Endpoint", "ServerConfig", "describe", "version"),
                List.copyOf(facts.exports().keySet()),
                "the declared exports keep declaration order");
            checkEq(hostClass("host/cfg", "Endpoint"),
                facts.exports().get("Endpoint"),
                "the Endpoint export carries the canonical externals class type");
            checkEq(hostClass("host/cfg", "ServerConfig"),
                facts.exports().get("ServerConfig"),
                "the ServerConfig export carries the canonical externals class type");
            checkEq(new Type.Func(List.of(hostClass("host/cfg", "ServerConfig")),
                    Type.String.INSTANCE, false),
                facts.exports().get("describe"),
                "the describe export carries its checked function type");
            checkEq(new Type.Func(List.of(), Type.Int.INSTANCE, false),
                facts.exports().get("version"),
                "the version export carries its checked function type");

            // Per declared class: the fields in declaration order with
            // their resolved declared types plus the class kind.
            checkEq(List.of("Endpoint", "ServerConfig"),
                List.copyOf(facts.classes().keySet()),
                "the declared classes keep declaration order");
            DeclaredClass endpoint = facts.declaredClass("Endpoint");
            DeclaredClass serverConfig = facts.declaredClass("ServerConfig");
            check(endpoint != null && serverConfig != null,
                "both declared classes are present (no dropped class)");
            if (endpoint == null || serverConfig == null) return;
            checkEq(DeclarationKind.HOST, endpoint.kind(),
                "the Endpoint class carries the host declaration kind");
            checkEq(DeclarationKind.HOST, serverConfig.kind(),
                "the ServerConfig class carries the host declaration kind");
            checkEq(List.of("path"), fieldNames(endpoint),
                "the Endpoint fields keep declaration order");
            checkEq(List.of("path|optional=false|nullable=false|hasDefault=false"),
                fieldFlags(endpoint),
                "the Endpoint field record carries the declaration AST facts");
            checkEq(List.of(Type.String.INSTANCE), fieldTypes(endpoint),
                "the Endpoint field record carries the resolved declared type");
            checkEq(List.of("port", "endpoint", "tags", "note"),
                fieldNames(serverConfig),
                "the ServerConfig fields keep declaration order (no dropped field)");
            checkEq(List.of(
                    "port|optional=false|nullable=false|hasDefault=false",
                    "endpoint|optional=false|nullable=false|hasDefault=false",
                    "tags|optional=true|nullable=false|hasDefault=false",
                    "note|optional=true|nullable=true|hasDefault=false"),
                fieldFlags(serverConfig),
                "the ServerConfig field records carry the declaration AST facts");
            checkEq(List.of(
                    Type.Int.INSTANCE,
                    hostClass("host/cfg", "Endpoint"),
                    new Type.Array(Type.String.INSTANCE),
                    Types.nullable(Type.String.INSTANCE)),
                fieldTypes(serverConfig),
                "the ServerConfig field records carry the resolved declared types");
            checkEq(hostClass("host/cfg", "Endpoint"),
                serverConfig.fields().get(1).type(),
                "a same-module class field resolves to the declaring module's"
                    + " class identity");
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 2. A real extern-C declaration module carrying its generated
    //    metadata: the same facts under the extern-C kind.
    // =========================================================================

    private static void testExternCDeclarationModuleFacts() throws Exception {
        System.out.println("-- Extern-C declaration module facts (LuaJIT) --");
        Path proj = Files.createTempDirectory("extern-c-surface");
        try {
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
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as math from "native/math"

                export function main(): null {
                  return null;
                }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("out").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, Backend.LUAJIT,
                Map.of("native/math",
                    proj.resolve("src/math.d.deal").toAbsolutePath().toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize());
            check(orchestrator.compile(),
                "the extern-C-importing project compiles: "
                    + orchestrator.diagnostics());

            // Anti-hollow: the extern-C module really went through phase
            // 3.9 and carries its generated metadata.
            check(orchestrator.ffiGenerations().containsKey("native.math"),
                "the extern-C module carries its generated metadata: "
                    + orchestrator.ffiGenerations().keySet());
            check(orchestrator.ffiGenerations().get("native.math")
                    .plans().containsKey("@$external/native/math/Vec2"),
                "the generated metadata carries the Vec2 class plan");
            check(orchestrator.ffiGenerations().get("native.math")
                    .bindings().state() == deal.ffi.FfiBindingState.UNBOUND,
                "the extern-C forward cells stay UNBOUND (no library load"
                    + " and no symbol resolution during the compile)");

            HostDeclarationSurface surface =
                orchestrator.hostDeclarationSurface();
            check(surface != null, "the compile produced a declaration surface");
            if (surface == null) return;
            checkEq(List.of(new ModuleId("native.math")), surface.moduleIds(),
                "the surface covers exactly the imported extern-C module");

            DeclarationFacts facts =
                surface.require(new ModuleId("native.math"));
            checkEq(DeclarationKind.EXTERN_C, facts.kind(),
                "the extern-C declaration module carries the EXTERN_C kind");
            checkEq(List.of("Handle", "Vec2", "add"),
                List.copyOf(facts.exports().keySet()),
                "the extern-C exports keep declaration order");
            checkEq(hostClass("native/math", "Handle"),
                facts.exports().get("Handle"),
                "the Handle export carries the canonical externals class type");
            checkEq(hostClass("native/math", "Vec2"),
                facts.exports().get("Vec2"),
                "the Vec2 export carries the canonical externals class type");
            checkEq(new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                    Type.Int.INSTANCE, false),
                facts.exports().get("add"),
                "the add export carries its checked function type");

            checkEq(List.of("Handle", "Vec2"),
                List.copyOf(facts.classes().keySet()),
                "the declared classes keep declaration order");
            DeclaredClass handle = facts.declaredClass("Handle");
            DeclaredClass vec2 = facts.declaredClass("Vec2");
            check(handle != null && vec2 != null,
                "both declared extern-C classes are present");
            if (handle == null || vec2 == null) return;
            checkEq(DeclarationKind.EXTERN_C, handle.kind(),
                "the Handle class carries the extern-C declaration kind");
            checkEq(DeclarationKind.EXTERN_C, vec2.kind(),
                "the Vec2 class carries the extern-C declaration kind");
            checkEq(List.of(), fieldNames(handle),
                "the opaque pointer class carries no fields");
            checkEq(List.of(
                    "x|optional=false|nullable=false|hasDefault=true",
                    "y|optional=false|nullable=false|hasDefault=true"),
                fieldFlags(vec2),
                "the C-struct field records carry the declaration AST facts");
            checkEq(List.of(Type.Number.INSTANCE, Type.Number.INSTANCE),
                fieldTypes(vec2),
                "the C-struct field records carry the resolved declared types");
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 3. The retained host projection stays byte-identical: the JS
    //    declared map of the host import is pinned at its pre-change
    //    landing bytes.
    // =========================================================================

    /**
     * The pinned JS declared-map text of the battery's host import,
     * captured verbatim from the pre-ISSUE-0630 tree (the retained JS
     * declared-map consumer's output over the delegating producer).
     */
    private static final String PINNED_JS_DECLARED_MAP =
        "const cfg = $rt.loadHost($require(\"./host/cfg\"), "
            + "{\"Endpoint\": { $k: \"class\", $d: \"@$external/host/cfg/Endpoint\","
            + " $fields: [{ name: \"path\", $d: \"string\", optional: false,"
            + " nullable: false, hasDefault: false }] }, \"ServerConfig\":"
            + " { $k: \"class\", $d: \"@$external/host/cfg/ServerConfig\","
            + " $fields: [{ name: \"port\", $d: \"int\", optional: false,"
            + " nullable: false, hasDefault: false }, { name: \"endpoint\","
            + " $d: \"@$external/host/cfg/Endpoint\", optional: false,"
            + " nullable: false, hasDefault: false }, { name: \"tags\","
            + " $d: \"[string]\", optional: true, nullable: false,"
            + " hasDefault: false }, { name: \"note\", $d: \"?string\","
            + " optional: true, nullable: true, hasDefault: false }] },"
            + " \"describe\": { $k: \"function\","
            + " $d: \"(@$external/host/cfg/ServerConfig)->string\" },"
            + " \"version\": { $k: \"function\", $d: \"()->int\" }}, \"host/cfg\",";

    private static void testHostProjectionByteIdentity() throws Exception {
        System.out.println("-- Retained JS declared map stays byte-identical --");
        Path proj = Files.createTempDirectory("host-js-surface");
        try {
            writeFileIn(proj, "src/cfg.d.deal", HOST_DECLARATION);
            writeFileIn(proj, "src/app.deal", """
                import * as cfg from "host/cfg"

                export function main(): null {
                  return null;
                }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("out").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, Backend.JS,
                Map.of("host/cfg",
                    proj.resolve("src/cfg.d.deal").toAbsolutePath().toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize());
            check(orchestrator.compile(),
                "the host-importing project compiles on JS: "
                    + orchestrator.diagnostics());
            Path artifact = output.resolve("app.js");
            check(Files.isRegularFile(artifact),
                "the JS artifact is published: " + artifact);
            if (!Files.isRegularFile(artifact)) return;
            String source = Files.readString(artifact);
            check(source.contains(PINNED_JS_DECLARED_MAP),
                "the JS declared map is byte-identical to its pre-change"
                    + " pin: " + source);
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 4. Negative seed: an unrepresentable declared class field type
    //    returns the first E6005 through the descriptor path, no surface,
    //    and no artifact.
    // =========================================================================

    private static void testUnrepresentableFieldFailsClosed(
            Backend backend) throws Exception {
        System.out.println("-- Unrepresentable declared class field type"
            + " (" + backend + ") --");
        Path proj = Files.createTempDirectory("host-unrepresentable");
        try {
            writeFileIn(proj, "src/cfg.d.deal", """
                export class Cfg {
                  good: int;
                  bad1: null | null;
                  bad2: null | null;
                }

                export function describe(c: Cfg): string;
                """);
            writeFileIn(proj, "src/app.deal", """
                import * as cfg from "host/cfg"

                export function main(): null {
                  return null;
                }
                """);
            Path entry = proj.resolve("src/app.deal").toAbsolutePath();
            Path output = proj.resolve("out").toAbsolutePath();
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, output, false, false, false, backend,
                Map.of("host/cfg",
                    proj.resolve("src/cfg.d.deal").toAbsolutePath().toString()),
                List.of(proj.resolve("src").toAbsolutePath()),
                Path.of(".").toAbsolutePath().normalize());
            check(!orchestrator.compile(),
                "the unrepresentable declared class field type fails the compile");

            List<CompilerDiagnostic> errors = errors(orchestrator);
            checkEq(1, errors.size(),
                "exactly the first error is reported: " + errors);
            if (errors.size() != 1) return;
            CompilerDiagnostic e6005 = errors.get(0);
            checkEq("E6005", e6005.code(),
                "the failure carries E6005");
            String message = e6005.message();
            check(message.startsWith("Common semantic lowering failed: module"
                    + " 'host.cfg', capability DESCRIPTORS, validatorRule"
                    + " DESCRIPTOR_UNREPRESENTABLE,"),
                "the E6005 carries module, capability, and validator rule: "
                    + message);
            check(message.contains("semanticProfile DEAL_V1_2_INT32")
                    && message.contains("irVersion deal.semantic-ir/1"),
                "the E6005 carries the profile and IR version: " + message);
            check(message.contains("origin DescriptorService"
                    + " DESCRIPTOR_UNREPRESENTABLE"),
                "the E6005 carries the descriptor-path origin: " + message);
            check(message.contains("declared class field 'Cfg.bad1'"),
                "the E6005 names the first unrepresentable field: " + message);
            check(orchestrator.hostDeclarationSurface() == null,
                "a producer defect yields no surface");
            check(!Files.exists(output),
                "a producer defect publishes no artifact: " + output);
        } finally {
            deleteRecursively(proj);
        }
    }

    // =========================================================================
    // 5. The surface-shape invariants: one entry per declaration module and
    //    one declaration kind per module.
    // =========================================================================

    private static void testSurfaceShapeInvariants() {
        System.out.println("-- Surface shape invariants --");
        DeclarationFacts facts = new DeclarationFacts(
            new ModuleId("host.cfg"), DeclarationKind.HOST,
            Map.of(), Map.of());

        boolean duplicateRejected = false;
        try {
            HostDeclarationSurface.produce(List.of(facts, facts));
        } catch (IllegalArgumentException e) {
            duplicateRejected = e.getMessage().contains("duplicate declaration module");
        }
        check(duplicateRejected,
            "a duplicate declaration module identity is a producer defect");

        boolean kindMismatchRejected = false;
        try {
            new DeclarationFacts(new ModuleId("native.math"),
                DeclarationKind.EXTERN_C, Map.of(),
                Map.of("Vec2", new DeclaredClass("Vec2",
                    DeclarationKind.HOST, List.of())));
        } catch (IllegalArgumentException e) {
            kindMismatchRejected = true;
        }
        check(kindMismatchRejected,
            "a class whose declaration kind disagrees with its module is a"
                + " producer defect");

        HostDeclarationSurface.Production production =
            HostDeclarationSurface.produce(List.of(facts));
        check(!production.hasErrors() && production.surface() != null,
            "a representable fact set produces exactly one surface");
        DeclarationFacts empty = new DeclarationFacts(new ModuleId("host.empty"),
            DeclarationKind.HOST, Map.of(), Map.of());
        HostDeclarationSurface.Production emptyProduction =
            HostDeclarationSurface.produce(List.of(empty));
        check(!emptyProduction.hasErrors()
                && emptyProduction.surface().moduleIds()
                    .equals(List.of(new ModuleId("host.empty"))),
            "a class-free declaration module still contributes its entry");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Host Declaration Surface Tests (ISSUE-0630) ===\n");
        testHostDeclarationModuleFacts();
        testExternCDeclarationModuleFacts();
        testHostProjectionByteIdentity();
        testUnrepresentableFieldFailsClosed(Backend.LUAJIT);
        testUnrepresentableFieldFailsClosed(Backend.JS);
        testSurfaceShapeInvariants();
        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
