package deal.semantic;

import deal.ast.ClassField;
import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.ir.ModuleId;
import deal.types.Type;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The declaration surface of one compilation (ISSUE-0630; design source
 * {@code project-lowering-entry-and-registration-seeds} D3 and the
 * declaration-surface contract): the per-declaration-module facts the one
 * project lowering entry and its registration seeds consume, covering
 * every host and extern-C declaration module the compilation imports.
 *
 * <pre>{@code
 * HostDeclarationSurface { moduleId -> DeclarationFacts {
 *     kind: HOST | EXTERN_C,
 *     exports: name -> checked Type (declaration order),
 *     classes: class name -> DeclaredClass {
 *         kind, fields: [DeclaredField{class field AST, resolved declared Type}]
 *     } } }
 * }</pre>
 *
 * <p><b>Producer.</b> {@link #produce(List)} is the single production
 * path: it turns the per-module declaration facts the orchestrator
 * extracts from the declaration ASTs into the immutable surface. The
 * export map is the existing {@code deal.module.ExportExtractor}
 * resolution seeded with the compilation's module-path classification
 * (so a same-module class field type carries the declaring module's
 * canonical class identity, never a dotted-path reconstruction); the
 * per-class field records carry the declaration AST's
 * {@link ClassField} (name, optional, nullable, default-expression
 * presence, the declaration order) plus the extractor's
 * {@code resolveFieldType} result — all resolved in the declaring
 * module's own context. The declaration kind is the compilation's
 * closed classification: {@link DeclarationKind#EXTERN_C} for a module
 * the metadata phase classifies extern-C, {@link DeclarationKind#HOST}
 * otherwise.</p>
 *
 * <p><b>Compile-time data only.</b> No evaluator runs, no library loads,
 * no symbol resolves, and no host code executes on any path here. The
 * surface is never silently partial: every given declaration module
 * contributes exactly one entry (a repeated module identity is a
 * producer defect), every declaration-order relation is preserved, and a
 * declared class field whose resolved declared type has no runtime
 * representation ({@link Type.Error}) fails production through the
 * existing descriptor path ({@link DescriptorService#describe} &rarr;
 * {@link DescriptorService#e6005}) with the first E6005 and no surface —
 * never a dropped field, a partial class, or an invented descriptor.</p>
 *
 * <p><b>Coverage boundary.</b> The surface carries host and extern-C
 * declaration modules — the declaration imports the host ABI and the C
 * FFI classify. The spec stdlib declaration modules are not host
 * declarations: they keep their {@code BuiltinModule} classification and
 * their existing consumer surfaces, and they declare no classes.</p>
 *
 * @param modules the per-declaration-module facts by module identity, in
 *                the compilation's declaration-module visit order;
 *                frozen, never merged into a unit's own class layouts
 */
public record HostDeclarationSurface(
        Map<ModuleId, DeclarationFacts> modules) {

    public HostDeclarationSurface {
        Objects.requireNonNull(modules, "modules must not be null");
        Map<ModuleId, DeclarationFacts> frozen = new LinkedHashMap<>();
        for (Map.Entry<ModuleId, DeclarationFacts> entry
                : modules.entrySet()) {
            Objects.requireNonNull(entry.getKey(), "module id must not be null");
            Objects.requireNonNull(entry.getValue(),
                "declaration facts must not be null");
            frozen.put(entry.getKey(), entry.getValue());
        }
        modules = Collections.unmodifiableMap(frozen);
    }

    /**
     * The closed declaration-module kind (ISSUE-0630; design source
     * {@code project-lowering-entry-and-registration-seeds} D5): a host
     * declaration class takes {@code HOST_DEFAULTS} and an extern-C
     * declaration class takes {@code FFI_PLAN} as its default owner, so
     * the kind is the registration-seed discriminator.
     */
    public enum DeclarationKind {

        /**
         * A host declaration module: its declared classes carry the
         * loaded host module's {@code <C>_defaults} entry.
         */
        HOST,

        /**
         * An extern-C declaration module (the metadata phase classifies
         * it through {@code @extern-c}): its declared classes carry the
         * loaded module's validated {@code <C>_plan} entry.
         */
        EXTERN_C
    }

    /**
     * The declaration facts of one declaration module: its identity, its
     * declaration kind, its declared export names with their checked
     * {@link Type}s in declaration order, and its declared classes with
     * their per-class declaration kind and fields in declaration order.
     *
     * @param moduleId the declaration module's dotted module path;
     *                 non-null
     * @param kind     the module's declaration kind; non-null
     * @param exports  the declared export names with their checked
     *                 types, in declaration order; non-null
     * @param classes  the declared classes by name, in declaration
     *                 order; non-null
     */
    public record DeclarationFacts(
            ModuleId moduleId,
            DeclarationKind kind,
            Map<String, Type> exports,
            Map<String, DeclaredClass> classes) {

        public DeclarationFacts {
            Objects.requireNonNull(moduleId, "moduleId must not be null");
            Objects.requireNonNull(kind, "kind must not be null");
            Objects.requireNonNull(exports, "exports must not be null");
            Objects.requireNonNull(classes, "classes must not be null");
            // Insertion-order-preserving frozen copies: the declaration
            // order is part of the pinned fact source.
            exports = Collections.unmodifiableMap(new LinkedHashMap<>(exports));
            Map<String, DeclaredClass> frozenClasses = new LinkedHashMap<>();
            for (Map.Entry<String, DeclaredClass> entry
                    : classes.entrySet()) {
                Objects.requireNonNull(entry.getKey(),
                    "class name must not be null");
                DeclaredClass declaredClass =
                    Objects.requireNonNull(entry.getValue(),
                        "declared class must not be null");
                if (declaredClass.kind() != kind) {
                    throw new IllegalArgumentException(
                        "declared class '" + declaredClass.name()
                            + "' of declaration module '" + moduleId.path()
                            + "' carries kind " + declaredClass.kind()
                            + " but its module carries " + kind
                            + ": one declaration kind per module");
                }
                frozenClasses.put(entry.getKey(), declaredClass);
            }
            classes = Collections.unmodifiableMap(frozenClasses);
        }

        /** The declared class of one class name, or null when absent. */
        public DeclaredClass declaredClass(String name) {
            return classes.get(name);
        }
    }

    /**
     * One declared class of a declaration module: the class name, its
     * declaration kind, and its fields in declaration order.
     *
     * @param name   the class name exactly as declared; non-null
     * @param kind   the declaring module's declaration kind; non-null
     * @param fields the declared fields in declaration order; non-null
     */
    public record DeclaredClass(
            String name,
            DeclarationKind kind,
            List<DeclaredField> fields) {

        public DeclaredClass {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(kind, "kind must not be null");
            fields = List.copyOf(
                Objects.requireNonNull(fields, "fields must not be null"));
            if (name.isEmpty()) {
                throw new IllegalArgumentException("class name must not be empty");
            }
        }
    }

    /**
     * One declared class field: the declaration AST's {@link ClassField}
     * record plus the resolved declared {@link Type} — the same fact pair
     * the retained host consumers read, so the host projection stays
     * byte-identical.
     *
     * @param declaration the declaration AST's field record (name,
     *                    optional, nullable, default-expression
     *                    presence); non-null
     * @param type        the resolved declared type, resolved in the
     *                    declaring module's own context; non-null
     */
    public record DeclaredField(ClassField declaration, Type type) {

        public DeclaredField {
            Objects.requireNonNull(declaration,
                "declaration must not be null");
            Objects.requireNonNull(type, "type must not be null");
        }
    }

    /**
     * The outcome of one {@link #produce(List)} call: on success exactly
     * one immutable surface and no diagnostics; on a declared class
     * field whose resolved type has no runtime representation, both no
     * surface and the first E6005 produced through the descriptor path.
     *
     * @param surface     the produced surface; null exactly when
     *                    production failed
     * @param diagnostics the E6005 diagnostics (empty on success);
     *                    non-null
     */
    public record Production(
            HostDeclarationSurface surface,
            List<CompilerDiagnostic> diagnostics) {

        public Production {
            Objects.requireNonNull(diagnostics,
                "diagnostics must not be null");
            diagnostics = List.copyOf(diagnostics);
            if (surface != null && !diagnostics.isEmpty()) {
                throw new IllegalArgumentException(
                    "a successful production carries no diagnostics");
            }
            if (surface == null && diagnostics.isEmpty()) {
                throw new IllegalArgumentException(
                    "a failed production carries at least one diagnostic");
            }
        }

        /** Whether production failed (at least one E6005 diagnostic). */
        public boolean hasErrors() {
            return !diagnostics.isEmpty();
        }
    }

    /**
     * The single production path of the declaration surface: freezes the
     * given per-declaration-module facts into one immutable surface or,
     * for the first declared class field whose resolved type has no
     * runtime representation, returns the first E6005 with no surface.
     *
     * <p>Every module contributes exactly one entry; a duplicate module
     * identity is a producer defect rejected at construction (never a
     * silently overwritten entry). The representability check runs over
     * every declared class field in declaration order through
     * {@link DescriptorService#describe} — the existing descriptor path
     * — so the surface can never carry an unrepresentable field type.</p>
     *
     * @param facts the per-declaration-module facts in the compilation's
     *              visit order; non-null, no null entries
     * @return the production outcome (surface or the first E6005)
     */
    public static Production produce(List<DeclarationFacts> facts) {
        Objects.requireNonNull(facts, "facts must not be null");
        Map<ModuleId, DeclarationFacts> modules = new LinkedHashMap<>();
        for (DeclarationFacts module : facts) {
            Objects.requireNonNull(module, "declaration facts must not be null");
            if (modules.putIfAbsent(module.moduleId(), module) != null) {
                throw new IllegalArgumentException(
                    "duplicate declaration module '" + module.moduleId().path()
                        + "': exactly one entry per declaration module");
            }
            for (DeclaredClass declaredClass : module.classes().values()) {
                for (DeclaredField field : declaredClass.fields()) {
                    try {
                        DescriptorService.describe(field.type());
                    } catch (DescriptorService.Defect defect) {
                        return new Production(null, List.of(
                            DescriptorService.e6005(module.moduleId(),
                                new DescriptorService.Defect(
                                    "declared class field '"
                                        + declaredClass.name() + "."
                                        + field.declaration().name()
                                        + "' of declaration module '"
                                        + module.moduleId().path() + "': "
                                        + defect.getMessage()))));
                    }
                }
            }
        }
        return new Production(new HostDeclarationSurface(modules), List.of());
    }

    /**
     * The declaration facts of one module identity; an absent identity is
     * a producer defect (every declaration module of the compilation is
     * covered by construction, so a missing entry can never be a
     * legitimate state and is never silently defaulted).
     *
     * @param moduleId the declaration module's identity; non-null
     * @return the module's declaration facts; non-null
     */
    public DeclarationFacts require(ModuleId moduleId) {
        Objects.requireNonNull(moduleId, "moduleId must not be null");
        DeclarationFacts found = modules.get(moduleId);
        if (found == null) {
            throw new IllegalStateException(
                "declaration module '" + moduleId.path()
                    + "' has no declaration-surface entry: the surface covers"
                    + " every host and extern-C declaration module of the"
                    + " compilation (producer defect)");
        }
        return found;
    }

    /** The declaration module identities in the surface's visit order. */
    public List<ModuleId> moduleIds() {
        return List.copyOf(modules.keySet());
    }
}
