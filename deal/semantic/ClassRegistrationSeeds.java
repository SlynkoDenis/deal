package deal.semantic;

import deal.checker.BuiltinErrorDeclaration;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiClassDescriptor;
import deal.ffi.FfiCompilerClassDefaultPlan;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrTextDecodeException;
import deal.semantic.ir.SemanticProfile;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The project-level class registration seeds of one compilation
 * (ISSUE-0631; design sources
 * {@code project-lowering-entry-and-registration-seeds} D4-D6 and the
 * registration-seed contract,
 * {@code luajit-jvm-single-lowering-production-cutover} C1's registration
 * list, and {@code semantic-ir-construct-coverage-cutover} K9 items 3/6
 * and K13 item 1):
 *
 * <pre>{@code
 * ClassRegistrationSeeds { classId -> ClassRegistration {
 *     layout: ClassLayout(classId, fields in declaration order),
 *     owner: the class's closed DefaultOwner member } }
 * }</pre>
 *
 * <p><b>Coverage.</b> Exactly one entry per declared class of every
 * declaration module of the produced {@link HostDeclarationSurface} —
 * host declaration classes with the owner member
 * {@link DefaultOwner#HOST_DEFAULTS}, extern-C declaration classes with
 * {@link DefaultOwner#FFI_PLAN} — plus exactly one compiler-owned builtin
 * {@code Error} entry ({@link ClassId#ERROR}, owner
 * {@link DefaultOwner#BUILTIN_DEFAULTS}). A declaration module without
 * classes contributes no entry.</p>
 *
 * <p><b>Fact sources.</b> The declarations and their field records come
 * from the one declaration surface; the class identity of a declared
 * class is resolved through the compilation's module-path classification
 * (the module-identity layer's single classification surface, the same
 * input the declaration surface's field resolution is seeded with) and
 * projected by {@link DescriptorService#semanticModulePath} — never
 * reconstructed from a dotted path. A host declaration class's fields
 * carry {@code DescriptorService.describe} of the resolved declared
 * {@link deal.types.Type} in declaration order with
 * {@code required = !optional}; an extern-C declaration class's fields
 * come from the validated plan's ordered entries with the plan's
 * canonical descriptors and {@code required = true} (extern-C struct
 * fields are never optional), cross-checked against the declaration
 * surface's own resolution (a declared class without a plan entry, a plan
 * entry without a class, or a field name/order/descriptor mismatch fails
 * closed). The builtin {@code Error} entry derives from the checker's
 * synthesized builtin class declaration
 * ({@link BuiltinErrorDeclaration}) — never from source text, a host
 * declaration, or an interface-index entry.</p>
 *
 * <p><b>Project-level production data.</b> The seeds are immutable,
 * deterministic (the registration order is the compiler-owned builtin
 * {@code Error} entry, then the declaration modules in surface order with
 * the declaration order per class), one entry per {@link ClassId}, and are
 * never merged into a {@link LoweredModuleUnit#classLayouts()} map: each
 * unit keeps carrying only its own declared layouts. A duplicated
 * {@link ClassId} is a producer defect, never a silently overwritten
 * entry. On any producer defect the result carries the first E6005 and no
 * seeds.</p>
 */
public record ClassRegistrationSeeds(
        Map<ClassId, ClassRegistration> registrations) {

    /**
     * A declaration class without a resolvable {@link ClassId}: the
     * declaring module carries no public canonical module identity.
     */
    public static final String DECLARATION_CLASS_IDENTITY_UNRESOLVED =
        "DECLARATION_CLASS_IDENTITY_UNRESOLVED";

    /**
     * An extern-C plan/class cross-check failure: a declared class
     * without a generated class row or plan entry, a generated class row
     * or plan entry without a declared class, a field name, order, or
     * canonical-descriptor mismatch, an optional struct field, or a
     * missing generated metadata record.
     */
    public static final String FFI_PLAN_MISMATCH = "FFI_PLAN_MISMATCH";

    /** Two declared classes resolving to one {@link ClassId}. */
    public static final String DUPLICATE_CLASS_ID = "DUPLICATE_CLASS_ID";

    public ClassRegistrationSeeds {
        Objects.requireNonNull(registrations,
            "registrations must not be null");
        Map<ClassId, ClassRegistration> frozen = new LinkedHashMap<>();
        for (Map.Entry<ClassId, ClassRegistration> entry
                : registrations.entrySet()) {
            Objects.requireNonNull(entry.getKey(),
                "class id must not be null");
            Objects.requireNonNull(entry.getValue(),
                "class registration must not be null");
            frozen.put(entry.getKey(), entry.getValue());
        }
        registrations = Collections.unmodifiableMap(frozen);
    }

    /**
     * The outcome of one {@link #produce} call: on success exactly one
     * immutable seed set and no diagnostics; on the first producer defect
     * both no seeds and the first E6005.
     *
     * @param seeds       the produced seeds; null exactly when production
     *                    failed
     * @param diagnostics the E6005 diagnostics (empty on success);
     *                    non-null
     */
    public record Production(
            ClassRegistrationSeeds seeds,
            List<CompilerDiagnostic> diagnostics) {

        public Production {
            Objects.requireNonNull(diagnostics,
                "diagnostics must not be null");
            diagnostics = List.copyOf(diagnostics);
            if (seeds != null && !diagnostics.isEmpty()) {
                throw new IllegalArgumentException(
                    "a successful production carries no diagnostics");
            }
            if (seeds == null && diagnostics.isEmpty()) {
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
     * One class registration seed: the class's {@link ClassLayout} (fields
     * in declaration order, each carrying {@code defaultOwner} = the
     * class's owner member) and the class's closed
     * {@link DefaultOwner} member. The class-level owner and every field's
     * owner must agree: a registration fact is one owner per class.
     *
     * @param layout the class's layout; non-null
     * @param owner  the class's closed owner member; non-null
     */
    public record ClassRegistration(ClassLayout layout, DefaultOwner owner) {

        public ClassRegistration {
            Objects.requireNonNull(layout, "layout must not be null");
            Objects.requireNonNull(owner, "owner must not be null");
            for (ClassLayout.FieldLayout field : layout.fields()) {
                if (field.defaultOwner() != owner) {
                    throw new IllegalArgumentException(
                        "field '" + field.name() + "' of " + layout.classId()
                            + " carries defaultOwner " + field.defaultOwner()
                            + " but the registration's owner member is " + owner
                            + ": one owner per class registration");
                }
            }
        }
    }

    /** The registration of one class identity, or null when absent. */
    public ClassRegistration registrationFor(ClassId classId) {
        Objects.requireNonNull(classId, "classId must not be null");
        return registrations.get(classId);
    }

    /** The registered class identities in registration order. */
    public List<ClassId> classIds() {
        return List.copyOf(registrations.keySet());
    }

    /**
     * The single production path of the class registration seeds: exactly
     * one {@link ClassRegistration} per declared class of every
     * declaration module of the surface (declaration order) plus exactly
     * one builtin {@code Error} entry, or the first E6005 with no seeds.
     *
     * @param surface             the compilation's declaration surface
     *                            (the T1 producer's output); non-null
     * @param moduleClassification the compilation's module-path
     *                            classification keyed by module identity
     *                            (the module-identity layer's single
     *                            classification surface; a module absent
     *                            from it, or mapped to null, has no
     *                            public identity); non-null
     * @param externCModules      the validated generated metadata of every
     *                            declaration module the metadata phase
     *                            classified extern-C, keyed by module
     *                            identity; non-null
     * @param builtinError        the compiler-owned builtin {@code Error}
     *                            declaration; non-null
     * @return the production outcome (seeds or the first E6005)
     */
    public static Production produce(
            HostDeclarationSurface surface,
            Map<ModuleId, CanonicalModuleIdentity> moduleClassification,
            Map<ModuleId, FfiGeneratedModule> externCModules,
            BuiltinErrorDeclaration builtinError) {
        Objects.requireNonNull(surface, "surface must not be null");
        Objects.requireNonNull(moduleClassification,
            "moduleClassification must not be null");
        Objects.requireNonNull(externCModules,
            "externCModules must not be null");
        Objects.requireNonNull(builtinError, "builtinError must not be null");

        Map<ClassId, ClassRegistration> registrations = new LinkedHashMap<>();

        // The compiler-owned builtin `Error` entry first: it is a compiler
        // constant derived from the checker's synthesized builtin class
        // declaration, identical in every unit's layout context, with its
        // constant empty-string defaults under the BUILTIN_DEFAULTS owner —
        // never derived from source text, a host declaration, or an
        // interface-index entry.
        ClassId errorClassId = new ClassId(
            DescriptorService.semanticModulePath(builtinError.identity()),
            builtinError.identity().className());
        List<ClassLayout.FieldLayout> errorFields = new ArrayList<>();
        for (BuiltinErrorDeclaration.Field field : builtinError.fields()) {
            RuntimeDescriptor descriptor;
            try {
                descriptor = DescriptorService.describe(field.type());
            } catch (DescriptorService.Defect defect) {
                // The builtin declaration is a compiler constant: an
                // unrepresentable field there is an internal invariant
                // violation, never a project fact.
                throw new IllegalStateException(
                    "the compiler-owned builtin Error declaration carries an"
                        + " unrepresentable field '" + field.name() + "': "
                        + defect.getMessage());
            }
            errorFields.add(new ClassLayout.FieldLayout(field.name(),
                descriptor, field.required(),
                DefaultOwner.BUILTIN_DEFAULTS));
        }
        registrations.put(errorClassId, new ClassRegistration(
            new ClassLayout(errorClassId, errorFields),
            DefaultOwner.BUILTIN_DEFAULTS));

        for (ModuleId moduleId : surface.moduleIds()) {
            HostDeclarationSurface.DeclarationFacts facts =
                surface.require(moduleId);
            if (facts.classes().isEmpty()) {
                continue;
            }
            CanonicalModuleIdentity identity =
                moduleClassification.get(moduleId);
            if (identity == null) {
                return failure(DECLARATION_CLASS_IDENTITY_UNRESOLVED,
                    moduleId, "declared class '"
                        + facts.classes().keySet().iterator().next()
                        + "' of declaration module '" + moduleId.path()
                        + "' has no resolvable ClassId: the module carries no"
                        + " public canonical module identity (a declaration"
                        + " class there can never be registered)");
            }
            Production outcome = facts.kind()
                    == HostDeclarationSurface.DeclarationKind.EXTERN_C
                ? externCRegistrations(facts, identity,
                    externCModules.get(moduleId), registrations)
                : hostRegistrations(facts, identity, registrations);
            if (outcome != null) {
                return outcome;
            }
        }
        return new Production(new ClassRegistrationSeeds(registrations),
            List.of());
    }

    /**
     * The host declaration classes of one module: fields in declaration
     * order with {@code DescriptorService.describe} of the resolved
     * declared type, {@code required = !optional}, and the owner member
     * {@link DefaultOwner#HOST_DEFAULTS}.
     *
     * @return the failure outcome, or null when every class registered
     */
    private static Production hostRegistrations(
            HostDeclarationSurface.DeclarationFacts facts,
            CanonicalModuleIdentity identity,
            Map<ClassId, ClassRegistration> registrations) {
        for (HostDeclarationSurface.DeclaredClass declaredClass
                : facts.classes().values()) {
            ClassId classId = classIdOf(identity, declaredClass.name());
            List<ClassLayout.FieldLayout> fields = new ArrayList<>();
            for (HostDeclarationSurface.DeclaredField field
                    : declaredClass.fields()) {
                RuntimeDescriptor descriptor;
                try {
                    descriptor = DescriptorService.describe(field.type());
                } catch (DescriptorService.Defect defect) {
                    return descriptorFailure(facts.moduleId(), declaredClass,
                        field, defect);
                }
                fields.add(new ClassLayout.FieldLayout(
                    field.declaration().name(), descriptor,
                    !field.declaration().optional(),
                    DefaultOwner.HOST_DEFAULTS));
            }
            Production duplicate = register(registrations, classId,
                new ClassRegistration(new ClassLayout(classId, fields),
                    DefaultOwner.HOST_DEFAULTS),
                facts.moduleId(), declaredClass.name());
            if (duplicate != null) {
                return duplicate;
            }
        }
        return null;
    }

    /**
     * The extern-C declaration classes of one module: fields in
     * declaration order from the validated plan's ordered entries with the
     * plan's canonical descriptors and {@code required = true}, cross-
     * checked against the declaration surface's resolution, with the owner
     * member {@link DefaultOwner#FFI_PLAN}.
     *
     * @return the failure outcome, or null when every class registered
     */
    private static Production externCRegistrations(
            HostDeclarationSurface.DeclarationFacts facts,
            CanonicalModuleIdentity identity,
            FfiGeneratedModule generated,
            Map<ClassId, ClassRegistration> registrations) {
        ModuleId moduleId = facts.moduleId();
        if (generated == null) {
            return failure(FFI_PLAN_MISMATCH, moduleId,
                "extern-C declaration module '" + moduleId.path()
                    + "' carries no validated generated metadata: every"
                    + " declared class's plan entry comes from the phase-3.9"
                    + " generated module");
        }
        Map<String, FfiClassDescriptor> rowsByIdentity = new LinkedHashMap<>();
        for (FfiClassDescriptor row : generated.descriptor().classes()) {
            FfiClassDescriptor prior =
                rowsByIdentity.putIfAbsent(row.canonicalClassIdentity(), row);
            if (prior != null) {
                return failure(FFI_PLAN_MISMATCH, moduleId,
                    "two generated class rows carry the canonical identity '"
                        + row.canonicalClassIdentity() + "' ('" + prior.name()
                        + "' and '" + row.name() + "')");
            }
        }
        Map<String, FfiCompilerClassDefaultPlan> plans = generated.plans();
        // The plan/row bijection: every plan entry belongs to a C_STRUCT
        // class row (a plan without a class is a producer defect).
        for (Map.Entry<String, FfiCompilerClassDefaultPlan> entry
                : plans.entrySet()) {
            FfiClassDescriptor row = rowsByIdentity.get(entry.getKey());
            if (row == null) {
                return failure(FFI_PLAN_MISMATCH, moduleId,
                    "the validated plan entry '" + entry.getKey()
                        + "' has no generated class row: a plan entry without"
                        + " a class is a producer defect");
            }
            if (row.kind() != FfiClassDescriptor.ClassKind.C_STRUCT) {
                return failure(FFI_PLAN_MISMATCH, moduleId,
                    "the validated plan entry '" + entry.getKey()
                        + "' belongs to a " + row.kind()
                        + " class row: only a C_STRUCT class carries a plan");
            }
        }
        Set<String> declaredIdentities = new LinkedHashSet<>();
        for (HostDeclarationSurface.DeclaredClass declaredClass
                : facts.classes().values()) {
            ClassId classId = classIdOf(identity, declaredClass.name());
            declaredIdentities.add(classId.text());
            FfiClassDescriptor row = rowsByIdentity.get(classId.text());
            if (row == null) {
                return failure(FFI_PLAN_MISMATCH, moduleId,
                    "declared class '" + declaredClass.name() + "' ("
                        + classId.text() + ") has no plan entry: the validated"
                        + " extern-C metadata carries no generated class row"
                        + " for it");
            }
            List<ClassLayout.FieldLayout> fields = new ArrayList<>();
            switch (row.kind()) {
                case C_STRUCT -> {
                    FfiCompilerClassDefaultPlan plan = plans.get(classId.text());
                    if (plan == null) {
                        return failure(FFI_PLAN_MISMATCH, moduleId,
                            "the C_STRUCT class row '" + classId.text()
                                + "' has no validated plan entry");
                    }
                    if (declaredClass.fields().size()
                            != plan.entries().size()) {
                        return failure(FFI_PLAN_MISMATCH, moduleId,
                            "declared class '" + declaredClass.name()
                                + "' declares " + declaredClass.fields().size()
                                + " field(s) but its validated plan carries "
                                + plan.entries().size() + " entr(ies)");
                    }
                    for (int i = 0; i < plan.entries().size(); i++) {
                        FfiCompilerClassDefaultPlan.Entry entry =
                            plan.entries().get(i);
                        HostDeclarationSurface.DeclaredField surfaceField =
                            declaredClass.fields().get(i);
                        if (!entry.name().equals(
                                surfaceField.declaration().name())) {
                            return failure(FFI_PLAN_MISMATCH, moduleId,
                                "plan entry " + i + " of '" + classId.text()
                                    + "' names '" + entry.name()
                                    + "', not the declaration surface's '"
                                    + surfaceField.declaration().name()
                                    + "' (declaration order)");
                        }
                        if (entry.optional()) {
                            return failure(FFI_PLAN_MISMATCH, moduleId,
                                "the plan entry '" + entry.name()
                                    + "' of '" + classId.text()
                                    + "' is optional: extern-C struct fields"
                                    + " are never optional (optional fields"
                                    + " are E7002) and a seed field is always"
                                    + " required-present");
                        }
                        RuntimeDescriptor declared;
                        try {
                            declared = DescriptorService.describe(
                                surfaceField.type());
                        } catch (DescriptorService.Defect defect) {
                            return descriptorFailure(moduleId, declaredClass,
                                surfaceField, defect);
                        }
                        if (!declared.canonicalSpecText()
                                .equals(entry.canonicalDescriptor())) {
                            return failure(FFI_PLAN_MISMATCH, moduleId,
                                "the plan entry '" + entry.name() + "' of '"
                                    + classId.text()
                                    + "' carries canonical descriptor '"
                                    + entry.canonicalDescriptor()
                                    + "', not the declaration surface's"
                                    + " resolution '"
                                    + declared.canonicalSpecText() + "'");
                        }
                        RuntimeDescriptor descriptor;
                        try {
                            descriptor = RuntimeDescriptor.parseCanonicalText(
                                entry.canonicalDescriptor());
                        } catch (SemanticIrTextDecodeException decode) {
                            return failure(FFI_PLAN_MISMATCH, moduleId,
                                "the plan entry '" + entry.name() + "' of '"
                                    + classId.text() + "' carries a"
                                    + " non-canonical descriptor text '"
                                    + entry.canonicalDescriptor() + "': "
                                    + decode.getMessage());
                        }
                        fields.add(new ClassLayout.FieldLayout(entry.name(),
                            descriptor, true, DefaultOwner.FFI_PLAN));
                    }
                }
                case C_POINTER -> {
                    // An opaque pointer token: no fields, no plan.
                    if (!declaredClass.fields().isEmpty()) {
                        return failure(FFI_PLAN_MISMATCH, moduleId,
                            "the C_POINTER class row '" + classId.text()
                                + "' carries no fields but the declaration"
                                + " surface declares "
                                + declaredClass.fields().size() + " field(s)");
                    }
                }
            }
            Production duplicate = register(registrations, classId,
                new ClassRegistration(new ClassLayout(classId, fields),
                    DefaultOwner.FFI_PLAN),
                moduleId, declaredClass.name());
            if (duplicate != null) {
                return duplicate;
            }
        }
        // The converse direction: every generated class row names exactly
        // one declared class of the declaration surface.
        for (FfiClassDescriptor row : rowsByIdentity.values()) {
            if (!declaredIdentities.contains(row.canonicalClassIdentity())) {
                return failure(FFI_PLAN_MISMATCH, moduleId,
                    "the generated class row '"
                        + row.canonicalClassIdentity()
                        + "' has no declared class in the declaration"
                        + " surface: a plan entry without a class is a"
                        + " producer defect");
            }
        }
        return null;
    }

    /** Registers one class, failing closed on a duplicated identity. */
    private static Production register(
            Map<ClassId, ClassRegistration> registrations,
            ClassId classId,
            ClassRegistration registration,
            ModuleId moduleId,
            String className) {
        ClassRegistration prior =
            registrations.putIfAbsent(classId, registration);
        if (prior != null) {
            return failure(DUPLICATE_CLASS_ID, moduleId,
                "declared class '" + className + "' resolves to the class"
                    + " identity " + classId + ", which is already registered"
                    + ": exactly one registration per ClassId");
        }
        return null;
    }

    /**
     * The class identity of one declared class: the compilation's
     * module-path classification projected by
     * {@link DescriptorService#semanticModulePath} — the same rule the
     * lowering's class-typed arm uses for
     * {@code new ClassId(semanticModulePath(classType.identity()),
     * classType.name())}, never a dotted-path reconstruction.
     */
    private static ClassId classIdOf(CanonicalModuleIdentity moduleIdentity,
                                     String className) {
        return new ClassId(DescriptorService.semanticModulePath(
            new CanonicalClassIdentity(moduleIdentity, className)), className);
    }

    /**
     * The E6005 of an unrepresentable declared class field type through
     * the existing descriptor path ({@code capability DESCRIPTORS},
     * {@code validatorRule DESCRIPTOR_UNREPRESENTABLE}), naming the
     * offending class field.
     */
    private static Production descriptorFailure(
            ModuleId moduleId,
            HostDeclarationSurface.DeclaredClass declaredClass,
            HostDeclarationSurface.DeclaredField field,
            DescriptorService.Defect defect) {
        return new Production(null, List.of(DescriptorService.e6005(moduleId,
            new DescriptorService.Defect("declared class field '"
                + declaredClass.name() + "." + field.declaration().name()
                + "' of declaration module '" + moduleId.path() + "': "
                + defect.getMessage()))));
    }

    /** The first failure: E6005 with the rule, the module, and no seeds. */
    private static Production failure(String rule, ModuleId moduleId,
                                      String detail) {
        LoweringFailureDetail lowering = new LoweringFailureDetail(
            moduleId.path(), SemanticCapability.CLASSES, rule,
            SemanticProfile.DEAL_V1_2_INT32,
            LoweredModuleUnit.FORMAT_VERSION,
            "ClassRegistrationSeeds " + rule + " (" + detail + ")");
        return new Production(null,
            List.of(FailureContractRegistry.e6005(lowering)));
    }
}
