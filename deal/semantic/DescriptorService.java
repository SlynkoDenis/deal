package deal.semantic;

import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalModuleIdentity;

import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticProfile;
import deal.types.Type;

import java.util.Objects;

/**
 * The single {@code Type} → {@link RuntimeDescriptor} producer for common
 * units (ISSUE-0233, design D1/D2): static, pure, deterministic,
 * stateless.
 *
 * <p><b>Mapping (D1, exact):</b> {@code Null→Null.INSTANCE},
 * {@code Boolean→Boolean.INSTANCE}, {@code Int→Int.INSTANCE},
 * {@code Number→Number.INSTANCE}, {@code String→String.INSTANCE},
 * {@code Table→Table.INSTANCE}, {@code Bytes→Bytes.INSTANCE}
 * (the v1.2 bytes descriptor member — ISSUE-0158),
 * {@code Class(name, modulePath)→Class(new ClassId(modulePath, name))},
 * {@code Array(T)→Array(describe(T))},
 * {@code Nullable(T)→Nullable(describe(T))} (both type hierarchies
 * enforce the same invariants), and
 * {@code Func(paramTypes, returnType, isAsync)→Func(param descriptors in
 * order, describe(returnType), isAsync)}. The service is total over the
 * eleven supported variants; structural equality of the produced descriptors
 * follows type equality — never text-based comparison.</p>
 *
 * <p><b>Fail closed (D1):</b> {@link Type.Error} has no
 * {@code RuntimeDescriptor} member in {@code deal.semantic-ir/1} and must
 * never be represented. {@link #describe(Type)} raises
 * {@link Defect} for it — internal control flow, never a crash and
 * never an invented descriptor. The unit-production seam converts the
 * defect into the E6005 diagnostic through
 * {@link #e6005(ModuleId, Defect)}: {@code FailureContractRegistry.e6005}
 * with {@code capability DESCRIPTORS}, {@code validatorRule
 * DESCRIPTOR_UNREPRESENTABLE}, {@code semanticProfile
 * DEAL_V1_2_INT32}, {@code irVersion deal.semantic-ir/1}, the module, and
 * the origin — the same pattern as {@code CanonicalTypeText.Defect} →
 * {@code INDEX_INTERNAL_ERROR_SENTINEL} (parent D11).
 * the bytes descriptor is a first-class member of the table (its boundary
 * projection is the kind check; the two C FFI crossings stay reserved
 * boundary names).</p>
 *
 * <p><b>Canonical text (D2):</b> the service's canonical spec text is
 * exactly {@link RuntimeDescriptor#canonicalSpecText()} — the
 * schema-pinned grammar ({@code docs/spec-v1.2.md:2231-2283}). No second
 * renderer exists here: {@code deal.descriptors.CanonicalRuntimeTypeDescriptor}
 * stays the target-emission text authority and is not consulted, so the
 * builtin {@code Error} class renders as the schema-pinned {@code @/Error}
 * ({@link ClassId#ERROR}), never a target projection spelling.
 * {@code parseCanonicalText(describe(t).canonicalSpecText())} is
 * structurally equal to {@code describe(t)} for every supported variant.</p>
 */
public final class DescriptorService {

    /**
     * The fact-defect identifier carried in the {@code validatorRule}
     * field of the E6005 diagnostic for an unrepresentable type
     * ({@link Type.Error}).
     */
    public static final String DESCRIPTOR_UNREPRESENTABLE = "DESCRIPTOR_UNREPRESENTABLE";

    private DescriptorService() {
        // Static surface only; no instances and no state.
    }

    /**
     * A descriptor-production fact defect: {@link Type.Error} reached a
     * descriptor-production position. The unit-production seam owns the
     * conversion into E6005 ({@code DESCRIPTOR_UNREPRESENTABLE}); this
     * exception is internal control flow, never a crash and never a
     * rendered fallback.
     */
    public static final class Defect extends RuntimeException {

        private static final long serialVersionUID = 1L;

        public Defect(String message) {
            super(message);
        }
    }

    /**
     * Produces the structural runtime descriptor of a checked
     * {@link Type} — the only {@code Type}→{@link RuntimeDescriptor}
     * producer for common units. Total and deterministic over the eleven
     * supported variants; {@link Type.Error} raises {@link Defect} (fail
     * closed, never an invented descriptor).
     *
     * @param type the checked type; non-null
     * @return the mapped {@code RuntimeDescriptor} (D1 table); its
     *         {@link RuntimeDescriptor#canonicalSpecText()} is the
     *         schema-pinned canonical text (D2)
     * @throws Defect when {@code type} is {@link Type.Error} (the internal
     *         checker sentinel is excluded from common units by contract)
     */
    public static RuntimeDescriptor describe(Type type) {
        Objects.requireNonNull(type, "type must not be null");
        return switch (type) {
            case Type.Null ignored -> RuntimeDescriptor.Null.INSTANCE;
            case Type.Boolean ignored -> RuntimeDescriptor.Boolean.INSTANCE;
            case Type.Int ignored -> RuntimeDescriptor.Int.INSTANCE;
            case Type.Number ignored -> RuntimeDescriptor.Number.INSTANCE;
            case Type.String ignored -> RuntimeDescriptor.String.INSTANCE;
            case Type.Table ignored -> RuntimeDescriptor.Table.INSTANCE;
            case Type.Bytes ignored -> RuntimeDescriptor.Bytes.INSTANCE;
            case Type.Error ignored -> throw new Defect(
                "Type.Error reached a descriptor-production position: the internal checker "
                    + "sentinel has no RuntimeDescriptor member in deal.semantic-ir/1 and is "
                    + "excluded from common units");
            case Type.Class cls -> new RuntimeDescriptor.Class(
                new ClassId(semanticModulePath(cls.identity()),
                    cls.name()));
            case Type.Array array -> new RuntimeDescriptor.Array(describe(array.element()));
            case Type.Nullable nullable ->
                new RuntimeDescriptor.Nullable(describe(nullable.inner()));
            case Type.Func func -> new RuntimeDescriptor.Func(
                func.paramTypes().stream().map(DescriptorService::describe).toList(),
                describe(func.returnType()), func.isAsync());
        };
    }

    /**
     * The semantic layer's structural module-path key for a canonical
     * class identity (the mechanical identity-carriage continuation —
     * the ISSUE-0233 layer remains its own authority): the builtin
     * module maps to the empty path, an externals module to
     * {@code $external/<specifier>}, and a project module to
     * {@code <configuredRootText>/<relativeComponents>} — so the
     * layer's {@code @modulePath/ClassName} class text coincides with
     * the canonical projection byte-for-byte for representable
     * identities.  Never derived from dotted module paths.
     */
    public static String semanticModulePath(CanonicalClassIdentity identity) {
        return switch (identity.moduleIdentity()) {
            case CanonicalModuleIdentity.BuiltinModule ignored -> "";
            case CanonicalModuleIdentity.ExternalModule external ->
                "$external/" + external.rawImportSpecifier();
            case CanonicalModuleIdentity.ProjectModule project -> {
                StringBuilder sb = new StringBuilder(
                    project.projectIdentity().configuredRootText());
                for (String component
                        : project.projectIdentity().relativeModuleComponents()) {
                    sb.append('/').append(component);
                }
                yield sb.toString();
            }
        };
    }

    /**
     * The pinned conversion seam (D1): converts a {@link Defect} raised
     * by {@link #describe(Type)} into the canonical E6005 diagnostic
     * through the failure contract registry — the only sanctioned E6005
     * construction surface. No {@code RuntimeDescriptor} is constructed
     * on this path.
     *
     * @param module the module whose unit-production seam hit the defect;
     *               non-null
     * @param defect the defect raised by {@link #describe(Type)}; non-null
     * @return the E6005 diagnostic ({@code DiagnosticCode.E6005}, phase
     *         {@code BACKEND_LOWERING}) whose registry-instantiated
     *         message carries {@code capability DESCRIPTORS},
     *         {@code validatorRule DESCRIPTOR_UNREPRESENTABLE},
     *         {@code semanticProfile DEAL_V1_2_INT32},
     *         {@code irVersion deal.semantic-ir/1}, the module, and the
     *         origin
     */
    public static CompilerDiagnostic e6005(ModuleId module, Defect defect) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(defect, "defect must not be null");
        LoweringFailureDetail detail = new LoweringFailureDetail(
            module.path(),
            SemanticCapability.DESCRIPTORS,
            DESCRIPTOR_UNREPRESENTABLE,
            SemanticProfile.DEAL_V1_2_INT32,
            LoweredModuleUnit.FORMAT_VERSION,
            "DescriptorService " + DESCRIPTOR_UNREPRESENTABLE
                + " (" + defect.getMessage() + ")");
        return FailureContractRegistry.e6005(detail);
    }
}
