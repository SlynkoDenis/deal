package deal.semantic.ir;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * The factory-registration production record of
 * {@code deal.semantic-ir/1} (class-construction-jsonable-operations
 * K-D2; ISSUE-0511): one table per lowered unit recording, for each
 * exported class, the {@code CLASS_FACTORY} op registered under the
 * pre-allocated {@link ClassInterface#constructionEntry()}
 * {@link ClassFactoryId}.
 *
 * <pre>{@code
 * ClassFactoryRegistry {
 *   factories: Map<ClassFactoryId, OpId>   // constructionEntry -> CLASS_FACTORY op
 * }
 * }</pre>
 *
 * <p><b>Pinned production shape (K-D2).</b> The lowerer's
 * {@code ClassDeclaration} arm emits, for each exported class, exactly
 * one {@code CLASS_FACTORY} op registered under the deterministic
 * route-independent {@code constructionEntry} id allocated at index-build
 * time (foundation F2); non-exported classes get a layout but never a
 * factory and never a {@code ClassFactoryId} — their construction is
 * always {@code LOCAL}. The registry is the inert id&#8594;op binding
 * carrier the lowerer produces with the unit (the
 * {@link FunctionBindingRegistry}/{@link StructuredBodyTable} precedent):
 * consumers resolve the owner module's factory op by
 * {@code ClassFactoryId} without inference (parent D3), and the
 * factory&#8596;{@code constructionEntry} bijection for exported classes
 * is the production validator's check, never a construction check.</p>
 *
 * <p><b>Ownership.</b> This is construct-epic production data — no
 * schema-owned record changes and the foundation validator's closed
 * 14-condition rule set is untouched. The emission carrier that hands
 * the unit plus this record (and the block-membership table) to the
 * shared emitters is the later epic's seam; the record and its contract
 * are this epic's.</p>
 *
 * <p>Immutability: the map is defensively copied into an
 * insertion-ordered unmodifiable map, so later mutation of the
 * constructor argument cannot change the record. Map iteration order
 * (the producer's declaration order) is the deterministic traversal
 * order.</p>
 *
 * @param factories the constructionEntry-to-factory bindings; non-null
 *                  (keys and values must be non-null)
 */
public record ClassFactoryRegistry(Map<ClassFactoryId, OpId> factories) {

    public ClassFactoryRegistry {
        Objects.requireNonNull(factories, "factories must not be null");
        Map<ClassFactoryId, OpId> copied = new LinkedHashMap<>();
        for (Map.Entry<ClassFactoryId, OpId> entry : factories.entrySet()) {
            Objects.requireNonNull(entry.getKey(), "factories keys must not be null");
            Objects.requireNonNull(entry.getValue(), "factories values must not be null");
            copied.put(entry.getKey(), entry.getValue());
        }
        factories = Collections.unmodifiableMap(copied);
    }

    /**
     * The registered {@code CLASS_FACTORY} op id of the given
     * construction entry, or {@code null} when the id has no factory
     * (a non-exported class is never registered).
     *
     * @param constructionEntry the pre-allocated construction entry;
     *                          non-null
     * @return the factory op id, or {@code null}
     */
    public OpId factoryFor(ClassFactoryId constructionEntry) {
        return factories.get(Objects.requireNonNull(constructionEntry,
            "constructionEntry must not be null"));
    }

    /**
     * The owner's registered {@code CLASS_FACTORY} op of a
     * {@code CLASS_NEW(SHARED_FACTORY)} construction, resolved from the
     * delivered per-module registries of one executable closure: the
     * owner module is the unique module whose registry binds the
     * construction entry — the same binding the lowering's in-project
     * shared-factory facts carry ({@code SharedFactoryFacts.factoryOpId})
     * — and the bound op id carries that module.
     *
     * <p><b>The class descriptor namespace is never the owner.</b>
     * {@code ClassId.modulePath()} is the configured module-root text plus
     * the class file's relative directory components ({@code @src/Address}
     * for a class of the module {@code owner} under the root {@code src}),
     * not the module identity the closure's units and registries are keyed
     * by. Every {@code SHARED_FACTORY} execution consumer resolves its
     * owner through this method (the one delivered fact channel), never
     * from the class identity text.</p>
     *
     * @param registries      the closure's per-module registries, keyed by
     *                        module identity; non-null
     * @param classFactoryRef the construction's {@code classFactoryRef};
     *                        non-null on a validated shared-factory op
     * @return the owner's factory op id, or {@code null} when no module of
     *         the closure binds the construction entry
     * @throws IllegalStateException when the construction entry is a null
     *         reference, is registered by more than one module, or a
     *         registration binds an op of a different module (a producer
     *         defect, never a silent resolution)
     */
    public static OpId ownerFactoryOp(
            Map<ModuleId, ClassFactoryRegistry> registries,
            ClassFactoryId classFactoryRef) {
        Objects.requireNonNull(registries, "registries must not be null");
        if (classFactoryRef == null) {
            throw new IllegalStateException("a SHARED_FACTORY construction"
                + " carrying a null classFactoryRef is a producer defect");
        }
        ModuleId owner = null;
        OpId factoryOpId = null;
        for (Map.Entry<ModuleId, ClassFactoryRegistry> entry : registries.entrySet()) {
            OpId candidate = entry.getValue().factoryFor(classFactoryRef);
            if (candidate == null) {
                continue;
            }
            if (factoryOpId != null) {
                throw new IllegalStateException("constructionEntry " + classFactoryRef
                    + " is registered by modules " + owner + " and " + entry.getKey()
                    + ": one construction entry has exactly one owner (producer defect)");
            }
            owner = entry.getKey();
            factoryOpId = candidate;
        }
        if (factoryOpId != null && !factoryOpId.module().equals(owner)) {
            throw new IllegalStateException("constructionEntry " + classFactoryRef
                + " is registered under module " + owner + " but binds op "
                + factoryOpId + ": a module's registry binds a factory op of that"
                + " module (producer defect)");
        }
        return factoryOpId;
    }
}
