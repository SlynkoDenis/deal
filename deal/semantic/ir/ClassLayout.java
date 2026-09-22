package deal.semantic.ir;

import java.util.List;
import java.util.Objects;

/**
 * A class layout of {@code deal.semantic-ir/1} (parent D16; schema S2):
 * the structural field layout a {@code CLASS_NEW}/{@code CLASS_FACTORY}
 * and the {@code JSON_FROM_CLASS}/{@code JSON_TO_CLASS} conversions carry.
 * Fields are in declaration order with presence and default ownership;
 * default expressions themselves are never part of the layout (an
 * external class interface exposes layout and owner factory, not another
 * module's default-expression AST).
 *
 * @param classId the class identity; non-null
 * @param fields  the field layouts in declaration order; non-null
 */
public record ClassLayout(ClassId classId, List<FieldLayout> fields) {

    /**
     * The compiler-owned builtin {@code Error} layout (ISSUE-0619;
     * {@code semantic-ir-construct-coverage-cutover} K13 item 1):
     * {@code @/Error} with exactly the declared fields {@code code} and
     * {@code message}, both {@code string} required-present under
     * {@link DefaultOwner#BUILTIN_DEFAULTS}. The constant is the same
     * compiler-owned layout the project-lowering registration seeds carry
     * (derived there from the checker's synthesized builtin declaration),
     * and it is the one layout every consumer resolves for the builtin
     * class — never a layout derived from source text, a host declaration,
     * or an interface-index entry. Its members are compiler constants:
     * no default expression, no factory, and no host artifact exists for
     * them, and the layout participates in layout resolution only (the
     * emitters exclude the class from the generated class carriers and
     * from the JSON plans).
     */
    public static final ClassLayout BUILTIN_ERROR = new ClassLayout(
        ClassId.ERROR, List.of(
            new FieldLayout("code", RuntimeDescriptor.String.INSTANCE, true,
                DefaultOwner.BUILTIN_DEFAULTS),
            new FieldLayout("message", RuntimeDescriptor.String.INSTANCE, true,
                DefaultOwner.BUILTIN_DEFAULTS)));

    /**
     * One field layout entry: name, declared descriptor, required-present
     * marker, and the default ownership used when the field is omitted.
     */
    public record FieldLayout(
        String name,
        RuntimeDescriptor descriptor,
        boolean required,
        DefaultOwner defaultOwner
    ) {

        public FieldLayout {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
            Objects.requireNonNull(defaultOwner, "defaultOwner must not be null");
        }
    }

    public ClassLayout(ClassId classId, List<FieldLayout> fields) {
        this.classId = Objects.requireNonNull(classId, "classId must not be null");
        this.fields = List.copyOf(fields);
    }
}
