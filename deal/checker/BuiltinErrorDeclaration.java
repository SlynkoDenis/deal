package deal.checker;

import deal.ast.ClassField;
import deal.ast.LiteralExpr;
import deal.ast.LiteralValue;
import deal.ast.NamedType;
import deal.ast.Span;
import deal.identity.CanonicalClassIdentity;
import deal.types.Type;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The compiler-owned builtin {@code Error} class declaration — the
 * checker's synthesized root class of every module scope
 * ({@link NameResolver#seedIntrinsics}): the intrinsic
 * {@code BuiltinModule}/{@code Error} identity and exactly the two
 * declared fields {@code code} and {@code message}, both {@code string}
 * required-present with the constant empty-string default.
 *
 * <pre>{@code
 * BuiltinErrorDeclaration {
 *   identity: CanonicalClassIdentity(BuiltinModule, "Error"),
 *   fields: [ { declaration: ClassField(code,  string, required, ""), type: string },
 *             { declaration: ClassField(message, string, required, ""), type: string } ]
 * }
 * }</pre>
 *
 * <p><b>One authority (ISSUE-0631; design sources
 * {@code project-lowering-entry-and-registration-seeds} D6 and the
 * registration-seed contract).</b> {@link NameResolver#seedIntrinsics()}
 * defines its root {@code Error} binding from
 * {@link #synthesized(Span)}, and the project lowering derives the builtin
 * {@code Error} layout seed from the same declaration — so the builtin
 * layout is never derived from source text, from a host declaration, or
 * from an interface-index entry, and the two surfaces cannot diverge:
 * every {@link Field} carries both the declaration AST record (the name,
 * the optional flag, the constant empty-string default) and the resolved
 * declared {@link Type} authored once.</p>
 *
 * <p><b>Compile-time data only.</b> No evaluator runs, no library loads,
 * no symbol resolves, and no host code executes on any path here; the
 * record is immutable and deterministic.</p>
 *
 * @param identity the intrinsic builtin class identity
 *                 ({@code BuiltinModule}/{@code Error}); non-null
 * @param fields   the declared fields in declaration order
 *                 ({@code code}, {@code message}); non-null
 */
public record BuiltinErrorDeclaration(
        CanonicalClassIdentity identity,
        List<Field> fields) {

    public BuiltinErrorDeclaration {
        Objects.requireNonNull(identity, "identity must not be null");
        fields = List.copyOf(
            Objects.requireNonNull(fields, "fields must not be null"));
    }

    /**
     * One declared field of the builtin {@code Error} class: the
     * declaration AST record (name, optional, nullable, default-expression
     * presence — the constant empty-string default) plus the resolved
     * declared {@link Type}.
     *
     * @param declaration the declaration AST's field record; non-null
     * @param type        the resolved declared type; non-null
     */
    public record Field(ClassField declaration, Type type) {

        public Field {
            Objects.requireNonNull(declaration,
                "declaration must not be null");
            Objects.requireNonNull(type, "type must not be null");
        }

        /** The field name exactly as declared. */
        public String name() {
            return declaration.name();
        }

        /**
         * Whether the field is required-present (the declaration's
         * optional-negation) — every builtin {@code Error} field is.
         */
        public boolean required() {
            return !declaration.optional();
        }
    }

    /**
     * The synthesized builtin {@code Error} class declaration with its
     * AST field records at the given span: {@code code} and
     * {@code message}, both non-optional {@code string} fields whose
     * default expression is the constant empty string. The declared
     * {@code string} spelling and the resolved {@link Type.String} fact
     * are authored here, together, exactly once.
     *
     * @param span the span of the synthesized declaration (the checker's
     *             synthetic root span of the module being resolved);
     *             non-null
     * @return the synthesized declaration; non-null
     */
    public static BuiltinErrorDeclaration synthesized(Span span) {
        Objects.requireNonNull(span, "span must not be null");
        LiteralExpr emptyString = new LiteralExpr(span,
            new LiteralValue.StringLiteral(""));
        return new BuiltinErrorDeclaration(
            NameResolver.intrinsicErrorIdentity(),
            List.of(
                new Field(new ClassField(span, "code", false, false,
                    new NamedType(span, "string"), Optional.of(emptyString)),
                    Type.String.INSTANCE),
                new Field(new ClassField(span, "message", false, false,
                    new NamedType(span, "string"), Optional.of(emptyString)),
                    Type.String.INSTANCE)));
    }
}
