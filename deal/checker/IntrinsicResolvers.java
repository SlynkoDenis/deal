package deal.checker;

import deal.ast.*;
import deal.types.Type;
import deal.types.Types;

import java.util.List;
import deal.diagnostics.DiagnosticCode;

/**
 * Built-in intrinsic resolvers for {@code int()}, {@code number()}, and {@code has()}.
 *
 * <p>Note: {@code has(obj.field)} is parsed as a {@link HasExpr} by the parser
 * and checked directly by {@link TypeChecker#checkHas(HasExpr)}.  The
 * {@link #HAS} resolver here is kept for robustness but is not normally
 * invoked through the call-intrinsic path.
 */
final class IntrinsicResolvers {

    private IntrinsicResolvers() {}

    /**
     * {@code int(v)} — conversion to int.
     *
     * <p>Overloads:
     * <ul>
     *   <li>{@code (number) => int}</li>
     *   <li>{@code (int | null) => int}</li>
     * </ul>
     */
    static final IntrinsicResolver INT = (call, argTypes, ctx) -> {
        if (argTypes.size() != 1) {
            ctx.error(DiagnosticCode.E5001, "int() expects exactly 1 argument, got " + argTypes.size(),
                call.span());
            return Type.Error.INSTANCE;
        }
        Type arg = argTypes.get(0);
        if (isNumber(arg) || isNullableInt(arg)) {
            return Type.Int.INSTANCE;
        }
        ctx.error(DiagnosticCode.E5001,
            "int() argument must be number or int|null, got " + TypeChecker.typeName(arg),
            call.span());
        return Type.Error.INSTANCE;
    };

    /**
     * {@code number(v)} — conversion to number.
     *
     * <p>Overloads:
     * <ul>
     *   <li>{@code (int) => number}</li>
     *   <li>{@code (number | null) => number}</li>
     * </ul>
     */
    static final IntrinsicResolver NUMBER = (call, argTypes, ctx) -> {
        if (argTypes.size() != 1) {
            ctx.error(DiagnosticCode.E5001, "number() expects exactly 1 argument, got " + argTypes.size(),
                call.span());
            return Type.Error.INSTANCE;
        }
        Type arg = argTypes.get(0);
        if (isInt(arg) || isNullableNumber(arg)) {
            return Type.Number.INSTANCE;
        }
        ctx.error(DiagnosticCode.E5001,
            "number() argument must be int or number|null, got " + TypeChecker.typeName(arg),
            call.span());
        return Type.Error.INSTANCE;
    };

    /**
     * {@code bytes(n)} — allocation of a zero-filled byte buffer
     * (DEAL v1.2, js-v12-int32-bytes D3/D4).
     *
     * <p>Exactly one argument of static type {@code int} (the signed
     * allocation length); the result is {@code bytes}. The runtime
     * validates the length value (E8001/E8004/E8012) and returns the
     * fresh carrier — the checker pins the shape only.</p>
     */
    static final IntrinsicResolver BYTES = (call, argTypes, ctx) -> {
        if (argTypes.size() != 1) {
            ctx.error(DiagnosticCode.E5001,
                "bytes() expects exactly 1 argument, got " + argTypes.size(),
                call.span());
            return Type.Error.INSTANCE;
        }
        Type arg = argTypes.get(0);
        if (isInt(arg)) {
            return Type.Bytes.INSTANCE;
        }
        ctx.error(DiagnosticCode.E5001,
            "bytes() argument must be int, got " + TypeChecker.typeName(arg),
            call.span());
        return Type.Error.INSTANCE;
    };

    /**
     * {@code has(obj.field)} — field presence test.
     *
     * <p>This resolver is a fallback path; normally {@code has()} is
     * parsed as a {@link HasExpr} and handled by the type checker directly.
     */
    static final IntrinsicResolver HAS = (call, argTypes, ctx) -> {
        if (call.args().size() != 1) {
            ctx.error(DiagnosticCode.E5001, "has() expects exactly 1 argument, got " + call.args().size(),
                call.span());
            return Type.Error.INSTANCE;
        }
        ExpressionNode arg = call.args().get(0);

        // The argument must be a member access expression
        if (!(arg instanceof MemberAccessExpr mae)) {
            ctx.error(DiagnosticCode.E4005,
                "'has' argument must be a class field access (obj.field)",
                arg.span());
            return Type.Error.INSTANCE;
        }

        // Check that the object is a class type
        Type objType = argTypes.get(0);
        if (objType instanceof Type.Error) return Type.Error.INSTANCE;

        // Actually we need the object's type BEFORE the member access
        // argTypes contains the type of the member access itself, not the object
        // So we need to get the type of the object from the type map
        Type objActualType = ctx.typeOf(mae.object());
        if (objActualType instanceof Type.Error) return Type.Error.INSTANCE;

        if (!(objActualType instanceof Type.Class cls)) {
            ctx.error(DiagnosticCode.E4005,
                "'has' argument must be a class field access, got " + TypeChecker.typeName(objActualType),
                arg.span());
            return Type.Error.INSTANCE;
        }

        // Look up the field in the class
        Symbol sym = ctx.resolveSymbol(cls.name());
        if (!(sym instanceof Symbol.ClassSymbol cs)) {
            ctx.error(DiagnosticCode.E4005, "Class '" + cls.name() + "' not found", arg.span());
            return Type.Error.INSTANCE;
        }

        String fieldName = mae.field();
        ClassField field = findField(cs.fields(), fieldName);
        if (field == null) {
            ctx.error(DiagnosticCode.E4005,
                "Field '" + fieldName + "' not declared in class '" + cls.name() + "'",
                arg.span());
            return Type.Error.INSTANCE;
        }
        if (!field.optional()) {
            ctx.error(DiagnosticCode.E4005,
                "'has' argument must be an optional class field; '" + fieldName
                + "' is required",
                arg.span());
            return Type.Error.INSTANCE;
        }

        return Type.Boolean.INSTANCE;
    };

    // -- helpers --

    private static boolean isInt(Type t) { return t == Type.Int.INSTANCE; }
    private static boolean isNumber(Type t) { return t == Type.Number.INSTANCE; }

    private static boolean isNullableInt(Type t) {
        return t instanceof Type.Nullable n && n.inner() == Type.Int.INSTANCE;
    }

    private static boolean isNullableNumber(Type t) {
        return t instanceof Type.Nullable n && n.inner() == Type.Number.INSTANCE;
    }

    static ClassField findField(List<ClassField> fields, String name) {
        for (ClassField f : fields) {
            if (f.name().equals(name)) return f;
        }
        return null;
    }
}
