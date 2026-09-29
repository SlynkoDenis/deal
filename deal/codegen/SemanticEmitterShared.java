package deal.codegen;

import deal.semantic.ir.ClassId;
import deal.semantic.ir.RuntimeDescriptor;

/**
 * The static descriptor helpers shared by the JVM and LuaJIT semantic
 * emitters: the runtime-side descriptor text and the static runtime
 * kind both targets' boundary rows, checks, and atoms dispatch on.
 */
public final class SemanticEmitterShared {

    private SemanticEmitterShared() {
    }

    /**
     * The static runtime kind of a descriptor for atomization/checks:
     * {@code null}, {@code bool}, {@code int}, {@code number},
     * {@code string}, {@code table}, {@code array}, {@code function},
     * {@code class}, {@code err}, or {@code nullable:&lt;inner&gt;}.
     */
    public static String staticKind(RuntimeDescriptor descriptor) {
        if (descriptor == null) {
            return "ref";
        }
        if (descriptor instanceof RuntimeDescriptor.Null) {
            return "null";
        }
        if (descriptor instanceof RuntimeDescriptor.Boolean) {
            return "bool";
        }
        if (descriptor instanceof RuntimeDescriptor.Int) {
            return "int";
        }
        if (descriptor instanceof RuntimeDescriptor.Number) {
            return "number";
        }
        if (descriptor instanceof RuntimeDescriptor.String) {
            return "string";
        }
        if (descriptor instanceof RuntimeDescriptor.Table) {
            return "table";
        }
        if (descriptor instanceof RuntimeDescriptor.Array) {
            return "array";
        }
        if (descriptor instanceof RuntimeDescriptor.Bytes) {
            return "bytes";
        }
        if (descriptor instanceof RuntimeDescriptor.Func) {
            return "function";
        }
        if (descriptor instanceof RuntimeDescriptor.Class cls) {
            // The builtin Error class keeps the closed err atom
            // ({code, message}); user classes carry the class
            // identity tag (E5).
            return ClassId.ERROR.equals(cls.classId()) ? "err" : "class";
        }
        if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
            return "nullable:" + staticKind(nullable.inner());
        }
        return "ref";
    }

    /**
     * The runtime-side descriptor text of one descriptor (the closed
     * {@code null|boolean|int|number|string|table|array(INNER)|
     * nullable(INNER)|function(PARAMS;RETURN)} form the runtime checks
     * dispatch on): the single producer of the text the emitted boundary
     * rows, the host ABI cell checks, and a bridged host surface entry's
     * carried signature all use.
     */
    public static String descriptorText(RuntimeDescriptor descriptor) {
        if (descriptor instanceof RuntimeDescriptor.Null) {
            return "null";
        }
        if (descriptor instanceof RuntimeDescriptor.Boolean) {
            return "boolean";
        }
        if (descriptor instanceof RuntimeDescriptor.Int) {
            return "int";
        }
        if (descriptor instanceof RuntimeDescriptor.Number) {
            return "number";
        }
        if (descriptor instanceof RuntimeDescriptor.String) {
            return "string";
        }
        if (descriptor instanceof RuntimeDescriptor.Table) {
            return "table";
        }
        if (descriptor instanceof RuntimeDescriptor.Class cls) {
            return cls.classId().text();
        }
        if (descriptor instanceof RuntimeDescriptor.Array array) {
            return "array(" + descriptorText(array.element()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Bytes) {
            return "bytes";
        }
        if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
            return "nullable(" + descriptorText(nullable.inner()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Func func) {
            StringBuilder params = new StringBuilder();
            for (RuntimeDescriptor param : func.paramTypes()) {
                if (params.length() > 0) {
                    params.append(',');
                }
                params.append(descriptorText(param));
            }
            return "function(" + params + ";" + descriptorText(func.returnType()) + ")";
        }
        return "unknown";
    }
}
