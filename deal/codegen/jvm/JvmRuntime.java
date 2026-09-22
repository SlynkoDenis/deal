package deal.codegen.jvm;

import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SharedStdlibSemantics;
import deal.semantic.ir.ActualKind;

import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * The shared JVM runtime helper of the decomposition-tail integration
 * verification (ISSUE-0410): the real runtime the generated shared-JVM
 * artifact executes against — event/effect/terminal protocol encoding
 * (byte-identical to the semantic oracle's report), the closed atom
 * encoding with first-observation allocation ids, the native boundary
 * projections (the descriptor-kind rule with the pinned int ladder, the
 * array element cause chain, the function-signature projection — exactly
 * the closed failure registry's templates, never invented text), the
 * closed B-D2 comparison table realized with native Java operators
 * (primitive {@code ==}/{@code <} on ints; IEEE {@code ==}/{@code <} on
 * doubles — never {@code Double.compare}; code point order on strings —
 * never {@code String.compareTo}; identity {@code ==} on references —
 * never {@code equals()}), and the array read/bounds cells with the
 * shared slot-space context.
 */
public final class JvmRuntime {

    private JvmRuntime() {
    }

    // =========================================================================
    // Values
    // =========================================================================

    /** The internal missing sentinel (past-end array reads). */
    public static final Object MISSING = new Object() {
        @Override public String toString() {
            return "missing";
        }
    };

    /** A string-keyed table with explicit key presence. */
    public static final class Table {
        public final LinkedHashMap<String, Object> entries = new LinkedHashMap<>();
        public final java.util.HashSet<String> keys = new java.util.HashSet<>();

        public Object read(String key) {
            if (!keys.contains(key)) {
                return MISSING;
            }
            return entries.get(key);
        }

        public void write(String key, Object value) {
            entries.put(key, value);
            keys.add(key);
        }

        public void remove(String key) {
            entries.remove(key);
            keys.remove(key);
        }
    }

    /**
     * A generated class instance (the CLASSES family's presence
     * carrier, E5): the canonical class identity tag plus per-field
     * value slots and boolean presence flags — present null is
     * {@code value == null && present == true} and is never conflated
     * with a missing field. The emitter generates one carrier class per
     * {@code ClassId}; this interface is the runtime's closed surface
     * over it (presence lookups, reads, writes, deletes).
     */
    public interface ClassInstance {

        /** The canonical {@code @modulePath/ClassName} identity text. */
        String classIdText();

        /** Presence of one field: a present field (present null included) is present. */
        boolean isPresent(String field);

        /** The present field's value, or {@link #MISSING} for an absent field. */
        Object read(String field);

        /** Stores one field value and marks the field present. */
        void write(String field, Object value);

        /**
         * Clears one field: the value slot is emptied and the presence
         * flag is cleared, so the field is missing again (the
         * {@code FIELD_DELETE} commit). Deleting an already-missing
         * field is a no-op.
         */
        void delete(String field);
    }

    /**
     * HAS_FIELD presence over one checked receiver key (the
     * CONTAINERS_AND_STRINGS extras): present — present null included —
     * → true, absent → false. The table-presence half realizes through
     * the explicit key set; the class-instance half realizes through the
     * generated carrier's presence flags (the CLASSES family). A
     * receiver outside the realized carriers is a fail-closed producer
     * defect, never a silent presence value.
     */
    public static boolean hasField(Object receiver, String key) {
        if (receiver instanceof Table table) {
            return table.keys.contains(key);
        }
        if (receiver instanceof ClassInstance instance) {
            return instance.isPresent(key);
        }
        throw new IllegalStateException("HAS_FIELD receiver " + receiver
            + " is not a supported presence carrier in this domain (the "
            + "presence surface admits keyed tables and generated class "
            + "instances only)");
    }

    /** A dense array with the shared slot-space length. */
    public static final class Array {
        public final List<Object> elements = new ArrayList<>();
        public int length;

        public Array(int length) {
            this.length = length;
        }
    }

    /**
     * A DEAL Error value ({@code code, message}) — the builtin
     * {@code Error} class's runtime carrier (ISSUE-0619;
     * {@code semantic-ir-construct-coverage-cutover} K13). The carrier is
     * a {@link ClassInstance} of the canonical {@code @/Error} identity:
     * both declared fields are always present, a field write commits in
     * place (every alias observes it), and {@code hasField}/{@code read}/
     * {@code write} resolve the declared field names — the same closed
     * presence surface the generated carriers realize. A field delete never
     * reaches the runtime (every builtin Error field is required-present
     * and the checker rejects {@code delete e.f} with E4004) and stays a
     * fail-closed producer defect.
     */
    public static final class ErrorValue implements ClassInstance {
        public String code;
        public String message;

        public ErrorValue(String code, String message) {
            this.code = code;
            this.message = message;
        }

        @Override
        public String classIdText() {
            return "@/Error";
        }

        @Override
        public boolean isPresent(String field) {
            return "code".equals(field) || "message".equals(field);
        }

        @Override
        public Object read(String field) {
            return switch (field) {
                case "code" -> code;
                case "message" -> message;
                default -> MISSING;
            };
        }

        @Override
        public void write(String field, Object value) {
            switch (field) {
                case "code" -> code = (String) value;
                case "message" -> message = (String) value;
                default -> throw new IllegalStateException(
                    "the builtin Error carrier has no field '" + field
                        + "' (producer defect)");
            }
        }

        @Override
        public void delete(String field) {
            throw new IllegalStateException("FIELD_DELETE targets the builtin Error"
                + " field '" + field + "': every builtin Error field is"
                + " required-present and the checker rejects the delete with E4004"
                + " — a fail-closed producer defect, never executed");
        }
    }

    /** An intrinsic function value (int()/number() as first-class values). */
    public static final class Intrinsic {
        @Override public String toString() {
            return "intrinsic";
        }
    }

    /** A function value: the invoker plus its carried signature text. */
    public interface Fn {
        Object invoke(Object[] args);
    }

    public static class FunctionValue {
        public final Fn fn;
        public final String signature;
        /** The canonical spec text (E8010 projections); null when unknown. */
        public final String spec;
        /** The source function id text for frame pushes; null when absent. */
        public final String fid;

        public FunctionValue(Fn fn, String signature) {
            this(fn, signature, null, null);
        }

        public FunctionValue(Fn fn, String signature, String spec, String fid) {
            this.fn = fn;
            this.signature = signature;
            this.spec = spec;
            this.fid = fid;
        }
    }

    /**
     * A {@code FUNCTION_ADAPT} adapter value (D15): the closed capture
     * mode state ({@code VALUE}: the retained source identity;
     * {@code SHARED_CELL}: the generation cell re-read per invocation;
     * {@code REEVALUATE_THUNK}: the thunk re-executor), the source
     * arity/spec, and the target signature carried for boundary checks.
     */
    public static final class AdapterValue extends FunctionValue {
        /** 0 = VALUE, 1 = SHARED_CELL, 2 = REEVALUATE_THUNK. */
        public final int mode;
        public final Object value;
        public final Object[] cell;
        public final Fn thunk;
        public final int arity;
        public final String sourceSpec;

        public AdapterValue(Fn fn, String signature, String spec, int mode, Object value,
                            Object[] cell, Fn thunk, int arity, String sourceSpec) {
            super(fn, signature, spec, null);
            this.mode = mode;
            this.value = value;
            this.cell = cell;
            this.thunk = thunk;
            this.arity = arity;
            this.sourceSpec = sourceSpec;
        }
    }

    /** A BREAK/CONTINUE/RETURN transfer signal crossing a try boundary. */
    public static final class Transfer extends RuntimeException {
        public final String kind;
        public final long id;
        public final Object value;

        public Transfer(String kind, long id, Object value) {
            super(null, null, false, false);
            this.kind = kind;
            this.id = id;
            this.value = value;
        }
    }

    /** A DEAL failure carrying its exact projection facts. */
    public static final class DealError extends RuntimeException {
        public final String code;
        public final String msg;
        public final String origin;
        public final String expected;
        public final String actual;
        public final String frames;
        public final DealError cause;

        public DealError(String code, String msg, String origin, String expected,
                         String actual, String frames, DealError cause) {
            super(msg, cause);
            this.code = code;
            this.msg = msg;
            this.origin = origin;
            this.expected = expected;
            this.actual = actual;
            this.frames = frames;
            this.cause = cause;
        }
    }

    // =========================================================================
    // Protocol state
    // =========================================================================

    static final ThreadLocal<List<String>> FRAMES = ThreadLocal.withInitial(ArrayList::new);
    static long seq = 0;
    static final IdentityHashMap<Object, String> ALLOC_IDS = new IdentityHashMap<>();
    static long allocNext = 1;

    /** Pushes/pops the innermost active frame (function id text). */
    public static void pushFrame(String functionId) {
        FRAMES.get().add(0, functionId);
    }

    public static void popFrame() {
        FRAMES.get().remove(0);
    }

    public static String framesText() {
        List<String> frames = FRAMES.get();
        return frames.isEmpty() ? "-" : String.join(",", frames);
    }

    // =========================================================================
    // Encoding
    // =========================================================================

    public static String esc(String s) {
        if (s == null) {
            return "";
        }
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '\\' -> out.append("\\\\");
                case '\n' -> out.append("\\n");
                case '\t' -> out.append("\\t");
                case '\r' -> out.append("\\r");
                case ';' -> out.append("\\u003b");
                case '|' -> out.append("\\u007c");
                default -> {
                    if (c < 0x20 || c == 0x7f) {
                        out.append(String.format("\\u%04x", (int) c));
                    } else {
                        out.append(c);
                    }
                }
            }
        }
        return out.toString();
    }

    /** The closed atom encoding (first-observation allocation ids). */
    public static String atom(Object v, String kind) {
        if (v == MISSING) {
            return "missing";
        }
        if (kind == null) {
            return "missing";
        }
        // The value's own variant wins over the declared kind: the closed
        // value model keeps the int/number variant through every typed
        // boundary (an int value admitted at a number-typed position stays
        // a Long, a number value admitted at an int-typed position stays a
        // Double) — exactly the oracle's atomOf.
        if (v instanceof Long longValue) {
            return "int:" + longValue.longValue();
        }
        if (v instanceof Double doubleValue) {
            double d = doubleValue.doubleValue();
            if (Double.isNaN(d)) {
                return "num:nan";
            }
            return "num:" + Double.toHexString(d);
        }
        switch (kind) {
            case "null" -> {
                return "null";
            }
            case "missing" -> {
                return "missing";
            }
            case "bool" -> {
                return "bool:" + v;
            }
            case "int" -> {
                return "int:" + v;
            }
            case "number" -> {
                double d = (Double) v;
                if (Double.isNaN(d)) {
                    return "num:nan";
                }
                return "num:" + Double.toHexString(d);
            }
            case "string" -> {
                return "str:" + esc((String) v);
            }
            case "err" -> {
                ErrorValue error = (ErrorValue) v;
                return "err:" + error.code + ":" + esc(error.message);
            }
            default -> {
                if (kind.startsWith("nullable:")) {
                    if (v == null) {
                        return "null";
                    }
                    return atom(v, kind.substring("nullable:".length()));
                }
                if (kind.equals("ref") || kind.equals("table") || kind.equals("array")
                        || kind.equals("function") || kind.equals("class")) {
                    return "ref:" + allocId(v);
                }
                return "missing";
            }
        }
    }

    static String allocId(Object heap) {
        String id = ALLOC_IDS.get(heap);
        if (id == null) {
            id = String.valueOf(allocNext++);
            ALLOC_IDS.put(heap, id);
        }
        return id;
    }

    /**
     * The raw read atom of the OPTIONAL_READ envelope: the value's
     * actual runtime kind — missing → "missing", null → "null", else
     * the actual kind's atom (a wrong-kind present value atomizes as its
     * own kind, exactly the oracle's publish). Heap values carry the
     * shared allocation-id namespace.
     */
    public static String rawAtom(Object v, String kind) {
        if (v == MISSING) {
            return "missing";
        }
        if (v == null) {
            return "null";
        }
        if (v instanceof Boolean) {
            return "bool:" + v;
        }
        if (v instanceof Long) {
            return "int:" + v;
        }
        if (v instanceof Double) {
            return atom(v, "number");
        }
        if (v instanceof String) {
            return "str:" + esc((String) v);
        }
        if (v instanceof ErrorValue error) {
            return "err:" + error.code + ":" + esc(error.message);
        }
        if (v instanceof Table || v instanceof Array || v instanceof FunctionValue
                || v instanceof Intrinsic || v instanceof ClassInstance) {
            return "ref:" + allocId(v);
        }
        return atom(v, kind);
    }

    /** The nested error text form. */
    public static String errtext(Throwable e) {
        if (e instanceof DealError deal) {
            return deal.code + ";" + esc(deal.msg) + ";" + (deal.origin == null ? "-"
                : deal.origin) + ";" + (deal.expected == null ? "-" : deal.expected) + ";"
                + (deal.actual == null ? "-" : deal.actual) + ";"
                + (deal.frames == null || deal.frames.isEmpty() ? "-" : deal.frames) + ";"
                + (deal.cause == null ? "-" : errtext(deal.cause));
        }
        return "E9999;" + esc(String.valueOf(e)) + ";-;-;-;-;-";
    }

    /**
     * The protocol-channel gate (ISSUE-0239 E10): the conformance
     * consumers keep the channel on (the default), while a production
     * artifact disables it at startup so no trace/effect record ever
     * reaches stderr from a production run.
     */
    private static volatile boolean traceEnabled = true;

    /**
     * Sets the protocol-channel gate. Production artifacts call this
     * with {@code false} before executing any operation; the conformance
     * harness never calls it, so its per-process default stays on.
     *
     * @param enabled whether the dedicated trace/effect channel is active
     */
    public static void setTraceEnabled(boolean enabled) {
        traceEnabled = enabled;
    }

    /** Emits one protocol trace line to the dedicated channel (stderr). */
    public static void ev(String module, String op, String phase, String kind,
                          String digest, String parent, List<String> inputs,
                          String output, String errtext) {
        if (!traceEnabled) {
            return;
        }
        StringBuilder line = new StringBuilder();
        line.append("T|").append(seq++).append('|').append(module).append('|').append(op)
            .append('|').append(phase).append('|').append(kind).append('|').append(digest)
            .append('|').append(parent == null ? "-" : parent);
        if (inputs != null) {
            for (String input : inputs) {
                line.append('|').append(input);
            }
        }
        if (output != null) {
            line.append("|=>").append(output);
        }
        if (errtext != null) {
            line.append("|!").append(errtext);
        }
        PrintStream err = new PrintStream(System.err, true, StandardCharsets.UTF_8);
        err.println(line);
    }

    /** Records one console effect (real stdout bytes + the protocol record). */
    public static void console(String text) {
        PrintStream out = new PrintStream(System.out, true, StandardCharsets.UTF_8);
        out.println(text);
        if (!traceEnabled) {
            return;
        }
        PrintStream err = new PrintStream(System.err, true, StandardCharsets.UTF_8);
        err.println("F|CONSOLE_WRITE|STDOUT|" + esc(text));
        err.flush();
    }

    /**
     * Records one console error effect. {@code CONSOLE_ERROR} appends the
     * exact scalar bytes plus one {@code \n} to {@code STDERR} — the
     * channel identity is part of the closed one-effect contract. The
     * STDERR channel shares the trace stream, so the trace protocol stays
     * decode-clean: trace mode publishes only the protocol record (the
     * effect's exact scalar text plus its channel), production mode (no
     * protocol) publishes the exact effect bytes.
     */
    public static void consoleError(String text) {
        PrintStream err = new PrintStream(System.err, true, StandardCharsets.UTF_8);
        if (!traceEnabled) {
            err.println(text);
            err.flush();
            return;
        }
        err.println("F|CONSOLE_WRITE|STDERR|" + esc(text));
        err.flush();
    }

    // =========================================================================
    // Boundary projections (the closed failure registry's exact templates)
    // =========================================================================

    public static DealError fail(String code, String msg, String origin, String expected,
                                 String actual) {
        return new DealError(code, msg, origin, expected, actual, framesText(), null);
    }

    /**
     * The actual runtime kind of one value for failure projections: the
     * value's own kind — missing → "missing", null → "null", else the
     * runtime type's canonical kind text (a wrong-kind value projects as
     * its own kind, never the declared static kind; the declared kind is
     * the fallback for carriers outside the closed value kinds).
     */
    public static String actualOf(String staticKind, Object v) {
        if (v == MISSING) {
            return "missing";
        }
        if (v == null) {
            return "null";
        }
        if (v instanceof Boolean) {
            return "boolean";
        }
        if (v instanceof Long) {
            return "int";
        }
        if (v instanceof Double) {
            return "number";
        }
        if (v instanceof String) {
            return "string";
        }
        if (v instanceof Table) {
            return "table";
        }
        if (v instanceof Array) {
            return "array";
        }
        if (v instanceof FunctionValue || v instanceof Intrinsic) {
            return "function";
        }
        if (v instanceof ErrorValue) {
            return "class:@builtin/Error";
        }
        if (v instanceof ClassInstance instance) {
            return "class:" + instance.classIdText();
        }
        return staticKind;
    }

    /**
     * The descriptor-kind boundary check over the closed descriptor texts
     * ({@code null|boolean|int|number|string|table|array(INNER)|
     * nullable(INNER)|function(PARAMS;RETURN)}): the pinned int ladder
     * (kind → NaN → infinity → fractional → E8004), the array element
     * cause chain (E8003), and the function-signature projection (E8010).
     */
    public static Object bcheck(String desc, String staticKind, Object v) {
        String actual = actualOf(staticKind, v);
        if ("null".equals(desc)) {
            if (v == null) {
                return v;
            }
            throw fail("E8001", "expected null, got " + actual, "-", "null", actual);
        }
        if ("boolean".equals(desc)) {
            if (v instanceof Boolean) {
                return v;
            }
            throw fail("E8001", "expected boolean, got " + actual, "-", "boolean", actual);
        }
        if ("int".equals(desc)) {
            if (v instanceof Long longValue) {
                return v;
            }
            if (v instanceof Double doubleValue) {
                double d = doubleValue;
                if (Double.isNaN(d)) {
                    throw fail("E8001", "expected int, got NaN", "-", "int", "NaN");
                }
                if (Double.isInfinite(d)) {
                    throw fail("E8001", "expected int, got infinity", "-", "int",
                        "infinity");
                }
                if (d != Math.rint(d)) {
                    throw fail("E8001", "expected int, got non-integer number", "-", "int",
                        "non-integer number");
                }
                if (d < -2147483648d || d > 2147483647d) {
                    throw fail("E8004", "int out of safe range", "-", "int", "number");
                }
                return d;
            }
            throw fail("E8001", "expected int, got " + actual, "-", "int", actual);
        }
        if ("number".equals(desc)) {
            if (v instanceof Double || v instanceof Long) {
                return v;
            }
            throw fail("E8001", "expected number, got " + actual, "-", "number", actual);
        }
        if ("string".equals(desc)) {
            if (v instanceof String) {
                return v;
            }
            throw fail("E8001", "expected string, got " + actual, "-", "string", actual);
        }
        if ("table".equals(desc)) {
            if (v instanceof Table) {
                return v;
            }
            throw fail("E8001", "expected table, got " + actual, "-", "table", actual);
        }
        if (desc.startsWith("@")) {
            if ("@/Error".equals(desc)) {
                // The builtin Error class (the err carrier): an Error
                // value passes unchanged.
                if (v instanceof ErrorValue) {
                    return v;
                }
                throw fail("E8001", "expected " + desc + ", got " + actual, "-", desc,
                    actual);
            }
            // A nominal class descriptor (E5): the canonical
            // @modulePath/ClassName identity text — the instance must
            // carry the identical tag.
            if (v instanceof ClassInstance instance
                    && desc.equals(instance.classIdText())) {
                return v;
            }
            throw fail("E8001", "expected " + desc + ", got " + actual, "-", desc,
                actual);
        }
        if (desc.startsWith("array(")) {
            if (v instanceof Array array) {
                String inner = desc.substring(6, desc.length() - 1);
                for (int i = 0; i < array.length; i++) {
                    Object elem = i < array.elements.size() ? array.elements.get(i)
                        : MISSING;
                    if (elem == null) {
                        elem = MISSING;
                    }
                    try {
                        bcheck(inner, elem == MISSING ? "missing" : inner, elem);
                    } catch (DealError leaf) {
                        throw fail("E8003", "array element " + (i + 1)
                            + " type mismatch", "-", inner,
                            actualOf(elem == MISSING ? "missing" : inner, elem));
                    }
                }
                return v;
            }
            throw fail("E8001", "expected array, got " + actual, "-", "array", actual);
        }
        if (desc.startsWith("nullable(")) {
            if (v == null || v == MISSING) {
                return null;
            }
            return bcheck(desc.substring(9, desc.length() - 1), staticKind, v);
        }
        if (desc.startsWith("function(")) {
            if (v instanceof FunctionValue function) {
                String carried = function.signature == null ? "" : function.signature;
                if (carried.equals(desc)) {
                    return v;
                }
                throw fail("E8010", "function signature mismatch: expected " + desc
                    + ", got " + carried, "-", desc, carried);
            }
            throw fail("E8001", "expected function, got " + actual, "-", "function",
                actual);
        }
        return v;
    }

    // =========================================================================
    // The D15 adapter invocation protocol (FUNCTION_ADAPT / CALLBACK_INVOKE)
    // =========================================================================

    /**
     * The adapter's source-signature check (D15): the resolved source
     * value's carried canonical spec text must equal the adapter's
     * recorded source signature; a mismatch is E8010
     * {@code FUNCTION_SIGNATURE} at the invoking op's origin with the
     * active frames (the check runs before any source-frame push).
     */
    public static Object fnCheck(Object v, String expected, String origin) {
        String carried = "";
        if (v instanceof FunctionValue function && function.spec != null) {
            carried = function.spec;
        }
        if (expected.equals(carried)) {
            return v;
        }
        throw fail("E8010", "function signature mismatch: expected " + expected
            + ", got " + carried, origin, expected, carried);
    }

    /**
     * The D15 adapter invocation: resolve the source per the closed
     * capture mode (VALUE retains, SHARED_CELL re-reads the generation
     * cell, REEVALUATE_THUNK re-executes the thunk), the source-signature
     * check, then the source invocation with the leading M arguments
     * only. A DEAL-body source pushes its function id onto the active
     * frames for the invocation (popped on every path); the identical
     * completion error propagates unchanged.
     */
    public static Object invokeAdapter(AdapterValue adapter, String origin, Object[] args) {
        Object source = adapterSource(adapter);
        fnCheck(source, adapter.sourceSpec, origin);
        Object[] leading = new Object[adapter.arity];
        System.arraycopy(args, 0, leading, 0, adapter.arity);
        FunctionValue function = (FunctionValue) source;
        boolean pushed = function.fid != null;
        if (pushed) {
            pushFrame(function.fid);
        }
        try {
            return function.fn.invoke(leading);
        } finally {
            if (pushed) {
                popFrame();
            }
        }
    }

    /**
     * The actual-kind atom of one host-supplied argument (the callback
     * dispatch surface): null/boolean/int/number/string by the runtime
     * carrier — identical to the semantic oracle's scripted-argument
     * atomization.
     */
    public static String hostAtom(Object v) {
        if (v == null) {
            return "null";
        }
        if (v instanceof Boolean bool) {
            return "bool:" + bool;
        }
        if (v instanceof Long longValue) {
            return "int:" + longValue;
        }
        if (v instanceof Integer intValue) {
            return "int:" + intValue;
        }
        if (v instanceof Double doubleValue) {
            return atom(doubleValue, "number");
        }
        if (v instanceof String string) {
            return "str:" + esc(string);
        }
        return "ref:" + allocId(v);
    }

    // =========================================================================
    // The D13 async machine (ASYNC_START / AWAIT)
    // =========================================================================

    /**
     * One async task record per canonical token identity: the token's
     * {@link CompletableFuture}, the body supplier for DEAL body tasks
     * (null for host operations), and the host operation label for host
     * operations (null for body tasks).
     */
    public static final class AsyncTask {
        public final long tokenId;
        public final String owner;
        public final CompletableFuture<Object> future;
        public final java.util.function.Supplier<Object> body;
        public final String hostLabel;

        AsyncTask(long tokenId, String owner, CompletableFuture<Object> future,
                  java.util.function.Supplier<Object> body, String hostLabel) {
            this.tokenId = tokenId;
            this.owner = owner;
            this.future = future;
            this.body = body;
            this.hostLabel = hostLabel;
        }
    }

    /** The run-local pending task queue (deterministic FIFO). */
    static final ArrayDeque<AsyncTask> PENDING = new ArrayDeque<>();

    /** The canonical-token task registry (one task per token identity). */
    static final Map<Long, AsyncTask> TASKS = new HashMap<>();

    /**
     * The run-local single-thread serial executor (E4): every DEAL body
     * task's future completes on this thread — never the JDK common pool
     * (FIFO determinism is pinned).
     */
    private static final ExecutorService SERIAL_EXECUTOR =
        Executors.newSingleThreadExecutor(runnable -> {
            Thread thread = new Thread(() -> {
                serialThread = Thread.currentThread();
                runnable.run();
            }, "deal-shared-async-serial");
            thread.setDaemon(true);
            return thread;
        });

    /** The serial executor's thread (set when it first runs). */
    private static volatile Thread serialThread;

    /**
     * The deterministic host seam of the async machine (E6/E7): the
     * scenario host adapter scripts every async host terminal — an async
     * host start (the bound operation label, or {@code null} for a bad
     * handle) and an async host completion (the returned value or the
     * thrown host error). Without a seam an async host operation is a
     * producer defect, never a silent projection.
     */
    public interface HostAsync {

        /** One async host completion terminal. */
        record HostCompletion(Object value, String thrownCode, String thrownMessage) {

            public HostCompletion {
                if ((value == null) == (thrownCode == null)) {
                    throw new IllegalArgumentException("exactly one of value/thrownCode "
                        + "must be present in an async host completion");
                }
            }
        }

        /**
         * One async host start: returns the operation label the returned
         * handle binds to, or {@code null} for a bad handle (the
         * {@code ASYNC_OPERATION_HANDLE} terminal check fails).
         *
         * @param module the owning host module; non-null
         * @param export the host export name; non-null
         * @param label  the deterministic operation label; non-null
         * @param args   the boundary-checked argument values; non-null
         * @return the bound label, or {@code null} for a bad handle
         */
        String startAsync(String module, String export, String label, Object[] args);

        /**
         * One async host completion of the operation label.
         *
         * @param label the operation label; non-null
         * @return the completion terminal
         */
        HostCompletion completeAsync(String label);
    }

    /** The scenario host adapter's scripted seam (null outside host drives). */
    public static volatile HostAsync HOST_ASYNC;

    /** Registers one DEAL body task: its future completes on the serial executor at drain. */
    public static void startBodyTask(long tokenId, String owner,
                                     java.util.function.Supplier<Object> body) {
        AsyncTask task = new AsyncTask(tokenId, owner, new CompletableFuture<>(), body, null);
        TASKS.put(tokenId, task);
        PENDING.add(task);
    }

    /** Registers one async host operation: its future completes through the host seam. */
    public static void startHostTask(long tokenId, String label) {
        AsyncTask task = new AsyncTask(tokenId, "HOST_OPERATION",
            new CompletableFuture<>(), null, label);
        TASKS.put(tokenId, task);
        PENDING.add(task);
    }

    /**
     * The deterministic FIFO drain (the oracle's {@code drainReadyTasks}):
     * every pending DEAL body task completes on the run-local single
     * thread serial executor in submission order. A body that runs an
     * inner {@code AWAIT} already executes on the serial thread — its
     * inner drain runs the nested bodies inline on that same serial
     * thread (still FIFO, never a self-join deadlock, never the common
     * pool). Host operations complete only at their own {@code AWAIT}
     * through the seam.
     */
    public static void drainTasks() {
        while (!PENDING.isEmpty()) {
            AsyncTask task = PENDING.poll();
            if (task.future.isDone() || task.body == null) {
                continue;
            }
            if (Thread.currentThread() == serialThread) {
                // A nested drain inside a task body: the serial thread
                // runs the nested body inline (serial FIFO preserved).
                completeTask(task);
                continue;
            }
            // The body runs on the serial executor with the drainer's
            // active frames (the failure snapshots inside the body carry
            // the awaiting context's frames exactly like the oracle).
            List<String> frames = new ArrayList<>(FRAMES.get());
            Future<?> job = SERIAL_EXECUTOR.submit(() -> {
                List<String> saved = FRAMES.get();
                FRAMES.set(new ArrayList<>(frames));
                try {
                    completeTask(task);
                } finally {
                    FRAMES.set(saved);
                }
            });
            try {
                job.get();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                throw new IllegalStateException("the serial executor drain was interrupted",
                    interrupted);
            } catch (ExecutionException failed) {
                throw new IllegalStateException("the serial executor drain failed",
                    failed.getCause());
            }
        }
    }

    /** Completes one body task's future with its value or its identical error. */
    private static void completeTask(AsyncTask task) {
        try {
            task.future.complete(task.body.get());
        } catch (Throwable thrown) {
            task.future.completeExceptionally(thrown);
        }
    }

    /**
     * AWAIT — the completion position (D13 step 6): the deterministic
     * FIFO drain first, then the token's completion. A pending host
     * operation completes through the seam (the ordered
     * {@code ASYNC_COMPLETE_RETURN}/{@code ASYNC_COMPLETE_THROW}
     * effects); a failed operation rethrows the identical error — never a
     * re-check or a synthesized copy — and a completed value is returned
     * for the single {@code ASYNC_COMPLETION} boundary at the await site.
     *
     * @param tokenId     the canonical token identity; non-negative
     * @param awaitOrigin the {@code AWAIT} op's origin text (the origin
     *                    of a host-thrown completion error)
     * @return the completion value
     */
    public static Object awaitTask(long tokenId, String awaitOrigin) {
        drainTasks();
        AsyncTask task = TASKS.get(tokenId);
        if (task == null) {
            throw new IllegalStateException("AWAIT consumes an unbound token " + tokenId
                + " (producer defect)");
        }
        if (task.hostLabel != null && !task.future.isDone()) {
            if (HOST_ASYNC == null) {
                throw new IllegalStateException("an async host completion has no "
                    + "deterministic host seam (the scenario host drives it)");
            }
            HostAsync.HostCompletion completion = HOST_ASYNC.completeAsync(task.hostLabel);
            if (completion.thrownCode() == null) {
                effect("ASYNC_COMPLETE_RETURN", task.hostLabel + "="
                    + hostAtom(completion.value()));
                task.future.complete(completion.value());
            } else {
                effect("ASYNC_COMPLETE_THROW", task.hostLabel + "!"
                    + completion.thrownCode());
                task.future.completeExceptionally(new DealError(completion.thrownCode(),
                    completion.thrownMessage(), awaitOrigin, null, null, framesText(),
                    null));
            }
        }
        try {
            return task.future.join();
        } catch (CompletionException completion) {
            Throwable cause = completion.getCause();
            if (cause instanceof DealError dealError) {
                throw dealError; // the identical error — never re-checked or copied
            }
            if (cause instanceof RuntimeException runtime) {
                throw runtime;
            }
            throw new IllegalStateException("the async task " + tokenId + " failed with "
                + cause, cause);
        }
    }

    /** One ordered effect record of the closed effect protocol (F| lines). */
    public static void effect(String kind, String text) {
        if (!traceEnabled) {
            return;
        }
        PrintStream err = new PrintStream(System.err, true, StandardCharsets.UTF_8);
        err.println("F|" + kind + "|-|" + esc(text));
    }

    /**
     * The adapter's source resolution per the closed capture mode (the
     * async adapter task's D15 protocol half): VALUE retains, SHARED_CELL
     * re-reads the generation cell, REEVALUATE_THUNK re-executes the
     * thunk.
     */
    public static Object adapterSource(AdapterValue adapter) {
        if (adapter.mode == 0) {
            return adapter.value;
        }
        if (adapter.mode == 1) {
            return adapter.cell[0];
        }
        return adapter.thunk.invoke(new Object[0]);
    }

    // =========================================================================
    // The MODULE_INIT state machine (E8)
    // =========================================================================

    /**
     * The closed module-init lifecycle of one module: unrecorded is
     * {@code UNINITIALIZED}, {@code INITIALIZING} during the payload
     * walk, {@code INITIALIZED} after a completed walk, and
     * {@code FAILED} after a failing walk (no export publication).
     */
    public enum ModuleInitState { INITIALIZING, INITIALIZED, FAILED }

    /** The per-module lifecycle records of one run (keyed by module path). */
    static final Map<String, ModuleInitState> MODULE_STATES = new LinkedHashMap<>();

    /**
     * The MODULE_INIT envelope's state gate: {@code true} when the module
     * is still {@code UNINITIALIZED} (the walk runs), {@code false} when
     * it is already {@code INITIALIZED} (the once-after-dependencies
     * skip). A re-entrant ({@code INITIALIZING}) or post-failure
     * ({@code FAILED}) execution is a producer defect, never a silent
     * re-run.
     *
     * @param module the module path; non-null
     * @return whether the init walk runs
     */
    public static boolean moduleInitNeeded(String module) {
        ModuleInitState state = MODULE_STATES.get(module);
        if (state == null) {
            return true;
        }
        if (state == ModuleInitState.INITIALIZED) {
            return false;
        }
        throw new IllegalStateException("a second MODULE_INIT of module " + module
            + " after a re-entrant or failed init (the frontend rejects import "
            + "cycles with E2005) — a producer defect, never a silent re-run");
    }

    /** The {@code UNINITIALIZED -> INITIALIZING} transition. */
    public static void moduleInitBegin(String module) {
        MODULE_STATES.put(module, ModuleInitState.INITIALIZING);
    }

    /** The {@code INITIALIZING -> INITIALIZED} transition (completed walk). */
    public static void moduleInitComplete(String module) {
        MODULE_STATES.put(module, ModuleInitState.INITIALIZED);
    }

    /** The {@code INITIALIZING -> FAILED(error)} transition (no export publication). */
    public static void moduleInitFail(String module) {
        MODULE_STATES.put(module, ModuleInitState.FAILED);
    }

    // =========================================================================
    // The closed B-D2 comparison table (native operators)
    // =========================================================================

    public static boolean cmp(String selector, String kindL, Object l, String kindR,
                              Object r, String side) {
        boolean leftNullish = l == null || l == MISSING;
        boolean rightNullish = r == null || r == MISSING;
        if (leftNullish || rightNullish) {
            if ("NULLABLE_NULL_EQ".equals(selector)) {
                Object named = "LEFT".equals(side) ? l : r;
                return named == null || named == MISSING;
            }
            if ("NULLABLE_NULL_NE".equals(selector)) {
                Object named = "LEFT".equals(side) ? l : r;
                return !(named == null || named == MISSING);
            }
            boolean both = leftNullish && rightNullish;
            if (selector.endsWith("_EQ")) {
                return both;
            }
            if (selector.endsWith("_NE")) {
                return !both;
            }
            return false;
        }
        switch (selector) {
            case "INT32_EQ" -> {
                return ((Long) l).longValue() == ((Long) r).longValue();
            }
            case "INT32_NE" -> {
                return ((Long) l).longValue() != ((Long) r).longValue();
            }
            case "INT32_LT" -> {
                return ((Long) l).longValue() < ((Long) r).longValue();
            }
            case "INT32_LE" -> {
                return ((Long) l).longValue() <= ((Long) r).longValue();
            }
            case "INT32_GT" -> {
                return ((Long) l).longValue() > ((Long) r).longValue();
            }
            case "INT32_GE" -> {
                return ((Long) l).longValue() >= ((Long) r).longValue();
            }
            case "NUMBER_EQ" -> {
                return ((Number) l).doubleValue() == ((Number) r).doubleValue();
            }
            case "NUMBER_NE" -> {
                return ((Number) l).doubleValue() != ((Number) r).doubleValue();
            }
            case "NUMBER_LT" -> {
                return ((Number) l).doubleValue() < ((Number) r).doubleValue();
            }
            case "NUMBER_LE" -> {
                return ((Number) l).doubleValue() <= ((Number) r).doubleValue();
            }
            case "NUMBER_GT" -> {
                return ((Number) l).doubleValue() > ((Number) r).doubleValue();
            }
            case "NUMBER_GE" -> {
                return ((Number) l).doubleValue() >= ((Number) r).doubleValue();
            }
            case "STRING_EQ" -> {
                return ((String) l).equals((String) r);
            }
            case "STRING_NE" -> {
                return !((String) l).equals((String) r);
            }
            case "STRING_LT" -> {
                return codePointCompare((String) l, (String) r) < 0;
            }
            case "STRING_LE" -> {
                return codePointCompare((String) l, (String) r) <= 0;
            }
            case "STRING_GT" -> {
                return codePointCompare((String) l, (String) r) > 0;
            }
            case "STRING_GE" -> {
                return codePointCompare((String) l, (String) r) >= 0;
            }
            case "BOOLEAN_EQ" -> {
                return ((Boolean) l).equals((Boolean) r);
            }
            case "BOOLEAN_NE" -> {
                return !((Boolean) l).equals((Boolean) r);
            }
            case "NULL_EQ" -> {
                return true;
            }
            case "NULL_NE" -> {
                return false;
            }
            case "NULLABLE_EQ" -> {
                return nullableEquals(kindL, l, kindR, r);
            }
            case "NULLABLE_NE" -> {
                return !nullableEquals(kindL, l, kindR, r);
            }
            case "REFERENCE_EQ" -> {
                return l == r;
            }
            case "REFERENCE_NE" -> {
                return l != r;
            }
            default -> {
                return false;
            }
        }
    }

    /** Unicode-scalar (code point) order — never String.compareTo. */
    static int codePointCompare(String left, String right) {
        int[] leftPoints = left.codePoints().toArray();
        int[] rightPoints = right.codePoints().toArray();
        int n = Math.min(leftPoints.length, rightPoints.length);
        for (int i = 0; i < n; i++) {
            if (leftPoints[i] != rightPoints[i]) {
                return Integer.compare(leftPoints[i], rightPoints[i]);
            }
        }
        return Integer.compare(leftPoints.length, rightPoints.length);
    }

    static boolean nullableEquals(String kindL, Object l, String kindR, Object r) {
        // Inner equality by the value rules (both non-null here).
        if (l instanceof Long left && r instanceof Long right) {
            return left.longValue() == right.longValue();
        }
        if (l instanceof Number left && r instanceof Number right) {
            return left.doubleValue() == right.doubleValue();
        }
        if (l instanceof String left && r instanceof String right) {
            return left.equals(right);
        }
        if (l instanceof Boolean left && r instanceof Boolean right) {
            return left.equals(right);
        }
        return l == r; // reference identity for heap values
    }

    // =========================================================================
    // The closed int32/number arithmetic rows
    // =========================================================================

    public static Object unary(String selector, Object v, String opKey, String digest,
                               String parent, String origin) {
        if ("BOOL_NOT".equals(selector)) {
            return !((Boolean) v);
        }
        if ("INT32_NEG".equals(selector)) {
            long result = -((Long) v).longValue();
            return int32Result(result, opKey, digest, parent, origin, "UNARY");
        }
        return -((Number) v).doubleValue();
    }

    public static Object arith(String selector, Object l, Object r, String opKey,
                               String digest, String parent, String origin) {
        switch (selector) {
            case "INT32_ADD" -> {
                return int32Result(((Long) l) + ((Long) r), opKey, digest, parent, origin,
                    "BINARY");
            }
            case "INT32_SUB" -> {
                return int32Result(((Long) l) - ((Long) r), opKey, digest, parent, origin,
                    "BINARY");
            }
            case "INT32_MUL" -> {
                return int32Result(((Long) l) * ((Long) r), opKey, digest, parent, origin,
                    "BINARY");
            }
            case "INT32_DIV_TRUNC" -> {
                long divisor = ((Long) r);
                if (divisor == 0) {
                    raise(opKey, digest, parent, origin, "BINARY", "E8005",
                        "integer division by zero", null, null);
                }
                return int32Result(((Long) l) / divisor, opKey, digest, parent, origin,
                    "BINARY");
            }
            case "INT32_MOD_TRUNC" -> {
                long divisor = ((Long) r);
                if (divisor == 0) {
                    raise(opKey, digest, parent, origin, "BINARY", "E8005",
                        "integer division by zero", null, null);
                }
                return int32Result(((Long) l) % divisor, opKey, digest, parent, origin,
                    "BINARY");
            }
            case "INT32_POW" -> {
                long exponent = ((Long) r);
                if (exponent < 0) {
                    raise(opKey, digest, parent, origin, "BINARY", "E8006",
                        "integer exponent must be non-negative", null, null);
                }
                long result = 1;
                try {
                    for (long i = 0; i < exponent; i++) {
                        result = Math.multiplyExact(result, ((Long) l));
                    }
                } catch (ArithmeticException overflow) {
                    raise(opKey, digest, parent, origin, "BINARY", "E8004",
                        "int out of safe range", null, null);
                }
                return int32Result(result, opKey, digest, parent, origin, "BINARY");
            }
            case "NUMBER_ADD" -> {
                return ((Number) l).doubleValue() + ((Number) r).doubleValue();
            }
            case "NUMBER_SUB" -> {
                return ((Number) l).doubleValue() - ((Number) r).doubleValue();
            }
            case "NUMBER_MUL" -> {
                return ((Number) l).doubleValue() * ((Number) r).doubleValue();
            }
            case "NUMBER_DIV_IEEE" -> {
                return ((Number) l).doubleValue() / ((Number) r).doubleValue();
            }
            case "NUMBER_MOD_FLOOR" -> {
                double a = ((Number) l).doubleValue();
                double b = ((Number) r).doubleValue();
                return a - Math.floor(a / b) * b;
            }
            case "NUMBER_POW_IEEE" -> {
                return Math.pow(((Number) l).doubleValue(), ((Number) r).doubleValue());
            }
            default -> {
                return 0L;
            }
        }
    }

    static Object int32Result(long result, String opKey, String digest, String parent,
                              String origin, String kind) {
        if (result < Integer.MIN_VALUE || result > Integer.MAX_VALUE) {
            raise(opKey, digest, parent, origin, kind, "E8004", "int out of safe range", null,
                null);
        }
        return result;
    }

    static void raise(String opKey, String digest, String parent, String origin,
                      String kind, String code, String msg, String expected, String actual) {
        DealError e = fail(code, msg, origin, expected, actual);
        ev(currentModule(), opKey, "FAILURE", kind, digest, parent, List.of(), null,
            errtext(e));
        throw e;
    }

    // =========================================================================
    // The closed stdlib algorithms (STDLIB_CALL realization)
    // =========================================================================

    /**
     * An internal stdlib algorithm failure: the exact registry-row
     * projection facts, converted by {@link #stdlib} into the op FAILURE
     * event plus the {@link DealError} at the call origin (the same
     * conversion the arithmetic helpers perform).
     */
    private static final class StdlibFailure extends RuntimeException {

        private static final long serialVersionUID = 1L;

        final String code;
        final String msg;
        final String expected;
        final String actual;

        StdlibFailure(String code, String msg, String expected, String actual) {
            super(msg);
            this.code = code;
            this.msg = msg;
            this.expected = expected;
            this.actual = actual;
        }
    }

    /**
     * The single in-target realization of the closed 20-operation stdlib
     * table: the parameter boundaries already ran (the emitter emits the
     * {@code STDLIB_PARAMETER} children), so the algorithm receives the
     * boundary-admitted carriers — a string parameter is a valid scalar
     * {@link String}, an int parameter is a {@link Long} or an in-range
     * integral {@link Double}, a number parameter is a {@link Double} or
     * a {@link Long}, and a table parameter is a {@link Table}. A
     * failure raises the op FAILURE event and the {@link DealError}
     * through {@link #raise} with the exact closed projections —
     * {@code INT32_RESULT} E8004 {@code int out of safe range},
     * {@code SQRT_NEGATIVE} E8001 {@code sqrt of negative number} (actual
     * = the canonical hex float), {@code JSON_PARSE_SYNTAX} E8001
     * {@code JSON parse error at position {oneBasedByteOffset}:
     * {reason}}, and {@code JSON_TO_ERROR} E8001
     * {@code unsupported type for JSON encoding: {actual}} with the pinned
     * expected text {@code string, number, boolean, or table} and the
     * canonical actual-kind token —
     * at the {@code STDLIB_CALL} call origin with the active frames.
     * Console ids are emitted inline by the emitters (the byte-exact
     * one-effect contract), never through this surface.
     */
    public static Object stdlib(String fn, String opKey, String digest, String parent,
                                String origin, Object[] args) {
        try {
            switch (fn) {
                case "STRING_LENGTH" -> {
                    String text = (String) args[0];
                    long count = text.codePointCount(0, text.length());
                    if (count > Integer.MAX_VALUE) {
                        throw new StdlibFailure("E8004", "int out of safe range", null, null);
                    }
                    return Long.valueOf(count);
                }
                case "STRING_SUBSTRING" -> {
                    int[] codePoints = ((String) args[0]).codePoints().toArray();
                    long start = longOf(args[1]);
                    long end = longOf(args[2]);
                    int lo = (int) Math.max(0, start);
                    int hi = (int) Math.min(Math.max(0, end), codePoints.length);
                    if (lo >= hi) {
                        return "";
                    }
                    return new String(codePoints, lo, hi - lo);
                }
                case "STRING_CONTAINS" -> {
                    return indexOfSubsequence(codePointsOf((String) args[0]),
                        codePointsOf((String) args[1]), 0) >= 0;
                }
                case "STRING_STARTS_WITH" -> {
                    int[] input = codePointsOf((String) args[0]);
                    int[] part = codePointsOf((String) args[1]);
                    return part.length <= input.length && matchAt(input, part, 0);
                }
                case "STRING_ENDS_WITH" -> {
                    int[] input = codePointsOf((String) args[0]);
                    int[] part = codePointsOf((String) args[1]);
                    return part.length <= input.length
                        && matchAt(input, part, input.length - part.length);
                }
                case "STRING_REPLACE" -> {
                    int[] input = codePointsOf((String) args[0]);
                    int[] from = codePointsOf((String) args[1]);
                    int[] to = codePointsOf((String) args[2]);
                    if (from.length == 0) {
                        return args[0];
                    }
                    StringBuilder result = new StringBuilder();
                    int cursor = 0;
                    while (cursor <= input.length - from.length) {
                        if (matchAt(input, from, cursor)) {
                            appendCodePoints(result, to);
                            cursor += from.length;
                        } else {
                            result.appendCodePoint(input[cursor]);
                            cursor++;
                        }
                    }
                    for (int i = cursor; i < input.length; i++) {
                        result.appendCodePoint(input[i]);
                    }
                    return result.toString();
                }
                case "STRING_SPLIT" -> {
                    int[] input = codePointsOf((String) args[0]);
                    int[] separator = codePointsOf((String) args[1]);
                    if (input.length == 0) {
                        return new Array(0);
                    }
                    if (separator.length == 0) {
                        Array singles = new Array(input.length);
                        for (int codePoint : input) {
                            singles.elements.add(new String(
                                new int[] {codePoint}, 0, 1));
                        }
                        return singles;
                    }
                    Array parts = new Array(0);
                    int cursor = 0;
                    int occurrence;
                    while ((occurrence = indexOfSubsequence(input, separator, cursor))
                            >= 0) {
                        parts.elements.add(new String(input, cursor, occurrence - cursor));
                        parts.length++;
                        cursor = occurrence + separator.length;
                    }
                    parts.elements.add(new String(input, cursor, input.length - cursor));
                    parts.length++;
                    return parts;
                }
                case "STRING_TRIM" -> {
                    int[] codePoints = codePointsOf((String) args[0]);
                    int first = 0;
                    while (first < codePoints.length && isTrimScalar(codePoints[first])) {
                        first++;
                    }
                    int last = codePoints.length;
                    while (last > first && isTrimScalar(codePoints[last - 1])) {
                        last--;
                    }
                    return new String(codePoints, first, last - first);
                }
                case "TABLE_KEYS" -> {
                    Table table = (Table) args[0];
                    Array keys = new Array(table.entries.size());
                    for (String key : table.entries.keySet()) {
                        keys.elements.add(key);
                    }
                    return keys;
                }
                case "JSON_PARSE" -> {
                    return jsonParse((String) args[0]);
                }
                case "JSON_STRINGIFY" -> {
                    Table root = (Table) args[0];
                    StringBuilder out = new StringBuilder();
                    java.util.Set<Object> path =
                        java.util.Collections.newSetFromMap(new IdentityHashMap<>());
                    stringifyTable(out, root, path);
                    return out.toString();
                }
                case "MATH_FLOOR" -> {
                    return Math.floor(numberOf(args[0]));
                }
                case "MATH_CEIL" -> {
                    return Math.ceil(numberOf(args[0]));
                }
                case "MATH_SQRT" -> {
                    double value = numberOf(args[0]);
                    if (value < 0) {
                        throw new StdlibFailure("E8001", "sqrt of negative number", null,
                            Double.toHexString(value));
                    }
                    return Math.sqrt(value);
                }
                case "MATH_ABS_INT" -> {
                    long value = longOf(args[0]);
                    long absolute = value < 0 ? -value : value;
                    if (absolute > Integer.MAX_VALUE) {
                        throw new StdlibFailure("E8004", "int out of safe range", null, null);
                    }
                    return Long.valueOf(absolute);
                }
                case "MATH_ABS_NUMBER" -> {
                    return Math.abs(numberOf(args[0]));
                }
                case "MATH_MIN_INT" -> {
                    return Long.valueOf(Math.min(longOf(args[0]), longOf(args[1])));
                }
                case "MATH_MAX_INT" -> {
                    return Long.valueOf(Math.max(longOf(args[0]), longOf(args[1])));
                }
                default -> throw new StdlibFailure("E8001",
                    "unknown stdlib call " + fn, null, null);
            }
        } catch (StdlibFailure failure) {
            raise(opKey, digest, parent, origin, "STDLIB_CALL", failure.code, failure.msg,
                failure.expected, failure.actual);
            return null; // unreachable: raise throws
        }
    }

    /** An int parameter carrier: a Long or an in-range integral Double (unchanged). */
    private static long longOf(Object value) {
        if (value instanceof Long longValue) {
            return longValue.longValue();
        }
        return ((Double) value).longValue();
    }

    /**
     * The normalized index/length view of one runtime value: a Long or an
     * integral Double (the closed value model's variant tolerance — an
     * index value admitted at an int-typed position keeps its boxed
     * Double, so the normalized slot never casts it blind).
     */
    public static long indexOf(Object value) {
        return longOf(value);
    }

    /** A number parameter carrier: a Double or a Long (int → double is exact). */
    private static double numberOf(Object value) {
        return ((Number) value).doubleValue();
    }

    /** The closed trim set: U+0009-U+000D and U+0020, exactly. */
    private static boolean isTrimScalar(int codePoint) {
        return (codePoint >= 0x09 && codePoint <= 0x0D) || codePoint == 0x20;
    }

    /** The code points of a scalar-valid string in scalar order. */
    private static int[] codePointsOf(String text) {
        return text.codePoints().toArray();
    }

    /** True iff {@code needle} occurs at {@code offset} of {@code haystack}. */
    private static boolean matchAt(int[] haystack, int[] needle, int offset) {
        for (int i = 0; i < needle.length; i++) {
            if (haystack[offset + i] != needle[i]) {
                return false;
            }
        }
        return true;
    }

    /**
     * The first occurrence of {@code needle} in {@code haystack} at or
     * after {@code fromIndex}, or {@code -1} — a literal scalar
     * subsequence search.
     */
    private static int indexOfSubsequence(int[] haystack, int[] needle, int fromIndex) {
        if (needle.length == 0) {
            return fromIndex <= haystack.length ? fromIndex : -1;
        }
        for (int i = Math.max(0, fromIndex); i + needle.length <= haystack.length; i++) {
            if (matchAt(haystack, needle, i)) {
                return i;
            }
        }
        return -1;
    }

    /** Appends code points to the builder in order. */
    private static void appendCodePoints(StringBuilder builder, int[] codePoints) {
        for (int codePoint : codePoints) {
            builder.appendCodePoint(codePoint);
        }
    }

    // =========================================================================
    // The RFC-8259 JSON reader (JSON_PARSE realization)
    // =========================================================================

    /** The stable parse defect classifications ({reason} texts). */
    private static final String REASON_UNEXPECTED_CHARACTER = "unexpected character";
    private static final String REASON_UNTERMINATED_STRING = "unterminated string";
    private static final String REASON_UNTERMINATED_OBJECT = "unterminated object";
    private static final String REASON_UNTERMINATED_ARRAY = "unterminated array";
    private static final String REASON_INVALID_ESCAPE = "invalid escape";
    private static final String REASON_UNPAIRED_SURROGATE_ESCAPE = "unpaired surrogate escape";
    private static final String REASON_INVALID_NUMBER = "invalid number";
    private static final String REASON_LEADING_ZERO = "leading zero";
    private static final String REASON_MISSING_KEY = "missing key";
    private static final String REASON_MISSING_COLON = "missing colon";
    private static final String REASON_MISSING_COMMA = "missing comma";
    private static final String REASON_TRAILING_CONTENT = "trailing content";
    private static final String REASON_UNEXPECTED_END = "unexpected end of input";

    /** The internal parse failure: the defect class and its 1-based UTF-8 byte offset. */
    private static final class JsonParseFailure extends RuntimeException {

        private static final long serialVersionUID = 1L;

        final String reason;
        final long oneBasedByteOffset;

        JsonParseFailure(String reason, long oneBasedByteOffset) {
            super(reason + " at byte " + oneBasedByteOffset);
            this.reason = reason;
            this.oneBasedByteOffset = oneBasedByteOffset;
        }
    }

    /**
     * The RFC-8259 recursive-descent reader over the input's code points,
     * tracking the 1-based UTF-8 byte offset of the current scan position:
     * object order follows text, duplicate keys keep the last value and
     * the first position, a signed32 integer lexical form becomes a
     * {@link Long} ({@code -0} normalized to {@code 0}) and every other
     * numeric form becomes a {@link Double}.
     */
    private static final class JsonReader {

        private final int[] codePoints;
        private int position;
        private long bytesConsumed;

        JsonReader(int[] codePoints) {
            this.codePoints = codePoints;
        }

        boolean atEnd() {
            return position >= codePoints.length;
        }

        int peek() {
            return position < codePoints.length ? codePoints[position] : -1;
        }

        void advance() {
            bytesConsumed += utf8Length(codePoints[position]);
            position++;
        }

        long offsetOfCurrent() {
            return bytesConsumed + 1;
        }

        JsonParseFailure failure(String reason) {
            return new JsonParseFailure(reason, offsetOfCurrent());
        }

        void skipWs() {
            while (!atEnd() && isWs(peek())) {
                advance();
            }
        }

        Object parseValue() {
            if (atEnd()) {
                throw failure(REASON_UNEXPECTED_END);
            }
            int c = peek();
            switch (c) {
                case '{' -> {
                    return parseObject();
                }
                case '[' -> {
                    return parseArray();
                }
                case '"' -> {
                    return parseString();
                }
                case 't' -> {
                    return parseLiteral("true", Boolean.TRUE);
                }
                case 'f' -> {
                    return parseLiteral("false", Boolean.FALSE);
                }
                case 'n' -> {
                    return parseLiteral("null", null);
                }
                default -> {
                    if (c == '-' || (c >= '0' && c <= '9')) {
                        return parseNumber();
                    }
                    throw failure(REASON_UNEXPECTED_CHARACTER);
                }
            }
        }

        Object parseLiteral(String word, Object value) {
            for (int i = 0; i < word.length(); i++) {
                if (atEnd()) {
                    throw failure(REASON_UNEXPECTED_END);
                }
                if (peek() != word.codePointAt(i)) {
                    throw failure(REASON_UNEXPECTED_CHARACTER);
                }
                advance();
            }
            return value;
        }

        Table parseObject() {
            advance(); // '{'
            Table table = new Table();
            skipWs();
            if (!atEnd() && peek() == '}') {
                advance();
                return table;
            }
            while (true) {
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNEXPECTED_END);
                }
                if (peek() != '"') {
                    throw failure(REASON_MISSING_KEY);
                }
                String key = parseString();
                skipWs();
                if (atEnd() || peek() != ':') {
                    throw failure(REASON_MISSING_COLON);
                }
                advance(); // ':'
                skipWs();
                Object value = parseValue();
                // Duplicate keys keep the last value and the first
                // position: LinkedHashMap.put replaces in place and
                // appends only new keys (the Table order contract).
                table.write(key, value);
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNTERMINATED_OBJECT);
                }
                int c = peek();
                if (c == ',') {
                    advance();
                    continue;
                }
                if (c == '}') {
                    advance();
                    return table;
                }
                throw failure(REASON_MISSING_COMMA);
            }
        }

        Array parseArray() {
            advance(); // '['
            Array array = new Array(0);
            skipWs();
            if (!atEnd() && peek() == ']') {
                advance();
                return array;
            }
            while (true) {
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNEXPECTED_END);
                }
                array.elements.add(parseValue());
                array.length++;
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNTERMINATED_ARRAY);
                }
                int c = peek();
                if (c == ',') {
                    advance();
                    continue;
                }
                if (c == ']') {
                    advance();
                    return array;
                }
                throw failure(REASON_MISSING_COMMA);
            }
        }

        String parseString() {
            advance(); // '"'
            StringBuilder result = new StringBuilder();
            while (true) {
                if (atEnd()) {
                    throw failure(REASON_UNTERMINATED_STRING);
                }
                int c = peek();
                if (c == '"') {
                    advance();
                    return result.toString();
                }
                if (c == '\\') {
                    advance(); // backslash
                    if (atEnd()) {
                        throw failure(REASON_UNTERMINATED_STRING);
                    }
                    int escaped = peek();
                    switch (escaped) {
                        case '"' -> {
                            advance();
                            result.append('"');
                        }
                        case '\\' -> {
                            advance();
                            result.append('\\');
                        }
                        case '/' -> {
                            advance();
                            result.append('/');
                        }
                        case 'b' -> {
                            advance();
                            result.append('\b');
                        }
                        case 'f' -> {
                            advance();
                            result.append('\f');
                        }
                        case 'n' -> {
                            advance();
                            result.append('\n');
                        }
                        case 'r' -> {
                            advance();
                            result.append('\r');
                        }
                        case 't' -> {
                            advance();
                            result.append('\t');
                        }
                        case 'u' -> {
                            advance(); // 'u'
                            int codePoint = parseHex4();
                            if (Character.isHighSurrogate((char) codePoint)) {
                                // A high surrogate must pair with a
                                // following a four-hex-digit low surrogate escape.
                                if (atEnd() || peek() != '\\') {
                                    throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                                }
                                advance(); // backslash
                                if (atEnd() || peek() != 'u') {
                                    throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                                }
                                advance(); // 'u'
                                int low = parseHex4();
                                if (!Character.isLowSurrogate((char) low)) {
                                    throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                                }
                                result.appendCodePoint(
                                    Character.toCodePoint((char) codePoint, (char) low));
                            } else if (Character.isLowSurrogate((char) codePoint)) {
                                throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                            } else {
                                result.appendCodePoint(codePoint);
                            }
                        }
                        default -> throw failure(REASON_INVALID_ESCAPE);
                    }
                } else if (c < 0x20) {
                    // A raw control character is never allowed unescaped.
                    throw failure(REASON_UNEXPECTED_CHARACTER);
                } else {
                    advance();
                    result.appendCodePoint(c);
                }
            }
        }

        /** Exactly four hex digits; a non-hex digit or end of input is an invalid escape. */
        int parseHex4() {
            int value = 0;
            for (int i = 0; i < 4; i++) {
                if (atEnd()) {
                    throw failure(REASON_INVALID_ESCAPE);
                }
                int digit = hexDigit(peek());
                if (digit < 0) {
                    throw failure(REASON_INVALID_ESCAPE);
                }
                advance();
                value = value * 16 + digit;
            }
            return value;
        }

        Object parseNumber() {
            int start = position;
            boolean negative = false;
            if (peek() == '-') {
                negative = true;
                advance();
            }
            if (atEnd()) {
                throw failure(REASON_INVALID_NUMBER);
            }
            int c = peek();
            if (c < '0' || c > '9') {
                throw failure(REASON_INVALID_NUMBER);
            }
            boolean integerForm = true;
            if (c == '0') {
                advance();
                if (!atEnd() && isDigit(peek())) {
                    throw failure(REASON_LEADING_ZERO);
                }
            } else {
                advance();
                while (!atEnd() && isDigit(peek())) {
                    advance();
                }
            }
            if (!atEnd() && peek() == '.') {
                integerForm = false;
                advance();
                if (atEnd() || !isDigit(peek())) {
                    throw failure(REASON_INVALID_NUMBER);
                }
                while (!atEnd() && isDigit(peek())) {
                    advance();
                }
            }
            if (!atEnd() && (peek() == 'e' || peek() == 'E')) {
                integerForm = false;
                advance();
                if (!atEnd() && (peek() == '+' || peek() == '-')) {
                    advance();
                }
                if (atEnd() || !isDigit(peek())) {
                    throw failure(REASON_INVALID_NUMBER);
                }
                while (!atEnd() && isDigit(peek())) {
                    advance();
                }
            }
            String text = new String(codePoints, start, position - start);
            if (integerForm) {
                int digitsStart = start + (negative ? 1 : 0);
                int significantStart = digitsStart;
                while (significantStart < position && codePoints[significantStart] == '0') {
                    significantStart++;
                }
                int significantLength = Math.max(1, position - significantStart);
                boolean outOfRange;
                if (significantLength > 10) {
                    outOfRange = true;
                } else if (significantLength == 10) {
                    long significant = 0L;
                    for (int i = significantStart; i < significantStart + 10; i++) {
                        significant = significant * 10 + (codePoints[i] - '0');
                    }
                    long limit = negative ? 2147483648L : 2147483647L;
                    outOfRange = significant > limit;
                } else {
                    outOfRange = false;
                }
                if (!outOfRange) {
                    long value = 0L;
                    for (int i = digitsStart; i < position; i++) {
                        value = value * 10 + (codePoints[i] - '0');
                    }
                    if (negative) {
                        value = -value;
                    }
                    return Long.valueOf(value);
                }
            }
            return Double.valueOf(Double.parseDouble(text));
        }
    }

    private static boolean isWs(int codePoint) {
        return codePoint == 0x20 || codePoint == 0x09
            || codePoint == 0x0A || codePoint == 0x0D;
    }

    private static boolean isDigit(int codePoint) {
        return codePoint >= '0' && codePoint <= '9';
    }

    private static int hexDigit(int codePoint) {
        if (codePoint >= '0' && codePoint <= '9') {
            return codePoint - '0';
        }
        if (codePoint >= 'a' && codePoint <= 'f') {
            return codePoint - 'a' + 10;
        }
        if (codePoint >= 'A' && codePoint <= 'F') {
            return codePoint - 'A' + 10;
        }
        return -1;
    }

    /** The UTF-8 byte length of one Unicode scalar value. */
    private static int utf8Length(int codePoint) {
        return codePoint < 0x80 ? 1 : codePoint < 0x800 ? 2 : codePoint < 0x10000 ? 3 : 4;
    }

    /** {@code JSON_PARSE}: the parse entry with the pinned trailing-content check. */
    private static Object jsonParse(String text) {
        JsonReader reader = new JsonReader(text.codePoints().toArray());
        try {
            reader.skipWs();
            Object value = reader.parseValue();
            reader.skipWs();
            if (!reader.atEnd()) {
                throw reader.failure(REASON_TRAILING_CONTENT);
            }
            return value;
        } catch (JsonParseFailure parseFailure) {
            throw new StdlibFailure("E8001",
                "JSON parse error at position " + parseFailure.oneBasedByteOffset
                    + ": " + parseFailure.reason,
                null, null);
        }
    }

    // =========================================================================
    // The RFC-8259 serializer (JSON_STRINGIFY realization)
    // =========================================================================

    /**
     * The pinned {@code STDLIB_CALL(JSON_STRINGIFY)} rejection: the
     * corpus-aligned visible text (the {@code JSON_TO_ERROR} row's second
     * template) with the projection's expected text and the value's
     * canonical actual-kind token. The walk's internal position never
     * surfaces — the first declaration-order failure is the only
     * observable fact.
     */
    private static StdlibFailure jsonEncodingFailure(String actual) {
        return new StdlibFailure("E8001",
            "unsupported type for JSON encoding: " + actual,
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, actual);
    }

    /** Serializes one table (object) with cycle detection and first-insertion order. */
    private static void stringifyTable(StringBuilder out, Table table,
                                       java.util.Set<Object> path) {
        if (!path.add(table)) {
            throw jsonEncodingFailure("table");
        }
        out.append('{');
        List<String> keys = new ArrayList<>(table.entries.keySet());
        for (int i = 0; i < keys.size(); i++) {
            String key = keys.get(i);
            if (i > 0) {
                out.append(',');
            }
            appendJsonString(out, key);
            out.append(':');
            stringifyValue(out, table.entries.get(key), path);
        }
        out.append('}');
        path.remove(table);
    }

    /** Serializes one array with cycle detection and index order. */
    private static void stringifyArray(StringBuilder out, Array array,
                                       java.util.Set<Object> path) {
        if (!path.add(array)) {
            throw jsonEncodingFailure("array");
        }
        out.append('[');
        for (int i = 0; i < array.elements.size(); i++) {
            if (i > 0) {
                out.append(',');
            }
            stringifyValue(out, array.elements.get(i), path);
        }
        out.append(']');
        path.remove(array);
    }

    /** Serializes one value: the first declaration-order failure wins (pre-order). */
    private static void stringifyValue(StringBuilder out, Object value,
                                       java.util.Set<Object> path) {
        if (value == null) {
            out.append("null");
        } else if (value instanceof Boolean bool) {
            out.append(bool ? "true" : "false");
        } else if (value instanceof Long longValue) {
            out.append(Long.toString(longValue));
        } else if (value instanceof Double doubleValue) {
            double d = doubleValue.doubleValue();
            if (!Double.isFinite(d)) {
                throw jsonEncodingFailure("number");
            }
            out.append(Double.toString(d));
        } else if (value instanceof String string) {
            appendJsonString(out, string);
        } else if (value instanceof Table table) {
            stringifyTable(out, table, path);
        } else if (value instanceof Array array) {
            stringifyArray(out, array, path);
        } else if (value == MISSING) {
            throw jsonEncodingFailure("missing");
        } else if (value instanceof FunctionValue || value instanceof Intrinsic
                || value instanceof AdapterValue) {
            throw jsonEncodingFailure("function");
        } else if (value instanceof ErrorValue) {
            throw jsonEncodingFailure("class:@builtin/Error");
        } else if (value instanceof ClassInstance instance) {
            // A class instance is not JSON serializable and projects as its
            // canonical identity (the closed class:<ClassId> actual token),
            // never the carrier's shape.
            throw jsonEncodingFailure("class:" + instance.classIdText());
        } else {
            throw jsonEncodingFailure("table");
        }
    }

    /**
     * RFC-8259 string escaping: quote and backslash escaped; the named
     * short escapes \b \f \n \r \t; every other control scalar
     * (U+0000-U+001F) as the lowercase four-hex-digit escape; every other scalar —
     * surrogate pairs included — emitted as raw scalar UTF-8.
     */
    private static void appendJsonString(StringBuilder out, String carrier) {
        out.append('"');
        for (int i = 0; i < carrier.length();) {
            int codePoint = carrier.codePointAt(i);
            i += Character.charCount(codePoint);
            switch (codePoint) {
                case '"' -> out.append("\\\"");
                case '\\' -> out.append("\\\\");
                case '\b' -> out.append("\\b");
                case '\f' -> out.append("\\f");
                case '\n' -> out.append("\\n");
                case '\r' -> out.append("\\r");
                case '\t' -> out.append("\\t");
                default -> {
                    if (codePoint < 0x20) {
                        out.append(String.format("\\u%04x", codePoint));
                    } else {
                        out.appendCodePoint(codePoint);
                    }
                }
            }
        }
        out.append('"');
    }

    // =========================================================================
    // Array read/bounds cells (shared slot-space context)
    // =========================================================================

    /** The ARRAY_ELEMENT_READ cell: negative E8002 first, then the contextual decision. */
    public static Object arrayRead(String opKey, String digest, String parent,
                                   String bKey, String bDigest, String bParent,
                                   String desc, String inner, Array container,
                                   long index, boolean nullable, String origin) {
        Object elem = MISSING;
        if (index < 0) {
            ev(currentModule(), bKey, "START", "BOUNDARY", bDigest, bParent,
                List.of(atom(MISSING, "missing")), null, null);
            DealError e = fail("E8002", "negative array index", origin, null, null);
            ev(currentModule(), bKey, "FAILURE", "BOUNDARY", bDigest, bParent,
                List.of(), null, errtext(e));
            ev(currentModule(), opKey, "FAILURE", "INDEX_READ", digest, parent,
                List.of(), null, errtext(e));
            throw e;
        }
        if (index < container.length && index < container.elements.size()) {
            elem = container.elements.get((int) index);
        }
        // A present null element stays null (the slot was stored with a
        // language null); only an absent/deleted slot reads as missing.
        String elemKind;
        if (elem == MISSING) {
            elemKind = "missing";
        } else if (elem == null) {
            elemKind = "null";
        } else {
            elemKind = inner;
        }
        ev(currentModule(), bKey, "START", "BOUNDARY", bDigest, bParent,
            List.of(atom(elem, elemKind)), null, null);
        ev(currentModule(), bKey, "SUCCESS", "BOUNDARY", bDigest, bParent, List.of(),
            atom(elem, elemKind), null);
        if (elem == MISSING) {
            if (nullable) {
                return null;
            }
            return MISSING;
        }
        return elem;
    }

    /** The ARRAY_ELEMENT_ASSIGNMENT/ARRAY_ELEMENT_DELETE cells. */
    public static void arrayBounds(String bKey, String bDigest, String bParent,
                                   Object input, long index, long length, String desc,
                                   String staticKind, boolean isAssign, String origin) {
        ev(currentModule(), bKey, "START", "BOUNDARY", bDigest, bParent,
            List.of(atom(input, staticKind)), null, null);
        if (index < 0 || index > length) {
            DealError e = fail("E8002", "array index out of bounds", origin, null, null);
            ev(currentModule(), bKey, "FAILURE", "BOUNDARY", bDigest, bParent, List.of(),
                null, errtext(e));
            throw e;
        }
        if (isAssign) {
            bcheck(desc, staticKind, input);
        }
        ev(currentModule(), bKey, "SUCCESS", "BOUNDARY", bDigest, bParent, List.of(),
            atom(input, staticKind), null);
    }

    /** The ARRAY_ELEMENT_DELETE cell whose input operand is the normalized slot. */
    public static void arrayBoundsSlot(String bKey, String bDigest, String bParent,
                                       long[] slot, long length, String origin) {
        long index = slot[0];
        String slotAtom = "slot:" + index + "/" + (index < length) + "/"
            + (slot[2] == 1 && index == length);
        ev(currentModule(), bKey, "START", "BOUNDARY", bDigest, bParent,
            List.of(slotAtom), null, null);
        if (index < 0 || index > length) {
            DealError e = fail("E8002", "array index out of bounds", origin, null, null);
            ev(currentModule(), bKey, "FAILURE", "BOUNDARY", bDigest, bParent, List.of(),
                null, errtext(e));
            throw e;
        }
        ev(currentModule(), bKey, "SUCCESS", "BOUNDARY", bDigest, bParent, List.of(),
            slotAtom, null);
    }

    /** The FOR_EACH op's own TYPE_DESCRIPTOR terminal check. */
    public static void foreachCheck(String opKey, String digest, String parent,
                                    String desc, Object elem, String origin) {
        if (elem == MISSING) {
            DealError e = fail("E8001", "expected " + desc + ", got missing", origin, desc,
                "missing");
            ev(currentModule(), opKey, "FAILURE", "FOR_EACH", digest, parent, List.of(),
                null, errtext(e));
            throw e;
        }
        try {
            bcheck(desc, desc, elem);
        } catch (DealError e) {
            ev(currentModule(), opKey, "FAILURE", "FOR_EACH", digest, parent, List.of(),
                null, errtext(e));
            throw e;
        }
    }

    /** The intrinsic conversion ladders (INT_CONVERSION/NUMBER_CONVERSION). */
    public static Object intConv(Object v, String kind, String opKey, String digest,
                                 String parent, String origin) {
        if (v == null) {
            DealError e = fail("E8001", "cannot convert null to int", origin, "int", "null");
            ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent,
                List.of(), null, errtext(e));
            throw e;
        }
        if (v instanceof Double doubleValue) {
            double d = doubleValue;
            if (Double.isNaN(d)) {
                DealError e = fail("E8001", "expected int, got NaN", origin, "int", "NaN");
                ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent,
                    List.of(), null, errtext(e));
                throw e;
            }
            if (Double.isInfinite(d)) {
                DealError e = fail("E8001", "expected int, got infinity", origin, "int",
                    "infinity");
                ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent,
                    List.of(), null, errtext(e));
                throw e;
            }
            if (d != Math.rint(d)) {
                DealError e = fail("E8001", "expected int, got non-integer number",
                    origin, "int", "non-integer number");
                ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent,
                    List.of(), null, errtext(e));
                throw e;
            }
            if (d < -2147483648d || d > 2147483647d) {
                DealError e = fail("E8004", "int out of safe range", origin, "int", "number");
                ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent,
                    List.of(), null, errtext(e));
                throw e;
            }
            return (long) d;
        }
        if (v instanceof Long) {
            return v;
        }
        DealError e = fail("E8001", "expected int, got " + actualOf(kind, v), origin, "int",
            actualOf(kind, v));
        ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent, List.of(),
            null, errtext(e));
        throw e;
    }

    public static Object numConv(Object v, String kind, String opKey, String digest,
                                 String parent, String origin) {
        if (v == null) {
            DealError e = fail("E8001", "cannot convert null to number", origin, "number",
                "null");
            ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent,
                List.of(), null, errtext(e));
            throw e;
        }
        if (v instanceof Long longValue) {
            return (double) longValue;
        }
        if (v instanceof Double) {
            return v;
        }
        DealError e = fail("E8001", "expected number, got " + actualOf(kind, v), origin,
            "number", actualOf(kind, v));
        ev(currentModule(), opKey, "FAILURE", "INTRINSIC_CALL", digest, parent, List.of(),
            null, errtext(e));
        throw e;
    }

    // =========================================================================
    // Module context
    // =========================================================================

    private static String module = "";

    public static void setModule(String moduleName) {
        module = moduleName;
    }

    public static String currentModule() {
        return module;
    }
}
