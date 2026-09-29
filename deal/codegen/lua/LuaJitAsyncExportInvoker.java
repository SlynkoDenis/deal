package deal.codegen.lua;

import deal.codegen.AsyncExportEnvelope;
import deal.semantic.ir.JsonScan;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * The production LuaJIT host half of {@code BackendAsyncExportInvoker}
 * (luajit-async-export-invoker D1–D10, Architecture item 1): executes a
 * compiled entry artifact under real {@code luajit}, runs module
 * initialization and {@code main()} exactly once in one fresh runtime
 * instance, then calls
 * {@code __rt.invoke_async_export(exports, exportName, returnDescriptor)}
 * and maps the outcome.
 *
 * <h2>Invocation shape (D3)</h2>
 * Every {@link #invoke(AsyncExportInvocationRequest)} call:
 * <ol>
 *   <li>validates the request and derives the deployment root by walking
 *       up from the entry artifact's parent directory to the nearest
 *       ancestor containing {@code deal/runtime.lua} (D5); a missing
 *       entry artifact or marker is a hard failure before any spawn;</li>
 *   <li>locates the committed driver resource
 *       {@code deal/lua_async_export_driver.lua} classpath-first with a
 *       working-tree fallback — the same mechanism the orchestrator uses
 *       for {@code deal/runtime.lua}
 *       ({@code deal/module/CompilationOrchestrator.java:2031-2067}) —
 *       and materializes it into a per-invocation temp file (D1);</li>
 *   <li>spawns exactly one non-detached
 *       {@code ProcessBuilder("luajit", driverPath, entryArtifact,
 *       artifactRoot, exportName, returnDescriptor)} — argv only, no
 *       shell, working directory = artifact root — with stdout/stderr
 *       redirected to temp capture files (no pipe deadlock), waits for
 *       exit, imposes no deadline, and builds no containment (D3, the
 *       delegated containment boundary);</li>
 *   <li>parses the last stdout line with the exact marker prefix
 *       {@value #RESULT_PREFIX} through the strict conventional-JSON
 *       envelope codec (D6, Architecture item 3) and maps the outcome;</li>
 *   <li>deletes the per-invocation temp directory (capture files and the
 *       materialized driver) in a {@code finally} block.</li>
 * </ol>
 *
 * <h2>Outcome mapping (D2/D6/D8)</h2>
 * <ul>
 *   <li>{@code value} envelope → {@link Result.Value} — the
 *       matcher-validated completion as its exact JSON text plus the
 *       descriptor it was matched against;</li>
 *   <li>{@code deal-error} envelope → {@link Result.DealError} with
 *       code/message/file/line/column propagated byte-for-byte and
 *       absent location fields {@code null};</li>
 *   <li>{@code host-failure} envelope → {@link Result.HostFailure} with
 *       the runtime's pinned reason verbatim — missing, sync,
 *       parameterized, duplicate, descriptor-mismatched, non-wrapper,
 *       non-operation exports, and malformed protocol input;</li>
 *   <li>{@code representation-failure} and {@code infrastructure-failure}
 *       envelopes, a missing/malformed envelope, an unknown status or
 *       field, and a nonzero exit without one of the three invocation
 *       envelopes → {@link LuaJitAsyncExportInvocationException} with
 *       the captured process output — never an expected DEAL code.</li>
 * </ul>
 *
 * <p>The component is stateless: one process per invoke, no retry, no
 * state shared between invokes, and concurrent invokes are isolated
 * processes (D3).</p>
 */
public class LuaJitAsyncExportInvoker {

    /** The committed driver distribution resource (D1). */
    public static final String DRIVER_RESOURCE =
        "deal/lua_async_export_driver.lua";

    /** The exact stdout marker prefix of the envelope protocol (D6). */
    public static final String RESULT_PREFIX = "DEAL_ASYNC_EXPORT_RESULT:";

    /** Temp-directory prefix for the per-invocation materialization. */
    static final String TEMP_DIR_PREFIX = "deal-async-export-invoker-";


    // =========================================================================
    // Public API
    // =========================================================================

    /**
     * The sealed invocation result (D2): exactly three variants and no
     * others, so mistaking a host or infrastructure failure for a DEAL
     * code is impossible at the type level.
     */
    public sealed interface Result
            permits Result.Value, Result.DealError, Result.HostFailure {

        /**
         * The matcher-validated completion (D2/D6/D7).
         *
         * @param returnDescriptor the byte-exact canonical descriptor the
         *                         completion was matched against
         * @param valueJson        the completion value as its exact JSON
         *                         text over the JSON-encodable surface
         *                         (null, booleans, {@code %.17g} numbers,
         *                         UTF-8 strings, arrays, class/plain
         *                         objects)
         */
        record Value(String returnDescriptor, String valueJson)
                implements Result {
            public Value {
                Objects.requireNonNull(returnDescriptor,
                    "returnDescriptor must not be null");
                Objects.requireNonNull(valueJson, "valueJson must not be null");
            }
        }

        /**
         * A DEAL Error raised by module initialization, {@code main()},
         * the operation, or the completion matcher — propagated with
         * code and location unchanged (D8). Absent location fields are
         * {@code null}.
         */
        record DealError(String code, String message, String file,
                         Integer line, Integer column) implements Result {
            public DealError {
                Objects.requireNonNull(code, "code must not be null");
                Objects.requireNonNull(message, "message must not be null");
            }
        }

        /**
         * The parent's {@code HostInvocationFailure}: a missing, sync,
         * parameterized, duplicate, descriptor-mismatched, non-wrapper,
         * or non-operation export, or malformed protocol input — with
         * the runtime's pinned reason string verbatim (D9). Never a DEAL
         * code.
         */
        record HostFailure(String reason) implements Result {
            public HostFailure {
                Objects.requireNonNull(reason, "reason must not be null");
            }
        }
    }

    /**
     * Invokes one exact async export under one fresh real-LuaJIT
     * process. See the class contract for the full outcome mapping.
     *
     * @param request the three-field request; non-null
     * @return {@link Result.Value}, {@link Result.DealError}, or
     *         {@link Result.HostFailure} — never {@code null}
     * @throws LuaJitAsyncExportInvocationException for infrastructure,
     *         containment, and value-representation failures
     */
    public Result invoke(AsyncExportInvocationRequest request) {
        Objects.requireNonNull(request, "request must not be null");

        Path entryArtifact = request.entryArtifact().toAbsolutePath().normalize();
        // D5: a missing entry artifact is a hard failure before any spawn.
        if (!Files.isRegularFile(entryArtifact)) {
            throw new LuaJitAsyncExportInvocationException(
                "entry artifact not found: " + entryArtifact, null, null);
        }

        // D5: deployment-root derivation by the runtime marker. A missing
        // marker is a hard failure before any spawn.
        Path artifactRoot = deriveDeploymentRoot(entryArtifact);
        if (artifactRoot == null) {
            throw new LuaJitAsyncExportInvocationException(
                "no deployment root found: no deal/runtime.lua marker in"
                    + " any ancestor directory of " + entryArtifact,
                null, null);
        }

        // D1: driver resource, classpath-first with the working-tree
        // fallback. A missing driver is a hard failure before any spawn.
        final InputStream driverStream;
        try {
            driverStream = locateDriverResource();
        } catch (IOException e) {
            throw new LuaJitAsyncExportInvocationException(
                "cannot read the async-export driver resource "
                    + DRIVER_RESOURCE + ": " + e.getMessage(), null, null, e);
        }
        if (driverStream == null) {
            throw new LuaJitAsyncExportInvocationException(
                "async-export driver resource not found: " + DRIVER_RESOURCE
                    + " (classpath resource and working-tree fallback both"
                    + " absent)", null, null);
        }

        Path tempDir;
        try {
            tempDir = Files.createTempDirectory(TEMP_DIR_PREFIX);
        } catch (IOException e) {
            throw new LuaJitAsyncExportInvocationException(
                "cannot create the per-invocation temp directory: "
                    + e.getMessage(), null, null, e);
        }

        String stdout = null;
        String stderr = null;
        try (InputStream stream = driverStream) {
            Path driverFile = tempDir.resolve("lua_async_export_driver.lua");
            Files.copy(stream, driverFile);

            Path stdoutFile = tempDir.resolve("stdout.txt");
            Path stderrFile = tempDir.resolve("stderr.txt");

            // D3: exactly one non-detached luajit child per invoke, argv
            // only (no shell), working directory = artifact root, capture
            // files instead of pipes (no pipe deadlock), no deadline, no
            // setsid, no kill escalation.
            ProcessBuilder pb = new ProcessBuilder("luajit",
                driverFile.toString(),
                entryArtifact.toString(),
                artifactRoot.toString(),
                request.exportName(),
                request.returnDescriptor());
            pb.directory(artifactRoot.toFile());
            pb.redirectOutput(stdoutFile.toFile());
            pb.redirectError(stderrFile.toFile());

            final Process process;
            try {
                process = pb.start();
            } catch (IOException e) {
                throw new LuaJitAsyncExportInvocationException(
                    "cannot spawn luajit: " + e.getMessage(), null, null, e);
            }

            final int exit;
            try {
                exit = process.waitFor();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                throw new LuaJitAsyncExportInvocationException(
                    "interrupted while waiting for the luajit child",
                    null, null, e);
            }

            try {
                stdout = AsyncExportEnvelope.readCapture(stdoutFile);
                stderr = AsyncExportEnvelope.readCapture(stderrFile);
            } catch (IOException e) {
                throw new LuaJitAsyncExportInvocationException(
                    "cannot read the luajit capture files: " + e.getMessage(),
                    null, null, e);
            }

            return mapOutcome(exit, stdout, stderr);
        } catch (IOException e) {
            throw new LuaJitAsyncExportInvocationException(
                "async-export invoker I/O failure: " + e.getMessage(),
                stdout, stderr, e);
        } finally {
            AsyncExportEnvelope.deleteRecursively(tempDir);
        }
    }

    // =========================================================================
    // Driver resource location (D1)
    // =========================================================================

    /**
     * Locates the committed driver resource: classloader resource first,
     * working-tree file fallback — the same mechanism the orchestrator
     * uses for {@code deal/runtime.lua}
     * ({@code deal/module/CompilationOrchestrator.java:2031-2067}).
     *
     * <p>Overridable in tests to hide both lookup sources and exercise
     * the missing-driver hard-failure path.</p>
     *
     * @return an open stream over the driver text, or {@code null} when
     *         neither lookup source carries it
     * @throws IOException when the working-tree file exists but cannot
     *         be opened
     */
    protected InputStream locateDriverResource() throws IOException {
        InputStream stream = getClass().getClassLoader()
            .getResourceAsStream(DRIVER_RESOURCE);
        if (stream != null) {
            return stream;
        }
        Path workingTree = Path.of(DRIVER_RESOURCE);
        if (Files.isRegularFile(workingTree)) {
            return Files.newInputStream(workingTree);
        }
        return null;
    }

    // =========================================================================
    // Deployment-root derivation (D5)
    // =========================================================================

    /**
     * Walks up from the entry artifact's parent directory to the nearest
     * ancestor containing {@code deal/runtime.lua} — the orchestrator's
     * deployment marker ({@code deal/module/CompilationOrchestrator.java:1582}).
     *
     * @return the nearest ancestor deployment root, or {@code null} when
     *         no ancestor carries the marker
     */
    static Path deriveDeploymentRoot(Path entryArtifact) {
        Path dir = entryArtifact.getParent();
        while (dir != null) {
            if (Files.isRegularFile(dir.resolve("deal/runtime.lua"))) {
                return dir;
            }
            dir = dir.getParent();
        }
        return null;
    }

    // =========================================================================
    // Envelope mapping (D6)
    // =========================================================================

    /**
     * Maps process exit + captured streams to an invocation result or a
     * hard failure (D6). The driver's envelope line is always the last
     * stdout write of the process, so user {@code console.log} output
     * interleaving on both streams never corrupts the frame.
     */
    private Result mapOutcome(int exit, String stdout, String stderr) {
        String line = AsyncExportEnvelope.lastMarkerLine(stdout, RESULT_PREFIX);
        if (line == null) {
            throw new LuaJitAsyncExportInvocationException(
                "no " + RESULT_PREFIX + " envelope line on stdout (luajit"
                    + " exited " + exit + ")", stdout, stderr);
        }

        final AsyncExportEnvelope.Envelope envelope;
        try {
            envelope = AsyncExportEnvelope.decodeEnvelope(
                line.substring(RESULT_PREFIX.length()));
        } catch (EnvelopeJson.ParseException e) {
            throw new LuaJitAsyncExportInvocationException(
                "malformed async-export envelope on stdout (luajit exited "
                    + exit + "): " + e.getMessage(), stdout, stderr, e);
        }

        // Status dispatch owns the hard-failure mapping: a nonzero exit
        // without one of the three invocation envelopes (a
        // representation- or infrastructure-failure envelope) throws
        // below regardless of the exit code, the three invocation
        // envelopes map (the driver pins exit 0 for them), and every
        // other shape was already rejected fail-closed by the codec.
        return switch (envelope.status) {
            case AsyncExportEnvelope.STATUS_VALUE -> new Result.Value(
                envelope.descriptor, envelope.value);
            case AsyncExportEnvelope.STATUS_DEAL_ERROR -> new Result.DealError(
                envelope.code, envelope.message, envelope.file, envelope.line,
                envelope.column);
            case AsyncExportEnvelope.STATUS_HOST_FAILURE -> new Result.HostFailure(
                envelope.reason);
            case AsyncExportEnvelope.STATUS_REPRESENTATION_FAILURE ->
                throw new LuaJitAsyncExportInvocationException(
                    "value-representation failure: " + envelope.reason,
                    stdout, stderr);
            case AsyncExportEnvelope.STATUS_INFRASTRUCTURE_FAILURE ->
                throw new LuaJitAsyncExportInvocationException(
                    "infrastructure failure: " + envelope.reason,
                    stdout, stderr);
            default ->
                throw new LuaJitAsyncExportInvocationException(
                    "unknown envelope status: " + envelope.status,
                    stdout, stderr);
        };
    }

    // =========================================================================
    // Envelope JSON codec (D6, Architecture item 3)
    // =========================================================================

    /**
     * The strict conventional-JSON reader owned by the invoker. The
     * production {@code CanonicalJson}
     * ({@code deal/semantic/ir/CanonicalJson.java}) is canonical-only and
     * rejects conventional decimal numbers ({@code %.17g} text), so this
     * small fail-closed reader is required; the
     * no-second-JSON-library convention is preserved (no org.json, Gson,
     * Jackson, or ObjectMapper anywhere in the invoker).
     *
     * <p>Supported: objects, strings with the RFC 8259 escape set
     * ({@code \" \\ \/ \b \f \n \r \t \\uXXXX} with surrogate-pair
     * combination), conventional decimal numbers
     * ({@code -?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?}),
     * {@code true}/{@code false}/{@code null}. Rejected: arrays (not part
     * of the closed envelope schema), duplicate keys, raw control
     * characters in strings, unpaired surrogates, malformed numbers and
     * escapes, and trailing content.</p>
     */
    public static final class EnvelopeJson {

        /** A codec failure: malformed conventional JSON text. */
        public static final class ParseException extends RuntimeException {
            /**
             * Public construction (ISSUE-0161): the JVM async-export
             * invoker validates the shared closed envelope schema with
             * this same codec from {@code deal.codegen.jvm}, so its
             * schema validation failures are this exception type.
             */
            public ParseException(String message) {
                super(message);
            }
        }

        /** The closed value model of the reader. */
        public sealed interface Value
                permits EnvelopeJson.ObjectValue, EnvelopeJson.StringValue,
                        EnvelopeJson.NumberValue, EnvelopeJson.BooleanValue,
                        EnvelopeJson.NullValue {
        }

        /**
         * A JSON object with insertion-order-independent field access.
         * Duplicate keys were already rejected by the reader.
         */
        public record ObjectValue(Map<String, Value> fields) implements Value {
            public ObjectValue {
                fields = Map.copyOf(fields);
            }
        }

        /** A JSON string with its decoded text. */
        public record StringValue(String text) implements Value {}

        /**
         * A conventional JSON number, preserving the exact token text
         * ({@code %.17g} output like {@code 0.10000000000000001} is kept
         * byte-for-byte).
         */
        public record NumberValue(String token) implements Value {

            /** True when the token is integral text ({@code -?[0-9]+}). */
            public boolean isIntegralText() {
                return token.matches("-?[0-9]+");
            }

            /** The token parsed as a {@code long}. */
            public long longValue() {
                return Long.parseLong(token);
            }
        }

        /** A JSON boolean. */
        public record BooleanValue(boolean value) implements Value {}

        /** JSON {@code null}. */
        public record NullValue() implements Value {}

        /**
         * Parses conventional JSON text into the value model.
         *
         * @param text the JSON text; non-null
         * @return the parsed value, never {@code null}
         * @throws ParseException on malformed text, duplicate keys,
         *         unpaired surrogates, or trailing content
         */
        public static Value parseValue(String text) {
            Objects.requireNonNull(text, "text must not be null");
            Parser parser = new Parser(text);
            Value value = parser.parseValue();
            parser.skipWhitespace();
            if (!parser.atEnd()) {
                throw parser.err("trailing content after the top-level value");
            }
            return value;
        }

        /**
         * Parses conventional JSON text as an object (the envelope
         * protocol's only top-level shape).
         *
         * @param text the JSON object text; non-null
         * @return the parsed object, never {@code null}
         * @throws ParseException on malformed text or a non-object
         *         top-level value
         */
        public static ObjectValue parseObject(String text) {
            Value value = parseValue(text);
            if (!(value instanceof ObjectValue obj)) {
                throw new ParseException(
                    "expected a JSON object, got " + value.getClass()
                        .getSimpleName());
            }
            return obj;
        }

        private EnvelopeJson() {
        }

        /** Recursive-descent conventional-JSON parser. */
        private static final class Parser extends JsonScan.CharCursor {

            Parser(String text) {
                super(text);
            }

            @Override
            public ParseException err(String reason) {
                return new ParseException(reason + " at offset " + pos);
            }

            Value parseValue() {
                skipWhitespace();
                if (atEnd()) {
                    throw err("unexpected end of input (expected a value)");
                }
                char c = peek();
                return switch (c) {
                    case '{' -> parseObject();
                    case '"' -> parseString();
                    case 't' -> parseLiteral("true", new BooleanValue(true));
                    case 'f' -> parseLiteral("false", new BooleanValue(false));
                    case 'n' -> parseLiteral("null", new NullValue());
                    default -> {
                        if (c == '-' || (c >= '0' && c <= '9')) {
                            yield parseNumber();
                        }
                        throw err("unexpected character '" + printable(c)
                            + "' (expected a value)");
                    }
                };
            }

            ObjectValue parseObject() {
                pos++; // '{'
                Map<String, Value> fields = new LinkedHashMap<>();
                skipWhitespace();
                if (!atEnd() && peek() == '}') {
                    pos++;
                    return new ObjectValue(fields);
                }
                while (true) {
                    skipWhitespace();
                    if (atEnd() || peek() != '"') {
                        throw err("expected a string object key");
                    }
                    String key = parseString().text();
                    if (fields.containsKey(key)) {
                        throw err("duplicate object key \"" + key + "\"");
                    }
                    skipWhitespace();
                    if (atEnd() || peek() != ':') {
                        throw err("expected ':' after object key");
                    }
                    pos++;
                    fields.put(key, parseValue());
                    skipWhitespace();
                    if (atEnd()) {
                        throw err("unterminated object (expected ',' or '}')");
                    }
                    char c = peek();
                    if (c == ',') {
                        pos++;
                        continue;
                    }
                    if (c == '}') {
                        pos++;
                        return new ObjectValue(fields);
                    }
                    throw err("expected ',' or '}' in object");
                }
            }

            StringValue parseString() {
                pos++; // opening quote
                StringBuilder sb = new StringBuilder();
                while (true) {
                    if (atEnd()) {
                        throw err("unterminated string");
                    }
                    char c = text.charAt(pos++);
                    if (c == '"') {
                        break;
                    }
                    if (c == '\\') {
                        if (atEnd()) {
                            throw err("unterminated string escape");
                        }
                        char e = text.charAt(pos++);
                        switch (e) {
                            case '"' -> sb.append('"');
                            case '\\' -> sb.append('\\');
                            case '/' -> sb.append('/');
                            case 'b' -> sb.append('\b');
                            case 'f' -> sb.append('\f');
                            case 'n' -> sb.append('\n');
                            case 'r' -> sb.append('\r');
                            case 't' -> sb.append('\t');
                            case 'u' -> sb.append(parseUnicodeEscape());
                            default -> throw err(
                                "invalid string escape '\\" + e + "'");
                        }
                    } else if (c < 0x20) {
                        throw err("raw control character in string");
                    } else {
                        sb.append(c);
                    }
                }
                return new StringValue(sb.toString());
            }

            /** Decodes one {@code \\uXXXX} escape, combining surrogate pairs. */
            private String parseUnicodeEscape() {
                if (pos + 4 > text.length()) {
                    throw err("truncated \\u escape");
                }
                int value = readHex4();
                if (value >= 0xD800 && value <= 0xDBFF) {
                    // High surrogate: must be followed by a low one.
                    if (pos + 6 > text.length() || text.charAt(pos) != '\\'
                            || text.charAt(pos + 1) != 'u') {
                        throw err("unpaired high surrogate in \\u escape");
                    }
                    pos += 2;
                    int low = readHex4();
                    if (low < 0xDC00 || low > 0xDFFF) {
                        throw err("unpaired high surrogate in \\u escape");
                    }
                    int codePoint = 0x10000 + ((value - 0xD800) << 10)
                        + (low - 0xDC00);
                    return new String(Character.toChars(codePoint));
                }
                if (value >= 0xDC00 && value <= 0xDFFF) {
                    throw err("unpaired low surrogate in \\u escape");
                }
                return String.valueOf((char) value);
            }

            private int readHex4() {
                int value = 0;
                for (int i = 0; i < 4; i++) {
                    if (pos >= text.length()) {
                        throw err("truncated \\u escape");
                    }
                    int digit = Character.digit(text.charAt(pos++), 16);
                    if (digit < 0) {
                        throw err("invalid \\u escape (non-hex digit)");
                    }
                    value = (value << 4) | digit;
                }
                return value;
            }

            NumberValue parseNumber() {
                int start = pos;
                if (!atEnd() && peek() == '-') {
                    pos++;
                }
                if (atEnd()) {
                    throw err("malformed number");
                }
                char c = peek();
                if (c == '0') {
                    pos++;
                } else if (c >= '1' && c <= '9') {
                    do {
                        pos++;
                    } while (!atEnd() && isDigit(peek()));
                } else {
                    throw err("malformed number (expected a digit)");
                }
                if (!atEnd() && peek() == '.') {
                    pos++;
                    if (atEnd() || !isDigit(peek())) {
                        throw err("malformed number (fraction needs a digit)");
                    }
                    do {
                        pos++;
                    } while (!atEnd() && isDigit(peek()));
                }
                if (!atEnd() && (peek() == 'e' || peek() == 'E')) {
                    pos++;
                    if (!atEnd() && (peek() == '+' || peek() == '-')) {
                        pos++;
                    }
                    if (atEnd() || !isDigit(peek())) {
                        throw err("malformed number (exponent needs a digit)");
                    }
                    do {
                        pos++;
                    } while (!atEnd() && isDigit(peek()));
                }
                return new NumberValue(text.substring(start, pos));
            }

            boolean isDigit(char c) {
                return c >= '0' && c <= '9';
            }

            String printable(char c) {
                return c < 0x20 || c > 0x7E
                    ? String.format("\\u%04x", (int) c) : String.valueOf(c);
            }
        }
    }
}
