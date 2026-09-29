package deal.semantic.ir;

import java.nio.ByteBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HexFormat;
import java.util.List;
import java.util.Objects;
import java.util.regex.Pattern;

/**
 * The single canonical JSON facility of {@code deal.semantic-ir/1}
 * (schema S2; foundation F8): one generic value model, one serializer, one
 * parser, and one SHA-256 helper. Every foundation component serializes
 * through this serializer and parses through this parser — no component
 * serializes or parses canonical JSON for itself; the
 * {@link ContractSnapshotCanonicalizer} maps the snapshot records onto
 * this value model and the later validator/dumper/harness components
 * consume exactly this facility.
 *
 * <p>Canonical JSON rules (S2, exact): UTF-8; sorted object keys
 * (lexicographic {@code String} order — every pinned schema key is ASCII);
 * signed32 integers rendered as decimal integers; IEEE-754 numbers
 * rendered as unique hex floats ({@code 0x1.921fb54442d18p1}-style,
 * {@code NaN}, {@code Infinity}, {@code -Infinity}, negative zero
 * preserved as {@code -0x0.0p0}); explicit nulls (never omitted);
 * ordered arrays. Serialization never iterates a {@code Map} or
 * {@code Set}: objects carry an ordered entry list, and the serializer
 * sorts a defensive copy of it, so the output bytes are fully determined
 * by the value model. Strings must contain Unicode scalars — an unpaired
 * surrogate is rejected at construction (producer defect,
 * {@link IllegalArgumentException}) and at parse time (transport failure,
 * {@link SemanticIrTextDecodeException}).</p>
 *
 * <p>The parser is the exact inverse of the serializer over the pinned
 * schema: it accepts every serializer output, and re-serializing a parsed
 * tree reproduces the input bytes exactly. It is a strict transport: only
 * canonical number forms are accepted (decimal signed32 integers and
 * hex floats in the unique {@code Double.toHexString} spelling), duplicate
 * object keys, invalid UTF-8, unpaired surrogates, malformed syntax, and
 * trailing content raise {@link SemanticIrTextDecodeException}. It performs
 * no closed-enum, reserved-name, policy, or profile validation — those are
 * the validator's rules (T6).</p>
 */
public final class CanonicalJson {

    private CanonicalJson() {
        // Static utility; no instances.
    }

    // =========================================================================
    // Value model (ordered, map-free)
    // =========================================================================

    /** A canonical JSON value: exactly the seven shapes below. */
    public sealed interface Value permits Null, Bool, Int, Num, Str, Arr, Obj {
    }

    /** The canonical JSON {@code null}. */
    public enum Null implements Value {
        INSTANCE
    }

    /** A canonical JSON boolean. */
    public record Bool(boolean value) implements Value {
    }

    /** A canonical JSON signed32 integer (rendered as a decimal integer). */
    public record Int(int value) implements Value {
    }

    /** A canonical JSON IEEE-754 number (rendered as a unique hex float). */
    public record Num(double value) implements Value {
    }

    /** A canonical JSON string of Unicode scalars. */
    public record Str(String value) implements Value {

        public Str {
            Objects.requireNonNull(value, "value must not be null");
            requireUnicodeScalars(value);
        }
    }

    /** A canonical JSON array of ordered values. */
    public record Arr(List<Value> items) implements Value {

        public Arr(List<Value> items) {
            Objects.requireNonNull(items, "items must not be null");
            List<Value> copy = new ArrayList<>(items);
            for (Value item : copy) {
                Objects.requireNonNull(item, "array items must not be null");
            }
            this.items = List.copyOf(copy);
        }
    }

    /** One key/value entry of a canonical JSON object. */
    public record Entry(String key, Value value) {

        public Entry {
            Objects.requireNonNull(key, "key must not be null");
            requireUnicodeScalars(key);
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /**
     * A canonical JSON object carrying an ordered entry list. The
     * serializer sorts the entries by key, so the output is independent of
     * the construction order; duplicate keys are rejected at construction
     * (a producer defect — canonical objects are maps by name only).
     */
    public record Obj(List<Entry> entries) implements Value {

        public Obj(List<Entry> entries) {
            Objects.requireNonNull(entries, "entries must not be null");
            List<Entry> copy = new ArrayList<>(entries);
            for (int i = 0; i < copy.size(); i++) {
                Entry entry = Objects.requireNonNull(copy.get(i), "entries must not contain null");
                for (int j = i + 1; j < copy.size(); j++) {
                    if (entry.key().equals(copy.get(j).key())) {
                        throw new IllegalArgumentException(
                            "duplicate object key \"" + entry.key() + "\" in canonical JSON object");
                    }
                }
            }
            this.entries = List.copyOf(copy);
        }
    }

    // =========================================================================
    // Value constructors
    // =========================================================================

    /** The canonical JSON {@code null} value. */
    /**
     * The unique canonical hex-float spelling of an IEEE-754 number
     * ({@code Double.toHexString}; the single renderer of hex floats in
     * deal/semantic).
     */
    public static String numberHex(double value) {
        return Double.toHexString(value);
    }

    /**
     * The single decimal-number decode surface of {@code deal/semantic}
     * (schema S2): the nearest IEEE-754 double of a decimal numeral text
     * — the RFC-8259 integer/fraction/exponent forms the
     * {@code SharedStdlibSemantics} JSON parser validates. Grammar
     * ownership stays split: the stdlib parser owns the RFC-8259 numeral
     * grammar, this facility owns the decimal-to-IEEE conversion, and no
     * other semantic production component calls the JDK decimal
     * converter directly (the structural single-implementation
     * assertion). A magnitude beyond the IEEE range yields ±Infinity —
     * the parser's later consumers decide the projection.
     *
     * @param text the validated decimal numeral text; non-null
     * @return the nearest IEEE-754 double of {@code text}
     * @throws NullPointerException if {@code text} is null
     * @throws NumberFormatException if {@code text} is not a decimal
     *                               numeral (a producer defect — the
     *                               caller validates the grammar first)
     */
    public static double decodeDecimal(String text) {
        Objects.requireNonNull(text, "text must not be null");
        return Double.parseDouble(text);
    }

    public static Null nullValue() {
        return Null.INSTANCE;
    }

    /** A canonical JSON boolean value. */
    public static Bool bool(boolean value) {
        return new Bool(value);
    }

    /** A canonical JSON signed32 integer value. */
    public static Int intValue(int value) {
        return new Int(value);
    }

    /** A canonical JSON IEEE-754 number value. */
    public static Num number(double value) {
        return new Num(value);
    }

    /** A canonical JSON string value. */
    public static Str str(String value) {
        return new Str(value);
    }

    /** A canonical JSON array over the given ordered values. */
    public static Arr arr(Value... items) {
        return new Arr(List.of(items));
    }

    /** A canonical JSON array over the given ordered values. */
    public static Arr arr(List<Value> items) {
        return new Arr(items);
    }

    /** A canonical JSON object entry. */
    public static Entry e(String key, Value value) {
        return new Entry(key, value);
    }

    /** A canonical JSON object over the given entries (keys sorted at serialization). */
    public static Obj obj(Entry... entries) {
        return new Obj(List.of(entries));
    }

    /** A canonical JSON object over the given entries (keys sorted at serialization). */
    public static Obj obj(List<Entry> entries) {
        return new Obj(entries);
    }

    // =========================================================================
    // Serialization
    // =========================================================================

    /**
     * Serializes the value to canonical JSON UTF-8 bytes (S2 rules).
     *
     * @param value the value; non-null
     * @return the canonical JSON bytes
     */
    public static byte[] serializeBytes(Value value) {
        Objects.requireNonNull(value, "value must not be null");
        StringBuilder sb = new StringBuilder();
        append(sb, value);
        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }

    /** Serializes the value to canonical JSON text (debug/trace surface only). */
    public static String serializeText(Value value) {
        return new String(serializeBytes(value), StandardCharsets.UTF_8);
    }

    private static void append(StringBuilder sb, Value value) {
        switch (value) {
            case Null ignored -> sb.append("null");
            case Bool b -> sb.append(b.value() ? "true" : "false");
            case Int i -> sb.append(Integer.toString(i.value()));
            case Num n -> sb.append(numberHex(n.value()));
            case Str s -> appendString(sb, s.value());
            case Arr a -> {
                sb.append('[');
                for (int i = 0; i < a.items().size(); i++) {
                    if (i > 0) {
                        sb.append(',');
                    }
                    append(sb, a.items().get(i));
                }
                sb.append(']');
            }
            case Obj o -> {
                sb.append('{');
                List<Entry> sorted = new ArrayList<>(o.entries());
                sorted.sort(Comparator.comparing(Entry::key));
                for (int i = 0; i < sorted.size(); i++) {
                    if (i > 0) {
                        sb.append(',');
                    }
                    appendString(sb, sorted.get(i).key());
                    sb.append(':');
                    append(sb, sorted.get(i).value());
                }
                sb.append('}');
            }
        }
    }

    private static void appendString(StringBuilder sb, String s) {
        sb.append('"');
        for (int i = 0; i < s.length(); ) {
            int cp = s.codePointAt(i);
            i += Character.charCount(cp);
            switch (cp) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\b' -> sb.append("\\b");
                case '\f' -> sb.append("\\f");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> {
                    if (cp < 0x20) {
                        sb.append(String.format("\\u%04x", cp));
                    } else {
                        sb.appendCodePoint(cp);
                    }
                }
            }
        }
        sb.append('"');
    }

    private static void requireUnicodeScalars(String s) {
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (Character.isHighSurrogate(c)) {
                if (i + 1 >= s.length() || !Character.isLowSurrogate(s.charAt(i + 1))) {
                    throw new IllegalArgumentException(
                        "string contains an unpaired high surrogate; DEAL strings must be "
                            + "Unicode scalars (offset " + i + ")");
                }
                i++;
            } else if (Character.isLowSurrogate(c)) {
                throw new IllegalArgumentException(
                    "string contains an unpaired low surrogate; DEAL strings must be "
                        + "Unicode scalars (offset " + i + ")");
            }
        }
    }

    // =========================================================================
    // SHA-256
    // =========================================================================

    /**
     * The canonical digest encoding of this facility: lowercase SHA-256
     * hex over the given bytes. The single digest helper — every canonical
     * digest (contract snapshots, lowering-context hashes, index digests,
     * invocation hashes) flows through this method.
     *
     * @param bytes the bytes to digest; non-null
     * @return the lowercase 64-character hex digest
     */
    public static String sha256Hex(byte[] bytes) {
        Objects.requireNonNull(bytes, "bytes must not be null");
        try {
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            return HexFormat.of().formatHex(md.digest(bytes));
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 is unavailable on this platform", e);
        }
    }

    // =========================================================================
    // Parsing (the exact inverse)
    // =========================================================================

    /** The unique hex-float spelling accepted by the parser (S2 number rule). */
    private static final Pattern HEX_FLOAT = Pattern.compile(
        "-?0[xX][0-9a-fA-F]+(\\.[0-9a-fA-F]*)?([pP][+-]?[0-9]+)?");

    /**
     * Parses canonical JSON UTF-8 text into the value model. Accepts every
     * serializer output and reproduces it byte-exactly on re-serialization;
     * raises {@link SemanticIrTextDecodeException} for invalid UTF-8,
     * malformed syntax, non-canonical numbers, duplicate keys, unpaired
     * surrogates, or trailing content.
     *
     * @param utf8 the canonical JSON bytes; non-null
     * @return the parsed value
     * @throws SemanticIrTextDecodeException on any transport-level violation
     */
    public static Value parse(byte[] utf8) {
        Objects.requireNonNull(utf8, "utf8 must not be null");
        String text;
        try {
            text = StandardCharsets.UTF_8.newDecoder()
                .onMalformedInput(CodingErrorAction.REPORT)
                .onUnmappableCharacter(CodingErrorAction.REPORT)
                .decode(ByteBuffer.wrap(utf8))
                .toString();
        } catch (CharacterCodingException e) {
            throw new SemanticIrTextDecodeException("invalid UTF-8 input: " + e.getMessage());
        }
        return parse(text);
    }

    /**
     * Parses canonical JSON text into the value model.
     *
     * @param text the canonical JSON text; non-null
     * @return the parsed value
     * @throws SemanticIrTextDecodeException on any transport-level violation
     */
    public static Value parse(String text) {
        Objects.requireNonNull(text, "text must not be null");
        Parser parser = new Parser(text);
        Value value = parser.parseValue();
        parser.skipWhitespace();
        if (!parser.atEnd()) {
            throw parser.err("trailing content after the top-level value");
        }
        return value;
    }

    private static final class Parser extends JsonScan.CharCursor {

        Parser(String text) {
            super(text);
        }

        @Override
        public SemanticIrTextDecodeException err(String reason) {
            return new SemanticIrTextDecodeException(
                reason + " at offset " + pos + " in canonical JSON text");
        }

        Value parseValue() {
            skipWhitespace();
            if (atEnd()) {
                throw err("unexpected end of input (expected a value)");
            }
            char c = peek();
            return switch (c) {
                case '{' -> parseObject();
                case '[' -> parseArray();
                case '"' -> parseString();
                case 't' -> parseLiteral("true", new Bool(true));
                case 'f' -> parseLiteral("false", new Bool(false));
                case 'n' -> parseLiteral("null", Null.INSTANCE);
                default -> {
                    if (c == '-' || (c >= '0' && c <= '9') || c == 'N' || c == 'I') {
                        yield parseNumber();
                    }
                    throw err("unexpected character '" + printable(c) + "' (expected a value)");
                }
            };
        }

        Value parseNumber() {
            int start = pos;
            while (!atEnd()) {
                char c = peek();
                if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                        || c == '-' || c == '+' || c == '.' || c == 'x' || c == 'X'
                        || c == 'p' || c == 'P') {
                    pos++;
                } else {
                    break;
                }
            }
            String token = text.substring(start, pos);
            if (token.isEmpty()) {
                throw err("expected a number");
            }
            if (token.equals("NaN")) {
                return new Num(Double.NaN);
            }
            if (token.equals("Infinity")) {
                return new Num(Double.POSITIVE_INFINITY);
            }
            if (token.equals("-Infinity")) {
                return new Num(Double.NEGATIVE_INFINITY);
            }
            if (token.startsWith("0x") || token.startsWith("-0x") || token.startsWith("0X")
                    || token.startsWith("-0X")) {
                if (!HEX_FLOAT.matcher(token).matches()) {
                    throw err("malformed hex float \"" + token + "\"");
                }
                double d = Double.parseDouble(token);
                String canonical = Double.toHexString(d);
                if (!canonical.equals(token)) {
                    throw err("non-canonical hex float \"" + token + "\" (the unique canonical "
                        + "spelling is \"" + canonical + "\")");
                }
                return new Num(d);
            }
            if (token.matches("-?[0-9]+")) {
                try {
                    return new Int(Integer.parseInt(token));
                } catch (NumberFormatException e) {
                    throw err("integer \"" + token + "\" is outside the canonical signed32 range");
                }
            }
            throw err("non-canonical number \"" + token + "\" (canonical JSON admits decimal "
                + "signed32 integers and unique IEEE-754 hex floats only)");
        }

        Str parseString() {
            if (peek() != '"') {
                throw err("expected a string");
            }
            pos++;
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
                    char esc = text.charAt(pos++);
                    switch (esc) {
                        case '"' -> sb.append('"');
                        case '\\' -> sb.append('\\');
                        case '/' -> sb.append('/');
                        case 'b' -> sb.append('\b');
                        case 'f' -> sb.append('\f');
                        case 'n' -> sb.append('\n');
                        case 'r' -> sb.append('\r');
                        case 't' -> sb.append('\t');
                        case 'u' -> sb.append(readHexEscape());
                        default -> throw err("invalid string escape \\" + printable(esc));
                    }
                } else if (c < 0x20) {
                    throw err("raw control character 0x" + Integer.toHexString(c)
                        + " inside a string (must be escaped)");
                } else {
                    sb.append(c);
                }
            }
            String result = sb.toString();
            validateParsedScalars(result);
            return new Str(result);
        }

        char readHexEscape() {
            if (pos + 4 > text.length()) {
                throw err("truncated \\u escape");
            }
            int value = 0;
            for (int i = 0; i < 4; i++) {
                int digit = Character.digit(text.charAt(pos + i), 16);
                if (digit < 0) {
                    throw err("invalid \\u escape digit");
                }
                value = (value << 4) | digit;
            }
            pos += 4;
            return (char) value;
        }

        void validateParsedScalars(String s) {
            for (int i = 0; i < s.length(); i++) {
                char c = s.charAt(i);
                if (Character.isHighSurrogate(c)) {
                    if (i + 1 >= s.length() || !Character.isLowSurrogate(s.charAt(i + 1))) {
                        throw err("unpaired high surrogate in a string (DEAL strings must be "
                            + "Unicode scalars)");
                    }
                    i++;
                } else if (Character.isLowSurrogate(c)) {
                    throw err("unpaired low surrogate in a string (DEAL strings must be "
                        + "Unicode scalars)");
                }
            }
        }

        Value parseArray() {
            pos++; // '['
            List<Value> items = new ArrayList<>();
            skipWhitespace();
            if (!atEnd() && peek() == ']') {
                pos++;
                return new Arr(items);
            }
            while (true) {
                skipWhitespace();
                items.add(parseValue());
                skipWhitespace();
                if (atEnd()) {
                    throw err("unterminated array");
                }
                char c = peek();
                if (c == ',') {
                    pos++;
                } else if (c == ']') {
                    pos++;
                    return new Arr(items);
                } else {
                    throw err("expected ',' or ']' in array");
                }
            }
        }

        Value parseObject() {
            pos++; // '{'
            List<Entry> entries = new ArrayList<>();
            skipWhitespace();
            if (!atEnd() && peek() == '}') {
                pos++;
                return new Obj(entries);
            }
            while (true) {
                skipWhitespace();
                if (atEnd() || peek() != '"') {
                    throw err("expected a string key in object");
                }
                Str key = parseString();
                skipWhitespace();
                if (atEnd() || peek() != ':') {
                    throw err("expected ':' after object key \"" + key.value() + "\"");
                }
                pos++;
                skipWhitespace();
                Value value = parseValue();
                for (Entry existing : entries) {
                    if (existing.key().equals(key.value())) {
                        throw err("duplicate object key \"" + key.value() + "\"");
                    }
                }
                entries.add(new Entry(key.value(), value));
                skipWhitespace();
                if (atEnd()) {
                    throw err("unterminated object");
                }
                char c = peek();
                if (c == ',') {
                    pos++;
                } else if (c == '}') {
                    pos++;
                    return new Obj(entries);
                } else {
                    throw err("expected ',' or '}' in object");
                }
            }
        }

        static String printable(char c) {
            return c >= 0x20 && c < 0x7f ? String.valueOf(c)
                : String.format("\\u%04x", (int) c);
        }
    }
}
