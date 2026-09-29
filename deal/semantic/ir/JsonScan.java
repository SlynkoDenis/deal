package deal.semantic.ir;

/**
 * The shared RFC-8259 scanner cores of the JSON parsers
 * ({@code SharedStdlibSemantics}, {@code JvmRuntime},
 * {@code CanonicalJson}, the LuaJIT async-export invoker): the cursor
 * operations, the whitespace/literal/string/hex-escape scans, and the
 * signed32 integer-range decision. Value production stays in each parser's
 * own reader; the hooks build the parser's own failure type.
 */
public final class JsonScan {

    private JsonScan() {
    }

    private static final String REASON_UNEXPECTED_CHARACTER = "unexpected character";
    private static final String REASON_UNTERMINATED_STRING = "unterminated string";
    private static final String REASON_INVALID_ESCAPE = "invalid escape";
    private static final String REASON_UNPAIRED_SURROGATE_ESCAPE =
        "unpaired surrogate escape";
    private static final String REASON_INVALID_NUMBER = "invalid number";
    private static final String REASON_LEADING_ZERO = "leading zero";
    private static final String REASON_UNEXPECTED_END = "unexpected end of input";

    /**
     * The code-point cursor and scanner of a parser over
     * {@code int[]} code points, tracking the 1-based UTF-8 byte offset of
     * the current scan position.
     */
    public abstract static class CodePointCursor {

        private final int[] codePoints;
        private int position;
        private long bytesConsumed;

        protected CodePointCursor(int[] codePoints) {
            this.codePoints = codePoints;
        }

        /** The parser's own failure for one pinned reason. */
        public abstract RuntimeException failure(String reason);

        public final boolean atEnd() {
            return position >= codePoints.length;
        }

        public final int peek() {
            return position < codePoints.length ? codePoints[position] : -1;
        }

        public final void advance() {
            bytesConsumed += utf8Length(codePoints[position]);
            position++;
        }

        /** The 1-based UTF-8 byte offset of the current scan position. */
        public final long offsetOfCurrent() {
            return bytesConsumed + 1;
        }

        public final void skipWs() {
            while (!atEnd() && isWs(peek())) {
                advance();
            }
        }

        public final <T> T parseLiteral(String word, T value) {
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

        /** Exactly four hex digits; a non-hex digit or end of input is an invalid escape. */
        public final int parseHex4() {
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

        public final String parseString() {
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
                                // following four-hex-digit low surrogate escape.
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

        /**
         * The scanned number token: the raw text, whether the lexical form
         * is an integer, and the scan start/negative facts the signed32
         * range decision needs.
         */
        public record NumberScan(String text, boolean integerForm, int start,
                                 boolean negative) {
        }

        /** Scans one RFC-8259 number token; the value production stays with the caller. */
        public final NumberScan parseNumberText() {
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
            return new NumberScan(new String(codePoints, start, position - start),
                integerForm, start, negative);
        }

        /**
         * The exact signed32 value of an integer-form scan
         * ({@code -0} normalizes to {@code 0}), or {@code null} when the
         * lexically valid integer is outside the signed32 range.
         */
        public final Integer exactInt32OrNull(NumberScan scan) {
            int digitsStart = scan.start() + (scan.negative() ? 1 : 0);
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
                long limit = scan.negative() ? 2147483648L : 2147483647L;
                outOfRange = significant > limit;
            } else {
                outOfRange = false;
            }
            if (outOfRange) {
                return null;
            }
            // Exact digit accumulation: at most 10 significant digits, so
            // the long value is exact; "-0" yields 0.
            long value = 0L;
            for (int i = digitsStart; i < position; i++) {
                value = value * 10 + (codePoints[i] - '0');
            }
            if (scan.negative()) {
                value = -value;
            }
            return (int) value;
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
    }

    /**
     * The character cursor and scanner of a parser over {@code String}
     * text.
     */
    public abstract static class CharCursor {

        protected final String text;
        protected int pos;

        protected CharCursor(String text) {
            this.text = text;
        }

        /** The parser's own failure for one pinned reason. */
        public abstract RuntimeException err(String reason);

        public final boolean atEnd() {
            return pos >= text.length();
        }

        public final char peek() {
            return text.charAt(pos);
        }

        public final void skipWhitespace() {
            while (!atEnd()) {
                char c = peek();
                if (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
                    pos++;
                } else {
                    return;
                }
            }
        }

        public final boolean isDelimiter(char c) {
            return c == ' ' || c == '\t' || c == '\n' || c == '\r'
                || c == ',' || c == ']' || c == '}';
        }

        public final <T> T parseLiteral(String word, T value) {
            if (!text.startsWith(word, pos)) {
                throw err("malformed literal (expected \"" + word + "\")");
            }
            pos += word.length();
            if (!atEnd() && !isDelimiter(peek())) {
                throw err("malformed literal \"" + word + "\"");
            }
            return value;
        }
    }
}
