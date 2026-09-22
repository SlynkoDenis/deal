package deal.test;

import deal.ast.*;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.diagnostics.DiagnosticRange;
import deal.diagnostics.RangeOrigin;
import deal.lexer.*;
import deal.module.CompilationOrchestrator;
import deal.module.ExportExtractor;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.project.ProjectLocator;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;
import deal.source.ScalarSourceCursor;
import deal.types.Type;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

/**
 * The dedicated directive test battery (ISSUE-0273,
 * fixed-name-directive-events Verification 1-4, 6, 8): lexical forms,
 * the ordered anchoring machine, parser binding, the E1043(warning)/
 * E1044/E1045/E1046/E7002 contract, the exact (1,2) declaration-version
 * contract, template-embedded event rebasing, the registry delta, the
 * production {@code // @spec:} E1044 pin, and the production C FFI
 * manifest-policy pin (an unbacked {@code @extern-c} import is E2010 at
 * the import span; a manifest-backed one compiles — ISSUE-0477).
 */
public class DirectiveTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static LexResult lex(String source) {
        return new Lexer(source, "test.deal").tokenize();
    }

    private static LexResult lexFile(String source, String filename) {
        return new Lexer(source, filename).tokenize();
    }

    private static ParseResult parse(String source) {
        LexResult lex = lex(source);
        return new Parser(lex.tokens(), "test.deal",
            lex.directiveEvents()).parse();
    }

    private static ParseResult parseFile(String source, String filename) {
        LexResult lex = lexFile(source, filename);
        return new Parser(lex.tokens(), filename,
            lex.directiveEvents()).parse();
    }

    /** Full-pipeline diagnostics: lexer diagnostics plus parse result. */
    private static List<CompilerDiagnostic> fullDiags(String source) {
        LexResult lex = lex(source);
        ParseResult pr = new Parser(lex.tokens(), "test.deal",
            lex.directiveEvents()).parse();
        List<CompilerDiagnostic> all = new java.util.ArrayList<>(lex.diagnostics());
        all.addAll(pr.diagnostics());
        return all;
    }

    private static CompilerDiagnostic diagOf(List<CompilerDiagnostic> diags,
                                              String code) {
        return diags.stream().filter(d -> d.code().equals(code))
            .findFirst().orElse(null);
    }

    private static CompilerDiagnostic diagOf(ParseResult r, String code) {
        return r.diagnostics().stream()
            .filter(d -> d.code().equals(code))
            .findFirst().orElse(null);
    }

    private static boolean hasError(ParseResult r, String code) {
        return r.diagnostics().stream().anyMatch(
            d -> "error".equals(d.severity()) && d.code().equals(code));
    }

    // =========================================================================
    // Verification 1: lexical forms
    // =========================================================================

    static void testLexicalForms() {
        System.out.println("-- Lexical forms: five names under LF/CRLF/CR/EOF --");

        for (String terminator : new String[]{"\n", "\r\n", "\r", ""}) {
            String suffix = terminator.isEmpty() ? "" : terminator + "export class C {}";
            LexResult r = lex("// @jsonable" + suffix);
            check(r.directiveEvents().size() == 1,
                "jsonable under " + esc(terminator) + ": one event, got "
                    + r.directiveEvents().size());
            if (!r.directiveEvents().isEmpty()) {
                CompilerDirective e = r.directiveEvents().get(0);
                check(e.name() == DirectiveName.JSONABLE
                        && e.trimmedArgument().equals("")
                        && e.rawArgument().equals(""),
                    "jsonable shape under " + esc(terminator));
            }
            r = lex("// @c-struct" + suffix);
            check(!r.directiveEvents().isEmpty()
                    && r.directiveEvents().get(0).name() == DirectiveName.C_STRUCT,
                "c-struct under " + esc(terminator));
            r = lex("// @c-pointer" + suffix);
            check(!r.directiveEvents().isEmpty()
                    && r.directiveEvents().get(0).name() == DirectiveName.C_POINTER,
                "c-pointer under " + esc(terminator));
            r = lex("// @extern-c" + suffix);
            check(!r.directiveEvents().isEmpty()
                    && r.directiveEvents().get(0).name() == DirectiveName.EXTERN_C,
                "extern-c under " + esc(terminator));
            r = lex("// @deal-version 1.2" + suffix);
            check(!r.directiveEvents().isEmpty()
                    && r.directiveEvents().get(0).name() == DirectiveName.DEAL_VERSION
                    && r.directiveEvents().get(0).trimmedArgument().equals("1.2")
                    && r.directiveEvents().get(0).rawArgument().equals(" 1.2"),
                "deal-version raw/trimmed under " + esc(terminator));
        }

        // Delimiter-free @deal-version1.2 (D2).
        LexResult r = lex("// @deal-version1.2\nexport class C {}");
        check(!r.directiveEvents().isEmpty()
                && r.directiveEvents().get(0).name() == DirectiveName.DEAL_VERSION
                && r.directiveEvents().get(0).trimmedArgument().equals("1.2"),
            "delimiter-free @deal-version1.2");

        // Recognized prefixes are never reclassified as unknown: the four
        // forbidden-argument forms parse to jsonable + argument, and the
        // parser's argument sweep emits E1045 at the complete comment.
        for (String form : new String[]{"@jsonablex", "@jsonable:foo",
                "@jsonable-foo", "@jsonable foo"}) {
            ParseResult pr = parse("// " + form + "\nexport class C {}");
            check(hasError(pr, "E1045"),
                form + " → E1045, got " + pr.diagnostics());
            CompilerDiagnostic d = diagOf(pr, "E1045");
            if (d != null) {
                check(d.range().origin() == RangeOrigin.SOURCE
                        && d.range().startScalarOffset() == 0,
                    form + ": E1045 at the complete comment");
            }
        }

        // Unknown names: E1044 over the recovered name range plus the
        // complete-comment note (E1044 is a lexer diagnostic).
        CompilerDiagnostic d = diagOf(fullDiags("// @foo bar\nexport class C {}"),
            "E1044");
        check(d != null, "@foo bar → E1044");
        if (d != null) {
            // 'foo' runs 4..7; the complete comment is 0..11.
            check(d.range().startScalarOffset() == 4
                    && d.range().endScalarOffset() == 7,
                "@foo bar: E1044 over the recovered name (4,7), got ("
                    + d.range().startScalarOffset() + ","
                    + d.range().endScalarOffset() + ")");
            check(d.notes().size() == 1 && d.notes().get(0).range() != null
                    && d.notes().get(0).range().startScalarOffset() == 0
                    && d.notes().get(0).range().endScalarOffset() == 11,
                "@foo bar: complete-comment note (0,11), got " + d.notes());
        }

        // Prefix of a recognized name is unknown (never silently matched).
        check(diagOf(fullDiags("// @json\nexport class C {}"), "E1044") != null,
            "@json → E1044");

        // Punctuation/empty forms.
        CompilerDiagnostic empty = diagOf(
            fullDiags("// @\nexport class C {}"), "E1044");
        check(empty != null, "// @ → E1044");
        if (empty != null) {
            check(empty.range().startScalarOffset() == 3
                    && empty.range().endScalarOffset() == 4,
                "// @: E1044 over '@' (3,4), got ("
                    + empty.range().startScalarOffset() + ","
                    + empty.range().endScalarOffset() + ")");
        }
        CompilerDiagnostic punct = diagOf(
            fullDiags("// @!-x\nexport class C {}"), "E1044");
        check(punct != null, "// @!-x → E1044");
        if (punct != null) {
            check(punct.range().startScalarOffset() == 3
                    && punct.range().endScalarOffset() == 7,
                "// @!-x: E1044 over '@!-x' (3,7), got ("
                    + punct.range().startScalarOffset() + ","
                    + punct.range().endScalarOffset() + ")");
        }

        // LF/CRLF/CR/EOF pins: the E1044 recovered range and note hold
        // under every terminator.
        for (String term : new String[]{"\n", "\r\n", "\r", ""}) {
            String src = "// @nope" + term;
            CompilerDiagnostic dd = diagOf(fullDiags(src), "E1044");
            check(dd != null, "E1044 under " + esc(term));
            if (dd != null) {
                check(dd.range().startScalarOffset() == 4
                        && dd.range().endScalarOffset() == 8
                        && dd.notes().size() == 1
                        && dd.notes().get(0).range() != null
                        && dd.notes().get(0).range().endScalarOffset() == 8,
                    "E1044 range/note under " + esc(term) + ": "
                        + dd.range() + " notes " + dd.notes());
            }
        }
    }

    private static String esc(String s) {
        return s.replace("\r", "\\r").replace("\n", "\\n");
    }

    // =========================================================================
    // Verification 2: transitions
    // =========================================================================

    static void testTransitions() {
        System.out.println("-- Transitions: anchoring machine (D3) --");

        // Immediate attachment: anchor == emitted token index ==
        // preceding count (the anchor-before-clear-before-emission
        // invariant).
        LexResult r = lex("// @jsonable\nexport class C {}");
        check(!r.directiveEvents().isEmpty()
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() != null
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == 0
                && r.directiveEvents().get(0).precedingNonCommentTokenCount() == 0
                && r.directiveEvents().get(0).declarationAnchorTokenIndex()
                    == r.directiveEvents().get(0).precedingNonCommentTokenCount(),
            "immediate attachment: anchor == emitted index == preceding count");

        // Whitespace/blank-line preservation.
        r = lex("// @jsonable\n\n\t \nexport class C {}");
        check(!r.directiveEvents().isEmpty()
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() != null
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == 0,
            "whitespace/blank lines preserve the run");

        // Ordinary comment breaks without anchoring.
        r = lex("// @jsonable\n// hello\nexport class C {}");
        check(r.directiveEvents().size() == 1
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == null,
            "ordinary comment breaks the run without anchoring");

        // File directive breaks without anchoring (and stays unanchored).
        r = lex("// @jsonable\n// @deal-version 1.2\nexport class C {}");
        check(r.directiveEvents().size() == 2
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == null
                && r.directiveEvents().get(1).declarationAnchorTokenIndex() == null,
            "file directive breaks the run without anchoring");

        // Unknown directive breaks without anchoring.
        r = lex("// @jsonable\n// @nope\nexport class C {}");
        check(r.directiveEvents().size() == 2
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == null
                && r.directiveEvents().get(1).declarationAnchorTokenIndex() == null,
            "unknown directive breaks the run without anchoring");

        // Non-declaration anchors: let, import, field, expression tokens.
        r = lex("// @jsonable\nlet x = 1;");
        check(!r.directiveEvents().isEmpty()
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() != null
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == 0,
            "let is a non-declaration anchor (index 0)");
        ParseResult pr = parse("// @jsonable\nlet x = 1;");
        check(pr.diagnostics().stream().anyMatch(
                d -> d.code().equals("E1043") && d.severity().equals("warning")),
            "non-declaration anchor produces the finalize E1043 warning");

        // EOF retention as unanchored.
        r = lex("// @jsonable");
        check(r.directiveEvents().size() == 1
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == null,
            "EOF retains the event unanchored");

        // Broken C runs never attach.
        r = lex("// @c-struct\n// @extern-c\nexport class C {}");
        check(r.directiveEvents().size() == 2
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == null
                && r.directiveEvents().get(1).declarationAnchorTokenIndex() == null,
            "@c-struct broken by @extern-c never attaches");
        r = lex("// @c-struct\n// @nope\nexport class C {}");
        check(r.directiveEvents().size() == 2
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == null,
            "@c-struct broken by an unknown directive never attaches");

        // A second declaration directive extends the run: one anchor for
        // both.
        r = lex("// @c-struct\n// @c-pointer\nexport class C {}");
        check(r.directiveEvents().size() == 2
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() != null
                && r.directiveEvents().get(0).declarationAnchorTokenIndex() == 0
                && r.directiveEvents().get(1).declarationAnchorTokenIndex() != null
                && r.directiveEvents().get(1).declarationAnchorTokenIndex() == 0,
            "a second declaration directive extends the run to one anchor");
    }

    // =========================================================================
    // Verification 3: binding
    // =========================================================================

    static void testBinding() {
        System.out.println("-- Binding (D4) --");

        // Exported class + @jsonable: JSONABLE metadata, no diagnostics.
        ParseResult r = parse("// @jsonable\nexport class C { x: int = 0; }");
        check(r.diagnostics().isEmpty(), "export class binding clean: "
            + r.diagnostics());
        ExportDeclaration ed = (ExportDeclaration) r.program().statements().get(0);
        ClassDeclaration cd = (ClassDeclaration) ed.declaration();
        check(cd.isJsonable(), "JSONABLE metadata applied");
        check(r.program().fileDirectives() != null,
            "ProgramNode carries fileDirectives");

        // Export-wrapped function: E1043 warning, no metadata.
        r = parse("// @jsonable\nexport function f(): int { return 0; }");
        check(!r.hasErrors(), "E1043 is a warning (no parse errors)");
        check(diagOf(r, "E1043") != null, "E1043 for export function");

        // Non-exported class: E1043 warning, no metadata.
        r = parse("// @jsonable\nclass C { x: int = 0; }");
        check(diagOf(r, "E1043") != null, "E1043 for standalone class");
        ClassDeclaration standalone = (ClassDeclaration) r.program()
            .statements().get(0);
        check(!standalone.isJsonable(),
            "standalone class carries no JSONABLE metadata");

        // Non-exported function.
        r = parse("// @jsonable\nfunction f(): int { return 0; }");
        check(diagOf(r, "E1043") != null, "E1043 for standalone function");

        // Non-exported async function (start token ASYNC).
        r = parse("// @jsonable\nasync function f(): int { return 0; }");
        check(diagOf(r, "E1043") != null, "E1043 for standalone async function");

        // E1043 warning-and-ignore: no synthetic C$fromJson/C$toJson
        // symbols and no metadata (ExportExtractor never sees a
        // jsonable class).
        r = parse("// @jsonable\nfunction f(): int { return 0; }");
        Map<String, Type> exports = new ExportExtractor("m", false)
            .extract(r.program());
        check(!exports.containsKey("C$fromJson"),
            "no synthetic C$fromJson for an invalid binding");
        check(!exports.containsKey("C$toJson"),
            "no synthetic C$toJson for an invalid binding");

        // C-marker cardinality 0/1/2 in extern-C files → E7002 at the
        // class span (see ParserTest.testCMarkerCardinality); markers
        // outside extern-C → E1046 at the directive range.
        r = parse("// @c-pointer\nexport class C { x: int = 0; }");
        check(hasError(r, "E1046"), "marker outside extern-C → E1046");
        CompilerDiagnostic d = diagOf(r, "E1046");
        if (d != null) {
            check(d.range().startScalarOffset() == 0
                    && d.range().endScalarOffset() == 13,
                "E1046 at the directive range (0,13) — the complete "
                    + "'// @c-pointer' comment, got ("
                    + d.range().startScalarOffset() + ","
                    + d.range().endScalarOffset() + ")");
        }
        // No jsonable metadata on the marker-bearing class.
        ed = (ExportDeclaration) r.program().statements().get(0);
        cd = (ClassDeclaration) ed.declaration();
        check(!cd.isJsonable() && cd.directives().contains(
                DeclarationDirective.C_POINTER),
            "C marker recorded, no jsonable metadata");

        // Markers on non-class declarations in a non-extern-C file:
        // E1046.
        r = parse("// @c-struct\nexport function f(): int { return 0; }");
        check(hasError(r, "E1046"),
            "marker on a function outside extern-C → E1046");

        // Invalid metadata never reaches generation: the only jsonable
        // classes are the valid export-class bindings.
        r = parse("// @jsonable\nclass Bad { x: int = 0; }");
        check(!((ClassDeclaration) r.program().statements().get(0))
                .isJsonable(),
            "invalid metadata never applied");
    }

    // =========================================================================
    // Declaration-file binding
    // =========================================================================

    static void testDeclarationFileBinding() {
        System.out.println("-- Declaration-file binding (D4) --");

        // @jsonable on an export class in a .d.deal file: no metadata,
        // no E1043, no synthetic C$fromJson/C$toJson; explicit JSON
        // signatures preserved.
        String decl = "// @jsonable\nexport class C { x: int = 0; }\n"
            + "export function C$fromJson(s: string): C | null;\n"
            + "export function C$toJson(c: C): string;";
        ParseResult r = parseFile(decl, "lib.d.deal");
        check(r.diagnostics().isEmpty(),
            "declaration-file binding clean: " + r.diagnostics());
        ExportDeclaration ed = (ExportDeclaration) r.program().statements().get(0);
        ClassDeclaration cd = (ClassDeclaration) ed.declaration();
        check(!cd.isJsonable(), "no JSONABLE metadata in a .d.deal file");
        Map<String, Type> exports = new ExportExtractor("lib", true)
            .extract(r.program());
        check(exports.containsKey("C$fromJson")
                && exports.containsKey("C$toJson"),
            "explicit JSON signatures preserved in the export map: "
                + exports.keySet());

        // Unattached @jsonable in a .d.deal file still warns E1043.
        r = parseFile("// @jsonable\nlet x = 1;", "lib.d.deal");
        check(diagOf(r, "E1043") != null,
            "unattached @jsonable in a .d.deal file warns E1043");

        // Non-class attachment warns E1043 with no metadata.
        r = parseFile("// @jsonable\nexport function f(): int { return 0; }",
            "lib.d.deal");
        check(diagOf(r, "E1043") != null,
            "non-class attachment in a .d.deal file warns E1043");

        // The E1045 argument rule still fires in .d.deal files.
        r = parseFile("// @jsonable:foo\nexport class C { x: int = 0; }",
            "lib.d.deal");
        check(hasError(r, "E1045"),
            "@jsonable:foo in a .d.deal file still produces E1045");
    }

    // =========================================================================
    // Version contract (D7)
    // =========================================================================

    static void testVersionContract() {
        System.out.println("-- Declaration-version contract (D7) --");

        for (String value : new String[]{"1.2", "01.02", "1.02"}) {
            ParseResult r = parse("// @deal-version " + value
                + "\nexport class C { x: int = 0; }");
            check(r.diagnostics().isEmpty(),
                "@deal-version " + value + " accepted: " + r.diagnostics());
            check(r.program().fileDirectives().declaredDealVersion() != null
                    && r.program().fileDirectives().declaredDealVersion()
                        .equals(new DealVersion(1, 2)),
                value + " parses to (1,2)");
        }

        // Omission.
        ParseResult r = parse("export class C { x: int = 0; }");
        check(r.diagnostics().isEmpty() && r.program().fileDirectives()
                .declaredDealVersion() == null
                && r.program().fileDirectives().effectiveDealVersion()
                    .equals(new DealVersion(1, 2)),
            "omission defaults to effective (1,2)");

        // Empty / multi-value → E1045.
        check(hasError(parse("// @deal-version\nexport class C { x: int = 0; }"),
            "E1045"), "empty argument → E1045");
        check(hasError(parse("// @deal-version 1.2 1.3\nexport class C { x: int = 0; }"),
            "E1045"), "multi-value argument → E1045");

        // Malformed → E1046.
        for (String bad : new String[]{"1.2.3", "1", "1.", ".2", "abc", "1,2",
                "99999999999999999999999.2"}) {
            check(hasError(parse("// @deal-version " + bad
                    + "\nexport class C { x: int = 0; }"), "E1046"),
                "malformed '" + bad + "' → E1046");
        }

        // Older/newer → E1046.
        for (String bad : new String[]{"1.0", "1.1", "0.9", "1.3", "2.0"}) {
            check(hasError(parse("// @deal-version " + bad
                    + "\nexport class C { x: int = 0; }"), "E1046"),
                "unsupported '" + bad + "' → E1046");
        }

        // Duplicate and post-token → E1046.
        check(hasError(parse("// @deal-version 1.2\n// @deal-version 1.2"),
            "E1046"), "duplicate → E1046");
        check(hasError(parse("class A { x: int = 0; }\n// @deal-version 1.2"),
            "E1046"), "post-token → E1046");

        // No migration registry exists or is consulted: every parsed value
        // other than (1,2) fails, nothing is migrated.
        check(hasError(parse("// @deal-version 1.1\nexport class C { x: int = 0; }"),
            "E1046"), "1.1 is never migrated");

        // Extern-c file-directive failures.
        check(hasError(parse("// @extern-c\nexport class C { x: int = 0; }"),
            "E1046"), "@extern-c in an implementation file → E1046");
        check(hasError(parseFile(
                "// @extern-c\n// @extern-c\nexport class C { x: int = 0; }",
                "m.d.deal"),
            "E1046"), "duplicate @extern-c → E1046");
        check(hasError(parseFile(
                "export class C { x: int = 0; }\n// @extern-c", "m.d.deal"),
            "E1046"), "@extern-c after a declaration → E1046");
        check(hasError(parseFile(
                "// @extern-c\nimport * as m from \"./m\"\nexport class C { x: int = 0; }",
                "m.d.deal"),
            "E1046"), "@extern-c with a later import → E1046");
    }

    // =========================================================================
    // Template-embedded events (D10)
    // =========================================================================

    static void testTemplateEmbedded() {
        System.out.println("-- Template-embedded events (D10) --");

        // Recognized jsonable inside an interpolation: one E1043 warning
        // at the rebased complete-comment range, no metadata.
        String src = "let s = `${ // @jsonable\n x}`;";
        ParseResult r = parse(src);
        long e1043 = r.diagnostics().stream()
            .filter(d -> d.code().equals("E1043")).count();
        check(e1043 == 1,
            "exactly one E1043, got " + e1043 + ": " + r.diagnostics());
        CompilerDiagnostic w = diagOf(r, "E1043");
        if (w != null) {
            check(w.severity().equals("warning"),
                "E1043 severity warning, got " + w.severity());
            check(w.range().origin() == RangeOrigin.SOURCE
                    && w.range().startScalarOffset() == 12
                    && w.range().endScalarOffset() == 24,
                "E1043 at the rebased complete comment (12,24), got ("
                    + w.range().startScalarOffset() + ","
                    + w.range().endScalarOffset() + ")");
        }

        // Unknown name inside an interpolation: E1044 primary AND note
        // ranges in original-source coordinates (D10.8).
        String src2 = "let s = `${ // @nope\n x}`;";
        ParseResult r2 = parse(src2);
        CompilerDiagnostic e1044 = diagOf(r2, "E1044");
        check(e1044 != null, "embedded E1044 present");
        if (e1044 != null) {
            check(e1044.range().origin() == RangeOrigin.SOURCE
                    && e1044.range().startScalarOffset() == 16
                    && e1044.range().endScalarOffset() == 20,
                "E1044 primary at the rebased recovered name (16,20), got ("
                    + e1044.range().startScalarOffset() + ","
                    + e1044.range().endScalarOffset() + ")");
            check(e1044.notes().size() == 1
                    && e1044.notes().get(0).range() != null
                    && e1044.notes().get(0).range().origin()
                        == RangeOrigin.SOURCE
                    && e1044.notes().get(0).range().startScalarOffset() == 12
                    && e1044.notes().get(0).range().endScalarOffset() == 20,
                "E1044 note in original-source coordinates (12,20): "
                    + e1044.notes());
        }

        // @deal-version inside an interpolation: E1046 placement with a
        // truthful preceding count.
        ParseResult r3 = parse("let s = `${ // @deal-version 1.2\n x}`;");
        check(hasError(r3, "E1046"),
            "embedded @deal-version → E1046 placement");

        // A C marker inside an interpolation: E1046 (no extern-C).
        ParseResult r4 = parse("let s = `${ // @c-struct\n x}`;");
        CompilerDiagnostic e1046c = diagOf(r4, "E1046");
        check(e1046c != null, "embedded C marker → E1046");
        if (e1046c != null) {
            check(e1046c.range().startScalarOffset() == 12
                    && e1046c.range().endScalarOffset() == 24,
                "embedded C-marker E1046 at the rebased range (12,24)");
        }

        // Nested templates bubble their events up.
        ParseResult r5 = parse("let s = `${ `${ // @jsonable\n x}` }`;");
        long nested1043 = r5.diagnostics().stream()
            .filter(d -> d.code().equals("E1043")).count();
        check(nested1043 == 1,
            "nested template bubbles exactly one E1043, got " + nested1043
                + ": " + r5.diagnostics());

        // No sub-event ever binds to a declaration (no metadata).
        boolean jsonable = false;
        for (StatementNode stmt : r.program().statements()) {
            if (stmt instanceof ClassDeclaration c && c.isJsonable()) {
                jsonable = true;
            }
        }
        check(!jsonable, "no merged event produces metadata");
    }

    // =========================================================================
    // Registry (D6)
    // =========================================================================

    static void testRegistry() {
        System.out.println("-- Diagnostic registry (D6) --");

        check(DiagnosticCode.fromCode("E1043") != null, "E1043 registered");
        check(DiagnosticCode.fromCode("E1044") != null, "E1044 registered");
        check(DiagnosticCode.fromCode("E1045") != null, "E1045 registered");
        check(DiagnosticCode.fromCode("E1046") != null, "E1046 registered");
        check(DiagnosticCode.fromCode("E7002") != null, "E7002 registered");
        check(DiagnosticCode.fromCode("E1052") == null, "E1052 retired");
        check(DiagnosticCode.fromCode("E1053") == null, "E1053 retired");
        check(DiagnosticCode.fromCode("E1054") == null, "E1054 retired");
        check(DiagnosticCode.fromCode("E1055") == null, "E1055 retired");
        check(DiagnosticCode.E1043.phase() == DiagnosticCode.Phase.FRONTEND
                && DiagnosticCode.E1044.phase() == DiagnosticCode.Phase.FRONTEND
                && DiagnosticCode.E1045.phase() == DiagnosticCode.Phase.FRONTEND
                && DiagnosticCode.E1046.phase() == DiagnosticCode.Phase.FRONTEND
                && DiagnosticCode.E7002.phase() == DiagnosticCode.Phase.FRONTEND,
            "E1043-E1046/E7002 are FRONTEND");
    }

    // =========================================================================
    // Production @spec pin (D8/D12): metadata is not stripped in production
    // =========================================================================

    static void testProductionSpecHeaderE1044() throws Exception {
        System.out.println("-- Production // @spec: → E1044 --");

        Path tmp = Files.createTempDirectory("deal_directive_prod_");
        try {
            Path srcDir = tmp.resolve("src");
            Files.createDirectories(srcDir);
            Files.writeString(tmp.resolve("deal.json"),
                "{\"languageVersion\": \"1.2\"}\n");
            Files.writeString(srcDir.resolve("main.deal"),
                "// @spec: Lexical elements — comment semantics\n"
                    + "export function main(): null { return null; }\n");

            // ISSUE-0269: the tolerant DealConfig reader is retired; the
            // test-only isolated-phase overload synthesizes the internal
            // ProjectContext, and this manifest declares no externals.
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                srcDir.resolve("main.deal"), tmp.resolve("build"),
                false, false, false, Backend.LUAJIT,
                Map.of(),
                List.of(srcDir), Path.of(".").toAbsolutePath().normalize());
            boolean success = orchestrator.compile();
            check(!success, "the production compile fails on // @spec:");
            List<CompilerDiagnostic> diags = orchestrator.diagnostics();
            long e1044 = diags.stream()
                .filter(d -> d.code().equals("E1044")).count();
            check(e1044 == 1,
                "production // @spec: emits exactly one E1044, got "
                    + e1044 + ": " + diags);
            CompilerDiagnostic d = diags.stream()
                .filter(x -> x.code().equals("E1044"))
                .findFirst().orElse(null);
            if (d != null) {
                // '@spec:' — the recovered unknown name runs from offset
                // 3+... the comment starts at 0: "// @spec: ..." — '@' at
                // 3, 'spec' at 4..8.
                check(d.range().startScalarOffset() == 4
                        && d.range().endScalarOffset() == 8,
                    "E1044 at the recovered name (4,8), got ("
                        + d.range().startScalarOffset() + ","
                        + d.range().endScalarOffset() + ")");
            }
        } finally {
            try {
                Files.walk(tmp).sorted(Comparator.reverseOrder())
                    .forEach(f -> { try { Files.deleteIfExists(f); }
                        catch (IOException ignored) { } });
            } catch (IOException ignored) { }
        }
    }

    // =========================================================================
    // Production C FFI manifest policy (docs/spec-v1.2.md:1891)
    // =========================================================================

    /**
     * The production emission site behind the promoted
     * {@code ffi-manifest-missing-native-library-rejected.deal} E2010
     * pin (ISSUE-0477): the production module resolver
     * ({@code CompilationOrchestrator.ModuleResolverImpl}) rejects an
     * import of a C FFI declaration file ({@code .d.deal} with
     * {@code // @extern-c}) that no externals entry declares with
     * {@code nativeLibrary} — E2010 at the import span via the
     * checker's manifest-policy mapping. The same import through an
     * externals entry carrying {@code nativeLibrary} compiles; an entry
     * that omits {@code nativeLibrary} is the invalid-manifest-policy
     * rejection again.
     */
    static void testProductionCffiManifestPolicy() throws Exception {
        System.out.println("-- Production C FFI manifest policy: E2010 at the import --");

        Path tmp = Files.createTempDirectory("deal_cffi_manifest_");
        try {
            String importLine = "import * as ffi from \"./ffi_math\";";
            // Case 1 (the promoted conformance pin's exact shape): an
            // import of a @extern-c declaration file that no externals
            // entry declares with nativeLibrary is rejected with exactly
            // one E2010 at the import span.
            Files.writeString(tmp.resolve("deal.json"),
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\".\"]}\n");
            Files.writeString(tmp.resolve("ffi_math.d.deal"),
                "// @extern-c\n\nexport function add(a: int, b: int): int;\n");
            Path entry = tmp.resolve("main.deal");
            Files.writeString(entry,
                importLine + "\n\n"
                    + "export function test_ffi_add(): int {\n"
                    + "  return ffi.add(1, 2);\n"
                    + "}\n\n"
                    + "export function main(): null { return null; }\n");
            CompilationOrchestrator orchestrator = locateOrchestrator(entry);
            if (orchestrator == null) {
                return;
            }
            boolean ok = orchestrator.compile();
            check(!ok, "the unlisted extern-C import fails the production compile");
            List<CompilerDiagnostic> diags = orchestrator.diagnostics();
            List<CompilerDiagnostic> e2010s = diags.stream()
                .filter(d -> "E2010".equals(d.code()))
                .toList();
            check(e2010s.size() == 1,
                "the unlisted extern-C import emits exactly one E2010, got "
                    + e2010s.size() + ": " + diags);
            if (e2010s.size() == 1) {
                CompilerDiagnostic d = e2010s.get(0);
                check(d.range().startScalarOffset() == 0,
                    "E2010 starts at the import statement (offset 0), got "
                        + d.range().startScalarOffset());
                check(d.range().endScalarOffset() >= importLine.length(),
                    "E2010 covers the whole import statement ("
                        + importLine.length() + " chars), got end "
                        + d.range().endScalarOffset());
            }

            // Case 2: the same declaration imported through an
            // externals entry carrying nativeLibrary compiles with no
            // E2010 (the manifest policy's passing shape).
            Files.writeString(tmp.resolve("deal.json"),
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\".\"],"
                    + " \"externals\": {\"ffi\": {\"declaration\":"
                    + " \"ffi_math.d.deal\", \"nativeLibrary\": \"math\"}}}\n");
            Files.writeString(entry,
                "import * as ffi from \"ffi\";\n\n"
                    + "export function test_ffi_add(): int {\n"
                    + "  return ffi.add(1, 2);\n"
                    + "}\n\n"
                    + "export function main(): null { return null; }\n");
            CompilationOrchestrator backed = locateOrchestrator(entry);
            if (backed == null) {
                return;
            }
            boolean backedOk = backed.compile();
            check(backedOk,
                "the manifest-backed extern-C import compiles: "
                    + backed.diagnostics());
            check(backed.diagnostics().stream()
                    .noneMatch(d -> "E2010".equals(d.code())),
                "the manifest-backed extern-C import emits no E2010: "
                    + backed.diagnostics());

            // ISSUE-0643 P10 item 2: the same fixture through the
            // release-owned production invocation fails closed with
            // E6005 SHARED_EMITTER_COVERAGE (HOST_MODULE_IMPORT) and
            // stages nothing (the FFI realization is the FFI child's).
            ByteArrayOutputStream prodErr = new ByteArrayOutputStream();
            PrintStream originalErr = System.err;
            int prodExit;
            try {
                System.setErr(new PrintStream(prodErr, true,
                    java.nio.charset.StandardCharsets.UTF_8));
                prodExit = deal.Main.run(new String[]{"compile",
                    entry.toString(), "--output",
                    tmp.resolve("prod_out").toString()});
                System.err.flush();
            } finally {
                System.setErr(originalErr);
            }
            String prodText = prodErr.toString(
                java.nio.charset.StandardCharsets.UTF_8);
            check(prodExit != 0 && prodText.contains("E6005")
                    && prodText.contains("SHARED_EMITTER_COVERAGE")
                    && prodText.contains("HOST_MODULE_IMPORT"),
                "the release-owned production invocation fails the extern-C "
                    + "fixture closed with E6005 SHARED_EMITTER_COVERAGE "
                    + "(HOST_MODULE_IMPORT): " + prodText);
            check(!Files.exists(tmp.resolve("prod_out")),
                "the production failure stages no artifact under the "
                    + "probe output");

            // Case 3: an externals entry that declares the file without
            // nativeLibrary is the invalid-manifest-policy rejection —
            // rejected at locate time by ProjectLocator step 4(b)
            // (ISSUE-0508): exactly one E2010 at the externals entry's
            // manifest value range naming the nativeLibrary policy, and
            // no context is published (a C FFI entry must include
            // nativeLibrary, docs/spec-v1.2.md:1891).
            Files.writeString(tmp.resolve("deal.json"),
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\".\"],"
                    + " \"externals\": {\"ffi\": {\"declaration\":"
                    + " \"ffi_math.d.deal\"}}}\n");
            ProjectLocator.LocateResult unbacked = ProjectLocator.locate(
                entry.toString(), null);
            check(unbacked.e2010() != null,
                "the nativeLibrary-less externals entry is rejected at "
                    + "locate time with an E2010");
            check(unbacked.cliDiagnostic() == null
                    && unbacked.context() == null,
                "the nativeLibrary-less externals entry publishes exactly "
                    + "the E2010 (no cliDiagnostic, no context)");
            if (unbacked.e2010() != null) {
                check("E2010".equals(unbacked.e2010().code()),
                    "the locate-time rejection code is exactly E2010: "
                        + unbacked.e2010().code());
                check(unbacked.e2010().message().contains(
                        "without a nativeLibrary"),
                    "the locate-time E2010 names the nativeLibrary policy: "
                        + unbacked.e2010().message());
            }
        } finally {
            try {
                Files.walk(tmp).sorted(Comparator.reverseOrder())
                    .forEach(f -> { try { Files.deleteIfExists(f); }
                        catch (IOException ignored) { } });
            } catch (IOException ignored) { }
        }
    }

    /**
     * Locates the production context for {@code entry} and builds the
     * context-driven orchestrator, or null after a failing check. The
     * compile resolves the harness invocation (ISSUE-0643 P10 item 3):
     * the suite's extern-C fixtures carry a HOST-kind declaration import
     * the release-owned production invocation fails closed, while the
     * suite's subject — the directive/manifest policy — is
     * arm-independent.
     */
    private static CompilationOrchestrator locateOrchestrator(Path entry) {
        ProjectLocator.LocateResult located = ProjectLocator.locate(
            entry.toString(), null);
        check(located.context() != null && located.e2010() == null
                && located.cliDiagnostic() == null,
            "the manifest locates a context: "
                + (located.e2010() != null
                    ? located.e2010() : located.cliDiagnostic()));
        if (located.context() == null) {
            return null;
        }
        CompilerInvocation invocation = ConformanceHarnessMetadata.invocation(
            deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32);
        return new CompilationOrchestrator(located.context(),
            entry.toAbsolutePath().normalize(), false, false, false, false,
            null, invocation);
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Directive Test Battery (ISSUE-0273) ===\n");

        testLexicalForms();
        testTransitions();
        testBinding();
        testDeclarationFileBinding();
        testVersionContract();
        testTemplateEmbedded();
        testRegistry();
        testProductionSpecHeaderE1044();
        testProductionCffiManifestPolicy();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
