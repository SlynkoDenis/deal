package deal.test;

import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticFormatter;
import deal.diagnostics.DiagnosticStructuredOutput;
import deal.module.CompilationOrchestrator;
import deal.project.CliOverrides;
import deal.project.ProjectLocator;
import deal.semantic.CompilerInvocation;
import deal.semantic.ir.SemanticProfile;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

/**
 * The test-scope harness compile entry (ISSUE-0643; design source
 * {@code production-project-emission-and-atomic-cutover} P10 item 3 — the
 * gate-path allocation, mechanism 1).
 *
 * <p>{@link #run(String[])} mirrors {@code deal.Main}'s CLI surface — the
 * entry path, {@code --backend lua|luajit|jvm|js}, {@code --output
 * <dir>}, {@code --dump-ir}, {@code --source-map}, {@code --verbose}, and
 * {@code --diagnostics-json} — but resolves the <b>harness</b> invocation
 * ({@code COMMON_SHADOW} / {@code DEAL_V1_2_INT32}, {@link
 * ConformanceHarnessMetadata#invocation}) in place of the release-owned
 * production invocation. Every compile it drives therefore keeps the
 * harness arm (phase 3.7 route planning, the per-module route dispatch,
 * the retained loops and counters, the mixed-edge validation, the
 * per-module production emission, and the retained source-map behavior),
 * exactly as the gate paths it serves asserted before the ISSUE-0643
 * phase-4 dispatch activated the production arm.</p>
 *
 * <p><b>Scope.</b> This class is {@code test/**} only: it is compiled
 * into {@code build} by {@code run_tests.sh}'s {@code TEST_SOURCES} list
 * and is outside the production source set. It adds no CLI option to
 * {@code deal.Main}, changes no {@code deal/**} source, and never selects
 * the production arm — a release-owned production compile is reachable
 * only through {@code deal.Main} (or an orchestrator constructed with the
 * release-owned record).</p>
 */
public final class HarnessCompileEntry {

    private HarnessCompileEntry() {
    }

    /**
     * The CLI-equivalent harness compile: the same arguments
     * {@code deal.Main} accepts, the harness invocation in place of the
     * release-owned production record.
     *
     * @param args the command line ({@code compile <entry> [--backend
     *             lua|luajit|jvm|js] [--output <dir>] [--dump-ir]
     *             [--source-map] [--verbose] [--diagnostics-json
     *             <path>]}); non-null
     * @return the process exit code (0 on success, 1 on a compile or
     *         CLI failure, 2 on an internal error)
     * @throws IOException on an escaping I/O failure
     */
    public static int run(String[] args) throws IOException {
        if (args.length == 0) {
            System.err.println("deal: missing command");
            return 1;
        }
        if (!args[0].equals("compile")) {
            System.err.println("deal: unknown command '" + args[0] + "'");
            return 1;
        }

        String[] remaining = Arrays.copyOfRange(args, 1, args.length);
        String entryPath = null;
        String outputOverride = null;
        String backendName = null;
        boolean verbose = false;
        boolean dumpIr = false;
        boolean sourceMap = false;
        Path diagnosticsJsonPath = null;

        int i = 0;
        while (i < remaining.length) {
            String arg = remaining[i];
            switch (arg) {
                case "--output", "-o" -> {
                    if (i + 1 >= remaining.length) {
                        System.err.println(
                            "deal: --output requires a directory argument");
                        return 1;
                    }
                    outputOverride = remaining[++i];
                }
                case "--backend" -> {
                    if (i + 1 >= remaining.length) {
                        System.err.println("deal: --backend requires a backend"
                            + " name (lua|luajit|jvm|js)");
                        return 1;
                    }
                    backendName = remaining[++i];
                }
                case "--diagnostics-json" -> {
                    if (i + 1 >= remaining.length) {
                        System.err.println("deal: --diagnostics-json requires a"
                            + " path argument");
                        return 1;
                    }
                    diagnosticsJsonPath = Path.of(remaining[++i]);
                }
                case "--verbose", "-v" -> verbose = true;
                case "--dump-ir" -> dumpIr = true;
                case "--source-map" -> sourceMap = true;
                default -> {
                    if (arg.startsWith("-")) {
                        System.err.println("deal: unknown option '" + arg + "'");
                        return 1;
                    }
                    if (entryPath != null) {
                        System.err.println(
                            "deal: multiple entry files specified");
                        return 1;
                    }
                    entryPath = arg;
                }
            }
            i++;
        }
        if (entryPath == null) {
            System.err.println("deal: missing entry file");
            return 1;
        }

        ProjectLocator.LocateResult located = ProjectLocator.locate(entryPath,
            new CliOverrides(backendName, outputOverride));
        if (located.e2010() != null) {
            System.err.println(DiagnosticFormatter.format(located.e2010()));
            return writeDiagnosticsJson(List.of(located.e2010()),
                diagnosticsJsonPath);
        }
        if (located.cliDiagnostic() != null) {
            System.err.println(located.cliDiagnostic().message());
            return 1;
        }
        if (located.context() == null) {
            System.err.println("deal: cannot locate a project context for '"
                + entryPath + "'");
            return 1;
        }

        Backend backend = Backend.fromCliName(located.context().backend())
            .orElseThrow();
        Path entryFile = Path.of(entryPath).toAbsolutePath().normalize();

        // The harness invocation of this compile: COMMON_SHADOW /
        // DEAL_V1_2_INT32, never the release-owned production record, so
        // the phase-4 dispatch selects the harness arm.
        CompilerInvocation invocation = ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entryFile, verbose, dumpIr,
            dumpIr || sourceMap, sourceMap, diagnosticsJsonPath, invocation);
        boolean success;
        try {
            success = orchestrator.compile();
        } catch (IOException e) {
            System.err.println("deal: cannot write output to '"
                + located.context().outputPath().absoluteNormalizedPath()
                + "': " + e.getMessage());
            return 1;
        }
        return success ? 0 : 1;
    }

    public static void main(String[] args) {
        try {
            System.exit(run(args));
        } catch (Exception e) {
            System.err.println("deal: internal error: " + e.getMessage());
            e.printStackTrace(System.err);
            System.exit(2);
        }
    }

    /**
     * Writes the structured diagnostics document of a manifest
     * configuration failure (the {@code deal.Main} D8 mirror): a write
     * failure is a deterministic compiler I/O diagnostic on stderr with
     * exit 1 — no raw path exception escapes.
     */
    private static int writeDiagnosticsJson(List<CompilerDiagnostic> diagnostics,
                                            Path diagnosticsJsonPath) {
        if (diagnosticsJsonPath == null) {
            return 1;
        }
        try {
            Files.writeString(diagnosticsJsonPath,
                DiagnosticStructuredOutput.toJson(diagnostics));
        } catch (IOException e) {
            System.err.println("deal: cannot write diagnostics JSON to '"
                + diagnosticsJsonPath + "': " + e.getMessage());
        }
        return 1;
    }
}
