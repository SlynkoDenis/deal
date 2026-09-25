package deal.distribution;

import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * The pinned runtime/stdlib distribution resolution (design source
 * {@code release-distribution-packaging-and-discovery} D3,
 * {@code whole-project-artifact-publication} D6).
 *
 * <p><b>Resolution order, pinned (D3):</b></p>
 * <ol>
 *   <li><b>Project-local surface</b> — {@code <manifestDir>/std} when
 *       present (the pinned v1.2 override surface; unchanged
 *       precedence).</li>
 *   <li><b>Language distribution</b> — classpath resources
 *       ({@code std/<m>.d.deal}, {@code std/<m>.lua},
 *       {@code std/<m>.js}, {@code deal/runtime.lua},
 *       {@code deal/runtime.js}), then the {@code DEAL_HOME} filesystem
 *       layout (the {@code deal.home} system property or the
 *       {@code DEAL_HOME} environment variable — the documented
 *       override for non-layout installs; the packaged {@code bin/deal}
 *       launcher supplies the distribution on the classpath).</li>
 *   <li><b>Checkout CWD fallback</b> — {@code <cwd>/std} and
 *       {@code <cwd>/deal/runtime.*} (dev mode only; never reachable
 *       from an installed distribution whose surface is present).</li>
 * </ol>
 *
 * <p>Each request resolves to exactly one source in this order: the
 * first tier that provides the requested file wins. The project-local
 * tier applies to stdlib files only — no project-local location is
 * pinned for the runtime sources, which resolve classpath → distribution
 * home → CWD (the order {@code copyRuntimeLibrary}/{@code
 * copyJsRuntimeLibrary} gain, removing the implicit CWD dependency of
 * the legacy fallback).</p>
 *
 * <p><b>Read-only and deterministic.</b> Resolution performs reads only
 * (existence/regularity probes and resource lookups), never creates
 * anything, and is deterministic for a fixed environment and layout.
 * Absence at all tiers is a plain empty result — never an error: the
 * existing diagnostics own the failure surface (E2003 for a missing
 * stdlib import, the pinned E6000 runtime-not-found diagnostic for the
 * runtime copies). Results are cached per JVM keyed by the manifest
 * directory, the resource loader, and the effective distribution-home
 * value (like {@code StdlibModuleResolver}'s per-surface cache).</p>
 *
 * <p><b>JDK-only.</b> This package depends on the JDK alone and is
 * consumed by {@code deal.module}, {@code deal.project},
 * {@code deal.codegen.lua}, {@code deal.Main}, and — later — the
 * {@code deal.publication} stager (the resolved-surface API of
 * {@code whole-project-artifact-publication} D6); it never depends on
 * them.</p>
 */
public final class DistributionHome {

    /** The project-local tier name ({@code <manifestDir>/std}). */
    public static final String TIER_PROJECT_LOCAL = "project-local";

    /** The classpath-resource distribution tier name. */
    public static final String TIER_CLASSPATH_RESOURCES =
        "distribution-classpath-resources";

    /** The {@code DEAL_HOME} filesystem distribution tier name. */
    public static final String TIER_DISTRIBUTION_HOME = "distribution-home";

    /** The checkout CWD dev-fallback tier name. */
    public static final String TIER_CWD_FALLBACK = "cwd-fallback";

    /** The {@code deal.home} system property name (D3). */
    public static final String DEAL_HOME_PROPERTY = "deal.home";

    /** The {@code DEAL_HOME} environment variable name (D3). */
    public static final String DEAL_HOME_ENV = "DEAL_HOME";

    /**
     * The six spec-listed stdlib module names, in pinned declaration
     * order — the same six names pinned by the stdlib authority (the
     * names behind {@code StdlibModuleResolver#SPEC_STDLIB_MODULES} and
     * {@code ModuleIdentityResolver#SPEC_STDLIB_MODULE_NAMES}; this
     * package is JDK-only and keeps its own pinned copy). Used only for
     * the classpath-surface probe (which declaration resource proves the
     * classpath carries the {@code std/} prefix).
     */
    public static final List<String> SPEC_STDLIB_MODULE_NAMES = List.of(
        "console", "string", "table", "json", "math", "time"
    );

    /**
     * One resolved stdlib surface: the tier that provided it plus the
     * resolved directory path. Only directory surfaces are ever
     * published — a classpath resource surface is published only when it
     * materializes to a {@code file:} URL whose parent directory exists
     * (the directory-distribution reality the distribution layout pins;
     * a non-materializable resource surface contributes nothing here and
     * the next tier is consulted).
     *
     * @param tier     the pinned tier name ({@link
     *                 #TIER_PROJECT_LOCAL}, {@link
     *                 #TIER_CLASSPATH_RESOURCES}, {@link
     *                 #TIER_DISTRIBUTION_HOME}, or {@link
     *                 #TIER_CWD_FALLBACK})
     * @param pathText the resolved surface directory path text
     */
    public record ResolvedSurface(String tier, String pathText) {
        public ResolvedSurface {
            Objects.requireNonNull(tier, "tier");
            Objects.requireNonNull(pathText, "pathText");
        }
    }

    /**
     * One resolved readable source of a requested file: a filesystem
     * path (project-local, distribution-home, CWD tiers) or a classpath
     * resource URL. Exactly one source is produced per request.
     */
    public static final class ResolvedSource {
        private final String tier;
        private final Path path;
        private final URL resource;

        private ResolvedSource(String tier, Path path, URL resource) {
            this.tier = Objects.requireNonNull(tier, "tier");
            this.path = path;
            this.resource = resource;
        }

        /** The pinned tier name this source resolved from. */
        public String tier() {
            return tier;
        }

        /** The filesystem path, present exactly for the file tiers. */
        public Optional<Path> path() {
            return Optional.ofNullable(path);
        }

        /**
         * Opens the source for reading. Never null; a filesystem source
         * opens a fresh stream, a resource source opens the resource
         * stream.
         */
        public InputStream open() throws IOException {
            if (path != null) {
                return Files.newInputStream(path);
            }
            if (resource != null) {
                return resource.openStream();
            }
            throw new IllegalStateException(
                "resolved source carries no location (internal invariant"
                    + " violation)");
        }

        /** The human-readable source location (path or resource URL). */
        public String locationText() {
            if (path != null) {
                return path.toString();
            }
            return resource.toExternalForm();
        }

        @Override
        public String toString() {
            return tier + " " + locationText();
        }
    }

    /** The resolved-surface cache (per composite resolution key). */
    private static final Map<String, Optional<ResolvedSurface>>
        SURFACE_CACHE = new HashMap<>();

    /** The resolved-source cache (per composite resolution key). */
    private static final Map<String, Optional<ResolvedSource>>
        SOURCE_CACHE = new HashMap<>();

    private final String manifestDirectoryText;
    private final ClassLoader resourceLoader;

    private DistributionHome(String manifestDirectoryText,
                             ClassLoader resourceLoader) {
        this.manifestDirectoryText = Objects.requireNonNull(
            manifestDirectoryText, "manifestDirectoryText");
        this.resourceLoader = Objects.requireNonNull(resourceLoader,
            "resourceLoader");
    }

    /**
     * The resolver for one project's manifest directory, reading
     * classpath resources through this class's loader (the application
     * classpath — the distribution root when the compiler runs from an
     * installed layout via {@code bin/deal}).
     */
    public static DistributionHome forManifestDirectory(
            String manifestDirectoryText) {
        return forManifestDirectory(manifestDirectoryText,
            DistributionHome.class.getClassLoader());
    }

    /**
     * The resolver for one project's manifest directory with an explicit
     * resource loader (the pinned injection seam the tier-selection
     * tests use to stage classpath-resource distributions).
     */
    public static DistributionHome forManifestDirectory(
            String manifestDirectoryText, ClassLoader resourceLoader) {
        return new DistributionHome(manifestDirectoryText, resourceLoader);
    }

    /**
     * The manifest-directory text this resolver was constructed with:
     * the base of the manifest-relative deployment-copy resolution (and
     * the same text a compile's FFI emission input carries for a
     * manifest-relative native-library loader text).
     */
    public String manifestDirectoryText() {
        return manifestDirectoryText;
    }

    /**
     * The stable composite cache identity of this resolver for cached
     * consumers ({@code StdlibModuleResolver}'s per-home cache): the
     * manifest directory, the resource-loader identity, and the
     * effective distribution-home value. Distinct environments (a
     * changed {@code deal.home} property, a different loader) never
     * share a cached result.
     */
    public String cacheIdentity() {
        return cachePrefix();
    }

    /**
     * Resolves the stdlib surface directory in the pinned D3 order:
     * project-local {@code <manifestDir>/std}, the materialized
     * classpath-resource {@code std/} directory, the
     * {@code DEAL_HOME}/{@code deal.home} filesystem {@code std/}
     * directory, then the checkout CWD {@code std/} directory. Absence
     * at all tiers is an empty result — never an error. Cached per
     * composite key for the JVM.
     */
    public Optional<ResolvedSurface> resolveStdlibSurface() {
        String key = cachePrefix() + "|surface";
        synchronized (SURFACE_CACHE) {
            Optional<ResolvedSurface> cached = SURFACE_CACHE.get(key);
            if (cached != null) {
                return cached;
            }
        }
        Optional<ResolvedSurface> resolved = probeStdlibSurface();
        synchronized (SURFACE_CACHE) {
            SURFACE_CACHE.putIfAbsent(key, resolved);
        }
        return resolved;
    }

    /**
     * Resolves one spec-listed stdlib declaration file
     * ({@code std/<moduleName>.d.deal}) in the pinned D3 order:
     * project-local first, then classpath resources, then the
     * distribution home, then the CWD dev fallback. Cached per JVM.
     *
     * @param moduleName the stdlib module bare name ({@code console},
     *                   {@code string}, {@code table}, {@code json},
     *                   {@code math}, {@code time})
     */
    public Optional<ResolvedSource> resolveStdlibDeclaration(
            String moduleName) {
        return resolveStdlibFileImpl("std/" + moduleName + ".d.deal");
    }

    /**
     * Resolves one spec-listed stdlib implementation file
     * ({@code std/<moduleName>.<extension>}, {@code extension} =
     * {@code lua} or {@code js}) in the pinned D3 order: project-local
     * first, then classpath resources, then the distribution home, then
     * the CWD dev fallback. Cached per JVM.
     */
    public Optional<ResolvedSource> resolveStdlibImplementation(
            String moduleName, String extension) {
        return resolveStdlibFileImpl("std/" + moduleName + "." + extension);
    }

    /**
     * Resolves one runtime source ({@code deal/runtime.lua} or
     * {@code deal/runtime.js}) in the pinned order: classpath resources,
     * then the distribution home, then the CWD dev fallback (no
     * project-local location is pinned for the runtime). Cached per
     * JVM.
     */
    public Optional<ResolvedSource> resolveRuntimeSource(
            String relativeName) {
        String key = cachePrefix() + "|runtime:" + relativeName;
        synchronized (SOURCE_CACHE) {
            Optional<ResolvedSource> cached = SOURCE_CACHE.get(key);
            if (cached != null) {
                return cached;
            }
        }
        Optional<ResolvedSource> resolved =
            probeRuntimeSource(relativeName);
        synchronized (SOURCE_CACHE) {
            SOURCE_CACHE.putIfAbsent(key, resolved);
        }
        return resolved;
    }

    // =========================================================================
    // Per-file resolution
    // =========================================================================

    private Optional<ResolvedSource> resolveStdlibFileImpl(
            String relativeName) {
        String key = cachePrefix() + "|stdlib:" + relativeName;
        synchronized (SOURCE_CACHE) {
            Optional<ResolvedSource> cached = SOURCE_CACHE.get(key);
            if (cached != null) {
                return cached;
            }
        }
        Optional<ResolvedSource> resolved =
            probeStdlibFile(relativeName);
        synchronized (SOURCE_CACHE) {
            SOURCE_CACHE.putIfAbsent(key, resolved);
        }
        return resolved;
    }

    private Optional<ResolvedSource> probeStdlibFile(String relativeName) {
        // Tier 1: the project-local surface (<manifestDir>/std).
        Optional<ResolvedSource> projectLocal = fileSource(
            TIER_PROJECT_LOCAL, manifestDirectoryText, relativeName);
        if (projectLocal.isPresent()) {
            return projectLocal;
        }
        // Tier 2a: classpath resources.
        Optional<ResolvedSource> resource = resourceSource(
            TIER_CLASSPATH_RESOURCES, relativeName);
        if (resource.isPresent()) {
            return resource;
        }
        // Tier 2b: the DEAL_HOME filesystem layout.
        Optional<ResolvedSource> home = fileSource(TIER_DISTRIBUTION_HOME,
            dealHomeText(), relativeName);
        if (home.isPresent()) {
            return home;
        }
        // Tier 3: the checkout CWD dev fallback.
        return fileSource(TIER_CWD_FALLBACK, cwdText(), relativeName);
    }

    private Optional<ResolvedSource> probeRuntimeSource(String relativeName) {
        // No project-local location is pinned for the runtime: classpath
        // resources first, then the distribution home, then the CWD.
        Optional<ResolvedSource> resource = resourceSource(
            TIER_CLASSPATH_RESOURCES, relativeName);
        if (resource.isPresent()) {
            return resource;
        }
        Optional<ResolvedSource> home = fileSource(TIER_DISTRIBUTION_HOME,
            dealHomeText(), relativeName);
        if (home.isPresent()) {
            return home;
        }
        return fileSource(TIER_CWD_FALLBACK, cwdText(), relativeName);
    }

    // =========================================================================
    // Surface resolution
    // =========================================================================

    private Optional<ResolvedSurface> probeStdlibSurface() {
        // Tier 1: the project-local surface — <manifestDir>/std when it
        // exists as a directory (the pinned v1.2 override surface).
        Path projectStd = resolveBase(manifestDirectoryText, "std");
        if (projectStd != null && Files.isDirectory(projectStd)) {
            return Optional.of(new ResolvedSurface(TIER_PROJECT_LOCAL,
                projectStd.toString()));
        }

        // Tier 2a: the classpath-resource std/ directory — a pinned
        // declaration resource under the std/ prefix whose file: URL
        // materializes to a directory (the directory-distribution
        // reality; a non-materializable resource contributes no
        // directory surface and the next tier is consulted).
        for (String moduleName : SPEC_STDLIB_MODULE_NAMES) {
            URL url = resourceLoader.getResource(
                "std/" + moduleName + ".d.deal");
            if (url == null || !"file".equals(url.getProtocol())) {
                continue;
            }
            try {
                Path stdDir = Path.of(url.toURI()).getParent();
                if (stdDir != null && Files.isDirectory(stdDir)) {
                    return Optional.of(new ResolvedSurface(
                        TIER_CLASSPATH_RESOURCES, stdDir.toString()));
                }
            } catch (URISyntaxException | IllegalArgumentException e) {
                // Not a materializable resource location: fall through.
            }
        }

        // Tier 2b: the DEAL_HOME filesystem layout.
        Path homeStd = resolveBase(dealHomeText(), "std");
        if (homeStd != null && Files.isDirectory(homeStd)) {
            return Optional.of(new ResolvedSurface(TIER_DISTRIBUTION_HOME,
                homeStd.toString()));
        }

        // Tier 3: the checkout CWD dev fallback.
        Path cwdStd = resolveBase(cwdText(), "std");
        if (cwdStd != null && Files.isDirectory(cwdStd)) {
            return Optional.of(new ResolvedSurface(TIER_CWD_FALLBACK,
                cwdStd.toString()));
        }

        return Optional.empty();
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /**
     * The effective distribution-home text: the {@code deal.home} system
     * property when set to a non-blank value, else the {@code DEAL_HOME}
     * environment variable when set to a non-blank value, else null.
     */
    private static String dealHomeText() {
        String property = System.getProperty(DEAL_HOME_PROPERTY);
        if (property != null && !property.isBlank()) {
            return property;
        }
        String env = System.getenv(DEAL_HOME_ENV);
        if (env != null && !env.isBlank()) {
            return env;
        }
        return null;
    }

    /** The normalized absolute process-CWD text. */
    private static String cwdText() {
        return Path.of("").toAbsolutePath().normalize().toString();
    }

    /**
     * Resolves {@code relativeName} under {@code baseText} to a
     * normalized absolute path with no existence requirement; null when
     * the base is null or cannot be materialized.
     */
    private static Path resolveBase(String baseText, String relativeName) {
        if (baseText == null) {
            return null;
        }
        try {
            return Path.of(baseText).resolve(relativeName)
                .toAbsolutePath().normalize();
        } catch (InvalidPathException e) {
            return null;
        }
    }

    /** One filesystem source when the file exists as a regular file. */
    private static Optional<ResolvedSource> fileSource(String tier,
            String baseText, String relativeName) {
        Path candidate = resolveBase(baseText, relativeName);
        if (candidate == null || !Files.isRegularFile(candidate)) {
            return Optional.empty();
        }
        return Optional.of(new ResolvedSource(tier, candidate, null));
    }

    /** One classpath-resource source when the resource exists. */
    private Optional<ResolvedSource> resourceSource(String tier,
            String relativeName) {
        URL url = resourceLoader.getResource(relativeName);
        if (url == null) {
            return Optional.empty();
        }
        return Optional.of(new ResolvedSource(tier, null, url));
    }

    /**
     * The composite cache key: manifest directory, resource-loader
     * identity, and the current effective distribution-home value — a
     * changed environment never shares a cached resolution.
     */
    private String cachePrefix() {
        return manifestDirectoryText + "|"
            + System.identityHashCode(resourceLoader) + "|"
            + dealHomeText();
    }
}
