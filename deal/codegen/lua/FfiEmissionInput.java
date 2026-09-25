package deal.codegen.lua;

import deal.ffi.FfiGeneratedModule;
import deal.semantic.ir.ModuleId;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * The FFI emission input of one LuaJIT production session
 * ({@code luajit-ffi-load-emission-and-typed-crossings} F1/F2; the FFI
 * import and load contract): the compile's validated extern-C
 * generated-module metadata keyed by the resolved declaration module
 * plus the compile's manifest-directory text, and nothing else.
 *
 * <p>The input is what selects the emitted FFI load: a session carrying
 * it emits the {@code __rt.load_ffi} prelude at the owning
 * {@code MODULE_IMPORT} of an extern-C declaration import, resolves a
 * {@code MANIFEST_RELATIVE_PATH} loader text through the pinned
 * prefix-resolved conversion against the manifest directory, and fails
 * closed (a producer defect the production arm maps to E6005
 * {@code SHARED_EMITTER_COVERAGE}) when the import resolves no
 * generated module. A session without the input emits no FFI load: its
 * extern-C import keeps the landed no-op {@code MODULE_IMPORT} arm and
 * its loaded surface is the trace session's scenario seam.</p>
 *
 * <p><b>Compile-time metadata only.</b> The record carries the compile's
 * already-validated facts: it invokes no evaluator, opens no library,
 * resolves no symbol, and mutates no input. The map is keyed by module
 * identity (never a path string), so the emission's lookup is the exact
 * declaration-module identity the import op names.</p>
 *
 * @param generatedModules  the compile's extern-C generated modules by
 *                          resolved declaration-module identity, in the
 *                          compile's publication order; non-null
 * @param manifestDirectory the compile's manifest-directory text (the
 *                          base of manifest-relative loader-text
 *                          resolution); non-null
 */
public record FfiEmissionInput(
        Map<ModuleId, FfiGeneratedModule> generatedModules,
        String manifestDirectory) {

    public FfiEmissionInput {
        Objects.requireNonNull(generatedModules,
            "generatedModules must not be null");
        Map<ModuleId, FfiGeneratedModule> frozen = new LinkedHashMap<>();
        for (Map.Entry<ModuleId, FfiGeneratedModule> entry
                : generatedModules.entrySet()) {
            frozen.put(Objects.requireNonNull(entry.getKey(),
                    "a generated-module key must not be null"),
                Objects.requireNonNull(entry.getValue(),
                    "a generated module must not be null"));
        }
        generatedModules = Collections.unmodifiableMap(frozen);
        Objects.requireNonNull(manifestDirectory,
            "manifestDirectory must not be null");
    }

    /**
     * The generated metadata of one extern-C declaration module. An
     * absent entry is the fail-closed presence rule of the emission
     * input (a session carrying the input never silently omits an
     * extern-C import's load), so it throws instead of returning null:
     * the production arm maps the throw to E6005
     * {@code SHARED_EMITTER_COVERAGE} at the import origin and stages
     * nothing.
     *
     * @param moduleId the resolved declaration-module identity; non-null
     * @return the module's generated metadata; non-null
     */
    public FfiGeneratedModule require(ModuleId moduleId) {
        Objects.requireNonNull(moduleId, "moduleId must not be null");
        FfiGeneratedModule found = generatedModules.get(moduleId);
        if (found == null) {
            throw new IllegalStateException(
                "the extern-C declaration module '" + moduleId.path()
                    + "' carries no generated-module entry in the FFI"
                    + " emission input: the input covers exactly the"
                    + " compile's validated extern-C metadata (a producer"
                    + " defect, never a silently omitted load)");
        }
        return found;
    }
}
