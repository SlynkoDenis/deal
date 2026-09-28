-- test/ffigen_integration.lua — the LuaJIT FFIGEN boundary integration
-- driver (luajit-ffigen-boundary-integration D2/D3/D5/D6/D7/D8/D9/D10;
-- ISSUE-0455). Run from the repository root through the fail-closed
-- run_tests.sh gate line:
--
--     luajit test/ffigen_integration.lua
--
-- One LuaJIT VM, fail-closed, no skip path. The bootstrap compiles the
-- committed native fixture (T2) with GCC, compiles the three committed
-- extern-c fixture projects (T2) through the production CLI, resets the
-- event file, and runs the generated-artifact surface scan (gate half 3
-- of D1) as its first verification step. The eight-phase scenario matrix
-- (D7) then drives the generated bindings through the production
-- __rt.load_ffi path — the full composition: generated binding ->
-- load_ffi identity/cache gate -> cdef registration -> handle
-- open/resolve -> private casts -> wrapper build -> cell fill -> atomic
-- publish -> wrapper calls through the converters (D10). Any bootstrap
-- failure, scan mismatch, or assertion failure exits nonzero and fails
-- the gate. The driver performs no direct FFI namespace access and never
-- modifies production code.

-- ===== D3: the symlink-resolved physical root =====

-- The single stripped output line of `pwd -P` — kernel-resolved physical
-- text with no `.`/`..` segments and no symlink components, which is
-- exactly the resolution the production emission performs
-- (toRealPath()). The raw `..`-carrying precedent form and the raw
-- logical pwd text are never used.
local root_pipe = io.popen("pwd -P")
if root_pipe == nil then
  error("FFIGEN integration bootstrap failed: cannot run `pwd -P`")
end
local root = root_pipe:read("*l")
local extra_line = root_pipe:read("*l")
root_pipe:close()
if root == nil or root == "" then
  error("FFIGEN integration bootstrap failed: `pwd -P` produced no output")
end
root = root:match("^%s*(.-)%s*$")
if root == "" then
  error("FFIGEN integration bootstrap failed: `pwd -P` produced an empty line")
end
if extra_line ~= nil then
  error("FFIGEN integration bootstrap failed: `pwd -P` produced more than one line")
end
if root:sub(-1) == "/" then
  error("FFIGEN integration bootstrap failed: the pwd -P root ends with '/': " .. root)
end
if string.find(root, "/../", 1, true) ~= nil or string.find(root, "/./", 1, true) ~= nil then
  error("FFIGEN integration bootstrap failed: the pwd -P root carries a dot segment: " .. root)
end
print("FFIGEN integration root (pwd -P): " .. root)

-- package.path: the symlink-resolved root prefix first — every generated
-- artifact resolves the same production deal/runtime.lua and std/*
-- modules, so one VM-wide runtime module instance carries the FFI module
-- cache the cache-replay and event-file proofs depend on — then each
-- staged artifact directory.
package.path = root .. "/?.lua;"
  .. root .. "/build/ffigen-gen/missing-lib/?.lua;"
  .. root .. "/build/ffigen-gen/missing-symbol/?.lua;"
  .. root .. "/build/ffigen-gen/valid/?.lua;"
  .. package.path

-- ===== Pinned paths (D5) =====

local FIXTURE_C = "test/fixtures/ffigen/ffigen-integration-fixture.c"
local GEN_ROOT = root .. "/build/ffigen-gen"
local SO_PATH = root .. "/build/ffigen-integration-fixture.so"
local EVENTS_PATH = root .. "/build/ffigen-events.log"

local PROJECTS = {
  { name = "missing-lib", entry = root .. "/test/fixtures/ffigen/missing-lib/src/main.deal",
    loader = root .. "/build/ffigen-no-such-lib.so" },
  { name = "missing-symbol", entry = root .. "/test/fixtures/ffigen/missing-symbol/src/main.deal",
    loader = root .. "/build/ffigen-integration-fixture.so" },
  { name = "valid", entry = root .. "/test/fixtures/ffigen/valid/src/main.deal",
    loader = root .. "/build/ffigen-integration-fixture.so" },
}

-- ===== Toolchain and build probes (fail-closed; no skip path) =====

-- The driver runs only when the Java classes are built and the committed
-- fixture exists; a missing tool or build/ is a named bootstrap failure,
-- never a skipped scenario.
do
  local f = io.open(root .. "/build/deal/Main.class", "r")
  if f == nil then
    error("FFIGEN integration bootstrap failed: build/ is missing deal/Main.class; "
      .. "the Java classes must be built before the driver runs (no skip path)")
  end
  f:close()
end
do
  local f = io.open(FIXTURE_C, "r")
  if f == nil then
    error("FFIGEN integration bootstrap failed: the committed fixture is missing: " .. FIXTURE_C)
  end
  f:close()
end

local function probe_command(what, cmd)
  local status = os.execute(cmd .. " >/dev/null 2>&1")
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: " .. what
      .. " is not available (`" .. cmd .. "` exited with status " .. tostring(status) .. ")")
  end
end
probe_command("gcc", "gcc --version")
probe_command("java", "java -version")

-- ===== Bootstrap step 1 (D4; battery B3 pattern): GCC fixture compile =====

do
  local cmd = "mkdir -p build && gcc -shared -fPIC -O2 -DFIXTURE_EVENTS_PATH='\""
    .. EVENTS_PATH .. "\"' -o build/ffigen-integration-fixture.so " .. FIXTURE_C
  print("FFIGEN integration bootstrap: fixture GCC compile:")
  print("  " .. cmd)
  local status = os.execute(cmd)
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: fixture GCC compile exited with status "
      .. tostring(status))
  end
  local f = io.open(SO_PATH, "r")
  if f == nil then
    error("FFIGEN integration bootstrap failed: " .. SO_PATH .. " missing after the compile")
  end
  f:close()
end

-- ===== Bootstrap step 2 (D2/D5): harness-invocation compile per project =====
-- The three extern-C fixture projects carry a HOST-kind extern-C
-- declaration import, so the retained per-module artifact set (their
-- load_ffi emission) is produced by the test-scope harness compile entry
-- (ISSUE-0643 P10 item 3, mechanism 1: the same CLI-equivalent
-- arguments of deal.Main with the harness invocation). The release-owned
-- production invocation is asserted separately in step 2b: the extern-C
-- declaration import is admitted (the load_ffi prelude is emitted at the
-- import's MODULE_IMPORT, and the executed artifact fails at the import
-- with FFI_LIBRARY_LOAD for the never-built library), while the valid
-- project's bytes constructs (bytes(2), the element writes, and the
-- typed FFI call) are production-covered (ISSUE-0626).
for i = 1, #PROJECTS do
  local p = PROJECTS[i]
  local out = GEN_ROOT .. "/" .. p.name
  local status = os.execute("rm -rf '" .. out .. "' && mkdir -p '" .. out .. "'")
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: staging directory setup failed for " .. p.name)
  end
  local cmd = "java -ea -cp build deal.test.HarnessCompileEntry compile '" .. p.entry
    .. "' --backend lua --output '" .. out .. "'"
  print("FFIGEN integration bootstrap: harness-invocation compile (" .. p.name .. "):")
  print("  " .. cmd)
  status = os.execute(cmd)
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: the harness-invocation compile of "
      .. p.name .. " exited with status " .. tostring(status))
  end
  local f = io.open(out .. "/main.lua", "r")
  if f == nil then
    error("FFIGEN integration bootstrap failed: " .. out
      .. "/main.lua missing after the harness-invocation compile of " .. p.name)
  end
  f:close()
end

-- ===== Bootstrap step 2b (ISSUE-0662): the release-owned production
-- invocation of the extern-C fixtures =====
-- The extern-C declaration import is admitted: the production compile of
-- the missing-lib project stages the one project artifact carrying the
-- load_ffi prelude (the metadata module key, the manifest-resolved loader
-- text, the import span triplet), and executing it under luajit fails at
-- the import with FFI_LIBRARY_LOAD at the import statement's origin. The
-- valid project is admitted as well and — its bytes constructs now
-- lowering through the one production pipeline (ISSUE-0626) — compiles
-- and stages its one project artifact.
do
  local prodOut = GEN_ROOT .. "/production-probe"
  local status = os.execute("rm -rf '" .. prodOut .. "'")
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: production probe staging setup failed")
  end
  local logPath = GEN_ROOT .. "/production-probe.log"
  local entry = nil
  for i = 1, #PROJECTS do
    if PROJECTS[i].name == "missing-lib" then
      entry = PROJECTS[i].entry
    end
  end
  if entry == nil then
    error("FFIGEN integration bootstrap failed: the committed 'missing-lib' fixture project is missing")
  end
  local cmd = "java -ea -cp build deal.Main compile '" .. entry
    .. "' --backend lua --output '" .. prodOut .. "' >'" .. logPath .. "' 2>&1"
  print("FFIGEN integration bootstrap: production-invocation probe (missing-lib):")
  print("  " .. cmd)
  status = os.execute(cmd)
  local logHandle = io.open(logPath, "r")
  local probeOutput = ""
  if logHandle ~= nil then
    probeOutput = logHandle:read("*a")
    logHandle:close()
  end
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: the release-owned production invocation"
      .. " of missing-lib exited nonzero: " .. probeOutput)
  end
  local artifactHandle = io.open(prodOut .. "/main.lua", "r")
  if artifactHandle == nil then
    error("FFIGEN integration bootstrap failed: the production-invocation probe of"
      .. " missing-lib staged no artifact")
  end
  local artifact = artifactHandle:read("*a")
  artifactHandle:close()
  if not string.find(artifact, "__rt.load_ffi(\"ffi:@$external/ffi/missing_lib\"", 1, true) then
    error("FFIGEN integration bootstrap failed: the production artifact carries no"
      .. " load_ffi call with the metadata module key")
  end
  if not string.find(artifact, "loaderText = \"" .. root
      .. "/build/ffigen-no-such-lib.so\"", 1, true) then
    error("FFIGEN integration bootstrap failed: the production artifact carries no"
      .. " manifest-resolved loader text")
  end
  if not string.find(artifact, "main.deal\", 1, 1)", 1, true) then
    error("FFIGEN integration bootstrap failed: the production load carries no"
      .. " import span triplet")
  end
  if string.find(artifact, "ffi.C", 1, true) ~= nil then
    error("FFIGEN integration bootstrap failed: the production artifact carries ffi.C access")
  end
  local probeWriter = io.open(prodOut .. "/probe.lua", "w")
  if probeWriter == nil then
    error("FFIGEN integration bootstrap failed: cannot write the execution probe")
  end
  probeWriter:write([[
    package.path = "./?.lua;./std/?.lua;" .. package.path
    local ok, err = pcall(dofile, "main.lua")
    if ok then print("FFIGEN_PROD|init succeeded") os.exit(1) end
    if type(err) ~= "table" or err.code == nil then
      print("FFIGEN_PROD|not a runtime error: " .. tostring(err)) os.exit(1)
    end
    print("FFIGEN_PROD_ERROR|" .. tostring(err.code) .. "|" .. tostring(err.file)
      .. "|" .. tostring(err.line) .. "|" .. tostring(err.column))
  ]])
  probeWriter:close()
  local runPipe = io.popen("cd '" .. prodOut .. "' && luajit probe.lua 2>&1")
  if runPipe == nil then
    error("FFIGEN integration bootstrap failed: cannot run the production artifact")
  end
  local runOutput = runPipe:read("*a")
  runPipe:close()
  print("FFIGEN integration bootstrap: production artifact execution (missing-lib):")
  print("  " .. runOutput:gsub("%s+$", ""))
  if not string.find(runOutput, "FFIGEN_PROD_ERROR|FFI_LIBRARY_LOAD|", 1, true) then
    error("FFIGEN integration bootstrap failed: the production artifact of"
      .. " missing-lib did not raise FFI_LIBRARY_LOAD: " .. runOutput)
  end
  if not string.find(runOutput, "main.deal|1|1", 1, true) then
    error("FFIGEN integration bootstrap failed: the FFI_LIBRARY_LOAD did not carry"
      .. " the import statement's origin (1:1): " .. runOutput)
  end
end

-- The valid project is production-covered (ISSUE-0626): the extern-C
-- import is admitted (no HOST_MODULE_IMPORT outcome) and the compile
-- stages its one project artifact.
do
  local validEntry = root .. "/test/fixtures/ffigen/valid/src/main.deal"
  local validOut = GEN_ROOT .. "/production-probe-valid"
  local status = os.execute("rm -rf '" .. validOut .. "'")
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: valid production probe staging setup failed")
  end
  local logPath = GEN_ROOT .. "/production-probe-valid.log"
  local cmd = "java -ea -cp build deal.Main compile '" .. validEntry
    .. "' --backend lua --output '" .. validOut .. "' >'" .. logPath .. "' 2>&1"
  print("FFIGEN integration bootstrap: production-invocation probe (valid):")
  print("  " .. cmd)
  status = os.execute(cmd)
  local logHandle = io.open(logPath, "r")
  local probeOutput = ""
  if logHandle ~= nil then
    probeOutput = logHandle:read("*a")
    logHandle:close()
  end
  if status ~= 0 and status ~= true then
    error("FFIGEN integration bootstrap failed: the release-owned production invocation"
      .. " of valid did not compile (its bytes constructs are production-covered):\n"
      .. probeOutput)
  end
  if string.find(probeOutput, "E6005", 1, true) ~= nil
    or string.find(probeOutput, "HOST_MODULE_IMPORT", 1, true) ~= nil then
    error("FFIGEN integration bootstrap failed: the production-invocation probe of"
      .. " valid reported an emitter gap or the host-guard token:\n" .. probeOutput)
  end
  local validArtifact = io.open(validOut .. "/main.lua", "r")
  if validArtifact == nil then
    error("FFIGEN integration bootstrap failed: the production-invocation probe of"
      .. " valid staged no project artifact")
  end
  validArtifact:close()
end

-- ===== Bootstrap step 3: event-file reset + the surface scan (half 3) =====

os.remove(EVENTS_PATH)

local function read_all(path)
  local f = io.open(path, "r")
  if f == nil then
    return nil
  end
  local text = f:read("*a")
  f:close()
  return text
end

local function list_artifact_files(project_name)
  local files = {}
  local p = io.popen("find '" .. GEN_ROOT .. "/" .. project_name .. "' -type f")
  if p == nil then
    error("FFIGEN integration scan failed: cannot list the generated artifacts of " .. project_name)
  end
  for line in p:lines() do
    files[#files + 1] = line
  end
  p:close()
  if #files == 0 then
    error("FFIGEN integration scan failed: no generated artifacts found for " .. project_name)
  end
  return files
end

local function count_occurrences(text, needle)
  local n = 0
  local pos = 1
  while true do
    local hit = string.find(text, needle, pos, true)
    if hit == nil then
      return n
    end
    n = n + 1
    pos = hit + #needle
  end
  return n
end

--- Extract the first __rt.load_ffi call's first string argument (the
-- moduleKey) from the generated main.lua text.
local function extract_first_load_ffi_argument(text)
  local pos = string.find(text, "__rt.load_ffi%(")
  if pos == nil then
    return nil
  end
  local rest = text:sub(pos + #"__rt.load_ffi(")
  local _, q = string.find(rest, "^%s*\"")
  if q == nil then
    return nil
  end
  local arg = ""
  local i = q + 1
  while i <= #rest do
    local c = rest:sub(i, i)
    if c == "\\" then
      local nxt = rest:sub(i + 1, i + 1)
      if nxt == "\\" or nxt == "\"" then
        arg = arg .. nxt
        i = i + 2
      else
        arg = arg .. c
        i = i + 1
      end
    elseif c == "\"" then
      return arg
    else
      arg = arg .. c
      i = i + 1
    end
  end
  return nil
end

--- The generated-artifact surface scan (D7 phase 8; gate half 3 at
-- bootstrap): zero ffi.C[ and zero ffi.load( in every generated
-- artifact, at least one __rt.load_ffi( call per extern import in the
-- project's main artifact, the first __rt.load_ffi argument pairwise
-- distinct across the three projects, and each project's main artifact
-- byte-exactly carrying its pinned symlink-resolved absolute loader text
-- (no test/build fragment). A mismatch raises (fail-closed). Returns the
-- recorded scan summary for the phase-8 assertions.
local function surface_scan()
  local keys = {}
  local summaries = {}
  for i = 1, #PROJECTS do
    local p = PROJECTS[i]
    local files = list_artifact_files(p.name)
    local forbidden = 0
    local main_text = nil
    for j = 1, #files do
      local text = read_all(files[j])
      if text == nil then
        error("FFIGEN integration scan failed: cannot read generated artifact " .. files[j])
      end
      if string.find(text, "ffi.C[", 1, true) ~= nil then
        forbidden = forbidden + 1
      end
      if string.find(text, "ffi.load(", 1, true) ~= nil then
        forbidden = forbidden + 1
      end
      if files[j] == GEN_ROOT .. "/" .. p.name .. "/main.lua" then
        main_text = text
      end
    end
    if main_text == nil then
      error("FFIGEN integration scan failed: main.lua missing for " .. p.name)
    end
    local load_ffi_calls = count_occurrences(main_text, "__rt.load_ffi(")
    local key = extract_first_load_ffi_argument(main_text)
    local loader_found = string.find(main_text, p.loader, 1, true) ~= nil
    local wrong_path = string.find(main_text, root .. "/test/build", 1, true) ~= nil
    if forbidden ~= 0 then
      error("FFIGEN integration scan failed: " .. p.name .. " carries "
        .. forbidden .. " forbidden FFI namespace pattern occurrence(s)")
    end
    if load_ffi_calls < 1 then
      error("FFIGEN integration scan failed: " .. p.name
        .. " carries no __rt.load_ffi( call for its extern import")
    end
    if key == nil then
      error("FFIGEN integration scan failed: cannot read the first __rt.load_ffi argument of "
        .. p.name)
    end
    if not loader_found then
      error("FFIGEN integration scan failed: " .. p.name
        .. " does not carry its pinned resolved-absolute loader text byte-exactly: " .. p.loader)
    end
    if wrong_path then
      error("FFIGEN integration scan failed: " .. p.name
        .. " carries a test/build loader-path fragment")
    end
    keys[i] = key
    summaries[p.name] = {
      artifacts = #files,
      load_ffi_calls = load_ffi_calls,
      moduleKey = key,
      loader = p.loader,
      forbidden = 0,
    }
    print("  scan " .. p.name .. ": " .. #files .. " generated artifact file(s), "
      .. load_ffi_calls .. " __rt.load_ffi( call(s), first argument "
      .. key .. ", pinned loader text present")
  end
  if keys[1] == keys[2] or keys[1] == keys[3] or keys[2] == keys[3] then
    error("FFIGEN integration scan failed: the first __rt.load_ffi arguments are not "
      .. "pairwise distinct across the three projects")
  end
  return { keys = keys, summaries = summaries }
end

-- Gate half 3: the bootstrap's first verification step.
print("FFIGEN integration bootstrap: generated-artifact surface scan (gate half 3):")
local bootstrap_scan = surface_scan()

-- ===== The assertion pattern (test_runtime.lua:1-38) and helpers =====

local __rt = require("deal.runtime")

local passed = 0
local failed = 0
local function test(name, fn)
  local ok, err = pcall(fn)
  if ok then
    passed = passed + 1
    print("PASS: " .. name)
  else
    failed = failed + 1
    print("FAIL: " .. name .. " -- " .. tostring(err))
  end
end

-- Helper to check that an error was raised with the expected code
-- (the test_runtime.lua pattern); returns the captured error table.
local function assert_error(fn, expected_code)
  local ok, err = pcall(fn)
  if ok then
    error("expected error with code " .. tostring(expected_code) .. " but no error was raised")
  end
  if type(err) ~= "table" then
    error("expected error table but got " .. type(err) .. ": " .. tostring(err))
  end
  if err.code ~= expected_code then
    error("expected error code " .. tostring(expected_code) .. " but got "
      .. tostring(err.code) .. ": " .. tostring(err.message))
  end
  return err
end

local function read_event_lines()
  local lines = {}
  local f = io.open(EVENTS_PATH, "r")
  if f ~= nil then
    for line in f:lines() do
      lines[#lines + 1] = line
    end
    f:close()
  end
  return lines
end

local function event_signature(lines)
  return table.concat(lines, ",")
end

-- ===== Pinned artifacts and spans (the committed T2 fixture sources) =====

-- Each entry module's import statement sits at line 1, column 1 — the
-- import span every loader code must carry (R13).
local MISSING_LIB_ARTIFACT = GEN_ROOT .. "/missing-lib/main.lua"
local MISSING_SYMBOL_ARTIFACT = GEN_ROOT .. "/missing-symbol/main.lua"
local VALID_ARTIFACT = GEN_ROOT .. "/valid/main.lua"

local MISSING_LIB_ENTRY = root .. "/test/fixtures/ffigen/missing-lib/src/main.deal"
local MISSING_SYMBOL_ENTRY = root .. "/test/fixtures/ffigen/missing-symbol/src/main.deal"
local VALID_ENTRY = root .. "/test/fixtures/ffigen/valid/src/main.deal"

local IMPORT_LINE = 1
local IMPORT_COLUMN = 1

-- The two phase-7 call sites in valid/src/main.deal: the echo call in
-- scenario_invalid_string and the call in scenario_null_string.
local INVALID_STRING_CALL_LINE = 62
local INVALID_STRING_CALL_COLUMN = 10
local NULL_STRING_CALL_LINE = 68
local NULL_STRING_CALL_COLUMN = 10

-- Cross-phase state: the cached error values (reference-equality proofs)
-- and the event-file signatures the replay phases must preserve.
local phase1_error = nil
local phase3_error = nil
local phase3_events_sig = nil
local phase5_events_sig = nil
local valid_exports = nil

-- ===== D7: the eight-phase scenario matrix, in order, one VM =====

test("phase 1: missing library raises FFI_LIBRARY_LOAD with the import span and zero event lines", function()
  print("  load: dofile(" .. MISSING_LIB_ARTIFACT .. ")")
  local err = assert_error(function()
    dofile(MISSING_LIB_ARTIFACT)
  end, "FFI_LIBRARY_LOAD")
  assert(err.file == MISSING_LIB_ENTRY,
    "the import span file must be the entry source: got " .. tostring(err.file))
  assert(err.line == IMPORT_LINE,
    "the import span line must be " .. IMPORT_LINE .. ": got " .. tostring(err.line))
  assert(err.column == IMPORT_COLUMN,
    "the import span column must be " .. IMPORT_COLUMN .. ": got " .. tostring(err.column))
  local lines = read_event_lines()
  assert(#lines == 0,
    "no open ever happened: expected zero event lines, got " .. #lines)
  phase1_error = err
end)

test("phase 2: exact replay re-raises the same cached error value with no retry", function()
  local ok, err = pcall(dofile, MISSING_LIB_ARTIFACT)
  assert(ok == false, "the exact replay must raise")
  assert(err == phase1_error,
    "cached-error replay re-raises the cached error table itself (reference equality)")
  assert(err.code == "FFI_LIBRARY_LOAD", "code drift on replay: " .. tostring(err.code))
  local lines = read_event_lines()
  assert(#lines == 0,
    "no retry and no fresh open: expected zero event lines, got " .. #lines)
end)

test("phase 3: changed identity with invalid content raises FFI_SYMBOL_MISSING and closes the failed handle once", function()
  print("  load: dofile(" .. MISSING_SYMBOL_ARTIFACT .. ")")
  local err = assert_error(function()
    dofile(MISSING_SYMBOL_ARTIFACT)
  end, "FFI_SYMBOL_MISSING")
  assert(err.file == MISSING_SYMBOL_ENTRY,
    "the import span file must be the entry source: got " .. tostring(err.file))
  assert(err.line == IMPORT_LINE,
    "the import span line must be " .. IMPORT_LINE .. ": got " .. tostring(err.line))
  assert(err.column == IMPORT_COLUMN,
    "the import span column must be " .. IMPORT_COLUMN .. ": got " .. tostring(err.column))
  local lines = read_event_lines()
  assert(#lines == 2,
    "the fresh pipeline ran and the failed opened handle closed exactly once: "
      .. "expected two event lines, got " .. #lines)
  assert(lines[1] == "open" and lines[2] == "close",
    "expected exactly one open and one close line, got " .. event_signature(lines))
  phase3_error = err
  phase3_events_sig = event_signature(lines)
end)

test("phase 4: exact replay of the symbol failure re-raises the same cached error and opens nothing", function()
  local ok, err = pcall(dofile, MISSING_SYMBOL_ARTIFACT)
  assert(ok == false, "the exact replay must raise")
  assert(err == phase3_error,
    "cached-error replay re-raises the cached error table itself (reference equality)")
  assert(err.code == "FFI_SYMBOL_MISSING", "code drift on replay: " .. tostring(err.code))
  local lines = read_event_lines()
  assert(event_signature(lines) == phase3_events_sig,
    "cached-error replay only on exact full-content replay: the event file must be unchanged")
end)

test("phase 5: valid load yields ready typed wrappers, real roundtrips, one native call each, zero default evaluation", function()
  print("  load: dofile(" .. VALID_ARTIFACT .. ")")
  local ok, exports = pcall(dofile, VALID_ARTIFACT)
  assert(ok == true, "the valid artifact must load through production load_ffi: "
    .. tostring(exports))
  assert(type(exports) == "table", "the artifact must return the module exports table")
  local lines = read_event_lines()
  assert(#lines == 3 and lines[1] == "open" and lines[2] == "close" and lines[3] == "open",
    "cumulative two open and one close (the ready handle is retained): got "
      .. event_signature(lines) .. " (" .. #lines .. " lines)")
  phase5_events_sig = event_signature(lines)

  local function scenario(name)
    local w = exports[name]
    assert(type(w) == "table" and w.__kind == "function",
      "export " .. name .. " is not a function wrapper")
    return w.f
  end
  local call_count = scenario("scenario_call_count")

  -- Zero default evaluation (D8): the Probe default calls
  -- fixture_count_call_int, so any load-time evaluation would read >= 1.
  assert(call_count() == 0,
    "immediately after load the fixture counter must read 0 (zero default evaluation)")

  assert(scenario("scenario_add_int")() == 42, "add_int(20, 22) roundtrip")
  assert(call_count() == 1,
    "exactly one native call per wrapper call: expected counter 1, got " .. call_count())
  assert(scenario("scenario_sub_int")() == 5, "sub_int(7, 2) left-to-right order")
  assert(call_count() == 2,
    "exactly one native call per wrapper call: expected counter 2, got " .. call_count())
  assert(scenario("scenario_add_number")() == 3.75, "add_number(1.25, 2.5) roundtrip")
  assert(call_count() == 3,
    "exactly one native call per wrapper call: expected counter 3, got " .. call_count())
  assert(scenario("scenario_not")() == true, "not(0) -> true (_Bool 0/1 roundtrip)")
  assert(call_count() == 4,
    "exactly one native call per wrapper call: expected counter 4, got " .. call_count())
  assert(scenario("scenario_echo_string")() == "hello",
    "echo_string copies the C-owned buffer")
  assert(call_count() == 5,
    "exactly one native call per wrapper call: expected counter 5, got " .. call_count())
  assert(scenario("scenario_bytes_sum")() == 15, "bytes_sum over bytes(7, 8)")
  assert(call_count() == 6,
    "exactly one native call per wrapper call: expected counter 6, got " .. call_count())
  assert(scenario("scenario_count_call")() == __rt.__NULL, "count_call -> null")
  assert(call_count() == 7,
    "exactly one native call per wrapper call: expected counter 7, got " .. call_count())
  assert(scenario("scenario_count_call_int")() == 8,
    "count_call_int increments and returns the counter (8)")
  assert(call_count() == 8,
    "exactly one native call per wrapper call: expected counter 8, got " .. call_count())
  assert(scenario("scenario_reset_counter")() == __rt.__NULL, "reset_counter -> null")
  assert(call_count() == 0,
    "the reset leaves the zero-evaluation baseline for phase 6: expected 0, got "
      .. call_count())
  valid_exports = exports
end)

test("phase 6: ready replay serves the cached record with no fresh open and no default evaluation", function()
  local ok, exports2 = pcall(dofile, VALID_ARTIFACT)
  assert(ok == true, "the ready replay must return a working module: " .. tostring(exports2))
  assert(type(exports2) == "table", "the replay must return the module exports table")
  local lines = read_event_lines()
  assert(event_signature(lines) == phase5_events_sig,
    "the cached ready record served: no fresh library open, the event file must be unchanged")
  local call_count = exports2.scenario_call_count.f
  assert(call_count() == 0,
    "the ready replay performed no default evaluation and no native call: expected 0, got "
      .. call_count())
end)

test("phase 7: FFI_INVALID_STRING raises before the call with no native effect", function()
  local call_count = valid_exports.scenario_call_count.f
  assert(call_count() == 0, "the phase-7 baseline counter must read 0")
  local err = assert_error(function()
    valid_exports.scenario_invalid_string.f()
  end, "FFI_INVALID_STRING")
  assert(err.file == VALID_ENTRY,
    "the call-site span file must be the entry source: got " .. tostring(err.file))
  assert(err.line == INVALID_STRING_CALL_LINE,
    "the call-site span line must be " .. INVALID_STRING_CALL_LINE .. ": got "
      .. tostring(err.line))
  assert(err.column == INVALID_STRING_CALL_COLUMN,
    "the call-site span column must be " .. INVALID_STRING_CALL_COLUMN .. ": got "
      .. tostring(err.column))
  assert(call_count() == 0,
    "validate before narrowing: the native call never ran, the counter must be unchanged")
end)

test("phase 7: FFI_NULL_STRING raises after the call with native effects retained", function()
  local call_count = valid_exports.scenario_call_count.f
  local err = assert_error(function()
    valid_exports.scenario_null_string.f()
  end, "FFI_NULL_STRING")
  assert(err.file == VALID_ENTRY,
    "the call-site span file must be the entry source: got " .. tostring(err.file))
  assert(err.line == NULL_STRING_CALL_LINE,
    "the call-site span line must be " .. NULL_STRING_CALL_LINE .. ": got "
      .. tostring(err.line))
  assert(err.column == NULL_STRING_CALL_COLUMN,
    "the call-site span column must be " .. NULL_STRING_CALL_COLUMN .. ": got "
      .. tostring(err.column))
  assert(call_count() == 1,
    "the call ran: native effects remain, the counter must read exactly 1, got "
      .. call_count())
end)

test("phase 8: generated-artifact surface scan re-verification", function()
  -- The same checks as the bootstrap scan (gate half 3), re-verified on
  -- every run. The settled seam shapes and the canonical descriptor
  -- content are enforced by the load itself: phases 1-7 above consumed
  -- the generated artifacts and observed exactly the pinned codes and
  -- roundtrips, so any divergent sibling shape already failed the
  -- integration at load.
  print("  surface scan re-verification:")
  local scan = surface_scan()
  for i = 1, #PROJECTS do
    assert(scan.keys[i] == bootstrap_scan.keys[i],
      "the first __rt.load_ffi argument of project " .. PROJECTS[i].name
        .. " drifted during the run")
  end
  assert(scan.keys[1] ~= scan.keys[2] and scan.keys[1] ~= scan.keys[3]
      and scan.keys[2] ~= scan.keys[3],
    "the first __rt.load_ffi arguments must stay pairwise distinct")
  for i = 1, #PROJECTS do
    local s = scan.summaries[PROJECTS[i].name]
    assert(s.loader == PROJECTS[i].loader,
      "pinned loader text drift for " .. PROJECTS[i].name)
    assert(s.load_ffi_calls >= 1,
      "at least one __rt.load_ffi( call per extern import for " .. PROJECTS[i].name)
    assert(s.forbidden == 0,
      "zero forbidden FFI namespace patterns for " .. PROJECTS[i].name)
  end
end)

-- ===== Summary (the test_runtime.lua pattern: nonzero exit on failure) =====

print("")
print("========================================")
print("Results: " .. passed .. " passed, " .. failed .. " failed")
print("========================================")

if failed > 0 then
  os.exit(1)
end
