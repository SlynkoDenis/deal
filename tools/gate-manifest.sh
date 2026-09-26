#!/bin/bash

TEST_MAINS=(
  'bg|=== Launching JVM Backend Tests (background) ===|java -ea -cp build deal.test.JvmBackendTest'
  'bg|=== Launching Lua ABI Unit Tests (background; JUnit4 + Hamcrest) ===|java -ea -cp build:/usr/share/java/junit4.jar:/usr/share/java/hamcrest-core.jar org.junit.runner.JUnitCore deal.test.LuaAbiTest deal.test.LuaAbiBackendTest deal.test.CrossModuleTypingTest'
  'bg|=== Launching Conformance Tests (background) ===|java -ea -cp build deal.test.ConformanceTest test/conformance/'
  'bg|=== Launching JVM Conformance Tests (background; ISSUE-0102 origin — ISSUE-0168 capability accounting) ===|java -ea -cp build deal.test.JvmConformanceTest test/conformance/'
  'bg|=== Launching JS Conformance Tests (background) ===|java -ea -cp build deal.test.JsConformanceTest test/conformance/'
  'fg|=== Running Diagnostic Range Tests ===|java -ea -cp build deal.test.DiagnosticRangeTest'
  'fg|=== Running Diagnostic Classification Tests ===|java -ea -cp build deal.test.DiagnosticClassificationTest'
  'fg|=== Running Lowering Foundation Tests (ISSUE-0281) ===|java -ea -cp build deal.test.LoweringFoundationTest'
  'fg|=== Running Checked Project Builder Tests (ISSUE-0288) ===|java -ea -cp build deal.test.CheckedProjectBuilderTest'
  'fg|=== Running Lowering Support / Requirement Manifest Tests (ISSUE-0289) ===|java -ea -cp build deal.test.LoweringSupportTest'
  'fg|=== Running Migration Planner / Route Plan Tests (ISSUE-0290) ===|java -ea -cp build deal.semantic.MigrationPlannerTest'
  'fg|=== Running Foundation Integration Tests (ISSUE-0292) ===|java -ea -cp build deal.test.FoundationIntegrationTest'
  'fg|=== Running Invocation / Profile / Capability Registry Tests (ISSUE-0284) ===|java -ea -cp build deal.test.InvocationProfileRegistryTest'
  'fg|=== Running Semantic IR Schema Tests (ISSUE-0282) ===|java -ea -cp build deal.test.SemanticIrSchemaTest'
  'fg|=== Running Descriptor Service Tests (ISSUE-0233 D1/D2) ===|java -ea -cp build deal.test.DescriptorServiceTest'
  'fg|=== Running Container Payload Descriptor Bridge Tests (ISSUE-0232 D2) ===|java -ea -cp build deal.test.ContainerPayloadDescriptorsTest'
  'fg|=== Running Boundary Executor Tests (ISSUE-0364 D3) ===|java -ea -cp build deal.test.BoundaryExecutorTest'
  'fg|=== Running Comparison Operand View and Executor Tests (ISSUE-0406, ISSUE-0234 B-D1/B-D2/B-D4) ===|java -ea -cp build deal.test.ComparisonExecutorTest'
  'fg|=== Running Address Chain Protocol / Normalized Slot Tests (ISSUE-0234 A-D1/A-D3/A-D9) ===|java -ea -cp build deal.test.AddressChainProtocolTest'
  'fg|=== Running Address Chain Lowering Tests (ISSUE-0405 ASSIGN/DELETE chains) ===|java -ea -cp build deal.test.AddressChainLoweringTest'
  'fg|=== Running Control Flow Lowering Tests (ISSUE-0409 BRANCH/LOOP/FOR_EACH/TRY_CATCH/THROW/BREAK/CONTINUE/DISCARD) ===|java -ea -cp build deal.test.ControlFlowLoweringTest'
  'fg|=== Running Evaluation Order Integration Tests (ISSUE-0410, decomposition tail) ===|java -ea -cp build deal.test.EvaluationOrderIntegrationTest'
  'fg|=== Running the Runtime Integration Matrix (ISSUE-0410: semantic oracle + shared LuaJIT + shared JVM) ===|java -ea -cp build deal.test.RuntimeIntegrationMatrixTest'
  # ISSUE-0582 registration: the CALLS family's FUNCTION_ADAPT/
  # CALLBACK_INVOKE differential corpus (sequencing step 6 first half).
  'fg|=== Running the Call Adapter / Callback Integration Matrix (ISSUE-0582: semantic oracle + shared LuaJIT + shared JVM) ===|java -ea -cp build deal.test.CallAdapterCallbackIntegrationTest'
  # ISSUE-0583 registration: the CALLS family's ASYNC_START/AWAIT
  # differential corpus (sequencing step 6 second half).
  'fg|=== Running the Async Start / Await Integration Matrix (ISSUE-0583: semantic oracle + shared LuaJIT + shared JVM) ===|java -ea -cp build deal.test.AsyncStartAwaitIntegrationTest'
  # ISSUE-0586 registration: the CLASSES family's CLASS_DEFAULT/
  # CLASS_NEW/CLASS_FACTORY differential corpus (sequencing step 8 first
  # slice; semantic oracle + shared LuaJIT + shared JVM).
  'fg|=== Running the Class Construction Differential Matrix (ISSUE-0586: semantic oracle + shared LuaJIT + shared JVM) ===|java -ea -cp build deal.test.ClassConstructionDifferentialTest'
  'fg|=== Running Unicode Scalars Tests (ISSUE-0382, ISSUE-0232 D5) ===|java -ea -cp build deal.test.UnicodeScalarsTest'
  'fg|=== Running Failure Contract Registry Tests (ISSUE-0285) ===|java -ea -cp build deal.test.FailureContractRegistryTest'
  'fg|=== Running Canonical JSON / Snapshot Digest Tests (ISSUE-0283) ===|java -ea -cp build deal.test.CanonicalJsonTest'
  'fg|=== Running Semantic IR Validator Tests (ISSUE-0286) ===|java -ea -cp build deal.test.SemanticIrValidatorTest'
  'fg|=== Running Dynamic Resolution IR Tests (ISSUE-0531) ===|java -ea -cp build deal.test.DynamicResolutionIrTest'
  'fg|=== Running Boundary Table Corpus Tests (ISSUE-0366, wiki Verification 4) ===|java -ea -cp build deal.test.BoundaryTableCorpusTest'
  'fg|=== Running Boundary Integration Tests (ISSUE-0367, decomposition tail) ===|java -ea -cp build deal.test.BoundaryIntegrationTest'
  'fg|=== Running Control Flow Validator Tests (ISSUE-0408) ===|java -ea -cp build deal.test.ControlFlowValidatorTest'
  'fg|=== Running Semantic IR Dumper / ID Allocator Tests (ISSUE-0287) ===|java -ea -cp build deal.test.SemanticIrDumperTest'
  'fg|=== Running Semantic Table / Array Value Model Tests (ISSUE-0383 C2) ===|java -ea -cp build deal.test.SemanticTableTest'
  'fg|=== Running Container Ops Executor Tests (ISSUE-0384 C3) ===|java -ea -cp build deal.test.ContainerOpsExecutorTest'
  'fg|=== Running Comparison Selector Lowering Tests (ISSUE-0407) ===|java -ea -cp build deal.test.ComparisonSelectorLoweringTest'
  'fg|=== Running Container Lowering Arms Tests (ISSUE-0386) ===|java -ea -cp build deal.test.ContainerLoweringArmsTest'
  'fg|=== Running Container Claiming Seam Tests (ISSUE-0387) ===|java -ea -cp build deal.test.ContainerClaimingSeamTest'
  'fg|=== Running Container Integration Tests (ISSUE-0388, decomposition tail) ===|java -ea -cp build deal.test.ContainerIntegrationTest'
  'fg|=== Running Binding Core Lowering Tests (ISSUE-0444 binding-core child) ===|java -ea -cp build deal.test.BindingCoreLoweringTest'
  'fg|=== Running Closure Lowering Tests (ISSUE-0445 closure child) ===|java -ea -cp build deal.test.ClosureLoweringTest'
  'fg|=== Running Recursive Group Lowering Tests (ISSUE-0446 group child) ===|java -ea -cp build deal.test.RecursiveGroupLoweringTest'
  'fg|=== Running Function Binding Registry Tests (ISSUE-0447 registry child) ===|java -ea -cp build deal.test.FunctionBindingRegistryTest'
'fg|=== Running Binding Immutability Proof Tests (ISSUE-0448 proof child) ===|java -ea -cp build deal.test.BindingImmutabilityProofTest'
'fg|=== Running Adapter Creation Rule Tests (ISSUE-0449 creation-rule child) ===|java -ea -cp build deal.test.AdapterCreationRuleTest'
'fg|=== Running Adapter Shape Map / Payload Tests (ISSUE-0450 shape-map child) ===|java -ea -cp build deal.test.AdapterShapeMapPayloadTest'
'fg|=== Running Bindings Production Validation Tests (ISSUE-0451 B9 validation child) ===|java -ea -cp build deal.test.BindingsValidationTest'
'fg|=== Running Bindings Integration Verification (ISSUE-0452, sequencing item 9) ===|java -ea -cp build deal.test.BindingsIntegrationVerificationTest'
  # ISSUE-0632 registration: the intrinsic seed registrations and the
  # closed bindings-gate admission (project-lowering-entry-and-registration-seeds
  # D7/D13, the registration-seed contract; semantic-ir-construct-coverage-cutover
  # K9 item 7 and K14's registration half).
  'fg|=== Running Intrinsic Seed Bindings / Closed Gate Admission Tests (ISSUE-0632) ===|java -ea -cp build deal.test.IntrinsicSeedBindingsTest'
  # ISSUE-0673 registration: the closed DynamicFunctionValue member, its
  # canonical/raw shapes, the registry entry point, and the shape-admission
  # and producing-op correlation clauses
  # (function-typed-value-materialization-and-dispatch M1/M3 items 1-2;
  # semantic-ir-construct-coverage-cutover K9 item 4).
  'fg|=== Running Dynamic Function Value Binding / Closed Shapes Tests (ISSUE-0673) ===|java -ea -cp build deal.test.DynamicFunctionValueBindingTest'
  # ISSUE-0674 registration: the closed gate of the function-typed
  # materialization (the producing-position clause, the callee-position
  # exclusivity, and the dynamic cell family) plus the intrinsic-load and
  # VALUE-over-intrinsic refinements the identity-preserving function-typed
  # load of the seeded intrinsic binding requires
  # (function-typed-value-materialization-and-dispatch M2 item 4, M3 items 3-6;
  # conversion-intrinsic-function-values J1).
  'fg|=== Running Dynamic Function Value Gate / Identity-Preserving Intrinsic Load Tests (ISSUE-0674) ===|java -ea -cp build deal.semantic.DynamicFunctionValueGateTest'
  # ISSUE-0675 registration: the closed producer rule's lowering arms —
  # the typed binding load, the member/index/field reads, the
  # optional-read envelope, the call result (direct, dynamic, and
  # imported) and the AWAIT completion result register exactly one
  # DynamicFunctionValue keyed by their producing op, the imported export
  # read and the tracked alias keep their landed static class, and every
  # produced unit passes the schema and bindings gates in one pass
  # (function-typed-value-materialization-and-dispatch M2 items 1-3 and 5;
  # semantic-ir-construct-coverage-cutover K11/K12).
  'fg|=== Running Dynamic Producer Rule / Materialization Arms Tests (ISSUE-0675) ===|java -ea -cp build deal.semantic.DynamicProducerRuleTest'
  'fg|=== Running Protected Path Ops Tests (ISSUE-0262) ===|java -ea -cp build deal.test.ProtectedPathOpsTest'
  'fg|=== Running Identity Carrier Package Tests (ISSUE-0309) ===|java -ea -cp build deal.test.CanonicalIdentityTest'
  'fg|=== Running Sidecar Schema Validator Tests (ISSUE-0348) ===|java -ea -cp build deal.test.conformance.SidecarSchemaValidatorTest'
  'fg|=== Running Sidecar Corpus Validation Tests (ISSUE-0349) ===|java -ea -cp build deal.test.conformance.SidecarCorpusValidationTest'
  'fg|=== Running Strict Manifest Parser Tests (ISSUE-0263 T2) ===|java -ea -cp build deal.project.StrictManifestParserTest'
  'fg|=== Running Output Config Resolver Tests (ISSUE-0264 T3) ===|java -ea -cp build deal.project.OutputConfigResolverTest'
  'fg|=== Running Project Locator Tests (ISSUE-0265 T4) ===|java -ea -cp build deal.project.ProjectLocatorTest'
  'fg|=== Running Module Identity Resolver Classifier Tests (ISSUE-0266 T5) ===|java -ea -cp build deal.module.ModuleIdentityResolverTest'
  'fg|=== Running Module Identity Assembly Tests (ISSUE-0268 T7) ===|java -ea -cp build deal.module.ModuleIdentityAssemblyTest'
  'fg|=== Running C FFI Declaration Validation and Forward Binding Tests (ISSUE-0162) ===|java -ea -cp build deal.test.FfiDeclarationValidatorTest'
  'fg|=== Running AST/Types Tests ===|java -ea -cp build deal.test.AstAndTypesTest'
  'fg|=== Running Types Bytes Tests (ISSUE-0308) ===|java -ea -cp build deal.test.TypesBytesTest'
  'fg|=== Running Directive Tests ===|java -ea -cp build deal.test.DirectiveTest'
  'fg|=== Running Lexer Tests ===|java -ea -cp build deal.test.LexerTest'
  'fg|=== Running Parser Tests ===|java -ea -cp build deal.test.ParserTest'
  'fg|=== Running Checker Tests ===|java -ea -cp build deal.test.CheckerTest'
  'fg|=== Running IR Dumper Tests ===|java -ea -cp build deal.test.IrDumperTest'
  'fg|=== Running IR Golden Tests ===|java -ea -cp build deal.test.IrGoldenTest'
  'fg|=== Running Type Descriptor Tests ===|java -ea -cp build deal.test.TypeDescriptorTest'
  'fg|=== Running Descriptor Emission Byte Identity Tests (ISSUE-0315) ===|java -ea -cp build deal.test.DescriptorEmissionByteIdentityTest'
  'fg|=== Running Canonical Runtime Type Descriptor Tests (ISSUE-0310/0311/0314) ===|java -ea -cp build deal.test.CanonicalRuntimeTypeDescriptorTest'
  'fg|=== Running Runtime Type Matcher Tests (ISSUE-0312) ===|java -ea -cp build deal.test.RuntimeTypeMatcherTest'
  'fg|=== Running JS Backend Unit Tests ===|java -ea -cp build deal.test.JsBackendTest'
  'fg|=== Running JS E2E Tests ===|java -ea -cp build deal.test.JsE2eTest'
  'fg|=== Running Lua Backend Tests ===|java -ea -cp build deal.test.LuaBackendTest'
  'fg|=== Running Lua Backend Integration Tests ===|java -ea -cp build deal.test.LuaBackendIntegrationTest'
  'fg|=== Running Module System Tests ===|java -ea -cp build deal.test.ModuleSystemTest'
  'fg|=== Running Project Migration Integration Tests (ISSUE-0269 T8) ===|java -ea -cp build deal.test.ProjectMigrationIntegrationTest'
  'fg|=== Running Project Integration Gates (ISSUE-0270 T9: out-of-root both-backend gates) ===|java -ea -cp build deal.test.ProjectIntegrationGatesTest'
  'fg|=== Running Production Project-Graph Fixture Gates (ISSUE-0506 D11) ===|java -ea -cp build deal.test.ProjectGraphFixturesGatesTest'
  # ISSUE-0630 registration: the declaration surface producer — the host
  # and extern-C per-declaration-module facts (exports, order, per-class
  # field records and kinds), the retained JS declared-map byte
  # identity, the descriptor-path negative seed, and the surface-shape
  # invariants (project-lowering-entry-and-registration-seeds D3).
  'fg|=== Running Host Declaration Surface Tests (ISSUE-0630) ===|java -ea -cp build deal.test.HostDeclarationSurfaceTest'
  # ISSUE-0631 registration: the project-level class registration seeds —
  # the three closed DefaultOwner members, one ClassRegistration per
  # declared class of every declaration module of the real T1 surface
  # (host and extern-C, with the plan cross-check), the compiler-owned
  # builtin Error layout, the negative seeds, and the fail-closed
  # consumer arms (project-lowering-entry-and-registration-seeds D4-D6
  # and the registration-seed contract; semantic-ir-construct-coverage-
  # cutover K9 items 3/6 and K13 item 1).
  'fg|=== Running Class Registration Seeds Tests (ISSUE-0631) ===|java -ea -cp build deal.test.ClassRegistrationSeedsTest'
  'fg|=== Running Source Module Resolver Tests (ISSUE-0267 T6) ===|java -ea -cp build deal.module.SourceModuleResolverTest'
  'fg|=== Running LuaJIT Async Export Invoker Tests (ISSUE-0417 component, ISSUE-0418 verification matrix) ===|java -ea -cp build:/usr/share/java/junit4.jar:/usr/share/java/hamcrest-core.jar org.junit.runner.JUnitCore deal.test.LuaJitAsyncExportInvokerTest'
'fg|=== Running Registry Async-Export Boundary Tests (ISSUE-0346 REGISTRY) ===|java -ea -cp build:/usr/share/java/junit4.jar:/usr/share/java/hamcrest-core.jar org.junit.runner.JUnitCore deal.test.RegistryAsyncExportBoundaryTest'
  'fg|=== Running JVM Async Export Invoker Tests (ISSUE-0161 JVM host ABI) ===|java -ea -cp build:/usr/share/java/junit4.jar:/usr/share/java/hamcrest-core.jar org.junit.runner.JUnitCore deal.test.JvmAsyncExportInvokerTest'
  'fg|=== Running JVM Registry Async-Export Boundary Tests (ISSUE-0161 JVM lane of the REGISTRY boundary) ===|java -ea -cp build:/usr/share/java/junit4.jar:/usr/share/java/hamcrest-core.jar org.junit.runner.JUnitCore deal.test.JvmRegistryAsyncExportBoundaryTest'
  'fg|=== Running Stdlib .d.deal Parse Tests ===|java -ea -cp build deal.test.StdlibDeclParseTest'
  'fg|=== Running Source Map Tests ===|java -ea -cp build deal.test.SourceMapTest'
  'fg|=== Running Runtime Source Location Tests ===|java -ea -cp build deal.test.RuntimeSourceLocationTest'
  'luajit|=== Running Runtime Library Tests ===|luajit test_runtime.lua
luajit test_runtime_int32.lua
WARNING: luajit not found, skipping runtime library tests'
  'luajit|=== Running Lua Async Export Driver Tests ===|luajit test/lua_async_export_driver_test.lua
WARNING: luajit not found, skipping async export driver tests'
  'luajit|=== Running Jsonable Runtime Tests ===|luajit test_runtime_jsonable.lua
WARNING: luajit not found, skipping jsonable runtime tests'
  'node|=== Running Jsonable Runtime JS Tests ===|node test_jsonable_js.js
WARNING: node not found, skipping jsonable runtime JS tests'
  'node|=== Running Host ABI Runtime JS Tests ===|node test_host_js.js
WARNING: node not found, skipping host ABI runtime JS tests'
  'luajit|=== Running Standard Library Tests ===|luajit test_stdlib.lua
WARNING: luajit not found, skipping standard library tests'
  'node|=== Running Standard Library JS Tests ===|node test_stdlib_js.js
WARNING: node not found, skipping standard library JS tests'
  'luajit|=== Running Async Nesting Stress Tests ===|luajit test_async_nesting.lua
WARNING: luajit not found, skipping async nesting stress tests'
  'fg||java -ea -cp build deal.test.StdlibContractTest'
  'golden-ir|=== Stdlib Golden IR Check ===|java -ea -cp build deal.test.GenerateStdlibGoldenIr "$TEMP_FILE" 2>/dev/null'
  'fg|=== Running Conformance Harness Metadata Seam Tests ===|java -ea -cp build deal.test.ConformanceHarnessMetadataTest'
  # ISSUE-0457 registration: the DistributionHome tier-selection proofs
  # (project-local, classpath-resource, DEAL_HOME, and CWD tiers).
  'fg|=== Running Distribution Home Tier-Selection Tests (ISSUE-0457) ===|java -ea -cp build deal.test.DistributionHomeTest'
  # ISSUE-0458 registration: the transactional publication contract
  # suite (whole-project-artifact-publication Verification 1-7).
  'fg|=== Running Publication Stager Tests (ISSUE-0458) ===|java -ea -cp build deal.test.PublicationStagerTest'
  # ISSUE-0493 registration: the closed stdlib catalog and the
  # checked-fact recognition predicate (stdlib-operations-and-time-lock
  # D1, sequencing item 1).
  'fg|=== Running Stdlib Function Catalog / Checked-Fact Recognition Tests (ISSUE-0493) ===|java -ea -cp build deal.test.StdlibFunctionCatalogTest'
  # ISSUE-0494 registration: the STDLIB_CALL lowering arm — the
  # 20-id battery, argument operand completion, descriptor-kind-rule
  # boundaries, single-source policy stamping, dump determinism, the
  # validator negative, and the time lock (stdlib-operations-and-time-lock
  # D2, Verification 4; sequencing item 2).
  'fg|=== Running Stdlib STDLIB_CALL Lowering Tests (ISSUE-0494) ===|java -ea -cp build deal.test.StdlibCallLoweringTest'
  # ISSUE-0495 registration: the single stdlib algorithm executor —
  # the 20-id family batteries, exact projections, the console effect
  # contract, boundary precedence, and the combined T2/T1 drive
  # (stdlib-operations-and-time-lock D4/D5, Verification 1 and 3;
  # sequencing item 3).
  'fg|=== Running Shared Stdlib Semantics Tests (ISSUE-0495) ===|java -ea -cp build deal.test.SharedStdlibSemanticsTest'
  # ISSUE-0496 registration: the stdlib failure-projection wiring and
  # boundary realization reporting — exact projections, precedence,
  # realization reports, and the validator stdlibCell negative
  # (stdlib-operations-and-time-lock D6, Verification 2 and 4;
  # sequencing item 4).
  'fg|=== Running Stdlib Failure Projection / Boundary Realization Tests (ISSUE-0496) ===|java -ea -cp build deal.test.StdlibFailureProjectionTest'
  # ISSUE-0497 registration: the STDLIB_SEMANTICS claiming arms, the
  # time-lock negative proofs, and the stdlib-export value-read
  # disposition (stdlib-operations-and-time-lock D3/D8/D9,
  # Verification 4 and 5; sequencing item 5).
  'fg|=== Running Stdlib Claiming / Time-Lock Tests (ISSUE-0497) ===|java -ea -cp build deal.test.StdlibClaimingTimeLockTest'
  'fg|=== Running Stdlib Target-Helper Equivalence Battery (ISSUE-0498) ===|java -ea -cp build deal.test.StdlibEquivalenceBatteryTest'
  # ISSUE-0499 registration: the epic's decomposition tail — one
  # pipeline drives T1-T6 end-to-end (catalog, lowering, the shared
  # algorithms, the exact projections, the claiming seam plus the time
  # lock and the D3 disposition, and the equivalence-battery verdicts),
  # and the injected-fault variants prove the all-constituents contract
  # (stdlib-operations-and-time-lock Contracts §Integration verification
  # task, Verification 7-8; sequencing item 7, the last task).
  'fg|=== Running Stdlib Integration Verification (ISSUE-0499, decomposition tail) ===|java -ea -cp build deal.test.StdlibIntegrationTest'
  'fg|=== Running Class Declaration Lowering Tests (ISSUE-0511 declaration arm) ===|java -ea -cp build deal.test.ClassDeclarationLoweringTest'
  # ISSUE-0512 registration: the CLASS_NEW LOCAL execution battery —
  # the closed K-D4/D16 order with fixture side-effect probes
  # (class-construction-jsonable-operations K-D4/K-D11,
  # Verification 1; sequencing item 2).
  'fg|=== Running Class Ops Executor Tests (ISSUE-0512 K-D4/K-D11) ===|java -ea -cp build deal.test.ClassOpsExecutorTest'
  # ISSUE-0512 registration: the CLASS_NEW LOCAL lowering battery —
  # the pinned literal payload shapes, the combined T1+T2 executor
  # drive, and determinism (class-construction-jsonable-operations
  # K-D4; sequencing item 2).
  'fg|=== Running Class New Lowering Tests (ISSUE-0512 LOCAL arm) ===|java -ea -cp build deal.test.ClassNewLoweringTest'
  # ISSUE-0513 registration: the field-operation executor battery — the
  # K-D6/K-D7 presence semantics, the canonical receiver projections,
  # and the commit discipline (class-construction-jsonable-operations
  # K-D6/K-D7, Verification 4; sequencing item 3).
  'fg|=== Running Call Machine Integration Verification (ISSUE-0236, E7) ===|java -ea -cp build deal.test.CallMachineIntegrationTest'
  'fg|=== Running Field Ops Executor Tests (ISSUE-0513 K-D6/K-D7) ===|java -ea -cp build deal.test.FieldOpsExecutorTest'
  # ISSUE-0513 registration: the field-operation lowering battery — the
  # pinned read/write/delete/has arms and the combined T1+T2+T3 drive
  # (class-construction-jsonable-operations K-D6/K-D7; sequencing
  # item 3).
  'fg|=== Running Field Ops Lowering Tests (ISSUE-0513 K-D6/K-D7 arms) ===|java -ea -cp build deal.test.FieldOpsLoweringTest'
  # ISSUE-0514 registration: the shared-factory executor battery —
  # driven through the assembled ClassOpsExecutor (K-D4/K-D5).
  'fg|=== Running Shared Factory Executor Tests (ISSUE-0514 K-D4/K-D5) ===|java -ea -cp build deal.test.SharedFactoryExecutorTest'
  # ISSUE-0514 registration: the shared-factory lowering battery — the
  # imported-construction slice through the extended two-module seam.
  'fg|=== Running Shared Factory Lowering Tests (ISSUE-0514 SHARED_FACTORY arm) ===|java -ea -cp build deal.test.SharedFactoryLoweringTest'
  # ISSUE-0540 registration: the carrier-shape battery main - one
  # foreground record (default-plan-carriers D10).
  'fg|=== Running Default Plan Carrier Shape Tests (ISSUE-0540) ===|java -ea -cp build deal.module.DefaultPlanCarriersTest'
  # ISSUE-0515 registration: the JSON walker executor battery — the
  # generated C$fromJson/C$toJson walk contracts over the fixture JSON
  # delegate (class-construction-jsonable-operations K-D8/K-D9/K-D10/
  # K-D11; sequencing item 5).
  'fg|=== Running Json Class Executor Tests (ISSUE-0515 K-D8/K-D9/K-D10/K-D11) ===|java -ea -cp build deal.test.JsonClassExecutorTest'
  # ISSUE-0515 registration: the generated @jsonable body lowering
  # battery — the pinned generated bodies, the JsonDefaultChildTable
  # record, and the combined T1..T5 end-to-end drive
  # (class-construction-jsonable-operations K-D8/K-D10; sequencing
  # item 5).
  'fg|=== Running Json Class Lowering Tests (ISSUE-0515 K-D8/K-D10) ===|java -ea -cp build deal.test.JsonClassLoweringTest'
  # ISSUE-0516 registration: the class epic's decomposition tail — the
  # production validator battery, the claiming seams, and the
  # end-to-end integration verification
  # (class-construction-jsonable-operations K-D7/K-D11, Verification 7;
  # sequencing item 6, the last task).
  'fg|=== Running Class Construction Validator Tests (ISSUE-0516 K-D11) ===|java -ea -cp build deal.test.ClassConstructionValidatorTest'
  'fg|=== Running Class Integration Verification (ISSUE-0516, decomposition tail) ===|java -ea -cp build deal.test.ClassIntegrationVerificationTest'
  'fg|=== Running Default Semantic Planner Tests (ISSUE-0541) ===|java -ea -cp build deal.test.DefaultSemanticPlannerTest'
  'fg|=== Running Default IR Recorder Tests (ISSUE-0541) ===|java -ea -cp build deal.module.DefaultIrRecorderTest'
  'fg|=== Running E2 Identity Integration Gates (ISSUE-0316) ===|java -ea -cp build deal.test.E2IdentityIntegrationGatesTest'
  'fg|=== Running Default Semantic Serializer Tests (ISSUE-0542) ===|java -ea -cp build deal.test.DefaultSemanticSerializerTest'
  'fg|=== Running Module Dependency Graph Tests (ISSUE-0543) ===|java -ea -cp build deal.test.ModuleDependencyGraphTest'
  'fg|=== Running Runtime Default Lowering Tests (ISSUE-0544) ===|java -ea -cp build deal.test.RuntimeDefaultLoweringTest'
  'fg|=== Running Runtime Construction Phases Tests (ISSUE-0545) ===|java -ea -cp build deal.test.RuntimeConstructionPhasesTest'
  'fg|=== Running Lua Lane Tests (ISSUE-0354) ===|java -ea -cp build deal.test.conformance.LuaLaneTest'
  'fg|=== Running JS Lane Tests (ISSUE-0356) ===|java -ea -cp build deal.test.conformance.JsLaneTest'
  'fg|=== Running JVM Lane Tests (ISSUE-0355) ===|java -ea -cp build deal.test.conformance.JvmLaneTest'
  'fg|=== Running Differential Gate Comparator Tests (ISSUE-0353) ===|java -ea -cp build deal.test.conformance.StructuredExpectationComparatorTest'
  'fg|=== Running Compile Diagnostic Comparator Tests (ISSUE-0353) ===|java -ea -cp build deal.test.conformance.CompileDiagnosticComparatorTest'
  'fg|=== Running Gate Dispatcher Tests (ISSUE-0353) ===|java -ea -cp build deal.test.conformance.GateDispatcherTest'
  'fg|=== Running Gate Classification Tests (ISSUE-0353) ===|java -ea -cp build deal.test.conformance.GateClassificationTest'
  'fg|=== Running Differential Gate Corpus Tests (ISSUE-0353) ===|java -ea -cp build deal.test.conformance.DifferentialGateCorpusTest'
  'fg|=== Running Differential Gate Lanes Corpus Tests (ISSUE-0357) ===|java -ea -cp build deal.test.conformance.DifferentialGateLanesCorpusTest'
  'fg|=== Running Capability Registry Transition Surface Tests (ISSUE-0485) ===|java -ea -cp build deal.test.CapabilityRegistryTransitionTest'
  'fg|=== Running Semantic Production Gate Tests (ISSUE-0239) ===|java -ea -cp build deal.test.SemanticProductionGateTest'
  'fg|=== Running Class Construction Integration Tail Tests (ISSUE-0517) ===|java -ea -cp build deal.test.ClassConstructionIntegrationTailTest'
  'fg|=== Running the Module Init Differential Matrix and the Shared-Emitter Totality Gate (ISSUE-0590) ===|java -ea -cp build deal.test.ModuleInitDifferentialTest'
  # ISSUE-0633 registration: the import alias-cell list on MODULE_IMPORT
  # and the per-imported-module namespace registrations (the recording
  # half of project-lowering-entry-and-registration-seeds D8 and of
  # semantic-ir-construct-coverage-cutover K9 item 8/K15 items 1-2).
  'fg|=== Running Import Alias Cells / Namespace Registration Tests (ISSUE-0633) ===|java -ea -cp build deal.test.ModuleImportNamespaceRegistrationTest'
  # ISSUE-0634 registration: the one project lowering entry, the one
  # allocator, and the composed validator chain
  # (project-lowering-entry-and-registration-seeds D1/D2/D4/D8/D11/D12
  # and the project lowering, registration-seed, namespace registration,
  # and project validation gate contracts;
  # luajit-jvm-single-lowering-production-cutover C1/C4/C7/C10;
  # semantic-ir-construct-coverage-cutover K3/K12's lowering context):
  # the real multi-module checked project closure, the one allocator, the
  # byte-identical repeated project dumps, the seeds/intrinsic
  # bindings/namespace registrations delivery, the composed per-unit
  # chain over the E7-armed unified units, the four named negative seeds,
  # and the declaration-class fail-closed acceptance.
  # ISSUE-0636 extends the same main (its only test-list change is none):
  # the in-project imported-class resolution — CLASS_NEW(SHARED_FACTORY)
  # with the owner's constructionEntry and factory-result reference, the
  # declaration-order boundaries, the accumulated EXTERNAL_ENTRY
  # resolution of a cross-module call, and the inconsistent-fact deferral
  # seed (project-lowering-entry-and-registration-seeds D10 and the
  # in-project imported-class contract; semantic-ir-construct-coverage-
  # cutover K3).
  'fg|=== Running Project Lowering Entry Tests (ISSUE-0634) ===|java -ea -cp build deal.test.ProjectLoweringTest'
  # ISSUE-0635 registration: the body-invocation identity takeover and
  # the never-called guard removal
  # (project-lowering-entry-and-registration-seeds D9 and the
  # body-invocation identity contract;
  # luajit-jvm-single-lowering-production-cutover C10;
  # semantic-ir-construct-coverage-cutover K12's lowering side): the three
  # statically-uninvoked body shapes lower through the project entry with
  # zero CONSTRUCT_UNLOWERED, each body's RETURN identity resolves to
  # exactly one emitted op, each body carries exactly one body-local
  # FUNCTION_RETURN cell, the carrier-slice entry (whose
  # uncalled-declaration guard is deleted) lowers a never-called
  # declaration to a validating unit through its own frontend chain, and
  # the two producer-defect negatives fail R-BOUNDARY-TRIPLE.
  'fg|=== Running Body-Invocation Identity Tests (ISSUE-0635) ===|java -ea -cp build deal.test.BodyInvocationIdentityTest'
  # ISSUE-0637 registration: the project-gate fault battery and the
  # unchanged-surface audit
  # (project-lowering-entry-and-registration-seeds Sequencing item 6 and
  # Verifications 7-8, D11/D12; semantic-ir-construct-coverage-cutover
  # K9's frozen extension set; luajit-jvm-single-lowering-production-
  # cutover C5/C6): one fault per newly composed gate clause driven
  # through the real lowerProject entry (the declaration-fact faults and
  # the inconsistent-fact deferral) and through the same composed
  # per-unit chain over units the entry produced (the intrinsic
  # admission clauses, the alias/namespace agreement, and the two
  # body-local producer defects), each returning the first E6005 with its
  # rule, module, capability, and origin and producing no project, no
  # tables, no registries, no seeds, and no registrations; plus the
  # frozen-surface assertions over the real loaded closed sets, the
  # payload-record shapes, the version text and both dump key sets, the
  # production source surface (no lowerProject call site), JavaScript,
  # the retained classes, and the gate manifest itself.
  'fg|=== Running Project-Gate Fault Battery / Unchanged-Surface Audit Tests (ISSUE-0637) ===|java -ea -cp build deal.test.ProjectGateFaultBatteryTest'
  # ISSUE-0639 registration: the module export-surface registry in both
  # project-mode sessions (the module-identity key)
  # (production-project-emission-and-atomic-cutover P2 and the module
  # export-surface contract; luajit-jvm-single-lowering-production-
  # cutover C2 and the production LuaJIT/JVM emission contracts;
  # semantic-ir-construct-coverage-cutover K15 item 1): one chunk-global
  # registry keyed by the dotted module path on LuaJIT (one
  # JvmRuntime.Table per module on the JVM), created idempotently before
  # the module walks, the EXPORT_PUBLISH write with the landed entry
  # shape, the production chunk's entry-surface return, the shared
  # single-unit shapes, the real-toolchain execution probes (a two-module
  # project without a cross-module call, the declaration-order entries,
  # the repeated dealMain()/cross-chunk idempotence), and the
  # byte-identical repeated emission.
  'fg|=== Running Module Export Surface Tests (ISSUE-0639) ===|java -ea -cp build deal.test.ModuleExportSurfaceTest'
  # ISSUE-0641 registration: the JVM production project entry
  # (JvmSemanticEmitter.emitProductionProject) — one public final class
  # with public static void main and the dealMain() drive carrying the
  # whole closure, the trace protocol suppressed, the production
  # DEAL_ERROR_CODE terminal, the one entry-module ENTRY_INVOKE
  # delegation, and the per-module export-surface registry keyed by the
  # module identity (production-project-emission-and-atomic-cutover
  # P1/P2/P3 and the production JVM emission contract;
  # luajit-jvm-single-lowering-production-cutover C2): the verbatim
  # className use, the emitted-text shapes (the runtime-class-only
  # imports, one dealMain() drive, one main delegation, the surface
  # registry and its declaration-order writes), the real-toolchain
  # javac --release 25 -proc:none + java run (empty success output, no
  # R| trace line, the two per-module surfaces after the run, the
  # repeated dealMain() drive), the E8004 terminal, and the
  # byte-identical repeated emission.
  'fg|=== Running JVM Production Project Emission Tests (ISSUE-0641) ===|java -ea -cp build deal.test.JvmProductionProjectEmissionTest'
  # ISSUE-0640 registration: LuaSemanticEmitter.emitProductionProject —
  # the production project entry (production-project-emission-and-
  # atomic-cutover P1/P3 and the production LuaJIT emission contract;
  # luajit-jvm-single-lowering-production-cutover C2): the entry's
  # signature and inputs (the validated project, the tables, and the
  # registries only), one chunk with the trace protocol suppressed and
  # the DEAL_ERROR_CODE terminal, the observable one-main probe, the
  # module export-surface registry with the entry-surface return, the
  # real-luajit execution (the clean run and the E8004 terminal), the
  # executed surfaces (the T1 dependency), and byte-identical repeated
  # emission.
  'fg|=== Running Lua Production Project Emission Tests (ISSUE-0640) ===|java -ea -cp build deal.test.LuaProductionProjectEmissionTest'
  # ISSUE-0642 registration: the production project emission unit
  # (deal.module.ProductionProjectEmission) — the C9 warning, the one
  # project lowering over the compile's declared inputs, the pre-emission
  # closure guard's narrowed extern-C declaration-import shape (ISSUE-0656),
  # the one production emission per target, the one staged project
  # artifact plus the unchanged LuaJIT runtime/stdlib deployment copies,
  # and the fail-closed E6005 mapping
  # (production-project-emission-and-atomic-cutover P5/P6/P7/P9/P11 and
  # the production-arm, source-map, and fail-closed producer-guard
  # contracts; luajit-jvm-single-lowering-production-cutover
  # C3/C4/C5/C7/C8/C9; host-module-load-and-host-call-realization H6 and
  # the extern-C remnant contract; cross-module-call-realization X3): the
  # one public static entry and its input set, the pinned warning texts and
  # the narrowed HOST_MODULE_IMPORT token, the two-module fixture's
  # one staged artifact per target (`app.lua`/`App.java`) with no sidecar
  # and the byte-identical repeated staging, the real luajit execution
  # (the one-main probe) and the javac --release 25 -proc:none + java
  # run, the atomic-failure cases (a bytes-bearing lowering and a
  # cross-module sync-call emission each stage nothing), the
  # HOST-declaration import's emitted declared-map load and staged
  # artifact, the extern-C declaration-import fail-closed outcome, the
  # cross-module async emission with the executed alias-token transcript
  # (the superseded EXTERNAL_ASYNC_CALL shape is removed), the same-module
  # async acceptance, and the source-map warning disposition. The fixture
  # inputs are gathered through a harness-invocation compile (P10 item 3)
  # and the unit is driven with the release-owned production invocation.
  'fg|=== Running Production Project Emission Tests (ISSUE-0642) ===|java -ea -cp build deal.test.ProductionProjectEmissionTest'
  # ISSUE-0643 registration: the phase-4 production dispatch and the
  # atomic cutover acceptance tests
  # (production-project-emission-and-atomic-cutover P4/P6/P7/P8/P10/P11
  # and the production-arm, source-map, zero-retained-reachability,
  # publication, and fail-closed producer-guard contracts;
  # luajit-jvm-single-lowering-production-cutover C3/C5/C7/C8;
  # conformance-lane-production-cutover L1/L4): the record-identity
  # production-invocation predicate (the release-owned record against
  # COMMON_SHADOW, LEGACY_REGRESSION, and the two test-only PUBLIC_BUILD
  # record families), the LuaJIT and JVM production compiles' one project
  # artifact with semanticEmissionCount()==1, retainedEmissionCount()==0,
  # routePlan()==null, empty jvmGeneratedResults(), no per-module
  # siblings, byte-identical repeats and real-toolchain execution, the
  # two-module realizable fixture with the executed per-module export
  # surfaces and the one-main probe, the conversion-overflow terminal,
  # the atomic-failure preservation of the previous artifact set, the
  # realized families (HOST-declaration import with its declared-map load
  # and one staged artifact, cross-module sync, cross-module async —
  # ISSUE-0656 removed the EXTERNAL_ASYNC_CALL shape), the fail-closed
  # families (bytes, function-typed materialization), the admitted
  # extern-C import on LuaJIT (the emitted load_ffi prelude, the
  # import-origin FFI_LIBRARY_LOAD, and the preserved JVM E6006), the
  # accepted same-module async closure, the C9 source-map disposition,
  # and the harness-arm dispatch rows.
  'fg|=== Running Production Dispatch and Cutover Acceptance Tests (ISSUE-0643) ===|java -ea -cp build deal.test.ProductionDispatchTest'
  # ISSUE-0618 registration: the canonical v1.2 failure-text parity test
  # (semantic-ir-construct-coverage-cutover K8 and Verification 9;
  # semantic-ir-construct-coverage-cutover K1/K2 for the drive): the
  # INT32_RESULT row and the row-driven producers (SharedValueSemantics,
  # the stdlib primitive) rendering `int out of safe range`, the
  # JSON_TO_ERROR row's corpus-aligned STDLIB_CALL(JSON_STRINGIFY)
  # rejection template with the pinned expected/actual pair, the
  # literal-carrying shared JVM runtime sites, and the two probes
  # (int32 overflow, json.stringify rejection) driving the one project
  # lowering through the oracle, the production LuaJIT artifact under
  # real luajit, and the production JVM artifact under javac --release 25
  # -proc:none plus java; plus the unchanged surfaces (the legacy-profile
  # corpus pin, the JS runtime / std/json.lua texts, the retained JVM
  # backend's legacy arm, and the four std/json and four int-overflow
  # corpus sidecars).
  'fg|=== Running Canonical Failure-Text Parity Tests (ISSUE-0618) ===|java -ea -cp build deal.test.CanonicalFailureTextParityTest'
  # ISSUE-0619 registration: the builtin Error construction, its field
  # surface, and the canonical err carriers
  # (semantic-ir-construct-coverage-cutover K13 and the K13 contract;
  # luajit-jvm-single-lowering-production-cutover C1's registration list):
  # the vertical drive (an Error literal with provided fields, a defaulted
  # Error literal, a field read, a field write observed through an alias,
  # and a catch-and-rethrow through the one project lowering, the composed
  # chain, the semantic oracle, and both shared artifacts under the real
  # luajit and javac/java toolchains), the CLASS_NEW(BUILTIN_DEFAULTS)
  # facts over the compiler-owned builtin layout, the @/Error boundary
  # crossings, the canonical carriers of both artifacts, the release-owned
  # production artifacts' DEAL_ERROR_CODE terminal, the named drivable
  # Error corpus fixtures, and the negative seeds (a non-builtin class
  # under BUILTIN_DEFAULTS, the has/delete checker rejections).
  'fg|=== Running Builtin Error Construction Tests (ISSUE-0619) ===|java -ea -cp build deal.test.BuiltinErrorConstructionTest'
  # ISSUE-0623 registration: time.nowMillis coverage through the closed
  # std.time/nowMillis catalog row (semantic-ir-construct-coverage-cutover
  # K7, the time.nowMillis contract, and K9 item 2): the 21st closed
  # selector member with the empty reservation list, the single zero-arity
  # std.time catalog row with its declared ()->int descriptors and the
  # INT32_RESULT terminal, the recognition path, the lowering shape
  # (STDLIB_CALL(TIME_NOW_MILLIS) with zero parameter boundaries and one
  # STDLIB_RETURN on int), the recorded STDLIB_TIME_NOW_MILLIS coverage row
  # with R-COVERAGE applied, the STDLIB_SEMANTICS claim with zero
  # STDLIB_TIME_CONFLICT claims, the vertical drive through the oracle and
  # both shared artifacts under the real luajit and javac/java toolchains
  # with the pinned E8004 int out of safe range terminal at the
  # call-expression origin, the real corpus fixture's production-artifact
  # drive on both targets, and the R-COVERAGE negative seed.
  'fg|=== Running time.nowMillis Coverage Tests (ISSUE-0623) ===|java -ea -cp build deal.test.TimeNowMillisCoverageTest'
  # ISSUE-0644 registration: the in-project imported-class construction
  # vertical three-consumer verification
  # (module-export-reads-and-in-project-class-construction M7 and the
  # in-project imported-class construction contract;
  # semantic-ir-construct-coverage-cutover K3;
  # luajit-jvm-single-lowering-production-cutover C1): the probe project
  # (the owner exports a class with a defaulted field; the entry imports
  # the owner and constructs the imported class literals; no cross-module
  # call exists) lowers through the one project entry with zero
  # RETAINED_ABI_DEFERRED to exactly one project, the entry unit's
  # CLASS_NEW(SHARED_FACTORY) payload facts (the owner interface
  # constructionEntry, the owner unit's layout, an empty local
  # default-child list, the literal-order provided fields, the
  # declaration-order boundaries wired to the owner factory result), the
  # composed validator verdict with the in-project facts (and the
  # facts-absent rejection proving the D10 producer is load-bearing), the
  # oracle's owner-module CLASS_FACTORY/CLASS_DEFAULT events parented to
  # the caller CLASS_NEW with the owner-scope default value observable
  # and the field reads publishing the constructed values, and the
  # production artifacts (one LuaJIT chunk; one JVM class) staged with
  # byte-identical repeated staging. Both artifacts construct through the
  # owner's factory and their field reads observe the constructed values
  # under the real toolchains (luajit; javac --release 25 -proc:none +
  # java). The emitter seam the drive exposed is repaired at its root: the
  # LuaJIT chunk pre-declares the detached class-default locals beside the
  # factory names and assigns them (instead of declaring them with
  # `local function` after the factories that reference them), and no
  # second fact producer or imported-class-specific emission arm is
  # added. The SHARED_FACTORY owner resolution is the delivered per-module
  # class-factory registry fact (the unique module whose registry binds the
  # construction entry), never the class descriptor namespace, so the
  # conventional root/module layout (root `src`, modules
  # `owner.deal`/`app.deal`) constructs through the owner's factory end to
  # end: the conventional-layout drive asserts the class-identity namespace
  # `@src/Address` against the module identity `owner`, the oracle's
  # success with the owner-attributed factory events and the constructed
  # field values, and both production artifacts executing under the real
  # toolchains with byte-identical repeated staging.
  'fg|=== Running In-Project Imported-Class Construction Vertical Tests (ISSUE-0644) ===|java -ea -cp build deal.test.InProjectClassConstructionVerticalTest'
  # ISSUE-0650 registration: the host module load and the JVM host ABI
  # emission surface (host-module-load-and-host-call-realization H1, H2
  # items 1-2, H7's carrier set, and the host-load contract;
  # luajit-jvm-single-lowering-production-cutover C2; sequencing step 1):
  # the LuaJIT inline load at the MODULE_IMPORT(HOST) op with the emitted
  # declared map in declaration order and the import statement's origin,
  # the one-load-per-module identity guard with a two-alias import (one
  # load, one shared surface value), the pinned E8011 defects (missing
  # declared export at the import origin, class identity mismatch,
  # missing <C>_defaults), the JVM module-keyed load entry with the
  # declared parameter-class projection and the <C>_defaults captures,
  # the per-export wrappers with the declared parameter/return cells and
  # the pinned E8010 texts, and the synthesized top-level $DealRt
  # host-record and host-carrier scope the deployed
  # test/conformance/host-fixtures implementations compile against. Both
  # artifacts execute under the real toolchains (luajit; javac --release
  # 25 -proc:none + java with the emitted wrappers driven directly), and
  # the production unit's two emitter call sites pass the declaration
  # surface through.
  'fg|=== Running Host Module Load / JVM Host ABI Surface Tests (ISSUE-0650) ===|java -ea -cp build deal.test.HostModuleLoadEmissionTest'
  # ISSUE-0659 registration: the import-member read production — the
  # value-position arm, the STDLIB catalog branch, and the exactly-one
  # registrations (import-member-read-arm-lowering-and-registration R1-R3
  # and R5, the import-read (lowering) contract, guard-table rows
  # G1/G2/G4/G5/G6; module-export-reads-and-in-project-class-construction
  # M1; semantic-ir-construct-coverage-cutover K2/K9;
  # luajit-jvm-single-lowering-production-cutover C1): the stub battery
  # per import kind in both positions (exactly one EXPORT_READ per source
  # occurrence with the expected payload, a USER origin at the access
  # span, parentOpId = the position's current parent, and the expected
  # registration shape and owner per kind — HostFunction for HOST and for
  # a cataloged STDLIB export with the row's declared descriptor,
  # ExternalFunction(SHARED_BODY) for a COMPILED import through the
  # session's callee-route facts), the non-function read with no
  # registration, the guards (unresolved alias, route-less COMPILED read,
  # out-of-catalog STDLIB member, STDLIB descriptor mismatch) each E6005
  # CONSTRUCT_UNLOWERED with no unit, the focused project runs (the
  # compiled companion's declared function export read with no invocation;
  # HOST and STDLIB in both positions; the slot convention pinned by a
  # class-default read publishing the CLASS_DEFAULT threaded cell and
  # keying its registration by it), the determinism of repeated lowerings,
  # and the registration/gate seeds (a duplicate rejected at registration
  # time and never overwritten; a zero-registration function-typed read
  # result failing the closed gate with R-FUNCTION-BINDING; the
  # unmodified units admitted on the typed and the text surface).
  'fg|=== Running Import-Member Read Arm Tests (ISSUE-0659) ===|java -ea -cp build deal.test.ImportMemberReadArmTest'
  # ISSUE-0646 registration: the compiled export read realization across
  # the three consumers plus the oracle's per-run published-surface
  # registry (module-export-reads-and-in-project-class-construction M2,
  # M3, M6, the read execution contract, and the export-read contract;
  # semantic-ir-construct-coverage-cutover K2;
  # luajit-jvm-single-lowering-production-cutover C1/C2): the probe
  # project whose entry reads a compiled companion's declared function
  # export twice into function-typed bindings (no cross-module
  # invocation) lowers through the one project entry and validates; the
  # LuaJIT publication's __val field and the nil-safe program-scoped
  # accessor read, the uniform JVM surface read over the class-level view
  # of the runtime-hosted registry, the mode-shared read operation in
  # both project sessions with byte-identical repeats; the oracle's
  # per-run published-surface registry (the read's trace SUCCESS atom is
  # the publication's own creation atom, both reads publish the identical
  # value, the export:<module>.<name> placeholder is gone, the value-keyed
  # binding map stays the producing allocation's — the owner-side
  # LoweredBody registration and the read's own allocation-identity
  # registration — and a doctored re-keying fails the closed gate); the
  # absent-slot projection of the landed partial drive (Value.MissingValue
  # / __MISSING / JvmRuntime.MISSING, atomizing as missing) in the oracle
  # and both per-unit artifacts; the three-consumer project trace matrix
  # under the real toolchains; the two-chunk/two-class per-unit
  # program-scoped registry drive (the identical published object for two
  # reads, and the JVM class-level field view being the runtime-hosted
  # registry instance); the production artifacts (the real luajit run and
  # the javac --release 25 -proc:none + java run with the read value being
  # the published JvmRuntime.FunctionValue carrier and the .f/.fn
  # retained-caller projections still calling the module function); and
  # the project-session ownership guard (a foreign owner fails both
  # project sessions closed, the per-unit sessions never do, and an
  # emitter failure maps to E6005 SHARED_EMITTER_COVERAGE with nothing
  # staged and the previous artifact set byte-identical).
  'fg|=== Running Compiled Export Read Realization Tests (ISSUE-0646) ===|java -ea -cp build deal.test.CompiledExportReadRealizationTest'
  # ISSUE-0648 registration: the HOST/FFI export-read execution
  # realization across the three consumers (module-export-reads-and-
  # in-project-class-construction M5, M3's HOST branch, M6, the host/FFI
  # read boundary contract, and the read execution contract;
  # semantic-ir-construct-coverage-cutover K15 item 1 — a HOST module's
  # surface is the loaded module table; luajit-jvm-single-lowering-
  # production-cutover C1/C2; sequencing step 6/T5): the checker-valid
  # declaration-only fixtures lowered/validated/registered in both
  # positions (exactly one EXPORT_READ with the declared function
  # descriptor plus exactly one HostFunction registration keyed by the
  # read result's allocation identity, and the composed project gate
  # admitting the project); the emitted read in both project sessions and
  # both modes of both targets (LuaJIT
  # S.v<id> = __exportHostValue(<module>, <name>) — the program-scoped
  # surface entry itself, absent -> __MISSING; JVM
  # v<id> = exportSurface(<module>).read(<name>) — the uniform read,
  # absent -> JvmRuntime.MISSING), the identical operation in the per-unit
  # sessions, byte-identical repeats, and no placeholder arm; the oracle's
  # per-kind resolution (an absent surface or entry projects
  # Value.MissingValue, a surface holding the recorded entries resolves the
  # entry itself — the publication's own creation atom — and no
  # export:<module>.<name> placeholder atom remains), the read's
  # registration addressable by its own allocation identity with the
  # doctored zero-registration/re-keyed seeds failing R-FUNCTION-BINDING;
  # the combined per-unit probe (the entry carries T3's compiled read and
  # this leaf's HOST read) resolved consistently across the oracle and both
  # per-unit artifacts under the real toolchains (luajit;
  # javac --release 25 -proc:none + java), with the absent-slot projection,
  # the compiled read's published-value identity, the pinned E8001 at the
  # HOST read's function-typed binding boundary, and the surface-populated
  # seeds resolving exactly the seeded entry; and the production arm's
  # HOST-declaration emit-and-stage outcome (ISSUE-0656 retargeted this
  # pin: the declared-map __rt.load_host call in the module init walk, the
  # one staged project artifact with no per-module sibling, no guard
  # token). No loader surface and no executable value-position drive are
  # added.
  'fg|=== Running Host Export Read Realization Tests (ISSUE-0648) ===|java -ea -cp build deal.test.HostExportReadRealizationTest'
  # ISSUE-0657 registration: the dynamic call shape production
  # (dynamic-call-shape-production-and-emission Y1/Y4 and the dynamic
  # call/async-start shape contracts;
  # semantic-ir-construct-coverage-cutover K5 and K12's form (b)): the
  # CALL(INDIRECT) with CallCallee.Dynamic, the declared-signature
  # FUNCTION_PARAMETER children, and the three recorded
  # DynamicReturnBoundary cells with the DEAL-body cell parented to the
  # call-owned RETURN naming the CALL; the ASYNC_START(Dynamic, DEAL_BODY,
  # RUN) with the single recorded task cell parented to the RETURN naming
  # the start, consumed by exactly one AWAIT/ASYNC_COMPLETION; the
  # identifier-callee and callee-expression arms; the gate-clean closure
  # carriers (the closed gate, the address-chain protocol, the
  # control-flow validator's call-owned-record admission, and the
  # bindings production validator pass; repeated dumps are byte-identical),
  # the pending materialization clause (R-FUNCTION-BINDING) of the
  # function-typed-value child, the unchanged static arms, and the
  # hand-built dynamic-cell/record negatives. The class lives in
  # package deal.semantic to reach the package-internal project walk.
  'fg|=== Running Dynamic Call Shape Production Tests (ISSUE-0657) ===|java -ea -cp build deal.semantic.DynamicCallLoweringTest'
  # ISSUE-0658 registration: the dynamic dispatch emission and the
  # function-id to owning-module resolution
  # (dynamic-call-shape-production-and-emission Y2/Y3/Y5/Y6, the dynamic
  # dispatch contract, the dynamic async start contract, and the boundary
  # with the function-typed-value child;
  # semantic-ir-construct-coverage-cutover K5/K12;
  # luajit-jvm-single-lowering-production-cutover C2): the emitted class
  # dispatch on both targets (the LuaJIT chunk-global __fnModules table
  # built by the walk that declares the function factories and the JVM
  # generated dealModuleOfFunction lookup over the closure's function
  # ids, the DEAL_BODY frame push and module switch with the carrier's own
  # invoker, the landed D15 adapter path with the leading-M projection,
  # the HOST row and the pinned E8001 expected/actual residue), the
  # closure-carrier, adapter-carrier, dynamic-async, and dynamic-async-
  # adapter drives whose oracle and trace-mode emitters agree
  # event-for-event and whose production artifacts execute under luajit
  # and javac --release 25 -proc:none + java, the residue and fault drives
  # (the non-function carrier's E8001, the adapter source-signature E8010,
  # the dynamically invoked DEAL body's own failing RETURN cell with the
  # callee's origin, and the adapter whose D15 source value identifies no
  # class the closed protocol resolves), the factory
  # triple (descriptor text, canonical spec text, function identity) and
  # the adapter's pinned null fid, and the unchanged closed op-kind,
  # boundary-kind, failure-policy, and payload sets. The drives register
  # the callee carrier read with the runtime carrier's own binding (the
  # pending DynamicFunctionValue materialization registration of
  # ISSUE-0622) and change nothing else of the one lowering's output. The
  # class lives in package deal.semantic to reach the package-internal
  # project walk.
  'fg|=== Running Dynamic Dispatch Emission Tests (ISSUE-0658) ===|java -ea -cp build deal.semantic.DynamicDispatchEmissionTest'
  # ISSUE-0647 registration: the spec-stdlib import-read realization in
  # the three consumers (module-export-reads-and-in-project-class-
  # construction M4, the cataloged stdlib callable contract, and M3's
  # STDLIB branch; semantic-ir-construct-coverage-cutover K2/K7;
  # luajit-jvm-single-lowering-production-cutover C2): the probe project
  # whose entry reads a std.console export (value and callee positions)
  # and a std.string algorithmic row into function-typed bindings lowers
  # through the one project entry and validates; the LuaJIT
  # __stdlibEntry accessor and the JVM JvmRuntime.stdlibCallable carrier
  # reads in both project sessions, the one surface entry per catalog row
  # of each imported STDLIB module in catalog order with the row's
  # canonical spec text, the one shared row invoker
  # (__stdlibInvoke/JvmRuntime.stdlibInvoke) of the direct STDLIB_CALL
  # arm with the console rows' single-effect write factored in, the
  # oracle's memoized Value.StdlibCallableValue per catalog row (the
  # carried signature admitted by the function-typed binding boundary,
  # the read registered once at its creation, a doctored differing
  # registration and a doctored differing descriptor both failing
  # closed), the direct arm's unchanged observable (exactly one console
  # effect write, the null result, the call-expression origin), the
  # three-consumer parity matrix, the combined compiled + stdlib read
  # composition over both production artifacts under the real toolchains,
  # the per-unit session read emission, and the reviewed comparison
  # correction (the cataloged callable integrated into the oracle's closed
  # comparison operand view; a checker-valid console.log === console.log /
  # console.log === console.error program driving the oracle and both
  # production artifacts to the identical identity outcomes).
  'fg|=== Running Stdlib Export Read Realization Tests (ISSUE-0647) ===|java -ea -cp build deal.test.StdlibExportReadRealizationTest'
  # ISSUE-0649 registration: the read-value integration verification leaf -
  # the consolidated three-consumer probe matrix, the per-unit multi-chunk
  # resolution probe, the exactly-one-binding and both-directions binding
  # invariants, the five negative seeds through the production arm, and the
  # emission-agreement/determinism assertions
  # (module-export-reads-and-in-project-class-construction Verification 1
  # (consolidated), 3, 5, 7, 8 and the Failure and operations section; the
  # read execution and export-read contracts;
  # semantic-ir-construct-coverage-cutover K2/K9;
  # luajit-jvm-single-lowering-production-cutover C2): one composition
  # project whose entry reads a compiled companion's declared function
  # export twice plus a std.console value read, a std.string row read, and
  # the console callee read lowers through the one project entry, validates,
  # runs the oracle and the three-consumer differential matrix, and stages
  # both production artifacts under the real toolchains (luajit;
  # javac --release 25 -proc:none + java) with no placeholder text, the
  # identical published object for two reads of one export, and the
  # identical memoized catalog callable for two stdlib reads; the per-kind
  # exactly-one registration (COMPILED/STDLIB/HOST) with the doctored
  # duplicate, zero-registration, and re-keying seeds; the owner-side
  # LoweredBody and read-side ExternalFunction(SHARED_BODY) directions; the
  # five fail-closed seeds (a non-exported member read, an unresolved
  # alias, an out-of-catalog stdlib member, a stdlib descriptor mismatch,
  # and a class-descriptor read) each E6005 CONSTRUCT_UNLOWERED through the
  # production arm with nothing staged and the previous artifact set
  # byte-identical; the mode-shared read operation with the byte-identical
  # body and repeated emissions; the absent-slot projection (missing)
  # identical in the oracle, the LuaJIT chunk, and the JVM class; the
  # two-chunk/two-class per-unit program-scoped registry resolution with
  # the identical published object and the runtime-hosted catalog
  # callable; and the retargeted-pin/registration assertions (the
  # previously pinned value-read E6005 assertions assert the realized
  # behavior, and the landed async-entry matrix stays registered).
  'fg|=== Running Read-Value Integration Verification Tests (ISSUE-0649) ===|java -ea -cp build deal.test.ReadValueIntegrationVerificationTest'
  # ISSUE-0651 registration: the sync host call arms and the
  # host-boundary crossings (host-module-load-and-host-call-realization
  # H3, H7, the sync host call contract, and the host-boundary carrier
  # projection contract; semantic-ir-construct-coverage-cutover K4;
  # luajit-jvm-single-lowering-production-cutover C2; sequencing step 2):
  # the CALL(HOST)/CALL(INDIRECT) and CALLBACK_INVOKE host arms on both
  # targets (the LuaJIT .f invocation with the trailing span triplet and
  # the pinned E8010 parameter/return cells at the call origin; the JVM
  # per-export wrapper with the import's origin triple), the H7 crossing
  # projection (the $DealRt function bridges, the declared element-shape
  # array carriers with the normal-return copy-back, the declared-return
  # materialization, the nullable-declared ?[T] array positions crossing
  # like their [T] form), the bridge's carrier resolution (the D15 protocol
  # for a production JvmRuntime.AdapterValue and the carried function id
  # pushed around a plain carrier invocation), the admitted sync host
  # fixture set executed end-to-end under luajit and javac --release 25
  # -proc:none + java with the sidecar-pinned outcomes and origins
  # (including the sidecar's attained expected/actual pair), and the
  # trace-mode oracle agreement drive (the trace-mode project sessions
  # carrying the declaration surface, the oracle's seam-supplied loaded
  # surface entry, and the event-for-event/terminal comparison).
  'fg|=== Running Sync Host Call Realization Tests (ISSUE-0651) ===|java -ea -cp build deal.test.HostCallRealizationTest'
  # ISSUE-0652 registration: the async host path through the operation
  # handle (host-module-load-and-host-call-realization H4 and the async
  # host start and completion contract; semantic-ir-construct-coverage-
  # cutover K4; sequencing step 4): ASYNC_START(HOST) invokes the loaded
  # declared async export through the same host-boundary call shape as the
  # sync arm (the loaded wrapper's declared-async shape check realizing the
  # op's ASYNC_OPERATION_HANDLE terminal with the pinned E8010 at the call
  # origin) and binds the returned operation handle to the canonical token;
  # AWAIT drives a handle-carrying LuaJIT record through the landed
  # __rt.async_step machinery (the operation's own DEAL error identical, a
  # non-DEAL failure rethrown as infrastructure) and joins the JVM
  # production JvmRuntime.startHostTask(tokenId, label, operation)
  # registration without reading JvmRuntime.HOST_ASYNC; the single
  # ASYNC_COMPLETION boundary at the await origin, the admitted async host
  # fixture set under luajit and javac --release 25 -proc:none + java with
  # the sidecar-pinned outcomes and origins, the pending-operation drive
  # with poisoned seams, the operation-failure and unloaded-surface
  # fail-closed seeds, and the combined trace-mode oracle agreement drive
  # (one load, a sync host call, an async host start and its await).
  'fg|=== Running Async Host Realization Tests (ISSUE-0652) ===|java -ea -cp build deal.test.AsyncHostRealizationTest'
  # ISSUE-0653 registration: the host value-position export read invocation
  # (host-module-load-and-host-call-realization H5 and the host value-read
  # invocation contract; semantic-ir-construct-coverage-cutover K2's
  # exactly-one HostFunction registration; module-export-reads-and-in-
  # project-class-construction M1/M5 read-only; sequencing step 3): the sync
  # form (let f: (…) => … = host.<export>; f(args)) and the async form
  # (let op: async () => string = host.fetchValue; await op()) lower through
  # the reads child's exactly one EXPORT_READ per source occurrence plus its
  # exactly one HostFunction registration, and execute through this epic's
  # static host arms — CALL(INDIRECT) and ASYNC_START(HOST) on the same
  # registration — on both targets and through the oracle with the same
  # cells, texts, origins, and effects the direct CALL(HOST) carries; neither
  # form produces or uses a CallCallee.Dynamic shape, the read is consumed
  # (never re-produced, re-registered, or re-checked), the corpus fixture
  # host-abi/host-async-shape-value keeps its pinned call-site E8010 (line 10
  # column 31) through the static route, the host load runs once per program
  # with the pinned E8011 checks holding in the drive, and a registration
  # whose module identity has no loaded surface fails closed. The LuaJIT
  # function row accepts the loaded host surface entry's own declared
  # canonical signature (the host ABI wrapper's sig metadata, beside the
  # DEAL carrier's internal text), and the oracle's closed value model gains
  # the loaded host entry value, so the read publishes the loaded entry on
  # every consumer.
  'fg|=== Running Host Value-Position Read Invocation Tests (ISSUE-0653) ===|java -ea -cp build deal.test.HostValueReadInvocationTest'

  # ISSUE-0654 registration: the cross-module sync call realization
  # through the callee unit's EXTERNAL_ENTRY
  # (cross-module-call-realization X1/X4/X5, the cross-module sync call
  # contract, and the entry record contract;
  # luajit-jvm-single-lowering-production-cutover C2/C7;
  # semantic-ir-construct-coverage-cutover K4): the six named corpus
  # fixtures lower through the one project entry with exactly one
  # EXTERNAL_PARAMETER child per argument in one-based order, no
  # caller-side return boundary, the callee's single EXTERNAL_RETURN on
  # the declared return descriptor, and the recorded externalEntryRef;
  # the oracle and both conformance emitters agree event-for-event over
  # the probe (a cross-module call, a same-module exported call, and
  # recursion), the failing probe, and all six fixtures; the production
  # artifacts execute on both targets with the pinned sidecar transcripts
  # (luajit; javac --release 25 -proc:none + java); the entry events
  # parent to the caller's CALL under the callee module with the caller's
  # module restored on the success and the failure path; and the
  # fail-closed seeds (an externalEntryRef naming a module outside the
  # closure, an externalEntryRef resolving to a non-entry op) are rejected
  # by both emitters and the oracle with nothing emitted.
  'fg|=== Running Cross-Module Call Realization Tests (ISSUE-0654) ===|java -ea -cp build deal.test.CrossModuleCallRealizationTest'

  # ISSUE-0655 registration: the cross-module async realization and the
  # external async link (cross-module-call-realization X2 and the
  # cross-module async call contract; luajit-jvm-single-lowering-production
  # -cutover C2; semantic-ir-construct-coverage-cutover K4): both emitters
  # emit one async entry per async EXTERNAL_ENTRY op of every closure unit
  # (the LuaJIT chunk keyed __asyncEntries["<owner>#<export>"], the JVM
  # class carrying the local ae<entryOpId> methods with no SharedM
  # reference), each entry resolving its function and capture cells through
  # its own unit and establishing its own module context around the callee
  # body and its own events (LuaJIT __modStack; the JVM per-entry module
  # literal with a finally restore); the caller's ASYNC_START(EXTERNAL)
  # publishes the alias token over the callee entry's canonical token and
  # the single AWAIT drains and runs the single ASYNC_COMPLETION boundary
  # on the declared descriptor; the composed drive executes a sync
  # cross-module call from the corpus fixture set jointly with the async
  # probe on both real toolchains (luajit; javac --release 25 -proc:none +
  # java) with the pinned completion value; the oracle and the per-unit
  # conformance emitters agree event-for-event through the differential
  # harness's async-entry matrix, and the project trace artifact carries
  # the callee module on the callee entry and body events; and the
  # fail-closed seeds (an async start without its ExternalAsyncLink, an
  # entry reference resolving to no emitted entry) are rejected by both
  # production emitters, and the production arm emits and stages the
  # closure's one project artifact (ISSUE-0656 removed the guard shape).
  'fg|=== Running Cross-Module Async Realization Tests (ISSUE-0655) ===|java -ea -cp build deal.test.CrossModuleAsyncRealizationTest'

  # ISSUE-0656 registration: the guard replacement, the pin retargeting,
  # and the production-arm drives
  # (host-module-load-and-host-call-realization H6 and the extern-C
  # remnant contract; cross-module-call-realization X3;
  # luajit-jvm-single-lowering-production-cutover C2/C4; read-only
  # production-project-emission-and-atomic-cutover P9/P10; sequencing
  # step 7): the replaced HOST_MODULE_IMPORT remnant (ISSUE-0656 narrowed
  # it to the extern-C declaration import, which ISSUE-0662 replaces when
  # it realizes the load_ffi table — no HOST-kind import trips the guard,
  # while the stable token, the detail fields, and the E6005 producer
  # stay landed), the removed EXTERNAL_ASYNC_CALL shape (the token has no
  # producer in the production source set and appears in no production
  # outcome), and the composed production-arm drives over
  # ProductionProjectEmission.run: the host closure (two host declaration
  # modules, the emitted declared-map loads, the sync and async host
  # calls, and both host value-position read forms through the static
  # arms) and the cross-module closure (the sync and async external
  # calls through the callee module's own async entry and the caller's
  # alias token), each with one project emission,
  # retainedEmissionCount() == 0, one staged project artifact, and the
  # pinned transcript under luajit and java.
  'fg|=== Running Guard Replacement Tests (ISSUE-0656) ===|java -ea -cp build deal.test.GuardReplacementTest'

  # ISSUE-0624 registration: host-declared class construction over the loaded
  # <C>_defaults (semantic-ir-construct-coverage-cutover K10, the K10 contract,
  # and K9 item 3; luajit-jvm-single-lowering-production-cutover C1;
  # host-module-abi D2 and the host-load contract; sequencing step 3): the
  # CLASS_NEW(HOST_DEFAULTS) lowering shape (the resolved class identity, the
  # null factory ref, the empty default-child list, exactly one
  # CLASS_LITERAL_FIELD boundary per provided field in declaration order, zero
  # RETAINED_ABI_DEFERRED, no RETAINED_ABI), the five pinned construction
  # phases over the loaded defaults entry (the per-attempt deep copy with the
  # sentinel identities preserved, the provided overlay with the E8007
  # extra-key rejection at the literal origin, the __MISSING removal, the
  # canonical identity tag), the field operations and has() through the
  # registered declaration layout with the alias-observed commits, the
  # combined host-class corpus fixtures (host-class-export,
  # host-class-default-isolation, host-export-presence,
  # plan-host-discriminator, host-class-extra-field) under real luajit and
  # javac --release 25 -proc:none + java together with the deployed corpus host
  # implementations and through the oracle's host-seam defaults projection,
  # and the call-free negative load seeds' pinned E8011 at the import origin.
  'fg|=== Running Host-Class Construction Tests (ISSUE-0624) ===|java -ea -cp build deal.test.HostClassConstructionTest'

  # ISSUE-0662 registration: the extern-C admission and the emitted FFI
  # load prelude (luajit-ffi-load-emission-and-typed-crossings F1/F2 and
  # the FFI import and load contract; ffi-admission-and-jvm-e6006-rejection
  # A1; luajit-ffi-shared-emission-and-jvm-rejection F1/F2; sequencing
  # step 1): the corpus fixtures ffi/025, ffi/026, and ffi/027 compile
  # through the production arm with the corpus's production FFI metadata
  # (CorpusFfi.module(...).generatedModule() and the bootstrapped loader
  # text) and execute under luajit with the sidecar-pinned outcomes (the
  # emitted load_ffi prelude carries the metadata module key, the
  # generated bundle/plans/bindings literals, and the import statement's
  # span triplet; FFI_SYMBOL_MISSING and FFI_LIBRARY_LOAD at the import
  # origin; ffi/027 clean); the admitted declaration imports (the extern-C
  # import's load_ffi and the HOST declaration import's load_host, with
  # the retained HOST_MODULE_IMPORT producer); one load per module shared
  # by two aliases; the fail-closed seeds (a missing generated-module
  # entry, a provider module outside the declaration surface, and an
  # unserializable generated module each failing E6005 with nothing
  # staged); and the trace session's load-free emission with the runtime
  # bound.
  'fg|=== Running FFI Load Emission Tests (ISSUE-0662) ===|java -ea -cp build deal.test.FfiLoadEmissionTest'

  # ISSUE-0663 registration: the typed FFI crossings and the class-value
  # carrier projection (luajit-ffi-load-emission-and-typed-crossings F3/F4,
  # luajit-ffi-shared-emission-and-jvm-rejection F3, the FFI typed call and
  # value-read contract, and the carrier projection contract; sequencing
  # step 2): the scalar fixtures ffi/012, ffi/013, ffi/014, ffi/048,
  # ffi/049, ffi/050 and the pointer fixture ffi/020 compile through the
  # production arm with the corpus's production FFI metadata
  # (CorpusFfi.module(...).generatedModule() and the bootstrapped loader
  # text) and execute under luajit with the sidecar-pinned runtime-ok
  # transcripts (the drives resolve the real loaded surface and fail on a
  # broken library wiring); the emitted crossing positions (the
  # DEAL_TO_HOST + HOST_PARAMETER cells in one-based order, the loaded
  # wrapper's .f invocation with the trailing literal span triplet, the
  # single HOST_TO_DEAL + HOST_SYNC_RETURN cell at the call origin, no new
  # boundary kind, and no conversion code in the artifact — the ABI
  # conversions stay owned by deal/runtime.lua); the call-site failures
  # ffi/022-ffi/024 pinned to FFI_NULL_STRING/FFI_INVALID_UTF8/
  # FFI_NULL_POINTER at the call expression with the sidecar's message,
  # span, and framed terminal code; the class-value carrier projection (the
  # class parameter cell accepting the chunk shape and failing every other
  # value with the pinned E8010 texts, never E8001; the post-cell
  # chunk-to-wrapper projection allocating a fresh wrapper-facing value per
  # crossing while the program's own value stays untouched; the
  # wrapper-to-chunk projection before the crossing's events, one heap
  # value per class-typed crossing in the trace stream); and the closed
  # boundary-kind set with no null mapping inside the bridge.
  'fg|=== Running FFI Typed Crossing Tests (ISSUE-0663) ===|java -ea -cp build deal.test.FfiTypedCrossingTest'

  # ISSUE-0664 registration: the ffi/051-ffi-invalid-string fixture and
  # the six-code completion (luajit-ffi-load-emission-and-typed-crossings
  # Verification 3; the FFI typed call and value-read contract; sequencing
  # step 3): the new fixture obtains a U+0000-bearing string through
  # json.parse("{\"s\":\"\\u0000\"}") and pins runtime-error
  # FFI_INVALID_STRING at the call expression; its sidecar carries the
  # LuaJIT runtime-error expectation (code, the embedded-NUL message, and
  # the call-expression origin) plus the jvm/js compile-reject E6006
  # entries and validates clean in the sanctioned divergent C6 form; the
  # production-artifact drive under luajit asserts the emitted load_ffi
  # prelude (T1) and the string parameter's DEAL_TO_HOST + HOST_PARAMETER
  # crossing with the loaded wrapper's .f invocation (T2), and compares
  # the captured code/message/sourceFile/line/column with the sidecar and
  # the DEAL_ERROR_CODE line through the canonical G4.6 framing; the
  # scenario's dependency on the load (a missing library fails it with
  # FFI_LIBRARY_LOAD, never FFI_INVALID_STRING) and on the string crossing
  # (a NUL-free payload executes the native echo clean) is proven; and the
  # corpus's LuaJIT FFI sidecars cover exactly the closed six FFI_* codes
  # with their pinned import-statement/call-expression origins.
  'fg|=== Running FFI Invalid String / Six-Code Completion Tests (ISSUE-0664) ===|java -ea -cp build deal.test.FfiSixCodeCompletionTest'

  # ISSUE-0665 registration: the extern-C value-position read drive
  # (luajit-ffi-load-emission-and-typed-crossings F5 and the FFI typed
  # call and value-read contract; luajit-ffi-shared-emission-and-jvm-
  # rejection F1/F3/F5; semantic-ir-construct-coverage-cutover K2;
  # sequencing step 4): the lowered read carries exactly one EXPORT_READ
  # per source occurrence with exactly one
  # HostFunction(candidate.native, export, descriptor) registration keyed
  # by the read result's allocation identity, no CallCallee.Dynamic and no
  # HostFunctionValue, and the static CALL(INDIRECT) consumes exactly that
  # registration with the direct CALL(HOST)'s cells; the corpus scalar
  # exports (ffi_add/ffi_half/ffi_not/ffi_echo/ffi_identity_int/ffi_noop)
  # execute through the production artifact under luajit with the pinned
  # runtime-ok transcript and through the oracle with the same calls and
  # outcomes, the read publishing the loaded surface entry the emitted
  # load_ffi prelude (T1) installs and the invocation resolving that same
  # entry (a spy observes exactly the one call; a torn load fails loudly);
  # a failing export (ffi_null_string, ffi_invalid_utf8) keeps the corpus
  # 022/023 pinned code and message at its call-expression origin in value
  # position and in the direct-call companion; and an async extern-C
  # declaration stays a compile-time E7002 rejection.
  'fg|=== Running FFI Value-Position Read Invocation Tests (ISSUE-0665) ===|java -ea -cp build deal.test.FfiValueReadInvocationTest'
  # ISSUE-0666 registration: the C-struct construction site and the
  # seed-layout validator admission (luajit-ffi-struct-plan-construction-
  # and-oracle-projection F1/F2/F3; luajit-ffi-shared-emission-and-jvm-
  # rejection F6; semantic-ir-construct-coverage-cutover K9 item 3;
  # sequencing step 5): ffi/019-ffi-struct-copy-isolation constructs
  # native.Pair through the loaded Pair_plan entry, compiles through the
  # production arm with the corpus's production FFI metadata, and executes
  # under luajit with the sidecar-pinned transcript (the artifact carries
  # the __rt.class_plan_ call over the export-surface registry's plan entry
  # with the literal's span triplet, the CLASS_LITERAL_FIELD boundary
  # children in declaration order, the wrapper-to-chunk projection, and no
  # CLASS_DEFAULT child, no in-project factory, and no ABI conversion
  # text); the lowered and emitted FFI_PLAN shape over the seed layout
  # (null factory ref, empty default-op list, the provided-field
  # boundaries, and zero RETAINED_ABI_DEFERRED); the evaluator-once drive
  # (a focused declaration whose struct fields carry native-counting
  # defaults: zero evaluator invocations at load, exactly one evaluator per
  # omitted field per attempt in class source order, and provided-field
  # suppression) through the production artifact; the extra-key E8007 drive
  # (a doctored CLASS_NEW(FFI_PLAN) payload with two extra provided names
  # fails with exactly one E8007 naming the first provided-source extra at
  # the literal origin, before any default, with the guard preceding the
  # runtime entry call and the native counter proving that no evaluator ran
  # for the failed attempts); the validator deviation battery (the
  # seed-layout input admits exactly the realized shape and rejects the
  # unresolvable-layout pre-change outcome, a non-seed layout, a non-null
  # factory ref, a non-empty default-op list, a CLASS_DEFAULT_FIELD
  # boundary, a missing provided-field boundary, a wrong boundary order,
  # and the HOST_DEFAULTS owner over an extern-C class with
  # CONSTRUCTION_COHERENCE); and the JVM arm's fail-closed FFI_PLAN
  # disposition (the production project entry rejects the extern-C closure
  # and the direct unit assertion keeps the owner defect).
  'fg|=== Running FFI Struct Construction Tests (ISSUE-0666) ===|java -ea -cp build deal.test.FfiStructConstructionTest'
  # ISSUE-0681 registration: the materialization-site origin and the
  # function-row projection on the shared route (function-typed-value-
  # materialization-and-dispatch M8 items 1-5, the materialization
  # contract's visible errors, and the task's origin drives;
  # semantic-ir-construct-coverage-cutover K11): the annotated-declaration
  # VARIABLE_DECLARATION boundary of the direct and the adapted arm
  # carries the declared type annotation's own span as its origin (never
  # the declaration's let span) with the descriptor-kind policy; the
  # function-typed declaration crossing with a non-function value fails
  # the pinned function row (E8001, expected function, actual the shared
  # actual-kind classification) at the annotation span in the oracle and
  # on both production artifacts with exactly one boundary FAILURE
  # terminal per consumer and the three-consumer differential verdict
  # passing; a non-function-typed declared crossing over a deferred
  # composite read fails the descriptor-kind row at the annotation span
  # while the contextual read child keeps its own span and passes; a
  # differing carried signature keeps the pinned E8010 with the two
  # canonical signature texts on the materialization site; and a
  # doctored free boundary outside the declaration arms carries its own
  # origin and its single FAILURE terminal in all three consumers (the
  # origin is compared). The function-typed drives register the
  # materialized value's allocation identity with the runtime carrier's
  # own binding at the unit level — the pending DynamicFunctionValue
  # producer rule of ISSUE-0622; the end-to-end fixture drive belongs to
  # the joint fixture battery. The class lives in package deal.semantic
  # to reach the package-internal project walk.
  'fg|=== Running Materialization-Site Origin / Function-Row Projection Tests (ISSUE-0681) ===|java -ea -cp build deal.semantic.MaterializationSiteOriginTest'
  # ISSUE-0667 registration: the oracle plan-projection seam and the FFI
  # construction execution (luajit-ffi-struct-plan-construction-and-oracle-
  # projection F4 and the oracle plan-projection contract;
  # luajit-ffi-shared-emission-and-jvm-rejection F6;
  # luajit-ffi-class-plan-consumption-verification D4; sequencing step 6):
  # HostResponder gains exactly one closed plan-projection terminal
  # (module + class name + class descriptor -> the ordered plan entries
  # with their deferred-default suppliers) and the new
  # ClassOpsExecutor.executeClassNewFfiPlan surface accepts only FFI_PLAN
  # and runs the runtime entry's four phases — the provided fields'
  # CLASS_LITERAL_FIELD boundary children in declaration order, the
  # provided-source-order E8007 guard, each omitted required-present
  # field's supplier exactly once per attempt in class source order, the
  # per-field descriptor validation (the canonical matcher's E8001/E8004
  # at the literal origin), and the declaration-order ClassValue with
  # every declared field present, never a partial instance and never a
  # memoized supplier. The ffi/019 provided-only drive runs the oracle's
  # plan projection with the resolved declaring module, the class name,
  # and the class descriptor, asserts the construction's event order and
  # the fixture's copy isolation, and runs the same fixture's production
  # artifact (the T5 construction site) under luajit with the pinned
  # runtime-ok transcript; the omitted-field drive runs the focused
  # native-counting declaration through the seam with one supplier per
  # omitted field per attempt (the artifact's counter sequence 0, 2, 3, 5)
  # beside the same project's production artifact executing under luajit;
  # the negative seeds reject a mutated entry order, a mutated descriptor,
  # a short projection, and an absent projection (and the phase-3
  # E8001/E8004 projections pin the literal origin); a failing deferred
  # default's proxy failure crosses as its own DEAL failure with the later
  # field's supplier suppressed; a doctored
  # extra-field payload yields the identical E8007 through the oracle and
  # the emitted artifact; the surface rejects every foreign owner, a
  # non-null factory ref, a non-empty default-op list, and an absent
  # projection; and the negative drives compile the focused fixture
  # without building its native library at all (the oracle loads no
  # library, resolves no symbol, and runs no generated evaluator content).
  'fg|=== Running FFI Plan Projection Oracle Tests (ISSUE-0667) ===|java -ea -cp build deal.test.FfiPlanProjectionOracleTest'

  # ISSUE-0670 registration: the consolidated FFI production-corpus
  # integration drive (luajit-ffi-load-emission-and-typed-crossings
  # Verification 1-4 and 7-8; luajit-ffi-struct-plan-construction-and-
  # oracle-projection Verification 1; luajit-ffi-shared-emission-and-jvm-
  # rejection Verification 1-4 and 7; the epic criteria): one drive
  # compiles every LuaJIT-executing FFI fixture (012, 013, 014, 019, 020,
  # 022-027, 048, 049, 050, 051) through the production pipeline with the
  # corpus's production FFI metadata (CorpusFfi.module(...).generatedModule()
  # and the bootstrapped loader text) and executes each published artifact
  # under luajit — the runtime-ok fixtures compare exit code and both
  # transcript streams with their sidecars, the runtime-error fixtures
  # compare the artifact's exit code, the production terminal's
  # DEAL_ERROR_CODE line (the call-expression legs), the captured
  # code/message/sourceFile/line/column, and the reconstructed canonical
  # DEAL_ERROR_CODE/DEAL_ERROR_SNAPSHOT transcript byte-for-byte with their
  # sidecars; the load_ffi prelude (the metadata module key, the generated
  # bindings literal, the import statement's span triplet, no dotted
  # provider require) is asserted in every artifact; the six FFI_* codes
  # keep their pinned origins (FFI_SYMBOL_MISSING and FFI_LIBRARY_LOAD at
  # the import statement; FFI_NULL_STRING, FFI_INVALID_UTF8,
  # FFI_NULL_POINTER, FFI_INVALID_STRING at the call expression); ffi/016
  # stays unclaimed (the bytes child ISSUE-0626) and ffi/047 keeps its
  # E7002 declaration negative; the corpus inventory is the pinned closed
  # list (no fixture or sidecar deleted or reshaped, ffi/051 the only
  # addition); and no library, no symbol, and no evaluator is touched at
  # compile (the never-built library and the absent symbol both emit, the
  # plan literal carries only the deferred evaluator closures, and the
  # generator's literals are byte-deterministic) with no
  # ffi.C/cdef/dlopen/dlsym text in any artifact.
  'fg|=== Running FFI Production-Corpus Integration Tests (ISSUE-0670) ===|java -ea -cp build deal.test.FfiProductionCorpusTest'

  # ISSUE-0668 registration: the trace-mode FFI session and the both-mode
  # runtime binding (luajit-ffi-load-emission-and-typed-crossings F6;
  # luajit-ffi-shared-emission-and-jvm-rejection F2;
  # luajit-ffi-struct-plan-construction-and-oracle-projection F4;
  # sequencing step 7): a project session over an extern-C closure binds
  # __rt and the host-boundary prelude in both modes and both trace
  # entries (with and without the compile's declaration surface, exactly
  # once), while a host-free chunk keeps its self-contained prelude and
  # the trace entries keep their signatures with a no-op extern-C
  # MODULE_IMPORT (its op events run; no load_ffi/load_host is emitted);
  # the three-input trace entry over ffi/020 and the four-input entry
  # over ffi/019 pre-publish the scenario surface (one function wrapper
  # per declared function plus the real generated <C>_plan entry from the
  # plan literal) and run the crossings and the construction under
  # luajit, comparing the decoded stream with the oracle event-for-event
  # and asserting one heap value per class-typed crossing, the
  # pre-published surface surviving the chunk's or-guards, and the seam's
  # own wrappers serving the calls; the focused counting fixture shows
  # the trace construction running the real generated plan evaluators
  # (zero at load, once per omitted field per attempt in class source
  # order) with the oracle's projection suppliers matching; an absent
  # surface or entry stays the fail-visible missing projection on the
  # value-position read (the oracle publishes the same missing atom) and
  # the invocation fails visibly while the published entry succeeds; the
  # generated literals and both mode emissions are byte-deterministic.
  'fg|=== Running FFI Trace Session Tests (ISSUE-0668) ===|java -ea -cp build deal.test.FfiTraceSessionTest'
)
