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
  # closure guard (a HOST-kind MODULE_IMPORT and a cross-module async
  # call), the one production emission per target, the one staged project
  # artifact plus the unchanged LuaJIT runtime/stdlib deployment copies,
  # and the fail-closed E6005 mapping
  # (production-project-emission-and-atomic-cutover P5/P6/P7/P9/P11 and
  # the production-arm, source-map, and fail-closed producer-guard
  # contracts; luajit-jvm-single-lowering-production-cutover
  # C3/C4/C5/C7/C8/C9): the one public static entry and its input set,
  # the pinned warning texts and guard tokens, the two-module fixture's
  # one staged artifact per target (`app.lua`/`App.java`) with no sidecar
  # and the byte-identical repeated staging, the real luajit execution
  # (the one-main probe) and the javac --release 25 -proc:none + java
  # run, the atomic-failure cases (a bytes-bearing lowering and a
  # cross-module sync-call emission each stage nothing), the HOST-import
  # and cross-module-async fail-closed outcomes, the same-module async
  # acceptance, and the source-map warning disposition. The fixture
  # inputs are gathered through a harness-invocation compile (P10 item 3)
  # and the unit is driven with the release-owned production invocation.
  'fg|=== Running Production Project Emission Tests (ISSUE-0642) ===|java -ea -cp build deal.test.ProductionProjectEmissionTest'
)
