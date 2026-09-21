package deal.semantic;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.BinaryOp;
import deal.ast.Block;
import deal.ast.BreakStatement;
import deal.ast.CallExpr;
import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.ContinueStatement;
import deal.ast.DeleteStatement;
import deal.ast.Either;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionNode;
import deal.ast.ExpressionStatement;
import deal.ast.ForInit;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.FunctionExpr;
import deal.ast.HasExpr;
import deal.ast.IdentifierExpr;
import deal.ast.IfStatement;
import deal.ast.ImportDeclaration;
import deal.ast.IndexExpr;
import deal.ast.LiteralExpr;
import deal.ast.LiteralValue;
import deal.ast.MemberAccessExpr;
import deal.ast.ReturnStatement;
import deal.ast.ObjectLiteralExpr;
import deal.ast.Parameter;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.UnaryOp;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.NamespaceRegistrations;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.AddressChainProtocol;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.UnarySelector;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The common lowerer's per-construct shape map inside {@code
 * deal.semantic}: the container/string construct stage (ISSUE-0232
 * D1/D7; ISSUE-0386) producing the six container/string operations, plus
 * the value-operation slice (signed-int32 foundation I3; ISSUE-0395)
 * producing {@code CONST}/{@code UNARY}/{@code BINARY}/
 * {@code INTRINSIC_CALL} with the fixed selector→policy stamping.
 *
 * <p><b>The I3 value-operation slice (pinned).</b> Over checked facts,
 * the slice produces exactly the closed value operations — each with the
 * policy stamped from the single closed selector→policy tables of
 * {@link SemanticIrValidator} ({@code unaryPolicy}/{@code binaryPolicy}/
 * {@code intrinsicPolicy} — never a copy), a complete
 * {@code OperationContractSnapshot} with the T3 digest, and the
 * producing {@code SourceOrigin}:</p>
 *
 * <ul>
 *   <li>scalar {@link LiteralExpr} → one {@code CONST} (all five scalar
 *       kinds; an {@code IntLiteral} is signed32 by the I1 parser
 *       invariant);</li>
 *   <li>{@link UnaryExpr} → one {@code UNARY} with {@code BOOL_NOT} /
 *       {@code INT32_NEG} / {@code NUMBER_NEG} selected by the operator
 *       plus the operand's checked type (the checker's unary rules);
 *       policy {@code INT32_RESULT} for {@code INT32_NEG},
 *       {@code NO_DEAL_FAILURE} otherwise;</li>
 *   <li>{@link BinaryExpr} → one {@code BINARY} with the int32/number
 *       selector families selected by the operator plus the operand
 *       checked types ({@code INT32_ADD/SUB/MUL} →
 *       {@code INT32_RESULT}; {@code INT32_DIV_TRUNC/MOD_TRUNC} →
 *       {@code INT32_DIVISOR_THEN_RESULT}; {@code INT32_POW} →
 *       {@code INT32_EXPONENT_THEN_RESULT}; every {@code NUMBER_*}
 *       arithmetic incl. {@code NUMBER_POW_IEEE} →
 *       {@code NO_DEAL_FAILURE}). The other closed selector families
 *       ({@code STRING_*}, {@code BOOLEAN_*}, {@code NULL_*},
 *       {@code NULLABLE_*}, {@code REFERENCE_*} — the comparison
 *       producer {@link ComparisonSelectorLowering} — and the logical
 *       {@code BRANCH} operators) remain defined-but-not-produced by
 *       this slice; string {@code +} lowers to {@code STRING_CONCAT},
 *       never {@code BINARY};</li>
 *   <li>{@code int(…)}/{@code number(…)} intrinsic calls
 *       ({@code Symbol.IntrinsicSymbol}) → one {@code INTRINSIC_CALL}
 *       with {@code INT_CONVERT}/{@code NUMBER_CONVERT}, zero
 *       {@code BOUNDARY} children, and the conversion policy
 *       ({@code INT_CONVERSION}/{@code NUMBER_CONVERSION}) as the
 *       terminal check.</li>
 * </ul>
 *
 * <p><b>The E5 address-chain arms (pinned).</b> Over checked facts, the
 * arms lower every checked {@link AssignmentExpr}/{@link DeleteStatement}
 * target shape through the closed A-D9 map into one {@code ASSIGN}/
 * {@code DELETE} op with the pinned child order and trace roles (A-D2:
 * receiver → key → RHS → normalize → boundary → commit; VARIABLE: value
 * → boundary → commit; DELETE omits the RHS), the closed boundary
 * production (A-D4), the single-last commit structure (A-D5), the
 * committed-value result (A-D6), and single evaluation (A-D8):
 * {@code IdentifierExpr} targets → {@code ASSIGN VARIABLE}
 * {@code [valueOp, boundaryOp(VARIABLE_ASSIGNMENT),
 * commitOp(BINDING_STORE)]} with the declared target descriptor and the
 * descriptor-kind policy (the {@code FUNCTION_ADAPT} adapter slot stays
 * E6's — this epic produces no adapter children); {@code MemberAccessExpr}
 * on table → {@code TABLE_SLOT [containerOp, valueOp, MEMBER_WRITE]};
 * {@code IndexExpr} on table → {@code TABLE_SLOT [containerOp, keyOp,
 * valueOp, INDEX_NORMALIZE(TABLE_WRITE), INDEX_WRITE]} (the key is
 * statically {@code string} by the checker's E3018 gate);
 * {@code IndexExpr} on array → {@code ARRAY_SLOT [containerOp, keyOp,
 * valueOp, ARRAY_LENGTH, INDEX_NORMALIZE(ARRAY_WRITE),
 * ARRAY_ELEMENT_ASSIGNMENT, INDEX_WRITE]} (the length read pins at
 * normalize time; the append idiom lowers through this standard chain);
 * {@code MemberAccessExpr} on class → {@code CLASS_FIELD [containerOp,
 * valueOp, FIELD_WRITE]}; the four {@code DELETE} rows of A-D9 with the
 * {@code ARRAY_ELEMENT_DELETE + ARRAY_DELETE_BOUNDS} bounds boundary on
 * the array row. {@code ASSIGN} publishes the committed value with
 * {@code resultType} = the target position's checked descriptor;
 * {@code DELETE} publishes none. Every chain child records the chain op
 * as its {@code parentOpId}, nested chains record the enclosing chain
 * op, and the unit-production seam runs {@link AddressChainProtocol}
 * over the produced unit (A-D1).</p>
 *
 * <p><b>I3 profile guard.</b> {@link #lowerModule} refuses any lowering
 * request whose invocation profile is not
 * {@code DEAL_V1_2_INT32} with E6005 {@link #LOWER_LEGACY_PROFILE_REJECTED}
 * before any op is built — {@code LEGACY_SAFE_INT} is inspectable for
 * routing/regression but never lowered; the validator's R-PROFILE is the
 * backstop and {@link LoweredModuleUnit} admits only
 * {@code DEAL_V1_2_INT32} by construction.</p>
 *
 * <p><b>I3 scalar descriptor rows.</b> The value arms admit exactly
 * the pinned one-line scalar descriptor rows (int, number, boolean,
 * null, string, and the nullable rows over int/number/boolean — see
 * {@code ModuleLowerer#valueDescriptorOf}), realized through the single
 * {@code DescriptorService} producer (the verbatim D2 scalar table); no
 * structural descriptor service is built in this slice. The slice
 * performs no evaluation: {@code CONST} carries parser-guaranteed
 * scalars, {@code INTRINSIC_CALL} is a terminal check, and the
 * selector→policy stamping reads the closed table data.</p>
 *
 * <p><b>The D1 shape map (pinned).</b> Every arm below produces exactly
 * the design's closed shape — op kind, payload fields, failure policy,
 * result/operand types, child order, {@code parentOpId}, and origin span.
 * Payload-referenced values are prior ordered steps in source order and
 * these ops carry empty operand lists (schema-pinned); every source
 * subexpression appears exactly once as a producing op; no consumer may
 * infer an omitted source step:</p>
 *
 * <ul>
 *   <li>scalar {@link LiteralExpr} → one {@code CONST
 *       {value: ScalarValue}}, result type {@code D(checked type)},
 *       policy {@code NO_DEAL_FAILURE}, origin = the literal span
 *       (template literal parts reuse this exact arm). An
 *       {@code IntLiteral} whose value is outside signed32
 *       [-2147483648, 2147483647] raises {@link IntLiteralOutOfRange}
 *       — converted at the unit-production seam to E6005
 *       {@code INT32_LITERAL_OUT_OF_RANGE} (capability
 *       {@code SIGNED_INT32}), never a truncated scalar (the E1036
 *       signed32 literal gate is ISSUE-0111's frontend item, not yet
 *       satisfied by the checker);</li>
 *   <li>{@link IdentifierExpr} in an operand position → one
 *       {@code BINDING_LOAD {binding, generation}} per the loop-binding
 *       load-resolution rule: a load of an enclosing for-of loop binding
 *       carries that {@code FOR_EACH} payload's initial generation
 *       ({@link #INITIAL_LOOP_GENERATION}); the payload is never
 *       rewritten per iteration and the body-runner substitutes
 *       initial + iteration index at execution. Every other identifier
 *       is a foreign construct in this stage's window — an unresolvable
 *       identifier is a producer defect (E6005), never an invented op;
 *       binding allocation, non-loop loads, and generation
 *       increments/stores are E6's;</li>
 *   <li>{@link ArrayLiteralExpr} with checked {@code Type.Array(T)} → one
 *       {@code ARRAY_NEW {elementDescriptor: D(T), values: element
 *       ValueIds in source order, elementBoundaryOpIds: child op ids in
 *       the same order}} plus one {@code BOUNDARY} child per element in
 *       the same source order — kind {@code ARRAY_LITERAL_ELEMENT},
 *       descriptor {@code D(T)}, policy
 *       {@code ARRAY_ELEMENT_DESCRIPTOR}, input = the element
 *       {@code ValueId}, realization
 *       {@code RuntimeValidation("runtime-validation")}
 *       ({@link #CANONICAL_RUNTIME_VALIDATION_ID}), {@code parentOpId} =
 *       the {@code ARRAY_NEW} op id, origin = the element expression
 *       span. An empty literal produces zero values and zero children;</li>
 *   <li>{@link ObjectLiteralExpr} with checked {@code Type.Table} → one
 *       {@code TABLE_NEW {entries: [(key, value ValueId) in source
 *       order]}}; keys are the identifier property names; duplicate keys
 *       stay in source order in the payload — the executor's
 *       {@code SemanticTable.put} pins the later value and the first
 *       position;</li>
 *   <li>{@link MemberAccessExpr} {@code .length} on an array-typed
 *       object → one {@code ARRAY_LENGTH {arrayValue}}, result type
 *       {@code int}, policy {@code INT32_RESULT}; the receiver is one
 *       prior step and is never re-evaluated;</li>
 *   <li>{@link MemberAccessExpr} on a table-typed object in a checked
 *       read context → one {@code MEMBER_READ {table, key}} (result type
 *       {@code D(contextual type)}, policy {@code NO_DEAL_FAILURE}, the
 *       receiver {@code ValueId} exactly once, the key the constant
 *       identifier string, never evaluated) plus exactly one
 *       {@code BOUNDARY} child — kind {@code CONTEXTUAL_TABLE_READ},
 *       descriptor {@code D(contextual type)}, policy by the
 *       descriptor-kind rule ({@code TYPE_DESCRIPTOR} for non-function
 *       descriptors, {@code FUNCTION_SIGNATURE} for function
 *       descriptors), input = the {@code MEMBER_READ} result
 *       {@code ValueId}, realization
 *       {@code RuntimeValidation("runtime-validation")},
 *       {@code parentOpId} = the {@code MEMBER_READ} op id, origin = the
 *       member-access span;</li>
 *   <li>{@link BinaryExpr} with {@code BinaryOp.ADD} and checked
 *       {@code Type.String} → one {@code STRING_CONCAT {fragments: [left
 *       ValueId, right ValueId] in source order}} — string {@code +}
 *       never lowers to {@code BINARY};</li>
 *   <li>{@link TemplateLiteralExpr} → per part in source order: each
 *       literal part (even index) is one {@code CONST
 *       {value: ScalarValue.String(part text)}} step and each
 *       interpolation (odd index, string-typed per E3016) is the
 *       interpolation expression's producing op chain; then one
 *       {@code STRING_CONCAT {fragments: [part ValueIds in source
 *       order]}}. A template with no interpolations still produces
 *       {@code STRING_CONCAT} with one fragment — no folding;</li>
 *   <li>{@link ForOfStatement} with a {@code string}-typed iterable →
 *       one {@code FOR_EACH {mode: STRING_SCALARS, iterable, binding,
 *       generation, body}}, result none, policy
 *       {@code TYPE_DESCRIPTOR}, origin = the for-of span; the iterable
 *       expression is one prior step. The body block is lowered
 *       recursively under the loop-binding frame;</li>
 *   <li>{@link ForOfStatement} with an array-typed iterable
 *       ({@code [T]}) → one {@code FOR_EACH {mode: ARRAY_VALUES,
 *       iterable, binding, generation, body}} (control-flow-structures
 *       C-D5: the iterable completes exactly once before START; the op
 *       snapshots the array reference and the initial length and visits
 *       slot indices {@code 0..initialLength-1} in increasing order with
 *       the op's own {@code TYPE_DESCRIPTOR} terminal check against the
 *       element descriptor derived from the recorded array operand type,
 *       {@code [T]} → element {@code T}; a fresh binding per iteration,
 *       mechanics E6). The element type is derived fail-closed through
 *       the {@code ContainerPayloadDescriptors} bridge; a bytes-bearing
 *       element (representable since the ISSUE-0158 schema lift, but
 *       without shared bytes value semantics) is the container pipeline's
 *       {@code CONSTRUCT_UNLOWERED} producer guard, never an invented
 *       descriptor.</li>
 * </ul>
 *
 * <p><b>The E5 control-flow arms (pinned; ISSUE-0409).</b> Over checked
 * facts, the arms lower every checked control-flow construct into the
 * pinned structured ops of control-flow-structures C-D3..C-D8 with the
 * per-op execution contracts recorded for consumers, and produce the
 * {@link StructuredBodyTable} block-membership record for the unit
 * (C-D1):</p>
 *
 * <ul>
 *   <li>{@link IfStatement} → {@code BRANCH(IF) {selector: IF,
 *       condition, selectedBlock, alternateBlock}}: the condition's
 *       producing ops complete in the enclosing block before the
 *       {@code BRANCH} op; exactly one of {@code selectedBlock}/
 *       {@code alternateBlock} executes; the {@code else} branch is
 *       {@code alternateBlock} (an {@code else if} chain nests its
 *       {@code BRANCH} op inside the alternate block); an absent
 *       {@code else} produces {@code alternateBlock = null}; SUCCESS
 *       publishes no result;</li>
 *   <li>{@link BinaryExpr} with {@code &&}/{@code ||} → {@code
 *       BRANCH(LOGICAL_AND/LOGICAL_OR)} (never {@code BINARY}): the
 *       left operand completes before START as the condition; the right
 *       operand's producing ops live in {@code selectedBlock} and
 *       execute only when the left value does not decide the result
 *       (AND: left false → result false, block skipped; OR: left true →
 *       result true, block skipped). The op's result {@code ValueId} is
 *       the right operand's value identity (result type {@code
 *       D(boolean)} — a boolean either way, checker-pinned boolean
 *       operands). Chained {@code &&}/{@code ||} lower to nested
 *       {@code BRANCH}es in source order;</li>
 *   <li>{@link WhileStatement} → {@code LOOP(WHILE) {selector: WHILE,
 *       initBlock = the per-iteration condition block, condition,
 *       bodyBlock, updateBlock = null}}: repeat { execute
 *       {@code initBlock}; evaluate the condition value; if false →
 *       SUCCESS; execute {@code bodyBlock} }; the condition ops are
 *       explicit members of {@code initBlock} (C-D1), never an inferred
 *       subgraph; no speculative body execution;</li>
 *   <li>{@link ForStatement} → {@code LOOP(FOR) {selector: FOR,
 *       initBlock = one-time init including the first condition
 *       production, condition, bodyBlock, updateBlock = [update ops,
 *       condition-producing ops]}}: execute {@code initBlock} once;
 *       repeat { evaluate the condition value; if false → SUCCESS;
 *       execute {@code bodyBlock}; execute {@code updateBlock} }. The
 *       condition {@code ValueId} is produced once in {@code initBlock}
 *       and re-produced by the {@code updateBlock} production (the most
 *       recently produced value of the condition {@code ValueId} wins —
 *       one value identity, re-produced per iteration). A test-less
 *       {@code for (;;)} produces exactly one {@code CONST} op with the
 *       boolean value {@code true} in {@code initBlock} as the
 *       condition production, and {@code updateBlock} carries only the
 *       update ops (no condition production). A {@code let}-declared
 *       for-initializer is E6's {@code BINDING_ALLOC} — fail closed;</li>
 *   <li>{@link TryStatement} → {@code TRY_CATCH {tryBlock,
 *       catchBinding, catchBlock}} (C-D6: execute {@code tryBlock};
 *       success → SUCCESS, catch skipped; a DEAL failure raised inside
 *       {@code tryBlock} is reified as an {@code Error} value bound to
 *       {@code catchBinding} — binding init mechanics E6 — and
 *       {@code catchBlock} executes; a failure raised from
 *       {@code catchBlock} becomes the {@code TRY_CATCH} FAILURE with
 *       its own code/message/origin preserved and {@code cause} = the
 *       original caught failure snapshot). The catch binding identity
 *       is allocated by this stage and a load of the catch variable
 *       inside {@code catchBlock} lowers to {@code BINDING_LOAD}
 *       carrying that binding with the pinned initial generation;</li>
 *   <li>{@link ThrowStatement} → {@code THROW {errorValue}}: the operand
 *       completes before START; the op never succeeds; policy
 *       {@code THROW_TRANSFER} — code/message from the supplied
 *       {@code Error} value's fields, origin = the THROW origin, frames
 *       active; control transfers to the nearest enclosing
 *       {@code TRY_CATCH}, else the error escapes as the host-visible
 *       {@code DEALRuntimeError};</li>
 *   <li>{@link BreakStatement}/{@link ContinueStatement} →
 *       {@code BREAK}/{@code CONTINUE {loopId = the innermost enclosing
 *       loop op ({@code LOOP} or {@code FOR_EACH}) recorded by the
 *       lowerer}} (C-D7: BREAK exits the target loop; CONTINUE — FOR:
 *       execute {@code updateBlock} then re-test; WHILE: execute the
 *       condition block ({@code initBlock}) then re-test; FOR_EACH:
 *       next slot index; transfer across an enclosing {@code TRY_CATCH}
 *       boundary is legal). The checker's E2000 pins source-level loop
 *       placement, so a missing target is a producer defect;</li>
 *   <li>{@link ExpressionStatement} → {@code DISCARD {value}}: the
 *       value's producing ops already completed before the op; START →
 *       SUCCESS with no result; origin kind {@code SYNTHETIC} (C-D8 —
 *       the intentional discard is audited in the op stream and traces,
 *       never inferred away).</li>
 * </ul>
 *
 * <p><b>Block membership (C-D1).</b> Every op the session produces is a
 * member of exactly one block (the block stack of the session); the
 * module-init block is the root block of the unit's module-level
 * statements; every payload-referenced {@code BlockId} exists in the
 * produced {@link StructuredBodyTable} (empty child blocks included);
 * block ops record the enclosing structure op as {@code parentOpId}.
 * The unit-production seam validates the produced unit plus table
 * through {@link ControlFlowValidator} (C-D2 — block tree, dominance,
 * exits; violations are E6005 {@code CONTROL_BLOCK_TREE}/
 * {@code CONTROL_EXIT}). A source statement following a terminator
 * ({@code THROW}/{@code BREAK}/{@code CONTINUE}) in the same block is
 * unreachable and fails closed ({@code CONSTRUCT_UNLOWERED}) — the
 * validated block model never admits an op after a terminator in its
 * block. The condition of a {@code LOOP(FOR)} is re-produced in
 * {@code updateBlock} publishing the same condition {@code ValueId}
 * (the slot-threaded expression lowering below).</p>
 *
 * <p><b>Value-operation arms.</b> The I3 slice adds the value-operation
 * arms to the shape map ({@code CONST} of every scalar kind,
 * {@code UNARY}, {@code BINARY} of the int32/number arithmetic
 * selectors, and {@code INTRINSIC_CALL} of the two conversion
 * intrinsics); see the class-level I3 section. Operands complete
 * left-to-right and appear as the produced op's {@code operands}/
 * {@code operandTypes} in source order — the slice never evaluates,
 * re-emits, or re-reads an operand.</p>
 *
 * <p><b>Fail-closed arms (exactly one outcome each).</b> A construct
 * reaching an arm without a lowering arm raises {@link ConstructUnlowered}
 * — class-typed object literals ({@code CLASS_NEW} is E9's), class
 * member access ({@code FIELD_READ} is E9's), module member access
 * ({@code EXPORT_READ} is E10's), {@code .length} on bytes
 * (ISSUE-0158), comparison binary operators (the comparison producer
 * {@link ComparisonSelectorLowering}'s), ordinary calls ({@code CALL}
 * is E7's), and every other foreign construct. An {@code IntLiteral}
 * outside signed32 at the
 * {@code CONST} arm raises {@link IntLiteralOutOfRange} — the same
 * fail-closed discipline for a scalar outside the closed scalar set
 * (the {@code CONST} contract's "a literal outside the closed scalar
 * set is a producer defect (E6005), never an invented op"), converted
 * at the same seam to E6005 {@code INT32_LITERAL_OUT_OF_RANGE} with
 * capability {@code SIGNED_INT32} — never a truncation. The unit-production
 * seam converts a {@code ConstructUnlowered} defect to the pinned E6005
 * {@code CONSTRUCT_UNLOWERED} diagnostic through
 * {@link FailureContractRegistry} with the exact
 * {@link LoweringFailureDetail} — a hard compile failure in this stage's
 * window, never a reroute; LEGACY routing for modules containing
 * unlowerable constructs is the plan-time capability-gating consequence,
 * never caused by this E6005. Descriptor positions use
 * {@link ContainerPayloadDescriptors}; a {@code Type.Error} derivation
 * converts at the same seam to E6005
 * {@code DESCRIPTOR_UNREPRESENTABLE} — never an invented descriptor,
 * never a crash — and a bytes-bearing container element position stays
 * the container pipeline's fail-closed exclusion (ISSUE-0158 bytes value
 * semantics are backend-owned).</p>
 *
 * <p><b>The binding-core child (ISSUE-0444).</b> {@link
 * #lowerModuleBindingCore} drives the same session in binding-core mode:
 * one {@code BindingId} per declared name, static per-incarnation
 * generation ordinals, {@code BINDING_ALLOC/INIT/LOAD/STORE} with the
 * closed {@code DIRECT|SHARED_CELL} defaults and special cases
 * (for-let per-iteration incarnations and {@code FOR_EACH} iteration
 * bindings are {@code SHARED_CELL}), module-init-top intrinsic bindings,
 * hoisted module-level function ALLOCs, the two-incarnation for-let
 * {@code LOOP} shape, and {@code FOR_EACH} iteration-binding producing
 * allocations — with identifier loads and assignment stores resolving
 * the dominant incarnation through the installed
 * {@link BindingSiteResolver}. The walk consumes the value-expression
 * seam for initializer/assignment/condition value ops and the comparison
 * producer for comparison operands; it implements no expression-value
 * lowering of its own. Closure production, adapter creation, and adapter
 * invocation stay out of this child's window.</p>
 *
 * <p><b>The closure child (ISSUE-0445).</b> {@link
 * #lowerModuleClosureCore} drives the same session in closure-core mode
 * (the binding walk plus the closure arms): {@code CLOSURE_NEW}/
 * {@code LoweredFunction} for every function expression and every size-1
 * non-group function declaration (the group child partitions SCCs),
 * capture-by-binding with the capture set collected in first-reference
 * order during the buffered detached-body walk (the free bindings of the
 * body resolved through the dominant frame entries at the creation site —
 * B3/B9 R2/R3 as the resolution model, so doubly-nested captures resolve
 * transitively along the detaching chain), captures of later-declared
 * module functions resolving to the hoisted module-init ALLOC (B1), the
 * closure-capture arm of the B2 {@code SHARED_CELL} cell-kind upgrade
 * (whole-scope: the finalization re-derivation over the capture-reference
 * union rewrites every affected {@code BINDING_ALLOC} payload through the
 * single {@link CellKindDerivation} — no production path writes a
 * cell-kind literal outside that derivation, and the thunk/adapter arms
 * are registered by the shape-map child, T7), the {@code LoweredBody}
 * {@code functionBindings} registrations through the registry child's
 * registration seam (B5), and static function-identity preservation on
 * function-typed loads ({@code R-FUNCTION-BINDING} holds by construction;
 * dynamic function values — parameters, catch bindings, iteration
 * bindings — fail closed as the registry child's resolution). Adapter
 * creation and invocation stay out of this child's window.</p>
 *
 * <p><b>The recursive-group child (ISSUE-0446).</b> {@link
 * #lowerModuleGroupCore} drives the same session in group-core mode
 * (the binding walk plus the closure arms plus the group arms): within
 * one scope the lowerer builds the reference graph over function
 * declarations (name references in bodies) and partitions it into SCCs.
 * An SCC of size >= 2 lowers as exactly one {@code RECURSIVE_GROUP_INIT}
 * op with the declaration-ordered member {@code {bindings, functions}}
 * payload — phase 1 allocates a fresh {@code FunctionAllocationIdentity}
 * per member (pre-assigned at lowering in declaration order, unique per
 * member, deterministic) and registers each member's
 * {@code LoweredBody}; phase 2 publishes every member binding cell
 * atomically (the op has no result slot — the bindings are the observable
 * effect). Member cells are {@code SHARED_CELL} by construction (B2:
 * the closed group payload records no cell-kind field, SCC mutual capture
 * makes every member captured, and no member carries a separate
 * {@code BINDING_ALLOC}/{@code BINDING_INIT}); member loads resolve to
 * the group op as the producing allocation at generation 0 (B1 —
 * {@code BindingProducer.RECURSIVE_GROUP_INIT}). Module-level groups
 * execute at module-init top in declaration order (B4); nested-scope
 * groups execute at the first member's declaration position. Member
 * bodies lower like any function body with captures per the closure
 * contract (B3). A size-1 SCC — including a self-recursive declaration —
 * lowers as {@code CLOSURE_NEW} + {@code BINDING_INIT} at the
 * declaration position (the closure child's arm); no group op is
 * produced. Group execution (allocation/publication) is realized by the
 * oracle/emitters — this child produces the op, the member identities,
 * and the payload; {@code GROUP_SHAPE} validation and member invocation
 * stay out of this child's window.</p>
 *
 * <p><b>The immutability-proof child (ISSUE-0448).</b> {@link
 * #lowerModuleImmutabilityCore} drives the same session in proof-analysis
 * mode (the group walk plus the conservative assignment analysis, B7):
 * every variable assignment the walk resolves defeats exactly the
 * dominant incarnation it names — the for-let update defeats the counter
 * generation 0 while the per-iteration generation 1 keeps its proof,
 * parameters are defeated by any body assignment, function names by any
 * assignment in the module, and the {@code int}/{@code number} intrinsic
 * bindings always carry the proof. Proofs derive over the binding-core
 * incarnation map as the closed {@link
 * deal.semantic.ir.BindingImmutabilityProof} records per
 * {@code {binding, generation}} — the facts the shape-map child's VALUE
 * arm consumes; the {@link BindingImmutabilityAnalysis} production class
 * owns the closed rule, records nothing but checker facts (resolved
 * assignments, declaration/parameter facts, intrinsic-binding facts —
 * never target, route, or emitter knowledge), and never consults
 * narrowing flow state (B3). Mode selection, payload construction, and
 * invocation stay out of this child's window.</p>
 *
 * <p><b>The validation child (ISSUE-0451).</b> {@link
 * #lowerModuleValidationCore} drives the complete shape-map walk and
 * additionally runs the production-time validation stack — the closed
 * schema validator, the address-chain protocol, the control-flow
 * validator (C-D2), and the B9 rule set of {@link
 * BindingsProductionValidator} over the one uniform resolution context
 * (R1-R4); the produced {@code LOOP(FOR)} op sits in the enclosing block
 * with its init/body/update blocks as children (C-D4 placement, the
 * intra-{@code LOOP} sequencing input B9's Basis consumes).</p>
 *
 * <p><b>IDs and determinism (D4/D8/D10).</b> Every id is allocated
 * through the project's {@link SemanticIdAllocator} in the pinned order —
 * dependency order, source order, semantic role, then synthetic ordinal —
 * realized here as one strictly increasing per-module source-ordinal
 * sequence handed out in the pinned emission order (element prior steps
 * before the consuming op; boundary children after their parent op;
 * iterable prior steps before the {@code FOR_EACH} op; body ops after
 * it), with the closed role per id kind. The same checked source lowered
 * twice through fresh allocators produces byte-identical validated units
 * and dumps.</p>
 *
 * <p><b>Claiming (D9 items 2–4, at E5's gate).</b> Units built by this
 * stage derive their claim set through {@link ContainerClaimingSeam} (the
 * unit-producer claiming seam, ISSUE-0387): the full-evidence claim
 * derivation over the produced ops and the then-active rows — at E5's
 * gate the active rows are
 * {@link ContainerClaimingSeam#E5_GATE_ACTIVATION} — checked with
 * the derived set as the unit's claims (the derivation-invariant guard —
 * the E6005 {@code OPERATION_OUTSIDE_CLAIMED_CAPABILITY} firing condition
 * can never trigger inside the producer because the unit claims exactly
 * its derived set). A unit fully evidencing an active row claims it; an
 * under-evidenced row defers per unit and the still-staged rows record
 * staged hand-offs. The manifest's plan-time claims are routing facts and
 * stay untouched.</p>
 */
public final class SemanticLowerer {

    /** The producer fact-defect identifier of the E6005 unlowered-construct arm (D7). */
    public static final String CONSTRUCT_UNLOWERED = "CONSTRUCT_UNLOWERED";

    /**
     * The producer fact-defect identifier of the E6005 out-of-signed32
     * int-literal arm (D1's CONST contract — a literal outside the closed
     * scalar set is a producer defect, never an invented op): the checked
     * frontend still admits out-of-int32 literals until the E1036
     * signed32 literal gate (ISSUE-0111) lands, so the {@code CONST} arm
     * fails closed instead of truncating.
     */
    public static final String INT32_LITERAL_OUT_OF_RANGE = "INT32_LITERAL_OUT_OF_RANGE";

    /**
     * The fact-defect identifier of the E6005 profile guard (I3): a
     * lowering request whose invocation profile is not
     * {@code DEAL_V1_2_INT32} is rejected before any op is built —
     * {@code LEGACY_SAFE_INT} is inspectable for routing/regression but
     * never lowered (the validator's R-PROFILE and
     * {@link LoweredModuleUnit}'s constructor guard are the backstops).
     * The detail carries the offending profile, capability
     * {@code FOUNDATION_VALUES}, and the {@code SemanticLowerer} origin.
     */
    public static final String LOWER_LEGACY_PROFILE_REJECTED =
        "LOWER_LEGACY_PROFILE_REJECTED";

    /**
     * The pinned canonical realization id of every lowerer-created
     * boundary child (D3): {@code RuntimeValidation("runtime-validation")}
     * — a pinned constant inside the contract digest, so units and dumps
     * are byte-identical, and E4's report-completion predicate carries it
     * unchanged.
     */
    public static final String CANONICAL_RUNTIME_VALIDATION_ID = "runtime-validation";

    /**
     * The pinned initial generation of every for-of loop binding (D1/D6),
     * of every variable-assignment store in this stage's E5 window, and
     * of every first-incarnation binding of the binding-core child (the
     * for-let per-iteration incarnation is the pinned generation 1 —
     * B1): the {@code FOR_EACH} payload's {@code generation} field and
     * the {@code BINDING_STORE} commit's {@code generation} field carry
     * this initial generation, never rewritten; loads of the loop binding
     * inside the body carry it and the body-runner resolves the effective
     * generation as initial + current iteration index at execution.
     * Binding allocation and generation ordinals are the binding-core
     * child's ({@link #lowerModuleBindingCore}, ISSUE-0444/ISSUE-0235);
     * this stage's E3/E5 window only pins the payload value.
     */
    public static final long INITIAL_LOOP_GENERATION = 0L;

    /**
     * The fact-defect identifier of the E6005 default-block admission arm
     * (class-construction-jsonable-operations K-D3; ISSUE-0511): a
     * detached per-construction {@code CLASS_DEFAULT} block may reference
     * only allocations inside the default block itself and module-level
     * bindings resolved through the module-init block; an
     * enclosing-region (function-local) free reference is invalid and
     * fails E6005 with this {@code validatorRule} — the closed
     * {@code ClassDefaultPayload} records no captures and the closed
     * schema cannot carry them. The detail carries capability
     * {@code CLASSES}, the module, and the {@code SemanticLowerer}
     * origin.
     */
    public static final String CLASS_DEFAULT_CAPTURE = "CLASS_DEFAULT_CAPTURE";
    /**
     * The fact-defect identifier of the E6005 imported-construction
     * deferral arm (class-construction-jsonable-operations K-D4/K-D5;
     * ISSUE-0514): a class-typed literal of an imported class whose
     * owner has no shared factory facts (an owner on a retained route)
     * defers to E10 (ISSUE-0239, the cross-module factory ABI transport)
     * and fails E6005 with this {@code validatorRule} — never silently
     * emitted as {@code SHARED_FACTORY} and never executed here. The
     * detail carries capability {@code CLASSES}, the module, and the
     * {@code SemanticLowerer} origin.
     */
    public static final String RETAINED_ABI_DEFERRED = "RETAINED_ABI_DEFERRED";

    // =========================================================================
    // The binding-core child (ISSUE-0444): incarnations, generations, cell kinds
    // =========================================================================

    /**
     * The closed producing-allocation kinds of the binding-core child:
     * an incarnation is produced by its {@code BINDING_ALLOC} op, by
     * the {@code FOR_EACH} iteration op (the iteration binding's producing
     * allocation — {@code FOR_EACH} payloads record no cell kind because
     * iteration bindings are always {@code SHARED_CELL}, B2), or by the
     * {@code RECURSIVE_GROUP_INIT} group op (the recursive-group child,
     * ISSUE-0446: a group member's producing allocation is the group op's
     * publication phase — members have no separate
     * {@code BINDING_ALLOC}/{@code BINDING_INIT}, B1/B4, and member cells
     * are {@code SHARED_CELL} by construction, B2).
     */
    public enum BindingProducer {

        /** The incarnation's producing allocation is its {@code BINDING_ALLOC} op. */
        BINDING_ALLOC,

        /** The incarnation's producing allocation is the {@code FOR_EACH} iteration op. */
        FOR_EACH,

        /**
         * The incarnation's producing allocation is the
         * {@code RECURSIVE_GROUP_INIT} group op (the member's binding
         * cell is published by the group's atomic publication phase).
         */
        RECURSIVE_GROUP_INIT
    }

    /**
     * One incarnation fact of the binding-core walk: the static
     * per-binding generation ordinal (assigned in lowering order starting
     * at 0), the block the incarnation's producing allocation sits in,
     * the default cell kind ({@code DIRECT} everywhere except the pinned
     * special cases — for-let per-iteration incarnations and
     * {@code FOR_EACH} iteration bindings are {@code SHARED_CELL}), the
     * reassignability fact recorded independently of the cell kind, the
     * producing-allocation kind, and the pinned-shared-cell marker of the
     * closed special cases. The <em>final</em> cell kind of an incarnation
     * is derived by {@link CellKindDerivation} over the union of the
     * pinned special cases and the registered capture references — every
     * {@code BINDING_ALLOC} payload and every facts-surface cell kind
     * flows through that one derivation.
     */
    public record BindingCoreIncarnation(long generation, BlockId scope,
                                         BindingCellKind cellKind, boolean mutable,
                                         BindingProducer producer,
                                         boolean pinnedSharedCell) {

        public BindingCoreIncarnation {
            Objects.requireNonNull(scope, "scope must not be null");
            Objects.requireNonNull(cellKind, "cellKind must not be null");
            Objects.requireNonNull(producer, "producer must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException(
                    "generation must be >= 0, got " + generation);
            }
        }
    }

    /**
     * One declared name's binding-core facts: the single globally unique
     * {@link BindingId} of the declared name and its incarnations in
     * allocation (source) order.
     */
    public record BindingCoreBinding(String name, BindingId binding,
                                     List<BindingCoreIncarnation> incarnations) {

        public BindingCoreBinding {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(binding, "binding must not be null");
            Objects.requireNonNull(incarnations, "incarnations must not be null");
            incarnations = List.copyOf(incarnations);
        }
    }

    /**
     * The binding-core walk's complete fact surface: one entry per
     * declared name in the pinned registration order (intrinsic bindings
     * first, then module-level hoisted names in declaration order, then
     * every remaining declaration in source order).
     */
    public record BindingCoreFacts(List<BindingCoreBinding> bindings) {

        /** The empty fact set (the failure-path value). */
        public static BindingCoreFacts empty() {
            return new BindingCoreFacts(List.of());
        }

        public BindingCoreFacts {
            Objects.requireNonNull(bindings, "bindings must not be null");
            bindings = List.copyOf(bindings);
        }
    }

    /**
     * The result of the binding-core entry point: the validated lowering
     * result plus the walk's binding facts (partial on failure, complete
     * on success).
     */
    public record BindingCoreResult(LoweringResult lowering, BindingCoreFacts facts) {

        public BindingCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(facts, "facts must not be null");
        }
    }

    /**
     * The single cell-kind derivation of the BINDINGS capability's
     * capture-driven cell-kind rule (B2): the final cell kind of every
     * binding incarnation is derived exactly here, over the union of the
     * pinned special cases ({@code FOR_EACH} iteration bindings and
     * for-let per-iteration incarnations — the binding-core defaults)
     * and the registered capture references. The complete closed iff
     * ("{@code SHARED_CELL} iff any function capture resolves to the
     * incarnation") is enforced by construction: cell kinds are emitted
     * only from this derivation, never from a literal outside it.
     *
     * <p><b>Ownership split (B2's three capture arms).</b> The closure
     * child (ISSUE-0445) registers the {@code CLOSURE_NEW}/
     * {@code LoweredFunction.captures} arm through
     * {@link #registerCaptureReference} and re-derives every
     * {@code BINDING_ALLOC} payload cell kind after the walk (whole-scope
     * analysis: a closure anywhere in the enclosing scope referencing the
     * binding upgrades every incarnation of that binding that a capture
     * resolves to). The shape-map child (T7) registers the two remaining
     * arms — {@code REEVALUATE_THUNK} {@code capturedBindings} entries and
     * {@code FUNCTION_ADAPT(SHARED_CELL)} {@code SharedCell} source
     * references — through the same registration surface and runs the
     * final derivation after registering them; this child emits and
     * claims neither arm.</p>
     *
     * <p>Capture references are registered per incarnation instance
     * (identity semantics): two equal-shaped incarnations of different
     * bindings never alias in the reference set.</p>
     */
    public static final class CellKindDerivation {

        /** The registered capture references (identity semantics). */
        private final Set<BindingCoreIncarnation> captureReferences =
            java.util.Collections.newSetFromMap(new IdentityHashMap<>());

        /**
         * Registers one capture reference (B2's closure-capture arm for
         * this child; the shape-map child registers the thunk/adapter
         * arms through the same surface): the incarnation the capture
         * resolves to at the capture's creation site.
         *
         * @param incarnation the resolved incarnation; non-null
         */
        public void registerCaptureReference(BindingCoreIncarnation incarnation) {
            captureReferences.add(Objects.requireNonNull(incarnation,
                "incarnation must not be null"));
        }

        /** True iff any capture reference resolves to the incarnation. */
        public boolean isCaptured(BindingCoreIncarnation incarnation) {
            return captureReferences.contains(incarnation);
        }

        /** The number of registered capture references. */
        public int captureReferenceCount() {
            return captureReferences.size();
        }

        /**
         * The derived cell kind of one incarnation: {@code SHARED_CELL}
         * iff the incarnation is a pinned special case or any registered
         * capture resolves to it; {@code DIRECT} otherwise (reassignability
         * alone never forces {@code SHARED_CELL} — the {@code mutable}
         * flag records it independently).
         *
         * @param incarnation the incarnation; non-null
         * @return the derived {@code DIRECT|SHARED_CELL} kind
         */
        public BindingCellKind cellKindOf(BindingCoreIncarnation incarnation) {
            Objects.requireNonNull(incarnation, "incarnation must not be null");
            if (incarnation.pinnedSharedCell() || isCaptured(incarnation)) {
                return BindingCellKind.SHARED_CELL;
            }
            return BindingCellKind.DIRECT;
        }
    }

    /**
     * One resolved closure capture of the closure child's fact surface:
     * the captured binding plus the producing allocation the capture
     * resolves to at the detaching op's creation site — the dominant
     * incarnation's generation, the block its producing allocation sits
     * in, and the producing-allocation kind (B9 R1/R2: the resolution
     * evaluated at the {@code CLOSURE_NEW} creation site, recursively
     * along the detaching chain).
     */
    public record ClosureCapture(String name, BindingId binding, long generation,
                                 BlockId scope, BindingProducer producer) {

        public ClosureCapture {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(binding, "binding must not be null");
            Objects.requireNonNull(scope, "scope must not be null");
            Objects.requireNonNull(producer, "producer must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException(
                    "generation must be >= 0, got " + generation);
            }
        }
    }

    /**
     * One closure's complete fact record (ISSUE-0445 closure child): the
     * function identity, the exact signature, the body block identity,
     * and the resolved captures in first-reference order.
     */
    public record ClosureFacts(FunctionId functionId, RuntimeDescriptor.Func signature,
                               BlockId bodyBlock, List<ClosureCapture> captures) {

        public ClosureFacts {
            Objects.requireNonNull(functionId, "functionId must not be null");
            Objects.requireNonNull(signature, "signature must not be null");
            Objects.requireNonNull(bodyBlock, "bodyBlock must not be null");
            Objects.requireNonNull(captures, "captures must not be null");
            captures = List.copyOf(captures);
        }
    }

    /**
     * The result of the closure-core entry point: the validated lowering
     * result, the binding walk's binding facts (with final derived cell
     * kinds), and the produced closures' capture facts in creation order
     * (partial on failure, complete on success).
     */
    public record ClosureCoreResult(LoweringResult lowering, BindingCoreFacts bindingFacts,
                                    List<ClosureFacts> closures) {

        public ClosureCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(bindingFacts, "bindingFacts must not be null");
            Objects.requireNonNull(closures, "closures must not be null");
            closures = List.copyOf(closures);
        }
    }

    /**
     * One group member's complete fact record (ISSUE-0446 recursive-group
     * child): the declared name, the member's single {@link BindingId}
     * (no separate {@code BINDING_ALLOC}/{@code BINDING_INIT} — the
     * group op's publication phase is the producing allocation), the
     * member function identity, the pre-assigned member allocation
     * identity (unique per member, declaration order — the key the
     * registry's {@code LoweredBody} registration consumes, B4/B5), the
     * exact signature, the body block identity, and the member body's
     * captures resolved at the group op's creation site (B3).
     */
    public record GroupMemberFacts(String name, BindingId binding, FunctionId functionId,
                                   ValueId identity, RuntimeDescriptor.Func signature,
                                   BlockId bodyBlock, List<ClosureCapture> captures) {

        public GroupMemberFacts {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(binding, "binding must not be null");
            Objects.requireNonNull(functionId, "functionId must not be null");
            Objects.requireNonNull(identity, "identity must not be null");
            Objects.requireNonNull(signature, "signature must not be null");
            Objects.requireNonNull(bodyBlock, "bodyBlock must not be null");
            Objects.requireNonNull(captures, "captures must not be null");
            captures = List.copyOf(captures);
        }
    }

    /**
     * One produced {@code RECURSIVE_GROUP_INIT} op's complete fact
     * record (ISSUE-0446 recursive-group child): the op identity, the
     * declaration-ordered member facts, and the block the group op sits
     * in (module-init top for module-level groups; the first member's
     * enclosing block for nested-scope groups — B4).
     */
    public record GroupFacts(OpId opId, List<GroupMemberFacts> members, BlockId block) {

        public GroupFacts {
            Objects.requireNonNull(opId, "opId must not be null");
            Objects.requireNonNull(members, "members must not be null");
            Objects.requireNonNull(block, "block must not be null");
            members = List.copyOf(members);
        }
    }

    /**
     * The result of the group-core entry point: the validated lowering
     * result, the binding walk's binding facts (with final derived cell
     * kinds), the produced closures' capture facts in creation order,
     * and the produced recursive groups' member facts in creation order
     * (partial on failure, complete on success).
     */
    public record GroupCoreResult(LoweringResult lowering, BindingCoreFacts bindingFacts,
                                  List<ClosureFacts> closures, List<GroupFacts> groups) {

        public GroupCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(bindingFacts, "bindingFacts must not be null");
            Objects.requireNonNull(closures, "closures must not be null");
            Objects.requireNonNull(groups, "groups must not be null");
            closures = List.copyOf(closures);
            groups = List.copyOf(groups);
        }
    }

    /**
     * The result of the immutability-proof entry point (ISSUE-0448 proof
     * child): the validated lowering result, the binding walk's binding
     * facts (the incarnation map the proofs derive over), the produced
     * closures' capture facts, the produced recursive groups' member
     * facts, and the derived {@code BindingImmutabilityProof} fact
     * surface — proof records per {@code {binding, generation}} of the
     * dominant incarnation plus the resolved assignment facts (partial
     * on failure, complete on success). The unit's
     * {@code functionBindings} map is populated by the same walk through
     * the registry child's seam (B5 — the registry-combined proof
     * surface).
     */
    public record ImmutabilityCoreResult(
            LoweringResult lowering, BindingCoreFacts bindingFacts,
            List<ClosureFacts> closures, List<GroupFacts> groups,
            BindingImmutabilityAnalysis.BindingImmutabilityFacts proofFacts) {

        public ImmutabilityCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(bindingFacts, "bindingFacts must not be null");
            Objects.requireNonNull(closures, "closures must not be null");
            Objects.requireNonNull(groups, "groups must not be null");
            Objects.requireNonNull(proofFacts, "proofFacts must not be null");
            closures = List.copyOf(closures);
            groups = List.copyOf(groups);
        }
    }

    /**
     * The result of the creation-rule entry point (ISSUE-0449
     * creation-rule child): the validated lowering result, the binding
     * walk's binding facts, the produced closures' capture facts, the
     * produced recursive groups' member facts, the derived proof fact
     * surface, and the creation-rule classification facts — one
     * {@link AdapterCreationRule.PositionClassification} per classified
     * function-typed position in walk order (partial on failure,
     * complete on success). The unit the walk produced contains zero
     * {@code FUNCTION_ADAPT} ops (mode selection, payload construction,
     * and emission are the shape-map child's) and the classification is
     * purely observational: the same walk's emitted ops are
     * byte-identical to the proof child's for the same checked module.
     */
    public record CreationRuleCoreResult(
            LoweringResult lowering, BindingCoreFacts bindingFacts,
            List<ClosureFacts> closures, List<GroupFacts> groups,
            BindingImmutabilityAnalysis.BindingImmutabilityFacts proofFacts,
            AdapterCreationRule.CreationRuleFacts creationFacts) {

        public CreationRuleCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(bindingFacts, "bindingFacts must not be null");
            Objects.requireNonNull(closures, "closures must not be null");
            Objects.requireNonNull(groups, "groups must not be null");
            Objects.requireNonNull(proofFacts, "proofFacts must not be null");
            Objects.requireNonNull(creationFacts, "creationFacts must not be null");
            closures = List.copyOf(closures);
            groups = List.copyOf(groups);
        }
    }

    /**
     * One emitted adapter of the shape-map child (ISSUE-0450 sequencing
     * item 7): the producing {@code FUNCTION_ADAPT} op, its fresh
     * adapter allocation identity (fresh per creation, stable for the
     * run — B8), the closed-map capture mode and the closed source
     * reference the op carries from birth (the map's mode plus its
     * per-mode payload — B7/B8; no provisional or non-map mode ever
     * exists), the derived source/target signature pair, the recorded
     * immutability proof (present exactly for VALUE over a binding
     * load — B8), and the consumed wiring point (the adapted position's
     * own {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
     * boundary op or the inferred declaration's {@code BINDING_INIT} —
     * B9's creation-wiring target). At creation the adapter result is
     * the direct input of exactly that boundary chain; after the
     * commit it flows as an ordinary identity-preserving function
     * value whose later typed-boundary crossings are ordinary
     * {@code FUNCTION_SIGNATURE} checks (a later crossing's input
     * carries the same identity through a load, never through the
     * adapter's own direct wiring).
     */
    public record AdapterEmission(
            OpId adaptOpId, ValueId adapterIdentity, CaptureMode mode,
            AdaptSourceRef sourceRef, RuntimeDescriptor.Func sourceSignature,
            RuntimeDescriptor.Func targetSignature, BindingImmutabilityProof proof,
            OpId wiringTargetOpId, BoundaryKind wiringBoundaryKind) {

        public AdapterEmission {
            Objects.requireNonNull(adaptOpId, "adaptOpId must not be null");
            Objects.requireNonNull(adapterIdentity, "adapterIdentity must not be null");
            Objects.requireNonNull(mode, "mode must not be null");
            Objects.requireNonNull(sourceRef, "sourceRef must not be null");
            Objects.requireNonNull(sourceSignature, "sourceSignature must not be null");
            Objects.requireNonNull(targetSignature, "targetSignature must not be null");
            Objects.requireNonNull(wiringTargetOpId, "wiringTargetOpId must not be null");
            Objects.requireNonNull(wiringBoundaryKind, "wiringBoundaryKind must not be null");
        }
    }

    /**
     * The shape-map child's complete emission fact surface of one module
     * lowering: one {@link AdapterEmission} per emitted
     * {@code FUNCTION_ADAPT} op in emission order (partial on a failed
     * walk, complete on success).
     */
    public record ShapeMapFacts(List<AdapterEmission> emissions) {

        /** The empty fact set (the failure-path value). */
        public static ShapeMapFacts empty() {
            return new ShapeMapFacts(List.of());
        }

        public ShapeMapFacts {
            Objects.requireNonNull(emissions, "emissions must not be null");
            emissions = List.copyOf(emissions);
        }
    }

    /**
     * The result of the shape-map entry point (ISSUE-0450 shape-map
     * child): the validated lowering result, the binding walk's binding
     * facts, the produced closures' capture facts, the produced
     * recursive groups' member facts, the derived proof fact surface,
     * the creation-rule classification facts, and the shape-map
     * emission facts (partial on failure, complete on success). Unlike
     * the creation-rule child, the produced unit carries exactly one
     * {@code FUNCTION_ADAPT} op per {@code ADAPT}-classified position —
     * the closed-map mode with its per-mode payload from birth, wired
     * as the direct input of the adapted position's own boundary chain
     * (B6-B9).
     */
    public record ShapeMapCoreResult(
            LoweringResult lowering, BindingCoreFacts bindingFacts,
            List<ClosureFacts> closures, List<GroupFacts> groups,
            BindingImmutabilityAnalysis.BindingImmutabilityFacts proofFacts,
            AdapterCreationRule.CreationRuleFacts creationFacts,
            ShapeMapFacts shapeMapFacts) {

        public ShapeMapCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(bindingFacts, "bindingFacts must not be null");
            Objects.requireNonNull(closures, "closures must not be null");
            Objects.requireNonNull(groups, "groups must not be null");
            Objects.requireNonNull(proofFacts, "proofFacts must not be null");
            Objects.requireNonNull(creationFacts, "creationFacts must not be null");
            Objects.requireNonNull(shapeMapFacts, "shapeMapFacts must not be null");
            closures = List.copyOf(closures);
            groups = List.copyOf(groups);
        }
    }

    /**
     * The result of the validation entry point (ISSUE-0451 validation
     * child, sequencing item 8): the B9-validated lowering result plus
     * the complete fact surfaces of the six production children
     * (partial on failure, complete on success). The unit is produced
     * by the same shape-map walk as {@link ShapeMapCoreResult} and is
     * additionally validated by the closed schema validator, the
     * address-chain protocol (A-D1), the control-flow validator
     * (C-D2 — the block-tree/dominance/exits Basis the B9 rules run
     * over), and the B9 production-time rule set of
     * {@link BindingsProductionValidator}.
     */
    public record ValidationCoreResult(
            LoweringResult lowering, BindingCoreFacts bindingFacts,
            List<ClosureFacts> closures, List<GroupFacts> groups,
            BindingImmutabilityAnalysis.BindingImmutabilityFacts proofFacts,
            AdapterCreationRule.CreationRuleFacts creationFacts,
            ShapeMapFacts shapeMapFacts) {

        public ValidationCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(bindingFacts, "bindingFacts must not be null");
            Objects.requireNonNull(closures, "closures must not be null");
            Objects.requireNonNull(groups, "groups must not be null");
            Objects.requireNonNull(proofFacts, "proofFacts must not be null");
            Objects.requireNonNull(creationFacts, "creationFacts must not be null");
            Objects.requireNonNull(shapeMapFacts, "shapeMapFacts must not be null");
            closures = List.copyOf(closures);
            groups = List.copyOf(groups);
        }
    }

    /**
     * The dominant-incarnation resolver of the binding environment
     * (ISSUE-0444 binding-core child): the identifier arm and the
     * variable-assignment arm consult this hook when installed so every
     * {@code BINDING_LOAD}/{@code BINDING_STORE} they emit names the
     * dominant incarnation at the site (B9 R1). Absent (the default in
     * this stage's E3/E5 window), the pre-existing frame/on-demand
     * resolution is unchanged.
     */
    @FunctionalInterface
    public interface BindingSiteResolver {

        /**
         * The dominant incarnation of the named declared binding at the
         * current site, or {@code null} when the name is not a declared
         * binding of the installed environment.
         *
         * @param name the source identifier name; non-null
         * @return the dominant incarnation, or {@code null}
         */
        BindingSite resolve(String name);
    }

    /**
     * One generation-pinned binding reference of the installed resolver:
     * the binding identity plus the dominant generation at the site.
     */
    public record BindingSite(BindingId binding, long generation) {

        public BindingSite {
            Objects.requireNonNull(binding, "binding must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException(
                    "generation must be >= 0, got " + generation);
            }
        }
    }

    private SemanticLowerer() {
        // Static entry points plus the per-module lowering session; no instances.
    }

    /**
     * A construct reaching an arm of this stage without a lowering arm
     * (D7): internal control flow, converted at the unit-production seam
     * to the pinned E6005 {@code CONSTRUCT_UNLOWERED} diagnostic — a hard
     * compile failure in this stage's window, never a reroute and never a
     * crash.
     */
    public static final class ConstructUnlowered extends RuntimeException {

        private static final long serialVersionUID = 1L;

        /** The human-readable construct description (pinned in the diagnostic's origin). */
        private final String construct;

        public ConstructUnlowered(String construct) {
            super("a construct without a lowering arm reached this stage: " + construct);
            this.construct = Objects.requireNonNull(construct, "construct must not be null");
        }

        /** The construct description carried into the E6005 origin. */
        public String construct() {
            return construct;
        }
    }

    /**
     * A default-block reference outside the closed admission rule
     * (class-construction-jsonable-operations K-D3; ISSUE-0511): a
     * detached per-construction {@code CLASS_DEFAULT} block may reference
     * only allocations inside the default block itself and module-level
     * bindings resolved through the module-init block. An
     * enclosing-region (function-local) free reference is invalid —
     * the closed {@code ClassDefaultPayload} records no captures and the
     * closed schema cannot carry them — and converts at the unit-production
     * seam to the pinned E6005 {@code CLASS_DEFAULT_CAPTURE} diagnostic
     * (capability {@code CLASSES}) — never a silent capture, never a
     * reroute, and never a crash.
     */
    public static final class ClassDefaultCapture extends RuntimeException {

        private static final long serialVersionUID = 1L;

        /** The referenced enclosing-region name carried into the E6005 origin. */
        private final String name;

        public ClassDefaultCapture(String name) {
            super("default-block free reference '" + name
                + "' resolves to an enclosing-region binding (a detached "
                + "CLASS_DEFAULT block admits only block-internal allocations and "
                + "module-level bindings resolved through the module-init block; the "
                + "closed payload records no captures)");
            this.name = Objects.requireNonNull(name, "name must not be null");
        }

        /** The referenced enclosing-region name carried into the E6005 origin. */
        public String name() {
            return name;
        }
    }

    /**
     * The imported-construction deferral defect of the class-literal arm
     * (class-construction-jsonable-operations K-D4; ISSUE-0514): a
     * class-typed literal of an imported class whose owner carries no
     * shared factory facts — an owner not on the shared route — defers
     * to E10 (ISSUE-0239, the cross-module factory ABI transport) and
     * converts at the unit-production seam to the pinned E6005
     * {@code RETAINED_ABI_DEFERRED} diagnostic (capability
     * {@code CLASSES}) — never a silent {@code SHARED_FACTORY} emission,
     * never a silent {@code RETAINED_ABI} emission, and never a crash.
     * Same-module literals stay LOCAL (T2's arm).
     */
    public static final class RetainedAbiDeferred extends RuntimeException {

        private static final long serialVersionUID = 1L;

        /** The imported class identity carried into the E6005 origin. */
        private final String classId;

        public RetainedAbiDeferred(String classId) {
            super("class-typed literal of imported class " + classId
                + " whose owner carries no shared factory facts (the "
                + "RETAINED_ABI derivation is E10's, ISSUE-0239)");
            this.classId = Objects.requireNonNull(classId, "classId must not be null");
        }

        /** The imported class identity carried into the E6005 origin. */
        public String classId() {
            return classId;
        }
    }

    /**
     * An int literal whose value is outside the closed signed32 scalar
     * set (D1's CONST contract — "a literal outside the closed scalar
     * set is a producer defect (E6005), never an invented op"): the
     * checked frontend still admits out-of-int32 literals until the
     * E1036 signed32 literal gate (ISSUE-0111) lands, so the
     * {@code CONST} arm fails closed instead of truncating. Converted at
     * the unit-production seam to the pinned E6005
     * {@code INT32_LITERAL_OUT_OF_RANGE} diagnostic — a hard compile
     * failure in this stage's window, never a truncation, never an
     * invented scalar, and never a crash.
     */
    public static final class IntLiteralOutOfRange extends RuntimeException {

        private static final long serialVersionUID = 1L;

        /** The out-of-range literal value carried into the E6005 origin. */
        private final long value;

        public IntLiteralOutOfRange(long value) {
            super("int literal " + value
                + " outside signed32 [-2147483648, 2147483647] (the E1036 "
                + "signed32 literal gate is ISSUE-0111's frontend item; this "
                + "stage fails closed, never truncates)");
            this.value = value;
        }

        /** The out-of-range literal value carried into the E6005 origin. */
        public long value() {
            return value;
        }
    }

    /**
     * The unit-production seam's failure carrier (D2/D7): maps a defect
     * raised by an arm to its exact {@link LoweringFailureDetail} —
     * {@code ConstructUnlowered} → E6005 {@code CONSTRUCT_UNLOWERED}
     * (capability {@code CONTAINERS_AND_STRINGS}, origin
     * {@code SemanticLowerer CONSTRUCT_UNLOWERED (construct)}),
     * {@link IntLiteralOutOfRange} → E6005
     * {@code INT32_LITERAL_OUT_OF_RANGE} (capability
     * {@code SIGNED_INT32}, origin
     * {@code SemanticLowerer INT32_LITERAL_OUT_OF_RANGE (defect message)}),
     * and a {@link ContainerPayloadDescriptors.Defect} → E6005
     * {@code DESCRIPTOR_UNREPRESENTABLE} through the bridge's pinned
     * carrier. The caller converts the returned detail into the E6005
     * diagnostic through {@code FailureContractRegistry.e6005(detail)};
     * this seam constructs no diagnostic itself.
     *
     * @param module the module whose unit-production seam hit the defect;
     *               non-null
     * @param defect the defect raised by an arm; non-null
     * @return the exact {@code LoweringFailureDetail} of the named failure
     * @throws IllegalArgumentException on a defect kind this stage has no
     *         E6005 projection for (a producer defect)
     */
    public static LoweringFailureDetail loweringFailureDetail(ModuleId module,
                                                              RuntimeException defect) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(defect, "defect must not be null");
        if (defect instanceof ConstructUnlowered unlowered) {
            return new LoweringFailureDetail(module.path(),
                SemanticCapability.CONTAINERS_AND_STRINGS, CONSTRUCT_UNLOWERED,
                SemanticProfile.DEAL_V1_2_INT32, LoweredModuleUnit.FORMAT_VERSION,
                "SemanticLowerer " + CONSTRUCT_UNLOWERED + " (" + unlowered.construct() + ")");
        }
        if (defect instanceof IntLiteralOutOfRange outOfRange) {
            return new LoweringFailureDetail(module.path(),
                SemanticCapability.SIGNED_INT32, INT32_LITERAL_OUT_OF_RANGE,
                SemanticProfile.DEAL_V1_2_INT32, LoweredModuleUnit.FORMAT_VERSION,
                "SemanticLowerer " + INT32_LITERAL_OUT_OF_RANGE + " ("
                    + outOfRange.getMessage() + ")");
        }
        if (defect instanceof ClassDefaultCapture capture) {
            return new LoweringFailureDetail(module.path(),
                SemanticCapability.CLASSES, CLASS_DEFAULT_CAPTURE,
                SemanticProfile.DEAL_V1_2_INT32, LoweredModuleUnit.FORMAT_VERSION,
                "SemanticLowerer " + CLASS_DEFAULT_CAPTURE + " (" + capture.getMessage() + ")");
        }
        if (defect instanceof RetainedAbiDeferred deferred) {
            return new LoweringFailureDetail(module.path(),
                SemanticCapability.CLASSES, RETAINED_ABI_DEFERRED,
                SemanticProfile.DEAL_V1_2_INT32, LoweredModuleUnit.FORMAT_VERSION,
                "SemanticLowerer " + RETAINED_ABI_DEFERRED + " (class "
                    + deferred.classId() + " — the RETAINED_ABI derivation is E10's)");
        }
        if (defect instanceof ContainerPayloadDescriptors.Defect descriptorDefect) {
            return ContainerPayloadDescriptors.loweringFailureDetail(module, descriptorDefect);
        }
        throw new IllegalArgumentException(
            "a defect kind without an E6005 projection in this stage reached the seam: "
                + defect.getClass().getSimpleName());
    }

    /**
     * The result of the module-level unit production: the validated unit
     * plus its produced {@link StructuredBodyTable} (C-D1), or
     * {@code null}/{@code null} with exactly the first E6005 diagnostic
     * on failure (a lowered-away construct, an unrepresentable
     * descriptor, a validator rejection of the produced unit, an
     * address-chain protocol violation, or a control-flow validation
     * rejection).
     *
     * @param unit        the validated {@link LoweredModuleUnit}, or
     *                    {@code null} on failure
     * @param table       the produced block-membership table of the unit
     *                    (C-D1), or {@code null} on failure
     * @param diagnostics empty on success, otherwise the failure
     *                    diagnostics
     */
    public record LoweringResult(LoweredModuleUnit unit, StructuredBodyTable table,
                                 List<CompilerDiagnostic> diagnostics) {

        public LoweringResult {
            Objects.requireNonNull(diagnostics, "diagnostics must not be null");
            diagnostics = List.copyOf(diagnostics);
        }

        /** True iff the lowering failed (no unit was produced). */
        public boolean hasErrors() {
            return !diagnostics.isEmpty();
        }
    }

    /**
     * The E7 call-machine lowering result (ISSUE-0236): the validated
     * lowering result plus the module's recorded {@code EXTERNAL_ENTRY}
     * and {@code CALLBACK_INVOKE} op ids by export name — the surfaces a
     * caller module's {@code CALL(EXTERNAL)}/{@code ASYNC_START(EXTERNAL)}
     * resolution and the scenario host's callback triggering consume. On
     * failure the lowering result carries the first E6005 and both maps
     * are empty.
     */
    public record FullProgramE7Result(LoweringResult lowering,
                                      Map<String, OpId> externalEntries,
                                      Map<String, OpId> callbackInvokes) {

        public FullProgramE7Result {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(externalEntries, "externalEntries must not be null");
            Objects.requireNonNull(callbackInvokes, "callbackInvokes must not be null");
            externalEntries = Map.copyOf(externalEntries);
            callbackInvokes = Map.copyOf(callbackInvokes);
        }
    }

    /**
     * The class-declaration child's lowering result (ISSUE-0511,
     * extended by the ISSUE-0515 JSON child): the validated lowering
     * result plus the two produced production records carried alongside
     * the unit (K-D2/K-D8 — the
     * {@link deal.semantic.ir.FunctionBindingRegistry}/
     * {@link StructuredBodyTable} precedent): the
     * {@link deal.semantic.ir.ClassFactoryRegistry}
     * factory-registration record (the
     * {@code constructionEntry}&#8594;{@code CLASS_FACTORY} op bindings) and the
     * {@link deal.semantic.ir.JsonDefaultChildTable} record (the
     * per-site {@code CLASS_DEFAULT} child op ids of every
     * {@code @jsonable} class's {@code JSON_FROM_CLASS} op in
     * declaration order). On failure the lowering result carries the
     * first E6005 and both records are empty.
     */
    public record ClassDeclarationCoreResult(LoweringResult lowering,
                                             deal.semantic.ir.ClassFactoryRegistry registry,
                                             deal.semantic.ir.JsonDefaultChildTable jsonDefaults) {

        public ClassDeclarationCoreResult {
            Objects.requireNonNull(lowering, "lowering must not be null");
            Objects.requireNonNull(registry, "registry must not be null");
            Objects.requireNonNull(jsonDefaults, "jsonDefaults must not be null");
        }
    }

    /**
     * One frame of the lowering environment (D1's loop-binding
     * load-resolution rule): the enclosing for-of's loop-binding name,
     * its producer-allocated {@link BindingId}, and the payload's initial
     * generation. A {@code BINDING_LOAD} of the frame's name carries the
     * frame's generation; the for-of arm pushes exactly one frame while
     * lowering the loop body.
     */
    public record ForEachFrame(String name, BindingId binding, long generation) {

        public ForEachFrame {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(binding, "binding must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException("generation must be >= 0, got " + generation);
            }
        }
    }

    /**
     * One catch-binding frame of the lowering environment (C-D6): the
     * enclosing {@code TRY_CATCH}'s catch-variable name and its
     * producer-allocated {@link BindingId}. A {@code BINDING_LOAD} of
     * the frame's name carries the frame's binding with the pinned
     * initial generation; the try/catch arm pushes exactly one frame
     * while lowering the catch block. Binding init mechanics are E6's
     * (ISSUE-0235) — this stage pins the binding identity and the load
     * resolution only.
     */
    public record CatchFrame(String name, BindingId binding) {

        public CatchFrame {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(binding, "binding must not be null");
        }
    }

    /**
     * Lowers one checked implementation module through this stage and
     * produces the validated unit (the unit-production seam, S1): the
     * module's top-level statements lower through the positionable
     * statement arms (for-of statements, the E5 delete arm — transparent
     * blocks recurse; every other statement is a foreign construct and
     * fails E6005 {@code CONSTRUCT_UNLOWERED}), the manifest's
     * construct-coverage rows are recorded onto the unit at lowering
     * start, descriptor defects convert to E6005
     * {@code DESCRIPTOR_UNREPRESENTABLE}, and the produced unit must pass
     * the closed validator, the production-time address-chain protocol
     * (A-D1), and the production-time control-flow validation of
     * {@link ControlFlowValidator} over the unit plus its produced
     * {@link StructuredBodyTable} (C-D2 — block tree, dominance, exits;
     * the first rejection is the returned diagnostic). At E5's gate the
     * unit's capability claim set is derived through the claiming seam
     * under {@link ContainerClaimingSeam#E5_GATE_ACTIVATION} (D9 item
     * 5(c) — {@code CONTAINERS_AND_STRINGS} and {@code EVALUATION_ORDER}
     * activate).
     *
     * <p><b>I3 profile guard.</b> The invocation profile is a required
     * input: a lowering request whose profile is not
     * {@code DEAL_V1_2_INT32} is rejected with E6005
     * {@link #LOWER_LEGACY_PROFILE_REJECTED} before any op is built —
     * {@code LEGACY_SAFE_INT} is inspectable for routing/regression but
     * never lowered; the validator's R-PROFILE is the backstop.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit plus its block-membership table, or
     *         the first E6005 on failure
     */
    public static LoweringResult lowerModule(CheckedModuleInput module,
                                             SemanticProfile profile,
                                             Map<ConstructKind, List<SemanticOpKind>>
                                                 constructCoverage,
                                             String interfaceHash,
                                             String capabilityRegistryHash,
                                             SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: the rejection runs before any op is built and
        // before any id is allocated — a LEGACY_SAFE_INT lowering request
        // produces no unit and no partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new LoweringResult(null, null, List.of(FailureContractRegistry.e6005(
                new LoweringFailureDetail(module.moduleId().path(),
                    SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                    profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer"))));
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator);
        try {
            lowerer.lowerStatements(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered))));
        } catch (IntLiteralOutOfRange outOfRange) {
            return new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange))));
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect))));
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new LoweringResult(null, null, List.of(validation.get()));
        }
        // E5 production-time check (A-D1): the closed address-chain
        // protocol runs after the foundation validator — every produced
        // ASSIGN/DELETE chain must match exactly one closed A-D9 shape
        // with single evaluation; the first violation is the returned
        // E6005 (ADDRESS_CHAIN_SHAPE | SINGLE_EVALUATION).
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new LoweringResult(null, null, List.of(chainShape.get()));
        }
        // E5 production-time check (C-D2): the produced block-membership
        // table of the unit must pass the control-flow validator — block
        // tree, dominance, and exit checks; the first violation is the
        // returned E6005 (CONTROL_BLOCK_TREE | CONTROL_EXIT).
        StructuredBodyTable table = lowerer.bodyTable();
        Optional<CompilerDiagnostic> controlFlow = ControlFlowValidator.validate(unit, table);
        if (controlFlow.isPresent()) {
            return new LoweringResult(null, null, List.of(controlFlow.get()));
        }
        return new LoweringResult(unit, table, List.of());
    }

    /**
     * The binding-core child's public lowering entry point (ISSUE-0444
     * sequencing item 1): lowers one checked implementation module
     * through the binding walk — one {@code BindingId} per declared name,
     * static per-incarnation generation ordinals, {@code
     * BINDING_ALLOC/INIT/LOAD/STORE} production with the closed
     * {@code DIRECT|SHARED_CELL} defaults and special cases, hoisted
     * module-level function ALLOCs and module-init-top intrinsic
     * bindings, the two-incarnation for-let shape, and {@code FOR_EACH}
     * iteration-binding producing allocations — and produces the validated
     * unit plus the walk's binding facts.
     *
     * <p>The walk consumes the value-expression seam of
     * {@link ModuleLowerer} for initializer/assignment/condition value
     * ops (never re-implementing expression-value lowering); comparison
     * operands lower through the single comparison producer
     * {@link ComparisonSelectorLowering} (the values epic's producer),
     * and identifier loads plus variable-assignment stores resolve
     * through the installed {@link BindingSiteResolver} so every
     * {@code BINDING_LOAD}/{@code BINDING_STORE} payload names the
     * dominant incarnation at the site (B9 R1). The produced unit passes
     * the closed validator, the production-time address-chain protocol,
     * and the claiming seam under the pinned E6-gate activation
     * ({@code BINDINGS} activates for {@code BINDING_LOAD}; binding-core
     * units defer the row per unit because the full family set includes
     * the closure child's {@code RECURSIVE_GROUP_INIT}/
     * {@code CLOSURE_NEW}).</p>
     *
     * <p>This entry point is driven by the binding-core tests; no
     * production route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the binding facts, or the first
     *         E6005 with the partial facts on failure
     */
    public static BindingCoreResult lowerModuleBindingCore(CheckedModuleInput module,
                                                           SemanticProfile profile,
                                                           Map<ConstructKind,
                                                               List<SemanticOpKind>>
                                                               constructCoverage,
                                                           String interfaceHash,
                                                           String capabilityRegistryHash,
                                                           SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModule — a non-DEAL_V1_2_INT32
        // lowering request produces no unit and no partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, module.ast().span());
        try {
            lowerer.lowerBindingModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(validation.get())), lowerer.bindingFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new BindingCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())), lowerer.bindingFacts());
        }
        return new BindingCoreResult(new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts());
    }

    /**
     * The full-program lowering entry of the decomposition-tail carrier
     * slice (ISSUE-0410): lowers one checked implementation module
     * through the unified walk — module-level lets/imports/functions,
     * every E5 statement and expression arm, the carrier's
     * {@code CALL(DIRECT)}/console-{@code STDLIB_CALL}/{@code RETURN}
     * arms inside function bodies, the per-function return-boundary and
     * call-site reservations, and the module-init-level entry delegation
     * ({@code CALL(DIRECT main)} + {@code DISCARD}) — and produces the
     * validated unit plus the block-membership table under the same
     * validator/address-chain/control-flow gates as {@link #lowerModule}.
     *
     * <p>This entry point is driven by the decomposition-tail integration
     * matrix (the semantic oracle and both shared emitters consume its
     * output); no production route change — retained/public compilation
     * paths and {@link #lowerModule}/{@link #lowerModuleBindingCore}/
     * {@link #lowerModuleClosureCore} are untouched.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile (I3
     *                              guard: only {@code DEAL_V1_2_INT32}
     *                              is lowered); non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with its produced block-membership
     *         table, or the first E6005
     */
    public static LoweringResult lowerModuleFullProgram(CheckedModuleInput module,
                                                        SemanticProfile profile,
                                                        Map<ConstructKind,
                                                            List<SemanticOpKind>>
                                                            constructCoverage,
                                                        String interfaceHash,
                                                        String capabilityRegistryHash,
                                                        SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new LoweringResult(null, null, List.of(FailureContractRegistry.e6005(
                new LoweringFailureDetail(module.moduleId().path(),
                    SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                    profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer"))));
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, module.ast().span(), true);
        lowerer.setModuleImports(module.imports());
        try {
            lowerer.seedIntrinsicBindings();
            lowerer.hoistModuleLevelAllocs(module.ast().statements());
            lowerer.statementWalk.walk(module.ast().statements(), true);
            lowerer.emitEntryMainCall();
            lowerer.finalizeCellKinds();
        } catch (ConstructUnlowered unlowered) {
            return new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered))));
        } catch (IntLiteralOutOfRange outOfRange) {
            return new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange))));
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect))));
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect)));
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new LoweringResult(null, null, List.of(validation.get()));
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new LoweringResult(null, null, List.of(chainShape.get()));
        }
        StructuredBodyTable table = lowerer.bodyTable();
        Optional<CompilerDiagnostic> controlFlow = ControlFlowValidator.validate(unit, table);
        if (controlFlow.isPresent()) {
            return new LoweringResult(null, null, List.of(controlFlow.get()));
        }
        return new LoweringResult(unit, table, List.of());
    }

    /**
     * The E7 call-machine lowering entry point (ISSUE-0236): the
     * full-program walk plus the statically-resolved D13/D15 call arms —
     * {@code CALL(DIRECT)}/{@code CALL(INDIRECT)}/{@code CALL(HOST)}/
     * {@code CALL(EXTERNAL)}, {@code ASYNC_START}+{@code AWAIT} (DEAL
     * bodies, async host functions, async externals, and
     * adapter-over-async), adapter creation at adapted
     * initializer/assignment positions with the D15 invocation cells,
     * one {@code EXTERNAL_ENTRY} or {@code CALLBACK_INVOKE} per exported
     * function, and the {@code ENTRY_INVOKE} delegation of
     * {@code main}: null.
     *
     * <p>The extra facts are all lowering-time: the callee-module route
     * facts (the {@code ExternalExecutionOwner} resolution),
     * the callee modules' recorded {@code EXTERNAL_ENTRY} op ids (the
     * caller-side {@code externalEntryRef} resolution), and the exported
     * function names the scenario invokes as callbacks. Runtime
     * selection of binding kind, boundary family, return-boundary owner,
     * or async source is ISSUE-0531's and fails closed here.</p>
     */
    public static FullProgramE7Result lowerModuleFullProgramE7(CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash, String capabilityRegistryHash,
            SemanticIdAllocator allocator, Map<ModuleId, ModuleRoute> calleeRoutes,
            Map<ModuleId, Map<String, OpId>> calleeExternalEntries,
            Set<String> callbackExports) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        Objects.requireNonNull(calleeRoutes, "calleeRoutes must not be null");
        Objects.requireNonNull(calleeExternalEntries, "calleeExternalEntries must not be null");
        Objects.requireNonNull(callbackExports, "callbackExports must not be null");
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                Map.of(), Map.of());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, module.ast().span(), true);
        lowerer.setModuleImports(module.imports());
        lowerer.setE7Facts(module.exports(), calleeRoutes, calleeExternalEntries,
            callbackExports);
        try {
            lowerer.seedIntrinsicBindings();
            lowerer.hoistModuleLevelAllocs(module.ast().statements());
            lowerer.statementWalk.walk(module.ast().statements(), true);
            lowerer.emitE7Terminals();
            lowerer.finalizeCellKinds();
        } catch (ConstructUnlowered unlowered) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                Map.of(), Map.of());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                Map.of(), Map.of());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                Map.of(), Map.of());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                Map.of(), Map.of());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(validation.get())), Map.of(), Map.of());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(chainShape.get())), Map.of(), Map.of());
        }
        StructuredBodyTable table = lowerer.bodyTable();
        Optional<CompilerDiagnostic> controlFlow = ControlFlowValidator.validate(unit, table);
        if (controlFlow.isPresent()) {
            return new FullProgramE7Result(new LoweringResult(null, null,
                List.of(controlFlow.get())), Map.of(), Map.of());
        }
        return new FullProgramE7Result(new LoweringResult(unit, table, List.of()),
            lowerer.recordedEntries(), lowerer.recordedCallbacks());
    }

    /**
     * A declaration import of the closure has no entry in the supplied
     * declaration surface: the seeds (and therefore the layouts the
     * class-literal arm resolves) would be silently incomplete, so the
     * project entry refuses the input (ISSUE-0634).
     */
    public static final String DECLARATION_SURFACE_INCOMPLETE =
        "DECLARATION_SURFACE_INCOMPLETE";

    /**
     * The declaration surface's per-module declaration kind disagrees with
     * the extern-C generated metadata: the class registration seeds would
     * take the wrong owner member, so the project entry refuses the input
     * (ISSUE-0634).
     */
    public static final String DECLARATION_KIND_MISMATCH =
        "DECLARATION_KIND_MISMATCH";

    /**
     * A closure module of the checked project carries no requirement
     * manifest or no interface-index entry: the unit's coverage rows and the
     * module's own interface facts would be silently absent, so the project
     * entry refuses the input (ISSUE-0634).
     */
    public static final String PROJECT_INPUT_INCOMPLETE =
        "PROJECT_INPUT_INCOMPLETE";

    /**
     * The one project lowering entry of a compilation (ISSUE-0634; design
     * sources {@code project-lowering-entry-and-registration-seeds}
     * D1/D2/D4/D8/D11/D12 and the project lowering, registration-seed,
     * namespace registration, and project validation gate contracts;
     * {@code luajit-jvm-single-lowering-production-cutover} C1/C4/C7/C10;
     * {@code semantic-ir-construct-coverage-cutover} K3/K12's lowering
     * context): it lowers the complete checked implementation closure in
     * dependency order, through exactly one
     * {@link SemanticIdAllocator} and exactly one session per module with
     * every arm active, and produces exactly one validated
     * {@link deal.semantic.ir.ExecutableLoweredProject} plus the
     * per-module production records, the class registration seeds, and the
     * namespace registrations — or the first E6005 and no project, no
     * tables, no registries, no seeds, and no namespace registrations.
     *
     * <p><b>Order of operations.</b> (1) the profile guard before any id
     * is allocated; (2) the declaration-fact agreement and the class
     * registration seeds (plus the intrinsic seeds the sessions carry)
     * before the first unit walk; (3) the namespace registrations created
     * before the first unit walk in dependency order and completed by each
     * unit's import arm; (4) per module in dependency order, one session
     * with the binding, closure, group, full-program call, and class arms
     * active and the pinned walk order of
     * {@link ModuleLowerer#lowerProjectModule}, followed by the composed
     * per-unit closed chain; (5) after the complete closure is lowered,
     * the project-form gate over the whole closure.</p>
     *
     * <p><b>One allocator, no partial result.</b> The allocator orders the
     * dependency-ordered closure once, so ids are issued once per
     * compilation in the pinned order (dependency order, then source
     * order, then role, then synthetic ordinal) and are globally unique
     * including the cross-unit {@code OpId} module tags. Every failure
     * returns the first E6005 with its module, capability, validator rule,
     * profile, IR version, and origin, and a result with no project, no
     * tables, no registries, no seeds, and no namespace registrations — no
     * retry and no per-module partial result escape the entry. Repeated
     * lowerings of the same input yield byte-identical project dumps.</p>
     *
     * <p><b>The cross-module facts of the one lowering.</b> The closure
     * modules' recorded {@code EXTERNAL_ENTRY} op ids accumulate in
     * dependency order inside the walk (the caller-side
     * {@code externalEntryRef} resolution), and every cross-module callee
     * of the closure is a {@code SHARED_BODY} external: no route plan, no
     * per-module route map, and no retained-ABI execution owner enter the
     * project lowering. The in-project shared-factory facts of this stage
     * are empty (the in-project imported-class resolution child realizes
     * them).</p>
     *
     * <p><b>Session seeds.</b> Each session receives the class
     * registration seeds as its layout-resolution context (after the
     * unit's own declared layouts; the seeds are never merged into
     * {@code unit.classLayouts}) and the compilation's declared conversion
     * intrinsics, and each unit's import arm completes the namespace
     * registrations created before the first walk.</p>
     *
     * @param invocation                 the release-owned compiler
     *                                   invocation (profile guard and
     *                                   capability-registry hash); non-null
     * @param checkedProject             the complete checked implementation
     *                                   closure in dependency order; non-null
     * @param interfaceIndex             the project interface index; non-null
     * @param requirementManifests       the per-module requirement manifests
     *                                   (the construct-coverage rows the
     *                                   units record); non-null
     * @param declarationSurface         the declaration surface covering
     *                                   every declaration import of the
     *                                   closure; non-null
     * @param declarationModuleIdentities the compilation's module-path
     *                                   classification keyed by module
     *                                   identity (the identity the seeds'
     *                                   {@code ClassId}s are projected
     *                                   through); non-null
     * @param externCModules             the validated generated metadata of
     *                                   every extern-C declaration module,
     *                                   keyed by module identity; non-null
     * @param builtinError               the compiler-owned builtin
     *                                   {@code Error} declaration; non-null
     * @param conversionIntrinsics       the compilation's declared
     *                                   conversion intrinsics (the closed
     *                                   {@link IntrinsicKind} set the seeds
     *                                   register); non-null
     * @param callbackExports            the exported function names the
     *                                   scenario invokes as callbacks (empty
     *                                   for production); non-null
     * @return the one project lowering outcome
     */
    public static ProjectLoweringResult lowerProject(
            CompilerInvocation invocation,
            CheckedProjectInput checkedProject,
            deal.semantic.ir.ProjectInterfaceIndex interfaceIndex,
            List<SemanticRequirementManifest> requirementManifests,
            HostDeclarationSurface declarationSurface,
            Map<ModuleId, CanonicalModuleIdentity> declarationModuleIdentities,
            Map<ModuleId, FfiGeneratedModule> externCModules,
            BuiltinErrorDeclaration builtinError,
            List<IntrinsicKind> conversionIntrinsics,
            Set<String> callbackExports) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(checkedProject, "checkedProject must not be null");
        Objects.requireNonNull(interfaceIndex, "interfaceIndex must not be null");
        Objects.requireNonNull(requirementManifests,
            "requirementManifests must not be null");
        Objects.requireNonNull(declarationSurface, "declarationSurface must not be null");
        Objects.requireNonNull(declarationModuleIdentities,
            "declarationModuleIdentities must not be null");
        Objects.requireNonNull(externCModules, "externCModules must not be null");
        Objects.requireNonNull(builtinError, "builtinError must not be null");
        Objects.requireNonNull(conversionIntrinsics,
            "conversionIntrinsics must not be null");
        Objects.requireNonNull(callbackExports, "callbackExports must not be null");

        // (1) The profile guard: before any id is allocated and before any
        // op is built. A non-DEAL_V1_2_INT32 invocation fails closed here.
        if (invocation.semanticProfile() != SemanticProfile.DEAL_V1_2_INT32) {
            return projectFailure(checkedProject.entryModule(),
                SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                invocation.semanticProfile(), "SemanticLowerer.lowerProject");
        }
        String interfaceHash = interfaceIndex.interfaceIndexDigest();
        String capabilityRegistryHash = invocation.capabilityRegistryHash();
        SemanticIrValidator.ComparisonFacts comparisonFacts =
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash);

        // (2) The declaration-fact agreement: every declaration import of
        // the closure is covered by the surface (a declaration module's
        // class literal would otherwise defer silently) and the surface's
        // declaration kind agrees with the extern-C generated metadata (the
        // seeds' owner member derives from exactly that pair).
        for (CheckedModuleInput module : checkedProject.modules()) {
            for (ResolvedImport importFact : module.imports()) {
                deal.semantic.ir.ExternalModuleInterface target =
                    interfaceIndex.modules().get(importFact.resolvedModuleId());
                if (target != null
                        && target.kind() == ExternalModuleKind.HOST
                        && !declarationSurface.modules()
                            .containsKey(importFact.resolvedModuleId())) {
                    return projectFailure(importFact.resolvedModuleId(),
                        SemanticCapability.FOUNDATION_VALUES,
                        DECLARATION_SURFACE_INCOMPLETE,
                        invocation.semanticProfile(),
                        "declaration import '" + importFact.modulePath()
                            + "' of module '" + module.moduleId().path()
                            + "' has no declaration-surface entry (the surface"
                            + " covers every declaration import of the closure)");
                }
            }
        }
        for (ModuleId declarationModule : declarationSurface.moduleIds()) {
            HostDeclarationSurface.DeclarationFacts facts =
                declarationSurface.require(declarationModule);
            boolean externC = externCModules.containsKey(declarationModule);
            if (externC
                    != (facts.kind()
                        == HostDeclarationSurface.DeclarationKind.EXTERN_C)) {
                return projectFailure(declarationModule,
                    SemanticCapability.CLASSES, DECLARATION_KIND_MISMATCH,
                    invocation.semanticProfile(),
                    "the declaration surface classifies '" + declarationModule.path()
                        + "' as " + facts.kind() + " but the extern-C generated"
                        + " metadata " + (externC ? "is present" : "is absent")
                        + " for it (the seeds' owner member derives from exactly"
                        + " this pair)");
            }
        }

        // (2) The class registration seeds, produced before the first unit
        // walk: one layout per declared class of every declaration module
        // plus the compiler-owned builtin Error entry.
        ClassRegistrationSeeds.Production seeds = ClassRegistrationSeeds.produce(
            declarationSurface, declarationModuleIdentities, externCModules,
            builtinError);
        if (seeds.hasErrors()) {
            return projectFailureResult(seeds.diagnostics());
        }

        // (3) The namespace registrations: created before the first unit
        // walk in dependency order (then first-import declaration order) and
        // completed by each unit's import arm.
        Map<ModuleId, ModuleImportKind> preRegistered = new LinkedHashMap<>();
        for (CheckedModuleInput module : checkedProject.modules()) {
            for (ResolvedImport importFact : module.imports()) {
                preRegistered.putIfAbsent(importFact.resolvedModuleId(),
                    ModuleLowerer.moduleImportKindOf(importFact));
            }
        }
        NamespaceRegistrations.Recorder namespaceRecorder =
            new NamespaceRegistrations.Recorder(preRegistered);

        // (4) The one closure walk in dependency order: one allocator, one
        // session per module with every arm active, and the composed
        // per-unit closed chain.
        List<ModuleId> closureOrder = new ArrayList<>();
        for (CheckedModuleInput module : checkedProject.modules()) {
            closureOrder.add(module.moduleId());
        }
        if (closureOrder.isEmpty()) {
            return projectFailure(checkedProject.entryModule(),
                SemanticCapability.FOUNDATION_VALUES, PROJECT_INPUT_INCOMPLETE,
                invocation.semanticProfile(),
                "the checked project carries no implementation module (the closure"
                    + " is the complete implementation closure of the compile)");
        }
        if (!closureOrder.contains(checkedProject.entryModule())) {
            return projectFailure(checkedProject.entryModule(),
                SemanticCapability.FOUNDATION_VALUES, PROJECT_INPUT_INCOMPLETE,
                invocation.semanticProfile(),
                "the entry module '" + checkedProject.entryModule().path()
                    + "' is not part of the dependency-ordered closure "
                    + closureOrder + " (the project admits only the complete"
                    + " closure with its entry module)");
        }
        SemanticIdAllocator allocator = SemanticIdAllocator.over(closureOrder);
        Map<ModuleId, ModuleRoute> closureRoutes = new LinkedHashMap<>();
        for (ModuleId module : closureOrder) {
            closureRoutes.put(module, ModuleRoute.SHARED);
        }

        Map<ModuleId, LoweredModuleUnit> units = new LinkedHashMap<>();
        Map<ModuleId, StructuredBodyTable> tables = new LinkedHashMap<>();
        Map<ModuleId, deal.semantic.ir.ClassFactoryRegistry> registries =
            new LinkedHashMap<>();
        Map<ModuleId, Map<String, OpId>> calleeExternalEntries = new LinkedHashMap<>();

        for (CheckedModuleInput module : checkedProject.modules()) {
            SemanticRequirementManifest manifest =
                manifestOf(requirementManifests, module.moduleId());
            if (manifest == null) {
                return projectFailure(module.moduleId(),
                    SemanticCapability.FOUNDATION_VALUES, PROJECT_INPUT_INCOMPLETE,
                    invocation.semanticProfile(),
                    "module '" + module.moduleId().path() + "' has no requirement"
                        + " manifest (every closure module carries exactly one"
                        + " manifest's construct-coverage rows)");
            }
            deal.semantic.ir.ExternalModuleInterface ownInterface =
                interfaceIndex.modules().get(module.moduleId());
            if (ownInterface == null) {
                return projectFailure(module.moduleId(),
                    SemanticCapability.FOUNDATION_VALUES, PROJECT_INPUT_INCOMPLETE,
                    invocation.semanticProfile(),
                    "module '" + module.moduleId().path() + "' has no interface-index"
                        + " entry (the index covers every module of the closure)");
            }
            LoweredProjectModule lowered = lowerProjectModule(module, manifest,
                interfaceHash, capabilityRegistryHash, allocator, closureRoutes,
                calleeExternalEntries, callbackExports, seeds.seeds(),
                conversionIntrinsics, ownInterface, comparisonFacts);
            if (lowered.hasErrors()) {
                return projectFailureResult(lowered.diagnostics());
            }
            Optional<CompilerDiagnostic> namespaceFailure =
                namespaceRecorder.record(lowered.unit());
            if (namespaceFailure.isPresent()) {
                return projectFailureResult(List.of(namespaceFailure.get()));
            }
            units.put(module.moduleId(), lowered.unit());
            tables.put(module.moduleId(), lowered.table());
            registries.put(module.moduleId(), lowered.registry());
            if (!lowered.externalEntries().isEmpty()) {
                calleeExternalEntries.put(module.moduleId(), lowered.externalEntries());
            }
        }

        // (5) The project-form gate over the complete closure.
        ExecutableLoweredProject project = new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32, interfaceIndex, units,
            checkedProject.entryModule());
        Optional<CompilerDiagnostic> projectGate = SemanticIrValidator.validate(
            project, comparisonFacts);
        if (projectGate.isPresent()) {
            return projectFailureResult(List.of(projectGate.get()));
        }
        NamespaceRegistrations.Assembly namespaceAssembly = namespaceRecorder.build();
        return new ProjectLoweringResult(project, tables, registries, seeds.seeds(),
            namespaceAssembly.registrations(), List.of());
    }

    /**
     * One module's lowering inside the one project walk (ISSUE-0634): the
     * session with every arm active under the assembled context, the
     * composed per-unit closed chain over the produced unit, and the
     * module's per-walk production records. Internal to
     * {@link #lowerProject} — no per-module result escapes the entry.
     */
    private static LoweredProjectModule lowerProjectModule(
            CheckedModuleInput module,
            SemanticRequirementManifest manifest,
            String interfaceHash,
            String capabilityRegistryHash,
            SemanticIdAllocator allocator,
            Map<ModuleId, ModuleRoute> closureRoutes,
            Map<ModuleId, Map<String, OpId>> calleeExternalEntries,
            Set<String> callbackExports,
            ClassRegistrationSeeds seeds,
            List<IntrinsicKind> conversionIntrinsics,
            deal.semantic.ir.ExternalModuleInterface ownInterface,
            SemanticIrValidator.ComparisonFacts comparisonFacts) {
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, false, false, false,
            module.ast().span(), true, true, ownInterface, Map.of());
        lowerer.setModuleImports(module.imports());
        lowerer.setRegistrationSeeds(seeds);
        lowerer.setDeclaredConversionIntrinsics(conversionIntrinsics);
        lowerer.setE7Facts(module.exports(), closureRoutes, calleeExternalEntries,
            callbackExports);
        try {
            lowerer.lowerProjectModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return LoweredProjectModule.failure(List.of(FailureContractRegistry.e6005(
                loweringFailureDetail(module.moduleId(), unlowered))));
        } catch (IntLiteralOutOfRange outOfRange) {
            return LoweredProjectModule.failure(List.of(FailureContractRegistry.e6005(
                loweringFailureDetail(module.moduleId(), outOfRange))));
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return LoweredProjectModule.failure(List.of(FailureContractRegistry.e6005(
                loweringFailureDetail(module.moduleId(), defect))));
        } catch (ComparisonSelectorLowering.Defect defect) {
            return LoweredProjectModule.failure(List.of(
                ComparisonSelectorLowering.e6005(module.moduleId(), defect)));
        } catch (ClassDefaultCapture capture) {
            return LoweredProjectModule.failure(List.of(FailureContractRegistry.e6005(
                loweringFailureDetail(module.moduleId(), capture))));
        } catch (RetainedAbiDeferred deferred) {
            return LoweredProjectModule.failure(List.of(FailureContractRegistry.e6005(
                loweringFailureDetail(module.moduleId(), deferred))));
        }
        LoweredModuleUnit unit = lowerer.buildUnit(manifest.constructCoverage(),
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        StructuredBodyTable table = lowerer.bodyTable();
        Optional<CompilerDiagnostic> unitChain = validateProjectUnit(unit, table,
            comparisonFacts, lowerer.pinnedWriteFacts(), lowerer.factoryRegistry(),
            lowerer.jsonDefaultChildren(), ownInterface, Map.of());
        if (unitChain.isPresent()) {
            return LoweredProjectModule.failure(List.of(unitChain.get()));
        }
        return new LoweredProjectModule(unit, table, lowerer.factoryRegistry(),
            lowerer.jsonDefaultChildren(), lowerer.recordedEntries(),
            lowerer.pinnedWriteFacts(), List.of());
    }

    /**
     * The composed per-unit closed chain of the project gate (ISSUE-0634;
     * design source {@code project-lowering-entry-and-registration-seeds}
     * D11 and the project validation gate contract): in order, the closed
     * 14 rules ({@link SemanticIrValidator#validate(LoweredModuleUnit,
     * SemanticIrValidator.ComparisonFacts)}), the address-chain protocol,
     * the control-flow validator, the bindings production validator over
     * the unified unit with the walk's pinned-write facts (including the
     * intrinsic-seed admission clauses), and the class-construction
     * validator with the module's interface entry and the in-project
     * factory facts. Returns empty on pass and exactly the first E6005 on
     * failure — the chain stops at the first failing rule, so a defective
     * unit never reaches a later validator.
     *
     * @param unit           the produced unit; non-null
     * @param table          the unit's block-membership table; non-null
     * @param facts          the comparison facts (interface digest, profile,
     *                       capability-registry hash); non-null
     * @param pinnedWrites   the walk's pinned-write binding facts; non-null
     * @param factories      the module's class-factory registry; non-null
     * @param jsonDefaults   the module's JSON default-child record; non-null
     * @param ownInterface   the module's own interface entry; non-null
     * @param sharedFactories the in-project factory facts by class
     *                       identity; non-null
     * @return empty on pass, otherwise the first E6005
     */
    public static Optional<CompilerDiagnostic> validateProjectUnit(
            LoweredModuleUnit unit,
            StructuredBodyTable table,
            SemanticIrValidator.ComparisonFacts facts,
            BindingsProductionValidator.PinnedWriteFacts pinnedWrites,
            deal.semantic.ir.ClassFactoryRegistry factories,
            deal.semantic.ir.JsonDefaultChildTable jsonDefaults,
            deal.semantic.ir.ExternalModuleInterface ownInterface,
            Map<ClassId, SharedFactoryFacts> sharedFactories) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(facts, "facts must not be null");
        Objects.requireNonNull(pinnedWrites, "pinnedWrites must not be null");
        Objects.requireNonNull(factories, "factories must not be null");
        Objects.requireNonNull(jsonDefaults, "jsonDefaults must not be null");
        Objects.requireNonNull(ownInterface, "ownInterface must not be null");
        Objects.requireNonNull(sharedFactories, "sharedFactories must not be null");
        Optional<CompilerDiagnostic> validation =
            SemanticIrValidator.validate(unit, facts);
        if (validation.isPresent()) {
            return validation;
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return chainShape;
        }
        Optional<CompilerDiagnostic> controlFlow =
            ControlFlowValidator.validate(unit, table);
        if (controlFlow.isPresent()) {
            return controlFlow;
        }
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(
            unit, table, pinnedWrites);
        if (bindings.isPresent()) {
            return bindings;
        }
        return ClassConstructionValidator.validate(unit, table, factories,
            jsonDefaults, ownInterface, sharedFactories);
    }

    /** The requirement manifest of one module, or {@code null} when absent. */
    private static SemanticRequirementManifest manifestOf(
            List<SemanticRequirementManifest> manifests, ModuleId moduleId) {
        for (SemanticRequirementManifest manifest : manifests) {
            if (manifest.moduleId().equals(moduleId)) {
                return manifest;
            }
        }
        return null;
    }

    /** The first E6005 of the project entry, with no project and no records. */
    private static ProjectLoweringResult projectFailure(ModuleId module,
            SemanticCapability capability, String rule, SemanticProfile profile,
            String origin) {
        return projectFailureResult(List.of(FailureContractRegistry.e6005(
            new LoweringFailureDetail(module.path(), capability, rule, profile,
                LoweredModuleUnit.FORMAT_VERSION,
                "SemanticLowerer.lowerProject " + rule + " (" + origin + ")"))));
    }

    /** The failure result carrying exactly the first E6005 and no records. */
    private static ProjectLoweringResult projectFailureResult(
            List<CompilerDiagnostic> diagnostics) {
        return new ProjectLoweringResult(null, Map.of(), Map.of(), null, null,
            List.copyOf(diagnostics));
    }

    /**
     * The one project lowering result (ISSUE-0634; design source
     * {@code project-lowering-entry-and-registration-seeds} D1 and the
     * project lowering contract): exactly one validated
     * {@link ExecutableLoweredProject} with its per-module block-membership
     * tables and class-factory registries, the project-level class
     * registration seeds, and the project-level namespace registrations;
     * or, on the first E6005 anywhere in the closure walk or the project
     * gate, no project, no tables, no registries, no seeds, and no
     * namespace registrations.
     *
     * @param project     the one executable lowered project; null exactly
     *                    on failure
     * @param tables      the per-module block-membership tables (empty on
     *                    failure); non-null
     * @param registries  the per-module class-factory registries (empty on
     *                    failure); non-null
     * @param seeds       the project-level class registration seeds; null
     *                    exactly on failure
     * @param namespaces  the project-level namespace registrations; null
     *                    exactly on failure
     * @param diagnostics the E6005 diagnostics (empty on success); non-null
     */
    public record ProjectLoweringResult(
            ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, deal.semantic.ir.ClassFactoryRegistry> registries,
            ClassRegistrationSeeds seeds,
            NamespaceRegistrations namespaces,
            List<CompilerDiagnostic> diagnostics) {

        public ProjectLoweringResult {
            Objects.requireNonNull(tables, "tables must not be null");
            Objects.requireNonNull(registries, "registries must not be null");
            Objects.requireNonNull(diagnostics, "diagnostics must not be null");
            diagnostics = List.copyOf(diagnostics);
            if (project != null && !diagnostics.isEmpty()) {
                throw new IllegalArgumentException(
                    "a successful project lowering carries no diagnostics");
            }
            if (project == null
                    && (diagnostics.isEmpty() || !tables.isEmpty()
                        || !registries.isEmpty() || seeds != null
                        || namespaces != null)) {
                throw new IllegalArgumentException(
                    "a failed project lowering carries exactly the first E6005 and"
                        + " no project, no tables, no registries, no seeds, and no"
                        + " namespace registrations");
            }
            tables = Map.copyOf(tables);
            registries = Map.copyOf(registries);
        }

        /** Whether the lowering failed (no project was produced). */
        public boolean hasErrors() {
            return !diagnostics.isEmpty();
        }

        /** The block-membership table of one module, or {@code null}. */
        public StructuredBodyTable tableOf(ModuleId moduleId) {
            return tables.get(Objects.requireNonNull(moduleId,
                "moduleId must not be null"));
        }

        /** The class-factory registry of one module, or {@code null}. */
        public deal.semantic.ir.ClassFactoryRegistry registryOf(ModuleId moduleId) {
            return registries.get(Objects.requireNonNull(moduleId,
                "moduleId must not be null"));
        }
    }

    /**
     * One module's per-walk production records inside the one project
     * lowering (ISSUE-0634). Internal to the closure walk: the records are
     * collected into the project result and no per-module result escapes
     * the entry.
     *
     * @param unit            the produced unit; null exactly on failure
     * @param table           the unit's block-membership table; null on
     *                        failure
     * @param registry        the module's class-factory registry; null on
     *                        failure
     * @param jsonDefaults    the module's JSON default-child record; null
     *                        on failure
     * @param externalEntries the module's recorded {@code EXTERNAL_ENTRY}
     *                        op ids by export name (empty on failure)
     * @param pinnedWrites    the walk's pinned-write binding facts
     * @param diagnostics     the E6005 diagnostics (empty on success)
     */
    private record LoweredProjectModule(
            LoweredModuleUnit unit,
            StructuredBodyTable table,
            deal.semantic.ir.ClassFactoryRegistry registry,
            deal.semantic.ir.JsonDefaultChildTable jsonDefaults,
            Map<String, OpId> externalEntries,
            BindingsProductionValidator.PinnedWriteFacts pinnedWrites,
            List<CompilerDiagnostic> diagnostics) {

        LoweredProjectModule {
            diagnostics = List.copyOf(diagnostics);
        }

        boolean hasErrors() {
            return !diagnostics.isEmpty();
        }

        static LoweredProjectModule failure(List<CompilerDiagnostic> diagnostics) {
            return new LoweredProjectModule(null, null, null, null, Map.of(),
                BindingsProductionValidator.PinnedWriteFacts.empty(), diagnostics);
        }
    }

    /**
     * The closure child's public lowering entry point (ISSUE-0445
     * sequencing item 2): lowers one checked implementation module
     * through the binding walk plus the closure arms — {@code
     * CLOSURE_NEW}/{@code LoweredFunction} for every function expression
     * and every size-1 non-group function declaration, capture-by-binding
     * resolution at the detaching op's creation site recursively along
     * the detaching chain, the closure-capture arm of the B2
     * {@code SHARED_CELL} cell-kind upgrade, and the {@code LoweredBody}
     * {@code functionBindings} registrations through the registry child's
     * registration seam — and produces the validated unit plus the
     * binding facts (final derived cell kinds) and the closure capture
     * facts.
     *
     * <p>The walk consumes the binding-core walk's statement and
     * value-expression seams (never re-implementing them); function
     * bodies lower through the same arms with capture collection active
     * during body walks (B9 R2/R3 as the resolution model: a reference
     * inside a detached body resolves the innermost frame entry — the
     * function's own scope chain first, outer frames as captures — and
     * the capture's producing allocation is the dominant incarnation at
     * the creation site). Function-typed {@code BINDING_LOAD}s preserve
     * allocation identity statically: a load of a function-typed binding
     * publishes the producing allocation identity its cell currently
     * holds (the pre-allocated identity of a hoisted module-level
     * function, the tracked identity of an initializer/store) so the
     * schema-level {@code R-FUNCTION-BINDING} rule holds; a function-typed
     * load whose cell value identity is not statically known (parameters,
     * catch bindings, iteration bindings) fails closed as the registry
     * child's resolution (B5).</p>
     *
     * <p>This entry point is driven by the closure tests; no production
     * route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the binding and closure facts, or
     *         the first E6005 with the partial facts on failure
     */
    public static ClosureCoreResult lowerModuleClosureCore(CheckedModuleInput module,
                                                           SemanticProfile profile,
                                                           Map<ConstructKind,
                                                               List<SemanticOpKind>>
                                                               constructCoverage,
                                                           String interfaceHash,
                                                           String capabilityRegistryHash,
                                                           SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModuleBindingCore — a
        // non-DEAL_V1_2_INT32 lowering request produces no unit and no
        // partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty(), List.of());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, module.ast().span());
        try {
            lowerer.lowerBindingModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts(), lowerer.closureFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts(), lowerer.closureFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts(), lowerer.closureFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts(), lowerer.closureFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                lowerer.bindingFacts(), lowerer.closureFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new ClosureCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                lowerer.bindingFacts(), lowerer.closureFacts());
        }
        return new ClosureCoreResult(new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts(), lowerer.closureFacts());
    }

    /**
     * The recursive-group child's public lowering entry point (ISSUE-0446
     * sequencing item 3): lowers one checked implementation module
     * through the binding walk plus the closure arms plus the group arms
     * — per-scope SCC partition over function declarations (name
     * references in bodies), one {@code RECURSIVE_GROUP_INIT} op per
     * size>=2 SCC with the declaration-ordered member
     * {@code {bindings, functions}} payload and pre-assigned unique
     * member allocation identities (the keys the registry's one
     * {@code LoweredBody} per member consumes, B4/B5), module-init-top
     * placement for module-level groups and first-member-position
     * placement for nested-scope groups, member cells
     * {@code SHARED_CELL} by construction with no separate
     * {@code BINDING_ALLOC}/{@code BINDING_INIT} (B1/B2), member bodies
     * lowering like any function body with captures per the closure
     * contract (B3), and size-1 SCCs — self-recursive declarations
     * included — lowering as {@code CLOSURE_NEW} + {@code BINDING_INIT}
     * at the declaration position (the closure child's arm) — and
     * produces the validated unit plus the binding facts, the closure
     * capture facts, and the group member facts.
     *
     * <p>Group-core mode implies closure-core and binding-core mode: the
     * walk consumes the binding walk's statement and value-expression
     * seams and the closure child's buffered detached-body walk with
     * capture collection. The group op has no result slot (the member
     * bindings are the observable effect); member {@code BINDING_LOAD}s
     * resolve to the group op as the producing allocation at generation
     * 0 and publish the member's pre-assigned allocation identity, so
     * the schema-level {@code R-FUNCTION-BINDING} rule holds by
     * construction for the one {@code LoweredBody} registration per
     * member. Group execution (phase 1 identity allocation, phase 2
     * atomic publication) is realized by the oracle/emitters — this
     * child produces the op, the member identities, and the payload;
     * {@code GROUP_SHAPE} validation (the validation child) and member
     * invocation (E7) stay out of this child's window.</p>
     *
     * <p>This entry point is driven by the recursive-group tests; no
     * production route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the binding, closure, and group
     *         facts, or the first E6005 with the partial facts on failure
     */
    public static GroupCoreResult lowerModuleGroupCore(CheckedModuleInput module,
                                                       SemanticProfile profile,
                                                       Map<ConstructKind,
                                                           List<SemanticOpKind>>
                                                           constructCoverage,
                                                       String interfaceHash,
                                                       String capabilityRegistryHash,
                                                       SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModuleClosureCore — a
        // non-DEAL_V1_2_INT32 lowering request produces no unit and no
        // partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty(), List.of(), List.of());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, module.ast().span());
        try {
            lowerer.lowerGroupModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new GroupCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
        }
        return new GroupCoreResult(new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts());
    }

    /**
     * The immutability-proof child's public lowering entry point
     * (ISSUE-0448 sequencing item 5): lowers one checked implementation
     * module through the group-core walk — the binding walk plus the
     * closure arms plus the group arms, the same walk the registry
     * child's {@code functionBindings} registrations populate (B5) —
     * with the conservative assignment analysis active on top of it, and
     * produces the validated unit plus the binding facts, the closure
     * capture facts, the group member facts, and the derived
     * {@code BindingImmutabilityProof} fact surface (B7).
     *
     * <p><b>Recording.</b> Every variable assignment the walk lowers
     * resolves to its dominant incarnation through the walk's own
     * environment and defeats exactly that incarnation's proof
     * (conservative: any assignment in the enclosing scope after the
     * declaration, regardless of its position relative to an adaptation
     * site — the for-let update defeats the counter generation 0, the
     * per-iteration generation 1 keeps its proof; parameters are
     * defeated by any body assignment; function names by any assignment
     * in the module; the {@code int}/{@code number} intrinsic bindings
     * are always proven, B7). Proofs derive over the binding-core
     * incarnation map after the walk — one
     * {@link BindingImmutabilityProof} per {@code {binding,
     * generation}} of the dominant incarnation at the site; the records
     * are the closed shape the shape-map child copies into
     * {@code FUNCTION_ADAPT} payloads. The analysis consumes checker
     * facts only — resolved assignments, declaration/parameter facts,
     * intrinsic-binding facts — never target, route, or emitter
     * knowledge; narrowing (NullNarrowing) never enters (B3).</p>
     *
     * <p>This entry point is driven by the proof tests; no production
     * route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched, and the binding/closure/group
     * entry points keep their exact shapes.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the binding, closure, group, and
     *         immutability-proof facts, or the first E6005 with the
     *         partial facts on failure
     */
    public static ImmutabilityCoreResult lowerModuleImmutabilityCore(
            CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash,
            String capabilityRegistryHash,
            SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModuleGroupCore — a
        // non-DEAL_V1_2_INT32 lowering request produces no unit and no
        // partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty(), List.of(), List.of(),
                BindingImmutabilityAnalysis.BindingImmutabilityFacts.empty());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, true, module.ast().span());
        try {
            lowerer.lowerGroupModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new ImmutabilityCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts());
        }
        return new ImmutabilityCoreResult(
            new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
            lowerer.proofFacts());
    }

    /**
     * The creation-rule child's public lowering entry point (ISSUE-0449
     * sequencing item 6): lowers one checked implementation module
     * through the binding walk plus the closure arms plus the group
     * arms plus the proof analysis plus the closed creation-rule
     * classification (B6) — for every function-typed value flow the
     * walk classifies the position by checker facts
     * ({@code CheckResult.typeMap}, {@code Types.equals} /
     * {@code Types.isAssignable}) before choosing any shape, exactly
     * per the closed rule: exact-signature initializer/assignment
     * positions store the value directly with no {@code FUNCTION_ADAPT}
     * (the direct-store flow is this child's production);
     * assignable-but-not-exact positions classify to exactly one
     * adaptation candidate with the derived source signature (the
     * source expression's checked type) and target signature (the
     * declared binding signature), the recorded proof fact for the
     * shape-map child (B7), the prepared wiring point (the adapted
     * position's own {@code VARIABLE_DECLARATION}/
     * {@code VARIABLE_ASSIGNMENT} boundary chain — B9's creation-wiring
     * target), and the producer facts the registry child's
     * host/external materialization seam supplies; non-assignable
     * positions record the {@code FUNCTION_SIGNATURE} E8010 failure
     * expectation at the position's own boundary (the executed check is
     * E4's machinery); every typed boundary position — parameter,
     * return, host/external/callback parameter/return, array/table/
     * class element, JSON, and every other {@link BoundaryKind} — never
     * adapts (the classifier admits no adaptation arm for any position
     * other than {@code VARIABLE_DECLARATION}/
     * {@code VARIABLE_ASSIGNMENT}, and the walk's direct value flow
     * into the position's boundary slot is the wiring E4's boundary
     * producer consumes).
     *
     * <p><b>Zero emission.</b> The produced unit contains zero
     * {@code FUNCTION_ADAPT} ops — mode selection, payload construction,
     * and emission are the shape-map child's obligations, so every
     * emitted adapter carries its closed-map mode from birth — and the
     * classification changes no emitted op: the same walk's unit dump
     * is byte-identical to the proof child's for the same checked
     * module. Boundary-op production and execution stay E4's; all
     * invocation phases stay E7's.</p>
     *
     * <p>This entry point is driven by the creation-rule tests; no
     * production route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the binding, closure, group,
     *         proof, and creation-rule classification facts, or the
     *         first E6005 with the partial facts on failure
     */
    public static CreationRuleCoreResult lowerModuleCreationRuleCore(
            CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash,
            String capabilityRegistryHash,
            SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModuleImmutabilityCore — a
        // non-DEAL_V1_2_INT32 lowering request produces no unit and no
        // partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty(), List.of(), List.of(),
                BindingImmutabilityAnalysis.BindingImmutabilityFacts.empty(),
                AdapterCreationRule.CreationRuleFacts.empty());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, true, true, module.ast().span());
        try {
            lowerer.lowerGroupModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new CreationRuleCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts());
        }
        return new CreationRuleCoreResult(
            new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
            lowerer.proofFacts(), lowerer.creationRuleFacts());
    }

    /**
     * The shape-map child's public lowering entry point (ISSUE-0450
     * sequencing item 7): lowers one checked implementation module
     * through the group-core walk with the creation-rule
     * classification and the shape-map production active — every
     * {@code ADAPT}-classified position emits exactly one
     * {@code FUNCTION_ADAPT} op carrying its closed-map mode and
     * per-mode payload from birth (B7/B8), produced before the
     * position's boundary and wired as the direct input of exactly the
     * adapted position's own
     * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT} boundary
     * chain (an inferred declaration's result feeds its
     * {@code BINDING_INIT} directly — B9's creation-wiring rule),
     * with a fresh adapter allocation identity per creation registered
     * as an {@code AdapterBinding} through the registry child's seam
     * (B5), zero {@code BOUNDARY} ops emitted by the adapter (the
     * adapter adds no second boundary; the N target-signature
     * parameter-boundary checks belong to the invoking op, E7), and the
     * B2 cell-kind derivation completed over the union of the closure
     * child's capture references and this child's two remaining arms
     * (every {@code REEVALUATE_THUNK} {@code capturedBindings} entry
     * and every {@code FUNCTION_ADAPT(SHARED_CELL)} {@code SharedCell}
     * source reference) before the walk's finalization re-derives every
     * {@code BINDING_ALLOC} payload.
     *
     * <p>The walk consumes the expression-lowering seam for the source
     * ops themselves (the values/calls epics' producers lower
     * call-result, member-read, conditional, and conversion sources;
     * this child's thunk builder wraps the already-lowered ops in a
     * fresh {@link BlockId} — zero evaluation at creation). Source-level
     * end-to-end lowering of those positions completes through the
     * declared consumed seams; this child's own tests construct those
     * source ops at the IR level over the pinned
     * {@code deal.semantic-ir/1} schema. No invocation execution is
     * built or verified here (generation-checked loads, thunk
     * re-execution with {@code ADAPTER_THUNK_STEP} children,
     * source-signature checks, N-argument projection with trailing
     * drop, and the per-source-kind single return boundary are E7's).
     * This entry point is driven by the shape-map tests; no production
     * route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched.
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the binding, closure, group,
     *         proof, creation-rule classification, and shape-map
     *         emission facts, or the first E6005 with the partial facts
     *         on failure
     */
    public static ShapeMapCoreResult lowerModuleShapeMapCore(
            CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash,
            String capabilityRegistryHash,
            SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModuleCreationRuleCore — a
        // non-DEAL_V1_2_INT32 lowering request produces no unit and no
        // partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty(), List.of(), List.of(),
                BindingImmutabilityAnalysis.BindingImmutabilityFacts.empty(),
                AdapterCreationRule.CreationRuleFacts.empty(), ShapeMapFacts.empty());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, true, true, true,
            module.ast().span());
        try {
            lowerer.lowerGroupModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new ShapeMapCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        return new ShapeMapCoreResult(
            new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
            lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
    }

    /**
     * The validation child's public lowering entry point (ISSUE-0451
     * sequencing item 8): lowers one checked implementation module
     * through the complete shape-map walk (binding-core, closure,
     * group, proof, creation-rule, and shape-map production active —
     * the same walk {@link #lowerModuleShapeMapCore} drives) and
     * additionally runs the production-time validation stack over the
     * produced unit plus its block-membership table: the closed
     * 14-condition schema validator (unchanged, both surfaces), the
     * address-chain protocol (A-D1), the control-flow validator
     * (C-D2 — the block-tree/dominance/exits Basis whose structured
     * edges and intra-{@code LOOP} sequencing the B9 rules consume),
     * and the B9 rule set of {@link BindingsProductionValidator}
     * ({@code GROUP_SHAPE}, {@code CAPTURE_RESOLUTION},
     * {@code BINDING_GENERATION_RESOLUTION}, {@code BINDING_INIT_ONCE},
     * {@code INIT_DOMINATES_LOAD}, {@code ADAPTER_PAIR},
     * {@code ADAPTER_SOURCE_SHAPE}, {@code REGISTRY_ONE_TO_ONE},
     * {@code NO_ADAPTER_AT_BOUNDARY}) over the one uniform resolution
     * context (R1-R4). The first E6005 of any production-time check is
     * the returned diagnostic; a passing unit is byte-identical across
     * repeated lowering of the same checked module (D10).
     *
     * <p>The pinned positive shapes validate (size-1 self-recursion,
     * forward module-function body references, group-member body
     * loads, parameter/catch/{@code FOR_EACH} entry-transfer captures,
     * nested size-1 self-recursion, the doubly-nested capture of
     * {@code nested-closure-mutation.deal}, structured child-block
     * loads of ancestor bindings, thunk-block captures of closures
     * created inside thunks, the for-let counter's generation-0
     * condition/update/body-top references under the intra-{@code
     * LOOP} sequencing, default-block module-level references,
     * VALUE-over-proof loads, and the store-to-pre-init shape
     * {@code let x: int = (x = 1);}); the pinned negatives reject with
     * E6005 naming the rule ({@code let x: int = x;},
     * {@code let x: int = g(() => x);}, stale generations, zero or
     * multiple producing allocations, free references outside
     * captures, group-shape violations, adapter-pair violations,
     * adapter-source-shape violations, registry one-to-one
     * violations, and adapter results wired into non-position
     * boundaries). This entry point is driven by the validation tests;
     * no production route change — retained/public compilation paths
     * and {@link #lowerModule} are untouched, and the binding/closure/
     * group/proof/creation-rule/shape-map entry points keep their
     * exact shapes.
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the B9-validated unit with the complete fact surfaces,
     *         or the first E6005 with the partial facts on failure
     */
    public static ValidationCoreResult lowerModuleValidationCore(
            CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash,
            String capabilityRegistryHash,
            SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        // I3 profile guard: identical to lowerModuleShapeMapCore — a
        // non-DEAL_V1_2_INT32 lowering request produces no unit and no
        // partial session state.
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                BindingCoreFacts.empty(), List.of(), List.of(),
                BindingImmutabilityAnalysis.BindingImmutabilityFacts.empty(),
                AdapterCreationRule.CreationRuleFacts.empty(), ShapeMapFacts.empty());
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, true, true, true,
            module.ast().span());
        try {
            lowerer.lowerGroupModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        } catch (IntLiteralOutOfRange outOfRange) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E6_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        Optional<CompilerDiagnostic> controlFlow =
            ControlFlowValidator.validate(unit, lowerer.bodyTable());
        if (controlFlow.isPresent()) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(controlFlow.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        Optional<CompilerDiagnostic> bindings =
            BindingsProductionValidator.validate(unit, lowerer.bodyTable(),
                lowerer.pinnedWriteFacts());
        if (bindings.isPresent()) {
            return new ValidationCoreResult(new LoweringResult(null, null,
                List.of(bindings.get())),
                lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
                lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
        }
        return new ValidationCoreResult(
            new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.bindingFacts(), lowerer.closureFacts(), lowerer.groupFacts(),
            lowerer.proofFacts(), lowerer.creationRuleFacts(), lowerer.shapeMapFacts());
    }

    /**
     * The class-declaration child's public lowering entry point
     * (ISSUE-0511, sequencing item 1): lowers one checked implementation
     * module through the group walk plus the class-declaration arms —
     * one {@link deal.semantic.ir.ClassLayout} per declared class in
     * declaration order keyed by the checker-resolved
     * {@link ClassId} (field descriptors produced through the single
     * {@link DescriptorService} producer, {@code required} from the
     * checker's non-optional field fact, {@code defaultOwner LOCAL} —
     * default expressions are never part of a layout), one detached
     * {@code CLASS_DEFAULT} op per defaulted field whose own default
     * block carries the lowered default expression (only the default
     * blocks enter the block-membership table; each {@code CLASS_DEFAULT}
     * op is a member of exactly its own default block; the block's
     * final producing op publishes the {@code CLASS_DEFAULT} op's
     * result identity — a function-typed default's result is the
     * closure identity of a function-literal default or the statically
     * tracked function identity of a binding-referenced default, each
     * already carrying its {@code FunctionExecutionBinding};
     * module-level bindings resolve through the module-init block and
     * an enclosing-region free reference — direct or through a nested
     * closure's capture — fails E6005
     * {@code CLASS_DEFAULT_CAPTURE}), and one detached static
     * {@code CLASS_FACTORY} op per exported class registered under the
     * pre-allocated {@code ClassInterface.constructionEntry} id in the
     * produced {@link deal.semantic.ir.ClassFactoryRegistry} (policy
     * {@code CLASS_CONSTRUCTION}, zero boundary children, zero return
     * boundaries, never part of the module-init flow). Non-exported
     * classes get a layout but never a factory and never a
     * {@code ClassFactoryId}.
     *
     * <p>The default-block walk routes class-typed object literals of
     * locally declared classes through the {@code CLASS_NEW} arm (K-D4's
     * closed LOCAL payload shape — provided values in literal order,
     * {@code classDefaultOpIds} for omitted required-present defaulted
     * fields in declaration order, field boundaries in declaration order with the
     * pinned input wiring, {@code CLASS_CONSTRUCTION}, tag-last result) —
     * the same arm any class-typed literal of the walk uses. A literal of
     * an imported class with the owner's shared-factory facts lowers
     * {@code SHARED_FACTORY} (ISSUE-0514, K-D4/K-D5:
     * {@code classFactoryRef} = the interface's {@code constructionEntry},
     * empty {@code classDefaultOpIds}, {@code CLASS_DEFAULT_FIELD}
     * boundaries wired to the owner {@code CLASS_FACTORY} op's result
     * {@code ValueId}); a literal of an imported class without facts
     * defers to E10 ({@code RETAINED_ABI_DEFERRED}, never silently
     * emitted).</p>
     *
     * <p>The field-operation arms (ISSUE-0513, K-D6/K-D7) extend the same
     * window: class member reads lower to {@code FIELD_READ} with the
     * {@code UNTYPED_CLASS_INPUT} + {@code OPTIONAL_FIELD_READ} boundary
     * children (the cross-module nullable read lowers the receiver as
     * checked), class-field assignments/deletes lower the closed
     * {@code CLASS_FIELD} address chains with the commit-op boundary
     * children ({@code UNTYPED_CLASS_INPUT} + {@code CLASS_FIELD_ASSIGNMENT}
     * on {@code FIELD_WRITE}, {@code UNTYPED_CLASS_INPUT} on
     * {@code FIELD_DELETE}), {@code has(obj.field)} lowers to
     * {@code HAS_FIELD}, and the class window's expression statements audit
     * the dropped committed value through {@code DISCARD}.</p>
     *
     * <p>The produced unit passes the closed validator, the production-time
     * address-chain protocol, the control-flow validator (the factory is
     * detached per the five-module-level-kind rule), and the B9
     * bindings production validator, and the class-construction validator
 * (ISSUE-0516, K-D11 — factory and construction coherence,
 * field-operation shapes, default-block admission, and nested-jsonable
 * layout resolution). The unit's
     * {@code constructCoverage} rows are recorded verbatim from the
     * caller-supplied rows; the {@code CLASS_DECLARATION} row is satisfied
     * through the produced {@code CLASS_DEFAULT}/{@code CLASS_FACTORY}
     * ops for defaulted/exported shapes and through the produced layout
     * record for the layout-only shape (the validator's row-extension
     * admission).</p>
     *
     * <p>This entry point is driven by the class-declaration,
     * class-construction, and field-operation tests; no
     * production route change — retained/public compilation paths and
     * {@link #lowerModule} are untouched.</p>
     *
     * @param module                the checked implementation module; non-null
     * @param profile               the invocation's semantic profile
     *                              (I3 guard: only
     *                              {@code DEAL_V1_2_INT32} is lowered);
     *                              non-null
     * @param constructCoverage     the manifest's reachable-construct rows
     *                              recorded at lowering start (S1); non-null
     * @param interfaceHash         the interface index digest the unit is
     *                              checked against (R-PROFILE); non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                              digest (R-PROFILE); non-null
     * @param ownInterface          the module's own interface index entry
     *                              (the pre-allocated
     *                              {@code constructionEntry} ids of the
     *                              exported classes, K-D2); non-null
     * @param allocator             the project's semantic-id allocator in
     *                              dependency order; non-null
     * @return the validated unit with the factory registry, or the first
     *         E6005 on failure
     */
    public static ClassDeclarationCoreResult lowerModuleClassCore(
            CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash,
            String capabilityRegistryHash,
            deal.semantic.ir.ExternalModuleInterface ownInterface,
            SemanticIdAllocator allocator) {
        return lowerModuleClassCore(module, profile, constructCoverage, interfaceHash,
            capabilityRegistryHash, ownInterface, Map.of(), allocator);
    }

    /**
     * The shared-factory seam of the class walk (ISSUE-0514,
     * class-construction-jsonable-operations K-D2/K-D4/K-D5): the
     * full-fact overload of {@link #lowerModuleClassCore} receiving the
     * imported-construction context — one {@link SharedFactoryFacts} per
     * imported class (the owner's factory facts: the interface's
     * pre-allocated {@code constructionEntry} {@link
     * deal.semantic.ir.ClassFactoryId}, the owner
     * {@link deal.semantic.ir.ClassFactoryRegistry} binding's
     * {@code CLASS_FACTORY} op id, and the factory op's result
     * {@link ValueId}, plus the owner unit's {@link
     * deal.semantic.ir.ClassLayout} record and the interface entry) — so
     * a class-typed literal of an imported class emits its
     * {@code CLASS_NEW} with {@code defaultOwner: SHARED_FACTORY},
     * {@code classFactoryRef} = the interface's {@code constructionEntry},
     * empty {@code classDefaultOpIds}, and the {@code CLASS_DEFAULT_FIELD}
     * boundaries wired to the owner factory op's result {@code ValueId}
     * (the K-D4 cross-unit D4-global reference). The reference is emitted
     * deterministically (byte-identical repeats) and is resolvable by the
     * executor through the layout-resolution context (the unit's
     * {@code classLayouts} plus the interface facts). A literal of an
     * imported class without facts — an owner not on the shared route —
     * defers to E10 (E6005 {@code RETAINED_ABI_DEFERRED}, never a silent
     * {@code SHARED_FACTORY} emission); same-module literals stay LOCAL.
     *
     * @param sharedFactories the imported-construction facts by
     *                        {@link ClassId} (empty for a module that
     *                        constructs no imported classes); non-null
     */
    public static ClassDeclarationCoreResult lowerModuleClassCore(
            CheckedModuleInput module,
            SemanticProfile profile,
            Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
            String interfaceHash,
            String capabilityRegistryHash,
            deal.semantic.ir.ExternalModuleInterface ownInterface,
            Map<ClassId, SharedFactoryFacts> sharedFactories,
            SemanticIdAllocator allocator) {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(profile, "profile must not be null");
        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        Objects.requireNonNull(ownInterface, "ownInterface must not be null");
        Objects.requireNonNull(sharedFactories, "sharedFactories must not be null");
        Objects.requireNonNull(allocator, "allocator must not be null");
        if (profile != SemanticProfile.DEAL_V1_2_INT32) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    new LoweringFailureDetail(module.moduleId().path(),
                        SemanticCapability.FOUNDATION_VALUES, LOWER_LEGACY_PROFILE_REJECTED,
                        profile, LoweredModuleUnit.FORMAT_VERSION, "SemanticLowerer")))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        ModuleLowerer lowerer = new ModuleLowerer(module.moduleId(), module.sourceId(),
            module.checks(), allocator, true, true, true, false, false, false,
            module.ast().span(), false, true, ownInterface, sharedFactories);
        lowerer.setModuleImports(module.imports());
        try {
            lowerer.lowerGroupModule(module.ast().statements());
        } catch (ConstructUnlowered unlowered) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), unlowered)))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        } catch (IntLiteralOutOfRange outOfRange) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), outOfRange)))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        } catch (ContainerPayloadDescriptors.Defect defect) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), defect)))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        } catch (ComparisonSelectorLowering.Defect defect) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(ComparisonSelectorLowering.e6005(module.moduleId(), defect))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        } catch (ClassDefaultCapture capture) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), capture)))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        } catch (RetainedAbiDeferred deferred) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(FailureContractRegistry.e6005(
                    loweringFailureDetail(module.moduleId(), deferred)))),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        LoweredModuleUnit unit = lowerer.buildUnit(constructCoverage,
            module.imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            interfaceHash, capabilityRegistryHash,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(interfaceHash,
                SemanticProfile.DEAL_V1_2_INT32, capabilityRegistryHash));
        if (validation.isPresent()) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(validation.get())),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        Optional<CompilerDiagnostic> chainShape = AddressChainProtocol.validate(unit);
        if (chainShape.isPresent()) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(chainShape.get())),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        Optional<CompilerDiagnostic> controlFlow =
            ControlFlowValidator.validate(unit, lowerer.bodyTable());
        if (controlFlow.isPresent()) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(controlFlow.get())),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        Optional<CompilerDiagnostic> bindings =
            BindingsProductionValidator.validate(unit, lowerer.bodyTable(),
                lowerer.pinnedWriteFacts());
        if (bindings.isPresent()) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(bindings.get())),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        // ISSUE-0516 production-time check (K-D11): the produced class
        // constructs must pass the class-construction validator — factory
        // and construction coherence, field-operation shapes, default-block
        // admission, and nested-jsonable layout resolution; the first
        // violation is the returned E6005 (FACTORY_COHERENCE |
        // CONSTRUCTION_COHERENCE | FIELD_OPERATION_SHAPE |
        // DEFAULT_BLOCK_ADMISSION | JSON_LAYOUT_COHERENCE).
        Optional<CompilerDiagnostic> construction =
            ClassConstructionValidator.validate(unit, lowerer.bodyTable(),
                lowerer.factoryRegistry(), lowerer.jsonDefaultChildren(),
                ownInterface, sharedFactories);
        if (construction.isPresent()) {
            return new ClassDeclarationCoreResult(new LoweringResult(null, null,
                List.of(construction.get())),
                new deal.semantic.ir.ClassFactoryRegistry(Map.of()),
                new deal.semantic.ir.JsonDefaultChildTable(Map.of()));
        }
        return new ClassDeclarationCoreResult(
            new LoweringResult(unit, lowerer.bodyTable(), List.of()),
            lowerer.factoryRegistry(),
            lowerer.jsonDefaultChildren());
    }

    // =========================================================================
    // The per-module lowering session (the arms)
    // =========================================================================

    /**
     * The per-module lowering session holding the D1 arms: one session
     * per module lowering, deterministic and stateless apart from its
     * pinned inputs. It consults the {@link CheckResult} (checked types
     * and the root symbol table) only as copied facts while lowering —
     * a produced unit carries no AST node, {@code SymbolTable},
     * {@code CheckResult}, or identity-keyed map (D4).
     *
     * <p>The session emits operations in the pinned order — element prior
     * steps in source order, then the consuming op, then its boundary
     * children in source order; the iterable's prior steps, then the
     * {@code FOR_EACH} op, then the body ops; a structure op, then its
     * child blocks in payload order ({@code LOOP}: init, body, update;
     * {@code BRANCH}: selected, alternate) — so {@link #ops()} is the
     * unit's produced-operation list in source order and the id
     * allocation sequence follows the same order. Every op is recorded
     * as a member of exactly the current emission block (C-D1); the
     * produced {@link StructuredBodyTable} is available through
     * {@link #bodyTable()}.</p>
     */
    public static final class ModuleLowerer {

        private final ModuleId module;
        private final String sourceId;
        private final CheckResult checks;
        private final SemanticIdAllocator ids;
        private final BlockId moduleInitBlock;
        private long nextOrdinal = 0;
        private final List<SemanticOp> ops = new ArrayList<>();
        private final List<ForEachFrame> frames = new ArrayList<>();
        /**
         * The catch-binding frames (C-D6): the innermost enclosing
         * {@code TRY_CATCH} catch variables. A {@code BINDING_LOAD} of a
         * frame's name carries the frame's binding and the pinned
         * initial generation; the try/catch arm pushes exactly one frame
         * while lowering the catch block (binding init mechanics E6).
         */
        private final List<CatchFrame> catchFrames = new ArrayList<>();
        /**
         * The block-membership production state (C-D1): the ordered ops
         * per block and the inverse membership, plus the emission block
         * stack. Every emitted op becomes a member of exactly the top
         * block; child blocks are pushed while their contents are
         * lowered. The produced {@link StructuredBodyTable} is built at
         * {@link #bodyTable()}.
         */
        private final java.util.LinkedHashMap<BlockId, List<OpId>> blockOps =
            new java.util.LinkedHashMap<>();
        private final java.util.LinkedHashMap<OpId, BlockId> opBlocks =
            new java.util.LinkedHashMap<>();
        /**
         * The enclosing structure-op parents (C-D3..C-D6): the innermost
         * structure op whose block is currently being lowered. Every op
         * emitted inside a structure's child block records that
         * structure as its {@code parentOpId} — block ops record the
         * structure op, and nested structure ops record their enclosing
         * structure op.
         */
        private final ArrayDeque<OpId> blockParents = new ArrayDeque<>();
        /**
         * The innermost enclosing loop ops (C-D7): {@code BREAK}/
         * {@code CONTINUE} record the top loop as their target — the
         * checker's E2000 pins source-level loop placement, so a missing
         * target is a producer defect. Pushed while lowering a loop or
         * for-of body block.
         */
        private final ArrayDeque<OpId> loopTargets = new ArrayDeque<>();
        /**
         * The per-block termination flags (C-D2 dominance): a
         * {@code THROW}/{@code BREAK}/{@code CONTINUE} terminates its
         * block; a following statement in the same block is unreachable
         * source and fails closed — the validated block model never
         * admits an op after a terminator in its block.
         */
        private final java.util.LinkedHashMap<BlockId, Boolean> blockTerminated =
            new java.util.LinkedHashMap<>();
        /**
         * The enclosing address-chain parents (A-D2): the innermost chain
         * op currently being built. Every op emitted while a chain is
         * active records that chain as its {@code parentOpId} — chain
         * children in payload order and nested chain ops alike.
         */
        private final ArrayDeque<OpId> chainParents = new ArrayDeque<>();
        /**
         * The cached store identities of assigned variables (keyed by the
         * resolved {@link Symbol.VariableSymbol} identity, never by name
         * or structural equality — two same-named bindings in nested
         * scopes stay distinct). E6's declaration-driven
         * {@code BINDING_ALLOC} replaces this on-demand allocation.
         */
        private final IdentityHashMap<Symbol.VariableSymbol, BindingId> variableBindings =
            new IdentityHashMap<>();
        /**
         * The binding-core mode flag (ISSUE-0444 binding-core child):
         * {@code true} exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleBindingCore} — the binding
         * walk's statement arms, the comparison-operand routing through
         * the comparison producer, and the binding-environment identifier
         * resolution are active; {@code false} (the default) preserves
         * the E3/E5 window behavior byte-for-byte.
         */
        private final boolean bindingCore;
        /**
         * The closure-core mode flag (ISSUE-0445 closure child):
         * {@code true} exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleClosureCore} — the closure
         * arms ({@code CLOSURE_NEW} for every function expression and
         * size-1 non-group function declaration), capture collection
         * during detached-body walks, and the closure-capture arm of the
         * B2 cell-kind upgrade are active. Closure-core mode implies
         * binding-core mode (the closure walk is the binding walk plus
         * the closure arms).
         */
        private final boolean closureCore;
        /**
         * The group-core mode flag (ISSUE-0446 recursive-group child):
         * {@code true} exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleGroupCore} — the group arms
         * (per-scope SCC partition over function declarations and one
         * {@code RECURSIVE_GROUP_INIT} op per size>=2 SCC with
         * pre-assigned member identities, module-init-top placement for
         * module-level groups and first-member-position placement for
         * nested-scope groups) are active on top of the closure arms.
         * Group-core mode implies closure-core and binding-core mode (the
         * group walk is the closure walk plus the group arms).
         */
        private final boolean groupCore;

        /**
         * The proof-analysis mode flag (ISSUE-0448 proof child):
         * {@code true} exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleImmutabilityCore} — the
         * conservative assignment analysis records every resolved
         * variable assignment during the walk (the same walk the
         * registry child populates) and the derived
         * {@code BindingImmutabilityProof} fact surface is available
         * through {@link #proofFacts()}. {@code false} (the default in
         * every other mode) preserves the other walks' behavior
         * byte-for-byte.
         */
        private final boolean proofAnalysis;
        /**
         * The conservative binding-immutability analysis of the session
         * (the proof child's production class, B7 — active only in
         * proof-analysis mode): the resolved assignment facts and the
         * intrinsic markers feeding the proof derivation over the
         * binding-core incarnation map.
         */
        private final BindingImmutabilityAnalysis assignmentAnalysis =
            new BindingImmutabilityAnalysis();
        /**
         * The creation-rule-analysis mode flag (ISSUE-0449 creation-rule
         * child): {@code true} exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleCreationRuleCore} — the
         * closed creation-rule classification (B6) records one
         * {@link AdapterCreationRule.PositionClassification} per
         * function-typed position in walk order, the fact surface
         * available through {@link #creationRuleFacts()}. The analysis
         * is purely observational: it emits zero ops, changes no op of
         * the shared walk, and the produced unit therefore contains
         * zero {@code FUNCTION_ADAPT} ops (mode selection, payload
         * construction, and emission are the shape-map child's).
         * {@code false} (the default in every other mode) preserves the
         * other walks' behavior byte-for-byte.
         */
        private final boolean creationRuleAnalysis;
        /**
         * The recorded creation-rule position classifications in walk
         * order (creation-rule-analysis mode): the fact surface backing
         * {@link #creationRuleFacts()}.
         */
        private final List<AdapterCreationRule.PositionClassification>
            creationClassifications = new ArrayList<>();
        /**
         * The shape-map-production mode flag (ISSUE-0450 shape-map
         * child): {@code true} exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleShapeMapCore} — every
         * {@code ADAPT}-classified position of the creation-rule walk
         * emits exactly one {@code FUNCTION_ADAPT} op carrying its
         * closed-map mode and per-mode payload from birth (B7/B8),
         * produced before the position's boundary and wired as the
         * direct input of exactly the adapted position's own
         * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
         * boundary chain (an inferred declaration's result feeds its
         * {@code BINDING_INIT} directly). The produced unit therefore
         * carries one {@code FUNCTION_ADAPT} per adapted position and
         * the adapter result is the direct input of no other
         * {@code BOUNDARY} op; every other position's flow is
         * unchanged. {@code false} (the default in every other mode)
         * preserves the other walks' behavior byte-for-byte.
         */
        private final boolean shapeMapAnalysis;
        /**
         * The recorded adapter emissions in emission order (shape-map
         * mode): the fact surface backing {@link #shapeMapFacts()}.
         */
        private final List<AdapterEmission> shapeMapEmissions = new ArrayList<>();
        /**
         * The seeded first-class intrinsic function-value identities by
         * intrinsic name ({@code int}/{@code number} — the values the
         * intrinsic bindings' INIT operands commit at module-init top):
         * the VALUE-over-intrinsic operand of the shape-map child (B7
         * arm (a) — an intrinsic function value is a materialized
         * function-value operand; the adapter retains that identity, and
         * no function-typed load of the intrinsic binding is emitted —
         * a first-class intrinsic value has no closed
         * {@code FunctionExecutionBinding} shape, B5).
         */
        private final Map<String, ValueId> intrinsicIdentities = new LinkedHashMap<>();
        /**
         * The produced recursive groups' member facts in creation order
         * (group-core mode): the fact surface backing
         * {@link #groupFacts()}.
         */
        private final List<GroupFacts> groupFactsList = new ArrayList<>();
        /**
         * The pinned parameter bindings of the walk (B1/B9): every
         * parameter ALLOC emission records its {@link BindingId} — the
         * checker facts {@code BINDING_INIT_ONCE}'s parameter arm
         * consumes ({@link #pinnedWriteFacts()}). The unit payload alone
         * cannot distinguish a parameter ALLOC from a local ALLOC (both
         * {@code mutable=true}, generation 0, body-root block).
         */
        private final LinkedHashSet<BindingId> parameterBindings = new LinkedHashSet<>();
        /**
         * The pinned import-alias bindings of the walk (B1/B9): every
         * hoisted import-alias ALLOC emission records its
         * {@link BindingId} — the checker facts
         * {@code BINDING_INIT_ONCE}'s import-alias arm consumes
         * ({@link #pinnedWriteFacts()}). The unit payload alone cannot
         * distinguish an alias ALLOC from an intrinsic ALLOC (both
         * module-region {@code mutable=false} ALLOCs).
         */
        private final LinkedHashSet<BindingId> importAliasBindings = new LinkedHashSet<>();
        /**
         * The hoisted import-alias cell per alias name (declaration
         * order): the alias&#8596;cell join the {@code MODULE_IMPORT}
         * arm records in the op's payload ({@code aliasCells}) — the
         * explicit list the import completion writes and the bindings
         * production validator resolves the alias's pinned initializing
         * write through.
         */
        private final Map<String, BindingId> importAliasCells = new LinkedHashMap<>();
        /**
         * The full-program mode flag (ISSUE-0410 decomposition-tail
         * carrier slice): {@code true} exactly when the session was
         * created by {@link SemanticLowerer#lowerModuleFullProgram} —
         * the unified walk (module-level lets/imports/functions plus
         * every E5 statement and the carrier's CALL/RETURN/stdlib arms
         * inside function bodies), the per-function entry/return
         * reservations, and the module-init-level entry delegation
         * ({@code CALL(DIRECT main)} + {@code DISCARD}) are active.
         * Full-program mode implies binding-core and closure-core modes.
         */
        private final boolean fullProgram;
        /**
         * The class-declaration mode flag (ISSUE-0511): {@code true}
         * exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleClassCore} — the class walk
         * is the group walk plus the class-declaration arms
         * ({@code ClassLayout} records, detached {@code CLASS_DEFAULT}
         * ops with their default blocks, and the exported classes'
         * {@code CLASS_FACTORY} ops plus the
         * {@link deal.semantic.ir.ClassFactoryRegistry} registrations).
         */
        private final boolean classCore;
        /**
         * The module's own interface index entry (class-core mode): the
         * pre-allocated {@code ClassInterface.constructionEntry} ids of
         * the exported classes (K-D2). {@code null} outside class-core
         * mode.
         */
        private final deal.semantic.ir.ExternalModuleInterface ownInterface;
        /**
         * The imported-construction facts of the session (class-core
         * mode, ISSUE-0514): the {@link SharedFactoryFacts} per imported
         * {@link ClassId} — the owner's factory facts (the interface's
         * {@code constructionEntry}, the factory op id, and the factory
         * result {@code ValueId}) plus the owner layout and interface
         * entry the {@code CLASS_NEW} arm consumes for
         * {@code SHARED_FACTORY} lowering (K-D4/K-D5). Empty by default;
         * a literal of an imported class without facts defers to E10
         * (never silently emitted).
         */
        private final Map<ClassId, SharedFactoryFacts> sharedFactories;
        /**
         * The project-level class registration seeds of the session
         * (ISSUE-0634; design source
         * {@code project-lowering-entry-and-registration-seeds} D4-D6 and
         * the registration-seed contract): the layout resolution context
         * every unit's session receives before its walk, consulted by the
         * class-literal arm after the unit's own declared layouts and the
         * in-project factory facts. The seeds are never merged into
         * {@link #classLayouts}: the unit keeps carrying its own declared
         * layouts only (the class-construction validator discriminates a
         * same-module class by exactly that membership). Empty outside the
         * project entry.
         */
        private ClassRegistrationSeeds registrationSeeds =
            new ClassRegistrationSeeds(Map.of());
        /**
         * The declared conversion intrinsics of the compilation
         * (ISSUE-0634): the closed {@link IntrinsicKind} set the project
         * entry hands the session — the seed registers exactly these
         * kinds and fails closed for a module intrinsic outside the
         * declared set (a compiler-constant disagreement is a producer
         * defect, never a silently registered third intrinsic). Empty
         * outside the project entry (the per-module entries keep their
         * closed two-member seed).
         */
        private List<IntrinsicKind> declaredConversionIntrinsics = List.of();
        /**
         * The produced class layouts keyed by {@link ClassId} in
         * declaration order (K-D2; the unit's {@code classLayouts} map,
         * built by the class-declaration arm).
         */
        private final java.util.LinkedHashMap<ClassId, deal.semantic.ir.ClassLayout>
            classLayouts = new java.util.LinkedHashMap<>();
        /**
         * The produced factory registrations keyed by the pre-allocated
         * {@link deal.semantic.ir.ClassFactoryId} construction entry in
         * declaration order (K-D2; the unit-side
         * {@link deal.semantic.ir.ClassFactoryRegistry} record).
         */
        private final java.util.LinkedHashMap<deal.semantic.ir.ClassFactoryId, OpId>
            factoryRegistry = new java.util.LinkedHashMap<>();
        /**
         * The produced per-site JSON default-child registrations keyed by
         * the {@code @jsonable} classes' {@code JSON_FROM_CLASS} op ids
         * (K-D8; ISSUE-0515 — the unit-side
         * {@link deal.semantic.ir.JsonDefaultChildTable} record): each
         * entry lists the class's required-present defaulted fields'
         * {@code CLASS_DEFAULT} op ids in declaration order (the same
         * list the factory payload carries; an omitted
         * optional-with-default field's default never runs and its op id
         * never enters the list, K-D4 step 2).
         */
        private final java.util.LinkedHashMap<OpId, List<OpId>> jsonDefaultChildren =
            new java.util.LinkedHashMap<>();
        /**
         * One defaulted field's declaration-arm facts: the emitted
         * {@code CLASS_DEFAULT} op id and its result {@code ValueId}
         * (the {@code CLASS_DEFAULT_FIELD} boundary input of a later
         * {@code CLASS_NEW}, K-D4).
         */
        private record ClassDefaultFact(OpId opId, ValueId result) {

            private ClassDefaultFact {
                Objects.requireNonNull(opId, "opId must not be null");
                Objects.requireNonNull(result, "result must not be null");
            }
        }
        /**
         * The produced per-class default facts keyed by {@link ClassId}
         * then field name in declaration order (class-core mode): the
         * surface the {@code CLASS_NEW} arm consults for
         * {@code classDefaultOpIds} and {@code CLASS_DEFAULT_FIELD}
         * boundary inputs — gated on required-present at the use site
         * (K-D4 step 2/step 5: an optional-with-default field's fact is
         * recorded but never wired).
         */
        private final java.util.LinkedHashMap<ClassId,
            java.util.LinkedHashMap<String, ClassDefaultFact>> classDefaults =
            new java.util.LinkedHashMap<>();
        /**
         * One open default-block walk's admission context (K-D3): the
         * default block itself, the blocks allocated inside the walk
         * (block-internal allocations), and the capture-collector depth
         * at entry. Every reference of the walk — a direct identifier
         * reference or a capture resolved by a nested detached walk (a
         * closure body allocated inside the default) — admits only blocks
         * in {@code internalBlocks} and the module-init block; the
         * collector depth decides the dispatch (direct load versus the
         * nested closure's capture registration), never the admission —
         * a nested closure's capture resolving to an enclosing-region
         * binding fails the same {@code CLASS_DEFAULT_CAPTURE} admission
         * (K-D3's closed rule has no nested-closure bypass).
         */
        private record DefaultContext(BlockId block, Set<BlockId> internalBlocks,
                                      int entryCaptureDepth) {

            private DefaultContext {
                Objects.requireNonNull(block, "block must not be null");
                Objects.requireNonNull(internalBlocks, "internalBlocks must not be null");
                if (entryCaptureDepth < 0) {
                    throw new IllegalArgumentException(
                        "entryCaptureDepth must be >= 0, got " + entryCaptureDepth);
                }
            }
        }
        /**
         * The open default-block walks of the session, innermost first
         * (class-core mode).
         */
        private final ArrayDeque<DefaultContext> defaultContexts = new ArrayDeque<>();
        /**
         * The statement-walk strategy of the session: the nested-statement
         * recursion every arm consults. The E5 window routes to
         * {@link #lowerStatements}, the binding/closure windows to
         * {@link #lowerBindingStatements}, and the full-program window to
         * the unified walk ({@link #lowerFullStatements}) — so every arm's
         * nested blocks follow the session's construct coverage without
         * re-implementing the dispatch.
         */
        private final StatementWalk statementWalk;
        /**
         * One closed statement-walk strategy (the session's nested-block
         * recursion).
         */
        @FunctionalInterface
        private interface StatementWalk {
            void walk(List<StatementNode> statements, boolean moduleLevel);
        }
        /**
         * The single cell-kind derivation of the session (B2): every
         * {@code BINDING_ALLOC} payload cell kind flows through
         * {@link CellKindDerivation#cellKindOf} — at emission and again
         * at the walk-finalization re-derivation over the complete
         * capture-reference union.
         */
        private final CellKindDerivation cellKinds = new CellKindDerivation();
        /**
         * The produced lowered functions keyed by {@link FunctionId} (the
         * unit's {@code functions} map; closure-core mode).
         */
        private final Map<FunctionId, LoweredFunction> functions = new LinkedHashMap<>();
        /**
         * The produced function-execution-bindings registry (the unit's
         * {@code functionBindings} map; the registry child's production
         * class, B5 — closure-core mode): exactly one registration per
         * producing allocation keyed by
         * {@link FunctionAllocationIdentity}, duplicate-key rejection at
         * registration time, and the insertion-ordered immutable
         * snapshot consumed by the unit producer.
         */
        private final FunctionBindingRegistry registry = new FunctionBindingRegistry();
        /**
         * The full-program per-function contexts (ISSUE-0410 carrier
         * slice): one context per module-level function declaration,
         * reserved at hoist time — the function identity, the body block,
         * the exact signature, and the pre-allocated return-boundary and
         * call-site op identities (forward references across declarations
         * and call sites resolve deterministically).
         */
        private final IdentityHashMap<BindingCoreIncarnation, FunctionContext>
            functionContexts = new IdentityHashMap<>();
        /**
         * The module-level function contexts keyed by declared name (the
         * entry-delegation lookup surface).
         */
        private final Map<String, FunctionContext> moduleFunctionContexts =
            new LinkedHashMap<>();
        /**
         * The binding-id → function-context index (the call-site
         * resolution surface of the carrier slice).
         */
        private final Map<BindingId, FunctionContext> contextsByBindingId =
            new LinkedHashMap<>();
        /**
         * The module's resolved import facts (the console-stdlib
         * detection surface), installed by the full-program entry.
         */
        private List<ResolvedImport> moduleImports = List.of();
        /**
         * The E7 call-machine mode flag (ISSUE-0236): {@code true}
         * exactly when the session was created by
         * {@link SemanticLowerer#lowerModuleFullProgramE7} — the
         * statically-resolved call arms, adapter creation, async starts,
         * entries/callbacks, and the {@code ENTRY_INVOKE} delegation are
         * active.
         */
        private boolean e7Calls;
        /** The module's checked export facts (the E7 entry/callback surface). */
        private List<ExportInterface> moduleExports = List.of();
        /** The callee-module route facts (execution-owner resolution). */
        private Map<ModuleId, ModuleRoute> calleeRoutes = Map.of();
        /** The callee modules' recorded {@code EXTERNAL_ENTRY} op ids by export name. */
        private Map<ModuleId, Map<String, OpId>> calleeExternalEntries = Map.of();
        /** The exported function names the scenario invokes as callbacks. */
        private Set<String> callbackExports = Set.of();
        /** The module's recorded {@code EXTERNAL_ENTRY} op ids by export name. */
        private final LinkedHashMap<String, OpId> recordedEntries = new LinkedHashMap<>();
        /** The module's recorded {@code CALLBACK_INVOKE} op ids by export name. */
        private final LinkedHashMap<String, OpId> recordedCallbacks = new LinkedHashMap<>();
        /** The function-context index by {@link FunctionId} (E7 call-site resolution). */
        private final Map<FunctionId, FunctionContext> contextsByFunctionId =
            new LinkedHashMap<>();
        /** The hoisted module-level functions' allocation identities by name. */
        private final Map<String, ValueId> moduleFunctionIdentities = new LinkedHashMap<>();
        /**
         * The innermost enclosing function context of the current body
         * walk (RETURN resolution).
         */
        private final ArrayDeque<FunctionContext> functionStack = new ArrayDeque<>();
        /**
         * One module-level function's carrier facts (ISSUE-0410): the
         * lowered identity plus the reserved return-boundary/call-site op
         * ids. The return boundary op is emitted exactly once (at the
         * first RETURN, or the implicit trailing return); the call-site
         * op id becomes the single {@code CALL(DIRECT)} that invokes the
         * function (the entry delegation for {@code main}).
         */
        /** The closed per-function invocation shapes of the E7 call machine. */
        private enum InvocationShape {
            /** Called from source: {@code CALL(DIRECT/INDIRECT)} (sync). */
            SOURCE_CALL,
            /** Awaited from source: an {@code ASYNC_START(DEAL_BODY)} body task. */
            SOURCE_ASYNC,
            /** Cross-module invocation: the function's {@code EXTERNAL_ENTRY}. */
            EXTERNAL_ENTRY_SHAPE,
            /** Host-driven invocation: the export's {@code CALLBACK_INVOKE}. */
            CALLBACK_SHAPE
        }

        private static final class FunctionContext {
            final FunctionId functionId;
            final BlockId bodyBlock;
            final RuntimeDescriptor.Func signature;
            final OpId returnBoundaryOpId;
            final OpId callSiteOpId;
            boolean returnBoundaryEmitted;
            boolean callSiteUsed;
            InvocationShape shape;
            OpId shapeOpId;

            FunctionContext(FunctionId functionId, BlockId bodyBlock,
                            RuntimeDescriptor.Func signature, OpId returnBoundaryOpId,
                            OpId callSiteOpId) {
                this.functionId = functionId;
                this.bodyBlock = bodyBlock;
                this.signature = signature;
                this.returnBoundaryOpId = returnBoundaryOpId;
                this.callSiteOpId = callSiteOpId;
            }

            /**
             * Assigns the function's single invocation shape (the
             * non-overlapping machine): the first assignment wins and a
             * conflicting later assignment is a producer defect — the
             * statically-resolved slice admits exactly one enclosing
             * invocation shape per function (runtime shape selection is
             * ISSUE-0531's).
             */
            void assignShape(InvocationShape candidate, OpId candidateOpId) {
                if (shape == null) {
                    shape = candidate;
                    shapeOpId = candidateOpId;
                    return;
                }
                if (shape != candidate) {
                    throw new ConstructUnlowered("function id " + functionId.id()
                        + " is invoked under two invocation shapes (" + shape + " and "
                        + candidate + ") — the statically-resolved slice admits exactly "
                        + "one shape per function (runtime shape selection is "
                        + "ISSUE-0531's)");
                }
            }

            /** The enclosing invocation op the function's RETURN ops name. */
            OpId invocationOpId() {
                return shapeOpId != null ? shapeOpId : callSiteOpId;
            }
        }
        /**
         * The produced closures' capture facts in creation order
         * (closure-core mode): the fact surface backing
         * {@link #closureFacts()}.
         */
        private final List<ClosureFacts> closureFactsList = new ArrayList<>();
        /**
         * The statically tracked function-value identities of binding
         * incarnations (closure-core mode, identity-keyed): the
         * allocation identity the incarnation's cell currently holds.
         * {@code BINDING_LOAD}s of function-typed bindings publish the
         * tracked identity (identity preservation — the schema-level
         * {@code R-FUNCTION-BINDING} rule holds); a load whose
         * incarnation has no tracked identity fails closed as the
         * registry child's resolution (B5).
         */
        private final IdentityHashMap<BindingCoreIncarnation, ValueId> functionIdentity =
            new IdentityHashMap<>();
        /**
         * The capture borders of the currently open detached-body walks
         * (closure-core mode), innermost first: the number of binding
         * frames outside the function recorded before its own frame was
         * pushed. A reference inside the body resolving to a frame at or
         * beyond {@code bindingScopes.size() - border} is a capture
         * (B9 R2/R3 as the resolution model).
         */
        private final ArrayDeque<Integer> captureBorders = new ArrayDeque<>();
        /**
         * The capture collectors of the currently open detached-body
         * walks (closure-core mode), innermost first: each collector
         * records the captured cells in first-reference order for the
         * {@code CLOSURE_NEW} being built.
         */
        private final ArrayDeque<List<CapturedCell>> captureCollectors = new ArrayDeque<>();
        /**
         * The emission targets of the session, innermost first: the
         * session's op list at the bottom, one buffer per open
         * detached-body walk. Every emission appends to
         * {@link #emitTarget()}, so a function body's ops can be
         * collected while the walk runs and flushed after the
         * {@code CLOSURE_NEW} op that needs the collected captures.
         */
        private final ArrayDeque<List<SemanticOp>> emitTargets = new ArrayDeque<>();
        /**
         * The installed binding-environment resolver (ISSUE-0444): the
         * identifier arm and the variable-assignment arm consult it
         * (after the for-of frames, before the legacy on-demand path) so
         * every {@code BINDING_LOAD}/{@code BINDING_STORE} they emit
         * names the dominant incarnation at the site. {@code null} in
         * the E3/E5 window.
         */
        private BindingSiteResolver bindingSiteResolver;
        /**
         * The binding environment's scope frames (binding-core mode),
         * innermost first: each frame maps a declared name to the
         * incarnation dominant <em>within that frame</em> — the frame
         * entry snapshots the dominant incarnation of the name at frame
         * entry, a registration during the frame replaces the entry, and
         * resolution walks the frames innermost-first. This keeps the
         * for-let's update block resolving the generation-0 counter after
         * the body frame (whose entry names generation 1) is popped.
         * Every cell ever registered stays recorded in
         * {@link #bindingCells}.
         */
        private final List<Map<String, FrameEntry>> bindingScopes = new ArrayList<>();
        /**
         * The checker's per-scoped-statement symbol tables, innermost
         * first: the current stack of scope-map key nodes (blocks,
         * function declarations, for statements, try statements) so the
         * walk resolves declared types of nested bindings without
         * retaining any {@code NameResolver} instance (D4).
         */
        private final ArrayDeque<StatementNode> checkerScopeNodes = new ArrayDeque<>();
        /**
         * The registered binding cells in registration order (binding-core
         * mode): the fact surface backing {@link #bindingFacts()}.
         */
        private final List<BindingCell> bindingCells = new ArrayList<>();
        /**
         * The registered binding cells by {@link BindingId}: a binding's
         * multiple incarnations (the for-let counter and its per-iteration
         * incarnation share one identity) append to exactly one cell.
         */
        private final Map<BindingId, BindingCell> cellsById = new LinkedHashMap<>();
        /**
         * The current structured-region block identities of the binding
         * walk, innermost first (module-init block at the bottom): the
         * scope every {@code BINDING_ALLOC} emitted at the current site
         * carries (B9 R1's same-block/structured-ancestor resolution
         * blocks).
         */
        private final ArrayDeque<BlockId> blockStack = new ArrayDeque<>();
        /**
         * The checked program's span: the pinned origin span of the
         * module-init-top intrinsic ALLOC/INIT ops (synthetic module
         * entry ops with no statement span of their own).
         */
        private final Span programSpan;

        /**
         * One binding cell of the binding environment (binding-core mode):
         * the declared name, its single globally unique {@link BindingId},
         * and its incarnations in allocation order.
         */
        private static final class BindingCell {

            final String name;
            final BindingId id;
            final List<BindingCoreIncarnation> incarnations = new ArrayList<>();

            BindingCell(String name, BindingId id) {
                this.name = Objects.requireNonNull(name, "name must not be null");
                this.id = Objects.requireNonNull(id, "id must not be null");
            }
        }

        /**
         * One scope-frame entry: the name's cell plus the incarnation
         * dominant within the frame (the frame-level visibility fact that
         * resolves loads/stores at the site).
         */
        private record FrameEntry(BindingCell cell, BindingCoreIncarnation incarnation) {
        }

        /**
         * One name resolution of the binding environment (closure-core
         * mode): the innermost frame entry plus the frame's index
         * (innermost first) — the frame index decides whether a body
         * reference resolves inside the function's own scope chain or is
         * a capture (B9 R2/R3).
         */
        private record FrameResolution(FrameEntry entry, int frameIndex) {

            private FrameResolution {
                Objects.requireNonNull(entry, "entry must not be null");
                if (frameIndex < 0) {
                    throw new IllegalArgumentException(
                        "frameIndex must be >= 0, got " + frameIndex);
                }
            }
        }

        /**
         * One captured cell of an open detached-body walk: the cell plus
         * the incarnation the capture resolves to at the creation site
         * (the dominant incarnation of the resolved frame entry).
         */
        private record CapturedCell(BindingCell cell, BindingCoreIncarnation incarnation) {
        }

        /**
         * Creates one lowering session. The module-init block is the
         * session's first allocation (role {@code BLOCK}).
         *
         * @param module   the module identity; non-null
         * @param sourceId the stable source identity carried on every
         *                 op's origin; non-null
         * @param checks   the module's checked facts (read-only); non-null
         * @param ids      the project's allocator in dependency order;
         *                 non-null
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids) {
            this(module, sourceId, checks, ids, false,
                new Span(sourceId, 1, 1, 1, 1, Span.UNKNOWN_OFFSET, Span.UNKNOWN_OFFSET));
        }

        /**
         * Creates one lowering session with the binding-core mode flag
         * (ISSUE-0444 binding-core child). In binding-core mode the
         * module scope frame is opened at construction and the
         * binding-environment resolver is installed, so the identifier
         * arm and the variable-assignment arm resolve declared bindings
         * against the walk's dominant incarnations.
         *
         * @param module      the module identity; non-null
         * @param sourceId    the stable source identity carried on every
         *                    op's origin; non-null
         * @param checks      the module's checked facts (read-only); non-null
         * @param ids         the project's allocator in dependency order;
         *                    non-null
         * @param bindingCore {@code true} to activate the binding walk's
         *                    arms and environment
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore, Span programSpan) {
            this(module, sourceId, checks, ids, bindingCore, false, programSpan);
        }

        /**
         * Creates one lowering session with the binding-core mode flag
         * and the closure-core mode flag (ISSUE-0444 binding-core child;
         * ISSUE-0445 closure child). Closure-core mode implies
         * binding-core mode (the closure walk is the binding walk plus
         * the closure arms).
         *
         * @param module      the module identity; non-null
         * @param sourceId    the stable source identity carried on every
         *                    op's origin; non-null
         * @param checks      the module's checked facts (read-only); non-null
         * @param ids         the project's allocator in dependency order;
         *                    non-null
         * @param bindingCore {@code true} to activate the binding walk's
         *                    arms and environment
         * @param closureCore {@code true} to activate the closure arms on
         *                    top of the binding walk
         * @param programSpan the checked program's span; non-null
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, Span programSpan) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, false, programSpan);
        }

        /**
         * Creates one lowering session with the binding-core, closure-core,
         * and group-core mode flags (ISSUE-0444 binding-core child;
         * ISSUE-0445 closure child; ISSUE-0446 recursive-group child).
         * Group-core mode implies closure-core and binding-core mode (the
         * group walk is the closure walk plus the group arms).
         *
         * @param module      the module identity; non-null
         * @param sourceId    the stable source identity carried on every
         *                    op's origin; non-null
         * @param checks      the module's checked facts (read-only); non-null
         * @param ids         the project's allocator in dependency order;
         *                    non-null
         * @param bindingCore {@code true} to activate the binding walk's
         *                    arms and environment
         * @param closureCore {@code true} to activate the closure arms on
         *                    top of the binding walk
         * @param groupCore   {@code true} to activate the group arms on
         *                    top of the closure walk
         * @param programSpan the checked program's span; non-null
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, boolean groupCore, Span programSpan) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, groupCore,
                false, programSpan);
        }

        /**
         * Creates one lowering session with the binding-core, closure-core,
         * group-core, and proof-analysis mode flags (ISSUE-0444 binding-core
         * child; ISSUE-0445 closure child; ISSUE-0446 recursive-group child;
         * ISSUE-0448 proof child). Proof-analysis mode rides on top of the
         * walk flags (the proof entry point passes all four): it records the
         * walk's resolved variable assignments and exposes the derived proof
         * fact surface; it changes no emitted op.
         *
         * @param module        the module identity; non-null
         * @param sourceId      the stable source identity carried on every
         *                      op's origin; non-null
         * @param checks        the module's checked facts (read-only); non-null
         * @param ids           the project's allocator in dependency order;
         *                      non-null
         * @param bindingCore   {@code true} to activate the binding walk's
         *                      arms and environment
         * @param closureCore   {@code true} to activate the closure arms on
         *                      top of the binding walk
         * @param groupCore     {@code true} to activate the group arms on
         *                      top of the closure walk
         * @param proofAnalysis {@code true} to activate the conservative
         *                      assignment analysis on top of the walk
         * @param programSpan   the checked program's span; non-null
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, boolean groupCore,
                             boolean proofAnalysis, Span programSpan) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, groupCore,
                proofAnalysis, false, programSpan);
        }

        /**
         * Creates one lowering session with the binding-core, closure-core,
         * group-core, proof-analysis, and creation-rule-analysis mode
         * flags (ISSUE-0444 binding-core child; ISSUE-0445 closure child;
         * ISSUE-0446 recursive-group child; ISSUE-0448 proof child;
         * ISSUE-0449 creation-rule child). Creation-rule-analysis mode
         * rides on top of the walk flags (the creation-rule entry point
         * passes all five): it classifies every function-typed position
         * the walk reaches by checker facts per the closed B6 rule and
         * records the classifications; it emits zero ops and changes no
         * emitted op of the shared walk.
         *
         * @param module              the module identity; non-null
         * @param sourceId            the stable source identity carried on
         *                            every op's origin; non-null
         * @param checks              the module's checked facts (read-only);
         *                            non-null
         * @param ids                 the project's allocator in dependency
         *                            order; non-null
         * @param bindingCore         {@code true} to activate the binding
         *                            walk's arms and environment
         * @param closureCore         {@code true} to activate the closure
         *                            arms on top of the binding walk
         * @param groupCore           {@code true} to activate the group arms
         *                            on top of the closure walk
         * @param proofAnalysis       {@code true} to activate the
         *                            conservative assignment analysis on
         *                            top of the walk
         * @param creationRuleAnalysis {@code true} to activate the closed
         *                            creation-rule classification on top
         *                            of the walk
         * @param programSpan         the checked program's span; non-null
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, boolean groupCore,
                             boolean proofAnalysis, boolean creationRuleAnalysis,
                             Span programSpan) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, groupCore,
                proofAnalysis, creationRuleAnalysis, false, programSpan);
        }

        /**
         * Creates one lowering session with the binding-core, closure-core,
         * group-core, proof-analysis, creation-rule-analysis, and
         * shape-map mode flags (ISSUE-0444 binding-core child;
         * ISSUE-0445 closure child; ISSUE-0446 recursive-group child;
         * ISSUE-0448 proof child; ISSUE-0449 creation-rule child;
         * ISSUE-0450 shape-map child). Shape-map mode rides on top of the
         * walk flags (the shape-map entry point passes all six): every
         * {@code ADAPT}-classified position emits exactly one
         * {@code FUNCTION_ADAPT} op carrying its closed-map mode and
         * per-mode payload from birth (B7/B8), produced before the
         * position's boundary and wired as the direct input of exactly
         * the adapted position's own
         * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
         * boundary chain (an inferred declaration's result feeds its
         * {@code BINDING_INIT} directly), with a fresh adapter
         * allocation identity registered as an {@code AdapterBinding}
         * through the registry seam, zero {@code BOUNDARY} ops emitted
         * by the adapter, and the B2 cell-kind derivation completed
         * over the union of the closure captures and this child's two
         * remaining capture arms ({@code REEVALUATE_THUNK}
         * {@code capturedBindings} entries and
         * {@code FUNCTION_ADAPT(SHARED_CELL)} {@code SharedCell} source
         * references) before the finalization re-derivation.
         *
         * @param module              the module identity; non-null
         * @param sourceId            the stable source identity carried on
         *                            every op's origin; non-null
         * @param checks              the module's checked facts (read-only);
         *                            non-null
         * @param ids                 the project's allocator in dependency
         *                            order; non-null
         * @param bindingCore         {@code true} to activate the binding
         *                            walk's arms and environment
         * @param closureCore         {@code true} to activate the closure
         *                            arms on top of the binding walk
         * @param groupCore           {@code true} to activate the group arms
         *                            on top of the closure walk
         * @param proofAnalysis       {@code true} to activate the
         *                            conservative assignment analysis on
         *                            top of the walk
         * @param creationRuleAnalysis {@code true} to activate the closed
         *                            creation-rule classification on top
         *                            of the walk
         * @param shapeMapAnalysis    {@code true} to activate the closed
         *                            shape-map production on top of the
         *                            walk (the ADAPT arm emits its
         *                            FUNCTION_ADAPT op)
         * @param programSpan         the checked program's span; non-null
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, boolean groupCore,
                             boolean proofAnalysis, boolean creationRuleAnalysis,
                             boolean shapeMapAnalysis, Span programSpan) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, groupCore,
                proofAnalysis, creationRuleAnalysis, shapeMapAnalysis, programSpan,
                false);
        }

        /**
         * The full-program session constructor (ISSUE-0410 carrier
         * slice): {@code fullProgram} activates the unified walk strategy
         * and the entry/return reservations on top of the binding and
         * closure arms.
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, Span programSpan, boolean fullProgram) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, false, false,
                false, false, programSpan, fullProgram);
        }

        /**
         * The terminal session constructor carrying every mode flag:
         * the binding-core, closure-core, group-core, proof-analysis,
         * creation-rule-analysis, and shape-map flags of the
         * ISSUE-0444..ISSUE-0450 children plus the ISSUE-0410
         * full-program flag of the decomposition-tail carrier slice.
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, boolean groupCore,
                             boolean proofAnalysis, boolean creationRuleAnalysis,
                             boolean shapeMapAnalysis, Span programSpan,
                             boolean fullProgram) {
            this(module, sourceId, checks, ids, bindingCore, closureCore, groupCore,
                proofAnalysis, creationRuleAnalysis, shapeMapAnalysis, programSpan,
                fullProgram, false, null, Map.of());
        }

        /**
         * The class-declaration session constructor (ISSUE-0511, extended
         * by the ISSUE-0514 shared-factory child): the {@code classCore}
         * flag activates the class-declaration arms on top of the walk
         * flags (the class walk is the group walk plus the class arms),
         * {@code ownInterface} supplies the module's own interface index
         * entry — the pre-allocated
         * {@code ClassInterface.constructionEntry} ids the exported
         * classes' {@code CLASS_FACTORY} ops register under (K-D2) —
         * and {@code sharedFactories} supplies the imported-construction
         * facts ({@link SharedFactoryFacts} per imported {@link ClassId})
         * the {@code CLASS_NEW} arm consumes for SHARED_FACTORY lowering
         * (K-D4/K-D5).
         */
        public ModuleLowerer(ModuleId module, String sourceId, CheckResult checks,
                             SemanticIdAllocator ids, boolean bindingCore,
                             boolean closureCore, boolean groupCore,
                             boolean proofAnalysis, boolean creationRuleAnalysis,
                             boolean shapeMapAnalysis, Span programSpan,
                             boolean fullProgram, boolean classCore,
                             deal.semantic.ir.ExternalModuleInterface ownInterface,
                             Map<ClassId, SharedFactoryFacts> sharedFactories) {

            this.module = Objects.requireNonNull(module, "module must not be null");
            this.sourceId = Objects.requireNonNull(sourceId, "sourceId must not be null");
            this.checks = Objects.requireNonNull(checks, "checks must not be null");
            this.ids = Objects.requireNonNull(ids, "ids must not be null");
            this.bindingCore = bindingCore;
            this.closureCore = closureCore && bindingCore;
            this.groupCore = groupCore && this.closureCore;
            this.proofAnalysis = proofAnalysis;
            this.creationRuleAnalysis = creationRuleAnalysis;
            this.shapeMapAnalysis = shapeMapAnalysis && this.creationRuleAnalysis;
            this.fullProgram = fullProgram && bindingCore;
            this.classCore = classCore;
            this.ownInterface = ownInterface;
            this.sharedFactories = Map.copyOf(sharedFactories);
            this.statementWalk = fullProgram
                ? this::lowerFullStatements
                : (bindingCore ? this::lowerBindingStatements
                    : (statements, moduleLevel) -> lowerStatements(statements));
            this.programSpan = Objects.requireNonNull(programSpan,
                "programSpan must not be null");
            this.moduleInitBlock = ids.nextBlockId(module, nextOrdinal++, 0);
            this.blockOps.put(moduleInitBlock, new ArrayList<>());
            this.blockTerminated.put(moduleInitBlock, false);
            this.blockStack.push(moduleInitBlock);
            emitTargets.push(ops);
            if (bindingCore) {
                bindingScopes.add(new LinkedHashMap<>());
                installBindingSiteResolver(name -> {
                    FrameEntry entry = frameEntryOf(name);
                    if (entry == null) {
                        return null;
                    }
                    return new BindingSite(entry.cell().id,
                        entry.incarnation().generation());
                });
            }
        }

        /**
         * Installs the binding-environment resolver consulted by the
         * identifier arm and the variable-assignment arm (ISSUE-0444
         * binding-core child). Installing a resolver never changes the
         * E3/E5 window's pre-existing frame/on-demand resolution — the
         * resolver is consulted only after the for-of frames and only
         * when it resolves the name.
         *
         * @param resolver the dominant-incarnation resolver; non-null
         */
        public void installBindingSiteResolver(BindingSiteResolver resolver) {
            this.bindingSiteResolver = Objects.requireNonNull(resolver,
                "resolver must not be null");
        }

        /** The binding-core mode flag of this session. */
        public boolean bindingCore() {
            return bindingCore;
        }

        /** The closure-core mode flag of this session. */
        public boolean closureCore() {
            return closureCore;
        }

        /** The group-core mode flag of this session. */
        public boolean groupCore() {
            return groupCore;
        }

        /** The module identity of this session. */
        public ModuleId module() {
            return module;
        }

        /** The produced operations in source order (unmodifiable). */
        public List<SemanticOp> ops() {
            return List.copyOf(ops);
        }

        /** The module-init block identity (the session's first allocation). */
        public BlockId moduleInitBlockId() {
            return moduleInitBlock;
        }

        // ---------------------------------------------------------------------
        // Block-membership machinery (C-D1) and the structure-op parents
        // ---------------------------------------------------------------------

        /**
         * Allocates one child block of the session: a fresh
         * {@link BlockId} registered in the block-membership state with
         * an empty op list (C-D1 — every payload-referenced block exists
         * in the produced table, empty blocks included).
         *
         * @return the fresh block identity
         */
        private BlockId allocateBlock() {
            BlockId block = ids.nextBlockId(module, nextOrdinal++, 0);
            blockOps.put(block, new ArrayList<>());
            blockTerminated.put(block, false);
            if (!defaultContexts.isEmpty()) {
                // K-D3: a block allocated inside an open default-block
                // walk is a block-internal allocation of that walk's
                // admission context.
                defaultContexts.peek().internalBlocks().add(block);
            }
            return block;
        }

        /** Pushes one allocated block as the current emission block. */
        private void pushBlock(BlockId block) {
            if (!blockOps.containsKey(block)) {
                throw new IllegalStateException(
                    "pushing an unregistered block (producer defect)");
            }
            blockStack.push(block);
        }

        /** Pops the current emission block (the outer block resumes). */
        private void popBlock() {
            if (blockStack.size() <= 1) {
                throw new IllegalStateException(
                    "popping the root module-init block (producer defect)");
            }
            blockStack.pop();
        }

        /**
         * Emits one op into the current emission target (the unit op
         * list or an open detached-body buffer, the closure child's
         * buffering) and the current emission block.
         */
        private void emit(SemanticOp op) {
            emitAt(emitTarget().size(), op);
        }

        /**
         * Emits one op at the pinned target-list position (the
         * structure-op position of a {@code LOOP}/{@code TRY_CATCH}/
         * {@code BRANCH(LOGICAL_*)} whose child blocks were lowered
         * before the op's emission) and records its membership in the
         * current emission block — the pinned unit order is structure op
         * first, then its child block ops in payload order. The mark is
         * relative to the current emission target, so a structure op
         * lowered inside a buffered detached-body walk keeps its pinned
         * position within that buffer.
         */
        private void emitAt(int mark, SemanticOp op) {
            List<SemanticOp> target = emitTarget();
            target.add(mark, op);
            BlockId block = blockStack.peek();
            if (blockOps.containsKey(block)) {
                blockOps.get(block).add(op.opId());
                opBlocks.put(op.opId(), block);
            }
        }

        /**
         * The parentage of the next USER op: the innermost address-chain
         * parent wins, then the innermost structure-op parent (block ops
         * record the enclosing structure op), else {@code null} at
         * module top level.
         */
        private OpId currentParent() {
            OpId chain = chainParents.peek();
            if (chain != null) {
                return chain;
            }
            return blockParents.peek();
        }

        /** Pushes one structure op as the current block-op parent. */
        private void pushBlockParent(OpId structureOpId) {
            blockParents.push(structureOpId);
        }

        /** Pops the current structure-op parent. */
        private void popBlockParent() {
            if (blockParents.isEmpty()) {
                throw new IllegalStateException(
                    "popping an empty block-parent stack (producer defect)");
            }
            blockParents.pop();
        }

        /** Pushes one loop op as the innermost break/continue target. */
        private void pushLoopTarget(OpId loopOpId) {
            loopTargets.push(loopOpId);
        }

        /** Pops the innermost break/continue target. */
        private void popLoopTarget() {
            if (loopTargets.isEmpty()) {
                throw new IllegalStateException(
                    "popping an empty loop-target stack (producer defect)");
            }
            loopTargets.pop();
        }

        /**
         * Marks the current emission block terminated after a
         * {@code THROW}/{@code BREAK}/{@code CONTINUE} emission (C-D2
         * dominance: no op may follow a terminator in its block).
         */
        private void terminateBlock() {
            blockTerminated.put(blockStack.peek(), true);
        }

        /**
         * Fails closed when the current emission block already carries a
         * terminator: a source statement following a
         * {@code THROW}/{@code BREAK}/{@code CONTINUE} in the same block
         * is unreachable and not representable in the validated block
         * model — {@code CONSTRUCT_UNLOWERED}, never a silent drop and
         * never an inferred block.
         */
        private void ensureBlockOpen() {
            if (Boolean.TRUE.equals(blockTerminated.get(blockStack.peek()))) {
                throw new ConstructUnlowered("statement after a terminator "
                    + "(THROW/BREAK/CONTINUE) in the same block — unreachable source "
                    + "statements are not representable in the validated block model");
            }
        }

        // ---------------------------------------------------------------------
        // Environment frames (the checker-scope analog; the for-of arm drives
        // these, and per-construct slices may arrange them explicitly)
        // ---------------------------------------------------------------------

        /**
         * Opens one for-of loop-binding frame: allocates the binding
         * (role {@code BINDING}, pinned initial generation
         * {@link #INITIAL_LOOP_GENERATION}) and pushes the frame as the
         * new innermost scope. The for-of arm drives exactly one
         * open/close pair while lowering the loop body; per-construct
         * slices may arrange frames explicitly to lower operand-position
         * identifiers against enclosing loop bindings.
         *
         * @param name the loop-binding name; non-null
         * @return the opened frame
         */
        public ForEachFrame openForEachScope(String name) {
            Objects.requireNonNull(name, "name must not be null");
            BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
            ForEachFrame frame = new ForEachFrame(name, binding, INITIAL_LOOP_GENERATION);
            frames.add(0, frame);
            return frame;
        }

        /**
         * Closes the innermost for-of loop-binding frame (a producer
         * defect when no frame is open).
         *
         * @throws IllegalStateException when no frame is open
         */
        public void closeForEachScope() {
            if (frames.isEmpty()) {
                throw new IllegalStateException(
                    "closeForEachScope without an open loop-binding frame (producer defect)");
            }
            frames.remove(0);
        }

        // ---------------------------------------------------------------------
        // The binding-core walk (ISSUE-0444 binding-core child)
        // ---------------------------------------------------------------------

        /**
         * Lowers the module's top-level statements through the
         * binding-core walk: first the module-init-top bindings — the
         * {@code int}/{@code number} intrinsic bindings (ALLOC + INIT at
         * module-init top, the retained per-module wrapper shape,
         * {@code deal/codegen/lua/LuaBackend.java:668-674}) and the
         * hoisted module-level function-name ALLOCs plus import-alias
         * ALLOCs in declaration order (B1) — then the statements in
         * source order.
         *
         * @param statements the module's top-level statements; non-null
         * @throws IllegalStateException outside binding-core mode
         * @throws ConstructUnlowered    on a construct outside the
         *         binding-core window
         */
        public void lowerBindingModule(List<StatementNode> statements) {
            if (!bindingCore) {
                throw new IllegalStateException(
                    "lowerBindingModule outside binding-core mode (producer defect)");
            }
            seedIntrinsicBindings();
            hoistModuleLevelAllocs(statements);
            statementWalk.walk(statements, true);
            finalizeCellKinds();
        }

        /**
         * The group walk's module entry point (ISSUE-0446 recursive-group
         * child): the intrinsic bindings and the hoisted module-level
         * names first (group members register without an ALLOC op and
         * pre-assign their member allocation identities — B1/B4), then
         * the module-level {@code RECURSIVE_GROUP_INIT} ops at
         * module-init top in declaration order (B4: module top level
         * admits only imports, function declarations, class declarations,
         * and exports — hoisting the group op is observationally
         * equivalent to declaration-position execution and places every
         * member's producing allocation where it dominates every closure
         * site, B3), then the statements in source order (group members
         * skip — their bodies were walked at group emission), then the
         * cell-kind finalization.
         *
         * @param statements the module's top-level statements; non-null
         * @throws IllegalStateException outside group-core mode
         * @throws ConstructUnlowered    on a construct outside the
         *         group-core window
         */
        public void lowerGroupModule(List<StatementNode> statements) {
            if (!groupCore) {
                throw new IllegalStateException(
                    "lowerGroupModule outside group-core mode (producer defect)");
            }
            List<FunctionDeclaration> moduleDeclarations = new ArrayList<>();
            for (StatementNode statement : statements) {
                if (statement instanceof FunctionDeclaration function) {
                    moduleDeclarations.add(function);
                }
            }
            List<List<FunctionDeclaration>> sccs =
                partitionFunctionDeclarations(moduleDeclarations);
            Set<FunctionDeclaration> moduleGroupMembers =
                java.util.Collections.newSetFromMap(new IdentityHashMap<>());
            List<List<FunctionDeclaration>> moduleGroups = new ArrayList<>();
            for (List<FunctionDeclaration> scc : sccs) {
                if (scc.size() >= 2) {
                    moduleGroups.add(scc);
                    moduleGroupMembers.addAll(scc);
                }
            }
            seedIntrinsicBindings();
            hoistModuleLevelAllocs(statements, moduleGroupMembers);
            // Module-init-top groups in declaration order (B4).
            for (List<FunctionDeclaration> group : moduleGroups) {
                lowerGroup(group, true);
            }
            lowerBindingStatements(statements, true);
            finalizeCellKinds();
        }

        /**
         * The project walk's module entry point (ISSUE-0634; design source
         * {@code project-lowering-entry-and-registration-seeds} D2 and the
         * project lowering contract): one session per module with every
         * arm active — the binding, closure, group, full-program call, and
         * class arms together — in the pinned walk order.
         *
         * <p><b>The pinned walk order.</b> (1) the intrinsic seeds (the
         * module-init-top {@code BINDING_ALLOC}/{@code BINDING_INIT} pair
         * per declared conversion intrinsic, with its closed
         * {@code IntrinsicFunction} registration); (2) the hoisted
         * module-level allocations (function-name and import-alias ALLOCs
         * in declaration order; module-level group members register
         * without an ALLOC — the group op's publication phase is their
         * producing allocation); (3) the module-level recursive groups at
         * module-init top in declaration order (B4); (4) the statement
         * walk with the class-declaration and call arms (nested-scope
         * groups lower at their first member's declaration position);
         * (5) the E7 terminals (export publications, entries/callbacks,
         * and the entry delegation); (6) the invocation-identity
         * finalization (the decision point after the walk and the
         * terminals, where the set of a body's static invocations is
         * final); (7) the cell-kind finalization.</p>
         *
         * <p>No two walks per module and no double allocation: the
         * session's single statement walk is the full-program walk (which
         * owns the class arms and the nested-scope group arms when the
         * class and group flags are active), so every op is emitted by
         * exactly one arm and every id is allocated once.</p>
         *
         * @param statements the module's top-level statements; non-null
         * @throws IllegalStateException outside the project session mode
         * @throws ConstructUnlowered    on a construct outside the closed
         *         coverage table of the unified walk
         */
        public void lowerProjectModule(List<StatementNode> statements) {
            Objects.requireNonNull(statements, "statements must not be null");
            if (!bindingCore || !closureCore || !groupCore || !fullProgram || !classCore) {
                throw new IllegalStateException("lowerProjectModule outside the project "
                    + "session mode (the unified walk requires the binding, closure, "
                    + "group, full-program, and class arms together; producer defect)");
            }
            List<FunctionDeclaration> moduleDeclarations = new ArrayList<>();
            for (StatementNode statement : statements) {
                if (statement instanceof FunctionDeclaration function) {
                    moduleDeclarations.add(function);
                }
            }
            List<List<FunctionDeclaration>> sccs =
                partitionFunctionDeclarations(moduleDeclarations);
            Set<FunctionDeclaration> moduleGroupMembers =
                java.util.Collections.newSetFromMap(new IdentityHashMap<>());
            List<List<FunctionDeclaration>> moduleGroups = new ArrayList<>();
            for (List<FunctionDeclaration> scc : sccs) {
                if (scc.size() >= 2) {
                    moduleGroups.add(scc);
                    moduleGroupMembers.addAll(scc);
                }
            }
            seedIntrinsicBindings();
            hoistModuleLevelAllocs(statements, moduleGroupMembers);
            // Module-init-top groups in declaration order (B4).
            for (List<FunctionDeclaration> group : moduleGroups) {
                lowerGroup(group, true);
            }
            statementWalk.walk(statements, true);
            emitE7Terminals();
            finalizeInvocationIdentities();
            finalizeCellKinds();
        }

        /**
         * The binding walk's complete fact surface: one
         * {@link BindingCoreBinding} per declared name in registration
         * order (partial when the walk failed mid-way).
         *
         * @return the recorded binding facts; non-null
         */
        public BindingCoreFacts bindingFacts() {
            List<BindingCoreBinding> facts = new ArrayList<>();
            for (BindingCell cell : bindingCells) {
                List<BindingCoreIncarnation> derived = new ArrayList<>();
                for (BindingCoreIncarnation incarnation : cell.incarnations) {
                    derived.add(new BindingCoreIncarnation(incarnation.generation(),
                        incarnation.scope(), cellKinds.cellKindOf(incarnation),
                        incarnation.mutable(), incarnation.producer(),
                        incarnation.pinnedSharedCell()));
                }
                facts.add(new BindingCoreBinding(cell.name, cell.id, derived));
            }
            return new BindingCoreFacts(facts);
        }

        /**
         * The walk's pinned-write binding facts (B1/B9): the parameter
         * and import-alias bindings the session recorded during the
         * walk — the checker-fact arms
         * {@code BindingsProductionValidator.BINDING_INIT_ONCE}
         * consumes (the unit payload alone cannot distinguish these two
         * pinned-write cells).
         *
         * @return the recorded pinned-write facts; non-null
         */
        public BindingsProductionValidator.PinnedWriteFacts pinnedWriteFacts() {
            return new BindingsProductionValidator.PinnedWriteFacts(parameterBindings,
                importAliasBindings);
        }

        /**
         * The closure walk's complete closure fact surface: one
         * {@link ClosureFacts} per produced {@code CLOSURE_NEW} in
         * creation order, each with its captures resolved at the
         * detaching op's creation site (partial when the walk failed
         * mid-way).
         *
         * @return the recorded closure facts; non-null
         */
        public List<ClosureFacts> closureFacts() {
            return List.copyOf(closureFactsList);
        }

        /**
         * The group walk's complete recursive-group fact surface: one
         * {@link GroupFacts} per produced {@code RECURSIVE_GROUP_INIT}
         * in creation order, each with its declaration-ordered member
         * facts (partial when the walk failed mid-way).
         *
         * @return the recorded group facts; non-null
         */
        public List<GroupFacts> groupFacts() {
            return List.copyOf(groupFactsList);
        }

        /**
         * The proof walk's complete immutability fact surface
         * (proof-analysis mode): the derived {@link
         * deal.semantic.ir.BindingImmutabilityProof} records per
         * {@code {binding, generation}} over the binding-core incarnation
         * map in registration order, plus the resolved assignment facts in
         * walk order (partial when the walk failed mid-way; the empty
         * surface outside proof-analysis mode).
         *
         * @return the proof fact surface; non-null
         */
        public BindingImmutabilityAnalysis.BindingImmutabilityFacts proofFacts() {
            if (!proofAnalysis) {
                return BindingImmutabilityAnalysis.BindingImmutabilityFacts.empty();
            }
            return assignmentAnalysis.facts(bindingFacts().bindings());
        }

        /**
         * The creation-rule walk's complete classification fact surface
         * (creation-rule-analysis mode): one
         * {@link AdapterCreationRule.PositionClassification} per
         * classified function-typed position in walk order (partial
         * when the walk failed mid-way; the empty surface outside
         * creation-rule-analysis mode).
         *
         * @return the classification fact surface; non-null
         */
        public AdapterCreationRule.CreationRuleFacts creationRuleFacts() {
            if (!creationRuleAnalysis) {
                return AdapterCreationRule.CreationRuleFacts.empty();
            }
            return new AdapterCreationRule.CreationRuleFacts(creationClassifications);
        }

        /**
         * The shape-map walk's complete emission fact surface (shape-map
         * mode): one {@link AdapterEmission} per emitted
         * {@code FUNCTION_ADAPT} op in emission order (partial when the
         * walk failed mid-way; the empty surface outside shape-map
         * mode).
         *
         * @return the adapter emission fact surface; non-null
         */
        public ShapeMapFacts shapeMapFacts() {
            if (!shapeMapAnalysis) {
                return ShapeMapFacts.empty();
            }
            return new ShapeMapFacts(shapeMapEmissions);
        }

        /**
         * Seeds the {@code int}/{@code number} intrinsic bindings at
         * module-init top (B1): exactly the root
         * {@code Symbol.IntrinsicSymbol} bindings of those two names
         * (shadowed-by-declaration names resolve to the user declaration,
         * never the intrinsic — the checker removes the root binding
         * before defining the shadow, so the symbol fact decides). Each
         * intrinsic binding gets one ALLOC (generation 0, {@code DIRECT},
         * not mutable) and one INIT whose operand is the pinned
         * intrinsic-function-value identity: a dedicated {@code ValueId}
         * allocated in the pinned order. No closed op produces an
         * intrinsic function value — the values seam has no
         * intrinsic-value arm and this child never implements
         * expression-value lowering — so the identity is wired as the
         * INIT operand and materialized by the invocation layer (E7); the
         * child emits no placeholder op, never a {@code CONST}, never a
         * closure.
         *
         * <p>The seeded identity also carries the closed
         * {@code IntrinsicFunction} registration ({@code kind} plus the
         * intrinsic's declared signature) through the registry child's
         * seed entry point, so the key is registered exactly once and
         * the bindings production validator's closed admission admits
         * exactly the seed's {@code BINDING_INIT} as its producing
         * position. The function-typed materialization that carries the
         * identity as a first-class value stays the function-value
         * child's: this walk emits neither a load of the intrinsic
         * binding nor an intrinsic carrier.</p>
         */
        private void seedIntrinsicBindings() {
            // The declared conversion intrinsics of the compilation
            // (ISSUE-0634): the project entry hands the session the closed
            // set the seed registers; the per-module entries keep the
            // closed two-member compiler constant. A module intrinsic
            // outside the declared set is a compiler-constant disagreement
            // — a producer defect, never a silently registered third
            // intrinsic.
            List<IntrinsicKind> declared = declaredConversionIntrinsics.isEmpty()
                ? List.of(IntrinsicKind.values()) : declaredConversionIntrinsics;
            for (String name : List.of("int", "number")) {
                if (!(checks.symbolTable().resolve(name)
                        instanceof Symbol.IntrinsicSymbol intrinsic)) {
                    continue;
                }
                IntrinsicKind kind = conversionIntrinsicKind(intrinsic.name());
                if (kind == null) {
                    throw new IllegalStateException("the intrinsic seed resolved '"
                        + name + "' to the non-conversion intrinsic '"
                        + intrinsic.name() + "' (producer defect)");
                }
                if (!declared.contains(kind)) {
                    throw new ConstructUnlowered("the module's conversion intrinsic '"
                        + name + "' is not part of the compilation's declared"
                        + " conversion intrinsics " + declared + " (a mismatch between"
                        + " the module's checker facts and the compiler constants is a"
                        + " producer defect)");
                }
                BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                    INITIAL_LOOP_GENERATION, moduleInitBlock, BindingCellKind.DIRECT,
                    false, BindingProducer.BINDING_ALLOC, false);
                registerBinding(name, binding, incarnation);
                if (proofAnalysis) {
                    // B7: intrinsic bindings (int/number) always carry
                    // the proof — builtin, unassignable — regardless of
                    // any assignment fact.
                    assignmentAnalysis.markIntrinsic(binding);
                }
                emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                    new KindPayload.BindingAllocPayload(binding, moduleInitBlock, false,
                        cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                    moduleInitSpan(), FailurePolicyId.NO_DEAL_FAILURE);
                ValueId intrinsicValue = ids.nextValueId(module, nextOrdinal++, 0);
                // The seeded intrinsic identity is the shape-map child's
                // VALUE-over-intrinsic operand (B7 arm (a)); it is
                // retained here so the adapted emission wires the exact
                // identity the intrinsic binding's cell holds.
                intrinsicIdentities.put(name, intrinsicValue);
                // The seed's closed registration: exactly one
                // IntrinsicFunction binding keyed by the seeded
                // identity, with the intrinsic's declared signature as
                // the checker's own symbol declares it (the closed gate
                // pins it against the kind's declared signature).
                registry.registerIntrinsic(
                    new FunctionAllocationIdentity(intrinsicValue.id()), kind,
                    (RuntimeDescriptor.Func) DescriptorService.describe(intrinsic.type()));
                // No static function-identity tracking for intrinsics: the
                // function-typed load of the intrinsic binding is the
                // function-value child's materialization; this walk never
                // emits an unvalidatable function-typed load.
                emitUserNullOp(SemanticOpKind.BINDING_INIT,
                    new KindPayload.BindingInitPayload(binding, INITIAL_LOOP_GENERATION,
                        intrinsicValue),
                    moduleInitSpan(), FailurePolicyId.NO_DEAL_FAILURE);
            }
        }

        /**
         * Hoists the module-level function-name ALLOCs and import-alias
         * ALLOCs to the top of the module-init block in declaration order
         * (B1: the retained per-scope pre-declaration shape; the
         * {@code CLOSURE_NEW} + {@code BINDING_INIT} stay at the
         * declaration position — the closure child's production). Only
         * top-level {@link FunctionDeclaration}/{@link ImportDeclaration}
         * statements hoist; nested-scope declarations allocate at their
         * position in the main walk. The group walk passes its module-
         * level group members so they register without an ALLOC op (the
         * group op's publication phase is their producing allocation).
         */
        private void hoistModuleLevelAllocs(List<StatementNode> statements) {
            hoistModuleLevelAllocs(statements, Set.of());
        }

        /**
         * Hoists the module-level names with the given module-level group
         * members excluded from {@code BINDING_ALLOC} emission (ISSUE-0446
         * group walk): a group member's name still registers — one
         * {@link BindingId} per declared name (B1) — with the
         * {@code RECURSIVE_GROUP_INIT} producing-allocation kind, the
         * pinned {@code SHARED_CELL} cell kind (B2: the closed group
         * payload records no cell-kind field, SCC mutual capture makes
         * every member captured, and members have no separate ALLOC/INIT),
         * and the member's pre-assigned allocation identity (the key the
         * registry's one {@code LoweredBody} per member consumes, B4/B5).
         */
        private void hoistModuleLevelAllocs(List<StatementNode> statements,
                                            Set<FunctionDeclaration> groupMembers) {
            for (StatementNode statement : statements) {
                if (statement instanceof ExportDeclaration exportDeclaration
                        && exportDeclaration.declaration()
                            instanceof FunctionDeclaration exported) {
                    statement = exported;
                }
                if (statement instanceof FunctionDeclaration function) {
                    BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                    boolean grouped = groupMembers.contains(function);
                    BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                        INITIAL_LOOP_GENERATION, moduleInitBlock,
                        grouped ? BindingCellKind.SHARED_CELL : BindingCellKind.DIRECT,
                        true, grouped ? BindingProducer.RECURSIVE_GROUP_INIT
                            : BindingProducer.BINDING_ALLOC,
                        grouped);
                    registerBinding(function.name(), binding, incarnation);
                    if (fullProgram) {
                        // The carrier's per-function reservation (forward
                        // references resolve deterministically): the
                        // lowered identity, the body block, the exact
                        // signature, and the single return-boundary and
                        // call-site op identities are pre-allocated here
                        // and reused by the declaration arm.
                        FunctionId functionId = ids.nextFunctionId(module, nextOrdinal++, 0);
                        BlockId bodyBlock = allocateBlock();
                        RuntimeDescriptor.Func signature =
                            functionSignatureOf(function);
                        OpId returnBoundaryOpId = ids.nextOpId(module, nextOrdinal++, 0);
                        OpId callSiteOpId = ids.nextOpId(module, nextOrdinal++, 0);
                        FunctionContext context = new FunctionContext(functionId,
                            bodyBlock, signature, returnBoundaryOpId, callSiteOpId);
                        if (e7Calls && isExported(function.name())
                                && !"main".equals(function.name())) {
                            // The exported function's reserved shape op
                            // identity (its EXTERNAL_ENTRY or
                            // CALLBACK_INVOKE op) — the RETURN ops'
                            // enclosing invocation resolves forward to
                            // the reserved id.
                            OpId shapeOpId = ids.nextOpId(module, nextOrdinal++, 0);
                            context.assignShape(
                                callbackExports.contains(function.name())
                                    ? InvocationShape.CALLBACK_SHAPE
                                    : InvocationShape.EXTERNAL_ENTRY_SHAPE,
                                shapeOpId);
                        }
                        functionContexts.put(incarnation, context);
                        moduleFunctionContexts.put(function.name(), context);
                        contextsByBindingId.put(binding, context);
                        contextsByFunctionId.put(functionId, context);
                    }
                    if (closureCore) {
                        // The function-allocation identity of the hoisted
                        // module-level function is pre-allocated here so a
                        // capture of a later-declared module function
                        // (B1; docs/spec-v1.2.md:1217-1221) — a
                        // function-typed load inside an earlier closure
                        // body — can publish the identity the cell will
                        // hold (loads preserve allocation identity; the
                        // declaration-position CLOSURE_NEW reuses this
                        // pre-allocated result identity, and a group
                        // member's publication phase publishes the same
                        // pre-assigned member identity).
                        ValueId closureIdentity = ids.nextValueId(module, nextOrdinal++, 0);
                        functionIdentity.put(incarnation, closureIdentity);
                    }
                    if (fullProgram) {
                        moduleFunctionIdentities.put(function.name(),
                            functionIdentity.get(incarnation));
                    }
                    if (grouped) {
                        // No BINDING_ALLOC for a group member: the
                        // RECURSIVE_GROUP_INIT op's publication phase
                        // publishes the member cell (B1/B4) — the closed
                        // payload records no cell-kind field, so the
                        // SHARED_CELL fact above is the only recording
                        // surface and the capture-driven rule yields
                        // SHARED_CELL for every member anyway (B2).
                        continue;
                    }
                    emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                        new KindPayload.BindingAllocPayload(binding, moduleInitBlock, true,
                            cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                        function.span(), FailurePolicyId.NO_DEAL_FAILURE);
                } else if (statement instanceof ImportDeclaration importDecl) {
                    BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                    BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                        INITIAL_LOOP_GENERATION, moduleInitBlock, BindingCellKind.DIRECT,
                        false, BindingProducer.BINDING_ALLOC, false);
                    registerBinding(importDecl.alias(), binding, incarnation);
                    importAliasBindings.add(binding);
                    importAliasCells.put(importDecl.alias(), binding);
                    emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                        new KindPayload.BindingAllocPayload(binding, moduleInitBlock, false,
                            cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                        importDecl.span(), FailurePolicyId.NO_DEAL_FAILURE);
                }
            }
        }

        /**
         * The binding-core statement walk (ISSUE-0444): exactly the
         * binding-relevant statement arms — let declarations, function
         * declarations (hoisted name ALLOCs plus parameter ALLOCs at the
         * body block's entry), the two-incarnation for-let shape, for-of
         * iteration bindings, try/catch bindings, import aliases (hoisted
         * — no position ops), and nested blocks. Every other statement is
         * a foreign construct in this child's window
         * ({@link ConstructUnlowered}).
         *
         * <p><b>Group-core mode (ISSUE-0446).</b> The walk partitions the
         * scope's function declarations into SCCs over the body-reference
         * graph first (B4): a size>=2 SCC lowers as one
         * {@code RECURSIVE_GROUP_INIT} op — nested-scope groups at the
         * first member's declaration position, module-level groups at
         * module-init top (already emitted by
         * {@link #lowerGroupModule}, so the walk skips every member) —
         * and a size-1 SCC — self-recursive declarations included —
         * lowers as {@code CLOSURE_NEW} + {@code BINDING_INIT} at the
         * declaration position (the closure child's arm).</p>
         */
        private void lowerBindingStatements(List<StatementNode> statements,
                                           boolean moduleLevel) {
            if (!groupCore) {
                for (StatementNode statement : statements) {
                    switch (statement) {
                        case FunctionDeclaration function ->
                            lowerBindingFunctionDecl(function, moduleLevel);
                        default -> lowerBindingStatement(statement);
                    }
                }
                return;
            }
            // Group-core mode: the per-scope SCC partition over function
            // declarations (name references in bodies, B4).
            Map<FunctionDeclaration, List<FunctionDeclaration>> memberGroups =
                groupMembership(statements);
            for (StatementNode statement : statements) {
                if (statement instanceof FunctionDeclaration function) {
                    if (skipGroupedFunctionDecl(function, memberGroups, moduleLevel)) {
                        continue;
                    }
                    lowerBindingFunctionDecl(function, moduleLevel);
                    continue;
                }
                lowerBindingStatement(statement);
            }
        }

        /**
         * The per-scope recursive-group membership of one statement list
         * (ISSUE-0634, the group walk's B4 partition): every size&gt;=2 SCC's
         * members mapped to their declaration-ordered SCC. Size-1 SCCs
         * carry no entry (the closure-arm lowers them at their declaration
         * position) and an empty map is returned outside group-core mode.
         *
         * @param statements the scope's statements; non-null
         * @return the member-to-group map in first-member declaration order
         */
        private Map<FunctionDeclaration, List<FunctionDeclaration>> groupMembership(
                List<StatementNode> statements) {
            if (!groupCore) {
                return Map.of();
            }
            List<FunctionDeclaration> declarations = new ArrayList<>();
            for (StatementNode statement : statements) {
                if (statement instanceof FunctionDeclaration function) {
                    declarations.add(function);
                }
            }
            Map<FunctionDeclaration, List<FunctionDeclaration>> memberGroups =
                new IdentityHashMap<>();
            for (List<FunctionDeclaration> scc
                    : partitionFunctionDeclarations(declarations)) {
                if (scc.size() >= 2) {
                    for (FunctionDeclaration member : scc) {
                        memberGroups.put(member, scc);
                    }
                }
            }
            return memberGroups;
        }

        /**
         * Handles one function declaration that belongs to a size&gt;=2 SCC:
         * a nested-scope group emits its single {@code RECURSIVE_GROUP_INIT}
         * op at the first member's declaration position (B4) and every
         * other member is skipped (the op publishes all member bindings at
         * once); a module-level group was emitted at module-init top by the
         * walk entry, so its members are skipped here.
         *
         * @param function       the declared function; non-null
         * @param memberGroups   the scope's member-to-group map; non-null
         * @param moduleLevel    whether the declaration sits at module top
         * @return {@code true} when the declaration was handled by the group
         *         arm (the caller must not lower it as a closure)
         */
        private boolean skipGroupedFunctionDecl(FunctionDeclaration function,
                Map<FunctionDeclaration, List<FunctionDeclaration>> memberGroups,
                boolean moduleLevel) {
            List<FunctionDeclaration> group = memberGroups.get(function);
            if (group == null) {
                return false;
            }
            if (!moduleLevel && group.get(0) == function) {
                lowerGroup(group, false);
            }
            return true;
        }

        /**
         * The binding walk's non-function statement arms (shared by the
         * binding/closure walk and the group walk): let declarations,
         * the two-incarnation for-let shape, for-of iteration bindings,
         * try/catch bindings, import aliases (hoisted — no position
         * ops), nested blocks, and assignment expression statements.
         * Every other statement is a foreign construct in this child's
         * window ({@link ConstructUnlowered}).
         */
        private void lowerBindingStatement(StatementNode statement) {
            switch (statement) {
                case VariableDeclaration decl -> lowerBindingVarDecl(decl);
                case ForStatement forStatement -> lowerBindingForLet(forStatement);
                case ForOfStatement forOf -> lowerBindingForOf(forOf);
                case TryStatement tryStatement -> lowerBindingTry(tryStatement);
                case ImportDeclaration ignored -> {
                    // The alias ALLOC was hoisted to module-init top
                    // (B1); the MODULE_IMPORT completion write is the
                    // modules epic's (ISSUE-0239).
                }
                case deal.ast.ExpressionStatement expressionStatement ->
                    lowerBindingExprStatement(expressionStatement);
                case Block block -> lowerBindingBlock(block);
                case ClassDeclaration classDeclaration -> {
                    if (!classCore) {
                        throw new ConstructUnlowered(describeStatement(statement));
                    }
                    lowerClassDeclaration(classDeclaration, false);
                }
                case ExportDeclaration exportDeclaration -> {
                    if (!(classCore
                            && exportDeclaration.declaration()
                                instanceof ClassDeclaration classDeclaration)) {
                        throw new ConstructUnlowered(describeStatement(statement));
                    }
                    lowerClassDeclaration(classDeclaration, true);
                }
                case deal.ast.DeleteStatement delete -> {
                    if (!classCore) {
                        throw new ConstructUnlowered(describeStatement(statement));
                    }
                    lowerDelete(delete);
                }
                default -> throw new ConstructUnlowered(describeStatement(statement));
            }
        }

        /**
         * The binding walk's expression-statement arm: exactly assignment
         * statements lower (the variable-assignment {@code BINDING_STORE}
         * commit naming the dominant incarnation is this child's op; the
         * chain's committed-value result is dropped exactly like the
         * for-let update block's — no {@code DISCARD}, which is E5's).
         * Every other expression statement is a foreign construct.
         */
        private void lowerBindingExprStatement(
                deal.ast.ExpressionStatement statement) {
            if (!(statement.expr() instanceof AssignmentExpr)) {
                throw new ConstructUnlowered("expression statement "
                    + describeExpression(statement.expr()) + " (DISCARD is E5's, "
                    + "ISSUE-0234; the binding walk admits assignment statements only)");
            }
            if (classCore) {
                // The class window's expression-statement arm (C-D8): the
                // committed value's producing ops already completed, then
                // one DISCARD audited in the op stream — never inferred
                // away (and the closed RETURN_EXPRESSION_STATEMENT
                // coverage row is satisfied through its pinned
                // DISCARD form).
                ValueId value = lowerExpression(statement.expr());
                emitNullOp(SemanticOpKind.DISCARD,
                    new KindPayload.DiscardPayload(value), statement.span(),
                    FailurePolicyId.NO_DEAL_FAILURE, SourceOriginKind.SYNTHETIC,
                    currentParent());
                return;
            }
            lowerExpression(statement.expr());
        }

        // ---------------------------------------------------------------------
        // The class-declaration arms (ISSUE-0511 declaration arm): class
        // layouts, CLASS_DEFAULT emission, CLASS_FACTORY registration, and
        // the CLASS_NEW literal arm (K-D2/K-D3/K-D4)
        // ---------------------------------------------------------------------

        /**
         * The class-declaration arm (K-D2/K-D3): one
         * {@link deal.semantic.ir.ClassLayout} per declared class keyed by
         * the checker-resolved {@link ClassId} in declaration order —
         * fields in declaration order with the declared descriptor
         * produced through the single {@link DescriptorService} producer,
         * the required-present marker ({@code !optional}), and
         * {@code defaultOwner LOCAL} (default expressions are never part
         * of a layout). For each defaulted field the arm emits exactly
         * one detached {@code CLASS_DEFAULT} op whose own default block
         * carries the lowered default expression — the
         * {@code CLASS_DEFAULT} op is a member of exactly its own default
         * block, the default-block ops record it as {@code parentOpId},
         * and only these default blocks enter the block-membership table
         * (K-D3). For an exported class the arm additionally emits one
         * detached static {@code CLASS_FACTORY} op (policy
         * {@code CLASS_CONSTRUCTION}, zero boundary children, zero return
         * boundaries, never part of the module-init flow) registered under
         * the pre-allocated
         * {@code ClassInterface.constructionEntry} id in the produced
         * {@link deal.semantic.ir.ClassFactoryRegistry} (K-D2);
         * non-exported classes get a layout but never a factory and never
         * a {@code ClassFactoryId}. Default application is gated on
         * required-present (K-D4 step 2: "applies defaults for omitted
         * required-present fields"): the factory payload's
         * {@code classDefaultOpIds} lists only required-present defaulted
         * fields' {@code CLASS_DEFAULT} op ids in declaration order — an
         * omitted optional-with-default field stays missing and its
         * default never runs, so its op id never enters the factory
         * payload (the {@code CLASS_DEFAULT} op itself is still emitted,
         * one per defaulted field per class).
         *
         * @param declaration the checked class declaration; non-null
         * @param exported    whether the declaration is module-level
         *                    export-wrapped
         * @throws ConstructUnlowered    on a fact defect (duplicate class,
         *         missing interface entry, unrepresentable field type)
         * @throws ClassDefaultCapture   on a default-block reference to an
         *         enclosing-region binding
         */
        private void lowerClassDeclaration(ClassDeclaration declaration, boolean exported) {
            ClassId classId = classIdOf(declaration);
            if (classLayouts.containsKey(classId)) {
                throw new ConstructUnlowered("duplicate class declaration '"
                    + declaration.name() + "' (the checker rejects duplicate class names; "
                    + "a second layout for " + classId + " is a fact defect)");
            }
            // The layout: one FieldLayout per declared field in declaration
            // order (K-D2).
            List<deal.semantic.ir.ClassLayout.FieldLayout> fields = new ArrayList<>();
            Map<String, RuntimeDescriptor> descriptors = new LinkedHashMap<>();
            for (ClassField field : declaration.fields()) {
                Type fieldType = fieldTypeOf(field.type());
                RuntimeDescriptor descriptor;
                try {
                    descriptor = DescriptorService.describe(fieldType);
                } catch (DescriptorService.Defect defect) {
                    throw new ConstructUnlowered("class field '" + declaration.name()
                        + "." + field.name() + "' of unrepresentable checked type "
                        + typeName(fieldType) + " (" + defect.getMessage() + ")");
                }
                fields.add(new deal.semantic.ir.ClassLayout.FieldLayout(field.name(),
                    descriptor, !field.optional(), DefaultOwner.LOCAL));
                descriptors.put(field.name(), descriptor);
            }
            deal.semantic.ir.ClassLayout layout =
                new deal.semantic.ir.ClassLayout(classId, fields);
            classLayouts.put(classId, layout);

            // CLASS_DEFAULT emission: one detached op per defaulted field in
            // declaration order (K-D3); only these default blocks enter the
            // block-membership table and each CLASS_DEFAULT op is a member of
            // exactly its own default block.
            List<OpId> classDefaultOpIds = new ArrayList<>();
            LinkedHashMap<String, ClassDefaultFact> defaults = new LinkedHashMap<>();
            for (ClassField field : declaration.fields()) {
                if (field.defaultExpr().isEmpty()) {
                    continue;
                }
                ExpressionNode defaultExpr = field.defaultExpr().get();
                BlockId defaultBlock = allocateBlock();
                ValueId slot = ids.nextValueId(module, nextOrdinal++, 0);
                AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
                OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
                // The detached structural op (K-D12: SYNTHETIC; no static
                // parent — the nesting owner is the triggering CLASS_NEW /
                // CLASS_FACTORY recorded in their payloads).
                SourceOrigin origin = new SourceOrigin(sourceId,
                    toSourceSpan(defaultExpr.span()), SourceOriginKind.SYNTHETIC,
                    anchor, null);
                SemanticOp op = buildOp(opId, SemanticOpKind.CLASS_DEFAULT,
                    new KindPayload.ClassDefaultPayload(classId, field.name(), defaultBlock),
                    slot, descriptors.get(field.name()), FailurePolicyId.NO_DEAL_FAILURE,
                    origin);
                pushBlock(defaultBlock);
                pushBlockParent(opId);
                Set<BlockId> internalBlocks =
                    java.util.Collections.newSetFromMap(new IdentityHashMap<>());
                DefaultContext context = new DefaultContext(defaultBlock, internalBlocks,
                    captureCollectors.size());
                defaultContexts.push(context);
                ValueId produced;
                try {
                    emit(op);
                    // The default expression's final producing op publishes
                    // the CLASS_DEFAULT op's result slot (the slot-threaded
                    // production — one value identity re-produced per
                    // construction execution, the LOOP(FOR) condition
                    // precedent). A function-typed default whose final
                    // producing op publishes the statically tracked
                    // function identity instead of the threaded slot — a
                    // function-typed binding reference's load — rebuilds
                    // the CLASS_DEFAULT op with that identity as its
                    // result, so R-FUNCTION-BINDING resolves the op's
                    // result through the identity's own
                    // FunctionExecutionBinding (K-D3:
                    // binding-referenced defaults pass the referenced
                    // value by reference; loads preserve allocation
                    // identity). The function-literal default's
                    // CLOSURE_NEW publishes the threaded slot itself, so
                    // no rebuild fires there.
                    produced = lowerExpression(defaultExpr, slot);
                    if (!produced.equals(slot)) {
                        op = buildOp(opId, SemanticOpKind.CLASS_DEFAULT,
                            new KindPayload.ClassDefaultPayload(classId, field.name(),
                                defaultBlock),
                            produced, descriptors.get(field.name()),
                            FailurePolicyId.NO_DEAL_FAILURE, origin);
                        List<SemanticOp> target = emitTarget();
                        for (int i = target.size() - 1; i >= 0; i--) {
                            if (target.get(i).opId().equals(opId)) {
                                target.set(i, op);
                                break;
                            }
                        }
                    }
                } finally {
                    defaultContexts.pop();
                    popBlockParent();
                    popBlock();
                }
                if (!field.optional()) {
                    classDefaultOpIds.add(opId);
                }
                defaults.put(field.name(), new ClassDefaultFact(opId, produced));
            }
            classDefaults.put(classId, defaults);

            // The generated C$fromJson/C$toJson function bodies (K-D8/
            // K-D10, ISSUE-0515): emitted for every @jsonable class
            // (exported or not) — the checker defines the synthetic
            // function symbols for every @jsonable class.
            if (declaration.isJsonable()) {
                lowerJsonFunctions(declaration, classId, layout, classDefaultOpIds);
            }

            if (!exported) {
                return;
            }
            // CLASS_FACTORY emission for exported classes (K-D2): the
            // pre-allocated constructionEntry from the module's own interface
            // index entry; zero boundary children and zero return boundaries;
            // detached static op, never part of the module-init flow.
            deal.semantic.ir.ClassInterface interfaceEntry = null;
            for (deal.semantic.ir.ClassInterface candidate : ownInterface.classes()) {
                if (candidate.classId().equals(classId)) {
                    interfaceEntry = candidate;
                    break;
                }
            }
            if (interfaceEntry == null) {
                throw new ConstructUnlowered("exported class " + classId
                    + " has no interface index entry (the index build derives one "
                    + "ClassInterface per exported class — a fact defect)");
            }
            OpId callerOpRef = ids.nextOpId(module, nextOrdinal++, 0);
            ValueId result = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId,
                toSourceSpan(declaration.span()), SourceOriginKind.SYNTHETIC, anchor, null);
            SemanticOp op = buildOp(opId, SemanticOpKind.CLASS_FACTORY,
                new KindPayload.ClassFactoryPayload(classId, List.copyOf(classDefaultOpIds),
                    callerOpRef),
                result, classDescriptorOf(declaration.name()),
                FailurePolicyId.CLASS_CONSTRUCTION, origin);
            // Detached emission: appended to the unit op list with no block
            // membership (the five-module-level-kind rule; the factory is
            // never part of the module-init flow).
            emitTarget().add(op);
            factoryRegistry.put(interfaceEntry.constructionEntry(), opId);
        }

        /**
         * The generated {@code @jsonable} function bodies (ISSUE-0515,
         * class-construction-jsonable-operations K-D8/K-D10; the
         * {@code js-v12-jsonable-completion}/{@code jvm-v12-json-completion}
         * generated {@code C$fromJson}/{@code C$toJson} shapes): for
         * every {@code @jsonable} class exactly two synthetic
         * module-level {@link LoweredFunction}s —
         * {@code C$fromJson(s: string): C|null} and
         * {@code C$toJson(v: C): string} — emitted as ordinary
         * {@code CLOSURE_NEW} producers (the closure-seam precedent: the
         * {@code CLOSURE_NEW} op at the declaration position, the
         * {@code LoweredFunction} record in {@code unit.functions}, and
         * the {@code FunctionExecutionBinding.LoweredBody} registration
         * through the {@link FunctionBindingRegistry} seam). The {@code $}
         * sigil names are compiler-reserved (the spec {@code $} rule;
         * the checker already defines the synthetic function symbols in
         * the root scope). Each body block carries exactly the parameter
         * {@code BINDING_ALLOC} at the body entry (the pinned parameter
         * model), the parameter {@code BINDING_LOAD}, and one JSON op:
         * {@code JSON_FROM_CLASS {layout, jsonString = the parameter
         * load result}} with policy {@code JSON_FROM_NULL} and result
         * type {@code ?class:<ClassId>}, or {@code JSON_TO_CLASS
         * {classValue = the parameter load result, layout}} with policy
         * {@code JSON_TO_ERROR} and result type {@code string} (the
         * validator-pinned policies and result types). The
         * {@code JSON_FROM_CLASS} op's per-site {@code CLASS_DEFAULT}
         * children are recorded in the produced
         * {@link deal.semantic.ir.JsonDefaultChildTable} record — the
         * class's required-present defaulted fields'
         * {@code CLASS_DEFAULT} op ids in declaration order (the
         * {@code classDefaultOpIds} list; the schema payload carries no
         * child list, K-D8 step 5). Export publication of the generated
         * functions is E10's — not emitted here. All ids/origins are
         * deterministic synthetic values, so repeated lowering is
         * byte-identical.
         *
         * @param declaration       the checked {@code @jsonable} class
         *                          declaration; non-null
         * @param classId           the checker-resolved class identity;
         *                          non-null
         * @param layout            the produced layout record of the
         *                          class; non-null
         * @param classDefaultOpIds the class's required-present defaulted
         *                          fields' {@code CLASS_DEFAULT} op ids in
         *                          declaration order; non-null
         */
        private void lowerJsonFunctions(ClassDeclaration declaration, ClassId classId,
                                        deal.semantic.ir.ClassLayout layout,
                                        List<OpId> classDefaultOpIds) {
            // The generated signatures flow from the checker's synthetic
            // C$fromJson/C$toJson function symbols through the single
            // DescriptorService producer (the producer-singularity rule:
            // no RuntimeDescriptor is ever constructed directly here).
            SymbolTable scope = currentCheckerScope();
            Symbol fromSymbol = scope == null ? null
                : scope.resolve(declaration.name() + "$fromJson");
            Symbol toSymbol = scope == null ? null
                : scope.resolve(declaration.name() + "$toJson");
            if (!(fromSymbol instanceof Symbol.FunctionSymbol fromFunction)
                    || !(toSymbol instanceof Symbol.FunctionSymbol toFunction)) {
                throw new ConstructUnlowered("the @jsonable class '"
                    + declaration.name() + "' has no checked C$fromJson/C$toJson "
                    + "function symbols (the checker defines the synthetic symbols for "
                    + "every @jsonable class — a fact defect)");
            }
            RuntimeDescriptor.Func fromSignature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(fromFunction.funcType());
            RuntimeDescriptor.Func toSignature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(toFunction.funcType());
            RuntimeDescriptor fromResult = fromSignature.returnType();
            RuntimeDescriptor toResult = toSignature.returnType();
            RuntimeDescriptor fromParameter = fromSignature.paramTypes().get(0);
            RuntimeDescriptor toParameter = toSignature.paramTypes().get(0);

            // C$fromJson(s: string): C|null — the walk records the
            // class's per-site CLASS_DEFAULT children (declaration
            // order) in the produced JsonDefaultChildTable record.
            OpId fromJsonOpId = lowerJsonFunction(declaration, layout, fromSignature,
                fromParameter, fromResult, FailurePolicyId.JSON_FROM_NULL, true);
            jsonDefaultChildren.put(fromJsonOpId, List.copyOf(classDefaultOpIds));

            // C$toJson(v: C): string.
            lowerJsonFunction(declaration, layout, toSignature, toParameter, toResult,
                FailurePolicyId.JSON_TO_ERROR, false);
        }

        /**
         * Emits one generated {@code @jsonable} function: the body block
         * (parameter {@code BINDING_ALLOC}, parameter {@code
         * BINDING_LOAD}, the single JSON op — the parameter load
         * result wired as the JSON payload's operand), then the
         * {@code CLOSURE_NEW} op publishing the fresh function identity
         * with the {@code LoweredFunction} record and the
         * {@code LoweredBody} registration through the registry seam,
         * and finally the buffered body ops flushed after the closure
         * (the closure-expression precedent's pinned unit order). The
         * JSON op's id is returned (the {@code JsonDefaultChildTable}
         * key of the {@code fromJson} arm).
         */
        private OpId lowerJsonFunction(ClassDeclaration declaration,
                                       deal.semantic.ir.ClassLayout layout,
                                       RuntimeDescriptor.Func signature,
                                       RuntimeDescriptor parameterDescriptor,
                                       RuntimeDescriptor jsonResultType,
                                       FailurePolicyId jsonPolicy,
                                       boolean fromJson) {
            BlockId bodyBlock = allocateBlock();
            FunctionId functionId = ids.nextFunctionId(module, nextOrdinal++, 0);
            ValueId closureIdentity = ids.nextValueId(module, nextOrdinal++, 0);
            List<SemanticOp> bodyOps = new ArrayList<>();
            emitTargets.push(bodyOps);
            blockStack.push(bodyBlock);
            OpId jsonOpId;
            try {
                // The parameter ALLOC at the body entry (the pinned
                // parameter model: DIRECT, mutable, generation 0, the
                // body-root block).
                BindingId parameterBinding = ids.nextBindingId(module, nextOrdinal++, 0);
                BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                    INITIAL_LOOP_GENERATION, bodyBlock, BindingCellKind.DIRECT,
                    true, BindingProducer.BINDING_ALLOC, false);
                parameterBindings.add(parameterBinding);
                AnchorId allocAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
                OpId allocOpId = ids.nextOpId(module, nextOrdinal++, 0);
                SourceOrigin allocOrigin = new SourceOrigin(sourceId,
                    toSourceSpan(declaration.span()), SourceOriginKind.SYNTHETIC,
                    allocAnchor, null);
                emit(buildOp(allocOpId, SemanticOpKind.BINDING_ALLOC,
                    new KindPayload.BindingAllocPayload(parameterBinding, bodyBlock, true,
                        cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                    null, null, FailurePolicyId.NO_DEAL_FAILURE, allocOrigin));

                // The parameter load: the generated body's only operand
                // producer.
                ValueId loadValue = ids.nextValueId(module, nextOrdinal++, 0);
                AnchorId loadAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
                OpId loadOpId = ids.nextOpId(module, nextOrdinal++, 0);
                SourceOrigin loadOrigin = new SourceOrigin(sourceId,
                    toSourceSpan(declaration.span()), SourceOriginKind.SYNTHETIC,
                    loadAnchor, null);
                emit(buildOp(loadOpId, SemanticOpKind.BINDING_LOAD,
                    new KindPayload.BindingLoadPayload(parameterBinding,
                        INITIAL_LOOP_GENERATION),
                    loadValue, parameterDescriptor, FailurePolicyId.NO_DEAL_FAILURE,
                    loadOrigin));

                // The single JSON op of the body: payload-referenced
                // operand wiring (the FIELD_READ precedent), the pinned
                // policy and result type, a SYNTHETIC origin at the class
                // declaration span.
                ValueId jsonResult = ids.nextValueId(module, nextOrdinal++, 0);
                AnchorId jsonAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
                jsonOpId = ids.nextOpId(module, nextOrdinal++, 0);
                SourceOrigin jsonOrigin = new SourceOrigin(sourceId,
                    toSourceSpan(declaration.span()), SourceOriginKind.SYNTHETIC,
                    jsonAnchor, null);
                KindPayload payload = fromJson
                    ? new KindPayload.JsonFromClassPayload(layout, loadValue)
                    : new KindPayload.JsonToClassPayload(loadValue, layout);
                emit(buildOp(jsonOpId,
                    fromJson ? SemanticOpKind.JSON_FROM_CLASS : SemanticOpKind.JSON_TO_CLASS,
                    payload, jsonResult, jsonResultType, jsonPolicy, jsonOrigin));
            } finally {
                blockStack.pop();
                emitTargets.pop();
            }
            // The CLOSURE_NEW producer: the fresh function identity, the
            // LoweredFunction record, and the LoweredBody registration
            // through the registry seam (generated synthetics are
            // ordinary CLOSURE_NEW producers).
            AnchorId closureAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId closureOpId = ids.nextOpId(module, nextOrdinal++, 0);
            FunctionExecutionBinding.LoweredBody binding =
                new FunctionExecutionBinding.LoweredBody(functionId, bodyBlock);
            SourceOrigin closureOrigin = new SourceOrigin(sourceId,
                toSourceSpan(declaration.span()), SourceOriginKind.SYNTHETIC,
                closureAnchor, currentParent());
            emit(buildOp(closureOpId, SemanticOpKind.CLOSURE_NEW,
                new KindPayload.ClosureNewPayload(functionId, signature, List.of(), binding),
                closureIdentity, signature, FailurePolicyId.NO_DEAL_FAILURE,
                closureOrigin));
            functions.put(functionId, new LoweredFunction(functionId, signature, List.of(),
                bodyBlock));
            registry.registerClosure(new FunctionAllocationIdentity(closureIdentity.id()),
                functionId, bodyBlock);
            emitTarget().addAll(bodyOps);
            return jsonOpId;
        }

        /**
         * {@code CLASS_NEW} — the class-typed object-literal arm of the
         * class walk (K-D4's closed payload shape; ISSUE-0511, extended
         * by the ISSUE-0514 SHARED_FACTORY arm): the provided-value
         * operands complete in literal order before the op, the payload
         * records {@code providedFields} in literal order,
         * {@code classDefaultOpIds} for omitted required-present
         * defaulted fields in declaration order (LOCAL default
         * application, K-D4 step 2 — empty under SHARED_FACTORY, whose
         * defaults transfer to the owner's {@code CLASS_FACTORY}), and
         * {@code fieldBoundaries} in declaration order —
         * {@code CLASS_LITERAL_FIELD} per provided field with input =
         * the provided value, {@code CLASS_DEFAULT_FIELD} per omitted
         * required-present defaulted field with input = the field's
         * {@code CLASS_DEFAULT} child result (LOCAL, K-D4 input wiring)
         * or the owner {@code CLASS_FACTORY} op's result {@code ValueId}
         * (SHARED_FACTORY, the K-D4 cross-unit D4-global reference —
         * the executor's extraction rule reads the transferred
         * instance's named field); omitted optional fields get no
         * boundary and no default op id, defaulted or not — an
         * optional-with-default field's default never runs at
         * construction and the field stays missing.
         * The op carries policy {@code CLASS_CONSTRUCTION} and publishes a
         * fresh tagged-instance value ({@code class:<ClassId>}); the
         * boundary children record the {@code CLASS_NEW} op as
         * {@code parentOpId}. A literal of an imported class with the
         * owner's shared-factory facts lowers {@code defaultOwner:
         * SHARED_FACTORY} with {@code classFactoryRef} = the interface's
         * pre-allocated {@code constructionEntry} (K-D4/K-D5); a literal
         * of an imported class without facts defers to E10
         * ({@code RETAINED_ABI_DEFERRED}) and is never silently emitted
         * as SHARED_FACTORY. Same-module literals stay LOCAL.
         *
         * @param literal the checked class-typed object literal; non-null
         * @param slot    the result slot of the final producing op, or
         *                {@code null} to allocate one
         * @return the produced {@code ValueId} (the slot when given)
         * @throws ConstructUnlowered on a shape outside this arm
         * @throws RetainedAbiDeferred on an imported class without the
         *         owner's shared-factory facts (the E10 deferral)
         */
        private ValueId lowerClassLiteral(ObjectLiteralExpr literal, ValueId slot) {
            Type type = checkedType(literal);
            if (!(type instanceof Type.Class classType)) {
                throw new ConstructUnlowered("class literal of non-class checked type "
                    + typeName(type) + " (a class-typed ObjectLiteralExpr must carry a "
                    + "Type.Class fact)");
            }
            ClassId classId = new ClassId(
                DescriptorService.semanticModulePath(classType.identity()), classType.name());
            // The closed owner lookup order (ISSUE-0634; design sources
            // {@code project-lowering-entry-and-registration-seeds} D4 and
            // the project lowering contract): the unit's own declared layout
            // -> LOCAL (a locally declared class stays LOCAL, T2's arm); the
            // in-project factory facts -> SHARED_FACTORY (K-D4/K-D5); a
            // project registration seed -> the seed's owner member; none ->
            // the fail-closed E10 deferral (never silently emitted and never
            // executed here). The seeds are the project-level layout
            // resolution context, consulted after the unit's own declared
            // layouts and never merged into them.
            deal.semantic.ir.ClassLayout layout = classLayouts.get(classId);
            DefaultOwner defaultOwner = DefaultOwner.LOCAL;
            deal.semantic.ir.ClassFactoryId classFactoryRef = null;
            ValueId sharedFactoryResult = null;
            SharedFactoryFacts sharedFacts = null;
            if (layout == null) {
                sharedFacts = sharedFactories.get(classId);
                if (sharedFacts != null) {
                    layout = sharedFacts.layout();
                    defaultOwner = DefaultOwner.SHARED_FACTORY;
                    classFactoryRef = sharedFacts.interfaceEntry().constructionEntry();
                    sharedFactoryResult = sharedFacts.factoryResult();
                } else {
                    ClassRegistrationSeeds.ClassRegistration seed =
                        registrationSeeds.registrationFor(classId);
                    if (seed == null) {
                        throw new RetainedAbiDeferred(classId.text());
                    }
                    // A registration seed: the class's layout and its closed
                    // owner member (HOST_DEFAULTS for a host declaration
                    // class, FFI_PLAN for an extern-C declaration class,
                    // BUILTIN_DEFAULTS for the builtin Error). The emitted
                    // CLASS_NEW carries the seed's owner fact; the
                    // construction of a seeded owner is the construction
                    // children's, so the composed gate rejects the op
                    // fail-closed — a registration fact is never silently
                    // executed as another owner.
                    layout = seed.layout();
                    defaultOwner = seed.owner();
                }
            }
            // Provided values complete in literal order (K-D4 step 1).
            List<KindPayload.ProvidedField> providedFields = new ArrayList<>();
            Map<String, ValueId> providedValues = new LinkedHashMap<>();
            Map<String, Span> providedSpans = new LinkedHashMap<>();
            for (Property property : literal.properties()) {
                ValueId value = lowerExpression(property.value());
                providedFields.add(new KindPayload.ProvidedField(property.name(), value));
                providedValues.put(property.name(), value);
                providedSpans.put(property.name(), property.span());
            }
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            // Default application and field validation in declaration order
            // (K-D4 steps 2 and 5): the boundary children are built first so
            // the payload names their op ids, then emitted as children.
            // LOCAL wires the field's CLASS_DEFAULT child result;
            // SHARED_FACTORY wires the owner CLASS_FACTORY op's result
            // ValueId (the K-D4 cross-unit D4-global reference) and records
            // no classDefaultOpIds (the owner's factory carries them).
            List<OpId> classDefaultOpIds = new ArrayList<>();
            List<KindPayload.FieldBoundary> boundaries = new ArrayList<>();
            List<SemanticOp> children = new ArrayList<>();
            Map<String, ClassDefaultFact> facts = classDefaults.get(classId);
            for (deal.semantic.ir.ClassLayout.FieldLayout field : layout.fields()) {
                ValueId provided = providedValues.get(field.name());
                if (provided != null) {
                    SemanticOp child = buildFieldBoundary(BoundaryKind.CLASS_LITERAL_FIELD,
                        field.descriptor(), provided, providedSpans.get(field.name()), opId);
                    boundaries.add(new KindPayload.FieldBoundary(field.name(),
                        BoundaryKind.CLASS_LITERAL_FIELD, child.opId()));
                    children.add(child);
                    continue;
                }
                if (defaultOwner == DefaultOwner.SHARED_FACTORY) {
                    // An omitted required-present field of an imported class
                    // is always defaulted (the checker's E4001 rejects a
                    // no-default omitted required field); the owner's factory
                    // fills exactly those fields, so the boundary wires the
                    // factory result (the K-D4 extraction rule). The
                    // interface fact is re-checked fail closed — never
                    // inferred.
                    if (field.required()) {
                        if (!sharedFacts.hasDeclaredDefault(field.name())) {
                            throw new ConstructUnlowered("omitted required-present field '"
                                + field.name() + "' of imported class " + classId
                                + " without a declared default (the checker's E4001 "
                                + "rejects the shape — a fact defect, never an invented "
                                + "default)");
                        }
                        SemanticOp child = buildFieldBoundary(
                            BoundaryKind.CLASS_DEFAULT_FIELD, field.descriptor(),
                            sharedFactoryResult, literal.span(), opId);
                        boundaries.add(new KindPayload.FieldBoundary(field.name(),
                            BoundaryKind.CLASS_DEFAULT_FIELD, child.opId()));
                        children.add(child);
                    }
                    // An omitted optional field stays missing: no boundary.
                    continue;
                }
                ClassDefaultFact fact = facts == null ? null : facts.get(field.name());
                if (fact != null && field.required()) {
                    SemanticOp child = buildFieldBoundary(BoundaryKind.CLASS_DEFAULT_FIELD,
                        field.descriptor(), fact.result(), literal.span(), opId);
                    classDefaultOpIds.add(fact.opId());
                    boundaries.add(new KindPayload.FieldBoundary(field.name(),
                        BoundaryKind.CLASS_DEFAULT_FIELD, child.opId()));
                    children.add(child);
                }
                // An omitted optional field stays missing: no boundary.
            }
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(literal.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.CLASS_NEW,
                new KindPayload.ClassNewPayload(classId, layout, providedFields,
                    defaultOwner, classDefaultOpIds, classFactoryRef, boundaries),
                result, ContainerPayloadDescriptors.resultDescriptorOf(classType),
                FailurePolicyId.CLASS_CONSTRUCTION, origin));
            for (SemanticOp child : children) {
                emit(child);
            }
            return result;
        }

        /**
         * Builds (without emitting) one {@code CLASS_NEW} field-boundary
         * child (K-D4 step 5): kind, the field's declared descriptor, the
         * pinned input, the descriptor-kind policy, the canonical
         * runtime-validation realization, {@code parentOpId} = the
         * {@code CLASS_NEW} op id, and a {@code SYNTHETIC} origin at the
         * given span (the {@code ARRAY_NEW} element-boundary precedent).
         */
        private SemanticOp buildFieldBoundary(BoundaryKind kind, RuntimeDescriptor descriptor,
                                              ValueId input, Span span, OpId classNewOpId) {
            return buildNullOp(SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(kind, descriptor, input,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                span, descriptorKindPolicy(descriptor), SourceOriginKind.SYNTHETIC,
                classNewOpId);
        }

        /**
         * The checker-resolved class identity of one class declaration
         * (ISSUE-0634; design sources
         * {@code project-lowering-entry-and-registration-seeds} D4 and
         * the project lowering contract): the checked
         * {@code ClassSymbol}'s canonical identity projected through the
         * single {@link DescriptorService} module-path producer — the
         * same producer the class-literal, field-access, and
         * class-descriptor arms use, so a unit's own
         * {@code classLayouts} key, its {@code CLASS_NEW} payloads, its
         * class-typed descriptors, and the interface index's
         * {@code ClassInterface} are one identity ({@code ClassSymbol}'s
         * {@code modulePath} is the private deployment wiring key and
         * never renders descriptor text). A declaration without a
         * checked {@code ClassSymbol} is a producer defect.
         */
        private ClassId classIdOf(ClassDeclaration declaration) {
            SymbolTable scope = currentCheckerScope();
            Symbol symbol = scope == null ? null : scope.resolve(declaration.name());
            if (!(symbol instanceof Symbol.ClassSymbol classSymbol)) {
                throw new ConstructUnlowered("class declaration '"
                    + declaration.name() + "' has no checked ClassSymbol (a missing "
                    + "checker fact is a producer defect)");
            }
            return new ClassId(
                DescriptorService.semanticModulePath(classSymbol.identity()),
                classSymbol.name());
        }

        /**
         * The class descriptor of a locally declared class (the factory's
         * result type): the checked {@code Type.Class} of the checker's
         * {@code ClassSymbol} rendered through the single
         * {@link DescriptorService} producer — never a hand-built
         * descriptor (the producer-singularity rule).
         */
        private RuntimeDescriptor classDescriptorOf(String name) {
            SymbolTable scope = currentCheckerScope();
            Symbol symbol = scope == null ? null : scope.resolve(name);
            if (!(symbol instanceof Symbol.ClassSymbol classSymbol)) {
                throw new ConstructUnlowered("class declaration '" + name
                    + "' has no checked ClassSymbol (a missing checker fact is a "
                    + "producer defect)");
            }
            try {
                return DescriptorService.describe(
                    deal.types.Types.classType(classSymbol.name(), classSymbol.identity()));
            } catch (DescriptorService.Defect defect) {
                throw new ConstructUnlowered("class '" + name
                    + "' of unrepresentable checked type (" + defect.getMessage() + ")");
            }
        }

        /**
         * The checked {@link Type} of a class-field annotation (K-D2: the
         * layout descriptors are produced from the checked field types
         * through {@link DescriptorService}): the checker-fact mirror of
         * {@code NameResolver.resolveTypeNode} resolved against the
         * current checker scope (the scope the checker resolved the
         * annotation in — D4: no {@code NameResolver} instance is
         * retained). An unresolvable annotation is a producer defect.
         */
        private Type fieldTypeOf(deal.ast.TypeNode node) {
            return switch (node) {
                case deal.ast.NamedType named -> resolveNamedFieldType(named);
                case deal.ast.QualifiedType qualified -> resolveQualifiedFieldType(qualified);
                case deal.ast.ArrayType array -> deal.types.Types.array(
                    fieldTypeOf(array.elementType()));
                case deal.ast.NullableType nullable -> deal.types.Types.nullable(
                    fieldTypeOf(nullable.innerType()));
                case deal.ast.FunctionType function -> {
                    List<Type> paramTypes = new ArrayList<>();
                    for (deal.ast.FunctionTypeParam parameter : function.params()) {
                        paramTypes.add(fieldTypeOf(parameter.type()));
                    }
                    yield new Type.Func(List.copyOf(paramTypes),
                        fieldTypeOf(function.returnType()), function.isAsync());
                }
            };
        }

        /** The checker-fact mirror of {@code NameResolver.resolveNamedType}. */
        private Type resolveNamedFieldType(deal.ast.NamedType named) {
            String name = named.name();
            return switch (name) {
                case "null" -> Type.Null.INSTANCE;
                case "boolean" -> Type.Boolean.INSTANCE;
                case "int" -> Type.Int.INSTANCE;
                case "number" -> Type.Number.INSTANCE;
                case "string" -> Type.String.INSTANCE;
                case "table" -> Type.Table.INSTANCE;
                case "Error" -> deal.types.Types.classType("Error",
                    deal.checker.NameResolver.intrinsicErrorIdentity());
                case "bytes" -> {
                    Symbol symbol = resolveScopeName(name);
                    if (symbol instanceof Symbol.ClassSymbol classSymbol) {
                        yield deal.types.Types.classType(classSymbol.name(),
                            classSymbol.identity());
                    }
                    yield Type.Bytes.INSTANCE;
                }
                default -> {
                    Symbol symbol = resolveScopeName(name);
                    if (symbol instanceof Symbol.ClassSymbol classSymbol) {
                        yield deal.types.Types.classType(classSymbol.name(),
                            classSymbol.identity());
                    }
                    throw new ConstructUnlowered("class-field type annotation names unknown "
                        + "type '" + name + "' (a checked module cannot reach this arm — "
                        + "a fact defect, never an invented type)");
                }
            };
        }

        /** The checker-fact mirror of {@code NameResolver.resolveQualifiedType}. */
        private Type resolveQualifiedFieldType(deal.ast.QualifiedType qualified) {
            Symbol symbol = resolveScopeName(qualified.moduleName());
            if (!(symbol instanceof Symbol.ModuleSymbol moduleSymbol)) {
                throw new ConstructUnlowered("class-field type annotation qualifies unknown "
                    + "module '" + qualified.moduleName() + "' (a checked module cannot "
                    + "reach this arm — a fact defect)");
            }
            Type exportType = moduleSymbol.exports().get(qualified.typeName());
            if (exportType == null) {
                throw new ConstructUnlowered("class-field type annotation names unknown "
                    + "export '" + qualified.typeName() + "' of module '"
                    + qualified.moduleName() + "' (a fact defect)");
            }
            return exportType;
        }

        /** Resolves one annotation name against the current checker scope. */
        private Symbol resolveScopeName(String name) {
            SymbolTable scope = currentCheckerScope();
            return scope == null ? null : scope.resolve(name);
        }

        /**
         * The produced factory-registration record of the session (K-D2):
         * the insertion-ordered {@code constructionEntry}&#8594;factory
         * bindings of the exported classes.
         */
        public deal.semantic.ir.ClassFactoryRegistry factoryRegistry() {
            return new deal.semantic.ir.ClassFactoryRegistry(
                new LinkedHashMap<>(factoryRegistry));
        }

        /**
         * The produced JSON default-child record of the session (K-D8):
         * the insertion-ordered {@code JSON_FROM_CLASS}&#8594;per-site
         * {@code CLASS_DEFAULT} child bindings of the {@code @jsonable}
         * classes.
         */
        public deal.semantic.ir.JsonDefaultChildTable jsonDefaultChildren() {
            return new deal.semantic.ir.JsonDefaultChildTable(
                new LinkedHashMap<>(jsonDefaultChildren));
        }

        /**
         * The binding walk's {@code let} arm: one ALLOC (generation 0,
         * {@code DIRECT}, mutable — the closed default cell kind for
         * ordinary declarations), the initializer's value ops through the
         * value-expression seam, the declaration boundary for annotated
         * declarations ({@code VARIABLE_DECLARATION} with the declared
         * descriptor and the descriptor-kind policy; inferred
         * declarations carry no boundary and init directly — the Binding
         * lifecycle contract shape), then exactly one BINDING_INIT. The
         * binding is registered before the initializer lowers (the
         * checker defines the name before walking the initializer), so
         * pre-init stores resolve the generation-0 incarnation.
         */
        private void lowerBindingVarDecl(VariableDeclaration decl) {
            BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
            BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                INITIAL_LOOP_GENERATION, currentBlock(), BindingCellKind.DIRECT,
                true, BindingProducer.BINDING_ALLOC, false);
            registerBinding(decl.name(), binding, incarnation);
            emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                new KindPayload.BindingAllocPayload(binding, currentBlock(), true,
                    cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            if ((shapeMapAnalysis || e7Calls) && declaredTypeOf(decl) instanceof Type.Func) {
                Type sourceType = checkedType(decl.initializer());
                if (AdapterCreationRule.variableDisposition(sourceType,
                        declaredTypeOf(decl)) == AdapterCreationRule.Disposition.ADAPT) {
                    // The shape-map child's adapted declaration (B6-B9):
                    // exactly one FUNCTION_ADAPT op with its closed-map
                    // mode and per-mode payload from birth, produced
                    // before the position's boundary and wired as the
                    // direct input of exactly the position's own
                    // VARIABLE_DECLARATION boundary chain (an inferred
                    // declaration's result feeds its BINDING_INIT
                    // directly).
                    lowerAdaptedVarDecl(decl, binding, incarnation);
                    return;
                }
            }
            ValueId value = lowerExpression(decl.initializer());
            OpId declarationBoundary = null;
            if (decl.typeAnnotation().isPresent()) {
                RuntimeDescriptor descriptor =
                    ContainerPayloadDescriptors.resultDescriptorOf(declaredTypeOf(decl));
                FailurePolicyId boundaryPolicy = descriptor instanceof RuntimeDescriptor.Func
                    ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
                declarationBoundary = emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.VARIABLE_DECLARATION,
                        descriptor, value,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    decl.span(), boundaryPolicy, SourceOriginKind.SYNTHETIC, null);
            }
            if (closureCore && descriptorOf(value) instanceof RuntimeDescriptor.Func) {
                // The initializer's function identity is the cell's
                // current value identity (loads preserve allocation
                // identity; R-FUNCTION-BINDING holds by construction).
                functionIdentity.put(incarnation, value);
            }
            OpId initOp = emitUserNullOp(SemanticOpKind.BINDING_INIT,
                new KindPayload.BindingInitPayload(binding, INITIAL_LOOP_GENERATION, value),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            if (creationRuleAnalysis) {
                classifyVarDeclPosition(decl, value, declarationBoundary, initOp);
            }
        }

        /**
         * The shape-map child's adapted {@code let} declaration (B6-B9):
         * the closed mode map selects exactly one mode from checker
         * facts (B7), the per-mode payload is built from birth (B8),
         * and exactly one {@code FUNCTION_ADAPT} op is emitted before
         * the position's boundary — its result wired as the direct
         * input of exactly the position's own
         * {@code VARIABLE_DECLARATION} boundary chain (the boundary
         * observes an exact-signature adapter value and passes), or as
         * the {@code BINDING_INIT} operand of an inferred declaration
         * (no boundary op exists there). The adapter emits zero
         * {@code BOUNDARY} ops of its own; its fresh allocation
         * identity registers exactly one {@code AdapterBinding}
         * through the registry child's seam; the cell's tracked
         * function identity becomes the adapter identity (loads/reads/
         * passes/returns preserve it).
         *
         * <p><b>Per-mode creation (B8, exactly).</b> VALUE completes its
         * single operand at creation — the {@code CLOSURE_NEW} result,
         * the intrinsic function-value identity, or the single proved
         * {@code BINDING_LOAD} at the proof's generation — and retains
         * that identity; the payload's {@code proof} is present iff the
         * operand is a binding load. SHARED_CELL evaluates nothing and
         * records {@code SharedCell {binding, generation}} naming the
         * dominant incarnation at the position; the incarnation joins
         * the B2 cell-kind derivation's capture-reference union (the
         * shape-map child's SHARED_CELL arm). REEVALUATE_THUNK
         * evaluates nothing at the creation site: the source
         * expression's already-lowered ops live only inside a fresh
         * detached thunk block whose {@code capturedBindings} pin the
         * thunk's free bindings, generation-pinned, ordered by first
         * reference (the thunk builder's production; the captures join
         * the B2 derivation through the walk's registration surface —
         * the shape-map child's thunk arm).</p>
         *
         * @param decl        the adapted declaration; non-null
         * @param binding     the declared name's {@link BindingId}; non-null
         * @param incarnation the declared name's generation-0
         *                    incarnation; non-null
         */
        private void lowerAdaptedVarDecl(VariableDeclaration decl, BindingId binding,
                                         BindingCoreIncarnation incarnation) {
            Type.Func sourceType = (Type.Func) checkedType(decl.initializer());
            Type.Func targetType = (Type.Func) declaredTypeOf(decl);
            RuntimeDescriptor.Func sourceSignature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(sourceType);
            RuntimeDescriptor.Func targetSignature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(targetType);
            Optional<BindingImmutabilityProof> proof = sourceProofOf(decl.initializer());
            AdapterShapeMap.SourceShape shape = AdapterShapeMap.sourceShapeOf(
                decl.initializer(), name -> checks.symbolTable().resolve(name));
            CaptureMode mode = AdapterShapeMap.selectMode(shape, proof);
            ThunkSource thunk = null;
            ValueId operand = null;
            BindingImmutabilityProof payloadProof = null;
            AdaptSourceRef sourceRef;
            List<ValueId> operands;
            List<RuntimeDescriptor> operandTypes;
            switch (mode) {
                case VALUE -> {
                    if (shape == AdapterShapeMap.SourceShape.INTRINSIC_FUNCTION_VALUE) {
                        // B7 arm (a): a first-class intrinsic function
                        // value — the seeded intrinsic identity is the
                        // materialized operand; no function-typed load
                        // of the intrinsic binding is emitted (a
                        // first-class intrinsic value has no closed
                        // FunctionExecutionBinding shape, B5).
                        String name = ((IdentifierExpr) decl.initializer()).name();
                        operand = intrinsicIdentities.get(name);
                        if (operand == null) {
                            throw new IllegalStateException("the intrinsic identity of '"
                                + name + "' was not seeded at module-init top (producer "
                                + "defect)");
                        }
                    } else {
                        operand = lowerExpression(decl.initializer());
                        if (shape == AdapterShapeMap.SourceShape.BINDING_REFERENCE) {
                            // B7 arm (b): the single proved BINDING_LOAD
                            // at the proof's generation — the payload
                            // proof must name that binding/generation
                            // (the load emission resolves the dominant
                            // incarnation, the same resolution the
                            // proof fact names).
                            payloadProof = proof.orElseThrow(() ->
                                new IllegalStateException("the closed shape map selects "
                                    + "VALUE over a binding only with the recorded proof "
                                    + "(producer defect)"));
                        }
                    }
                    sourceRef = new AdaptSourceRef.Value(operand);
                    operands = List.of(operand);
                    operandTypes = List.of(sourceSignature);
                }
                case SHARED_CELL -> {
                    IdentifierExpr identifier = (IdentifierExpr) decl.initializer();
                    FrameResolution resolution = resolveFrame(identifier.name());
                    if (resolution == null) {
                        throw new ConstructUnlowered("the SHARED_CELL source '"
                            + identifier.name() + "' is not a declared binding of the "
                            + "walk's environment (B7: a binding source resolves its "
                            + "dominant incarnation at the adaptation position)");
                    }
                    // The B2 capture arm: the SharedCell source reference
                    // makes the incarnation a shared cell (its cell is
                    // read per invocation, so later writes are observed);
                    // inside a detached body the enclosing closure must
                    // also capture the binding (the detaching chain).
                    maybeRegisterCapture(identifier.name(), resolution);
                    cellKinds.registerCaptureReference(resolution.entry().incarnation());
                    sourceRef = new AdaptSourceRef.SharedCell(
                        resolution.entry().cell().id,
                        resolution.entry().incarnation().generation());
                    operands = List.of();
                    operandTypes = List.of();
                }
                case REEVALUATE_THUNK -> {
                    thunk = lowerThunkSource(decl.initializer());
                    sourceRef = thunkSourceRef(thunk);
                    operands = List.of();
                    operandTypes = List.of();
                }
                default -> throw new IllegalStateException("unreachable mode " + mode);
            }
            EmittedAdapter adapter = emitFunctionAdapt(mode, sourceRef, sourceSignature,
                targetSignature, payloadProof, operands, operandTypes, decl.span());
            ValueId adapterIdentity = adapter.identity();
            OpId declarationBoundary = null;
            if (decl.typeAnnotation().isPresent()) {
                declarationBoundary = emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.VARIABLE_DECLARATION,
                        targetSignature, adapterIdentity,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    decl.span(), FailurePolicyId.FUNCTION_SIGNATURE,
                    SourceOriginKind.SYNTHETIC, null);
            }
            // The cell's tracked function identity becomes the adapter
            // identity — loads, reads, argument passing, and returns
            // preserve it (the adapter is an ordinary function value
            // after the commit).
            functionIdentity.put(incarnation, adapterIdentity);
            OpId initOp = emitUserNullOp(SemanticOpKind.BINDING_INIT,
                new KindPayload.BindingInitPayload(binding, INITIAL_LOOP_GENERATION,
                    adapterIdentity),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            OpId wiringTarget = declarationBoundary != null ? declarationBoundary : initOp;
            recordAdapterEmission(adapter.opId(), adapterIdentity, mode, sourceRef,
                sourceSignature, targetSignature, payloadProof, wiringTarget,
                BoundaryKind.VARIABLE_DECLARATION);
            if (thunk != null) {
                emitTarget().addAll(thunk.ops());
            }
            if (creationRuleAnalysis) {
                classifyVarDeclPosition(decl, adapterIdentity, declarationBoundary, initOp);
            }
        }

        /**
         * One detached thunk-block source of the shape-map child
         * (B8): the fresh block wrapping the source expression's
         * already-lowered ops in source order plus the collected
         * captures (the thunk's free bindings in first-reference
         * order).
         */
        private record ThunkSource(BlockId blockId, List<SemanticOp> ops,
                                   List<CapturedCell> captures) {
        }

        /**
         * Walks the source expression into a fresh detached thunk block
         * (B8): the expression's already-lowered ops emit into a buffer
         * whose members are the thunk block (the single emission path of
         * the walk's thunk production), the open-walk capture collector
         * records the thunk's free bindings in first-reference order
         * (the same registration surface the closure child uses — the
         * shape-map child's thunk capture arm joins the B2 cell-kind
         * derivation through it), and zero evaluation happens at the
         * creation site (the ops execute only when E7's protocol
         * re-executes the thunk).
         *
         * @param source the function-typed source expression; non-null
         * @return the detached thunk source (block, ordered ops, captures)
         */
        private ThunkSource lowerThunkSource(ExpressionNode source) {
            BlockId thunkBlock = allocateBlock();
            List<SemanticOp> thunkOps = new ArrayList<>();
            List<CapturedCell> captured = new ArrayList<>();
            emitTargets.push(thunkOps);
            // The thunk block is detached and declares no bindings of its
            // own: an empty binding frame is pushed so every reference
            // inside the walk resolves outside the thunk's own scope
            // chain and registers as a thunk capture (B9 R3 — the
            // capturedBindings pin the thunk's free bindings with their
            // generations). Enclosing detached-body walks keep receiving
            // the same references through the detaching chain (B9 R2).
            pushBindingFrame();
            captureBorders.push(bindingScopes.size());
            captureCollectors.push(captured);
            blockStack.push(thunkBlock);
            try {
                lowerExpression(source);
            } finally {
                blockStack.pop();
                captureCollectors.pop();
                captureBorders.pop();
                popBindingFrame();
                emitTargets.pop();
            }
            if (thunkOps.isEmpty()) {
                throw new IllegalStateException("the thunk source expression produced no "
                    + "op (producer defect)");
            }
            return new ThunkSource(thunkBlock, thunkOps, captured);
        }

        /**
         * Builds the closed {@link AdaptSourceRef.Thunk} of one thunk
         * source (B8): the generation-pinned {@code capturedBindings}
         * derive from the collected captures in first-reference order,
         * and the thunk builder is the single production path of
         * {@link AdaptSourceRef.Thunk} records (fail closed on a
         * malformed source op list).
         *
         * @param thunk the detached thunk source; non-null
         * @return the closed {@code Thunk {BlockId, capturedBindings}}
         *         source reference
         */
        private AdaptSourceRef.Thunk thunkSourceRef(ThunkSource thunk) {
            List<BindingGeneration> pinned = new ArrayList<>();
            for (CapturedCell capture : thunk.captures()) {
                pinned.add(new BindingGeneration(capture.cell().id,
                    capture.incarnation().generation()));
            }
            return AdapterThunkConstruction.buildThunk(thunk.blockId(), thunk.ops(), pinned);
        }

        /**
         * Emits exactly one {@code FUNCTION_ADAPT} op carrying its
         * closed-map mode and per-mode payload from birth (B7/B8): a
         * fresh adapter allocation identity per creation (stable for the
         * run), the source/target signature pair of the adaptation
         * candidate, exactly the operand set of the mode (one operand
         * for VALUE; zero for SHARED_CELL and REEVALUATE_THUNK — zero
         * evaluation at creation), policy {@code NO_DEAL_FAILURE}
         * (creation is infallible), zero {@code BOUNDARY} children (the
         * adapter adds no second boundary), and the single
         * {@code AdapterBinding} registration through the registry
         * child's seam keyed by the adapter identity.
         *
         * @param mode            the closed-map capture mode; non-null
         * @param sourceRef       the closed source reference; non-null
         * @param sourceSignature the derived source signature; non-null
         * @param targetSignature the derived target signature; non-null
         * @param proof           the recorded proof (present iff VALUE's
         *                        operand is a binding load); nullable
         * @param operands        the mode's operand set (VALUE: exactly
         *                        one; SHARED_CELL/REEVALUATE_THUNK:
         *                        zero); non-null
         * @param operandTypes    the operand descriptors in operand order
         *                        (the source signature for VALUE);
         *                        non-null
         * @param span            the position's origin span; non-null
         * @return the emitted op's identity plus its fresh adapter
         *         allocation identity
         */
        private EmittedAdapter emitFunctionAdapt(CaptureMode mode, AdaptSourceRef sourceRef,
                                                 RuntimeDescriptor.Func sourceSignature,
                                                 RuntimeDescriptor.Func targetSignature,
                                                 BindingImmutabilityProof proof,
                                                 List<ValueId> operands,
                                                 List<RuntimeDescriptor> operandTypes,
                                                 Span span) {
            ValueId adapterIdentity = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.USER, anchor, currentParent());
            KindPayload.FunctionAdaptPayload payload = new KindPayload.FunctionAdaptPayload(
                sourceSignature, targetSignature, mode, sourceRef, proof);
            emit(buildOp(opId, SemanticOpKind.FUNCTION_ADAPT, payload, adapterIdentity,
                targetSignature, operands, operandTypes, FailurePolicyId.NO_DEAL_FAILURE,
                origin));
            registry.registerAdapter(new FunctionAllocationIdentity(adapterIdentity.id()),
                opId, mode, sourceRef, sourceSignature, targetSignature);
            return new EmittedAdapter(opId, adapterIdentity);
        }

        /** One emitted {@code FUNCTION_ADAPT} op (its op id plus its fresh identity). */
        private record EmittedAdapter(OpId opId, ValueId identity) {
        }

        /**
         * Records one adapter emission fact (the shape-map child's fact
         * surface): the emitted op's identity, the fresh adapter
         * allocation identity, the closed-map mode and source reference
         * (the payload from birth), the signatures, the proof, and the
         * consumed wiring point (the adapted position's own boundary
         * op or the inferred declaration's {@code BINDING_INIT}).
         */
        private void recordAdapterEmission(OpId adaptOpId, ValueId adapterIdentity,
                                           CaptureMode mode, AdaptSourceRef sourceRef,
                                           RuntimeDescriptor.Func sourceSignature,
                                           RuntimeDescriptor.Func targetSignature,
                                           BindingImmutabilityProof proof,
                                           OpId wiringTargetOpId,
                                           BoundaryKind wiringBoundaryKind) {
            shapeMapEmissions.add(new AdapterEmission(adaptOpId, adapterIdentity, mode,
                sourceRef, sourceSignature, targetSignature, proof, wiringTargetOpId,
                wiringBoundaryKind));
        }

        /**
         * The creation-rule classification of one function-typed
         * {@code let} declaration position (B6; creation-rule-analysis
         * mode): the closed variable-position classification over the
         * initializer's checked type (the source signature) and the
         * declared/inferred binding type (the target signature), the
         * recorded proof fact of an identifier binding source (B7), the
         * prepared wiring point — the position's own
         * {@code VARIABLE_DECLARATION} boundary op for annotated
         * declarations, the {@code BINDING_INIT} op for inferred
         * declarations (no boundary exists there) — and the registry
         * child's producer facts of a host/external function-value
         * source (T4). The classification emits zero ops and changes
         * nothing: exact positions store directly (this child's
         * production), adapt positions record exactly one candidate for
         * the shape-map child, and the produced unit contains zero
         * {@code FUNCTION_ADAPT} ops.
         */
        private void classifyVarDeclPosition(VariableDeclaration decl, ValueId value,
                                             OpId declarationBoundary, OpId initOp) {
            Type targetType = declaredTypeOf(decl);
            if (!(targetType instanceof Type.Func)) {
                // Not a function-typed position — the creation rule's
                // window (the ordinary flow's descriptor-kind rule is
                // the boundary machinery's).
                return;
            }
            Type sourceType = checkedType(decl.initializer());
            Optional<BindingImmutabilityProof> proof = sourceProofOf(decl.initializer());
            Optional<FunctionBindingRegistry.FunctionValueMaterialization> producerFacts =
                sourceProducerFactsOf(value);
            AdapterCreationRule.WiringPoint wiringPoint = declarationBoundary != null
                ? new AdapterCreationRule.WiringPoint(declarationBoundary,
                    AdapterCreationRule.WiringTargetKind.VARIABLE_DECLARATION_BOUNDARY)
                : new AdapterCreationRule.WiringPoint(initOp,
                    AdapterCreationRule.WiringTargetKind.BINDING_INIT);
            creationClassifications.add(AdapterCreationRule.classifyVariablePosition(
                BoundaryKind.VARIABLE_DECLARATION, sourceType, targetType, proof,
                wiringPoint, producerFacts));
        }

        /**
         * The creation-rule classification of one function-typed
         * variable-assignment position (B6; creation-rule-analysis
         * mode): the closed variable-position classification over the
         * RHS's checked type (the source signature) and the target
         * binding's declared type (the target signature), the recorded
         * proof fact of an identifier binding source (B7), the prepared
         * wiring point (the position's own {@code VARIABLE_ASSIGNMENT}
         * boundary op), and the registry child's producer facts of a
         * host/external function-value source (T4). Zero emission: the
         * walk's {@code [valueOp, boundaryOp, commitOp]} chain is
         * unchanged and the unit contains zero {@code FUNCTION_ADAPT}
         * ops.
         */
        private void classifyVariableAssignPosition(AssignmentExpr assignment,
                                                    IdentifierExpr target, ValueId value,
                                                    OpId boundaryOp) {
            Type targetType = checkedType(target);
            if (!(targetType instanceof Type.Func)) {
                // Not a function-typed position — the creation rule's
                // window.
                return;
            }
            Type sourceType = checkedType(assignment.value());
            Optional<BindingImmutabilityProof> proof = sourceProofOf(assignment.value());
            Optional<FunctionBindingRegistry.FunctionValueMaterialization> producerFacts =
                sourceProducerFactsOf(value);
            creationClassifications.add(AdapterCreationRule.classifyVariablePosition(
                BoundaryKind.VARIABLE_ASSIGNMENT, sourceType, targetType, proof,
                new AdapterCreationRule.WiringPoint(boundaryOp,
                    AdapterCreationRule.WiringTargetKind.VARIABLE_ASSIGNMENT_BOUNDARY),
                producerFacts));
        }

        /**
         * The closed typed-boundary-position classification record (B6;
         * creation-rule-analysis mode): a boundary position never
         * adapts — the classifier records the {@code BOUNDARY_DIRECT}
         * classification and the recorded E8010
         * {@code FUNCTION_SIGNATURE} expectation for a mismatched
         * function-typed pair; the boundary op, its function-descriptor
         * cell, and the executed check are E4's machinery. The walk's
         * direct value flow into the position's boundary slot is the
         * wiring E4's boundary producer consumes.
         */
        private void recordBoundaryClassification(BoundaryKind kind, Type sourceType,
                                                  Type targetType) {
            creationClassifications.add(
                AdapterCreationRule.classifyBoundaryPosition(kind, sourceType, targetType));
        }

        /**
         * The recorded proof fact of an identifier binding source (B7):
         * present exactly when the source is an {@code IdentifierExpr}
         * whose dominant incarnation at the position carries the
         * conservative {@code BindingImmutabilityProof} — the fact the
         * shape-map child's VALUE arm consumes (an unproven binding is
         * the SHARED_CELL arm's). Non-identifier sources carry no proof
         * fact (materialized operands and member reads are the
         * shape-map child's VALUE/REEVALUATE_THUNK arms — the closed
         * map's decision, not this child's).
         */
        private Optional<BindingImmutabilityProof> sourceProofOf(ExpressionNode source) {
            if (!(source instanceof IdentifierExpr identifier)) {
                return Optional.empty();
            }
            FrameResolution resolution = resolveFrame(identifier.name());
            if (resolution == null) {
                return Optional.empty();
            }
            return proofFacts().proofOf(resolution.entry().cell().id,
                resolution.entry().incarnation().generation());
        }

        /**
         * The registry child's producer facts of the source value's
         * producing allocation (the T4 host/external materialization
         * seam): present exactly when the source's allocation identity
         * has a recorded host/external function-value materialization —
         * the fact the adaptation candidate carries for the shape-map
         * child's import-read arm (a host/external import read is a
         * non-identifier member-read source → REEVALUATE_THUNK, B7; the
         * mode decision is the shape-map child's). Loads, reads,
         * argument passing, and returns preserve the allocation
         * identity, so the identity lookup resolves the producing
         * site's classification.
         */
        private Optional<FunctionBindingRegistry.FunctionValueMaterialization>
                sourceProducerFactsOf(ValueId value) {
            return registry.materializationOf(new FunctionAllocationIdentity(value.id()));
        }

        /**
         * The runtime descriptor of an already-lowered value (closure-core
         * mode): the result type of the value's producing op in the
         * current emission target. Used to classify the initializer's
         * value for the static function-identity tracking.
         */
        private RuntimeDescriptor descriptorOf(ValueId value) {
            List<SemanticOp> target = emitTarget();
            for (int i = target.size() - 1; i >= 0; i--) {
                SemanticOp op = target.get(i);
                if (value.equals(op.result())
                        && op.resultType() instanceof RuntimeDescriptor descriptor) {
                    return descriptor;
                }
            }
            throw new IllegalStateException("no produced op publishes value " + value
                + " (producer defect)");
        }

        /**
         * The binding walk's function-declaration arm: the module-level
         * name ALLOC was hoisted (B1); a nested-scope declaration emits
         * its name ALLOC at the declaration position in the enclosing
         * block. The body then gets its block identity, the parameter
         * ALLOCs at the body block's entry (generation 0, {@code DIRECT},
         * no BINDING_INIT — the parameter-transfer write is the invoking
         * machinery's, E7), and the body statements through the binding
         * walk.
         *
         * <p><b>Closure-core mode (ISSUE-0445).</b> Every size-1
         * non-group declaration additionally produces {@code CLOSURE_NEW}
         * + {@code BINDING_INIT} at the declaration position (B4): the
         * body walks first into a buffer with capture collection active
         * (the capture set is the body's free bindings in first-reference
         * order, resolved at the creation site through the dominant frame
         * entries — B3/B9 R2), then the {@code CLOSURE_NEW} op publishes
         * the pre-allocated function-allocation identity (module-level
         * names reuse the hoist-time identity so captures of
         * later-declared module functions resolve to the hoisted ALLOC —
         * B1; nested names pre-allocate at the declaration), the
         * {@code BINDING_INIT} commits it to the name binding as the
         * immediate commit after the closure creation, and the buffered
         * body ops flush after the pair.</p>
         */
        private void lowerBindingFunctionDecl(FunctionDeclaration function,
                                              boolean moduleLevel) {
            BindingCoreIncarnation nameIncarnation = null;
            BindingId nameBinding = null;
            if (!moduleLevel) {
                // Nested-scope declarations allocate their name binding at
                // the declaration position (B1: nested functions are
                // defined at their position, no hoisting).
                nameBinding = ids.nextBindingId(module, nextOrdinal++, 0);
                nameIncarnation = new BindingCoreIncarnation(
                    INITIAL_LOOP_GENERATION, currentBlock(), BindingCellKind.DIRECT,
                    true, BindingProducer.BINDING_ALLOC, false);
                registerBinding(function.name(), nameBinding, nameIncarnation);
                emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                    new KindPayload.BindingAllocPayload(nameBinding, currentBlock(), true,
                        cellKinds.cellKindOf(nameIncarnation), INITIAL_LOOP_GENERATION),
                    function.span(), FailurePolicyId.NO_DEAL_FAILURE);
            }
            if (!closureCore) {
                // Module-level name ALLOCs were hoisted (B1): no second
                // allocation here.
                BlockId bodyBlock = allocateBlock();
                checkerScopeNodes.push(function);
                pushBindingFrame();
                blockStack.push(bodyBlock);
                for (deal.ast.Parameter parameter : function.params()) {
                    BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                    BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                        INITIAL_LOOP_GENERATION, bodyBlock, BindingCellKind.DIRECT,
                        true, BindingProducer.BINDING_ALLOC, false);
                    registerBinding(parameter.name(), binding, incarnation);
                    parameterBindings.add(binding);
                    emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                        new KindPayload.BindingAllocPayload(binding, bodyBlock, true,
                            cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                        parameter.span(), FailurePolicyId.NO_DEAL_FAILURE);
                }
                checkerScopeNodes.push(function.body());
                statementWalk.walk(function.body().statements(), false);
                checkerScopeNodes.pop();
                blockStack.pop();
                popBindingFrame();
                checkerScopeNodes.pop();
                return;
            }
            // --- Closure-core mode: CLOSURE_NEW + BINDING_INIT at the
            // declaration position over the buffered body walk. ---
            FrameEntry hoisted = null;
            if (moduleLevel) {
                hoisted = frameEntryOf(function.name());
                if (hoisted == null) {
                    throw new IllegalStateException("hoisted module-level function ALLOC "
                        + "missing for '" + function.name() + "' (producer defect)");
                }
                nameBinding = hoisted.cell().id;
                nameIncarnation = hoisted.incarnation();
            }
            FunctionContext reservedContext = fullProgram && moduleLevel
                ? functionContexts.get(nameIncarnation) : null;
            BlockId bodyBlock = reservedContext != null
                ? reservedContext.bodyBlock : allocateBlock();
            FunctionId functionId = reservedContext != null
                ? reservedContext.functionId : ids.nextFunctionId(module, nextOrdinal++, 0);
            ValueId closureIdentity;
            if (functionIdentity.containsKey(nameIncarnation)) {
                // The hoist-time pre-allocated identity (B1: captures of
                // later-declared module functions resolve to the hoisted
                // ALLOC and publish this identity).
                closureIdentity = functionIdentity.get(nameIncarnation);
            } else {
                closureIdentity = ids.nextValueId(module, nextOrdinal++, 0);
                functionIdentity.put(nameIncarnation, closureIdentity);
            }
            RuntimeDescriptor.Func signature = functionSignatureOf(function);
            List<SemanticOp> bodyOps = new ArrayList<>();
            List<CapturedCell> captured = new ArrayList<>();
            emitTargets.push(bodyOps);
            captureBorders.push(bindingScopes.size());
            captureCollectors.push(captured);
            try {
                checkerScopeNodes.push(function);
                pushBindingFrame();
                blockStack.push(bodyBlock);
                for (deal.ast.Parameter parameter : function.params()) {
                    BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                    BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                        INITIAL_LOOP_GENERATION, bodyBlock, BindingCellKind.DIRECT,
                        true, BindingProducer.BINDING_ALLOC, false);
                    registerBinding(parameter.name(), binding, incarnation);
                    parameterBindings.add(binding);
                    emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                        new KindPayload.BindingAllocPayload(binding, bodyBlock, true,
                            cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                        parameter.span(), FailurePolicyId.NO_DEAL_FAILURE);
                }
                checkerScopeNodes.push(function.body());
                if (reservedContext != null) {
                    functionStack.push(reservedContext);
                }
                boolean bodyComplete = false;
                try {
                    statementWalk.walk(function.body().statements(), false);
                    bodyComplete = true;
                } finally {
                    if (reservedContext != null) {
                        if (bodyComplete) {
                            // The implicit trailing return of an
                            // unterminated null-returning body ("a
                            // function with return type null returns the
                            // null value through the boundary").
                            if (!Boolean.TRUE.equals(blockTerminated.get(bodyBlock))) {
                                if (!(reservedContext.signature.returnType()
                                        instanceof RuntimeDescriptor.Null)) {
                                    throw new ConstructUnlowered("function '"
                                        + function.name()
                                        + "' body is not terminated and its return type is "
                                        + "not null (the carrier slice lowers the pinned "
                                        + "implicit null return only)");
                                }
                                lowerImplicitReturn(reservedContext, function.body().span());
                            }
                        }
                        functionStack.pop();
                    }
                    checkerScopeNodes.pop();
                    blockStack.pop();
                    popBindingFrame();
                    checkerScopeNodes.pop();
                }
            } finally {
                captureCollectors.pop();
                captureBorders.pop();
                emitTargets.pop();
            }
            List<BindingId> captureIds = new ArrayList<>();
            for (CapturedCell capture : captured) {
                captureIds.add(capture.cell().id);
            }
            emitClosureNew(functionId, closureIdentity, signature, captureIds, bodyBlock,
                function.span(), captured);
            emitUserNullOp(SemanticOpKind.BINDING_INIT,
                new KindPayload.BindingInitPayload(nameBinding, INITIAL_LOOP_GENERATION,
                    closureIdentity),
                function.span(), FailurePolicyId.NO_DEAL_FAILURE);
            emitTarget().addAll(bodyOps);
        }

        /**
         * Lowers one size>=2 SCC of function declarations as exactly one
         * {@code RECURSIVE_GROUP_INIT} op (ISSUE-0446 recursive-group
         * child, B4): the payload carries the declaration-ordered member
         * {@code {bindings, functions}} lists; the op has no result slot
         * (the member bindings are the observable effect).
         *
         * <p><b>Identities first (phase 1).</b> Every member's
         * allocation identity is pre-assigned at lowering — unique per
         * member, deterministic, declaration order — before any member
         * body walks, so a sibling reference inside a member body
         * resolves to the sibling's incarnation (generation 0, producing
         * allocation = the group op) and publishes the pre-assigned
         * member identity; the one {@code LoweredBody} registration per
         * member is keyed by that identity (B4/B5, the keys the registry
         * consumes). Module-level members reuse the hoist-time
         * registration and pre-assigned identity (B1); nested-scope
         * members register at the group position with no
         * {@code BINDING_ALLOC}/{@code BINDING_INIT} — the publication
         * phase (phase 2) publishes every member binding cell atomically,
         * all-or-nothing, after every member identity is allocated.</p>
         *
         * <p>Member bodies lower like any function body with captures per
         * the closure contract (B3): the buffered detached-body walk with
         * capture collection resolves each body's free bindings at the
         * group op's creation site. Member cells are {@code SHARED_CELL}
         * by construction (B2). The group op is emitted at the given
         * site — module-init top for module-level groups, the first
         * member's declaration position for nested-scope groups (B4) —
         * and the member body ops flush after it in declaration order.
         * Group execution (allocation/publication) is realized by the
         * oracle/emitters.</p>
         *
         * @param members     the SCC's members in declaration order
         *                    (size >= 2); non-null
         * @param moduleLevel {@code true} for a module-level group whose
         *                    op sits at module-init top
         */
        private void lowerGroup(List<FunctionDeclaration> members, boolean moduleLevel) {
            List<BindingId> memberBindings = new ArrayList<>();
            List<FunctionId> memberFunctions = new ArrayList<>();
            List<ValueId> memberIdentities = new ArrayList<>();
            List<FrameEntry> memberEntries = new ArrayList<>();
            for (FunctionDeclaration member : members) {
                FrameEntry entry = null;
                ValueId identity = null;
                if (moduleLevel) {
                    entry = frameEntryOf(member.name());
                    if (entry == null) {
                        throw new IllegalStateException("hoisted module-level member "
                            + "registration missing for '" + member.name()
                            + "' (producer defect)");
                    }
                    identity = functionIdentity.get(entry.incarnation());
                    if (identity == null) {
                        throw new IllegalStateException("pre-assigned member identity "
                            + "missing for '" + member.name() + "' (producer defect)");
                    }
                } else {
                    BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                    BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                        INITIAL_LOOP_GENERATION, currentBlock(), BindingCellKind.SHARED_CELL,
                        true, BindingProducer.RECURSIVE_GROUP_INIT, true);
                    registerBinding(member.name(), binding, incarnation);
                    identity = ids.nextValueId(module, nextOrdinal++, 0);
                    functionIdentity.put(incarnation, identity);
                    entry = frameEntryOf(member.name());
                }
                memberBindings.add(entry.cell().id);
                memberIdentities.add(identity);
                memberEntries.add(entry);
            }
            // Phase 1 walk: every member body lowers through the buffered
            // detached-body walk with capture collection (B3) — siblings
            // resolve because every member binding registered before any
            // body walk.
            List<List<SemanticOp>> bodyOpLists = new ArrayList<>();
            List<List<BindingId>> captureIdLists = new ArrayList<>();
            List<BlockId> bodyBlocks = new ArrayList<>();
            List<RuntimeDescriptor.Func> signatures = new ArrayList<>();
            List<List<CapturedCell>> capturedLists = new ArrayList<>();
            for (FunctionDeclaration member : members) {
                // The full-program session's reserved facts win for a
                // module-level member (ISSUE-0634): the hoist's per-function
                // context is the member's single identity, so the group
                // registration and any call of the member resolve the same
                // function id and body block. Outside the full-program
                // session the group arm allocates its own.
                FrameEntry hoistedEntry = moduleLevel ? frameEntryOf(member.name()) : null;
                FunctionContext reservedContext = fullProgram && moduleLevel
                        && hoistedEntry != null
                    ? functionContexts.get(hoistedEntry.incarnation()) : null;
                BlockId bodyBlock = reservedContext != null
                    ? reservedContext.bodyBlock : allocateBlock();
                FunctionId functionId = reservedContext != null
                    ? reservedContext.functionId
                    : ids.nextFunctionId(module, nextOrdinal++, 0);
                RuntimeDescriptor.Func signature = functionSignatureOf(member);
                List<SemanticOp> bodyOps = new ArrayList<>();
                List<CapturedCell> captured = new ArrayList<>();
                emitTargets.push(bodyOps);
                captureBorders.push(bindingScopes.size());
                captureCollectors.push(captured);
                try {
                    checkerScopeNodes.push(member);
                    pushBindingFrame();
                    blockStack.push(bodyBlock);
                    if (reservedContext != null) {
                        functionStack.push(reservedContext);
                    }
                    for (deal.ast.Parameter parameter : member.params()) {
                        BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                        BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                            INITIAL_LOOP_GENERATION, bodyBlock, BindingCellKind.DIRECT,
                            true, BindingProducer.BINDING_ALLOC, false);
                        registerBinding(parameter.name(), binding, incarnation);
                        parameterBindings.add(binding);
                        emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                            new KindPayload.BindingAllocPayload(binding, bodyBlock, true,
                                cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                            parameter.span(), FailurePolicyId.NO_DEAL_FAILURE);
                    }
                    checkerScopeNodes.push(member.body());
                    lowerBindingStatements(member.body().statements(), false);
                    checkerScopeNodes.pop();
                    blockStack.pop();
                    popBindingFrame();
                    checkerScopeNodes.pop();
                    if (reservedContext != null) {
                        functionStack.pop();
                    }
                } finally {
                    captureCollectors.pop();
                    captureBorders.pop();
                    emitTargets.pop();
                }
                List<BindingId> captureIds = new ArrayList<>();
                for (CapturedCell capture : captured) {
                    captureIds.add(capture.cell().id);
                }
                memberFunctions.add(functionId);
                bodyOpLists.add(bodyOps);
                captureIdLists.add(captureIds);
                bodyBlocks.add(bodyBlock);
                signatures.add(signature);
                capturedLists.add(captured);
            }
            // Phase 2: exactly one RECURSIVE_GROUP_INIT op — the payload
            // pins the two-phase execution contract (identities allocated
            // first, then published atomically); the op carries no result
            // slot. The origin parentage mirrors the closure child's
            // CLOSURE_NEW (the enclosing structure op when one exists).
            Span groupSpan = members.get(0).span();
            AnchorId groupAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId groupOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin groupOrigin = new SourceOrigin(sourceId,
                toSourceSpan(groupSpan), SourceOriginKind.USER, groupAnchor,
                currentParent());
            emit(buildOp(groupOpId, SemanticOpKind.RECURSIVE_GROUP_INIT,
                new KindPayload.RecursiveGroupInitPayload(memberBindings, memberFunctions),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, groupOrigin));
            List<GroupMemberFacts> memberFacts = new ArrayList<>();
            for (int i = 0; i < members.size(); i++) {
                FunctionDeclaration member = members.get(i);
                FunctionId functionId = memberFunctions.get(i);
                List<BindingId> captureIds = captureIdLists.get(i);
                BlockId bodyBlock = bodyBlocks.get(i);
                RuntimeDescriptor.Func signature = signatures.get(i);
                ValueId identity = memberIdentities.get(i);
                functions.put(functionId, new LoweredFunction(functionId, signature,
                    captureIds, bodyBlock));
                registry.registerGroupMember(new FunctionAllocationIdentity(identity.id()),
                    functionId, bodyBlock);
                List<ClosureCapture> captureFacts = new ArrayList<>();
                for (CapturedCell capture : capturedLists.get(i)) {
                    captureFacts.add(new ClosureCapture(capture.cell().name,
                        capture.cell().id, capture.incarnation().generation(),
                        capture.incarnation().scope(), capture.incarnation().producer()));
                }
                memberFacts.add(new GroupMemberFacts(member.name(),
                    memberEntries.get(i).cell().id, functionId, identity, signature,
                    bodyBlock, captureFacts));
            }
            groupFactsList.add(new GroupFacts(groupOpId, memberFacts, currentBlock()));
            for (List<SemanticOp> bodyOps : bodyOpLists) {
                emitTarget().addAll(bodyOps);
            }
        }

        /**
         * The exact function signature of a checked function declaration
         * (closure-core mode): the {@code Symbol.FunctionSymbol} fact of
         * the declaration, resolved through the checker's per-scope
         * symbol table (the scope chain walks to the enclosing scope and
         * the hoisted module root — never retaining a
         * {@code NameResolver} instance, D4).
         */
        private RuntimeDescriptor.Func functionSignatureOf(FunctionDeclaration function) {
            SymbolTable scope = checks.scopeMap().get(function);
            Symbol symbol = (scope == null ? checks.symbolTable() : scope)
                .resolve(function.name());
            if (symbol instanceof Symbol.FunctionSymbol functionSymbol) {
                return (RuntimeDescriptor.Func)
                    ContainerPayloadDescriptors.resultDescriptorOf(functionSymbol.funcType());
            }
            throw new ConstructUnlowered("function declaration '" + function.name()
                + "' without a checked FunctionSymbol fact (a missing checker fact is a "
                + "producer defect)");
        }

        /**
         * The binding walk's for-let arm (B1): exactly two incarnations
         * of one {@link BindingId} — the counter (generation 0, ALLOC +
         * INIT in the {@code LOOP} init block with the first condition
         * production; condition/update references and the body-top INIT
         * operand name generation 0) and the per-iteration incarnation
         * (generation 1, {@code SHARED_CELL}, ALLOC at the top of the
         * body block, INIT from the generation-0 load; body references
         * resolve generation 1) — the retained per-iteration copy shape
         * ({@code deal/codegen/lua/LuaBackend.java:1489-1492}). The
         * {@code LOOP(FOR)} op carries
         * {@code {initBlock, condition, bodyBlock, updateBlock}} with the
         * init block = one-time init including the first condition
         * production and the update block = update ops + condition
         * re-production (the control-flow epic's placement contract,
         * {@code control-flow-structures} C-D4). A for without a let
         * initializer, without a condition, or with a non-assignment
         * update is outside this child's window.
         */
        private void lowerBindingForLet(ForStatement statement) {
            if (statement.init().isEmpty()
                    || !(statement.init().get() instanceof ForInit.VarDecl varDecl)) {
                throw new ConstructUnlowered("for statement without a let initializer "
                    + "(the binding-core child lowers exactly the for-let shape; a "
                    + "non-let for is the control-flow epic's)");
            }
            if (statement.condition().isEmpty()) {
                throw new ConstructUnlowered("for-let without a condition (the LOOP payload "
                    + "carries the condition value — an unconditional for is outside this "
                    + "child's window)");
            }
            if (statement.update().isPresent()
                    && !(statement.update().get() instanceof AssignmentExpr)) {
                throw new ConstructUnlowered("for-let update expression "
                    + statement.update().get().getClass().getSimpleName()
                    + " (the pinned shape is the assignment chain in the update block; "
                    + "another update shape is outside this child's window)");
            }
            VariableDeclaration decl = varDecl.decl();
            BindingId counter = ids.nextBindingId(module, nextOrdinal++, 0);
            Type counterType = counterTypeOf(statement, decl);
            if (closureCore
                    && ContainerPayloadDescriptors.resultDescriptorOf(counterType)
                        instanceof RuntimeDescriptor.Func) {
                throw new ConstructUnlowered("function-typed for-let counter (the "
                    + "per-iteration carry load's function identity is the registry "
                    + "child's resolution, B5)");
            }
            BlockId initBlock = allocateBlock();
            BlockId bodyBlock = allocateBlock();
            BlockId updateBlock = allocateBlock();
            ValueId conditionSlot = null;
            OpId forLetLoopOpId = null;
            if (fullProgram) {
                // The LOOP op lives in the ENCLOSING block (the validator's
                // block tree admits no self-reference) and the condition
                // value slot is allocated upfront: both the init-block
                // first production and the update-block re-production
                // publish this one slot (C-D4).
                conditionSlot = ids.nextValueId(module, nextOrdinal++, 0);
                AnchorId loopAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
                forLetLoopOpId = ids.nextOpId(module, nextOrdinal++, 0);
                SourceOrigin loopOrigin = new SourceOrigin(sourceId,
                    toSourceSpan(statement.span()), SourceOriginKind.USER, loopAnchor,
                    currentParent());
                emit(buildOp(forLetLoopOpId, SemanticOpKind.LOOP,
                    new KindPayload.LoopPayload(ControlSelector.FOR, initBlock,
                        conditionSlot, bodyBlock, updateBlock),
                    null, null, FailurePolicyId.NO_DEAL_FAILURE, loopOrigin));
                pushLoopTarget(forLetLoopOpId);
            }
            checkerScopeNodes.push(statement);
            pushBindingFrame();
            blockStack.push(initBlock);
            BindingCoreIncarnation counterIncarnation = new BindingCoreIncarnation(
                INITIAL_LOOP_GENERATION, initBlock, BindingCellKind.DIRECT,
                true, BindingProducer.BINDING_ALLOC, false);
            registerBinding(decl.name(), counter, counterIncarnation);
            // Init block: the counter ALLOC, the initializer value ops,
            // the counter INIT, then the first condition production
            // (init-block members — C-D4).
            emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                new KindPayload.BindingAllocPayload(counter, initBlock, true,
                    cellKinds.cellKindOf(counterIncarnation), INITIAL_LOOP_GENERATION),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            ValueId initializer = lowerExpression(decl.initializer());
            emitUserNullOp(SemanticOpKind.BINDING_INIT,
                new KindPayload.BindingInitPayload(counter, INITIAL_LOOP_GENERATION,
                    initializer),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            ValueId condition = fullProgram
                ? lowerExpression(statement.condition().get(), conditionSlot)
                : lowerExpression(statement.condition().get());
            // The LOOP op itself sits in the enclosing block (the
            // control-flow epic's placement contract, C-D4): the init
            // block is the one-time init child including the first
            // condition production — the op is not a member of its own
            // init child block (C-D2 block-tree shape). Pop before the
            // emission so the op lands in the enclosing block; the
            // full-program carrier emits the op at the top of this arm
            // instead (its condition slot is threaded through
            // init/update productions).
            blockStack.pop();
            if (!fullProgram) {
                emitUserNullOp(SemanticOpKind.LOOP,
                    new KindPayload.LoopPayload(ControlSelector.FOR, initBlock, condition,
                        bodyBlock, updateBlock),
                    statement.span(), FailurePolicyId.NO_DEAL_FAILURE);
            }
            // Body block: the per-iteration incarnation (generation 1,
            // SHARED_CELL) at the body top, INIT from the generation-0
            // load, then the body statements (dominant generation 1).
            blockStack.push(bodyBlock);
            checkerScopeNodes.push(statement.body());
            pushBindingFrame();
            BindingCoreIncarnation perIteration = new BindingCoreIncarnation(
                1L, bodyBlock, BindingCellKind.SHARED_CELL, true,
                BindingProducer.BINDING_ALLOC, true);
            registerBinding(decl.name(), counter, perIteration);
            emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                new KindPayload.BindingAllocPayload(counter, bodyBlock, true,
                    cellKinds.cellKindOf(perIteration), 1L),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            ValueId carry = emitSyntheticValueOp(SemanticOpKind.BINDING_LOAD,
                new KindPayload.BindingLoadPayload(counter, INITIAL_LOOP_GENERATION),
                decl.span(), ContainerPayloadDescriptors.resultDescriptorOf(counterType),
                FailurePolicyId.NO_DEAL_FAILURE);
            emitUserNullOp(SemanticOpKind.BINDING_INIT,
                new KindPayload.BindingInitPayload(counter, 1L, carry),
                decl.span(), FailurePolicyId.NO_DEAL_FAILURE);
            statementWalk.walk(statement.body().statements(), false);
            if (forLetLoopOpId != null) {
                popLoopTarget();
            }
            popBindingFrame();
            checkerScopeNodes.pop();
            blockStack.pop();
            // Update block: the update's assignment chain, then the
            // condition re-production (update-block members — C-D4;
            // both reference the generation-0 counter).
            blockStack.push(updateBlock);
            if (statement.update().isPresent()) {
                lowerExpression(statement.update().get());
            }
            if (fullProgram) {
                // The update-block condition re-production publishes the
                // one condition slot (C-D4).
                lowerExpression(statement.condition().get(), conditionSlot);
            } else {
                lowerExpression(statement.condition().get());
            }
            blockStack.pop();
            popBindingFrame();
            checkerScopeNodes.pop();
        }

        /**
         * The binding walk's for-of arm: the iterable's prior steps, the
         * {@code FOR_EACH} op (the iteration binding's producing
         * allocation — no {@code BINDING_ALLOC} exists for it; the
         * payload's binding generation is the incarnation's ordinal, and
         * the fresh per-iteration cell comes from the op's per-iteration
         * allocation semantics, never a new ordinal), then the body
         * statements under the iteration-binding frame. The iteration
         * binding is classified {@code SHARED_CELL} (B2 — the
         * per-iteration cell exists precisely for capture semantics; the
         * payload records no cell kind). A string-typed iterable lowers
         * ({@code STRING_SCALARS}); an array iterable is the
         * control-flow epic's ({@code FOR_EACH(ARRAY_VALUES)}).
         */
        private void lowerBindingForOf(ForOfStatement statement) {
            Type iterableType = checkedType(statement.iterable());
            if (iterableType instanceof Type.Array) {
                throw new ConstructUnlowered("array for-of (FOR_EACH(ARRAY_VALUES) is E5's, "
                    + "ISSUE-0234; an array-typed iterable reaching the binding-core walk "
                    + "fails hard)");
            }
            if (!(iterableType instanceof Type.String)) {
                throw new ConstructUnlowered("for-of over a non-string, non-array iterable "
                    + typeName(iterableType) + " (this child lowers string iterables only)");
            }
            ValueId iterable = lowerExpression(statement.iterable());
            BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
            BlockId bodyBlock = allocateBlock();
            pushBindingFrame();
            registerBinding(statement.varName(), binding, new BindingCoreIncarnation(
                INITIAL_LOOP_GENERATION, bodyBlock, BindingCellKind.SHARED_CELL,
                true, BindingProducer.FOR_EACH, true));
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(statement.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.FOR_EACH,
                new KindPayload.ForEachPayload(IterationMode.STRING_SCALARS, iterable,
                    binding, INITIAL_LOOP_GENERATION, bodyBlock),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, origin));
            checkerScopeNodes.push(statement.body());
            blockStack.push(bodyBlock);
            statementWalk.walk(statement.body().statements(), false);
            blockStack.pop();
            checkerScopeNodes.pop();
            popBindingFrame();
        }

        /**
         * The binding walk's try/catch arm: the {@code TRY_CATCH} op
         * carrying the try block, the catch binding (this child's single
         * {@link BindingId} for the catch name), and the catch block;
         * the catch binding's ALLOC sits at the catch block's entry
         * (generation 0, {@code DIRECT}, mutable, no BINDING_INIT — the
         * catch-entry write is {@code TRY_CATCH}'s, ISSUE-0234). The
         * control-flow epic refines the op's execution; this child
         * supplies the binding model the structure operates on.
         */
        private void lowerBindingTry(TryStatement statement) {
            BlockId tryBlock = allocateBlock();
            BlockId catchBlock = allocateBlock();
            BindingId catchBinding = ids.nextBindingId(module, nextOrdinal++, 0);
            emitUserNullOp(SemanticOpKind.TRY_CATCH,
                new KindPayload.TryCatchPayload(tryBlock, catchBinding, catchBlock),
                statement.span(), FailurePolicyId.NO_DEAL_FAILURE);
            checkerScopeNodes.push(statement.tryBlock());
            pushBindingFrame();
            blockStack.push(tryBlock);
            statementWalk.walk(statement.tryBlock().statements(), false);
            blockStack.pop();
            popBindingFrame();
            checkerScopeNodes.pop();
            checkerScopeNodes.push(statement);
            pushBindingFrame();
            blockStack.push(catchBlock);
            BindingCoreIncarnation catchIncarnation = new BindingCoreIncarnation(
                INITIAL_LOOP_GENERATION, catchBlock, BindingCellKind.DIRECT,
                true, BindingProducer.BINDING_ALLOC, false);
            registerBinding(statement.catchVar(), catchBinding, catchIncarnation);
            emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                new KindPayload.BindingAllocPayload(catchBinding, catchBlock, true,
                    cellKinds.cellKindOf(catchIncarnation), INITIAL_LOOP_GENERATION),
                statement.span(), FailurePolicyId.NO_DEAL_FAILURE);
            statementWalk.walk(statement.catchBlock().statements(), false);
            blockStack.pop();
            popBindingFrame();
            checkerScopeNodes.pop();
        }

        /**
         * The binding walk's nested-block arm: one fresh block identity
         * plus a scope frame, then the block's statements (blocks are
         * the structured graph nodes the dominant-incarnation walk
         * resolves against, B9 R1).
         */
        private void lowerBindingBlock(Block block) {
            BlockId blockId = allocateBlock();
            checkerScopeNodes.push(block);
            pushBindingFrame();
            blockStack.push(blockId);
            statementWalk.walk(block.statements(), false);
            blockStack.pop();
            popBindingFrame();
            checkerScopeNodes.pop();
        }

        // ---------------------------------------------------------------------
        // The recursive-group SCC partition (ISSUE-0446, B4)
        // ---------------------------------------------------------------------

        /**
         * Partitions one scope's function declarations into SCCs over the
         * body-reference graph (B4): an edge {@code D -> D'} exists iff
         * D's body references D'.name as a free name — a reference
         * anywhere in the body tree (nested closures included, matching
         * the checker's scope-table resolution) that is not shadowed by
         * D's own scope chain (parameters, block declarations, nested
         * function names, loop/catch bindings). The returned SCCs carry
         * their members in declaration order and the SCC list is ordered
         * by first member's declaration order — deterministic,
         * byte-identical lowering.
         *
         * @param declarations the scope's function declarations in
         *                     declaration order; non-null
         * @return the SCCs (size-1 self-recursive SCCs included)
         */
        private static List<List<FunctionDeclaration>> partitionFunctionDeclarations(
                List<FunctionDeclaration> declarations) {
            List<List<FunctionDeclaration>> sccs = new ArrayList<>();
            if (declarations.isEmpty()) {
                return sccs;
            }
            Map<FunctionDeclaration, Integer> position = new IdentityHashMap<>();
            for (int i = 0; i < declarations.size(); i++) {
                position.put(declarations.get(i), i);
            }
            Set<String> names = new LinkedHashSet<>();
            for (FunctionDeclaration declaration : declarations) {
                names.add(declaration.name());
            }
            Map<FunctionDeclaration, LinkedHashSet<FunctionDeclaration>> edges =
                new IdentityHashMap<>();
            for (FunctionDeclaration declaration : declarations) {
                LinkedHashSet<FunctionDeclaration> targets = new LinkedHashSet<>();
                Set<String> referenced = freeNameReferences(declaration);
                for (String name : referenced) {
                    if (!names.contains(name) || name.equals(declaration.name())) {
                        continue;
                    }
                    for (FunctionDeclaration candidate : declarations) {
                        if (candidate.name().equals(name)) {
                            targets.add(candidate);
                        }
                    }
                }
                edges.put(declaration, targets);
            }
            // Tarjan's SCC algorithm over the identity-keyed adjacency
            // (edges iterated in declaration order — deterministic).
            IdentityHashMap<FunctionDeclaration, Integer> index =
                new IdentityHashMap<>();
            IdentityHashMap<FunctionDeclaration, Integer> lowlink =
                new IdentityHashMap<>();
            List<FunctionDeclaration> stack = new ArrayList<>();
            Set<FunctionDeclaration> onStack =
                java.util.Collections.newSetFromMap(new IdentityHashMap<>());
            int[] nextIndex = {0};
            for (FunctionDeclaration declaration : declarations) {
                if (!index.containsKey(declaration)) {
                    strongConnect(declaration, edges, index, lowlink, stack, onStack,
                        nextIndex, sccs);
                }
            }
            // Deterministic normalization: members in declaration order,
            // SCCs ordered by first member's declaration order.
            for (List<FunctionDeclaration> scc : sccs) {
                scc.sort(Comparator.comparingInt(position::get));
            }
            sccs.sort(Comparator.comparingInt(scc -> position.get(scc.get(0))));
            return sccs;
        }

        /** One Tarjan recursion step (deterministic edge iteration). */
        private static void strongConnect(FunctionDeclaration node,
                                          Map<FunctionDeclaration,
                                              LinkedHashSet<FunctionDeclaration>> edges,
                                          IdentityHashMap<FunctionDeclaration, Integer> index,
                                          IdentityHashMap<FunctionDeclaration, Integer> lowlink,
                                          List<FunctionDeclaration> stack,
                                          Set<FunctionDeclaration> onStack,
                                          int[] nextIndex,
                                          List<List<FunctionDeclaration>> sccs) {
            index.put(node, nextIndex[0]);
            lowlink.put(node, nextIndex[0]);
            nextIndex[0]++;
            stack.add(node);
            onStack.add(node);
            for (FunctionDeclaration target : edges.get(node)) {
                if (!index.containsKey(target)) {
                    strongConnect(target, edges, index, lowlink, stack, onStack,
                        nextIndex, sccs);
                    lowlink.put(node, Math.min(lowlink.get(node), lowlink.get(target)));
                } else if (onStack.contains(target)) {
                    lowlink.put(node, Math.min(lowlink.get(node), index.get(target)));
                }
            }
            if (lowlink.get(node).equals(index.get(node))) {
                List<FunctionDeclaration> scc = new ArrayList<>();
                FunctionDeclaration member;
                do {
                    member = stack.remove(stack.size() - 1);
                    onStack.remove(member);
                    scc.add(member);
                } while (member != node);
                sccs.add(scc);
            }
        }

        /**
         * The free name references of one function declaration's body:
         * every identifier name referenced anywhere in the body tree that
         * the declaration's own scope chain does not bind (parameters,
         * same-block declarations — position-independent per the
         * checker's scope-table resolution — nested function names, and
         * loop/catch bindings). Member accesses name only their object
         * part; object-literal keys and class/property names are never
         * identifiers.
         */
        private static Set<String> freeNameReferences(FunctionDeclaration declaration) {
            Set<String> references = new LinkedHashSet<>();
            Set<String> bound = new HashSet<>();
            for (Parameter parameter : declaration.params()) {
                bound.add(parameter.name());
            }
            walkReferenceBlock(declaration.body(), bound, references);
            return references;
        }

        /**
         * Walks one block for free-name references: the block's own
         * declarations (at any position — the checker's scope-table
         * resolution binds them position-independently) join the bound
         * set before the statements walk; nested blocks and function
         * bodies extend the bound set with their own declarations.
         */
        private static void walkReferenceBlock(Block block, Set<String> bound,
                                               Set<String> references) {
            Set<String> local = new HashSet<>(bound);
            for (StatementNode statement : block.statements()) {
                String declared = declaredNameOf(statement);
                if (declared != null) {
                    local.add(declared);
                }
            }
            for (StatementNode statement : block.statements()) {
                walkReferenceStatement(statement, local, references);
            }
        }

        /**
         * The declared name a statement binds in its enclosing block, or
         * {@code null}: let names and nested function names (checker
         * scope-table resolution binds them position-independently).
         * For-let loop variables are NOT block bindings — the checker
         * defines them in the loop's own child scope
         * ({@code NameResolver.walkFor}), so they never shadow sibling
         * function names outside the loop.
         */
        private static String declaredNameOf(StatementNode statement) {
            return switch (statement) {
                case VariableDeclaration decl -> decl.name();
                case FunctionDeclaration function -> function.name();
                default -> null;
            };
        }

        /** Walks one statement for free-name references. */
        private static void walkReferenceStatement(StatementNode statement,
                                                   Set<String> bound,
                                                   Set<String> references) {
            switch (statement) {
                case VariableDeclaration decl ->
                    walkReferenceExpr(decl.initializer(), bound, references);
                case FunctionDeclaration function -> {
                    Set<String> inner = new HashSet<>(bound);
                    for (Parameter parameter : function.params()) {
                        inner.add(parameter.name());
                    }
                    walkReferenceBlock(function.body(), inner, references);
                }
                case Block block -> walkReferenceBlock(block, bound, references);
                case IfStatement ifStatement -> {
                    walkReferenceExpr(ifStatement.condition(), bound, references);
                    walkReferenceBlock(ifStatement.thenBlock(), bound, references);
                    if (ifStatement.elseBranch().isPresent()) {
                        Either<IfStatement, Block> branch = ifStatement.elseBranch().get();
                        switch (branch) {
                            case Either.Left<IfStatement, Block> left ->
                                walkReferenceStatement(left.value(), bound, references);
                            case Either.Right<IfStatement, Block> right ->
                                walkReferenceBlock(right.value(), bound, references);
                        }
                    }
                }
                case WhileStatement whileStatement -> {
                    walkReferenceExpr(whileStatement.condition(), bound, references);
                    walkReferenceBlock(whileStatement.body(), bound, references);
                }
                case ForStatement forStatement -> {
                    Set<String> loopBound = bound;
                    if (forStatement.init().isPresent()
                            && forStatement.init().get() instanceof ForInit.VarDecl varDecl) {
                        // The checker defines the loop variable in the
                        // loop's own child scope before walking the
                        // initializer — it binds throughout the loop,
                        // never in the enclosing block.
                        loopBound = new HashSet<>(bound);
                        loopBound.add(varDecl.decl().name());
                    }
                    if (forStatement.init().isPresent()) {
                        ForInit init = forStatement.init().get();
                        switch (init) {
                            case ForInit.VarDecl varDecl ->
                                walkReferenceExpr(varDecl.decl().initializer(), loopBound,
                                    references);
                            case ForInit.AssignExpr assignExpr ->
                                walkReferenceExpr(assignExpr.expr(), loopBound, references);
                        }
                    }
                    if (forStatement.condition().isPresent()) {
                        walkReferenceExpr(forStatement.condition().get(), loopBound,
                            references);
                    }
                    if (forStatement.update().isPresent()) {
                        walkReferenceExpr(forStatement.update().get(), loopBound,
                            references);
                    }
                    walkReferenceBlock(forStatement.body(), loopBound, references);
                }
                case ForOfStatement forOf -> {
                    // The iterable resolves in the parent scope; the loop
                    // variable binds only inside the body's scope chain.
                    walkReferenceExpr(forOf.iterable(), bound, references);
                    Set<String> loopBound = new HashSet<>(bound);
                    loopBound.add(forOf.varName());
                    walkReferenceBlock(forOf.body(), loopBound, references);
                }
                case TryStatement tryStatement -> {
                    walkReferenceBlock(tryStatement.tryBlock(), bound, references);
                    Set<String> catchBound = new HashSet<>(bound);
                    catchBound.add(tryStatement.catchVar());
                    walkReferenceBlock(tryStatement.catchBlock(), catchBound, references);
                }
                case ExpressionStatement expressionStatement ->
                    walkReferenceExpr(expressionStatement.expr(), bound, references);
                case ReturnStatement returnStatement -> {
                    if (returnStatement.expr().isPresent()) {
                        walkReferenceExpr(returnStatement.expr().get(), bound, references);
                    }
                }
                case ThrowStatement throwStatement ->
                    walkReferenceExpr(throwStatement.expr(), bound, references);
                case DeleteStatement deleteStatement ->
                    walkReferenceExpr(deleteStatement.target(), bound, references);
                // Class declarations, break/continue, imports, and
                // exports reference no sibling function names for the
                // partition (class defaults are per-construction R4
                // references, not body references — B4's graph covers
                // name references in function-declaration bodies).
                case ClassDeclaration _, BreakStatement _, ContinueStatement _,
                     ImportDeclaration _, ExportDeclaration _ -> { }
                default -> { /* no further statement kinds */ }
            }
        }

        /** Walks one expression for free-name references. */
        private static void walkReferenceExpr(ExpressionNode expr, Set<String> bound,
                                              Set<String> references) {
            switch (expr) {
                case LiteralExpr ignored -> { }
                case IdentifierExpr identifier -> {
                    if (!bound.contains(identifier.name())) {
                        references.add(identifier.name());
                    }
                }
                case BinaryExpr binary -> {
                    walkReferenceExpr(binary.left(), bound, references);
                    walkReferenceExpr(binary.right(), bound, references);
                }
                case UnaryExpr unary -> walkReferenceExpr(unary.expr(), bound, references);
                case CallExpr call -> {
                    walkReferenceExpr(call.callee(), bound, references);
                    for (ExpressionNode arg : call.args()) {
                        walkReferenceExpr(arg, bound, references);
                    }
                }
                case MemberAccessExpr access ->
                    walkReferenceExpr(access.object(), bound, references);
                case IndexExpr index -> {
                    walkReferenceExpr(index.array(), bound, references);
                    walkReferenceExpr(index.index(), bound, references);
                }
                case ArrayLiteralExpr array -> {
                    for (ExpressionNode element : array.elements()) {
                        walkReferenceExpr(element, bound, references);
                    }
                }
                case ObjectLiteralExpr object -> {
                    for (Property property : object.properties()) {
                        walkReferenceExpr(property.value(), bound, references);
                    }
                }
                case FunctionExpr functionExpr -> {
                    Set<String> inner = new HashSet<>(bound);
                    for (Parameter parameter : functionExpr.params()) {
                        inner.add(parameter.name());
                    }
                    walkReferenceBlock(functionExpr.body(), inner, references);
                }
                case HasExpr has -> walkReferenceExpr(has.object(), bound, references);
                case AssignmentExpr assignment -> {
                    walkReferenceExpr(assignment.target(), bound, references);
                    walkReferenceExpr(assignment.value(), bound, references);
                }
                case TemplateLiteralExpr template -> {
                    for (ExpressionNode part : template.parts()) {
                        walkReferenceExpr(part, bound, references);
                    }
                }
                case AwaitExpression awaitExpression ->
                    walkReferenceExpr(awaitExpression.callee(), bound, references);
            }
        }

        /**
         * The declared type of a let declaration (the annotated type for
         * annotated declarations, the inferred type otherwise): resolved
         * from the checker's per-scoped-statement symbol table of the
         * innermost enclosing scope (or the root table at module level)
         * so nested declarations resolve without retaining any
         * {@code NameResolver} instance (D4); falls back to the
         * initializer's checked type when no symbol fact exists.
         */
        private Type declaredTypeOf(VariableDeclaration decl) {
            SymbolTable scope = currentCheckerScope();
            if (scope != null) {
                Symbol symbol = scope.resolveLocal(decl.name());
                if (symbol instanceof Symbol.VariableSymbol variable
                        && variable.type() != null) {
                    return variable.type();
                }
            }
            return checkedType(decl.initializer());
        }

        /**
         * The for-let counter's declared type: resolved from the
         * checker's for-scope symbol table (the counter symbol, inferred
         * type included), falling back to the initializer's checked type.
         */
        private Type counterTypeOf(ForStatement statement, VariableDeclaration decl) {
            Map<StatementNode, SymbolTable> scopeMap = checks.scopeMap();
            SymbolTable scope = scopeMap.get(statement);
            if (scope != null) {
                Symbol symbol = scope.resolveLocal(decl.name());
                if (symbol instanceof Symbol.VariableSymbol variable
                        && variable.type() != null) {
                    return variable.type();
                }
            }
            return checkedType(decl.initializer());
        }

        /**
         * The innermost checker scope for declared-type resolution: the
         * scope-map table of the innermost scope-keyed node currently
         * being walked, or the root symbol table at module level.
         */
        private SymbolTable currentCheckerScope() {
            if (checkerScopeNodes.isEmpty()) {
                return checks.symbolTable();
            }
            return checks.scopeMap().get(checkerScopeNodes.peek());
        }

        /** The block identity binding ALLOCs in the current site carry as their scope. */
        private BlockId currentBlock() {
            return blockStack.peek();
        }

        /** Pushes one binding-environment scope frame (innermost first). */
        private void pushBindingFrame() {
            bindingScopes.add(0, new LinkedHashMap<>());
        }

        /** Pops the innermost binding-environment scope frame. */
        private void popBindingFrame() {
            if (bindingScopes.isEmpty()) {
                throw new IllegalStateException(
                    "popBindingFrame without an open binding frame (producer defect)");
            }
            bindingScopes.remove(0);
        }

        /**
         * Registers one incarnation of a declared name: the first
         * registration of a {@link BindingId} allocates its cell; later
         * incarnations of the same identity (the for-let counter's
         * per-iteration incarnation) append to the same cell, and a
         * shadowing redeclaration (a new {@link BindingId}) creates a new
         * cell and replaces the innermost frame entry.
         */
        private void registerBinding(String name, BindingId binding,
                                     BindingCoreIncarnation incarnation) {
            BindingCell cell = cellsById.get(binding);
            if (cell == null) {
                cell = new BindingCell(name, binding);
                cellsById.put(binding, cell);
                bindingCells.add(cell);
            }
            Map<String, FrameEntry> frame = bindingScopes.get(0);
            frame.put(name, new FrameEntry(cell, incarnation));
            cell.incarnations.add(incarnation);
        }

        /**
         * The innermost frame entry of a declared name (the dominant
         * incarnation at the site), or {@code null}.
         */
        private FrameEntry frameEntryOf(String name) {
            FrameResolution resolution = resolveFrame(name);
            return resolution == null ? null : resolution.entry();
        }

        /**
         * The innermost frame entry plus its frame index (innermost
         * first) of a declared name, or {@code null}: the resolution
         * surface the closure child's load/store arms and capture
         * collection use (B9 R1/R2/R3 as the resolution model — the
         * frame index decides whether a detached-body reference resolves
         * inside the function's own scope chain or is a capture).
         */
        private FrameResolution resolveFrame(String name) {
            for (int i = 0; i < bindingScopes.size(); i++) {
                FrameEntry entry = bindingScopes.get(i).get(name);
                if (entry != null) {
                    return new FrameResolution(entry, i);
                }
            }
            return null;
        }

        /** The innermost emission target of the session (the op list or a body buffer). */
        private List<SemanticOp> emitTarget() {
            return emitTargets.peek();
        }

        /**
         * Registers a body reference as a capture of every open
         * detached-body walk whose capture border the resolution lies
         * outside (B3/B9 R2/R3): the resolved incarnation joins the B2
         * cell-kind derivation's capture-reference set once, and the
         * captured cell joins each such walk's collector in
         * first-reference order. A reference resolving outside the
         * innermost walk's border is therefore additionally a free
         * reference of every enclosing walk whose own scope chain
         * excludes the resolved frame — the doubly-nested detaching
         * chain of B9 R2(ii): a closure created inside another detached
         * body resolves its captures in that body's context first, and
         * the enclosing body's captures must record the same binding so
         * the chain closes through every intermediate body
         * ({@code nested-closure-mutation.deal}'s inner-body capture →
         * make's body capture → the closing R1 step).
         */
        private void maybeRegisterCapture(String name, FrameResolution resolution) {
            if (!closureCore || captureBorders.isEmpty()) {
                return;
            }
            int frameCount = bindingScopes.size();
            if (resolution.frameIndex() < frameCount - captureBorders.peek()) {
                return; // the innermost function's own scope chain — not a capture at all.
            }
            Iterator<Integer> borders = captureBorders.iterator();
            Iterator<List<CapturedCell>> collectors = captureCollectors.iterator();
            while (borders.hasNext() && collectors.hasNext()) {
                int border = borders.next();
                List<CapturedCell> collector = collectors.next();
                // Frames pushed since the walk's entry (its own body
                // frame included) occupy indices [0, frameCount - border);
                // a resolution at or beyond that range is outside the
                // walk's own scope chain and must be its capture too.
                if (resolution.frameIndex() < frameCount - border) {
                    continue;
                }
                registerCaptureReference(resolution.entry(), collector);
            }
        }

        /**
         * The single capture-reference registration of the walk (B2's
         * closure-capture arm for this child): the incarnation the
         * capture resolves to joins the cell-kind derivation, and the
         * captured cell joins the given collector once (first-reference
         * order — deterministic capture lists). One reference event may
         * register into several open walks' collectors (the detaching-
         * chain propagation of {@link #maybeRegisterCapture}); the
         * cell-kind derivation's reference set has identity semantics,
         * so repeated registrations of one incarnation stay idempotent.
         */
        private void registerCaptureReference(FrameEntry entry,
                                              List<CapturedCell> collector) {
            cellKinds.registerCaptureReference(entry.incarnation());
            if (collector == null) {
                return;
            }
            for (CapturedCell captured : collector) {
                if (captured.cell() == entry.cell()) {
                    return;
                }
            }
            collector.add(new CapturedCell(entry.cell(), entry.incarnation()));
        }

        /**
         * Emits one {@code CLOSURE_NEW} op publishing the given
         * function-allocation identity, registers the {@code LoweredBody}
         * execution binding through the registry seam and the
         * {@code LoweredFunction} record, and records the closure facts
         * (resolved captures) in creation order. The closure publishes a
         * fresh function identity per creation (execution contract);
         * creation evaluates nothing.
         */
        private void emitClosureNew(FunctionId functionId, ValueId result,
                                    RuntimeDescriptor.Func signature,
                                    List<BindingId> captures, BlockId bodyBlock, Span span,
                                    List<CapturedCell> captured) {
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            FunctionExecutionBinding.LoweredBody binding =
                new FunctionExecutionBinding.LoweredBody(functionId, bodyBlock);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.CLOSURE_NEW,
                new KindPayload.ClosureNewPayload(functionId, signature, captures, binding),
                result, signature, FailurePolicyId.NO_DEAL_FAILURE, origin));
            functions.put(functionId, new LoweredFunction(functionId, signature, captures,
                bodyBlock));
            registry.registerClosure(new FunctionAllocationIdentity(result.id()),
                functionId, bodyBlock);
            List<ClosureCapture> captureFacts = new ArrayList<>();
            for (CapturedCell capture : captured) {
                captureFacts.add(new ClosureCapture(capture.cell().name, capture.cell().id,
                    capture.incarnation().generation(), capture.incarnation().scope(),
                    capture.incarnation().producer()));
            }
            closureFactsList.add(new ClosureFacts(functionId, signature, bodyBlock,
                captureFacts));
        }

        /**
         * The walk-finalization re-derivation of the B2 cell kinds over
         * the complete capture-reference union (whole-scope analysis: a
         * closure anywhere in the enclosing scope referencing a binding
         * upgrades every incarnation of that binding that a capture
         * resolves to). Every {@code BINDING_ALLOC} payload whose derived
         * kind differs from its emission-time kind is rebuilt in place
         * with the re-derived payload and contract digest — the final
         * emitted cell kinds flow from exactly one derivation.
         */
        private void finalizeCellKinds() {
            for (int i = 0; i < ops.size(); i++) {
                SemanticOp op = ops.get(i);
                if (!(op.payload() instanceof KindPayload.BindingAllocPayload alloc)) {
                    continue;
                }
                BindingCell cell = cellsById.get(alloc.binding());
                if (cell == null) {
                    continue; // not a binding of this walk's environment.
                }
                BindingCoreIncarnation incarnation = null;
                for (BindingCoreIncarnation candidate : cell.incarnations) {
                    if (candidate.generation() == alloc.generation()
                            && candidate.scope().equals(alloc.scope())) {
                        incarnation = candidate;
                        break;
                    }
                }
                if (incarnation == null) {
                    throw new IllegalStateException("BINDING_ALLOC of " + alloc.binding()
                        + " generation " + alloc.generation() + " in " + alloc.scope()
                        + " matches no registered incarnation (producer defect)");
                }
                BindingCellKind finalKind = cellKinds.cellKindOf(incarnation);
                if (finalKind == alloc.cellKind()) {
                    continue;
                }
                ops.set(i, rebuildAllocOp(op, finalKind));
            }
        }

        /**
         * Rebuilds one {@code BINDING_ALLOC} op with the final derived
         * cell kind: same identity, origin, result shape, operands, and
         * policy; the payload's cell kind and the contract snapshot
         * digest re-derive from the final payload through the single
         * canonicalizer path.
         */
        private SemanticOp rebuildAllocOp(SemanticOp op, BindingCellKind finalKind) {
            KindPayload.BindingAllocPayload alloc =
                (KindPayload.BindingAllocPayload) op.payload();
            KindPayload.BindingAllocPayload rebuilt = new KindPayload.BindingAllocPayload(
                alloc.binding(), alloc.scope(), alloc.mutable(), finalKind,
                alloc.generation());
            OperationContractSnapshot placeholder = contractOf(op.kind(), rebuilt,
                op.resultType(), op.operandTypes(), op.failurePolicy(), "placeholder");
            String digest = ContractSnapshotCanonicalizer.digest(placeholder);
            OperationContractSnapshot contract = contractOf(op.kind(), rebuilt,
                op.resultType(), op.operandTypes(), op.failurePolicy(), digest);
            return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
                op.resultType(), op.operands(), op.operandTypes(), rebuilt,
                op.failurePolicy(), contract);
        }

        /** The pinned origin span of module-init-top synthetic ops (the program span). */
        private Span moduleInitSpan() {
            return programSpan;
        }

        // ---------------------------------------------------------------------
        // The expression arms (D1)
        // ---------------------------------------------------------------------

        /**
         * Lowers one checked expression through the D1 shape map,
         * appending the produced operations to the session and returning
         * the produced value. Each expression lowers exactly once; the
         * produced subexpression ops precede the consuming op in
         * {@link #ops()}.
         *
         * @param expr the checked expression; non-null
         * @return the produced {@link ValueId}
         * @throws ConstructUnlowered on a construct without an arm in this
         *         stage's window
         */
        public ValueId lowerExpression(ExpressionNode expr) {
            return lowerExpression(expr, null);
        }

        /**
         * Lowers one checked expression through the D1 shape map with an
         * explicit result slot: the expression's final producing op
         * publishes {@code slot} instead of a fresh {@link ValueId}
         * ({@code null} allocates one). The pinned use is the
         * {@code LOOP(FOR)} condition re-production — the
         * {@code updateBlock} condition production re-publishes the
         * {@code initBlock} production's condition {@code ValueId} (one
         * value identity, the most recently produced value of the
         * condition {@code ValueId} wins at execution). Only the final
         * producing op takes the slot; every intermediate op allocates
         * its own value.
         *
         * @param expr the checked expression; non-null
         * @param slot the result slot of the final producing op, or
         *             {@code null} to allocate a fresh value
         * @return the produced {@link ValueId} (the slot when given)
         * @throws ConstructUnlowered on a construct without an arm in this
         *         stage's window
         */
        public ValueId lowerExpression(ExpressionNode expr, ValueId slot) {
            Objects.requireNonNull(expr, "expr must not be null");
            return switch (expr) {
                case LiteralExpr literal -> lowerConst(literal, slot);
                case IdentifierExpr identifier -> lowerBindingLoad(identifier, slot);
                case FunctionExpr functionExpr -> {
                    if (closureCore) {
                        yield lowerClosureExpr(functionExpr, slot);
                    }
                    throw new ConstructUnlowered(describeExpression(expr));
                }
                case ArrayLiteralExpr array -> lowerArrayNew(array, slot);
                case ObjectLiteralExpr object -> lowerTableNew(object, slot);
                case MemberAccessExpr access -> lowerMemberAccess(access, slot);
                case BinaryExpr binary -> lowerBinary(binary, slot);
                case TemplateLiteralExpr template -> lowerTemplate(template, slot);
                case UnaryExpr unary -> lowerUnary(unary, slot);
                case CallExpr call -> lowerCallSite(call, slot);
                case AwaitExpression awaitExpression -> {
                    if (e7Calls) {
                        yield lowerAwaitExpression(awaitExpression, slot);
                    }
                    throw new ConstructUnlowered(describeExpression(expr));
                }
                case IndexExpr index -> lowerIndexRead(index, slot);
                case AssignmentExpr assignment -> lowerAssignment(assignment, slot);
                case HasExpr has -> {
                    if (!classCore) {
                        throw new ConstructUnlowered(describeExpression(expr));
                    }
                    yield lowerHasField(has, slot);
                }
                default -> throw new ConstructUnlowered(describeExpression(expr));
            };
        }

        /**
         * Lowers one checked for-of statement with a string-typed
         * iterable through the D1 arm: the iterable prior step, the
         * {@code FOR_EACH} op, then the body block's statements under the
         * loop-binding frame. An array-typed iterable fails hard with
         * {@link ConstructUnlowered} ({@code FOR_EACH(ARRAY_VALUES)} is
         * E5's).
         *
         * @param stmt the checked for-of statement; non-null
         * @return the produced {@code FOR_EACH} op id
         * @throws ConstructUnlowered on a non-string iterable or on a
         *         body statement without an arm
         */
        public OpId lowerForOfStatement(ForOfStatement stmt) {
            Objects.requireNonNull(stmt, "stmt must not be null");
            Type iterableType = checkedType(stmt.iterable());
            if (iterableType instanceof Type.Array arrayType) {
                return lowerArrayForOf(stmt, arrayType);
            }
            if (!(iterableType instanceof Type.String)) {
                throw new ConstructUnlowered("for-of over a non-string, non-array iterable "
                    + typeName(iterableType) + " (this stage lowers string and array "
                    + "iterables only)");
            }
            BlockId bodyBlock = allocateBlock();
            ValueId iterable = lowerExpression(stmt.iterable());
            ForEachFrame frame = openForEachScope(stmt.varName());
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(stmt.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.FOR_EACH,
                new KindPayload.ForEachPayload(IterationMode.STRING_SCALARS, iterable,
                    frame.binding(), frame.generation(), bodyBlock),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, origin));
            pushBlockParent(opId);
            pushBlock(bodyBlock);
            pushLoopTarget(opId);
            try {
                statementWalk.walk(stmt.body().statements(), false);
            } finally {
                popLoopTarget();
                popBlock();
                popBlockParent();
                closeForEachScope();
            }
            return opId;
        }

        /**
         * {@code FOR_EACH(ARRAY_VALUES)} — the array for-of arm (C-D5):
         * the iterable operand completes exactly once before START as one
         * prior step in the enclosing block; the op snapshots the array
         * reference and the initial length and visits slot indices
         * {@code 0..initialLength-1} in increasing order with the op's
         * own {@code TYPE_DESCRIPTOR} terminal check against the element
         * descriptor derived from the recorded array operand type
         * ({@code [T]} → element {@code T}) — a missing element fails
         * E8001 {@code expected {T}, got missing} at the {@code FOR_EACH}
         * origin before the body runs; then a fresh binding per iteration
         * (mechanics E6 — the payload pins the binding identity and the
         * initial generation) and the body block executes.
         * {@code BREAK}/{@code CONTINUE} target this op's {@code OpId}.
         * The element type is derived fail-closed through the descriptor
         * bridge — an unrepresentable element ({@code bytes}) is a
         * producer defect, never an invented descriptor.
         */
        /**
         * The shared container pipeline's bytes-element exclusion
         * (ISSUE-0158 boundary): bytes <em>value</em> semantics are
         * backend-owned (the retained Lua/JVM emitters), so a container
         * element position whose checked type contains bytes — at any
         * depth — cannot produce an array/boundary op here. The bytes
         * element descriptor exists since the ISSUE-0158 schema lift, but
         * no shared bytes value semantics exist, so the position fails
         * closed as a producer defect (never an invented element check).
         */
        private RuntimeDescriptor containerElementDescriptor(Type element) {
            if (Types.containsBytes(element)) {
                throw new ConstructUnlowered("a container element position whose checked "
                    + "type contains bytes: bytes value semantics are backend-owned "
                    + "(ISSUE-0158) and the shared container pipeline excludes them "
                    + "(producer defect, never an invented element check)");
            }
            return ContainerPayloadDescriptors.elementDescriptorOf(element);
        }

        private OpId lowerArrayForOf(ForOfStatement stmt, Type.Array arrayType) {
            containerElementDescriptor(arrayType.element());
            BlockId bodyBlock = allocateBlock();
            ValueId iterable = lowerExpression(stmt.iterable());
            ForEachFrame frame = openForEachScope(stmt.varName());
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(stmt.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.FOR_EACH,
                new KindPayload.ForEachPayload(IterationMode.ARRAY_VALUES, iterable,
                    frame.binding(), frame.generation(), bodyBlock),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, origin));
            pushBlockParent(opId);
            pushBlock(bodyBlock);
            pushLoopTarget(opId);
            try {
                statementWalk.walk(stmt.body().statements(), false);
            } finally {
                popLoopTarget();
                popBlock();
                popBlockParent();
                closeForEachScope();
            }
            return opId;
        }

        // ---------------------------------------------------------------------
        // The address-chain arms (E5; assignment-delete-address-chains A-D9)
        // ---------------------------------------------------------------------

        /**
         * {@code ASSIGN} — the address-chain dispatch over the closed
         * A-D9 map: the target's checked shape selects exactly one chain
         * (VARIABLE, TABLE_SLOT member/index, ARRAY_SLOT, CLASS_FIELD).
         * Each chain is one {@code ASSIGN} op with the pinned child order
         * (A-D2), the closed boundary production (A-D4), the single-last
         * commit (A-D5), the committed-value result (A-D6), and single
         * evaluation (A-D8): every child records the chain op as its
         * {@code parentOpId} and each source subexpression appears
         * exactly once as a producing op.
         *
         * @param assignment the checked assignment expression; non-null
         * @return the committed value's {@link ValueId} (A-D6)
         * @throws ConstructUnlowered on a target shape outside the closed
         *         A-D9 map
         */
        public ValueId lowerAssignment(AssignmentExpr assignment) {
            return lowerAssignment(assignment, null);
        }

        /**
         * Lowers one checked assignment with an explicit result slot:
         * the slot threads to the RHS expression's final producing op,
         * whose value identity the {@code ASSIGN} op publishes (A-D6).
         *
         * @param assignment the checked assignment expression; non-null
         * @param slot       the committed-value slot, or {@code null} to
         *                   allocate fresh
         * @return the committed value's {@link ValueId}
         */
        public ValueId lowerAssignment(AssignmentExpr assignment, ValueId slot) {
            Objects.requireNonNull(assignment, "assignment must not be null");
            ExpressionNode target = assignment.target();
            if (target instanceof IdentifierExpr identifier) {
                if (closureCore) {
                    // The closure walk's variable-assignment arm: the
                    // store commits the dominant incarnation and, inside
                    // a detached-body walk, registers the reference as a
                    // capture (stores reference cells — capture by
                    // binding). The closure walk threads no result slot
                    // (the slot is the E5 LOOP(FOR) condition
                    // re-production's; the binding walk re-produces the
                    // condition with a fresh value).
                    return lowerVariableAssignClosure(assignment, identifier);
                }
                return lowerVariableAssign(assignment, identifier, slot);
            }
            if (target instanceof MemberAccessExpr access) {
                Type objectType = checkedType(access.object());
                if (objectType instanceof Type.Table) {
                    return lowerTableMemberAssign(assignment, access, slot);
                }
                if (objectType instanceof Type.Class classType) {
                    return lowerClassFieldAssign(assignment, access, classType, slot);
                }
                throw new ConstructUnlowered("assignment target '" + access.field()
                    + "' on " + typeName(objectType) + " (no closed A-D9 chain shape for "
                    + "this receiver: module members are E10's, array/bytes members carry "
                    + "no write shape)");
            }
            if (target instanceof IndexExpr index) {
                Type containerType = checkedType(index.array());
                if (containerType instanceof Type.Table) {
                    return lowerTableIndexAssign(assignment, index, slot);
                }
                if (containerType instanceof Type.Array arrayType) {
                    return lowerArrayIndexAssign(assignment, index, arrayType, slot);
                }
                throw new ConstructUnlowered("assignment target index on "
                    + typeName(containerType) + " (no closed A-D9 chain shape for this "
                    + "container: bytes indexing is ISSUE-0158's)");
            }
            throw new ConstructUnlowered("assignment target "
                + target.getClass().getSimpleName() + " (no closed A-D9 chain shape)");
        }

        /**
         * {@code DELETE} — the address-chain dispatch over the closed
         * A-D9 delete map: TABLE_SLOT member/index, ARRAY_SLOT, or
         * CLASS_FIELD; no RHS. The chain is one {@code DELETE} op with
         * the pinned order receiver → key → normalize → [array bounds
         * boundary] → commit; the result is {@code none} (A-D6).
         *
         * @param delete the checked delete statement; non-null
         * @throws ConstructUnlowered on a target shape outside the closed
         *         A-D9 map
         */
        public void lowerDelete(DeleteStatement delete) {
            Objects.requireNonNull(delete, "delete must not be null");
            ExpressionNode target = delete.target();
            if (target instanceof MemberAccessExpr access) {
                Type objectType = checkedType(access.object());
                if (objectType instanceof Type.Table) {
                    lowerTableMemberDelete(delete, access);
                    return;
                }
                if (objectType instanceof Type.Class classType) {
                    lowerClassFieldDelete(delete, access, classType);
                    return;
                }
                throw new ConstructUnlowered("delete target '" + access.field() + "' on "
                    + typeName(objectType) + " (no closed A-D9 delete shape for this "
                    + "receiver: module members are E10's, array/bytes members carry no "
                    + "delete shape)");
            }
            if (target instanceof IndexExpr index) {
                Type containerType = checkedType(index.array());
                if (containerType instanceof Type.Table) {
                    lowerTableIndexDelete(delete, index);
                    return;
                }
                if (containerType instanceof Type.Array arrayType) {
                    lowerArrayIndexDelete(delete, index, arrayType);
                    return;
                }
                throw new ConstructUnlowered("delete target index on " + typeName(containerType)
                    + " (no closed A-D9 delete shape for this container: bytes indexing is "
                    + "ISSUE-0158's)");
            }
            throw new ConstructUnlowered("delete target " + target.getClass().getSimpleName()
                + " (no closed A-D9 delete shape)");
        }

        /**
         * ASSIGN VARIABLE — the single closed shape
         * {@code [valueOp, boundaryOp(VARIABLE_ASSIGNMENT),
         * commitOp(BINDING_STORE)]}: the value child, then exactly one
         * {@code VARIABLE_ASSIGNMENT} boundary carrying the target
         * binding's declared descriptor and the descriptor-kind policy
         * with input = the committed value, then the {@code BINDING_STORE}
         * commit storing {@code {binding, generation, committed value}}
         * (A-D4/A-D5). The optional {@code FUNCTION_ADAPT} adapter slot
         * between the value and the boundary is E6's creation rule — this
         * epic produces no adapter children. The {@code ASSIGN} result is
         * the committed value with {@code resultType} = the declared
         * target descriptor (A-D6).
         */
        private ValueId lowerVariableAssign(AssignmentExpr assignment, IdentifierExpr target) {
            if (closureCore) {
                return lowerVariableAssignClosure(assignment, target);
            }
            return lowerVariableAssign(assignment, target, null);
        }

        private ValueId lowerVariableAssign(AssignmentExpr assignment, IdentifierExpr target,
                                            ValueId slot) {
            ForEachFrame frame = null;
            for (ForEachFrame candidate : frames) {
                if (candidate.name().equals(target.name())) {
                    frame = candidate;
                    break;
                }
            }
            BindingId binding;
            long generation;
            BindingSite site = bindingSiteResolver == null
                ? null : bindingSiteResolver.resolve(target.name());
            if (frame != null) {
                binding = frame.binding();
                generation = frame.generation();
            } else if (site != null) {
                // The binding-environment hook (ISSUE-0444 binding-core
                // child): the store commits the dominant incarnation at
                // the assignment site (B9 R1).
                binding = site.binding();
                generation = site.generation();
            } else if (checks.symbolTable().resolve(target.name())
                    instanceof Symbol.VariableSymbol variable) {
                binding = variableBindings.computeIfAbsent(variable,
                    v -> ids.nextBindingId(module, nextOrdinal++, 0));
                generation = INITIAL_LOOP_GENERATION;
            } else {
                throw new ConstructUnlowered("assignment target '" + target.name()
                    + "' is not a variable binding in this stage's window (binding "
                    + "allocation is E6's; only loop bindings and declared variables "
                    + "carry a store identity here)");
            }
            return emitVariableAssignChain(assignment, target, binding, generation, slot);
        }

        /**
         * ASSIGN VARIABLE — the closure walk's variable-assignment arm
         * (closure-core mode): the target must be a declared binding of
         * the walk's environment; the store commits the dominant
         * incarnation at the assignment site (B9 R1) and, inside a
         * detached-body walk, registers the reference as a capture of the
         * open {@code CLOSURE_NEW} (stores reference cells — capture
         * by binding). A store of a function-typed value updates the
         * incarnation's statically tracked function identity (identity
         * preservation).
         */
        private ValueId lowerVariableAssignClosure(AssignmentExpr assignment,
                                                   IdentifierExpr target) {
            FrameResolution resolution = resolveFrame(target.name());
            if (resolution == null) {
                throw new ConstructUnlowered("assignment target '" + target.name()
                    + "' is not a declared binding of the closure walk's environment "
                    + "(module members are E10's)");
            }
            maybeRegisterCapture(target.name(), resolution);
            ValueId value = emitVariableAssignChain(assignment, target,
                resolution.entry().cell().id, resolution.entry().incarnation().generation(),
                null);
            RuntimeDescriptor targetDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(target));
            if (targetDescriptor instanceof RuntimeDescriptor.Func) {
                functionIdentity.put(resolution.entry().incarnation(), value);
            }
            return value;
        }

        /**
         * ASSIGN VARIABLE chain emission (the shared closed shape
         * {@code [valueOp, boundaryOp(VARIABLE_ASSIGNMENT),
         * commitOp(BINDING_STORE)]}): the value child, then exactly one
         * {@code VARIABLE_ASSIGNMENT} boundary carrying the target
         * binding's declared descriptor and the descriptor-kind policy
         * with input = the committed value, then the
         * {@code BINDING_STORE} commit storing
         * {@code {binding, generation, committed value}} (A-D4/A-D5).
         * The {@code ASSIGN} result is the committed value with
         * {@code resultType} = the declared target descriptor (A-D6).
         */
        private ValueId emitVariableAssignChain(AssignmentExpr assignment,
                                                IdentifierExpr target, BindingId binding,
                                                long generation, ValueId slot) {
            if (proofAnalysis) {
                // B7: any resolved variable assignment defeats exactly the
                // incarnation it names — the dominant incarnation at the
                // assignment site (conservative: any assignment in the
                // enclosing scope after the declaration, regardless of its
                // position relative to an adaptation site).
                assignmentAnalysis.recordAssignment(target.name(), binding, generation);
            }
            Type targetType = checkedType(target);
            if ((shapeMapAnalysis || e7Calls) && targetType instanceof Type.Func) {
                Type sourceType = checkedType(assignment.value());
                if (AdapterCreationRule.variableDisposition(sourceType, targetType)
                        == AdapterCreationRule.Disposition.ADAPT) {
                    // The shape-map child's adapted assignment (B6-B9):
                    // exactly one FUNCTION_ADAPT op with its closed-map
                    // mode and per-mode payload from birth, produced
                    // inside the position's own chain before its
                    // VARIABLE_ASSIGNMENT boundary and wired as the
                    // boundary's direct input (the chain's committed
                    // value).
                    return emitAdaptedVariableAssignChain(assignment, target, binding,
                        generation, (Type.Func) sourceType, (Type.Func) targetType);
                }
            }
            RuntimeDescriptor targetDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(targetType);
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            ValueId value;
            OpId valueOp;
            OpId boundaryOp;
            OpId commitOp;
            try {
                value = lowerExpression(assignment.value(), slot);
                valueOp = producerOpId(value);
                FailurePolicyId boundaryPolicy = targetDescriptor instanceof RuntimeDescriptor.Func
                    ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
                boundaryOp = emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.VARIABLE_ASSIGNMENT,
                        targetDescriptor, value,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    target.span(), boundaryPolicy, SourceOriginKind.SYNTHETIC, chainOpId);
                commitOp = emitNullOp(SemanticOpKind.BINDING_STORE,
                    new KindPayload.BindingStorePayload(binding, generation, value),
                    target.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(assignment.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(valueOp, boundaryOp, commitOp)),
                value, targetDescriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            if (creationRuleAnalysis) {
                classifyVariableAssignPosition(assignment, target, value, boundaryOp);
            }
            return value;
        }

        /**
         * The shape-map child's adapted variable-assignment chain (B6-B9):
         * the closed mode map selects exactly one mode from checker
         * facts (B7) and the per-mode payload is built from birth (B8).
         * The chain's committed value is the adapter result: the closed
         * chain shapes are {@code [sourceOp, FUNCTION_ADAPT,
         * VARIABLE_ASSIGNMENT boundaryOp, BINDING_STORE commitOp]}
         * (VALUE — the single operand completes at creation as the
         * chain's RHS child, exactly once) and {@code [FUNCTION_ADAPT,
         * VARIABLE_ASSIGNMENT boundaryOp, BINDING_STORE commitOp]}
         * (SHARED_CELL/REEVALUATE_THUNK — zero evaluation at the
         * creation site; the thunk ops live only inside the detached
         * thunk block, whose captures are generation-pinned in
         * first-reference order). The adapter op emits zero
         * {@code BOUNDARY} children; the position's own
         * {@code VARIABLE_ASSIGNMENT} boundary takes the adapter result
         * as its direct input (exact-signature pass-through), the
         * commit stores it, the {@code ASSIGN} result is the committed
         * adapter identity, and the cell's tracked function identity
         * becomes the adapter identity (loads/reads/passes/returns
         * preserve it — the adapter is an ordinary function value after
         * the commit).
         *
         * @param assignment the adapted assignment; non-null
         * @param target     the target identifier; non-null
         * @param binding    the target binding's identity; non-null
         * @param generation the target's dominant generation; non-null
         * @param sourceType the RHS's checked function type; non-null
         * @param targetType the target's checked function type; non-null
         * @return the committed adapter identity (A-D6)
         */
        private ValueId emitAdaptedVariableAssignChain(AssignmentExpr assignment,
                                                       IdentifierExpr target,
                                                       BindingId binding, long generation,
                                                       Type.Func sourceType,
                                                       Type.Func targetType) {
            RuntimeDescriptor.Func sourceSignature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(sourceType);
            RuntimeDescriptor.Func targetSignature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(targetType);
            Optional<BindingImmutabilityProof> proof = sourceProofOf(assignment.value());
            AdapterShapeMap.SourceShape shape = AdapterShapeMap.sourceShapeOf(
                assignment.value(), name -> checks.symbolTable().resolve(name));
            CaptureMode mode = AdapterShapeMap.selectMode(shape, proof);
            // REEVALUATE_THUNK: the detached thunk walks before the
            // chain opens — the thunk ops execute only at invocation
            // (E7) and must not be chain children.
            ThunkSource thunk = mode == CaptureMode.REEVALUATE_THUNK
                ? lowerThunkSource(assignment.value()) : null;
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            ValueId value;
            OpId valueOp = null;
            OpId boundaryOp;
            OpId commitOp;
            EmittedAdapter adapter;
            AdaptSourceRef sourceRef = null;
            BindingImmutabilityProof payloadProof = null;
            try {
                ValueId operand = null;
                List<ValueId> operands;
                List<RuntimeDescriptor> operandTypes;
                switch (mode) {
                    case VALUE -> {
                        if (shape == AdapterShapeMap.SourceShape.INTRINSIC_FUNCTION_VALUE) {
                            String name = ((IdentifierExpr) assignment.value()).name();
                            operand = intrinsicIdentities.get(name);
                            if (operand == null) {
                                throw new IllegalStateException("the intrinsic identity "
                                    + "of '" + name + "' was not seeded at module-init "
                                    + "top (producer defect)");
                            }
                        } else {
                            operand = lowerExpression(assignment.value());
                            valueOp = producerOpId(operand);
                            if (shape == AdapterShapeMap.SourceShape.BINDING_REFERENCE) {
                                payloadProof = proof.orElseThrow(() ->
                                    new IllegalStateException("the closed shape map "
                                        + "selects VALUE over a binding only with the "
                                        + "recorded proof (producer defect)"));
                            }
                        }
                        sourceRef = new AdaptSourceRef.Value(operand);
                        operands = List.of(operand);
                        operandTypes = List.of(sourceSignature);
                    }
                    case SHARED_CELL -> {
                        IdentifierExpr identifier = (IdentifierExpr) assignment.value();
                        FrameResolution resolution = resolveFrame(identifier.name());
                        if (resolution == null) {
                            throw new ConstructUnlowered("the SHARED_CELL source '"
                                + identifier.name() + "' is not a declared binding of the "
                                + "walk's environment (B7: a binding source resolves its "
                                + "dominant incarnation at the adaptation position)");
                        }
                        maybeRegisterCapture(identifier.name(), resolution);
                        cellKinds.registerCaptureReference(
                            resolution.entry().incarnation());
                        sourceRef = new AdaptSourceRef.SharedCell(
                            resolution.entry().cell().id,
                            resolution.entry().incarnation().generation());
                        operands = List.of();
                        operandTypes = List.of();
                    }
                    case REEVALUATE_THUNK -> {
                        sourceRef = thunkSourceRef(thunk);
                        operands = List.of();
                        operandTypes = List.of();
                    }
                    default -> throw new IllegalStateException("unreachable mode " + mode);
                }
                adapter = emitFunctionAdapt(mode, sourceRef, sourceSignature,
                    targetSignature, payloadProof, operands, operandTypes,
                    assignment.value().span());
                value = adapter.identity();
                boundaryOp = emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.VARIABLE_ASSIGNMENT,
                        targetSignature, value,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    target.span(), FailurePolicyId.FUNCTION_SIGNATURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
                commitOp = emitNullOp(SemanticOpKind.BINDING_STORE,
                    new KindPayload.BindingStorePayload(binding, generation, value),
                    target.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            List<OpId> children = valueOp != null
                ? List.of(valueOp, adapter.opId(), boundaryOp, commitOp)
                : List.of(adapter.opId(), boundaryOp, commitOp);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId,
                toSourceSpan(assignment.span()), SourceOriginKind.USER, anchor,
                currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE, children),
                value, targetSignature, FailurePolicyId.NO_DEAL_FAILURE, origin));
            recordAdapterEmission(adapter.opId(), adapter.identity(), mode, sourceRef,
                sourceSignature, targetSignature, payloadProof, boundaryOp,
                BoundaryKind.VARIABLE_ASSIGNMENT);
            if (thunk != null) {
                emitTarget().addAll(thunk.ops());
            }
            if (creationRuleAnalysis) {
                classifyVariableAssignPosition(assignment, target, value, boundaryOp);
            }
            return value;
        }

        /**
         * ASSIGN TABLE_SLOT member write — {@code [containerOp, valueOp,
         * commitOp(MEMBER_WRITE)]}: the member key is a literal string
         * (no keyOp) and the shape carries zero write-check boundaries
         * (A-D4: the spec pins table writes unchecked).
         */
        private ValueId lowerTableMemberAssign(AssignmentExpr assignment,
                                               MemberAccessExpr access) {
            return lowerTableMemberAssign(assignment, access, null);
        }

        private ValueId lowerTableMemberAssign(AssignmentExpr assignment,
                                               MemberAccessExpr access, ValueId slot) {
            if (access.object() instanceof IdentifierExpr identifier
                    && checks.symbolTable().resolve(identifier.name())
                        instanceof Symbol.ModuleSymbol) {
                throw new ConstructUnlowered("module member assignment '" + identifier.name()
                    + "." + access.field() + "' (EXPORT_* is E10's)");
            }
            RuntimeDescriptor targetDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(access));
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            ValueId value;
            OpId containerOp;
            OpId valueOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(access.object());
                containerOp = producerOpId(container);
                value = lowerExpression(assignment.value(), slot);
                valueOp = producerOpId(value);
                commitOp = emitNullOp(SemanticOpKind.MEMBER_WRITE,
                    new KindPayload.MemberWritePayload(container, access.field(), value),
                    access.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(assignment.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.TABLE_SLOT,
                    List.of(containerOp, valueOp, commitOp)),
                value, targetDescriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            return value;
        }

        /**
         * ASSIGN TABLE_SLOT index write — {@code [containerOp, keyOp,
         * valueOp, normalizeOp(INDEX_NORMALIZE TABLE_WRITE),
         * commitOp(INDEX_WRITE)]}: the key is statically {@code string}
         * by the checker's E3018 gate (A-D10), so the normalize is total
         * with no coercion; its unused {@code currentLength} operand
         * references the raw key identity (no length read for table
         * targets, A-D3).
         */
        private ValueId lowerTableIndexAssign(AssignmentExpr assignment, IndexExpr index) {
            return lowerTableIndexAssign(assignment, index, null);
        }

        private ValueId lowerTableIndexAssign(AssignmentExpr assignment, IndexExpr index,
                                              ValueId slot) {
            if (!(checkedType(index.index()) instanceof Type.String)) {
                throw new ConstructUnlowered("table index assignment key of checked type "
                    + typeName(checkedType(index.index())) + " (A-D10's E3018 checker gate "
                    + "pins every table index write key to static string — a non-string "
                    + "key reaching lowering is a producer defect)");
            }
            RuntimeDescriptor targetDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(index));
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            ValueId value;
            OpId containerOp;
            OpId keyOp;
            OpId valueOp;
            OpId normalizeOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(index.array());
                containerOp = producerOpId(container);
                ValueId key = lowerExpression(index.index());
                keyOp = producerOpId(key);
                value = lowerExpression(assignment.value(), slot);
                valueOp = producerOpId(value);
                ValueId normalizedSlot = emitChainChildOp(SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(IndexMode.TABLE_WRITE, key, key),
                    index.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.String.INSTANCE),
                    FailurePolicyId.NO_DEAL_FAILURE);
                normalizeOp = producerOpId(normalizedSlot);
                commitOp = emitNullOp(SemanticOpKind.INDEX_WRITE,
                    new KindPayload.IndexWritePayload(container, normalizedSlot, value),
                    index.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(assignment.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.TABLE_SLOT,
                    List.of(containerOp, keyOp, valueOp, normalizeOp, commitOp)),
                value, targetDescriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            return value;
        }

        /**
         * ASSIGN ARRAY_SLOT write — {@code [containerOp, keyOp, valueOp,
         * lengthOp(ARRAY_LENGTH), normalizeOp(INDEX_NORMALIZE
         * ARRAY_WRITE), boundaryOp(ARRAY_ELEMENT_ASSIGNMENT +
         * ARRAY_WRITE_BOUNDS_THEN_ELEMENT), commitOp(INDEX_WRITE)]}: the
         * length read pins at normalize time (after key and RHS), the
         * boundary enforces {@code <0}/{@code >length} then the element
         * descriptor with input = the checked RHS value, and the commit
         * appends exactly when the normalize computed
         * {@code index == length} (the append idiom's standard shape).
         */
        private ValueId lowerArrayIndexAssign(AssignmentExpr assignment, IndexExpr index,
                                              Type.Array arrayType) {
            return lowerArrayIndexAssign(assignment, index, arrayType, null);
        }

        private ValueId lowerArrayIndexAssign(AssignmentExpr assignment, IndexExpr index,
                                              Type.Array arrayType, ValueId slot) {
            RuntimeDescriptor elementDescriptor =
                containerElementDescriptor(arrayType.element());
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            ValueId value;
            OpId containerOp;
            OpId keyOp;
            OpId valueOp;
            OpId lengthOp;
            OpId normalizeOp;
            OpId boundaryOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(index.array());
                containerOp = producerOpId(container);
                ValueId key = lowerExpression(index.index());
                keyOp = producerOpId(key);
                value = lowerExpression(assignment.value(), slot);
                valueOp = producerOpId(value);
                ValueId length = emitChainChildOp(SemanticOpKind.ARRAY_LENGTH,
                    new KindPayload.ArrayLengthPayload(container), index.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE),
                    FailurePolicyId.INT32_RESULT);
                lengthOp = producerOpId(length);
                ValueId normalizedSlot = emitChainChildOp(SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_WRITE, key, length),
                    index.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE),
                    FailurePolicyId.NO_DEAL_FAILURE);
                normalizeOp = producerOpId(normalizedSlot);
                boundaryOp = emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT,
                        elementDescriptor, value,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    index.span(), FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
                    SourceOriginKind.SYNTHETIC, chainOpId);
                commitOp = emitNullOp(SemanticOpKind.INDEX_WRITE,
                    new KindPayload.IndexWritePayload(container, normalizedSlot, value),
                    index.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(assignment.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.ARRAY_SLOT,
                    List.of(containerOp, keyOp, valueOp, lengthOp, normalizeOp, boundaryOp,
                        commitOp)),
                value, elementDescriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            if (creationRuleAnalysis && elementDescriptor instanceof RuntimeDescriptor.Func) {
                // A function-typed array element position: a typed
                // boundary position never adapts (B6) — the walk's
                // direct value flow into the ARRAY_ELEMENT_ASSIGNMENT
                // boundary slot is the wiring E4's boundary producer
                // consumes; the classifier records the closed
                // classification (and the E8010 expectation for a
                // mismatched pair — the executed check is E4's).
                recordBoundaryClassification(BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT,
                    checkedType(assignment.value()), arrayType.element());
            }
            return value;
        }

        /**
         * ASSIGN CLASS_FIELD write — {@code [containerOp, valueOp,
         * commitOp(FIELD_WRITE)]}: zero chain boundary ops (the write
         * check lives in the commit op, A-D4). The E4/E5 window keeps
         * the zero-boundary {@code FIELD_WRITE} shape
         * ({@code CLASS_FIELD_ASSIGNMENT} stays admissible but is
         * produced by E9, never here). The class window (K-D6) produces
         * the pinned boundary children parented to the commit op: (1)
         * {@code UNTYPED_CLASS_INPUT} with descriptor
         * {@code class:<ClassId>} and input = the resolved receiver;
         * (2) {@code CLASS_FIELD_ASSIGNMENT} with the field's declared
         * descriptor (the unit's local layout) and input = the stored
         * value — both with the descriptor-kind policy, the canonical
         * runtime-validation realization, a {@code SYNTHETIC} origin at
         * the access span, and {@code parentOpId} = the
         * {@code FIELD_WRITE} op (K-D12). The store commits only after
         * both pass; the receiver and the key are never re-evaluated
         * (the key is the static field name).
         */
        private ValueId lowerClassFieldAssign(AssignmentExpr assignment,
                                              MemberAccessExpr access, Type.Class classType) {
            return lowerClassFieldAssign(assignment, access, classType, null);
        }

        private ValueId lowerClassFieldAssign(AssignmentExpr assignment,
                                              MemberAccessExpr access, Type.Class classType,
                                              ValueId slot) {
            RuntimeDescriptor fieldDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(access));
            ClassId classId = new ClassId(DescriptorService.semanticModulePath(classType.identity()), classType.name());
            // The class window's pinned CLASS_FIELD_ASSIGNMENT descriptor
            // (K-D6): the field's declared descriptor from the unit's
            // local layout — never the checker's optional-read nullable
            // wrap, which write contexts do not carry here anyway.
            RuntimeDescriptor declaredDescriptor = null;
            RuntimeDescriptor classDescriptor = null;
            if (classCore) {
                deal.semantic.ir.ClassLayout layout = classLayouts.get(classId);
                if (layout == null) {
                    throw new ConstructUnlowered("class field write '" + access.field()
                        + "' on " + classId + " without a local layout (the declared field "
                        + "descriptor comes from the unit's classLayouts; an imported "
                        + "class's field write is outside this epic's unit-level window)");
                }
                deal.semantic.ir.ClassLayout.FieldLayout fieldLayout = null;
                for (deal.semantic.ir.ClassLayout.FieldLayout candidate : layout.fields()) {
                    if (candidate.name().equals(access.field())) {
                        fieldLayout = candidate;
                        break;
                    }
                }
                if (fieldLayout == null) {
                    throw new ConstructUnlowered("class field write '" + access.field()
                        + "' on " + classId + " names an undeclared field (the checker "
                        + "admits declared fields only — a fact defect)");
                }
                declaredDescriptor = fieldLayout.descriptor();
                try {
                    classDescriptor = DescriptorService.describe(classType);
                } catch (DescriptorService.Defect defect) {
                    throw new ConstructUnlowered("class field write '" + access.field()
                        + "' on " + classId + " of unrepresentable receiver type ("
                        + defect.getMessage() + ")");
                }
            }
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            ValueId value;
            OpId containerOp;
            OpId valueOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(access.object());
                containerOp = producerOpId(container);
                value = lowerExpression(assignment.value(), slot);
                valueOp = producerOpId(value);
                commitOp = emitNullOp(SemanticOpKind.FIELD_WRITE,
                    new KindPayload.FieldWritePayload(container, classId, access.field(),
                        value),
                    access.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
                if (classCore) {
                    emitNullOp(SemanticOpKind.BOUNDARY,
                        new KindPayload.BoundaryPayload(BoundaryKind.UNTYPED_CLASS_INPUT,
                            classDescriptor, container,
                            new BoundaryRealization.RuntimeValidation(
                                CANONICAL_RUNTIME_VALIDATION_ID)),
                        access.span(), descriptorKindPolicy(classDescriptor),
                        SourceOriginKind.SYNTHETIC, commitOp);
                    emitNullOp(SemanticOpKind.BOUNDARY,
                        new KindPayload.BoundaryPayload(BoundaryKind.CLASS_FIELD_ASSIGNMENT,
                            declaredDescriptor, value,
                            new BoundaryRealization.RuntimeValidation(
                                CANONICAL_RUNTIME_VALIDATION_ID)),
                        access.span(), descriptorKindPolicy(declaredDescriptor),
                        SourceOriginKind.SYNTHETIC, commitOp);
                }
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(assignment.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.CLASS_FIELD,
                    List.of(containerOp, valueOp, commitOp)),
                value, fieldDescriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            return value;
        }

        /**
         * DELETE TABLE_SLOT member — {@code [containerOp,
         * commitOp(MEMBER_DELETE)]}: the literal string key, no keyOp,
         * no normalize, no bounds boundary (A-D9).
         */
        private void lowerTableMemberDelete(DeleteStatement delete, MemberAccessExpr access) {
            if (access.object() instanceof IdentifierExpr identifier
                    && checks.symbolTable().resolve(identifier.name())
                        instanceof Symbol.ModuleSymbol) {
                throw new ConstructUnlowered("module member delete '" + identifier.name()
                    + "." + access.field() + "' (EXPORT_* is E10's)");
            }
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            OpId containerOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(access.object());
                containerOp = producerOpId(container);
                commitOp = emitNullOp(SemanticOpKind.MEMBER_DELETE,
                    new KindPayload.MemberDeletePayload(container, access.field()),
                    access.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(delete.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                    List.of(containerOp, commitOp)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * DELETE TABLE_SLOT index — {@code [containerOp, keyOp,
         * normalizeOp(INDEX_NORMALIZE TABLE_WRITE),
         * commitOp(INDEX_DELETE)]}: the write-mode normalize (delete is a
         * mutation context; the closed {@link IndexMode} set is not
         * extended) with the statically-string key of A-D10's E3018 gate.
         */
        private void lowerTableIndexDelete(DeleteStatement delete, IndexExpr index) {
            if (!(checkedType(index.index()) instanceof Type.String)) {
                throw new ConstructUnlowered("table index delete key of checked type "
                    + typeName(checkedType(index.index())) + " (A-D10's E3018 checker gate "
                    + "pins every table index delete key to static string — a non-string "
                    + "key reaching lowering is a producer defect)");
            }
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            OpId containerOp;
            OpId keyOp;
            OpId normalizeOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(index.array());
                containerOp = producerOpId(container);
                ValueId key = lowerExpression(index.index());
                keyOp = producerOpId(key);
                ValueId normalizedSlot = emitChainChildOp(SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(IndexMode.TABLE_WRITE, key, key),
                    index.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.String.INSTANCE),
                    FailurePolicyId.NO_DEAL_FAILURE);
                normalizeOp = producerOpId(normalizedSlot);
                commitOp = emitNullOp(SemanticOpKind.INDEX_DELETE,
                    new KindPayload.IndexDeletePayload(container, normalizedSlot),
                    index.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(delete.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                    List.of(containerOp, keyOp, normalizeOp, commitOp)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * DELETE ARRAY_SLOT — {@code [containerOp, keyOp,
         * lengthOp(ARRAY_LENGTH), normalizeOp(INDEX_NORMALIZE
         * ARRAY_WRITE), boundaryOp(ARRAY_ELEMENT_DELETE +
         * ARRAY_DELETE_BOUNDS), commitOp(INDEX_DELETE)]}: exactly one
         * bounds boundary whose input is the normalized index (E8002
         * {@code array index out of bounds} for {@code <0}/{@code >length}
         * at the delete-target origin; {@code == length} is a permitted
         * no-op commit, A-D4).
         */
        private void lowerArrayIndexDelete(DeleteStatement delete, IndexExpr index,
                                           Type.Array arrayType) {
            RuntimeDescriptor elementDescriptor =
                containerElementDescriptor(arrayType.element());
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            OpId containerOp;
            OpId keyOp;
            OpId lengthOp;
            OpId normalizeOp;
            OpId boundaryOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(index.array());
                containerOp = producerOpId(container);
                ValueId key = lowerExpression(index.index());
                keyOp = producerOpId(key);
                ValueId length = emitChainChildOp(SemanticOpKind.ARRAY_LENGTH,
                    new KindPayload.ArrayLengthPayload(container), index.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE),
                    FailurePolicyId.INT32_RESULT);
                lengthOp = producerOpId(length);
                ValueId normalizedSlot = emitChainChildOp(SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_WRITE, key, length),
                    index.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE),
                    FailurePolicyId.NO_DEAL_FAILURE);
                normalizeOp = producerOpId(normalizedSlot);
                boundaryOp = emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.ARRAY_ELEMENT_DELETE,
                        elementDescriptor, normalizedSlot,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    index.span(), FailurePolicyId.ARRAY_DELETE_BOUNDS,
                    SourceOriginKind.SYNTHETIC, chainOpId);
                commitOp = emitNullOp(SemanticOpKind.INDEX_DELETE,
                    new KindPayload.IndexDeletePayload(container, normalizedSlot),
                    index.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(delete.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                    List.of(containerOp, keyOp, lengthOp, normalizeOp, boundaryOp, commitOp)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * DELETE CLASS_FIELD — {@code [containerOp,
         * commitOp(FIELD_DELETE)]}: no key, no normalize, no bounds
         * boundary (table and class targets run no bounds boundary;
         * A-D9). The E4/E5 window keeps the zero-boundary
         * {@code FIELD_DELETE} shape. The class window (K-D6) produces
         * the pinned boundary child parented to the commit op: exactly
         * one {@code UNTYPED_CLASS_INPUT} boundary with descriptor
         * {@code class:<ClassId>} and input = the resolved receiver —
         * the descriptor-kind policy, the canonical runtime-validation
         * realization, a {@code SYNTHETIC} origin at the access span,
         * and {@code parentOpId} = the {@code FIELD_DELETE} op (K-D12).
         * Required-field deletes never reach the IR (checker E4004).
         */
        private void lowerClassFieldDelete(DeleteStatement delete, MemberAccessExpr access,
                                           Type.Class classType) {
            ClassId classId = new ClassId(DescriptorService.semanticModulePath(classType.identity()), classType.name());
            RuntimeDescriptor classDescriptor = null;
            if (classCore) {
                try {
                    classDescriptor = DescriptorService.describe(classType);
                } catch (DescriptorService.Defect defect) {
                    throw new ConstructUnlowered("class field delete '" + access.field()
                        + "' on " + classId + " of unrepresentable receiver type ("
                        + defect.getMessage() + ")");
                }
            }
            OpId chainOpId = ids.nextOpId(module, nextOrdinal++, 0);
            chainParents.push(chainOpId);
            OpId containerOp;
            OpId commitOp;
            try {
                ValueId container = lowerExpression(access.object());
                containerOp = producerOpId(container);
                commitOp = emitNullOp(SemanticOpKind.FIELD_DELETE,
                    new KindPayload.FieldDeletePayload(container, classId, access.field()),
                    access.span(), FailurePolicyId.NO_DEAL_FAILURE,
                    SourceOriginKind.SYNTHETIC, chainOpId);
                if (classCore) {
                    emitNullOp(SemanticOpKind.BOUNDARY,
                        new KindPayload.BoundaryPayload(BoundaryKind.UNTYPED_CLASS_INPUT,
                            classDescriptor, container,
                            new BoundaryRealization.RuntimeValidation(
                                CANONICAL_RUNTIME_VALIDATION_ID)),
                        access.span(), descriptorKindPolicy(classDescriptor),
                        SourceOriginKind.SYNTHETIC, commitOp);
                }
            } finally {
                chainParents.pop();
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(delete.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(chainOpId, SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.CLASS_FIELD,
                    List.of(containerOp, commitOp)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * The producing op of a completed value: the last op in the
         * emitted list publishing that {@link ValueId} (the chain op
         * itself is emitted after its children, so a nested chain as the
         * value child resolves to the inner {@code ASSIGN} op, which
         * publishes the committed value).
         */
        private OpId producerOpId(ValueId value) {
            List<SemanticOp> target = emitTarget();
            for (int i = target.size() - 1; i >= 0; i--) {
                SemanticOp op = target.get(i);
                if (value.equals(op.result())) {
                    return op.opId();
                }
            }
            throw new IllegalStateException("no produced op publishes value " + value
                + " (producer defect)");
        }

        /**
         * Emits one value-producing chain child (the normalize-phase
         * machinery: {@code ARRAY_LENGTH} length reads and
         * {@code INDEX_NORMALIZE} slot computations) parented to the
         * innermost chain op (A-D2).
         */
        private ValueId emitChainChildOp(SemanticOpKind kind, KindPayload payload, Span span,
                                         RuntimeDescriptor resultType,
                                         FailurePolicyId policy) {
            OpId parent = chainParents.peek();
            if (parent == null) {
                throw new IllegalStateException("chain child emission outside an address "
                    + "chain (producer defect)");
            }
            ValueId value = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.SYNTHETIC, anchor, parent);
            emit(buildOp(opId, kind, payload, value, resultType, List.of(), List.of(),
                policy, origin));
            return value;
        }

        // ---------------------------------------------------------------------
        // Unit production (S1)
        // ---------------------------------------------------------------------

        /**
         * Builds the immutable unit over the session's produced
         * operations: the manifest's construct-coverage rows recorded at
         * lowering start (each row must carry the closed construct→op
         * detector table verbatim, S4), the capability claim set derived
         * through the claiming seam's full-evidence derivation under
         * {@link ContainerClaimingSeam#E5_GATE_ACTIVATION} (D9 item 5(c):
         * {@code CONTAINERS_AND_STRINGS} and {@code EVALUATION_ORDER}
         * activate at E5's gate — this epic's gate; a unit fully
         * evidencing an active row claims it, an under-evidenced row
         * defers per unit), the module-init plan over the session's init
         * block, and the produced operations in source order.
         *
         * @param constructCoverage      the manifest's reachable-construct
         *                               rows; non-null
         * @param imports                the module's resolved imports in
         *                               dependency order; non-null
         * @param interfaceHash          the interface index digest
         *                               (R-PROFILE); non-null
         * @param capabilityRegistryHash the invocation's
         *                               capability-registry digest
         *                               (R-PROFILE); non-null
         * @return the immutable unit
         */
        public LoweredModuleUnit buildUnit(Map<ConstructKind, List<SemanticOpKind>>
                                               constructCoverage,
                                           List<ModuleId> imports,
                                           String interfaceHash,
                                           String capabilityRegistryHash) {
            return buildUnit(constructCoverage, imports, interfaceHash, capabilityRegistryHash,
                ContainerClaimingSeam.E5_GATE_ACTIVATION);
        }

        /**
         * Builds the validated unit under the named claiming-seam
         * activation state (the binding-core entry passes the pinned
         * E6-gate activation — {@code BINDINGS} activates for
         * {@code BINDING_LOAD} — while the E5 window derives the claim
         * set under the E5-gate activation:
         * {@code CONTAINERS_AND_STRINGS} and {@code EVALUATION_ORDER}
         * activate).
         */
        public LoweredModuleUnit buildUnit(Map<ConstructKind, List<SemanticOpKind>>
                                               constructCoverage,
                                           List<ModuleId> imports,
                                           String interfaceHash,
                                           String capabilityRegistryHash,
                                           Set<SemanticCapability> activation) {
            Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
            Objects.requireNonNull(imports, "imports must not be null");
            Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
            Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
            Objects.requireNonNull(activation, "activation must not be null");
            EnumMap<ConstructKind, List<SemanticOpKind>> coverage =
                new EnumMap<>(ConstructKind.class);
            for (Map.Entry<ConstructKind, List<SemanticOpKind>> entry
                    : constructCoverage.entrySet()) {
                Objects.requireNonNull(entry.getKey(), "constructCoverage keys must not be null");
                Objects.requireNonNull(entry.getValue(), "constructCoverage values must not be null");
                if (!entry.getValue().equals(entry.getKey().mappedOpKinds())) {
                    throw new IllegalArgumentException(
                        "constructCoverage rows carry the closed construct→op detector "
                            + "table's mapped op kinds verbatim (S4): row " + entry.getKey()
                            + " must be exactly " + entry.getKey().mappedOpKinds()
                            + ", got " + entry.getValue());
                }
                coverage.put(entry.getKey(), List.copyOf(entry.getValue()));
            }
            // The MODULE_INIT envelope op (E3/E8; ISSUE-0590): one
            // detached module-level op per unit whose payload carries
            // the module's resolved imports and the init block (the
            // ModuleInitPlan carrier) — the MODULES R-CAPABILITY
            // required operation, so no dead schema row remains. The op
            // is not a member of any block (a module-level kind, the
            // C-D1 completeness exemption): every consumer executes it
            // as the envelope around the unit's init-block walk
            // (UNINITIALIZED -> INITIALIZING -> INITIALIZED, FAILED(error)
            // on failure, no export publication on failure).
            AnchorId moduleInitAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId moduleInitOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin moduleInitOrigin = new SourceOrigin(sourceId,
                toSourceSpan(moduleInitSpan()), SourceOriginKind.SYNTHETIC,
                moduleInitAnchor, null);
            emitUnattached(buildOp(moduleInitOpId, SemanticOpKind.MODULE_INIT,
                new KindPayload.ModuleInitPayload(module, List.copyOf(imports),
                    moduleInitBlock),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, moduleInitOrigin));
            List<SemanticOp> produced = List.copyOf(ops);
            Set<SemanticCapability> claims = ContainerClaimingSeam.deriveClaims(produced,
                activation);
            ContainerClaimingSeam.SeamResult seam = ContainerClaimingSeam.check(produced,
                activation, claims, module);
            if (seam.failure() != null) {
                throw new IllegalStateException(
                    "the claiming seam's derivation-invariant guard fired inside the unit "
                        + "producer while the unit claims exactly its derived claim set — a "
                        + "producer defect: " + seam.failure().origin());
            }
            return new LoweredModuleUnit(
                LoweredModuleUnit.FORMAT_VERSION,
                SemanticProfile.DEAL_V1_2_INT32,
                module,
                interfaceHash,
                LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                    capabilityRegistryHash),
                claims,
                coverage,
                new LinkedHashMap<>(classLayouts),
                Map.copyOf(functions),
                new ModuleInitPlan(List.copyOf(imports), moduleInitBlock),
                ExportPlan.empty(),
                registry.bindings(),
                ops());
        }

        /**
         * Builds the produced {@link StructuredBodyTable} (C-D1): the
         * ordered ops per block and the inverse membership over every
         * allocated block of the session — empty child blocks included.
         * Every op emitted by the session is a member of exactly one
         * block; the module-init block is the root of the module-level
         * statements. The table is validated with the unit by
         * {@link ControlFlowValidator} at the unit-production seam
         * (C-D2).
         *
         * @return the produced block-membership table (defensively
         *         copied by the record)
         */
        public StructuredBodyTable bodyTable() {
            Map<BlockId, List<OpId>> ordered = new java.util.LinkedHashMap<>();
            for (Map.Entry<BlockId, List<OpId>> entry : blockOps.entrySet()) {
                ordered.put(entry.getKey(), List.copyOf(entry.getValue()));
            }
            Map<OpId, BlockId> inverse = new java.util.LinkedHashMap<>();
            for (Map.Entry<OpId, BlockId> entry : opBlocks.entrySet()) {
                inverse.put(entry.getKey(), entry.getValue());
            }
            return new StructuredBodyTable(ordered, inverse);
        }

        // ---------------------------------------------------------------------
        // The full-program carrier arms (ISSUE-0410 decomposition tail)
        // ---------------------------------------------------------------------

        /**
         * Installs the module's resolved import facts (the console-stdlib
         * detection surface of the full-program entry).
         */
        public void setModuleImports(List<ResolvedImport> imports) {
            this.moduleImports = List.copyOf(imports);
        }

        /**
         * Installs the project-level class registration seeds as the
         * session's layout resolution context (ISSUE-0634; design source
         * {@code project-lowering-entry-and-registration-seeds} D4 and the
         * registration-seed contract): each unit's layout context is the
         * unit's own declared layouts first, then the seeds — the seeds
         * are never merged into the unit's {@code classLayouts} map.
         *
         * @param seeds the project's class registration seeds; non-null
         */
        public void setRegistrationSeeds(ClassRegistrationSeeds seeds) {
            this.registrationSeeds = Objects.requireNonNull(seeds,
                "seeds must not be null");
        }

        /**
         * Installs the declared conversion intrinsics of the compilation
         * (ISSUE-0634): the seed registers exactly these closed
         * {@link IntrinsicKind}s and fails closed for a module intrinsic
         * outside the declared set.
         *
         * @param kinds the declared conversion-intrinsic kinds; non-null
         */
        public void setDeclaredConversionIntrinsics(List<IntrinsicKind> kinds) {
            Objects.requireNonNull(kinds, "kinds must not be null");
            this.declaredConversionIntrinsics = List.copyOf(kinds);
        }

        /** The closed MODULE_IMPORT kind of a resolved import fact. */
        private static deal.semantic.ir.ModuleImportKind moduleImportKindOf(
                ResolvedImport importFact) {
            return switch (importFact.kind()) {
                case STDLIB -> deal.semantic.ir.ModuleImportKind.STDLIB;
                case HOST -> deal.semantic.ir.ModuleImportKind.HOST;
                default -> deal.semantic.ir.ModuleImportKind.COMPILED;
            };
        }

        /** The import fact bound to the given alias, or {@code null}. */
        private ResolvedImport importByAlias(String alias) {
            for (ResolvedImport importFact : moduleImports) {
                if (importFact.alias().equals(alias)) {
                    return importFact;
                }
            }
            return null;
        }

        /**
         * The closed descriptor-kind rule of the carrier slice: function
         * descriptors check under {@code FUNCTION_SIGNATURE}, every other
         * descriptor under {@code TYPE_DESCRIPTOR}.
         */
        private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
            return descriptor instanceof RuntimeDescriptor.Func
                ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
        }

        /**
         * The carrier's call-site dispatch: the pinned conversion
         * intrinsics, the cataloged stdlib calls, and direct user calls —
         * every other call shape (indirect callees, host/external calls,
         * async) is E7's and stays rejected. The stdlib branch runs the
         * closed checked-fact recognition predicate
         * ({@code StdlibCallRecognition} over the checker's
         * {@code ModuleSymbol} fact and the {@link
         * StdlibFunctionCatalog}): every recognized cataloged id lowers
         * through the single {@code STDLIB_CALL} arm, and no module/name
         * pair is interpreted as a stdlib algorithm here (D1).
         */
        private ValueId lowerCallSite(CallExpr call, ValueId slot) {
            try {
                return lowerIntrinsicCall(call, slot);
            } catch (ConstructUnlowered notIntrinsic) {
                // Fall through: the classifier threw before any emission.
            }
            Optional<StdlibFunctionCatalog.Entry> stdlibEntry =
                StdlibCallRecognition.recognize(call.callee(), currentCheckerScope(),
                    moduleImports);
            if (stdlibEntry.isPresent()) {
                return lowerStdlibCall(call, slot, stdlibEntry.get());
            }
            return lowerUserCall(call, slot);
        }

        /**
         * {@code STDLIB_CALL} — the carrier arm for every cataloged
         * stdlib id (D2): the checked member access's export read
         * precedes the call; the argument operands complete
         * left-to-right before the {@code STDLIB_CALL} START; the
         * payload carries {@code {function, args, effectCapability}}
         * with {@code args} in the same left-to-right order and
         * {@code effectCapability} = {@code STDLIB_SEMANTICS}; the
         * operand descriptors are the catalog entry's declared
         * parameter descriptors in order; one {@code STDLIB_PARAMETER}
         * boundary child per declared parameter in one-based order
         * (declared descriptor, descriptor-kind rule) and the single
         * {@code STDLIB_RETURN} boundary (declared return descriptor,
         * descriptor-kind rule) run by the call op itself after the
         * algorithm result — all children parented to the
         * {@code STDLIB_CALL} op. The op's {@code failurePolicy} is
         * stamped from {@link SemanticIrValidator#stdlibPolicy} — the
         * single closed algorithm→policy table, never a lowerer-local
         * copy.
         */
        private ValueId lowerStdlibCall(CallExpr call, ValueId slot,
                                        StdlibFunctionCatalog.Entry entry) {
            StdlibFunctionId function = entry.function();
            String field = entry.exportName();
            ModuleId stdlibModule = new ModuleId(entry.modulePath());
            // The member access's checked export read (the MEMBER_ACCESS
            // construct's pinned form for a module member): one
            // EXPORT_READ of the stdlib export before the STDLIB_CALL.
            RuntimeDescriptor.Func exportDescriptor =
                (RuntimeDescriptor.Func) ContainerPayloadDescriptors
                    .resultDescriptorOf(checkedType(call.callee()));
            ValueId exportValue = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId exportAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId exportOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin exportOrigin = new SourceOrigin(sourceId,
                toSourceSpan(call.callee().span()), SourceOriginKind.USER, exportAnchor,
                currentParent());
            emit(buildOp(exportOpId, SemanticOpKind.EXPORT_READ,
                new KindPayload.ExportReadPayload(stdlibModule, field,
                    exportDescriptor, exportValue),
                exportValue, exportDescriptor, List.of(), List.of(),
                FailurePolicyId.NO_DEAL_FAILURE, exportOrigin));
            // The export value's execution binding (R-FUNCTION-BINDING):
            // the stdlib module's export host function identity, recorded
            // through the registry child's host-export seam (B5 — the
            // same seam every function-typed host export read registers
            // through).
            registry.registerHostOrExternalImport(
                new FunctionAllocationIdentity(exportValue.id()),
                new KindPayload.ExportReadPayload(stdlibModule, field,
                    exportDescriptor, exportValue),
                new FunctionBindingRegistry.FunctionValueImportFacts(
                    stdlibModule, null, field, exportDescriptor),
                (ModuleRoutePlan) null);
            // The argument operands complete left-to-right before the
            // STDLIB_CALL START (parent D13 step 1); their descriptors
            // are the catalog entry's declared parameter descriptors in
            // order — the declared signature is the single authority for
            // operand and boundary descriptors alike.
            List<ValueId> args = new ArrayList<>();
            for (ExpressionNode argument : call.args()) {
                args.add(lowerExpression(argument));
            }
            List<RuntimeDescriptor> parameterDescriptors = entry.parameterDescriptors();
            if (args.size() != parameterDescriptors.size()) {
                throw new ConstructUnlowered("stdlib call " + function + " ("
                    + entry.modulePath() + "." + field + ") with " + args.size()
                    + " arguments for " + parameterDescriptors.size()
                    + " declared parameters (the checker admits exact arity only)");
            }
            RuntimeDescriptor resultType = entry.returnDescriptor();
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.STDLIB_CALL,
                new KindPayload.StdlibCallPayload(function, args,
                    SemanticCapability.STDLIB_SEMANTICS),
                result, resultType, args, parameterDescriptors,
                SemanticIrValidator.stdlibPolicy(function), origin));
            for (int i = 0; i < args.size(); i++) {
                emitChildBoundary(BoundaryKind.STDLIB_PARAMETER,
                    parameterDescriptors.get(i), args.get(i), call.span(), opId);
            }
            emitChildBoundary(BoundaryKind.STDLIB_RETURN, resultType, result, call.span(),
                opId);
            return result;
        }

        /** Builds (without emitting) one BOUNDARY child parented to the given op. */
        private SemanticOp buildChildBoundary(BoundaryKind kind, RuntimeDescriptor descriptor,
                                              ValueId input, Span span, OpId parent) {
            FailurePolicyId policy = descriptorKindPolicy(descriptor);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.SYNTHETIC, anchor, parent);
            return buildOp(opId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(kind, descriptor, input,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                null, null, policy, origin);
        }

        /** Emits one BOUNDARY child parented to the given op. */
        private void emitChildBoundary(BoundaryKind kind, RuntimeDescriptor descriptor,
                                       ValueId input, Span span, OpId parent) {
            emit(buildChildBoundary(kind, descriptor, input, span, parent));
        }

        /** Builds one BOUNDARY child with the pinned policy (the fixed-policy cells). */
        private SemanticOp buildChildBoundaryWithPolicy(BoundaryKind kind,
                RuntimeDescriptor descriptor, FailurePolicyId policy, ValueId input,
                Span span, OpId parent) {
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.SYNTHETIC, anchor, parent);
            return buildOp(opId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(kind, descriptor, input,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                null, null, policy, origin);
        }

        /** Emits one module-level op outside the block-membership table
         * ({@code EXTERNAL_ENTRY}/{@code CALLBACK_INVOKE} — executed only
         * by their triggering callers/host steps, never by the
         * module-init walk). */
        private void emitUnattached(SemanticOp op) {
            emitTarget().add(op);
        }

        /**
         * {@code CALL(DIRECT)} — the carrier's single-call-site direct
         * call arm: the callee is a declared function binding (the
         * checker's function-typed binding fact); arguments complete
         * left-to-right before the CALL START; one
         * {@code FUNCTION_PARAMETER} boundary per argument in one-based
         * order (descriptor-kind rule) parented to the CALL; the CALL
         * names the callee's reserved return boundary and its body block
         * ({@code LoweredBody}); the callee's {@code RETURN} executes the
         * single {@code FUNCTION_RETURN} boundary and the CALL terminal
         * records the checked value without re-checking. Exactly one
         * CALL site per callee in this slice — the general D13 shape
         * (indirect/host/external/async and multiple sites) is E7's.
         */
        private ValueId lowerUserCall(CallExpr call, ValueId slot) {
            if (call.callee() instanceof IdentifierExpr identifier) {
                BindingSite site = bindingSiteResolver == null
                    ? null : bindingSiteResolver.resolve(identifier.name());
                FunctionContext context = site == null
                    ? null : contextsByBindingId.get(site.binding());
                if (context == null) {
                    if (!e7Calls) {
                        throw new ConstructUnlowered("callee '" + identifier.name()
                            + "' is not a declared function binding of the carrier slice "
                            + "(function-typed parameters/loads and imported functions are "
                            + "E7's registry resolution)");
                    }
                    return lowerUserCallBinding(call, slot, identifier);
                }
                return lowerDirectCall(call, slot, identifier, context);
            }
            if (!e7Calls) {
                throw new ConstructUnlowered("call callee shape "
                    + call.callee().getClass().getSimpleName()
                    + " (the carrier slice lowers direct calls of declared function "
                    + "bindings; indirect/host/external/async calls are E7's)");
            }
            if (call.callee() instanceof MemberAccessExpr access
                    && access.object() instanceof IdentifierExpr alias) {
                return lowerUserCallImport(call, slot, access, alias);
            }
            throw new ConstructUnlowered("call callee shape "
                + call.callee().getClass().getSimpleName()
                + " (the statically-resolved call machine lowers identifier and "
                + "import-member callees; runtime callee selection is ISSUE-0531's)");
        }

        /**
         * {@code CALL(DIRECT)} — the declared-function-binding arm (the
         * D13 machine's direct cell): the callee is a declared function
         * binding (the checker's function-typed binding fact); arguments
         * complete left-to-right before the CALL START; one
         * {@code FUNCTION_PARAMETER} boundary per argument in one-based
         * order (descriptor-kind rule) parented to the CALL; the CALL
         * names the callee's reserved return boundary and its body block
         * ({@code LoweredBody}); the callee's {@code RETURN} executes the
         * single {@code FUNCTION_RETURN} boundary and the CALL terminal
         * records the checked value without re-checking. The E7 surface
         * admits any number of call sites per callee (recursion
         * included).
         */
        private ValueId lowerDirectCall(CallExpr call, ValueId slot, IdentifierExpr identifier,
                                        FunctionContext context) {
            if (e7Calls) {
                context.assignShape(InvocationShape.SOURCE_CALL, context.callSiteOpId);
            }
            // The audited callee evaluation: the identifier loads the
            // declared function binding (its result identity is the
            // closure identity — R-FUNCTION-BINDING) before the CALL.
            lowerExpression(identifier);
            // The first call site reuses the function's reserved
            // canonical call-site identity (the RETURN ops' enclosing
            // invocation); later call sites allocate fresh op identities
            // while naming the same single return boundary — the closed
            // validator admits one return boundary per callee (D13's
            // single-return-boundary shape).
            OpId callOpId = context.callSiteUsed
                ? ids.nextOpId(module, nextOrdinal++, 0)
                : context.callSiteOpId;
            context.callSiteUsed = true;
            List<ValueId> args = new ArrayList<>();
            List<RuntimeDescriptor> argTypes = new ArrayList<>();
            for (ExpressionNode argument : call.args()) {
                args.add(lowerExpression(argument));
                argTypes.add(ContainerPayloadDescriptors.resultDescriptorOf(
                    checkedType(argument)));
            }
            if (args.size() != context.signature.paramTypes().size()) {
                throw new ConstructUnlowered("call of '" + identifier.name()
                    + "' with " + args.size() + " arguments for "
                    + context.signature.paramTypes().size()
                    + " parameters (the checker admits exact arity only)");
            }
            RuntimeDescriptor resultType = context.signature.returnType();
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.USER, anchor, currentParent());
            // Parameter boundary children (built first so the CALL payload
            // names their op ids, then emitted as its children).
            List<SemanticOp> parameterBoundaryOps = new ArrayList<>();
            List<OpId> parameterBoundaryIds = new ArrayList<>();
            for (int i = 0; i < args.size(); i++) {
                SemanticOp boundary = buildChildBoundary(BoundaryKind.FUNCTION_PARAMETER,
                    context.signature.paramTypes().get(i), args.get(i), call.span(),
                    callOpId);
                parameterBoundaryOps.add(boundary);
                parameterBoundaryIds.add(boundary.opId());
            }
            emit(buildOp(callOpId, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        context.functionId, context.bodyBlock)),
                    context.signature, parameterBoundaryIds, context.returnBoundaryOpId,
                    null, context.bodyBlock, null),
                result, resultType, args, argTypes,
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            for (SemanticOp boundary : parameterBoundaryOps) {
                emit(boundary);
            }
            return result;
        }

        /**
         * {@code CALL(INDIRECT)} — the E7 arm for a function-typed
         * binding callee whose producing allocation identity resolves to
         * exactly one registered {@code FunctionExecutionBinding}: the
         * load publishes the tracked identity (loads preserve allocation
         * identity — R-FUNCTION-BINDING) and the call records the
         * resolved binding inline ({@code CallCallee.Static} — the
         * statically-resolved slice never defers binding resolution).
         * Parameter and return boundary cells follow the closed
         * boundary-assignment table per the binding shape: ×N
         * {@code FUNCTION_PARAMETER} target-signature boundaries (the
         * complete set) for bodies and adapters,
         * {@code DEAL_TO_HOST}+{@code HOST_PARAMETER} for host functions,
         * {@code EXTERNAL_PARAMETER} for external functions; the single
         * return boundary per the shape — the source body's
         * {@code FUNCTION_RETURN} run by its {@code RETURN},
         * {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} run by the call
         * op for a host function, {@code EXTERNAL_RETURN} per the
         * execution owner for an external function.
         */
        private ValueId lowerUserCallBinding(CallExpr call, ValueId slot,
                                             IdentifierExpr identifier) {
            FrameResolution resolution = resolveFrame(identifier.name());
            if (resolution == null) {
                throw new ConstructUnlowered("callee '" + identifier.name()
                    + "' is not a declared binding of the walk's environment");
            }
            ValueId identity = functionIdentity.get(resolution.entry().incarnation());
            if (identity == null) {
                throw new ConstructUnlowered("callee '" + identifier.name()
                    + "' has no statically tracked function identity (dynamic "
                    + "function values — parameters, catch bindings, iteration "
                    + "bindings — are ISSUE-0531's)");
            }
            ValueId calleeValue = lowerExpression(identifier);
            FunctionExecutionBinding binding =
                registry.bindings().get(new FunctionAllocationIdentity(calleeValue.id()));
            if (binding == null) {
                throw new ConstructUnlowered("callee '" + identifier.name()
                    + "' identity " + calleeValue
                    + " has no registered FunctionExecutionBinding (producer defect)");
            }
            return lowerIndirectCall(call, slot, binding, calleeValue, identifier.name());
        }

        /** The declared parameter count of the resolved binding shape. */
        private int bindingParamCount(FunctionExecutionBinding binding) {
            return switch (binding) {
                case FunctionExecutionBinding.AdapterBinding adapter ->
                    adapter.targetSignature().paramTypes().size();
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionContext context = contextsByFunctionId.get(body.functionId());
                    if (context == null) {
                        throw new ConstructUnlowered("the LoweredBody binding's function "
                            + body.functionId().id() + " has no lowering context "
                            + "(producer defect)");
                    }
                    yield context.signature.paramTypes().size();
                }
                case FunctionExecutionBinding.HostFunction host ->
                    host.descriptor().paramTypes().size();
                case FunctionExecutionBinding.HostFunctionValue hostValue ->
                    hostValue.descriptor().paramTypes().size();
                case FunctionExecutionBinding.ExternalFunction external ->
                    external.descriptor().paramTypes().size();
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    intrinsic.descriptor().paramTypes().size();
            };
        }

        /** The pinned host-call parameter cells: DEAL_TO_HOST + HOST_PARAMETER. */
        private void hostParameterBoundaries(RuntimeDescriptor.Func descriptor,
                List<ValueId> args, CallExpr call, OpId callOpId,
                List<SemanticOp> parameterBoundaryOps, List<OpId> parameterBoundaryIds) {
            for (int i = 0; i < args.size(); i++) {
                SemanticOp boundary = buildChildBoundaryWithPolicy(
                    BoundaryKind.DEAL_TO_HOST, descriptor.paramTypes().get(i),
                    FailurePolicyId.HOST_PARAMETER, args.get(i), call.span(), callOpId);
                parameterBoundaryOps.add(boundary);
                parameterBoundaryIds.add(boundary.opId());
            }
        }

        /** The pinned host sync-return cell run by the call op. */
        private OpId emitHostReturnBoundary(RuntimeDescriptor.Func descriptor, ValueId result,
                                            Span span, OpId callOpId) {
            SemanticOp boundary = buildChildBoundaryWithPolicy(BoundaryKind.HOST_TO_DEAL,
                descriptor.returnType(), FailurePolicyId.HOST_SYNC_RETURN, result, span,
                callOpId);
            emit(boundary);
            return boundary.opId();
        }

        /** The retained-ABI external return cell run by the call op. */
        private OpId emitExternalReturnBoundary(RuntimeDescriptor.Func descriptor,
                                                ValueId result, Span span, OpId callOpId) {
            SemanticOp boundary = buildChildBoundary(BoundaryKind.EXTERNAL_RETURN,
                descriptor.returnType(), result, span, callOpId);
            emit(boundary);
            return boundary.opId();
        }

        /** The callee unit's recorded {@code EXTERNAL_ENTRY} op id of the export. */
        private OpId externalEntryRefOf(FunctionExecutionBinding.ExternalFunction external) {
            Map<String, OpId> entries = calleeExternalEntries.get(external.moduleId());
            OpId entry = entries == null ? null : entries.get(external.exportName());
            if (entry == null) {
                throw new ConstructUnlowered("the SHARED_BODY external call of '"
                    + external.moduleId() + "'." + external.exportName()
                    + " has no recorded EXTERNAL_ENTRY in the callee unit (lower the "
                    + "callee module first and pass its recorded entries)");
            }
            return entry;
        }

        /**
         * The fail-closed producer defect of an invocation that resolves the
         * not-yet-realized intrinsic function carrier: this slice registers
         * the closed {@code IntrinsicFunction} binding only — the carrier's
         * materialization and its call execution are the function-typed-value
         * child's.
         */
        private static ConstructUnlowered intrinsicCarrierDefect(
                FunctionExecutionBinding.IntrinsicFunction intrinsic, String site) {
            return new ConstructUnlowered("the '" + intrinsic.kind() + "' intrinsic "
                + "function value resolved by " + site + " has no call execution in this "
                + "slice (the intrinsic carrier is the function-typed-value child's — "
                + "producer defect)");
        }

        /** The adapter's statically fixed source binding, or null (thunk/call-result sources). */
        private FunctionExecutionBinding staticSourceBinding(
                FunctionExecutionBinding.AdapterBinding adapter) {
            ValueId identity = switch (adapter.sourceRef()) {
                case AdaptSourceRef.SharedCell cell ->
                    identityOfIncarnation(cell.binding(), cell.generation());
                case AdaptSourceRef.Value value -> value.value();
                case AdaptSourceRef.Thunk ignored -> null;
            };
            if (identity == null) {
                return null;
            }
            return registry.bindings().get(new FunctionAllocationIdentity(identity.id()));
        }

        /** The tracked function identity of one binding incarnation, or null. */
        private ValueId identityOfIncarnation(BindingId binding, long generation) {
            BindingCell cell = cellsById.get(binding);
            if (cell == null) {
                return null;
            }
            for (BindingCoreIncarnation incarnation : cell.incarnations) {
                if (incarnation.generation() == generation) {
                    return functionIdentity.get(incarnation);
                }
            }
            return null;
        }

        /**
         * {@code CALL(INDIRECT)} — the shared indirect-call emission over
         * the resolved binding (identifier and import-member sources).
         */
        private ValueId lowerIndirectCall(CallExpr call, ValueId slot,
                                          FunctionExecutionBinding binding,
                                          ValueId calleeValue, String calleeName) {
            Type calleeCheckedType = checkedType(call.callee());
            if (!(calleeCheckedType instanceof Type.Func funcType)
                    || !(ContainerPayloadDescriptors.resultDescriptorOf(funcType)
                        instanceof RuntimeDescriptor.Func signature)) {
                throw new ConstructUnlowered("call of '" + calleeName
                    + "' without a function-typed checked descriptor (producer defect)");
            }
            if (signature.isAsync()) {
                throw new ConstructUnlowered("call of async callee '" + calleeName
                    + "' outside await (the checker's E3014 pins the shape; the await "
                    + "arm owns async starts)");
            }
            List<ValueId> args = new ArrayList<>();
            List<RuntimeDescriptor> argTypes = new ArrayList<>();
            for (ExpressionNode argument : call.args()) {
                args.add(lowerExpression(argument));
                argTypes.add(ContainerPayloadDescriptors.resultDescriptorOf(
                    checkedType(argument)));
            }
            int expectedParams = bindingParamCount(binding);
            if (args.size() != expectedParams) {
                throw new ConstructUnlowered("call of '" + calleeName + "' with "
                    + args.size() + " arguments for " + expectedParams
                    + " parameters (the checker admits exact arity only)");
            }
            RuntimeDescriptor resultType = signature.returnType();
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.USER, anchor, currentParent());
            // The first call site of a body-source resolution reuses the
            // source function's reserved canonical call-site identity
            // (its RETURN ops name it); later sites allocate fresh op
            // identities naming the same single return boundary.
            OpId callOpId;
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionContext sourceContext =
                        contextsByFunctionId.get(body.functionId());
                    if (sourceContext == null) {
                        throw new ConstructUnlowered("the LoweredBody binding of '"
                            + calleeName + "' has no lowering context (producer defect)");
                    }
                    sourceContext.assignShape(InvocationShape.SOURCE_CALL,
                        sourceContext.callSiteOpId);
                    callOpId = sourceContext.callSiteUsed
                        ? ids.nextOpId(module, nextOrdinal++, 0)
                        : sourceContext.callSiteOpId;
                    sourceContext.callSiteUsed = true;
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    FunctionExecutionBinding source = staticSourceBinding(adapter);
                    if (source instanceof FunctionExecutionBinding.LoweredBody body) {
                        FunctionContext sourceContext =
                            contextsByFunctionId.get(body.functionId());
                        if (sourceContext == null) {
                            throw new ConstructUnlowered("the adapter's body-source "
                                + "binding has no lowering context (producer defect)");
                        }
                        sourceContext.assignShape(InvocationShape.SOURCE_CALL,
                            sourceContext.callSiteOpId);
                        callOpId = sourceContext.callSiteUsed
                            ? ids.nextOpId(module, nextOrdinal++, 0)
                            : sourceContext.callSiteOpId;
                        sourceContext.callSiteUsed = true;
                    } else {
                        callOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    }
                }
                default -> callOpId = ids.nextOpId(module, nextOrdinal++, 0);
            }
            // Parameter boundary cells per the closed table.
            List<SemanticOp> parameterBoundaryOps = new ArrayList<>();
            List<OpId> parameterBoundaryIds = new ArrayList<>();
            switch (binding) {
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    for (int i = 0; i < args.size(); i++) {
                        SemanticOp boundary = buildChildBoundary(
                            BoundaryKind.FUNCTION_PARAMETER,
                            adapter.targetSignature().paramTypes().get(i), args.get(i),
                            call.span(), callOpId);
                        parameterBoundaryOps.add(boundary);
                        parameterBoundaryIds.add(boundary.opId());
                    }
                }
                case FunctionExecutionBinding.LoweredBody body -> {
                    for (int i = 0; i < args.size(); i++) {
                        SemanticOp boundary = buildChildBoundary(
                            BoundaryKind.FUNCTION_PARAMETER,
                            signature.paramTypes().get(i), args.get(i), call.span(),
                            callOpId);
                        parameterBoundaryOps.add(boundary);
                        parameterBoundaryIds.add(boundary.opId());
                    }
                }
                case FunctionExecutionBinding.HostFunction host ->
                    hostParameterBoundaries(host.descriptor(), args, call, callOpId,
                        parameterBoundaryOps, parameterBoundaryIds);
                case FunctionExecutionBinding.HostFunctionValue hostValue ->
                    hostParameterBoundaries(hostValue.descriptor(), args, call, callOpId,
                        parameterBoundaryOps, parameterBoundaryIds);
                case FunctionExecutionBinding.ExternalFunction external -> {
                    for (int i = 0; i < args.size(); i++) {
                        SemanticOp boundary = buildChildBoundary(
                            BoundaryKind.EXTERNAL_PARAMETER,
                            external.descriptor().paramTypes().get(i), args.get(i),
                            call.span(), callOpId);
                        parameterBoundaryOps.add(boundary);
                        parameterBoundaryIds.add(boundary.opId());
                    }
                }
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicCarrierDefect(intrinsic, "the call of '" + calleeName
                        + "'");
            }
            // The single return boundary per the closed table.
            OpId returnBoundaryOpId = null;
            OpId externalEntryRef = null;
            BlockId bodyBlock = null;
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionContext context = contextsByFunctionId.get(body.functionId());
                    if (context == null) {
                        throw new ConstructUnlowered("the LoweredBody binding of '"
                            + calleeName + "' has no lowering context (producer defect)");
                    }
                    context.assignShape(InvocationShape.SOURCE_CALL, context.callSiteOpId);
                    returnBoundaryOpId = context.returnBoundaryOpId;
                    bodyBlock = context.bodyBlock;
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    FunctionExecutionBinding source = staticSourceBinding(adapter);
                    if (source == null) {
                        throw new ConstructUnlowered("adapter invocation of '" + calleeName
                            + "' whose source identity is not statically fixed "
                            + "(REEVALUATE_THUNK call-result sources are ISSUE-0531's)");
                    }
                    switch (source) {
                        case FunctionExecutionBinding.LoweredBody body -> {
                            FunctionContext context =
                                contextsByFunctionId.get(body.functionId());
                            if (context == null) {
                                throw new ConstructUnlowered("the adapter's body-source "
                                    + "binding has no lowering context (producer defect)");
                            }
                            context.assignShape(InvocationShape.SOURCE_CALL,
                                context.callSiteOpId);
                            returnBoundaryOpId = context.returnBoundaryOpId;
                        }
                        case FunctionExecutionBinding.HostFunction host ->
                            returnBoundaryOpId = emitHostReturnBoundary(host.descriptor(),
                                result, call.span(), callOpId);
                        case FunctionExecutionBinding.HostFunctionValue hostValue ->
                            returnBoundaryOpId = emitHostReturnBoundary(
                                hostValue.descriptor(), result, call.span(), callOpId);
                        case FunctionExecutionBinding.ExternalFunction external -> {
                            if (external.executionOwner()
                                    == ExternalExecutionOwner.SHARED_BODY) {
                                externalEntryRef = externalEntryRefOf(external);
                            } else {
                                returnBoundaryOpId = emitExternalReturnBoundary(
                                    external.descriptor(), result, call.span(), callOpId);
                            }
                        }
                        case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                            throw intrinsicCarrierDefect(intrinsic, "the adapted call "
                                + "of '" + calleeName + "'");
                        case FunctionExecutionBinding.AdapterBinding nested ->
                            throw new ConstructUnlowered("nested adapter source of '"
                                + calleeName + "' (adapter-of-adapter invocation is "
                                + "ISSUE-0531's)");
                    }
                }
                case FunctionExecutionBinding.HostFunction host ->
                    returnBoundaryOpId = emitHostReturnBoundary(host.descriptor(), result,
                        call.span(), callOpId);
                case FunctionExecutionBinding.HostFunctionValue hostValue ->
                    returnBoundaryOpId = emitHostReturnBoundary(hostValue.descriptor(),
                        result, call.span(), callOpId);
                case FunctionExecutionBinding.ExternalFunction external -> {
                    if (external.executionOwner() == ExternalExecutionOwner.SHARED_BODY) {
                        externalEntryRef = externalEntryRefOf(external);
                    } else {
                        returnBoundaryOpId = emitExternalReturnBoundary(
                            external.descriptor(), result, call.span(), callOpId);
                    }
                }
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicCarrierDefect(intrinsic, "the call of '" + calleeName
                        + "'");
            }
            emit(buildOp(callOpId, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Static(binding),
                    signature, parameterBoundaryIds, returnBoundaryOpId, null, bodyBlock,
                    externalEntryRef),
                result, resultType, args, argTypes,
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            for (SemanticOp boundary : parameterBoundaryOps) {
                emit(boundary);
            }
            return result;
        }

        /** One imported host/external export materialization (read + registration). */
        private record ImportMaterialization(FunctionExecutionBinding binding,
                                             RuntimeDescriptor.Func descriptor) {
        }

        /**
         * The import-member callee arm: {@code alias.export(args)} on a
         * host or compiled import. The checked export read materializes
         * the function value ({@code EXPORT_READ} + exactly one
         * {@code FunctionExecutionBinding} registration through the
         * registry seam — {@code HostFunction} for host imports,
         * {@code ExternalFunction} with the route-derived execution
         * owner for compiled imports).
         */
        private ImportMaterialization materializeImportRead(MemberAccessExpr access,
                                                            IdentifierExpr alias) {
            if (!(checks.symbolTable().resolve(alias.name()) instanceof Symbol.ModuleSymbol)) {
                throw new ConstructUnlowered("callee member base '" + alias.name()
                    + "' is not a module import (module member reads are EXPORT_READ "
                    + "shapes)");
            }
            ResolvedImport importFact = importByAlias(alias.name());
            if (importFact == null) {
                throw new ConstructUnlowered("import alias '" + alias.name()
                    + "' without a resolved import fact (a missing checker fact is a "
                    + "producer defect)");
            }
            if (importFact.kind() == ExternalModuleKind.STDLIB) {
                throw new ConstructUnlowered("stdlib member call not recognized by the "
                    + "closed stdlib catalog (the STDLIB_CALL arm owns cataloged stdlib "
                    + "ids; unrecognized stdlib members are not calls)");
            }
            RuntimeDescriptor.Func descriptor = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(access));
            ValueId exportValue = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId exportAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId exportOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin exportOrigin = new SourceOrigin(sourceId,
                toSourceSpan(access.span()), SourceOriginKind.USER, exportAnchor,
                currentParent());
            KindPayload.ExportReadPayload exportPayload =
                new KindPayload.ExportReadPayload(importFact.resolvedModuleId(),
                    access.field(), descriptor, exportValue);
            emit(buildOp(exportOpId, SemanticOpKind.EXPORT_READ, exportPayload, exportValue,
                descriptor, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                exportOrigin));
            FunctionBindingRegistry.FunctionValueImportFacts facts = switch (importFact.kind()) {
                case HOST -> new FunctionBindingRegistry.FunctionValueImportFacts(
                    importFact.resolvedModuleId(), null, access.field(), descriptor);
                case IMPLEMENTATION -> new FunctionBindingRegistry.FunctionValueImportFacts(
                    null, importFact.resolvedModuleId(), access.field(), descriptor);
                default -> throw new ConstructUnlowered("import kind "
                    + importFact.kind() + " is not a host/compiled call source");
            };
            registry.registerHostOrExternalImportWithRoutes(
                new FunctionAllocationIdentity(exportValue.id()), exportPayload, facts,
                calleeRoutes);
            FunctionExecutionBinding binding = registry.bindings().get(
                new FunctionAllocationIdentity(exportValue.id()));
            if (binding == null) {
                throw new IllegalStateException("the import materialization of '"
                    + alias.name() + "." + access.field()
                    + "' registered no binding (producer defect)");
            }
            return new ImportMaterialization(binding, descriptor);
        }

        /** The import-member sync call arm (CALL(HOST)/CALL(EXTERNAL)). */
        private ValueId lowerUserCallImport(CallExpr call, ValueId slot,
                                            MemberAccessExpr access, IdentifierExpr alias) {
            ImportMaterialization materialization = materializeImportRead(access, alias);
            return lowerImportCall(call, slot, materialization.binding(),
                materialization.descriptor());
        }

        /**
         * {@code CALL(HOST)}/{@code CALL(EXTERNAL)} — the imported-callee
         * arms: the parameter boundaries follow the pinned host/external
         * cells ({@code DEAL_TO_HOST}+{@code HOST_PARAMETER},
         * {@code EXTERNAL_PARAMETER}); the single return boundary follows
         * the owner — {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} run
         * by the call op for host functions, the callee
         * {@code EXTERNAL_ENTRY}'s {@code EXTERNAL_RETURN} for
         * {@code SHARED_BODY} externals (no caller-side boundary), and
         * the call-op {@code EXTERNAL_RETURN} for {@code RETAINED_ABI}
         * externals.
         */
        private ValueId lowerImportCall(CallExpr call, ValueId slot,
                                        FunctionExecutionBinding binding,
                                        RuntimeDescriptor.Func descriptor) {
            if (descriptor.isAsync()) {
                throw new ConstructUnlowered("async import call outside await (the "
                    + "checker's E3014 pins the shape; the await arm owns async starts)");
            }
            List<ValueId> args = new ArrayList<>();
            List<RuntimeDescriptor> argTypes = new ArrayList<>();
            for (ExpressionNode argument : call.args()) {
                args.add(lowerExpression(argument));
                argTypes.add(ContainerPayloadDescriptors.resultDescriptorOf(
                    checkedType(argument)));
            }
            if (args.size() != descriptor.paramTypes().size()) {
                throw new ConstructUnlowered("import call with " + args.size()
                    + " arguments for " + descriptor.paramTypes().size()
                    + " parameters (the checker admits exact arity only)");
            }
            RuntimeDescriptor resultType = descriptor.returnType();
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            OpId callOpId = ids.nextOpId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.USER, anchor, currentParent());
            List<SemanticOp> parameterBoundaryOps = new ArrayList<>();
            List<OpId> parameterBoundaryIds = new ArrayList<>();
            boolean host = binding instanceof FunctionExecutionBinding.HostFunction
                || binding instanceof FunctionExecutionBinding.HostFunctionValue;
            if (host) {
                hostParameterBoundaries(descriptor, args, call, callOpId,
                    parameterBoundaryOps, parameterBoundaryIds);
            } else {
                for (int i = 0; i < args.size(); i++) {
                    SemanticOp boundary = buildChildBoundary(BoundaryKind.EXTERNAL_PARAMETER,
                        descriptor.paramTypes().get(i), args.get(i), call.span(), callOpId);
                    parameterBoundaryOps.add(boundary);
                    parameterBoundaryIds.add(boundary.opId());
                }
            }
            OpId returnBoundaryOpId = null;
            OpId externalEntryRef = null;
            if (host) {
                returnBoundaryOpId = emitHostReturnBoundary(descriptor, result, call.span(),
                    callOpId);
            } else if (binding instanceof FunctionExecutionBinding.ExternalFunction external) {
                if (external.executionOwner() == ExternalExecutionOwner.SHARED_BODY) {
                    externalEntryRef = externalEntryRefOf(external);
                } else {
                    returnBoundaryOpId = emitExternalReturnBoundary(descriptor, result,
                        call.span(), callOpId);
                }
            } else {
                throw new IllegalStateException("import call binding shape "
                    + binding.getClass().getSimpleName() + " (producer defect)");
            }
            CallMode mode = host ? CallMode.HOST : CallMode.EXTERNAL;
            emit(buildOp(callOpId, SemanticOpKind.CALL,
                new KindPayload.CallPayload(mode, new KindPayload.CallCallee.Static(binding),
                    descriptor, parameterBoundaryIds, returnBoundaryOpId, null, null,
                    externalEntryRef),
                result, resultType, args, argTypes,
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            for (SemanticOp boundary : parameterBoundaryOps) {
                emit(boundary);
            }
            return result;
        }

        /**
         * {@code ASYNC_START} + {@code AWAIT} — the E7 await arm: the
         * checked await callee is an async call (the checker's E3012/
         * E3013/E3014 pin the shape). The callee and every argument
         * operand complete left-to-right before the {@code ASYNC_START}
         * START; the parameter boundaries follow the closed table per the
         * resolved binding; the op publishes exactly one token per call
         * (canonical for DEAL bodies and async host operations, an alias
         * through {@code ExternalAsyncLink} for async externals, an
         * {@code ADAPTER_INNER} alias for adapter-over-async); the single
         * {@code AWAIT} runs exactly one {@code ASYNC_COMPLETION}
         * boundary at the await site.
         */
        private ValueId lowerAwaitExpression(AwaitExpression awaitExpression, ValueId slot) {
            if (!(awaitExpression.callee() instanceof CallExpr call)) {
                throw new ConstructUnlowered("await callee shape "
                    + awaitExpression.callee().getClass().getSimpleName()
                    + " (the parser's E1042 pins await over a call)");
            }
            return lowerAwaitCall(call, slot, awaitExpression.span());
        }

        private ValueId lowerAwaitCall(CallExpr call, ValueId slot, Span awaitSpan) {
            if (call.callee() instanceof IdentifierExpr identifier) {
                BindingSite site = bindingSiteResolver == null
                    ? null : bindingSiteResolver.resolve(identifier.name());
                FunctionContext context = site == null
                    ? null : contextsByBindingId.get(site.binding());
                if (context != null) {
                    return lowerAwaitDeclared(call, slot, awaitSpan, identifier, context);
                }
                FrameResolution resolution = resolveFrame(identifier.name());
                if (resolution == null) {
                    throw new ConstructUnlowered("await callee '" + identifier.name()
                        + "' is not a declared binding of the walk's environment");
                }
                ValueId identity = functionIdentity.get(resolution.entry().incarnation());
                if (identity == null) {
                    throw new ConstructUnlowered("await callee '" + identifier.name()
                        + "' has no statically tracked function identity (dynamic "
                        + "function values are ISSUE-0531's)");
                }
                ValueId calleeValue = lowerExpression(identifier);
                FunctionExecutionBinding binding = registry.bindings().get(
                    new FunctionAllocationIdentity(calleeValue.id()));
                if (binding == null) {
                    throw new ConstructUnlowered("await callee '" + identifier.name()
                        + "' identity " + calleeValue
                        + " has no registered FunctionExecutionBinding (producer defect)");
                }
                if (binding instanceof FunctionExecutionBinding.AdapterBinding adapter) {
                    return lowerAdapterOverAsync(call, slot, awaitSpan, adapter,
                        identifier.name());
                }
                return lowerAsyncStart(call, slot, awaitSpan, binding, false);
            }
            if (call.callee() instanceof MemberAccessExpr access
                    && access.object() instanceof IdentifierExpr alias) {
                ImportMaterialization materialization = materializeImportRead(access, alias);
                return lowerAsyncStart(call, slot, awaitSpan, materialization.binding(),
                    false);
            }
            throw new ConstructUnlowered("await callee shape "
                + call.callee().getClass().getSimpleName()
                + " (the statically-resolved await arm lowers identifier and "
                + "import-member callees; runtime callee selection is ISSUE-0531's)");
        }

        /** The awaited declared-function arm: ASYNC_START(DEAL_BODY) + AWAIT. */
        private ValueId lowerAwaitDeclared(CallExpr call, ValueId slot, Span awaitSpan,
                                           IdentifierExpr identifier,
                                           FunctionContext context) {
            if (!context.signature.isAsync()) {
                throw new ConstructUnlowered("await of non-async function '"
                    + identifier.name() + "' (the checker's E3013 pins the shape)");
            }
            context.assignShape(InvocationShape.SOURCE_ASYNC, context.callSiteOpId);
            lowerExpression(identifier);
            return lowerAsyncStart(call, slot, awaitSpan,
                new FunctionExecutionBinding.LoweredBody(context.functionId,
                    context.bodyBlock),
                false);
        }

        /**
         * The shared {@code ASYNC_START}+{@code AWAIT} emission over the
         * resolved binding: the parameter-boundary cells per the closed
         * table, one token per call, and exactly one
         * {@code ASYNC_COMPLETION} boundary at the await site.
         */
        private ValueId lowerAsyncStart(CallExpr call, ValueId slot, Span awaitSpan,
                                        FunctionExecutionBinding binding, boolean nested) {
            List<ValueId> args = new ArrayList<>();
            List<RuntimeDescriptor> argTypes = new ArrayList<>();
            for (ExpressionNode argument : call.args()) {
                args.add(lowerExpression(argument));
                argTypes.add(ContainerPayloadDescriptors.resultDescriptorOf(
                    checkedType(argument)));
            }
            RuntimeDescriptor.Func signature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(call.callee()));
            AsyncStartSource source;
            OpId startOpId;
            OpId returnBoundaryOpId = null;
            String hostOperationLabel = null;
            ExternalAsyncLink externalAsyncLink = null;
            AsyncTokenId token;
            FailurePolicyId policy = FailurePolicyId.NO_DEAL_FAILURE;
            List<SemanticOp> parameterBoundaryOps = new ArrayList<>();
            List<OpId> parameterBoundaryIds = new ArrayList<>();
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionContext context = contextsByFunctionId.get(body.functionId());
                    if (context == null) {
                        throw new ConstructUnlowered("the async body binding's function "
                            + body.functionId().id()
                            + " has no lowering context (producer defect)");
                    }
                    context.assignShape(InvocationShape.SOURCE_ASYNC, context.callSiteOpId);
                    source = AsyncStartSource.DEAL_BODY;
                    startOpId = context.callSiteUsed
                        ? ids.nextOpId(module, nextOrdinal++, 0) : context.callSiteOpId;
                    context.callSiteUsed = true;
                    returnBoundaryOpId = context.returnBoundaryOpId;
                    token = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.DEAL_BODY_TASK);
                    if (args.size() != context.signature.paramTypes().size()) {
                        throw new ConstructUnlowered("async call with " + args.size()
                            + " arguments for " + context.signature.paramTypes().size()
                            + " parameters (the checker admits exact arity only)");
                    }
                    for (int i = 0; i < args.size(); i++) {
                        SemanticOp boundary = buildChildBoundary(
                            BoundaryKind.FUNCTION_PARAMETER,
                            context.signature.paramTypes().get(i), args.get(i),
                            call.span(), startOpId);
                        parameterBoundaryOps.add(boundary);
                        parameterBoundaryIds.add(boundary.opId());
                    }
                }
                case FunctionExecutionBinding.HostFunction host -> {
                    source = AsyncStartSource.HOST;
                    startOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    hostOperationLabel = host.hostModuleId().path() + "." + host.exportName();
                    token = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.HOST_OPERATION);
                    policy = FailurePolicyId.ASYNC_OPERATION_HANDLE;
                    if (args.size() != host.descriptor().paramTypes().size()) {
                        throw new ConstructUnlowered("async host call with " + args.size()
                            + " arguments for " + host.descriptor().paramTypes().size()
                            + " parameters (the checker admits exact arity only)");
                    }
                    hostParameterBoundaries(host.descriptor(), args, call, startOpId,
                        parameterBoundaryOps, parameterBoundaryIds);
                }
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    source = AsyncStartSource.HOST;
                    startOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    hostOperationLabel = hostValue.hostModuleId().path() + ".@value";
                    token = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.HOST_OPERATION);
                    policy = FailurePolicyId.ASYNC_OPERATION_HANDLE;
                    if (args.size() != hostValue.descriptor().paramTypes().size()) {
                        throw new ConstructUnlowered("async host-value call with "
                            + args.size() + " arguments for "
                            + hostValue.descriptor().paramTypes().size()
                            + " parameters (the checker admits exact arity only)");
                    }
                    hostParameterBoundaries(hostValue.descriptor(), args, call, startOpId,
                        parameterBoundaryOps, parameterBoundaryIds);
                }
                case FunctionExecutionBinding.ExternalFunction external -> {
                    source = AsyncStartSource.EXTERNAL;
                    startOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    Map<String, OpId> entries = calleeExternalEntries.get(external.moduleId());
                    OpId entryOp = entries == null ? null : entries.get(external.exportName());
                    if (entryOp == null) {
                        throw new ConstructUnlowered("the async external call of '"
                            + external.moduleId() + "'." + external.exportName()
                            + " has no recorded EXTERNAL_ENTRY in the callee unit");
                    }
                    AsyncTokenId calleeToken = new AsyncTokenId.Canonical(entryOp.id(),
                        AsyncTokenOwner.DEAL_BODY_TASK);
                    token = new AsyncTokenId.Alias(
                        ids.nextTokenId(module, nextOrdinal++, 0), calleeToken,
                        AsyncLinkKind.EXTERNAL_LINK);
                    externalAsyncLink = new ExternalAsyncLink(external.moduleId(),
                        external.exportName(), calleeToken);
                    if (args.size() != external.descriptor().paramTypes().size()) {
                        throw new ConstructUnlowered("async external call with "
                            + args.size() + " arguments for "
                            + external.descriptor().paramTypes().size()
                            + " parameters (the checker admits exact arity only)");
                    }
                    for (int i = 0; i < args.size(); i++) {
                        SemanticOp boundary = buildChildBoundary(
                            BoundaryKind.EXTERNAL_PARAMETER,
                            external.descriptor().paramTypes().get(i), args.get(i),
                            call.span(), startOpId);
                        parameterBoundaryOps.add(boundary);
                        parameterBoundaryIds.add(boundary.opId());
                    }
                }
                case FunctionExecutionBinding.AdapterBinding adapter ->
                    throw new ConstructUnlowered("adapter-over-async lower via "
                        + "lowerAdapterOverAsync (producer defect)");
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicCarrierDefect(intrinsic, "the await call");
            }
            RuntimeDescriptor completion = signature.returnType();
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(startOpId, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(binding), source,
                    nested ? ParameterBoundaryMode.ELIDED_BY_ADAPTER : ParameterBoundaryMode.RUN,
                    parameterBoundaryIds, completion, returnBoundaryOpId,
                    hostOperationLabel, externalAsyncLink),
                token, InternalResultType.INTERNAL_ASYNC, args, argTypes, policy, origin));
            for (SemanticOp boundary : parameterBoundaryOps) {
                emit(boundary);
            }
            return lowerAwait(token, completion, awaitSpan, slot);
        }

        /**
         * Adapter-over-async: the outer {@code ASYNC_START} carries the
         * {@code AdapterBinding} with the ×N target-signature parameter
         * boundaries (the complete set), an {@code ADAPTER_INNER} alias
         * token, and zero return boundaries; the nested source
         * {@code ASYNC_START} (parented to the outer op) carries
         * {@code ELIDED_BY_ADAPTER}, zero parameter boundaries, the
         * leading M argument operands, and its own per-resolution
         * terminal per the statically fixed source binding.
         */
        private ValueId lowerAdapterOverAsync(CallExpr call, ValueId slot, Span awaitSpan,
                FunctionExecutionBinding.AdapterBinding adapter, String calleeName) {
            FunctionExecutionBinding source = staticSourceBinding(adapter);
            if (source == null) {
                throw new ConstructUnlowered("adapter-over-async of '" + calleeName
                    + "' whose source identity is not statically fixed "
                    + "(REEVALUATE_THUNK call-result sources are ISSUE-0531's)");
            }
            RuntimeDescriptor.Func target = adapter.targetSignature();
            RuntimeDescriptor.Func sourceSignature = adapter.sourceSignature();
            List<ValueId> args = new ArrayList<>();
            List<RuntimeDescriptor> argTypes = new ArrayList<>();
            for (ExpressionNode argument : call.args()) {
                args.add(lowerExpression(argument));
                argTypes.add(ContainerPayloadDescriptors.resultDescriptorOf(
                    checkedType(argument)));
            }
            if (args.size() != target.paramTypes().size()) {
                throw new ConstructUnlowered("adapter-over-async call of '" + calleeName
                    + "' with " + args.size() + " arguments for "
                    + target.paramTypes().size()
                    + " target parameters (the checker admits exact arity only)");
            }
            int m = sourceSignature.paramTypes().size();
            OpId outerOpId = ids.nextOpId(module, nextOrdinal++, 0);
            AnchorId outerAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            // The nested source op (its token pins the outer alias
            // referent and the source function's RETURN enclosing
            // invocation).
            OpId nestedOpId;
            AsyncTokenId sourceToken;
            OpId nestedReturnBoundary = null;
            String nestedHostLabel = null;
            ExternalAsyncLink nestedLink = null;
            AsyncStartSource nestedSource;
            FailurePolicyId nestedPolicy = FailurePolicyId.NO_DEAL_FAILURE;
            switch (source) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionContext context = contextsByFunctionId.get(body.functionId());
                    if (context == null) {
                        throw new ConstructUnlowered("the adapter's body-source binding "
                            + "has no lowering context (producer defect)");
                    }
                    context.assignShape(InvocationShape.SOURCE_ASYNC, context.callSiteOpId);
                    nestedOpId = context.callSiteUsed
                        ? ids.nextOpId(module, nextOrdinal++, 0) : context.callSiteOpId;
                    context.callSiteUsed = true;
                    nestedReturnBoundary = context.returnBoundaryOpId;
                    nestedSource = AsyncStartSource.DEAL_BODY;
                    sourceToken = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.DEAL_BODY_TASK);
                }
                case FunctionExecutionBinding.HostFunction host -> {
                    nestedOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    nestedHostLabel = host.hostModuleId().path() + "." + host.exportName();
                    nestedSource = AsyncStartSource.HOST;
                    nestedPolicy = FailurePolicyId.ASYNC_OPERATION_HANDLE;
                    sourceToken = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.HOST_OPERATION);
                }
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    nestedOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    nestedHostLabel = hostValue.hostModuleId().path() + ".@value";
                    nestedSource = AsyncStartSource.HOST;
                    nestedPolicy = FailurePolicyId.ASYNC_OPERATION_HANDLE;
                    sourceToken = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.HOST_OPERATION);
                }
                case FunctionExecutionBinding.ExternalFunction external -> {
                    nestedOpId = ids.nextOpId(module, nextOrdinal++, 0);
                    Map<String, OpId> entries = calleeExternalEntries.get(external.moduleId());
                    OpId entryOp = entries == null ? null : entries.get(external.exportName());
                    if (entryOp == null) {
                        throw new ConstructUnlowered("the adapter's async external source '"
                            + external.moduleId() + "'." + external.exportName()
                            + " has no recorded EXTERNAL_ENTRY in the callee unit");
                    }
                    AsyncTokenId calleeToken = new AsyncTokenId.Canonical(entryOp.id(),
                        AsyncTokenOwner.DEAL_BODY_TASK);
                    sourceToken = new AsyncTokenId.Canonical(
                        ids.nextTokenId(module, nextOrdinal++, 0),
                        AsyncTokenOwner.DEAL_BODY_TASK);
                    nestedLink = new ExternalAsyncLink(external.moduleId(),
                        external.exportName(), calleeToken);
                    nestedSource = AsyncStartSource.EXTERNAL;
                }
                case FunctionExecutionBinding.AdapterBinding nestedAdapter ->
                    throw new ConstructUnlowered("nested adapter source of '" + calleeName
                        + "' (adapter-of-adapter invocation is ISSUE-0531's)");
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicCarrierDefect(intrinsic, "the adapter-over-async call "
                        + "of '" + calleeName + "'");
            }
            AsyncTokenId outerToken = new AsyncTokenId.Alias(
                ids.nextTokenId(module, nextOrdinal++, 0), sourceToken,
                AsyncLinkKind.ADAPTER_INNER);
            // The nested source op: ELIDED_BY_ADAPTER, zero parameter
            // boundaries, operands = the leading M argument values.
            List<ValueId> leadingArgs = List.copyOf(args.subList(0, m));
            List<RuntimeDescriptor> leadingTypes = List.copyOf(argTypes.subList(0, m));
            AnchorId nestedAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin nestedOrigin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.SYNTHETIC, nestedAnchor, outerOpId);
            emit(buildOp(nestedOpId, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(source), nestedSource,
                    ParameterBoundaryMode.ELIDED_BY_ADAPTER, List.of(),
                    sourceSignature.returnType(), nestedReturnBoundary, nestedHostLabel,
                    nestedLink),
                sourceToken, InternalResultType.INTERNAL_ASYNC, leadingArgs, leadingTypes,
                nestedPolicy, nestedOrigin));
            // The outer op: the adapter binding, DEAL_BODY, RUN, ×N
            // target-signature FUNCTION_PARAMETER boundaries, zero return
            // boundaries, the ADAPTER_INNER alias token.
            List<SemanticOp> parameterBoundaryOps = new ArrayList<>();
            List<OpId> parameterBoundaryIds = new ArrayList<>();
            for (int i = 0; i < args.size(); i++) {
                SemanticOp boundary = buildChildBoundary(BoundaryKind.FUNCTION_PARAMETER,
                    target.paramTypes().get(i), args.get(i), call.span(), outerOpId);
                parameterBoundaryOps.add(boundary);
                parameterBoundaryIds.add(boundary.opId());
            }
            SourceOrigin outerOrigin = new SourceOrigin(sourceId, toSourceSpan(call.span()),
                SourceOriginKind.USER, outerAnchor, currentParent());
            emit(buildOp(outerOpId, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(adapter), AsyncStartSource.DEAL_BODY,
                    ParameterBoundaryMode.RUN, parameterBoundaryIds, target.returnType(),
                    null, null, null),
                outerToken, InternalResultType.INTERNAL_ASYNC, args, argTypes,
                FailurePolicyId.NO_DEAL_FAILURE, outerOrigin));
            for (SemanticOp boundary : parameterBoundaryOps) {
                emit(boundary);
            }
            return lowerAwait(outerToken, target.returnType(), awaitSpan, slot);
        }

        /** The single {@code AWAIT} with its {@code ASYNC_COMPLETION} boundary child. */
        private ValueId lowerAwait(AsyncTokenId token, RuntimeDescriptor completion,
                                   Span awaitSpan, ValueId slot) {
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId awaitAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId awaitOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin awaitOrigin = new SourceOrigin(sourceId, toSourceSpan(awaitSpan),
                SourceOriginKind.USER, awaitAnchor, currentParent());
            SemanticOp completionBoundary = buildChildBoundaryWithPolicy(
                BoundaryKind.ASYNC_COMPLETION, completion, FailurePolicyId.ASYNC_COMPLETION,
                result, awaitSpan, awaitOpId);
            emit(buildOp(awaitOpId, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(token, completion, completionBoundary.opId()),
                result, completion, List.of(), List.of(),
                FailurePolicyId.NO_DEAL_FAILURE, awaitOrigin));
            emit(completionBoundary);
            return result;
        }

        /**
         * {@code RETURN} — the carrier arm (C-D6/D13): the optional value
         * operand completes before START; the function's single
         * {@code FUNCTION_RETURN} boundary (emitted once, parented to
         * this RETURN op, checking the declared return descriptor under
         * the descriptor-kind rule) executes as the RETURN's child and
         * publishes the checked value as the enclosing call's return
         * value; the RETURN transfers and terminates its block.
         */
        private void lowerReturn(ReturnStatement statement) {
            FunctionContext context = functionStack.peek();
            if (context == null) {
                throw new ConstructUnlowered("return statement outside a function body");
            }
            ValueId value;
            if (statement.expr().isPresent()) {
                value = lowerExpression(statement.expr().get());
            } else {
                if (!(context.signature.returnType() instanceof RuntimeDescriptor.Null)) {
                    throw new ConstructUnlowered("bare return in a function whose return "
                        + "type is not null (the checker requires the value)");
                }
                value = emitValueOp(SemanticOpKind.CONST,
                    new KindPayload.ConstPayload(ScalarValue.Null.INSTANCE),
                    statement.span(),
                    ContainerPayloadDescriptors.resultDescriptorOf(Type.Null.INSTANCE),
                    FailurePolicyId.NO_DEAL_FAILURE);
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId returnOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(statement.span()),
                SourceOriginKind.USER, anchor, currentParent());
            ensureReturnBoundary(context, value, statement.span(), returnOpId);
            emit(buildOp(returnOpId, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(value, context.functionId,
                    context.invocationOpId(), context.returnBoundaryOpId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
            terminateBlock();
        }

        /**
         * Emits the function's single return boundary op exactly once
         * (parented to the given RETURN op; the declared return
         * descriptor under the descriptor-kind rule). The boundary kind
         * follows the function's single invocation shape (the closed
         * boundary-assignment table's per-shape cell):
         * {@code FUNCTION_RETURN} under a CALL/ASYNC_START body task,
         * {@code DEAL_TO_HOST} under a CALLBACK_INVOKE,
         * {@code EXTERNAL_RETURN} under a sync EXTERNAL_ENTRY, and
         * {@code FUNCTION_RETURN} under an async EXTERNAL_ENTRY (the
         * callee task's boundary).
         */
        private void ensureReturnBoundary(FunctionContext context, ValueId value, Span span,
                                          OpId returnOpId) {
            if (context.returnBoundaryEmitted) {
                return;
            }
            context.returnBoundaryEmitted = true;
            RuntimeDescriptor returnType = context.signature.returnType();
            FailurePolicyId policy = descriptorKindPolicy(returnType);
            BoundaryKind kind = returnBoundaryKind(context);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.SYNTHETIC, anchor, returnOpId);
            emit(buildOp(context.returnBoundaryOpId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(kind, returnType,
                    value, new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                null, null, policy, origin));
        }

        /** The function's single return boundary kind per its invocation shape. */
        private BoundaryKind returnBoundaryKind(FunctionContext context) {
            if (!e7Calls || context.shape == null
                    || context.shape == InvocationShape.SOURCE_CALL
                    || context.shape == InvocationShape.SOURCE_ASYNC) {
                return BoundaryKind.FUNCTION_RETURN;
            }
            return switch (context.shape) {
                case CALLBACK_SHAPE -> BoundaryKind.DEAL_TO_HOST;
                case EXTERNAL_ENTRY_SHAPE ->
                    context.signature.isAsync() ? BoundaryKind.FUNCTION_RETURN
                        : BoundaryKind.EXTERNAL_RETURN;
                default -> BoundaryKind.FUNCTION_RETURN;
            };
        }

        /**
         * The implicit trailing return of an unterminated null-returning
         * function body: one {@code CONST null} production, the single
         * {@code FUNCTION_RETURN} boundary, and the {@code RETURN}
         * transfer ("a function with return type null returns the null
         * value through the boundary").
         */
        private void lowerImplicitReturn(FunctionContext context, Span span) {
            ValueId value = emitValueOp(SemanticOpKind.CONST,
                new KindPayload.ConstPayload(ScalarValue.Null.INSTANCE), span,
                ContainerPayloadDescriptors.resultDescriptorOf(Type.Null.INSTANCE),
                FailurePolicyId.NO_DEAL_FAILURE);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId returnOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.SYNTHETIC, anchor, currentParent());
            ensureReturnBoundary(context, value, span, returnOpId);
            emit(buildOp(returnOpId, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(value, context.functionId,
                    context.invocationOpId(), context.returnBoundaryOpId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
            terminateBlock();
        }

        /**
         * The unified full-program statement walk (ISSUE-0410 carrier
         * slice): module-level lets/imports/functions plus every E5
         * statement and the RETURN arm — function bodies recurse through
         * this same walk, so chains, comparisons, control flow, calls,
         * and returns lower together in one session.
         */
        private void lowerFullStatements(List<StatementNode> statements,
                                         boolean moduleLevel) {
            // The unified walk's per-scope recursive-group partition
            // (ISSUE-0634): the group arms are active in the same session,
            // so every scope partitions its function declarations exactly
            // as the group walk does — a module-level group was emitted at
            // module-init top (lowerProjectModule) and its members are
            // skipped here; a nested-scope group emits at its first
            // member's declaration position.
            Map<FunctionDeclaration, List<FunctionDeclaration>> groupMembership =
                groupCore ? groupMembership(statements) : Map.of();
            for (StatementNode statement : statements) {
                ensureBlockOpen();
                if (statement instanceof VariableDeclaration decl) {
                    lowerBindingVarDecl(decl);
                    continue;
                }
                if (statement instanceof FunctionDeclaration function) {
                    if (skipGroupedFunctionDecl(function, groupMembership, moduleLevel)) {
                        continue;
                    }
                    lowerBindingFunctionDecl(function, moduleLevel);
                    continue;
                }
                if (statement instanceof ClassDeclaration classDeclaration) {
                    if (!classCore) {
                        throw new ConstructUnlowered(describeStatement(statement));
                    }
                    lowerClassDeclaration(classDeclaration, false);
                    continue;
                }
                if (statement instanceof ExportDeclaration exportDeclaration) {
                    if (!e7Calls) {
                        throw new ConstructUnlowered(describeStatement(statement));
                    }
                    // The E7 surface unwraps exported function
                    // declarations (the declaration walks like any
                    // function body); the entry/callback/publish records
                    // emit at the unit terminal from the checked export
                    // facts — no position op exists for the export
                    // wrapper itself. An exported class declaration walks
                    // through the class arm (class-core mode).
                    if (exportDeclaration.declaration()
                            instanceof FunctionDeclaration exportedFunction) {
                        if (skipGroupedFunctionDecl(exportedFunction,
                                groupMembership, moduleLevel)) {
                            continue;
                        }
                        lowerBindingFunctionDecl(exportedFunction, moduleLevel);
                    } else if (exportDeclaration.declaration()
                            instanceof ClassDeclaration exportedClass) {
                        if (!classCore) {
                            throw new ConstructUnlowered(
                                describeStatement(statement));
                        }
                        lowerClassDeclaration(exportedClass, true);
                    }
                    continue;
                }
                if (statement instanceof ImportDeclaration importDeclaration) {
                    // The alias ALLOC was hoisted to module-init top (B1);
                    // the carrier slice produces the pinned MODULE_IMPORT
                    // op (the load-once initialization record) for the
                    // resolved import target — the stdlib console module
                    // needs no further initialization for the tail. The
                    // payload names the import's ordered alias cells:
                    // the completion is the pinned initializing write of
                    // every named cell (an import alias never carries a
                    // BINDING_INIT).
                    ResolvedImport importFact = importByAlias(importDeclaration.alias());
                    if (importFact == null) {
                        throw new ConstructUnlowered("import '" + importDeclaration.alias()
                            + "' without a resolved import fact (a missing checker fact "
                            + "is a producer defect)");
                    }
                    BindingId aliasCell = importAliasCells.get(importDeclaration.alias());
                    if (aliasCell == null) {
                        throw new ConstructUnlowered("import '" + importDeclaration.alias()
                            + "' without a hoisted alias cell (a missing hoist fact "
                            + "is a producer defect)");
                    }
                    emitNullOp(SemanticOpKind.MODULE_IMPORT,
                        new KindPayload.ModuleImportPayload(importFact.modulePath(),
                            importFact.resolvedModuleId(), moduleImportKindOf(importFact),
                            List.of(aliasCell)),
                        importDeclaration.span(), FailurePolicyId.NO_DEAL_FAILURE,
                        SourceOriginKind.USER, currentParent());
                    continue;
                }
                if (statement instanceof ReturnStatement returnStatement) {
                    lowerReturn(returnStatement);
                    continue;
                }
                if (statement instanceof ForOfStatement forOf) {
                    lowerForOfStatement(forOf);
                    continue;
                }
                if (statement instanceof DeleteStatement delete) {
                    lowerDelete(delete);
                    continue;
                }
                if (statement instanceof Block block) {
                    statementWalk.walk(block.statements(), false);
                    continue;
                }
                if (statement instanceof IfStatement ifStatement) {
                    lowerIfStatement(ifStatement);
                    continue;
                }
                if (statement instanceof WhileStatement whileStatement) {
                    lowerWhileStatement(whileStatement);
                    continue;
                }
                if (statement instanceof ForStatement forStatement) {
                    if (forStatement.init().isPresent()
                            && forStatement.init().get() instanceof ForInit.VarDecl) {
                        lowerBindingForLet(forStatement);
                    } else {
                        lowerForStatement(forStatement);
                    }
                    continue;
                }
                if (statement instanceof TryStatement tryStatement) {
                    lowerTryCatch(tryStatement);
                    continue;
                }
                if (statement instanceof ThrowStatement throwStatement) {
                    lowerThrow(throwStatement);
                    continue;
                }
                if (statement instanceof BreakStatement breakStatement) {
                    lowerBreak(breakStatement);
                    continue;
                }
                if (statement instanceof ContinueStatement continueStatement) {
                    lowerContinue(continueStatement);
                    continue;
                }
                if (statement instanceof ExpressionStatement expressionStatement) {
                    lowerDiscard(expressionStatement);
                    continue;
                }
                throw new ConstructUnlowered(describeStatement(statement));
            }
        }

        /**
         * Installs the E7 call-machine facts and activates the E7
         * surface: the module's checked exports, the callee-module route
         * facts, the callee modules' recorded {@code EXTERNAL_ENTRY} op
         * ids, and the exported callback function names.
         */
        void setE7Facts(List<ExportInterface> exports, Map<ModuleId, ModuleRoute> routes,
                        Map<ModuleId, Map<String, OpId>> calleeEntries,
                        Set<String> callbacks) {
            if (!fullProgram) {
                throw new IllegalStateException("the E7 surface requires the "
                    + "full-program session (producer defect)");
            }
            this.e7Calls = true;
            this.moduleExports = List.copyOf(exports);
            this.calleeRoutes = Map.copyOf(routes);
            this.calleeExternalEntries = Map.copyOf(calleeEntries);
            this.callbackExports = Set.copyOf(callbacks);
        }

        /** The module's recorded {@code EXTERNAL_ENTRY} op ids by export name. */
        Map<String, OpId> recordedEntries() {
            return Map.copyOf(recordedEntries);
        }

        /** The module's recorded {@code CALLBACK_INVOKE} op ids by export name. */
        Map<String, OpId> recordedCallbacks() {
            return Map.copyOf(recordedCallbacks);
        }

        /** True iff the module's checked export facts name the given export. */
        private boolean isExported(String name) {
            for (ExportInterface export : moduleExports) {
                if (export.name().equals(name)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * The E7 unit terminal: one {@code EXTERNAL_ENTRY} or
         * {@code CALLBACK_INVOKE} op per exported function (from the
         * checked export facts) plus the {@code ENTRY_INVOKE}
         * delegation of {@code main}: null. Non-exported declared
         * functions must be called from source (their RETURN ops name an
         * existing invocation).
         */
        private void emitE7Terminals() {
            for (Map.Entry<String, FunctionContext> entry
                    : moduleFunctionContexts.entrySet()) {
                String name = entry.getKey();
                FunctionContext context = entry.getValue();
                if (!isExported(name)) {
                    continue;
                }
                emitExportPublish(name, context);
                if ("main".equals(name)) {
                    // The ENTRY_INVOKE delegation owns main's single
                    // invocation shape; no EXTERNAL_ENTRY/CALLBACK_INVOKE
                    // record for the entry function.
                    continue;
                }
                if (callbackExports.contains(name)) {
                    emitCallbackInvoke(name, context);
                } else {
                    emitExternalEntry(name, context);
                }
            }
            emitEntryInvokeDelegation();
        }

        /**
         * The invocation-identity finalization of the unified walk
         * (ISSUE-0634; design sources
         * {@code project-lowering-entry-and-registration-seeds} D2/D9 and
         * {@code semantic-ir-construct-coverage-cutover} K12's lowering
         * side). It is the decision point after the walk and the E7
         * terminals, where the set of a body's statically materialized
         * invocations is final:
         *
         * <ul>
         *   <li>every lowered body's reserved invocation identity is
         *       materialized by at least one emitted op of the unit — an
         *       exported function's hoisted shape op, an
         *       entry/callback op, or the first source call site that took
         *       over the reserved call-site identity (the landed
         *       discipline);</li>
         *   <li>the identity is materialized exactly once: two emitted ops
         *       carrying one body's identity is a producer defect (a body's
         *       identity names exactly one invocation op);</li>
         *   <li>a recursive-group member's reserved identity is materialized
         *       by its group's single {@code RECURSIVE_GROUP_INIT}
         *       publication (the group arm's member bodies carry no
         *       {@code RETURN} — the group walk's member-body shape is the
         *       value-reference body).</li>
         * </ul>
         *
         * <p>A body with neither a statically materialized invocation nor a
         * group publication is a producer defect of this walk: the body's
         * {@code RETURN} names the reserved identity, and an identity that
         * resolves to no op would leave the produced unit rejected by the
         * closed gate. It is reported here as {@code CONSTRUCT_UNLOWERED} so
         * the failure names the body, never a dangling identity. The
         * creation-op takeover of a body with no static invocation (the
         * body-invocation identity child's D9/K12 arm) replaces this arm
         * when it lands; no second walk and no synthetic op exist.</p>
         */
        private void finalizeInvocationIdentities() {
            Map<OpId, Integer> occurrences = new LinkedHashMap<>();
            for (SemanticOp op : ops) {
                occurrences.merge(op.opId(), 1, Integer::sum);
            }
            for (Map.Entry<String, FunctionContext> entry
                    : moduleFunctionContexts.entrySet()) {
                String name = entry.getKey();
                FunctionContext context = entry.getValue();
                OpId identity = context.invocationOpId();
                int count = occurrences.getOrDefault(identity, 0);
                if (count == 1) {
                    continue;
                }
                // A recursive-group member's pre-assigned allocation identity
                // is published by its group's single RECURSIVE_GROUP_INIT op
                // (the group arm's member bodies carry no RETURN: the group
                // walk's member-body shape is the value-reference body, so
                // the member's reserved identity is referenced by no op and
                // its materialization is the group publication). The group
                // arm issues exactly one op per SCC, so the member's identity
                // is materialized exactly once; the creation-op takeover for
                // a member body that carries a RETURN is the body-invocation
                // identity child's extension of this step.
                if (groupsNaming(context.functionId) == 1) {
                    continue;
                }
                throw new ConstructUnlowered("declared function '" + name
                    + "' is never called (every non-exported declared function's"
                    + " single return boundary names an existing invocation: the"
                    + " reserved invocation identity " + identity + " is"
                    + " materialized by " + count + " emitted op(s))");
            }
        }

        /**
         * The number of emitted {@code RECURSIVE_GROUP_INIT} ops naming the
         * given function as a member (exactly one for a group member, zero
         * for every other body).
         */
        private int groupsNaming(FunctionId functionId) {
            int count = 0;
            for (SemanticOp op : ops) {
                if (op.kind() == SemanticOpKind.RECURSIVE_GROUP_INIT
                        && op.payload()
                            instanceof KindPayload.RecursiveGroupInitPayload group
                        && group.functions().contains(functionId)) {
                    count++;
                }
            }
            return count;
        }

        /**
         * {@code EXPORT_PUBLISH} — the atomic publication record of one
         * exported function: the checked {@code MODULE_EXPORT} boundary
         * (descriptor-kind rule) precedes the publication of the
         * function value.
         */
        private void emitExportPublish(String name, FunctionContext context) {
            ValueId functionValue = moduleFunctionIdentities.get(name);
            if (functionValue == null) {
                throw new IllegalStateException("the exported function identity of '"
                    + name + "' was not recorded at hoist (producer defect)");
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId publishOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin publishOrigin = new SourceOrigin(sourceId, toSourceSpan(programSpan),
                SourceOriginKind.SYNTHETIC, anchor, null);
            emit(buildOp(publishOpId, SemanticOpKind.EXPORT_PUBLISH,
                new KindPayload.ExportPublishPayload(module, name, context.signature,
                    functionValue),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, publishOrigin));
            emit(buildChildBoundary(BoundaryKind.MODULE_EXPORT,
                context.signature, functionValue, programSpan, publishOpId));
        }

        /**
         * {@code EXTERNAL_ENTRY} — the callee-unit invocation record of a
         * function callable across a shared/shadow edge: one static op
         * per exported function. Sync: the body's {@code RETURN} runs the
         * single {@code EXTERNAL_RETURN} boundary; async: the entry
         * creates the canonical token and the body task, whose
         * {@code RETURN} runs the single {@code FUNCTION_RETURN}
         * boundary. The entry runs no parameter boundaries (the caller's
         * {@code EXTERNAL_PARAMETER} boundaries run exactly once).
         */
        private void emitExternalEntry(String name, FunctionContext context) {
            OpId entryOpId = context.shapeOpId;
            RuntimeDescriptor completion = context.signature.isAsync()
                ? context.signature.returnType() : null;
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(programSpan),
                SourceOriginKind.SYNTHETIC, anchor, null);
            emitUnattached(buildOp(entryOpId, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload(name, context.functionId,
                    context.signature, context.signature.isAsync(),
                    context.returnBoundaryOpId, completion),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
            recordedEntries.put(name, entryOpId);
        }

        /**
         * {@code CALLBACK_INVOKE} — the host-driven top-level invocation
         * record of a statically resolved callback export: the export's
         * function identity, its descriptor, the {@code HOST_TO_DEAL}
         * parameter boundaries (descriptor-kind rule, one per declared
         * parameter in one-based order), and the single
         * {@code DEAL_TO_HOST} return boundary (run by the executed
         * body's {@code RETURN}).
         */
        private void emitCallbackInvoke(String name, FunctionContext context) {
            if (context.signature.isAsync()) {
                throw new ConstructUnlowered("callback export '" + name
                    + "' is async (a CALLBACK_INVOKE is sync only — the scenario "
                    + "schema pins FIXTURE_INVALID for async callbacks)");
            }
            OpId callbackOpId = context.shapeOpId;
            ValueId functionValue = moduleFunctionIdentities.get(name);
            if (functionValue == null) {
                throw new IllegalStateException("the exported function identity of '"
                    + name + "' was not recorded at hoist (producer defect)");
            }
            List<SemanticOp> parameterBoundaryOps = new ArrayList<>();
            List<OpId> parameterBoundaryIds = new ArrayList<>();
            for (int i = 0; i < context.signature.paramTypes().size(); i++) {
                // The callback argument slot: the scenario host fills the
                // slot with the host-supplied argument before the
                // boundary executes.
                ValueId argSlot = ids.nextValueId(module, nextOrdinal++, 0);
                SemanticOp boundary = buildChildBoundary(BoundaryKind.HOST_TO_DEAL,
                    context.signature.paramTypes().get(i), argSlot, programSpan,
                    callbackOpId);
                parameterBoundaryOps.add(boundary);
                parameterBoundaryIds.add(boundary.opId());
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(programSpan),
                SourceOriginKind.SYNTHETIC, anchor, null);
            emitUnattached(buildOp(callbackOpId, SemanticOpKind.CALLBACK_INVOKE,
                new KindPayload.CallbackInvokePayload(functionValue, context.signature,
                    parameterBoundaryIds, context.returnBoundaryOpId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
            for (SemanticOp boundary : parameterBoundaryOps) {
                emit(boundary);
            }
            recordedCallbacks.put(name, callbackOpId);
        }

        /**
         * {@code ENTRY_INVOKE} — the E7 entry delegation: exactly one
         * {@code CALL(DIRECT main)} (parented to the entry op, executed
         * once by the entry arm) and the entry terminal exits the
         * program; no separate boundary.
         */
        private void emitEntryInvokeDelegation() {
            FunctionContext main = moduleFunctionContexts.get("main");
            if (main == null) {
                return;
            }
            if (!main.signature.paramTypes().isEmpty()
                    || !(main.signature.returnType() instanceof RuntimeDescriptor.Null)
                    || main.signature.isAsync()) {
                throw new ConstructUnlowered("entry main must have the pinned non-async "
                    + "signature '(): null' (the orchestrator's E2011 pins this)");
            }
            if (main.callSiteUsed) {
                throw new ConstructUnlowered("entry main is called from source and "
                    + "delegated from the entry (the ENTRY_INVOKE delegation is main's "
                    + "call site)");
            }
            main.callSiteUsed = true;
            main.assignShape(InvocationShape.SOURCE_CALL, main.callSiteOpId);
            AnchorId entryAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId entryOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin entryOrigin = new SourceOrigin(sourceId, toSourceSpan(programSpan),
                SourceOriginKind.SYNTHETIC, entryAnchor, null);
            ValueId result = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId callAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin callOrigin = new SourceOrigin(sourceId, toSourceSpan(programSpan),
                SourceOriginKind.SYNTHETIC, callAnchor, entryOpId);
            emit(buildOp(entryOpId, SemanticOpKind.ENTRY_INVOKE,
                new KindPayload.EntryInvokePayload(module, main.functionId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, entryOrigin));
            emit(buildOp(main.callSiteOpId, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(main.functionId,
                            main.bodyBlock)),
                    main.signature, List.of(), main.returnBoundaryOpId, null,
                    main.bodyBlock, null),
                result, ContainerPayloadDescriptors.resultDescriptorOf(Type.Null.INSTANCE),
                List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, callOrigin));
        }

        /**
         * The entry delegation of the carrier slice: when the module
         * declares {@code main} with the pinned non-async signature
         * {@code (): null}, the module-init block's trailing ops are one
         * {@code CALL(DIRECT main)} (the entry call, using main's
         * reserved call-site identity) and one {@code DISCARD} of its
         * result — the decomposition-tail realization of
         * {@code ENTRY_INVOKE → CALL(DIRECT) to main(): null} (the
         * ENTRY_INVOKE op itself is the modules epic's production).
         */
        private void emitEntryMainCall() {
            FunctionContext main = moduleFunctionContexts.get("main");
            if (main == null) {
                return;
            }
            if (!main.signature.paramTypes().isEmpty()
                    || !(main.signature.returnType() instanceof RuntimeDescriptor.Null)
                    || main.signature.isAsync()) {
                throw new ConstructUnlowered("entry main must have the pinned non-async "
                    + "signature '(): null' (the orchestrator's E2011 pins this)");
            }
            if (main.callSiteUsed) {
                throw new ConstructUnlowered("entry main is called from source and "
                    + "delegated from module init (the carrier slice admits exactly one "
                    + "CALL site per callee — the entry delegation is main's call site)");
            }
            main.callSiteUsed = true;
            for (Map.Entry<String, FunctionContext> entry
                    : moduleFunctionContexts.entrySet()) {
                if (!entry.getValue().callSiteUsed) {
                    throw new ConstructUnlowered("declared function '" + entry.getKey()
                        + "' is never called (the decomposition-tail carrier slice "
                        + "admits exactly the called functions of a seed program — "
                        + "every declared function's single return boundary names an "
                        + "existing CALL; uncalled declarations are outside the "
                        + "slice)");
                }
            }
            ValueId result = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(programSpan),
                SourceOriginKind.SYNTHETIC, anchor, currentParent());
            emit(buildOp(main.callSiteOpId, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        main.functionId, main.bodyBlock)),
                    main.signature, List.of(), main.returnBoundaryOpId,
                    null, main.bodyBlock, null),
                result, ContainerPayloadDescriptors.resultDescriptorOf(
                    Type.Null.INSTANCE), List.of(), List.of(),
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            emitNullOp(SemanticOpKind.DISCARD, new KindPayload.DiscardPayload(result),
                programSpan, FailurePolicyId.NO_DEAL_FAILURE, SourceOriginKind.SYNTHETIC,
                null);
        }

        // ---------------------------------------------------------------------
        // Statement arms (the E5 positionable window)
        // ---------------------------------------------------------------------

        private void lowerStatements(List<StatementNode> statements) {
            for (StatementNode statement : statements) {
                ensureBlockOpen();
                if (statement instanceof ForOfStatement forOf) {
                    lowerForOfStatement(forOf);
                    continue;
                }
                if (statement instanceof DeleteStatement delete) {
                    lowerDelete(delete);
                    continue;
                }
                if (statement instanceof Block block) {
                    statementWalk.walk(block.statements(), false);
                    continue;
                }
                if (statement instanceof IfStatement ifStatement) {
                    lowerIfStatement(ifStatement);
                    continue;
                }
                if (statement instanceof WhileStatement whileStatement) {
                    lowerWhileStatement(whileStatement);
                    continue;
                }
                if (statement instanceof ForStatement forStatement) {
                    lowerForStatement(forStatement);
                    continue;
                }
                if (statement instanceof TryStatement tryStatement) {
                    lowerTryCatch(tryStatement);
                    continue;
                }
                if (statement instanceof ThrowStatement throwStatement) {
                    lowerThrow(throwStatement);
                    continue;
                }
                if (statement instanceof BreakStatement breakStatement) {
                    lowerBreak(breakStatement);
                    continue;
                }
                if (statement instanceof ContinueStatement continueStatement) {
                    lowerContinue(continueStatement);
                    continue;
                }
                if (statement instanceof ExpressionStatement expressionStatement) {
                    lowerDiscard(expressionStatement);
                    continue;
                }
                throw new ConstructUnlowered(describeStatement(statement));
            }
        }

        // ---------------------------------------------------------------------
        // The E5 control-flow arms (control-flow-structures C-D3..C-D8)
        // ---------------------------------------------------------------------

        /**
         * {@code BRANCH(IF)} — the if-statement arm (C-D3): the
         * condition's producing ops complete in the enclosing block
         * before the {@code BRANCH} op; exactly one of
         * {@code selectedBlock}/{@code alternateBlock} executes; the
         * {@code else} branch lowers inside {@code alternateBlock} (an
         * {@code else if} chain nests its {@code BRANCH} op there); an
         * absent {@code else} produces {@code alternateBlock = null};
         * SUCCESS publishes no result. Block ops record the
         * {@code BRANCH} as {@code parentOpId}.
         */
        private void lowerIfStatement(IfStatement statement) {
            ValueId condition = lowerExpression(statement.condition());
            BlockId selectedBlock = allocateBlock();
            boolean hasElse = statement.elseBranch().isPresent();
            BlockId alternateBlock = hasElse ? allocateBlock() : null;
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(statement.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.BRANCH,
                new KindPayload.BranchPayload(ControlSelector.IF, condition, selectedBlock,
                    alternateBlock),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
            pushBlockParent(opId);
            pushBlock(selectedBlock);
            try {
                statementWalk.walk(statement.thenBlock().statements(), false);
            } finally {
                popBlock();
            }
            if (hasElse) {
                pushBlock(alternateBlock);
                try {
                    switch (statement.elseBranch().get()) {
                        case Either.Left<IfStatement, Block> left ->
                            lowerIfStatement(left.value());
                        case Either.Right<IfStatement, Block> right ->
                            statementWalk.walk(right.value().statements(), false);
                    }
                } finally {
                    popBlock();
                }
            }
            popBlockParent();
        }

        /**
         * {@code LOOP(WHILE)} — the while-statement arm (C-D4): the
         * per-iteration condition block is {@code initBlock} (the
         * condition's producing ops are explicit members of
         * {@code initBlock}, never an inferred subgraph);
         * {@code updateBlock = null}; execution repeats { execute
         * {@code initBlock}; evaluate the condition value; if false →
         * SUCCESS; execute {@code bodyBlock} }. The {@code LOOP} op
         * precedes its child block ops in the unit list (payload order:
         * init, body). No speculative body execution; conditions
         * re-evaluate per iteration. Block ops record the {@code LOOP}
         * as {@code parentOpId}.
         */
        private void lowerWhileStatement(WhileStatement statement) {
            BlockId initBlock = allocateBlock();
            BlockId bodyBlock = allocateBlock();
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            int mark = emitTarget().size();
            pushBlockParent(opId);
            pushBlock(initBlock);
            ValueId condition;
            try {
                condition = lowerExpression(statement.condition());
            } finally {
                popBlock();
            }
            pushBlock(bodyBlock);
            pushLoopTarget(opId);
            try {
                statementWalk.walk(statement.body().statements(), false);
            } finally {
                popLoopTarget();
                popBlock();
            }
            popBlockParent();
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(statement.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emitAt(mark, buildOp(opId, SemanticOpKind.LOOP,
                new KindPayload.LoopPayload(ControlSelector.WHILE, initBlock, condition,
                    bodyBlock, null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * {@code LOOP(FOR)} — the for-statement arm (C-D4): the
         * one-time {@code initBlock} carries the init ops (an
         * assignment-expression initializer lowers through the address
         * chain; a {@code let}-declared initializer is E6's
         * {@code BINDING_ALLOC} and fails closed) and the first
         * condition production; {@code updateBlock} carries the update
         * ops then the condition-producing ops (the condition
         * {@code ValueId} is produced once in {@code initBlock} and
         * re-produced by the {@code updateBlock} production — one value
         * identity, the most recently produced value wins at
         * execution). Execution: {@code initBlock} once; repeat {
         * condition; body; updateBlock }. A test-less {@code for (;;)}
         * produces exactly one {@code CONST} op with the boolean value
         * {@code true} in {@code initBlock} as the condition production
         * ({@code SYNTHETIC}, the for-statement span) and
         * {@code updateBlock} carries only the update ops — a constant
         * needs no per-iteration re-production. The {@code LOOP} op
         * precedes its child block ops in the unit list (payload order:
         * init, body, update). Block ops record the {@code LOOP} as
         * {@code parentOpId}.
         */
        private void lowerForStatement(ForStatement statement) {
            BlockId initBlock = allocateBlock();
            BlockId bodyBlock = allocateBlock();
            BlockId updateBlock = allocateBlock();
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            ValueId condition = statement.condition().isPresent()
                ? ids.nextValueId(module, nextOrdinal++, 0) : null;
            int mark = emitTarget().size();
            pushBlockParent(opId);
            pushBlock(initBlock);
            try {
                statement.init().ifPresent(init -> {
                    switch (init) {
                        case ForInit.AssignExpr assign -> {
                            lowerExpression(assign.expr());
                        }
                        case ForInit.VarDecl decl -> throw new ConstructUnlowered(
                            "for-loop let-declared initializer (BINDING_ALLOC is E6's, "
                                + "ISSUE-0235)");
                    }
                });
                if (statement.condition().isPresent()) {
                    lowerExpression(statement.condition().get(), condition);
                } else {
                    // The test-less FOR row: exactly one CONST true in
                    // initBlock as the condition production.
                    condition = emitValueOpWith(SemanticOpKind.CONST,
                        new KindPayload.ConstPayload(new ScalarValue.Boolean(true)),
                        statement.span(),
                        ContainerPayloadDescriptors.resultDescriptorOf(
                            Type.Boolean.INSTANCE),
                        FailurePolicyId.NO_DEAL_FAILURE, null, SourceOriginKind.SYNTHETIC);
                }
            } finally {
                popBlock();
            }
            pushBlock(bodyBlock);
            pushLoopTarget(opId);
            try {
                statementWalk.walk(statement.body().statements(), false);
            } finally {
                popLoopTarget();
                popBlock();
            }
            pushBlock(updateBlock);
            try {
                statement.update().ifPresent(update -> lowerExpression(update));
                if (statement.condition().isPresent()) {
                    // The per-iteration condition re-production: the same
                    // condition ValueId, re-produced by the updateBlock
                    // production (most recently produced value wins).
                    lowerExpression(statement.condition().get(), condition);
                }
            } finally {
                popBlock();
            }
            popBlockParent();
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(statement.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emitAt(mark, buildOp(opId, SemanticOpKind.LOOP,
                new KindPayload.LoopPayload(ControlSelector.FOR, initBlock, condition,
                    bodyBlock, updateBlock),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * {@code TRY_CATCH} — the try/catch arm (C-D6): execute
         * {@code tryBlock}; success → SUCCESS (catch skipped, no
         * result); a DEAL failure (an E8 error) raised inside
         * {@code tryBlock} is reified as an {@code Error} value
         * ({@code {code, message}}) bound to {@code catchBinding}
         * (binding init mechanics E6 — this stage allocates the binding
         * identity) and {@code catchBlock} executes; a failure raised
         * from {@code catchBlock} becomes the {@code TRY_CATCH} FAILURE
         * with its own code/message/origin preserved and
         * {@code cause} = the original caught failure snapshot. Only
         * DEAL failures are catchable. A load of the catch variable
         * inside {@code catchBlock} lowers to {@code BINDING_LOAD}
         * carrying the catch binding with the pinned initial
         * generation. The {@code TRY_CATCH} op precedes its child block
         * ops in the unit list (payload order: try, catch). Block ops
         * record the {@code TRY_CATCH} as {@code parentOpId}.
         */
        private void lowerTryCatch(TryStatement statement) {
            BlockId tryBlock = allocateBlock();
            BlockId catchBlock = allocateBlock();
            BindingId catchBinding = ids.nextBindingId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            int mark = emitTarget().size();
            pushBlockParent(opId);
            pushBlock(tryBlock);
            try {
                statementWalk.walk(statement.tryBlock().statements(), false);
            } finally {
                popBlock();
            }
            catchFrames.add(0, new CatchFrame(statement.catchVar(), catchBinding));
            pushBlock(catchBlock);
            try {
                statementWalk.walk(statement.catchBlock().statements(), false);
            } finally {
                popBlock();
                catchFrames.remove(0);
            }
            popBlockParent();
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(statement.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emitAt(mark, buildOp(opId, SemanticOpKind.TRY_CATCH,
                new KindPayload.TryCatchPayload(tryBlock, catchBinding, catchBlock),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, origin));
        }

        /**
         * {@code THROW} — the throw arm (C-D6): the operand completes
         * before START; the op never succeeds; policy
         * {@code THROW_TRANSFER} — code/message from the supplied
         * {@code Error} value's fields, origin = the THROW origin,
         * frames active; control transfers to the nearest enclosing
         * {@code TRY_CATCH}, else the error escapes as the host-visible
         * {@code DEALRuntimeError}. {@code THROW} terminates its block
         * (C-D2 dominance).
         */
        private void lowerThrow(ThrowStatement statement) {
            ValueId errorValue = lowerExpression(statement.expr());
            emitNullOp(SemanticOpKind.THROW,
                new KindPayload.ThrowPayload(errorValue), statement.span(),
                FailurePolicyId.THROW_TRANSFER, SourceOriginKind.USER, currentParent());
            terminateBlock();
        }

        /**
         * {@code BREAK} — the break arm (C-D7): payload {@code loopId} =
         * the innermost enclosing loop op ({@code LOOP} or
         * {@code FOR_EACH}) recorded by the lowerer; BREAK exits the
         * target loop; effects completed before the transfer remain.
         * The checker's E2000 pins source-level loop placement, so a
         * missing target is a producer defect ({@code
         * CONSTRUCT_UNLOWERED}), never an invented target and never a
         * silent fallthrough. {@code BREAK} terminates its block.
         */
        private void lowerBreak(BreakStatement statement) {
            OpId target = loopTargets.peek();
            if (target == null) {
                throw new ConstructUnlowered("break without an enclosing loop target (the "
                    + "checker's E2000 pins source-level loop placement — a missing "
                    + "checker fact is a producer defect)");
            }
            emitNullOp(SemanticOpKind.BREAK,
                new KindPayload.BreakPayload(target), statement.span(),
                FailurePolicyId.NO_DEAL_FAILURE, SourceOriginKind.USER, currentParent());
            terminateBlock();
        }

        /**
         * {@code CONTINUE} — the continue arm (C-D7): payload
         * {@code loopId} = the innermost enclosing loop op; CONTINUE
         * proceeds to the target loop's next iteration — FOR: execute
         * {@code updateBlock} then re-test; WHILE: execute the condition
         * block ({@code initBlock}) then re-test; FOR_EACH: next slot
         * index. Transfer across an enclosing {@code TRY_CATCH} boundary
         * is legal. A missing target is a producer defect (see
         * {@link #lowerBreak}). {@code CONTINUE} terminates its block.
         */
        private void lowerContinue(ContinueStatement statement) {
            OpId target = loopTargets.peek();
            if (target == null) {
                throw new ConstructUnlowered("continue without an enclosing loop target (the "
                    + "checker's E2000 pins source-level loop placement — a missing "
                    + "checker fact is a producer defect)");
            }
            emitNullOp(SemanticOpKind.CONTINUE,
                new KindPayload.ContinuePayload(target), statement.span(),
                FailurePolicyId.NO_DEAL_FAILURE, SourceOriginKind.USER, currentParent());
            terminateBlock();
        }

        /**
         * {@code DISCARD} — the expression-statement arm (C-D8): the
         * value's producing ops already completed before the op; START →
         * SUCCESS with no result; origin kind {@code SYNTHETIC} — the
         * intentional discard is audited in the op stream and traces,
         * never inferred away.
         */
        private void lowerDiscard(ExpressionStatement statement) {
            ValueId value = lowerExpression(statement.expr());
            emitNullOp(SemanticOpKind.DISCARD,
                new KindPayload.DiscardPayload(value), statement.span(),
                FailurePolicyId.NO_DEAL_FAILURE, SourceOriginKind.SYNTHETIC,
                currentParent());
        }

        // ---------------------------------------------------------------------
        // The per-construct arms (D1)
        // ---------------------------------------------------------------------

        /**
         * {@code CONST} — the scalar-literal and template-fragment arm.
         * An {@code IntLiteral} outside signed32 [-2147483648,
         * 2147483647] raises {@link IntLiteralOutOfRange} (D1's CONST
         * contract — a literal outside the closed scalar set is a
         * producer defect, never an invented op): the checked frontend
         * still admits out-of-int32 literals until the E1036 signed32
         * literal gate (ISSUE-0111) lands, so this arm fails closed
         * instead of truncating — no {@code CONST} is produced for the
         * out-of-range value, and the in-range cast is exact.
         */
        private ValueId lowerConst(LiteralExpr literal) {
            return lowerConst(literal, null);
        }

        private ValueId lowerConst(LiteralExpr literal, ValueId slot) {
            Type type = checkedType(literal);
            ScalarValue scalar = switch (literal.value()) {
                case LiteralValue.NullLiteral ignored -> ScalarValue.Null.INSTANCE;
                case LiteralValue.BooleanLiteral bool -> new ScalarValue.Boolean(bool.value());
                case LiteralValue.IntLiteral integer -> {
                    long value = integer.value();
                    if (value < -2147483648L || value > 2147483647L) {
                        throw new IntLiteralOutOfRange(value);
                    }
                    yield new ScalarValue.Int((int) value);
                }
                case LiteralValue.NumberLiteral number ->
                    new ScalarValue.Number(number.value());
                case LiteralValue.StringLiteral string ->
                    new ScalarValue.String(string.value());
            };
            return emitValueOp(SemanticOpKind.CONST, new KindPayload.ConstPayload(scalar),
                literal.span(), ContainerPayloadDescriptors.resultDescriptorOf(type),
                FailurePolicyId.NO_DEAL_FAILURE, slot);
        }

        /**
         * {@code BINDING_LOAD} — the identifier arm with the loop-binding
         * load-resolution rule: the load carries the innermost matching
         * enclosing {@code FOR_EACH} payload's initial generation; any
         * other identifier is a foreign construct (E6005).
         *
         * <p><b>Closure-core mode (ISSUE-0445).</b> The load resolves
         * the declared binding of the walk's environment through the
         * frame walk (the function's own scope chain first — B9 R2), and
         * a reference resolving outside the innermost open detached-body
         * walk registers the capture (B3: the capture set is the body's
         * free bindings in first-reference order). A load of a
         * function-typed binding publishes the incarnation's statically
         * tracked function identity (loads preserve allocation identity);
         * a function-typed load whose identity is not statically known
         * (parameters, catch bindings, iteration bindings — dynamic
         * function values) fails closed as the registry child's
         * resolution (B5).</p>
         */
        private ValueId lowerBindingLoad(IdentifierExpr identifier) {
            return lowerBindingLoad(identifier, null);
        }

        private ValueId lowerBindingLoad(IdentifierExpr identifier, ValueId slot) {
            Type type = checkedType(identifier);
            for (ForEachFrame frame : frames) {
                if (frame.name().equals(identifier.name())) {
                    return emitValueOp(SemanticOpKind.BINDING_LOAD,
                        new KindPayload.BindingLoadPayload(frame.binding(), frame.generation()),
                        identifier.span(), ContainerPayloadDescriptors.resultDescriptorOf(type),
                        FailurePolicyId.NO_DEAL_FAILURE, slot);
                }
            }
            for (CatchFrame frame : catchFrames) {
                if (frame.name().equals(identifier.name())) {
                    return emitValueOp(SemanticOpKind.BINDING_LOAD,
                        new KindPayload.BindingLoadPayload(frame.binding(),
                            INITIAL_LOOP_GENERATION),
                        identifier.span(), ContainerPayloadDescriptors.resultDescriptorOf(type),
                        FailurePolicyId.NO_DEAL_FAILURE, slot);
                }
            }
            if (!defaultContexts.isEmpty()) {
                // The default-block admission rule (K-D3, ISSUE-0511):
                // every reference of the open default walk — a direct
                // identifier reference or a capture resolved by a nested
                // detached walk (a closure body inside the default) —
                // admits only block-internal allocations (blocks allocated
                // inside the walk) and module-level bindings resolved
                // through the module-init block; an enclosing-region
                // (function-local) free reference is invalid — the closed
                // ClassDefaultPayload records no captures — and fails
                // E6005 CLASS_DEFAULT_CAPTURE, never a silent capture. A
                // nested closure's capture collector is no bypass: its
                // captures resolve against the same closed admission set.
                DefaultContext context = defaultContexts.peek();
                FrameResolution resolution = resolveFrame(identifier.name());
                if (resolution == null) {
                    throw new ConstructUnlowered("identifier '" + identifier.name()
                        + "' is not a declared binding of the class walk's "
                        + "environment (class/module members are E9's/E10's)");
                }
                BlockId producing = resolution.entry().incarnation().scope();
                if (!producing.equals(moduleInitBlock)
                        && !producing.equals(context.block())
                        && !context.internalBlocks().contains(producing)) {
                    throw new ClassDefaultCapture(identifier.name());
                }
                if (captureCollectors.size() <= context.entryCaptureDepth()) {
                    // A direct reference of the walk: the load publishes
                    // the threaded slot when one is threaded (the
                    // slot-threaded production — the CLASS_DEFAULT op's
                    // result identity, K-D3); a function-typed load
                    // publishes the incarnation's statically tracked
                    // function identity instead (loads preserve
                    // allocation identity).
                    return emitResolvedLoad(identifier, type, resolution.entry(), slot);
                }
                // A nested detached walk's reference (a closure body
                // inside the default): the closure walk's own capture
                // business (B3) under the admission set checked above;
                // no slot is threaded below the default expression's
                // top level.
                maybeRegisterCapture(identifier.name(), resolution);
                return emitResolvedLoad(identifier, type, resolution.entry(), null);
            }
            if (closureCore) {
                FrameResolution resolution = resolveFrame(identifier.name());
                if (resolution == null) {
                    throw new ConstructUnlowered("identifier '" + identifier.name()
                        + "' is not a declared binding of the closure walk's environment "
                        + "(class/module members are E9's/E10's)");
                }
                maybeRegisterCapture(identifier.name(), resolution);
                return emitResolvedLoad(identifier, type, resolution.entry());
            }
            // The binding-environment hook (ISSUE-0444 binding-core child):
            // every declared binding of the walk's environment resolves to
            // its dominant incarnation at the site, so the emitted load
            // names {binding, generation} of that incarnation (B9 R1).
            if (bindingSiteResolver != null) {
                BindingSite site = bindingSiteResolver.resolve(identifier.name());
                if (site != null) {
                    return emitValueOp(SemanticOpKind.BINDING_LOAD,
                        new KindPayload.BindingLoadPayload(site.binding(), site.generation()),
                        identifier.span(), ContainerPayloadDescriptors.resultDescriptorOf(type),
                        FailurePolicyId.NO_DEAL_FAILURE);
                }
            }
            throw new ConstructUnlowered("identifier '" + identifier.name()
                + "' is not a load of an enclosing for-of loop binding or catch "
                + "binding in this stage's window (binding allocation, non-loop "
                + "loads, and generation increments/stores are E6's, ISSUE-0235)");
        }

        /**
         * Emits one resolved {@code BINDING_LOAD} (closure-core mode):
         * the payload names the dominant incarnation's
         * {@code {binding, generation}}; the result publishes the
         * incarnation's statically tracked function identity for
         * function-typed loads (identity preservation — a threaded slot
         * never replaces the tracked identity, because the identity is
         * the {@code ValueId} whose {@code FunctionExecutionBinding}
         * resolves the load under R-FUNCTION-BINDING) or a fresh
         * {@code ValueId} otherwise. A non-function load with a threaded
         * slot ({@code slot} non-null) publishes the slot instead of
         * allocating one — the slot-threaded production of the default
         * walk's direct identifier reference (the {@code CLASS_DEFAULT}
         * op's result identity, K-D3).
         */
        private ValueId emitResolvedLoad(IdentifierExpr identifier, Type type,
                                         FrameEntry entry) {
            return emitResolvedLoad(identifier, type, entry, null);
        }

        private ValueId emitResolvedLoad(IdentifierExpr identifier, Type type,
                                         FrameEntry entry, ValueId slot) {
            RuntimeDescriptor descriptor = ContainerPayloadDescriptors.resultDescriptorOf(type);
            ValueId result = null;
            if (descriptor instanceof RuntimeDescriptor.Func) {
                result = functionIdentity.get(entry.incarnation());
                if (result == null) {
                    throw new ConstructUnlowered("function-typed load of '"
                        + identifier.name() + "' whose cell value identity is not "
                        + "statically tracked (dynamic function values — parameters, "
                        + "catch bindings, iteration bindings, and first-class "
                        + "intrinsics, whose closed binding shape is the registry "
                        + "child's — are the registry child's resolution, B5)");
                }
            }
            if (result == null) {
                result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            }
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(identifier.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.BINDING_LOAD,
                new KindPayload.BindingLoadPayload(entry.cell().id,
                    entry.incarnation().generation()),
                result, descriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            return result;
        }

        /**
         * {@code CLOSURE_NEW} — the function-expression arm (closure-core
         * mode, ISSUE-0445): every function expression produces exactly
         * one {@code CLOSURE_NEW} publishing a fresh function identity
         * with the function expression's exact checked signature, the
         * body's captures in first-reference order (collected during the
         * buffered body walk — B3), and the {@code LoweredBody} binding.
         * The body ops flush after the {@code CLOSURE_NEW} op (the
         * buffered walk runs first so the captures are known when the
         * payload is built). A threaded result slot ({@code slot}
         * non-null) becomes the {@code CLOSURE_NEW} result identity — the
         * closure identity <em>is</em> the {@code CLASS_DEFAULT} op's
         * result for a function-literal default (K-D3), and the
         * {@code LoweredBody} binding registers under that identity so
         * R-FUNCTION-BINDING resolves it.
         */
        private ValueId lowerClosureExpr(FunctionExpr functionExpr) {
            return lowerClosureExpr(functionExpr, null);
        }

        private ValueId lowerClosureExpr(FunctionExpr functionExpr, ValueId slot) {
            BlockId bodyBlock = allocateBlock();
            FunctionId functionId = ids.nextFunctionId(module, nextOrdinal++, 0);
            Type checkedFunctionType = checkedType(functionExpr);
            if (!(checkedFunctionType instanceof Type.Func)) {
                throw new ConstructUnlowered("function expression of non-function checked "
                    + "type " + typeName(checkedFunctionType) + " (a checked FunctionExpr "
                    + "must be function-typed)");
            }
            RuntimeDescriptor.Func signature = (RuntimeDescriptor.Func)
                ContainerPayloadDescriptors.resultDescriptorOf(checkedFunctionType);
            List<SemanticOp> bodyOps = new ArrayList<>();
            List<CapturedCell> captured = new ArrayList<>();
            emitTargets.push(bodyOps);
            captureBorders.push(bindingScopes.size());
            captureCollectors.push(captured);
            try {
                checkerScopeNodes.push(functionExpr.body());
                pushBindingFrame();
                blockStack.push(bodyBlock);
                FunctionContext reservedClosureContext = null;
                if (e7Calls) {
                    // The E7 closure reservation: RETURNs inside the
                    // closure body lower against a per-closure-site
                    // context whose reserved return boundary/call-site
                    // identities the CALL(INDIRECT) resolves.
                    reservedClosureContext = new FunctionContext(functionId, bodyBlock,
                        signature, ids.nextOpId(module, nextOrdinal++, 0),
                        ids.nextOpId(module, nextOrdinal++, 0));
                    reservedClosureContext.assignShape(InvocationShape.SOURCE_CALL,
                        reservedClosureContext.callSiteOpId);
                    contextsByFunctionId.put(functionId, reservedClosureContext);
                    functionStack.push(reservedClosureContext);
                }
                for (deal.ast.Parameter parameter : functionExpr.params()) {
                    BindingId binding = ids.nextBindingId(module, nextOrdinal++, 0);
                    BindingCoreIncarnation incarnation = new BindingCoreIncarnation(
                        INITIAL_LOOP_GENERATION, bodyBlock, BindingCellKind.DIRECT,
                        true, BindingProducer.BINDING_ALLOC, false);
                    registerBinding(parameter.name(), binding, incarnation);
                    parameterBindings.add(binding);
                    emitUserNullOp(SemanticOpKind.BINDING_ALLOC,
                        new KindPayload.BindingAllocPayload(binding, bodyBlock, true,
                            cellKinds.cellKindOf(incarnation), INITIAL_LOOP_GENERATION),
                        parameter.span(), FailurePolicyId.NO_DEAL_FAILURE);
                }
                boolean closureBodyComplete = false;
                try {
                    statementWalk.walk(functionExpr.body().statements(), false);
                    closureBodyComplete = true;
                } finally {
                    if (reservedClosureContext != null) {
                        if (closureBodyComplete
                                && !Boolean.TRUE.equals(blockTerminated.get(bodyBlock))) {
                            if (!(signature.returnType()
                                    instanceof RuntimeDescriptor.Null)) {
                                throw new ConstructUnlowered("closure body is not "
                                    + "terminated and its return type is not null "
                                    + "(the E7 slice lowers the pinned implicit null "
                                    + "return only)");
                            }
                            lowerImplicitReturn(reservedClosureContext,
                                functionExpr.body().span());
                        }
                        functionStack.pop();
                    }
                    blockStack.pop();
                    popBindingFrame();
                    checkerScopeNodes.pop();
                }
            } finally {
                captureCollectors.pop();
                captureBorders.pop();
                emitTargets.pop();
            }
            List<BindingId> captureIds = new ArrayList<>();
            for (CapturedCell capture : captured) {
                captureIds.add(capture.cell().id);
            }
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            emitClosureNew(functionId, result, signature, captureIds, bodyBlock,
                functionExpr.span(), captured);
            emitTarget().addAll(bodyOps);
            return result;
        }

        /** {@code ARRAY_NEW} — element prior steps, the op, then the boundary children. */
        private ValueId lowerArrayNew(ArrayLiteralExpr literal) {
            return lowerArrayNew(literal, null);
        }

        private ValueId lowerArrayNew(ArrayLiteralExpr literal, ValueId slot) {
            Type type = checkedType(literal);
            if (!(type instanceof Type.Array arrayType)) {
                throw new ConstructUnlowered("array literal of non-array checked type "
                    + typeName(type) + " (a checked ArrayLiteralExpr must be array-typed)");
            }
            RuntimeDescriptor elementDescriptor =
                containerElementDescriptor(arrayType.element());
            List<ValueId> values = new ArrayList<>();
            for (ExpressionNode element : literal.elements()) {
                values.add(lowerExpression(element));
            }
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            List<OpId> boundaryIds = new ArrayList<>();
            List<SemanticOp> children = new ArrayList<>();
            for (int i = 0; i < literal.elements().size(); i++) {
                SemanticOp child = buildNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.ARRAY_LITERAL_ELEMENT,
                        elementDescriptor, values.get(i),
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    literal.elements().get(i).span(), FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
                    SourceOriginKind.SYNTHETIC, opId);
                boundaryIds.add(child.opId());
                children.add(child);
            }
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(literal.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.ARRAY_NEW,
                new KindPayload.ArrayNewPayload(elementDescriptor, values, boundaryIds),
                result, ContainerPayloadDescriptors.resultDescriptorOf(arrayType),
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            for (SemanticOp child : children) {
                emit(child);
            }
            if (creationRuleAnalysis && elementDescriptor instanceof RuntimeDescriptor.Func) {
                // Function-typed array literal element positions: typed
                // boundary positions never adapt (B6) — the direct
                // value flow into each ARRAY_LITERAL_ELEMENT boundary
                // slot is the wiring E4's boundary producer consumes;
                // the classifier records the closed classifications in
                // element order.
                for (int i = 0; i < literal.elements().size(); i++) {
                    recordBoundaryClassification(BoundaryKind.ARRAY_LITERAL_ELEMENT,
                        checkedType(literal.elements().get(i)), arrayType.element());
                }
            }
            return result;
        }

        /** {@code TABLE_NEW} — entry values in source order, then the op. */
        private ValueId lowerTableNew(ObjectLiteralExpr literal) {
            return lowerTableNew(literal, null);
        }

        private ValueId lowerTableNew(ObjectLiteralExpr literal, ValueId slot) {
            Type type = checkedType(literal);
            if (type instanceof Type.Class classType) {
                if (!classCore) {
                    throw new ConstructUnlowered("class-typed object literal "
                        + DescriptorService.semanticModulePath(classType.identity())
                        + "/" + classType.name()
                        + " (class construction and CLASS_NEW are E9's)");
                }
                return lowerClassLiteral(literal, slot);
            }
            if (!(type instanceof Type.Table)) {
                throw new ConstructUnlowered("object literal of non-table, non-class checked "
                    + "type " + typeName(type) + " (a checked ObjectLiteralExpr must be "
                    + "table- or class-typed)");
            }
            List<KindPayload.TableEntry> entries = new ArrayList<>();
            for (Property property : literal.properties()) {
                ValueId value = lowerExpression(property.value());
                entries.add(new KindPayload.TableEntry(property.name(), value));
            }
            return emitValueOp(SemanticOpKind.TABLE_NEW,
                new KindPayload.TableNewPayload(entries), literal.span(),
                ContainerPayloadDescriptors.resultDescriptorOf(Type.Table.INSTANCE),
                FailurePolicyId.NO_DEAL_FAILURE, slot);
        }

        /** {@code ARRAY_LENGTH}/{@code MEMBER_READ} — the member-access dispatch. */
        /**
         * {@code INDEX_READ} (array targets) — the carrier's read arm:
         * the container and the key complete as prior steps;
         * {@code INDEX_NORMALIZE(ARRAY_READ)} computes the slot from the
         * normalize-time {@code ARRAY_LENGTH} read; the
         * {@code ARRAY_ELEMENT_READ} boundary child (policy
         * {@code ARRAY_READ_INDEX_THEN_DESCRIPTOR}) enforces the
         * negative-index E8002 before any storage access and passes a
         * missing (past-end) read through to the consuming contextual
         * boundary/operand — the comparison operands' missing≡null rule
         * and the declaration boundary's E8001 projection decide.
         * Table index reads stay E2's (the carrier slice lowers array
         * index reads only).
         */
        private ValueId lowerIndexRead(IndexExpr index, ValueId slot) {
            Type objectType = checkedType(index.array());
            if (!(objectType instanceof Type.Array)) {
                throw new ConstructUnlowered("index read on " + typeName(objectType)
                    + " (the carrier slice lowers array index reads; table index reads "
                    + "are E2's)");
            }
            RuntimeDescriptor resultType =
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(index));
            ValueId container = lowerExpression(index.array());
            ValueId key = lowerExpression(index.index());
            ValueId length = emitValueOp(SemanticOpKind.ARRAY_LENGTH,
                new KindPayload.ArrayLengthPayload(container), index.span(),
                ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE),
                FailurePolicyId.INT32_RESULT);
            RuntimeDescriptor intDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE);
            ValueId normalize = emitOperandOp(SemanticOpKind.INDEX_NORMALIZE,
                new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_READ, key, length),
                List.of(key, length), List.of(
                    ContainerPayloadDescriptors.resultDescriptorOf(
                        checkedType(index.index())),
                    intDescriptor),
                index.span(), intDescriptor,
                FailurePolicyId.NO_DEAL_FAILURE);
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            AnchorId boundaryAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId boundaryOpId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(index.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.INDEX_READ,
                new KindPayload.IndexReadPayload(container, normalize, boundaryOpId),
                result, resultType, List.of(container, normalize), List.of(
                    ContainerPayloadDescriptors.resultDescriptorOf(objectType),
                    intDescriptor),
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            SourceOrigin boundaryOrigin = new SourceOrigin(sourceId,
                toSourceSpan(index.span()), SourceOriginKind.SYNTHETIC, boundaryAnchor,
                opId);
            emit(buildOp(boundaryOpId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.ARRAY_ELEMENT_READ,
                    resultType, result,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                null, null, FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
                boundaryOrigin));
            return result;
        }

        private ValueId lowerMemberAccess(MemberAccessExpr access) {
            return lowerMemberAccess(access, null);
        }

        private ValueId lowerMemberAccess(MemberAccessExpr access, ValueId slot) {
            // Module member access first: the checker types a module-symbol
            // object as `table`, so the symbol fact must win over the type
            // fact (EXPORT_READ is E10's).
            if (access.object() instanceof IdentifierExpr identifier
                    && checks.symbolTable().resolve(identifier.name())
                        instanceof Symbol.ModuleSymbol) {
                throw new ConstructUnlowered("module member access '" + identifier.name()
                    + "." + access.field() + "' (EXPORT_READ is E10's)");
            }
            Type objectType = checkedType(access.object());
            if (objectType instanceof Type.Array && "length".equals(access.field())) {
                return lowerArrayLength(access, slot);
            }
            if (objectType instanceof Type.Table) {
                return lowerMemberRead(access, slot);
            }
            if (objectType instanceof Type.Class classType) {
                if (!classCore) {
                    throw new ConstructUnlowered("class member access "
                        + DescriptorService.semanticModulePath(classType.identity())
                        + "/" + classType.name() + "." + access.field()
                        + " (FIELD_READ is E9's)");
                }
                return lowerFieldRead(access, classType, slot);
            }
            if (classCore && objectType instanceof Type.Nullable nullable
                    && nullable.inner() instanceof Type.Class innerClassType) {
                // The checker's cross-module nullable-class read unwrap
                // (a receiver of checked type ?C over a foreign identity):
                // the receiver lowers as checked (nullable) and the
                // runtime null guard is the FIELD_READ op's
                // UNTYPED_CLASS_INPUT boundary (K-D6).
                return lowerFieldRead(access, innerClassType, slot);
            }
            if (objectType instanceof Type.Bytes) {
                throw new ConstructUnlowered("member access '" + access.field()
                    + "' on bytes (bytes value semantics are ISSUE-0158's; a bytes member "
                    + "access reaching an E5 arm fails hard)");
            }
            throw new ConstructUnlowered("member access '" + access.field() + "' on "
                + typeName(objectType) + " (no member-access arm for this receiver shape "
                + "in this stage's window)");
        }

        /**
         * {@code FIELD_READ} — the class member-read arm of the class
         * walk (K-D6): exactly one {@code FIELD_READ} op whose receiver
         * lowers exactly once as a prior step and whose key is the
         * static field name (never evaluated), plus two {@code BOUNDARY}
         * children in order — (1) the nominal receiver boundary, kind
         * {@code UNTYPED_CLASS_INPUT}, descriptor {@code class:<ClassId>},
         * input = the receiver; (2) the field boundary, kind
         * {@code OPTIONAL_FIELD_READ}, descriptor = the read's checked
         * result descriptor (the checker's nullable-wrapped type for
         * optional fields), input = the {@code FIELD_READ} result. Both
         * children carry the descriptor-kind policy, the canonical
         * runtime-validation realization, a {@code SYNTHETIC} origin at
         * the access span, and {@code parentOpId} = the
         * {@code FIELD_READ} op (K-D12). A cross-module nullable class
         * read lowers the receiver as checked (nullable) — the runtime
         * null guard is the {@code UNTYPED_CLASS_INPUT} boundary. The op
         * carries policy {@code NO_DEAL_FAILURE} and publishes the
         * read's checked result descriptor.
         *
         * @param access    the checked class member access; non-null
         * @param classType the class the receiver's checked type names
         *                  (the inner class of a cross-module nullable
         *                  receiver); non-null
         * @param slot      the result slot of the final producing op, or
         *                  {@code null} to allocate one
         * @return the produced {@code ValueId} (the slot when given)
         * @throws ConstructUnlowered on an unrepresentable receiver
         *         descriptor (a fact defect)
         */
        private ValueId lowerFieldRead(MemberAccessExpr access, Type.Class classType,
                                       ValueId slot) {
            ClassId classId = new ClassId(
                DescriptorService.semanticModulePath(classType.identity()), classType.name());
            RuntimeDescriptor classDescriptor;
            try {
                classDescriptor = DescriptorService.describe(classType);
            } catch (DescriptorService.Defect defect) {
                throw new ConstructUnlowered("class member access "
                    + classId + "." + access.field() + " on an unrepresentable receiver "
                    + "type (" + defect.getMessage() + ")");
            }
            RuntimeDescriptor resultDescriptor =
                ContainerPayloadDescriptors.resultDescriptorOf(checkedType(access));
            ValueId receiver = lowerExpression(access.object());
            ValueId result = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SemanticOp receiverBoundary = buildNullOp(SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.UNTYPED_CLASS_INPUT,
                    classDescriptor, receiver,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                access.span(), descriptorKindPolicy(classDescriptor),
                SourceOriginKind.SYNTHETIC, opId);
            SemanticOp fieldBoundary = buildNullOp(SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.OPTIONAL_FIELD_READ,
                    resultDescriptor, result,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                access.span(), descriptorKindPolicy(resultDescriptor),
                SourceOriginKind.SYNTHETIC, opId);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(access.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, SemanticOpKind.FIELD_READ,
                new KindPayload.FieldReadPayload(receiver, classId, access.field()),
                result, resultDescriptor, FailurePolicyId.NO_DEAL_FAILURE, origin));
            emit(receiverBoundary);
            emit(fieldBoundary);
            return result;
        }

        /**
         * {@code HAS_FIELD} — the {@code has(obj.field)} arm of the class
         * walk (K-D7): exactly one {@code HAS_FIELD} op whose receiver
         * lowers exactly once as a prior step and whose key is the
         * static field name (never evaluated). The op runs no boundary
         * children, publishes {@code boolean}, and carries policy
         * {@code NO_DEAL_FAILURE}.
         *
         * @param has  the checked has expression; non-null
         * @param slot the result slot of the final producing op, or
         *             {@code null} to allocate one
         * @return the produced {@code ValueId} (the slot when given)
         */
        private ValueId lowerHasField(HasExpr has, ValueId slot) {
            ValueId receiver = lowerExpression(has.object());
            return emitValueOp(SemanticOpKind.HAS_FIELD,
                new KindPayload.HasFieldPayload(receiver, has.field()),
                has.span(),
                ContainerPayloadDescriptors.resultDescriptorOf(Type.Boolean.INSTANCE),
                FailurePolicyId.NO_DEAL_FAILURE, slot);
        }

        /** {@code ARRAY_LENGTH} — the receiver is one prior step, never re-evaluated. */
        private ValueId lowerArrayLength(MemberAccessExpr access) {
            return lowerArrayLength(access, null);
        }

        private ValueId lowerArrayLength(MemberAccessExpr access, ValueId slot) {
            ValueId receiver = lowerExpression(access.object());
            return emitValueOp(SemanticOpKind.ARRAY_LENGTH,
                new KindPayload.ArrayLengthPayload(receiver), access.span(),
                ContainerPayloadDescriptors.resultDescriptorOf(Type.Int.INSTANCE),
                FailurePolicyId.INT32_RESULT, slot);
        }

        /**
         * {@code MEMBER_READ} — the missing-aware read plus its contextual
         * child. A non-nullable read keeps the direct shape: one
         * {@code MEMBER_READ} publishing the read result plus one
         * {@code CONTEXTUAL_TABLE_READ} boundary child (missing →
         * nullable-null / E8001 via the contextual decision). A
         * missing-capable read (a nullable contextual type) lowers the
         * {@code OPTIONAL_READ} envelope: the {@code MEMBER_READ} op
         * publishes its result typed {@code INTERNAL_MISSING}, exactly one
         * {@code OPTIONAL_READ} op carries the raw value, the presence
         * marker, and the inner descriptor (missing → language null before
         * a present value is validated), and the
         * {@code CONTEXTUAL_TABLE_READ} boundary child validates the
         * optional read's result (present null passes the nullable
         * descriptor; a present wrong-kind value projects the pinned E8001).
         */
        private ValueId lowerMemberRead(MemberAccessExpr access) {
            return lowerMemberRead(access, null);
        }

        private ValueId lowerMemberRead(MemberAccessExpr access, ValueId slot) {
            Type contextualType = checkedType(access);
            RuntimeDescriptor resultType =
                ContainerPayloadDescriptors.resultDescriptorOf(contextualType);
            ValueId receiver = lowerExpression(access.object());
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(access.span()),
                SourceOriginKind.USER, anchor, currentParent());
            FailurePolicyId childPolicy = resultType instanceof RuntimeDescriptor.Func
                ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
            if (contextualType instanceof Type.Nullable nullable) {
                // The OPTIONAL_READ envelope (the CONTAINERS_AND_STRINGS
                // extras, parent E3): a missing-capable read — a table
                // member read whose checked contextual type is nullable —
                // lowers to the raw INTERNAL_MISSING read plus exactly one
                // OPTIONAL_READ op carrying the present value (or internal
                // missing) and the inner descriptor, with the present
                // branch validated by the CONTEXTUAL_TABLE_READ boundary
                // child per the closed table's optional-read rule (missing
                // → language null before a present value is validated).
                RuntimeDescriptor inner =
                    ContainerPayloadDescriptors.resultDescriptorOf(nullable.inner());
                ValueId readResult = ids.nextValueId(module, nextOrdinal++, 0);
                emit(buildOp(opId, SemanticOpKind.MEMBER_READ,
                    new KindPayload.MemberReadPayload(receiver, access.field()),
                    readResult, InternalResultType.INTERNAL_MISSING,
                    FailurePolicyId.NO_DEAL_FAILURE, origin));
                ValueId result = slot != null ? slot
                    : ids.nextValueId(module, nextOrdinal++, 0);
                AnchorId optionalAnchor = ids.nextAnchorId(module, nextOrdinal++, 0);
                OpId optionalOpId = ids.nextOpId(module, nextOrdinal++, 0);
                SourceOrigin optionalOrigin = new SourceOrigin(sourceId,
                    toSourceSpan(access.span()), SourceOriginKind.USER, optionalAnchor,
                    currentParent());
                SemanticOp optionalRead = buildOp(optionalOpId,
                    SemanticOpKind.OPTIONAL_READ,
                    new KindPayload.OptionalReadPayload(readResult, true, inner),
                    result, resultType, List.of(readResult), List.of(resultType),
                    FailurePolicyId.NO_DEAL_FAILURE, optionalOrigin);
                emit(optionalRead);
                emitNullOp(SemanticOpKind.BOUNDARY,
                    new KindPayload.BoundaryPayload(BoundaryKind.CONTEXTUAL_TABLE_READ,
                        resultType, result,
                        new BoundaryRealization.RuntimeValidation(
                            CANONICAL_RUNTIME_VALIDATION_ID)),
                    access.span(), childPolicy, SourceOriginKind.SYNTHETIC, optionalOpId);
                if (creationRuleAnalysis && resultType instanceof RuntimeDescriptor.Func) {
                    recordBoundaryClassification(BoundaryKind.CONTEXTUAL_TABLE_READ,
                        contextualType, contextualType);
                }
                return result;
            }
            ValueId readResult = slot != null ? slot
                : ids.nextValueId(module, nextOrdinal++, 0);
            emit(buildOp(opId, SemanticOpKind.MEMBER_READ,
                new KindPayload.MemberReadPayload(receiver, access.field()),
                readResult, resultType, FailurePolicyId.NO_DEAL_FAILURE, origin));
            emitNullOp(SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.CONTEXTUAL_TABLE_READ,
                    resultType, readResult,
                    new BoundaryRealization.RuntimeValidation(
                        CANONICAL_RUNTIME_VALIDATION_ID)),
                access.span(), childPolicy, SourceOriginKind.SYNTHETIC, opId);
            if (creationRuleAnalysis && resultType instanceof RuntimeDescriptor.Func) {
                // A function-typed contextual table read: a typed
                // boundary position never adapts (B6) — the read's
                // direct result flow into the CONTEXTUAL_TABLE_READ
                // boundary slot is the wiring E4's boundary producer
                // consumes (the read publishes the contextual
                // descriptor itself, so the classifier records the
                // exact-direct classification).
                recordBoundaryClassification(BoundaryKind.CONTEXTUAL_TABLE_READ,
                    contextualType, contextualType);
            }
            return readResult;
        }

        /** {@code STRING_CONCAT}/{@code BINARY} — the binary dispatch (I3 arithmetic). */
        private ValueId lowerBinary(BinaryExpr binary) {
            return lowerBinary(binary, null);
        }

        private ValueId lowerBinary(BinaryExpr binary, ValueId slot) {
            Type type = checkedType(binary);
            if (binary.op() == BinaryOp.ADD && type instanceof Type.String) {
                return lowerStringConcat(binary, slot);
            }
            if (binary.op() == BinaryOp.AND || binary.op() == BinaryOp.OR) {
                return lowerLogicalBranch(binary, slot);
            }
            if (isArithmeticOperator(binary.op())) {
                return lowerArithmeticBinary(binary, slot);
            }
            if (bindingCore && isComparisonOperator(binary.op())) {
                // The binding walk consumes the single comparison producer
                // (the values epic's producer) for condition/initializer
                // comparison operands — this child never implements
                // comparison-selector lowering itself. The carrier slice
                // threads the result slot (the LOOP(FOR) condition
                // re-production publishes one condition value identity,
                // C-D4).
                return lowerComparisonBinary(binary, slot);
            }
            throw new ConstructUnlowered("binary selector " + binary.op()
                + " of checked type " + typeName(type)
                + " (comparison selectors are the comparison producer "
                + "ComparisonSelectorLowering's; string + lowers to "
                + "STRING_CONCAT, never BINARY)");
        }


        /** True iff the operator is one of the six comparison operators (B-D3). */
        private static boolean isComparisonOperator(BinaryOp op) {
            return switch (op) {
                case EQ, NEQ, LT, LTE, GT, GTE -> true;
                case ADD, SUB, MUL, DIV, MOD, POW, AND, OR -> false;
            };
        }

        /**
         * One {@code BINARY} comparison op through the single comparison
         * producer (B-D3): operands complete in source order (the
         * binding-environment loads included), the producer selects the
         * closed selector from the checked operand types, stamps the
         * snapshot digest, and allocates its result/op ids at the
         * session's next source ordinal — the produced op appends to the
         * session in source order.
         */
        private ValueId lowerComparisonBinary(BinaryExpr binary, ValueId slot) {
            ValueId left = lowerExpression(binary.left());
            ValueId right = lowerExpression(binary.right());
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(binary.span()),
                SourceOriginKind.USER, anchor, chainParents.peek());
            SemanticOp comparison = ComparisonSelectorLowering.produce(module,
                binary.op(), checkedType(binary.left()), checkedType(binary.right()),
                left, right, origin, ids, nextOrdinal, 0);
            // The producer consumed exactly one source ordinal (VALUE, OP).
            nextOrdinal++;
            if (slot != null && !slot.equals(comparison.result())) {
                // The carrier's slot threading: the condition re-production
                // publishes the pinned condition slot; the result identity
                // is outside the operation-contract digest, so the digest
                // is unchanged.
                comparison = new SemanticOp(comparison.opId(), comparison.kind(),
                    comparison.origin(), slot, comparison.resultType(),
                    comparison.operands(), comparison.operandTypes(),
                    comparison.payload(), comparison.failurePolicy(),
                    comparison.contract());
            }
            emit(comparison);
            return (ValueId) comparison.result();
        }

        /**
         * {@code BRANCH(LOGICAL_AND/LOGICAL_OR)} — the logical short-circuit
         * arm (C-D3; never {@code BINARY}): the left operand completes
         * before START as the condition; the right operand's producing ops
         * live in {@code selectedBlock} and execute only when the left
         * value does not decide the result — AND: left false → result
         * false, block skipped; OR: left true → result true, block
         * skipped. The op's result {@code ValueId} is the right operand's
         * value identity (result type {@code D(boolean)} — a boolean
         * either way, checker-pinned boolean operands). Chained
         * {@code &&}/{@code ||} lower to nested {@code BRANCH}es in
         * source order. Block ops record the {@code BRANCH} as
         * {@code parentOpId}; the {@code BRANCH} op precedes its child
         * block ops in the unit list.
         */
        private ValueId lowerLogicalBranch(BinaryExpr binary, ValueId slot) {
            if (!(checkedType(binary.left()) instanceof Type.Boolean)
                    || !(checkedType(binary.right()) instanceof Type.Boolean)) {
                throw new ConstructUnlowered("logical operator " + binary.op()
                    + " over a non-boolean checked operand (the checker pins boolean "
                    + "operands — a missing checker fact is a producer defect)");
            }
            ControlSelector selector = binary.op() == BinaryOp.AND
                ? ControlSelector.LOGICAL_AND : ControlSelector.LOGICAL_OR;
            ValueId left = lowerExpression(binary.left());
            BlockId selectedBlock = allocateBlock();
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            int mark = emitTarget().size();
            pushBlockParent(opId);
            pushBlock(selectedBlock);
            ValueId right;
            try {
                right = lowerExpression(binary.right(), slot);
            } finally {
                popBlock();
                popBlockParent();
            }
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(binary.span()),
                SourceOriginKind.USER, anchor, currentParent());
            emitAt(mark, buildOp(opId, SemanticOpKind.BRANCH,
                new KindPayload.BranchPayload(selector, left, selectedBlock, null),
                right, ContainerPayloadDescriptors.resultDescriptorOf(Type.Boolean.INSTANCE),
                FailurePolicyId.NO_DEAL_FAILURE, origin));
            return right;
        }

        /** {@code STRING_CONCAT} — the string-{@code +} arm; never {@code BINARY}. */
        private ValueId lowerStringConcat(BinaryExpr binary) {
            return lowerStringConcat(binary, null);
        }

        private ValueId lowerStringConcat(BinaryExpr binary, ValueId slot) {
            ValueId left = lowerExpression(binary.left());
            ValueId right = lowerExpression(binary.right());
            return emitValueOp(SemanticOpKind.STRING_CONCAT,
                new KindPayload.StringConcatPayload(List.of(left, right)),
                binary.span(),
                ContainerPayloadDescriptors.resultDescriptorOf(Type.String.INSTANCE),
                FailurePolicyId.NO_DEAL_FAILURE, slot);
        }

        /** True iff the operator is one of the six arithmetic operators (I3). */
        private static boolean isArithmeticOperator(BinaryOp op) {
            return switch (op) {
                case ADD, SUB, MUL, DIV, MOD, POW -> true;
                case EQ, NEQ, LT, LTE, GT, GTE, AND, OR -> false;
            };
        }

        /**
         * {@code BINARY} — the I3 int32/number arithmetic arm: exactly one
         * closed selector from the operator plus the checked operand type
         * ({@code INT32_ADD/SUB/MUL/DIV_TRUNC/MOD_TRUNC/POW} over int;
         * {@code NUMBER_ADD/SUB/MUL/DIV_IEEE/MOD_FLOOR/POW_IEEE} over
         * number), operands in source order (left then right), the policy
         * stamped from the single closed {@code binaryPolicy} table (never
         * a copy), and the result descriptor from the checked result type.
         * Any operator/operand shape outside the map is a producer defect
         * ({@link ConstructUnlowered}) — never a guessed selector.
         */
        private ValueId lowerArithmeticBinary(BinaryExpr binary) {
            return lowerArithmeticBinary(binary, null);
        }

        private ValueId lowerArithmeticBinary(BinaryExpr binary, ValueId slot) {
            Type leftType = checkedType(binary.left());
            BinarySelector selector;
            if (leftType instanceof Type.Int) {
                selector = switch (binary.op()) {
                    case ADD -> BinarySelector.INT32_ADD;
                    case SUB -> BinarySelector.INT32_SUB;
                    case MUL -> BinarySelector.INT32_MUL;
                    case DIV -> BinarySelector.INT32_DIV_TRUNC;
                    case MOD -> BinarySelector.INT32_MOD_TRUNC;
                    case POW -> BinarySelector.INT32_POW;
                    default -> throw new ConstructUnlowered("arithmetic operator "
                        + binary.op() + " outside the I3 int32 rows (producer defect)");
                };
            } else if (leftType instanceof Type.Number) {
                selector = switch (binary.op()) {
                    case ADD -> BinarySelector.NUMBER_ADD;
                    case SUB -> BinarySelector.NUMBER_SUB;
                    case MUL -> BinarySelector.NUMBER_MUL;
                    case DIV -> BinarySelector.NUMBER_DIV_IEEE;
                    case MOD -> BinarySelector.NUMBER_MOD_FLOOR;
                    case POW -> BinarySelector.NUMBER_POW_IEEE;
                    default -> throw new ConstructUnlowered("arithmetic operator "
                        + binary.op() + " outside the I3 number rows (producer defect)");
                };
            } else {
                throw new ConstructUnlowered("arithmetic binary " + binary.op()
                    + " over non-int/number checked operand " + typeName(leftType)
                    + " (a checked arithmetic expression must be int- or number-typed)");
            }
            ValueId left = lowerExpression(binary.left());
            ValueId right = lowerExpression(binary.right());
            return emitOperandOp(SemanticOpKind.BINARY,
                new KindPayload.BinaryPayload(selector, null, null),
                List.of(left, right),
                List.of(valueDescriptorOf(leftType),
                    valueDescriptorOf(checkedType(binary.right()))),
                binary.span(), valueDescriptorOf(checkedType(binary)),
                SemanticIrValidator.binaryPolicy(selector), slot);
        }

        /**
         * {@code UNARY} — the I3 arm: exactly one closed selector from
         * the operator plus the operand's checked type ({@code BOOL_NOT}
         * over boolean; {@code INT32_NEG} over int; {@code NUMBER_NEG}
         * over number), the operand as one prior step (operands complete
         * left-to-right before {@code UNARY} START), the policy stamped
         * from the single closed {@code unaryPolicy} rule (never a copy),
         * and the result descriptor from the checked result type.
         */
        private ValueId lowerUnary(UnaryExpr unary) {
            return lowerUnary(unary, null);
        }

        private ValueId lowerUnary(UnaryExpr unary, ValueId slot) {
            Type operandType = checkedType(unary.expr());
            UnarySelector selector;
            switch (unary.op()) {
                case NOT -> {
                    if (!(operandType instanceof Type.Boolean)) {
                        throw new ConstructUnlowered("unary '!' over non-boolean checked "
                            + "operand " + typeName(operandType)
                            + " (a missing checker fact is a producer defect)");
                    }
                    selector = UnarySelector.BOOL_NOT;
                }
                case NEG -> {
                    if (operandType instanceof Type.Int) {
                        selector = UnarySelector.INT32_NEG;
                    } else if (operandType instanceof Type.Number) {
                        selector = UnarySelector.NUMBER_NEG;
                    } else {
                        throw new ConstructUnlowered("unary '-' over non-int/number checked "
                            + "operand " + typeName(operandType)
                            + " (a missing checker fact is a producer defect)");
                    }
                }
                default -> throw new ConstructUnlowered("unary operator " + unary.op()
                    + " outside the closed UnarySelector rows (producer defect)");
            }
            ValueId operand = lowerExpression(unary.expr());
            return emitOperandOp(SemanticOpKind.UNARY,
                new KindPayload.UnaryPayload(selector),
                List.of(operand), List.of(valueDescriptorOf(operandType)),
                unary.span(), valueDescriptorOf(checkedType(unary)),
                SemanticIrValidator.unaryPolicy(selector), slot);
        }

        /**
         * {@code INTRINSIC_CALL} — the I3 arm: a call of the {@code int}
         * or {@code number} intrinsic ({@code Symbol.IntrinsicSymbol})
         * lowers to one {@code INTRINSIC_CALL} with
         * {@code INT_CONVERT}/{@code NUMBER_CONVERT}, zero {@code BOUNDARY}
         * children, the single input as one prior step, and the conversion
         * policy ({@code INT_CONVERSION}/{@code NUMBER_CONVERSION} — the
         * single closed intrinsic rule) as the terminal check. Every other
         * call is a foreign construct ({@code CALL} is E7's); {@code
         * bytes(...)} is the bytes exclusion.
         */
        private ValueId lowerIntrinsicCall(CallExpr call) {
            return lowerIntrinsicCall(call, null);
        }

        private ValueId lowerIntrinsicCall(CallExpr call, ValueId slot) {
            IntrinsicKind kind = intrinsicKindOf(call);
            ExpressionNode argument = call.args().get(0);
            Type argumentType = checkedType(argument);
            ValueId input = lowerExpression(argument);
            return emitOperandOp(SemanticOpKind.INTRINSIC_CALL,
                new KindPayload.IntrinsicCallPayload(kind, input),
                List.of(input), List.of(valueDescriptorOf(argumentType)),
                call.span(), valueDescriptorOf(checkedType(call)),
                SemanticIrValidator.intrinsicPolicy(kind), slot);
        }

        /**
         * The intrinsic-call classifier (I3): exactly {@code int(...)}
         * and {@code number(...)} calls of the root
         * {@code Symbol.IntrinsicSymbol} bindings lower; every other call
         * shape — including {@code bytes(...)}, {@code has(...)} call
         * fallbacks, and ordinary user calls — fails closed.
         */
        private IntrinsicKind intrinsicKindOf(CallExpr call) {
            if (call.args().size() == 1
                    && call.callee() instanceof IdentifierExpr identifier) {
                Symbol symbol = checks.symbolTable().resolve(identifier.name());
                if (symbol instanceof Symbol.IntrinsicSymbol intrinsic) {
                    IntrinsicKind kind = conversionIntrinsicKind(intrinsic.name());
                    if (kind != null) {
                        return kind;
                    }
                }
            }
            throw new ConstructUnlowered("call expression (only int()/number() intrinsic "
                + "calls lower in this slice — INTRINSIC_CALL is the I3 terminal-check "
                + "arm; the CALL machinery is E7's and bytes() is the bytes exclusion)");
        }

        /**
         * The two conversion intrinsics' name-to-kind map (the seed's and
         * the intrinsic-call classifier's single authority): {@code int}
         * is {@code INT_CONVERT} and {@code number} is
         * {@code NUMBER_CONVERT}; every other name — including the
         * {@code bytes}/{@code has} intrinsics — maps to no conversion
         * kind.
         *
         * @param name the root intrinsic binding's name; non-null
         * @return the conversion kind, or {@code null} for a non-conversion
         *         intrinsic
         */
        private static IntrinsicKind conversionIntrinsicKind(String name) {
            return switch (name) {
                case "int" -> IntrinsicKind.INT_CONVERT;
                case "number" -> IntrinsicKind.NUMBER_CONVERT;
                default -> null;
            };
        }

        /**
         * The pinned one-line scalar descriptor rows of the value-operation
         * slice (I3): the slice admits exactly these rows —
         * null, boolean, signed32 int, number, string, and the nullable
         * rows over int/number/boolean (the nullable descriptor over the
         * same inner row) — for exactly
         * the descriptor positions its arms introduce (the conversion
         * intrinsics admit nullable int/number inputs). The rows realize
         * through the single {@link DescriptorService} producer (the
         * verbatim D2 scalar table — the slice builds no structural
         * descriptor service, ISSUE-0233 is excluded here); every other
         * checked type reaching a value-op descriptor position is a
         * producer defect ({@link ConstructUnlowered}).
         */
        private static RuntimeDescriptor valueDescriptorOf(Type type) {
            boolean admissible = switch (type) {
                case Type.Null ignored -> true;
                case Type.Boolean ignored -> true;
                case Type.Int ignored -> true;
                case Type.Number ignored -> true;
                case Type.String ignored -> true;
                case Type.Nullable nullable -> switch (nullable.inner()) {
                    case Type.Boolean ignored -> true;
                    case Type.Int ignored -> true;
                    case Type.Number ignored -> true;
                    default -> false;
                };
                default -> false;
            };
            if (!admissible) {
                throw new ConstructUnlowered(
                    "value-slice descriptor position over non-scalar checked type "
                        + typeName(type) + " (the slice's pinned one-line scalar rows "
                        + "only; the structural DescriptorService is ISSUE-0233's)");
            }
            try {
                return DescriptorService.describe(type);
            } catch (DescriptorService.Defect defect) {
                throw new ConstructUnlowered(
                    "value-slice descriptor position over unrepresentable checked type "
                        + typeName(type) + " (" + defect.getMessage() + ")");
            }
        }

        /** {@code STRING_CONCAT} — the template arm with fragment {@code CONST} steps. */
        private ValueId lowerTemplate(TemplateLiteralExpr template) {
            return lowerTemplate(template, null);
        }

        private ValueId lowerTemplate(TemplateLiteralExpr template, ValueId slot) {
            List<ValueId> fragments = new ArrayList<>();
            List<ExpressionNode> parts = template.parts();
            for (int i = 0; i < parts.size(); i++) {
                ExpressionNode part = parts.get(i);
                if (i % 2 == 0) {
                    if (!(part instanceof LiteralExpr literal)
                            || !(literal.value() instanceof LiteralValue.StringLiteral text)) {
                        throw new ConstructUnlowered("template literal part at index " + i
                            + " is not a literal string fragment (the parser alternates "
                            + "literal strings and interpolations — a parser defect)");
                    }
                    fragments.add(lowerConst(literal));
                } else {
                    fragments.add(lowerExpression(part));
                }
            }
            return emitValueOp(SemanticOpKind.STRING_CONCAT,
                new KindPayload.StringConcatPayload(fragments),
                template.span(),
                ContainerPayloadDescriptors.resultDescriptorOf(Type.String.INSTANCE),
                FailurePolicyId.NO_DEAL_FAILURE, slot);
        }

        // ---------------------------------------------------------------------
        // Emission helpers (D1/D4/D8)
        // ---------------------------------------------------------------------

        /**
         * The checked type fact of an expression (D4: consulted only as a
         * copied checker fact). A missing fact is a producer defect —
         * never an invented op and never a crash.
         */
        private Type checkedType(ExpressionNode expr) {
            Type type = checks.typeMap().get(expr);
            if (type == null) {
                throw new ConstructUnlowered(expr.getClass().getSimpleName()
                    + " without a checked type (a missing checker fact is a producer "
                    + "defect — never an invented op)");
            }
            return type;
        }

        /**
         * Emits one result-less source-positioned USER op (a declaration
         * or structured op of the binding walk: {@code BINDING_ALLOC}/
         * {@code BINDING_INIT}/{@code LOOP}/{@code FOR_EACH}/
         * {@code TRY_CATCH}) and returns its op id — the binding walk's
         * counterpart of {@link #emitValueOp} for ops whose result slot
         * is {@code none}.
         */
        private OpId emitUserNullOp(SemanticOpKind kind, KindPayload payload, Span span,
                                    FailurePolicyId policy) {
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.USER, anchor, chainParents.peek());
            emit(buildOp(opId, kind, payload, null, null, policy, origin));
            return opId;
        }

        /**
         * Emits one value-producing SYNTHETIC op without operands (the
         * for-let body-top generation-0 carry load — a synthetic step
         * with no source expression of its own) and returns its value id.
         */
        private ValueId emitSyntheticValueOp(SemanticOpKind kind, KindPayload payload,
                                             Span span, RuntimeDescriptor resultType,
                                             FailurePolicyId policy) {
            ValueId value = ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.SYNTHETIC, anchor, null);
            emit(buildOp(opId, kind, payload, value, resultType, List.of(), List.of(),
                policy, origin));
            return value;
        }

        /** Emits one value-producing USER op without operands and returns its value id. */
        private ValueId emitValueOp(SemanticOpKind kind, KindPayload payload, Span span,
                                    RuntimeDescriptor resultType, FailurePolicyId policy) {
            return emitOperandOp(kind, payload, List.of(), List.of(), span, resultType,
                policy, null);
        }

        /**
         * Emits one value-producing USER op without operands publishing the
         * given result slot ({@code null} allocates one) and returns its
         * value id (the slot when given).
         */
        private ValueId emitValueOp(SemanticOpKind kind, KindPayload payload, Span span,
                                    RuntimeDescriptor resultType, FailurePolicyId policy,
                                    ValueId slot) {
            return emitOperandOp(kind, payload, List.of(), List.of(), span, resultType,
                policy, slot);
        }

        /**
         * Emits one value-producing USER op carrying completed operand
         * values/types in source order (I3: operands complete left-to-right
         * before the op START; the slice never evaluates or re-reads an
         * operand) and returns its value id.
         */
        private ValueId emitOperandOp(SemanticOpKind kind, KindPayload payload,
                                      List<ValueId> operands,
                                      List<RuntimeDescriptor> operandTypes, Span span,
                                      RuntimeDescriptor resultType, FailurePolicyId policy) {
            return emitOperandOp(kind, payload, operands, operandTypes, span, resultType,
                policy, null);
        }

        /**
         * Emits one value-producing USER op with the given result slot:
         * the op publishes {@code slot} instead of a fresh value
         * ({@code null} allocates one) — the pinned mechanism of the
         * {@code LOOP(FOR)} condition re-production (one condition value
         * identity, re-produced by each block execution).
         */
        private ValueId emitOperandOp(SemanticOpKind kind, KindPayload payload,
                                      List<ValueId> operands,
                                      List<RuntimeDescriptor> operandTypes, Span span,
                                      RuntimeDescriptor resultType, FailurePolicyId policy,
                                      ValueId slot) {
            ValueId value = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span),
                SourceOriginKind.USER, anchor, currentParent());
            emit(buildOp(opId, kind, payload, value, resultType, operands, operandTypes,
                policy, origin));
            return value;
        }

        /**
         * Emits one value-producing op of the given origin kind publishing
         * the given result slot ({@code null} allocates one) — the
         * test-less FOR condition {@code CONST true} production (a
         * {@code SYNTHETIC} op, the for-statement span).
         */
        private ValueId emitValueOpWith(SemanticOpKind kind, KindPayload payload, Span span,
                                        RuntimeDescriptor resultType, FailurePolicyId policy,
                                        ValueId slot, SourceOriginKind originKind) {
            ValueId value = slot != null ? slot : ids.nextValueId(module, nextOrdinal++, 0);
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span), originKind,
                anchor, currentParent());
            emit(buildOp(opId, kind, payload, value, resultType, List.of(), List.of(),
                policy, origin));
            return value;
        }

        /** Emits one result-less child/terminal op and returns its op id. */
        private OpId emitNullOp(SemanticOpKind kind, KindPayload payload, Span span,
                                FailurePolicyId policy, SourceOriginKind originKind,
                                OpId parent) {
            SemanticOp op = buildNullOp(kind, payload, span, policy, originKind, parent);
            emit(op);
            return op.opId();
        }

        /** Builds (without emitting) one result-less child/terminal op. */
        private SemanticOp buildNullOp(SemanticOpKind kind, KindPayload payload, Span span,
                                       FailurePolicyId policy, SourceOriginKind originKind,
                                       OpId parent) {
            AnchorId anchor = ids.nextAnchorId(module, nextOrdinal++, 0);
            OpId opId = ids.nextOpId(module, nextOrdinal++, 0);
            SourceOrigin origin = new SourceOrigin(sourceId, toSourceSpan(span), originKind,
                anchor, parent);
            return buildOp(opId, kind, payload, null, null, policy, origin);
        }

        /**
         * Builds one op with its wired contract snapshot: the digest is
         * the single canonicalizer's SHA-256 over the snapshot's eight
         * pinned fields (T3), the selector is extracted from
         * selector-carrying payloads, and the behavior-referenced ids
         * live inside the payload itself. Operandless ops (the payload-
         * referenced container shapes) delegate with empty operand lists.
         */
        private SemanticOp buildOp(OpId opId, SemanticOpKind kind, KindPayload payload,
                                   SemanticValue result, OpResultType resultType,
                                   FailurePolicyId policy, SourceOrigin origin) {
            return buildOp(opId, kind, payload, result, resultType, List.of(), List.of(),
                policy, origin);
        }

        /**
         * Builds one op with completed operands and their descriptors in
         * source order plus the wired contract snapshot (I3 value ops):
         * the operand types are part of the digest — a behavior-selecting
         * field, never omitted.
         */
        private SemanticOp buildOp(OpId opId, SemanticOpKind kind, KindPayload payload,
                                   SemanticValue result, OpResultType resultType,
                                   List<ValueId> operands,
                                   List<RuntimeDescriptor> operandTypes,
                                   FailurePolicyId policy, SourceOrigin origin) {
            OperationContractSnapshot placeholder = contractOf(kind, payload, resultType,
                operandTypes, policy, "placeholder");
            String digest = ContractSnapshotCanonicalizer.digest(placeholder);
            OperationContractSnapshot contract = contractOf(kind, payload, resultType,
                operandTypes, policy, digest);
            return new SemanticOp(opId, kind, origin, result, resultType, operands,
                operandTypes, payload, policy, contract);
        }

        private OperationContractSnapshot contractOf(SemanticOpKind kind, KindPayload payload,
                                                     OpResultType resultType,
                                                     List<RuntimeDescriptor> operandTypes,
                                                     FailurePolicyId policy, String digest) {
            return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
                resultType, operandTypes,
                payload instanceof KindPayload.SelectorCarrying carrying
                    ? carrying.selector() : null,
                payload, policy, List.of(), digest);
        }

        /** Copies the checked span into the schema-owned span (D4). */
        private SourceSpan toSourceSpan(Span span) {
            return new SourceSpan(span.file(), span.startLine(), span.startColumn(),
                span.endLine(), span.endColumn(), span.startScalarOffset(),
                span.endScalarOffset());
        }

        private static String typeName(Type type) {
            return switch (type) {
                case Type.Array array -> "[" + typeName(array.element()) + "]";
                case Type.Nullable nullable -> "?" + typeName(nullable.inner());
                case Type.Class classType -> "@"
                    + DescriptorService.semanticModulePath(classType.identity())
                    + "/" + classType.name();
                case Type.Func func -> "function";
                default -> String.valueOf(type);
            };
        }

        /** The foreign-expression description of the E6005 origin. */
        private String describeExpression(ExpressionNode expr) {
            return switch (expr) {
                case deal.ast.CallExpr ignored ->
                    "call expression (only int()/number() intrinsic calls lower in this "
                        + "slice — INTRINSIC_CALL is the I3 terminal-check arm; the CALL "
                        + "machinery is E7's)";
                case deal.ast.IndexExpr ignored ->
                    "index access expression (INDEX_NORMALIZE/INDEX_READ are E5's, "
                        + "ISSUE-0234)";
                case deal.ast.FunctionExpr ignored ->
                    "function expression (CLOSURE_NEW is E6's, ISSUE-0235)";
                case deal.ast.HasExpr ignored ->
                    "has expression (HAS_FIELD is E9's, ISSUE-0238)";
                case deal.ast.AwaitExpression ignored ->
                    "await expression (ASYNC_START/AWAIT are E7's)";
                default -> expr.getClass().getSimpleName() + " expression";
            };
        }

        /** The foreign-statement description of the E6005 origin. */
        private String describeStatement(StatementNode statement) {
            return switch (statement) {
                case deal.ast.FunctionDeclaration ignored ->
                    "function declaration (CLOSURE_NEW/RECURSIVE_GROUP_INIT are E6's, "
                        + "ISSUE-0235)";
                case deal.ast.VariableDeclaration ignored ->
                    "variable declaration (BINDING_ALLOC/INIT are E6's, ISSUE-0235)";
                case deal.ast.ReturnStatement ignored ->
                    "return statement (RETURN is E7's)";
                case deal.ast.IfStatement ignored ->
                    "if statement (BRANCH(IF) is the E5 control-flow arm)";
                case deal.ast.WhileStatement ignored ->
                    "while statement (LOOP(WHILE) is the E5 control-flow arm)";
                case deal.ast.ForStatement ignored ->
                    "for statement (LOOP(FOR) is the E5 control-flow arm)";
                case deal.ast.ExpressionStatement ignored ->
                    "expression statement (DISCARD is the E5 control-flow arm)";
                case deal.ast.ImportDeclaration ignored ->
                    "import declaration (IMPORT_EXPORT_ENTRY is E10's)";
                case deal.ast.ExportDeclaration ignored ->
                    "export declaration (EXPORT_* is E10's)";
                case deal.ast.ClassDeclaration ignored ->
                    "class declaration (class layouts and CLASS_NEW are E9's)";
                case deal.ast.TryStatement ignored ->
                    "try statement (TRY_CATCH is the E5 control-flow arm)";
                case deal.ast.ThrowStatement ignored ->
                    "throw statement (THROW is the E5 control-flow arm)";
                case deal.ast.BreakStatement ignored ->
                    "break statement (matching loop-ID transfer is the E5 control-flow arm)";
                case deal.ast.ContinueStatement ignored ->
                    "continue statement (matching loop-ID transfer is the E5 control-flow arm)";
                default -> statement.getClass().getSimpleName() + " statement";
            };
        }
    }
}
