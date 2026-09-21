package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.ir.IrDumper;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.UnarySelector;
import deal.semantic.ir.ValueId;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Base64;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * Verifies the ISSUE-0287 semantic dump and ID allocation: the
 * {@link SemanticIrDumper} deterministic {@code deal.semantic-ir/1}
 * canonical-JSON dumps (unit, manifest, project) produced exclusively
 * through T3's single canonicalizer — a module dump is byte-for-byte the
 * canonicalizer's canonical JSON of the unit (the validator's pinned unit
 * text protocol; the dumper adds no reordering) — and the
 * {@link SemanticIdAllocator} contract with the pinned ID ordering
 * (dependency order, source order, semantic role, synthetic ordinal)
 * including {@link ClassFactoryId} allocation through the same contract —
 * while the existing {@code --dump-ir} surface and goldens stay
 * byte-identical.
 *
 * <p>Tests:
 * <ol>
 *   <li>Unit dump golden and shape: the rich unit's dump equals a stored
 *       byte golden; the dump equals T3's canonical JSON of the unit
 *       ({@code toJson(RawUnit.fromTyped(unit))}) byte-for-byte and
 *       equals {@link SemanticIrValidator#toUnitText} byte-for-byte (the
 *       dumper adds no reordering); the fixture ops carry T2's closed
 *       payload shapes with digests T3 fills and the profile/hashes T3's
 *       helper computes; the dump round-trips through the single
 *       canonical parser and re-validates through the validator's text
 *       surface (dump runs on validated input).</li>
 *   <li>Manifest/project shape: manifest equals a stored golden; the
 *       project dump is the manifest plus per-module dumps in dependency
 *       order; repeated project dumps are byte-identical.</li>
 *   <li>Cross-process determinism: a fresh JVM invocation recomputes the
 *       same dump bytes (byte-identical across JVM runs).</li>
 *   <li>LF-only line endings: file emission writes each canonical
 *       document terminated by exactly one LF, no CR anywhere.</li>
 *   <li>ID order: allocations follow dependency → source → role →
 *       synthetic ordinal with strictly increasing ids; out-of-order,
 *       duplicate, and unknown-module requests are rejected; a fresh
 *       allocator reproduces identical ids; {@link ClassFactoryId}
 *       values follow the pinned F2 derivation order; the dump fixture's
 *       ids equal one allocator run in the pinned order.</li>
 *   <li>Old surface: the {@code --dump-ir} output of a fixture project is
 *       byte-unchanged against the stored golden, and the
 *       {@code --dump-ir} CLI surface in {@code deal/Main.java} is
 *       untouched.</li>
 * </ol>
 */
public class SemanticIrDumperTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static final ModuleId APP = new ModuleId("app");
    private static final ModuleId LIB = new ModuleId("lib.math");

    /** The pinned capability-registry digest of the synthetic invocation. */
    private static final String REGISTRY_HASH =
        "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";

    private static final String INTERFACE_HASH =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    /** T3's helper computes the fixture's lowering-context hash (schema S1). */
    private static final String LOWERING_CONTEXT_HASH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);

    /** The comparison facts the validator's R-PROFILE recomputes against. */
    private static final SemanticIrValidator.ComparisonFacts FACTS =
        new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH, SemanticProfile.DEAL_V1_2_INT32,
            REGISTRY_HASH);

    // =========================================================================
    // Stored goldens (pinned; captured from this exact dumper once)
    // =========================================================================

    /** Stored golden: {@code dumpModuleText(richAppUnit())}. */
    private static final String PINNED_UNIT_GOLDEN = """
{"constructCoverage":[{"construct":"SCALAR_LITERAL","opKinds":["CONST"]},{"construct":"UNARY_ARITHMETIC_COMPARISON","opKinds":["UNARY","BINARY","BRANCH"]},{"construct":"STRING_CONCAT_TEMPLATE","opKinds":["STRING_CONCAT"]},{"construct":"CALL","opKinds":["CALL","CALLBACK_INVOKE","INTRINSIC_CALL","STDLIB_CALL","ASYNC_START","AWAIT"]},{"construct":"FUNCTION_DECLARATION_EXPRESSION","opKinds":["CLOSURE_NEW","RECURSIVE_GROUP_INIT","FUNCTION_ADAPT"]},{"construct":"RETURN_EXPRESSION_STATEMENT","opKinds":["RETURN","DISCARD"]},{"construct":"IMPORT_EXPORT_ENTRY","opKinds":["MODULE_INIT","MODULE_IMPORT","EXPORT_READ","EXPORT_PUBLISH","ENTRY_INVOKE"]}],"formatVersion":"deal.semantic-ir/1","functionBindings":[{"allocationId":28,"binding":{"captureMode":"SHARED_CELL","targetSignature":"(int,int)->int","type":"adapter"}}],"interfaceHash":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","loweringContextHash":"14903fa87ddfb93d6278bdcac42f20a5d7b9d4f0975cc55e695789f4e7f5ffb0","moduleId":"app","ops":[{"contract":{"canonicalDigest":"502e517f481ff2781f9903853c12bcb86d013f1ccf2b3fbe41006c6f20aff5e9","failurePolicy":"NO_DEAL_FAILURE","opKind":"MODULE_IMPORT","operandTypes":[],"payload":{"aliasCells":[],"kind":"COMPILED","rawSpecifier":"lib.math","resolvedModule":{"path":"lib.math","type":"module"}},"referencedSemanticIds":[],"resultType":null,"selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"MODULE_IMPORT","opId":{"id":14,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"aliasCells":[],"kind":"COMPILED","rawSpecifier":"lib.math","resolvedModule":{"path":"lib.math","type":"module"}},"result":null,"resultType":null},{"contract":{"canonicalDigest":"8cf835c87f7ecdfdcf168077b228723c20d8bbbb97ddb18f3e6414191db0b3fb","failurePolicy":"NO_DEAL_FAILURE","opKind":"CONST","operandTypes":[],"payload":{"value":1},"referencedSemanticIds":[],"resultType":"int","selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"CONST","opId":{"id":16,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"value":1},"result":{"id":15,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"dfecddf55204b2e9d689723eddc7f386283c8ef349f6aaeb4511504259fb204e","failurePolicy":"INT32_RESULT","opKind":"UNARY","operandTypes":["int"],"payload":{"selector":"INT32_NEG"},"referencedSemanticIds":[],"resultType":"int","selector":"INT32_NEG","version":1},"failurePolicy":"INT32_RESULT","kind":"UNARY","opId":{"id":18,"modulePath":"app","type":"op"},"operandTypes":["int"],"operands":[{"id":15,"type":"value"}],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"selector":"INT32_NEG"},"result":{"id":17,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"4f4adb1287b9736ef09f4a7e41d0856533b22d5c6d7990afaee9bbdc57b04789","failurePolicy":"INT32_RESULT","opKind":"BINARY","operandTypes":["int","int"],"payload":{"innerDescriptor":null,"selector":"INT32_ADD","side":null},"referencedSemanticIds":[],"resultType":"int","selector":"INT32_ADD","version":1},"failurePolicy":"INT32_RESULT","kind":"BINARY","opId":{"id":20,"modulePath":"app","type":"op"},"operandTypes":["int","int"],"operands":[{"id":15,"type":"value"},{"id":17,"type":"value"}],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"innerDescriptor":null,"selector":"INT32_ADD","side":null},"result":{"id":19,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"010e7099376bc2a05f7506c441d231f9f9f0d694e3495f52cc11b5d5f0bae6f0","failurePolicy":"NO_DEAL_FAILURE","opKind":"STRING_CONCAT","operandTypes":[],"payload":{"fragments":[{"id":21,"type":"value"}]},"referencedSemanticIds":[],"resultType":"string","selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"STRING_CONCAT","opId":{"id":22,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"fragments":[{"id":21,"type":"value"}]},"result":{"id":21,"type":"value"},"resultType":"string"},{"contract":{"canonicalDigest":"7620810bdca27f4b2ad29823efe4b761d501aa6e8c266727bfe6f26e92917619","failurePolicy":"TYPE_DESCRIPTOR","opKind":"BOUNDARY","operandTypes":[],"payload":{"descriptor":"int","input":{"id":19,"type":"value"},"kind":"FUNCTION_PARAMETER","realization":{"checkId":"check","type":"runtimeValidation"}},"referencedSemanticIds":[],"resultType":null,"selector":null,"version":1},"failurePolicy":"TYPE_DESCRIPTOR","kind":"BOUNDARY","opId":{"id":25,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":{"id":24,"modulePath":"app","type":"op"},"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"descriptor":"int","input":{"id":19,"type":"value"},"kind":"FUNCTION_PARAMETER","realization":{"checkId":"check","type":"runtimeValidation"}},"result":null,"resultType":null},{"contract":{"canonicalDigest":"2687981ca6eaea335b8b31ef53fca86e708bea3a4853983e8d204ecd210f2f8c","failurePolicy":"TYPE_DESCRIPTOR","opKind":"BOUNDARY","operandTypes":[],"payload":{"descriptor":"int","input":{"id":23,"type":"value"},"kind":"FUNCTION_RETURN","realization":{"checkId":"check","type":"runtimeValidation"}},"referencedSemanticIds":[],"resultType":null,"selector":null,"version":1},"failurePolicy":"TYPE_DESCRIPTOR","kind":"BOUNDARY","opId":{"id":26,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":{"id":24,"modulePath":"app","type":"op"},"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"descriptor":"int","input":{"id":23,"type":"value"},"kind":"FUNCTION_RETURN","realization":{"checkId":"check","type":"runtimeValidation"}},"result":null,"resultType":null},{"contract":{"canonicalDigest":"2b044f39bc8553955d8c2120c22e0c91b9b60450f7403faa1069630b9d6a095a","failurePolicy":"NO_DEAL_FAILURE","opKind":"CALL","operandTypes":[],"payload":{"bodyBlock":{"id":10,"type":"block"},"callee":{"binding":{"blockId":{"id":10,"type":"block"},"functionId":{"id":11,"type":"function"},"type":"loweredBody"},"type":"static"},"dynamicReturnBoundary":null,"externalEntryRef":null,"mode":"DIRECT","parameterBoundaryOpIds":[{"id":25,"modulePath":"app","type":"op"}],"returnBoundaryOpId":{"id":26,"modulePath":"app","type":"op"},"signature":"(int)->int"},"referencedSemanticIds":[],"resultType":"int","selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"CALL","opId":{"id":24,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"bodyBlock":{"id":10,"type":"block"},"callee":{"binding":{"blockId":{"id":10,"type":"block"},"functionId":{"id":11,"type":"function"},"type":"loweredBody"},"type":"static"},"dynamicReturnBoundary":null,"externalEntryRef":null,"mode":"DIRECT","parameterBoundaryOpIds":[{"id":25,"modulePath":"app","type":"op"}],"returnBoundaryOpId":{"id":26,"modulePath":"app","type":"op"},"signature":"(int)->int"},"result":{"id":23,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"68987e21e43b3d396f4529bdcf44bf38ca6a2bcf6aedd859c8895d39919d5beb","failurePolicy":"NO_DEAL_FAILURE","opKind":"RETURN","operandTypes":[],"payload":{"enclosingInvocationOpId":{"id":24,"modulePath":"app","type":"op"},"function":{"id":11,"type":"function"},"returnBoundaryOpId":{"id":26,"modulePath":"app","type":"op"},"value":{"id":23,"type":"value"}},"referencedSemanticIds":[],"resultType":null,"selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"RETURN","opId":{"id":27,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":{"id":24,"modulePath":"app","type":"op"},"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"enclosingInvocationOpId":{"id":24,"modulePath":"app","type":"op"},"function":{"id":11,"type":"function"},"returnBoundaryOpId":{"id":26,"modulePath":"app","type":"op"},"value":{"id":23,"type":"value"}},"result":null,"resultType":null},{"contract":{"canonicalDigest":"1119b6eddefc9f74821d66c4efafebac47e07bbd9eabdd222a9bb99efd5ced74","failurePolicy":"NO_DEAL_FAILURE","opKind":"FUNCTION_ADAPT","operandTypes":[],"payload":{"mode":"SHARED_CELL","proof":null,"source":{"binding":{"id":31,"type":"binding"},"generation":0,"type":"sharedCell"},"sourceSignature":"(int)->int","targetSignature":"(int,int)->int"},"referencedSemanticIds":[],"resultType":"(int,int)->int","selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"FUNCTION_ADAPT","opId":{"id":29,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"mode":"SHARED_CELL","proof":null,"source":{"binding":{"id":31,"type":"binding"},"generation":0,"type":"sharedCell"},"sourceSignature":"(int)->int","targetSignature":"(int,int)->int"},"result":{"id":28,"type":"value"},"resultType":"(int,int)->int"},{"contract":{"canonicalDigest":"8b7c8b04beb8b80af25e7fbc3ddf8928f55a116655fb60a22bf34ffd454d7de8","failurePolicy":"NO_DEAL_FAILURE","opKind":"EXPORT_PUBLISH","operandTypes":[],"payload":{"descriptor":"(int,int)->int","module":{"path":"app","type":"module"},"name":"double","value":{"id":28,"type":"value"}},"referencedSemanticIds":[],"resultType":null,"selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"EXPORT_PUBLISH","opId":{"id":30,"modulePath":"app","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"descriptor":"(int,int)->int","module":{"path":"app","type":"module"},"name":"double","value":{"id":28,"type":"value"}},"result":null,"resultType":null}],"requiredCapabilities":["FOUNDATION_VALUES","DESCRIPTORS","BOUNDARIES"],"semanticProfile":"DEAL_V1_2_INT32"}""";

    /** Stored golden: {@code dumpModuleText(libUnit())}. */
    private static final String PINNED_LIB_GOLDEN = """
{"constructCoverage":[{"construct":"SCALAR_LITERAL","opKinds":["CONST"]},{"construct":"UNARY_ARITHMETIC_COMPARISON","opKinds":["UNARY","BINARY","BRANCH"]},{"construct":"STRING_CONCAT_TEMPLATE","opKinds":["STRING_CONCAT"]}],"formatVersion":"deal.semantic-ir/1","functionBindings":[],"interfaceHash":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","loweringContextHash":"14903fa87ddfb93d6278bdcac42f20a5d7b9d4f0975cc55e695789f4e7f5ffb0","moduleId":"lib.math","ops":[{"contract":{"canonicalDigest":"5b6aba8956bd1bf1a3916ea8edcdc89a099f1b614a34d7c2035bb02692a19a97","failurePolicy":"NO_DEAL_FAILURE","opKind":"CONST","operandTypes":[],"payload":{"value":42},"referencedSemanticIds":[],"resultType":"int","selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"CONST","opId":{"id":2,"modulePath":"lib.math","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"value":42},"result":{"id":1,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"dfecddf55204b2e9d689723eddc7f386283c8ef349f6aaeb4511504259fb204e","failurePolicy":"INT32_RESULT","opKind":"UNARY","operandTypes":["int"],"payload":{"selector":"INT32_NEG"},"referencedSemanticIds":[],"resultType":"int","selector":"INT32_NEG","version":1},"failurePolicy":"INT32_RESULT","kind":"UNARY","opId":{"id":4,"modulePath":"lib.math","type":"op"},"operandTypes":["int"],"operands":[{"id":1,"type":"value"}],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"selector":"INT32_NEG"},"result":{"id":3,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"4f4adb1287b9736ef09f4a7e41d0856533b22d5c6d7990afaee9bbdc57b04789","failurePolicy":"INT32_RESULT","opKind":"BINARY","operandTypes":["int","int"],"payload":{"innerDescriptor":null,"selector":"INT32_ADD","side":null},"referencedSemanticIds":[],"resultType":"int","selector":"INT32_ADD","version":1},"failurePolicy":"INT32_RESULT","kind":"BINARY","opId":{"id":6,"modulePath":"lib.math","type":"op"},"operandTypes":["int","int"],"operands":[{"id":1,"type":"value"},{"id":3,"type":"value"}],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"innerDescriptor":null,"selector":"INT32_ADD","side":null},"result":{"id":5,"type":"value"},"resultType":"int"},{"contract":{"canonicalDigest":"49380670909c49fac7289b5fa67b63ff0d0aacb8f47c5d4b37ccd02513045ba4","failurePolicy":"NO_DEAL_FAILURE","opKind":"STRING_CONCAT","operandTypes":[],"payload":{"fragments":[{"id":7,"type":"value"}]},"referencedSemanticIds":[],"resultType":"string","selector":null,"version":1},"failurePolicy":"NO_DEAL_FAILURE","kind":"STRING_CONCAT","opId":{"id":8,"modulePath":"lib.math","type":"op"},"operandTypes":[],"operands":[],"origin":{"anchorId":{"id":0,"type":"anchor"},"kind":"SYNTHETIC","parentOpId":null,"sourceId":"semantic-ir","span":{"endColumn":1,"endLine":1,"endScalarOffset":-1,"file":"semantic-ir","startColumn":1,"startLine":1,"startScalarOffset":-1}},"payload":{"fragments":[{"id":7,"type":"value"}]},"result":{"id":7,"type":"value"},"resultType":"string"}],"requiredCapabilities":["FOUNDATION_VALUES"],"semanticProfile":"DEAL_V1_2_INT32"}""";

    /** Stored golden: {@code dumpManifestText(richProject())}. */
    private static final String PINNED_MANIFEST_GOLDEN = """
{"entryModule":"app","formatVersion":"deal.semantic-ir/1","modules":["lib.math","app"],"semanticProfile":"DEAL_V1_2_INT32"}""";

    // =========================================================================
    // Shared descriptors
    // =========================================================================

    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor.Func SIG_I_TO_I =
        new RuntimeDescriptor.Func(List.of(INT), INT);
    private static final RuntimeDescriptor.Func SIG_II_TO_I =
        new RuntimeDescriptor.Func(List.of(INT, INT), INT);
    private static final RuntimeDescriptor.Func MAIN_SIGNATURE =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);

    // =========================================================================
    // Fixtures (ids equal one SemanticIdAllocator run in the pinned order)
    // =========================================================================

    // The pinned allocation sequence over [lib.math, app]:
    //   (lib.math,0,BLOCK,0)   -> LIB_INIT_BLOCK = BlockId(0)
    //   (lib.math,1,VALUE,0)   -> LIB_CONST_VALUE = ValueId(1)
    //   (lib.math,1,OP,0)      -> LIB_CONST_OP = OpId(lib.math, 2)
    //   (lib.math,2,VALUE,0)   -> LIB_NEG_VALUE = ValueId(3)
    //   (lib.math,2,OP,0)      -> LIB_UNARY_OP = OpId(lib.math, 4)
    //   (lib.math,3,VALUE,0)   -> LIB_ADD_VALUE = ValueId(5)
    //   (lib.math,3,OP,0)      -> LIB_BINARY_OP = OpId(lib.math, 6)
    //   (lib.math,4,VALUE,0)   -> LIB_CONCAT_VALUE = ValueId(7)
    //   (lib.math,4,OP,0)      -> LIB_CONCAT_OP = OpId(lib.math, 8)
    //   (app,0,BLOCK,0)        -> APP_INIT_BLOCK = BlockId(9)
    //   (app,1,BLOCK,0)        -> INC_BODY = BlockId(10)
    //   (app,1,FUNCTION,0)     -> INC_FUNCTION = FunctionId(11)
    //   (app,2,BLOCK,0)        -> MAIN_BODY = BlockId(12)
    //   (app,2,FUNCTION,0)     -> MAIN_FUNCTION = FunctionId(13)
    //   (app,3,OP,0)           -> IMPORT_OP = OpId(app, 14)
    //   (app,4,VALUE,0)        -> CONST_VALUE = ValueId(15)
    //   (app,4,OP,0)           -> CONST_OP = OpId(app, 16)
    //   (app,5,VALUE,0)        -> NEG_VALUE = ValueId(17)
    //   (app,5,OP,0)           -> UNARY_OP = OpId(app, 18)
    //   (app,6,VALUE,0)        -> ADD_VALUE = ValueId(19)
    //   (app,6,OP,0)           -> BINARY_OP = OpId(app, 20)
    //   (app,7,VALUE,0)        -> CONCAT_VALUE = ValueId(21)
    //   (app,7,OP,0)           -> CONCAT_OP = OpId(app, 22)
    //   (app,8,VALUE,0)        -> CALL_RESULT = ValueId(23)
    //   (app,8,OP,0)           -> CALL_OP = OpId(app, 24)
    //   (app,9,OP,0)           -> PARAM_BOUNDARY_OP = OpId(app, 25)
    //   (app,10,OP,0)          -> RETURN_BOUNDARY_OP = OpId(app, 26)
    //   (app,11,OP,0)          -> RETURN_OP = OpId(app, 27)
    //   (app,12,VALUE,0)       -> ADAPT_VALUE = ValueId(28)
    //   (app,12,OP,0)          -> ADAPT_OP = OpId(app, 29)
    //   (app,13,OP,0)          -> PUBLISH_OP = OpId(app, 30)
    //   (app,14,BINDING,0)     -> ADAPT_CELL_BINDING = BindingId(31)
    private static final BlockId LIB_INIT_BLOCK = new BlockId(0);
    private static final ValueId LIB_CONST_VALUE = new ValueId(1);
    private static final OpId LIB_CONST_OP = new OpId(LIB, 2);
    private static final ValueId LIB_NEG_VALUE = new ValueId(3);
    private static final OpId LIB_UNARY_OP = new OpId(LIB, 4);
    private static final ValueId LIB_ADD_VALUE = new ValueId(5);
    private static final OpId LIB_BINARY_OP = new OpId(LIB, 6);
    private static final ValueId LIB_CONCAT_VALUE = new ValueId(7);
    private static final OpId LIB_CONCAT_OP = new OpId(LIB, 8);
    private static final BlockId APP_INIT_BLOCK = new BlockId(9);
    private static final BlockId INC_BODY = new BlockId(10);
    private static final FunctionId INC_FUNCTION = new FunctionId(11);
    private static final BlockId MAIN_BODY = new BlockId(12);
    private static final FunctionId MAIN_FUNCTION = new FunctionId(13);
    private static final OpId IMPORT_OP = new OpId(APP, 14);
    private static final ValueId CONST_VALUE = new ValueId(15);
    private static final OpId CONST_OP = new OpId(APP, 16);
    private static final ValueId NEG_VALUE = new ValueId(17);
    private static final OpId UNARY_OP = new OpId(APP, 18);
    private static final ValueId ADD_VALUE = new ValueId(19);
    private static final OpId BINARY_OP = new OpId(APP, 20);
    private static final ValueId CONCAT_VALUE = new ValueId(21);
    private static final OpId CONCAT_OP = new OpId(APP, 22);
    private static final ValueId CALL_RESULT = new ValueId(23);
    private static final OpId CALL_OP = new OpId(APP, 24);
    private static final OpId PARAM_BOUNDARY_OP = new OpId(APP, 25);
    private static final OpId RETURN_BOUNDARY_OP = new OpId(APP, 26);
    private static final OpId RETURN_OP = new OpId(APP, 27);
    private static final ValueId ADAPT_VALUE = new ValueId(28);
    private static final OpId ADAPT_OP = new OpId(APP, 29);
    private static final OpId PUBLISH_OP = new OpId(APP, 30);
    private static final BindingId ADAPT_CELL_BINDING = new BindingId(31);

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin("test.deal", SourceSpan.synthetic("test.deal"),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    /** T3 fills the contract digest: placeholder, recompute, carry. */
    private static OperationContractSnapshot contractFor(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        deal.semantic.ir.ClosedSelector selector =
            payload instanceof KindPayload.SelectorCarrying carrying
                ? carrying.selector() : null;
        return new deal.semantic.ir.OperationContractSnapshot(
            deal.semantic.ir.OperationContractSnapshot.VERSION, kind, resultType, operandTypes,
            selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, List<ValueId> operands,
            List<RuntimeDescriptor> operandTypes, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, operandTypes, policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, operandTypes, policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, operands,
            operandTypes, payload, policy, contract);
    }

    /** The app module: T2 payload shapes (CONST/UNARY/BINARY/BOUNDARY/CALL/RETURN/FUNCTION_ADAPT/MODULE_IMPORT/EXPORT_PUBLISH) with T3-filled digests. */
    static LoweredModuleUnit richAppUnit() {
        EnumMap<ConstructKind, List<SemanticOpKind>> coverage = new EnumMap<>(ConstructKind.class);
        coverage.put(ConstructKind.SCALAR_LITERAL, ConstructKind.SCALAR_LITERAL.mappedOpKinds());
        coverage.put(ConstructKind.STRING_CONCAT_TEMPLATE,
            ConstructKind.STRING_CONCAT_TEMPLATE.mappedOpKinds());
        coverage.put(ConstructKind.UNARY_ARITHMETIC_COMPARISON,
            ConstructKind.UNARY_ARITHMETIC_COMPARISON.mappedOpKinds());
        coverage.put(ConstructKind.CALL, ConstructKind.CALL.mappedOpKinds());
        coverage.put(ConstructKind.RETURN_EXPRESSION_STATEMENT,
            ConstructKind.RETURN_EXPRESSION_STATEMENT.mappedOpKinds());
        coverage.put(ConstructKind.FUNCTION_DECLARATION_EXPRESSION,
            ConstructKind.FUNCTION_DECLARATION_EXPRESSION.mappedOpKinds());
        coverage.put(ConstructKind.IMPORT_EXPORT_ENTRY,
            ConstructKind.IMPORT_EXPORT_ENTRY.mappedOpKinds());

        List<SemanticOp> ops = new ArrayList<>();
        ops.add(opWith(IMPORT_OP, SemanticOpKind.MODULE_IMPORT,
            new KindPayload.ModuleImportPayload("lib.math", LIB, ModuleImportKind.COMPILED),
            null, null, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(CONST_OP, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            CONST_VALUE, INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(UNARY_OP, SemanticOpKind.UNARY,
            new KindPayload.UnaryPayload(UnarySelector.INT32_NEG),
            NEG_VALUE, INT, List.of(CONST_VALUE), List.of(INT),
            FailurePolicyId.INT32_RESULT, null));
        ops.add(opWith(BINARY_OP, SemanticOpKind.BINARY,
            new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
            ADD_VALUE, INT, List.of(CONST_VALUE, NEG_VALUE), List.of(INT, INT),
            FailurePolicyId.INT32_RESULT, null));
        ops.add(opWith(CONCAT_OP, SemanticOpKind.STRING_CONCAT,
            new KindPayload.StringConcatPayload(List.of(CONCAT_VALUE)),
            CONCAT_VALUE, RuntimeDescriptor.String.INSTANCE, List.of(), List.of(),
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(PARAM_BOUNDARY_OP, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_PARAMETER, INT, ADD_VALUE,
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, List.of(), List.of(), FailurePolicyId.TYPE_DESCRIPTOR, CALL_OP));
        ops.add(opWith(RETURN_BOUNDARY_OP, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_RETURN, INT, CALL_RESULT,
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, List.of(), List.of(), FailurePolicyId.TYPE_DESCRIPTOR, CALL_OP));
        ops.add(opWith(CALL_OP, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.DIRECT,
                new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                    INC_FUNCTION, INC_BODY)),
                SIG_I_TO_I, List.of(PARAM_BOUNDARY_OP), RETURN_BOUNDARY_OP, null,
                INC_BODY, null),
            CALL_RESULT, INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(RETURN_OP, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(CALL_RESULT, INC_FUNCTION, CALL_OP,
                RETURN_BOUNDARY_OP),
            null, null, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, CALL_OP));
        ops.add(opWith(ADAPT_OP, SemanticOpKind.FUNCTION_ADAPT,
            new KindPayload.FunctionAdaptPayload(SIG_I_TO_I, SIG_II_TO_I,
                CaptureMode.SHARED_CELL,
                new AdaptSourceRef.SharedCell(ADAPT_CELL_BINDING, 0), null),
            ADAPT_VALUE, SIG_II_TO_I, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            null));
        ops.add(opWith(PUBLISH_OP, SemanticOpKind.EXPORT_PUBLISH,
            new KindPayload.ExportPublishPayload(APP, "double", SIG_II_TO_I, ADAPT_VALUE),
            null, null, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null));

        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings = Map.of(
            new FunctionAllocationIdentity(ADAPT_VALUE.id()),
            new FunctionExecutionBinding.AdapterBinding(ADAPT_OP, CaptureMode.SHARED_CELL,
                new AdaptSourceRef.SharedCell(ADAPT_CELL_BINDING, 0), SIG_I_TO_I, SIG_II_TO_I));

        return new LoweredModuleUnit(
            LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32,
            APP,
            INTERFACE_HASH,
            LOWERING_CONTEXT_HASH,
            EnumSet.of(SemanticCapability.FOUNDATION_VALUES, SemanticCapability.DESCRIPTORS,
                SemanticCapability.BOUNDARIES),
            coverage,
            Map.of(),
            Map.of(
                INC_FUNCTION, new LoweredFunction(INC_FUNCTION, SIG_I_TO_I, List.of(), INC_BODY),
                MAIN_FUNCTION, new LoweredFunction(MAIN_FUNCTION, MAIN_SIGNATURE, List.of(),
                    MAIN_BODY)),
            new ModuleInitPlan(List.of(LIB), APP_INIT_BLOCK),
            new ExportPlan(List.of(
                new ExportPlan.ExportPlanEntry("main", MAIN_SIGNATURE, PUBLISH_OP))),
            bindings,
            ops);
    }

    /**
     * The lib.math module: the four FOUNDATION_VALUES evidence ops
     * (CONST/UNARY/BINARY/STRING_CONCAT) with their coverage rows.
     */
    static LoweredModuleUnit libUnit() {
        EnumMap<ConstructKind, List<SemanticOpKind>> coverage = new EnumMap<>(ConstructKind.class);
        coverage.put(ConstructKind.SCALAR_LITERAL, ConstructKind.SCALAR_LITERAL.mappedOpKinds());
        coverage.put(ConstructKind.STRING_CONCAT_TEMPLATE,
            ConstructKind.STRING_CONCAT_TEMPLATE.mappedOpKinds());
        coverage.put(ConstructKind.UNARY_ARITHMETIC_COMPARISON,
            ConstructKind.UNARY_ARITHMETIC_COMPARISON.mappedOpKinds());
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(opWith(LIB_CONST_OP, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(42)),
            LIB_CONST_VALUE, INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(LIB_UNARY_OP, SemanticOpKind.UNARY,
            new KindPayload.UnaryPayload(UnarySelector.INT32_NEG),
            LIB_NEG_VALUE, INT, List.of(LIB_CONST_VALUE), List.of(INT),
            FailurePolicyId.INT32_RESULT, null));
        ops.add(opWith(LIB_BINARY_OP, SemanticOpKind.BINARY,
            new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
            LIB_ADD_VALUE, INT, List.of(LIB_CONST_VALUE, LIB_NEG_VALUE), List.of(INT, INT),
            FailurePolicyId.INT32_RESULT, null));
        ops.add(opWith(LIB_CONCAT_OP, SemanticOpKind.STRING_CONCAT,
            new KindPayload.StringConcatPayload(List.of(LIB_CONCAT_VALUE)),
            LIB_CONCAT_VALUE, RuntimeDescriptor.String.INSTANCE, List.of(), List.of(),
            FailurePolicyId.NO_DEAL_FAILURE, null));
        return new LoweredModuleUnit(
            LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32,
            LIB,
            INTERFACE_HASH,
            LOWERING_CONTEXT_HASH,
            EnumSet.of(SemanticCapability.FOUNDATION_VALUES),
            coverage,
            Map.of(),
            Map.of(),
            new ModuleInitPlan(List.of(), LIB_INIT_BLOCK),
            ExportPlan.empty(),
            Map.of(),
            ops);
    }

    static ExecutableLoweredProject richProject() {
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        modules.put(LIB, libUnit());
        modules.put(APP, richAppUnit());
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, Map.of(
                LIB, new ExternalModuleInterface(LIB, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES),
                APP, new ExternalModuleInterface(APP, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)));
        return new ExecutableLoweredProject(SemanticProfile.DEAL_V1_2_INT32, index, modules, APP);
    }

    // =========================================================================
    // 1. Unit dump golden and shape
    // =========================================================================

    static void testUnitDumpGoldenAndShape() {
        System.out.println("-- Unit dump golden and shape --");

        LoweredModuleUnit unit = richAppUnit();
        String text = SemanticIrDumper.dumpModuleText(unit);
        check(PINNED_UNIT_GOLDEN.equals(text),
            "the rich unit dump matches the stored canonical JSON golden byte-for-byte");
        check(!text.contains("\r") && !text.contains("\n"),
            "the canonical unit document is single-line (no CR, no embedded LF)");
        check(text.startsWith("{\"constructCoverage\":"),
            "the object keys render in sorted order (first key constructCoverage); got "
                + text.substring(0, 40));

        // The dump is produced exclusively through T3's single canonicalizer:
        // byte-for-byte the canonicalizer's canonical JSON of the unit (the
        // dumper adds no reordering), and byte-for-byte the validator's
        // pinned unit text protocol.
        byte[] viaCanonicalizer = ContractSnapshotCanonicalizer.serializeJson(
            ContractSnapshotCanonicalizer.toJson(RawUnit.fromTyped(unit)));
        check(java.util.Arrays.equals(SemanticIrDumper.dumpModule(unit), viaCanonicalizer),
            "the unit dump equals T3's canonical JSON of the unit byte-for-byte "
                + "(the dumper adds no reordering)");
        check(SemanticIrValidator.toUnitText(unit).equals(text),
            "the unit dump equals the validator's pinned unit text protocol byte-for-byte");
        check(SemanticIrDumper.toJson(unit).equals(
                ContractSnapshotCanonicalizer.toJson(RawUnit.fromTyped(unit))),
            "the dumper's unit mapping is exactly the canonicalizer's single unit mapping");

        // The canonical parser round-trips the dump byte-exactly.
        byte[] bytes = SemanticIrDumper.dumpModule(unit);
        byte[] reserialized = CanonicalJson.serializeBytes(CanonicalJson.parse(bytes));
        check(java.util.Arrays.equals(bytes, reserialized),
            "the unit dump round-trips through the single canonical parser byte-exactly");

        // RuntimeDescriptor/enum spellings come from T2's closed definitions
        // through the canonicalizer's shared mappings; the stored golden pins
        // them (a broken T2 or T3 serializer breaks the dump goldens).
        check(text.contains("\"moduleId\":\"app\""),
            "the module identity renders as the plain module path of the text protocol");
        check(text.contains("\"formatVersion\":\"deal.semantic-ir/1\""),
            "the format version is pinned to deal.semantic-ir/1");
        check(text.contains("\"semanticProfile\":\"DEAL_V1_2_INT32\""),
            "the profile spelling is the closed enum name");
        check(text.contains("\"loweringContextHash\":\"" + LOWERING_CONTEXT_HASH + "\""),
            "the dump carries the helper-computed lowering-context hash verbatim");
        check(LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH)
                .equals(richAppUnit().loweringContextHash()),
            "the fixture unit's loweringContextHash equals T3's pinned helper output");
        check(text.contains("\"requiredCapabilities\":[\"FOUNDATION_VALUES\",\"DESCRIPTORS\","
                + "\"BOUNDARIES\"]"),
            "requiredCapabilities render in SemanticCapability declaration order");
        check(text.contains("\"construct\":\"SCALAR_LITERAL\"")
                && text.contains("\"construct\":\"CALL\""),
            "constructCoverage renders T2's closed construct names");
        check(text.contains("\"resultType\":\"int\""),
            "descriptors render with T2's canonical spec text (int)");
        check(text.contains("\"targetSignature\":\"(int,int)->int\""),
            "function descriptors render with T2's canonical spec text ((int,int)->int)");
        check(text.contains("\"captureMode\":\"SHARED_CELL\""),
            "closed capture-mode enums render as their names");
        check(text.contains("\"mode\":\"DIRECT\""),
            "closed call-mode enums render as their names");

        // The fixture ops carry digests T3 fills: every contract digest
        // recomputes to itself (R-DIGEST would pass on every op).
        for (SemanticOp op : unit.ops()) {
            check(ContractSnapshotCanonicalizer.digest(op.contract())
                    .equals(op.contract().canonicalDigest()),
                "op " + op.opId() + " (" + op.kind() + ") carries a T3-computed digest");
        }

        // The dump runs on validated input: the typed fixture passes the
        // closed validator and the dumped text re-validates through the
        // validator's text surface.
        Optional<deal.diagnostics.CompilerDiagnostic> typed =
            SemanticIrValidator.validate(unit, FACTS);
        check(typed.isEmpty(), "the fixture unit passes the closed validator on the typed surface"
            + (typed.isPresent() ? ": " + typed.get().message() : ""));
        Optional<deal.diagnostics.CompilerDiagnostic> textValidation =
            SemanticIrValidator.validateText(text, FACTS);
        check(textValidation.isEmpty(),
            "the dumped unit text re-validates through the validator's text surface"
                + (textValidation.isPresent() ? ": " + textValidation.get().message() : ""));

        // Repeat dumps are byte-identical.
        check(java.util.Arrays.equals(bytes, SemanticIrDumper.dumpModule(unit)),
            "repeated unit dumps are byte-identical");
    }

    // =========================================================================
    // 2. Manifest and project dump shape
    // =========================================================================

    static void testManifestAndProjectShape() {
        System.out.println("-- Manifest and project dump shape --");

        ExecutableLoweredProject project = richProject();
        String manifest = SemanticIrDumper.dumpManifestText(project);
        check(PINNED_MANIFEST_GOLDEN.equals(manifest),
            "the project manifest matches the stored canonical JSON golden byte-for-byte");
        check(manifest.startsWith("{\"entryModule\":"),
            "the manifest keys render in sorted order (first key entryModule)");

        String libText = SemanticIrDumper.dumpModuleText(libUnit());
        check(PINNED_LIB_GOLDEN.equals(libText),
            "the lib module dump matches the stored canonical JSON golden byte-for-byte");

        SemanticIrDumper.ProjectDump dump = SemanticIrDumper.dumpProject(project);
        check(java.util.Arrays.equals(SemanticIrDumper.dumpManifest(project), dump.manifest()),
            "the project dump carries exactly the manifest bytes");
        check(dump.modules().size() == 2, "the project dump carries one module dump per module");
        check(dump.modules().get(0).moduleId().equals(LIB)
                && dump.modules().get(1).moduleId().equals(APP),
            "the module dumps are in dependency order (lib.math before app)");
        check(java.util.Arrays.equals(SemanticIrDumper.dumpModule(libUnit()),
                dump.modules().get(0).bytes()),
            "the lib module dump equals dumpModule(libUnit) byte-for-byte");
        check(java.util.Arrays.equals(SemanticIrDumper.dumpModule(richAppUnit()),
                dump.modules().get(1).bytes()),
            "the app module dump equals dumpModule(richAppUnit) byte-for-byte");

        SemanticIrDumper.ProjectDump again = SemanticIrDumper.dumpProject(project);
        check(java.util.Arrays.equals(dump.manifest(), again.manifest()),
            "repeated project dumps produce byte-identical manifests");
        check(dump.modules().get(0).text().equals(again.modules().get(0).text())
                && dump.modules().get(1).text().equals(again.modules().get(1).text()),
            "repeated project dumps produce byte-identical module dumps");

        // The whole project passes the closed validator (the pipeline
        // contract: T12 passes T6-validated units).
        Optional<deal.diagnostics.CompilerDiagnostic> projectValidation =
            SemanticIrValidator.validate(project, FACTS);
        check(projectValidation.isEmpty(),
            "the fixture project passes the closed validator on the typed surface"
                + (projectValidation.isPresent() ? ": " + projectValidation.get().message() : ""));
    }

    // =========================================================================
    // 3. Cross-process determinism (fresh JVM)
    // =========================================================================

    static void testCrossProcessDeterminism() {
        System.out.println("-- Cross-process determinism (fresh JVM recompute) --");

        ExecutableLoweredProject project = richProject();
        try {
            Process process = new ProcessBuilder(
                "java", "-cp", "build", "deal.test.SemanticIrDumperTest", "--emit")
                .redirectErrorStream(true)
                .start();
            process.getOutputStream().close();
            BufferedReader reader = new BufferedReader(
                new InputStreamReader(process.getInputStream(), StandardCharsets.UTF_8));
            List<String> lines = new ArrayList<>();
            String line;
            while ((line = reader.readLine()) != null) {
                lines.add(line);
            }
            boolean finished = process.waitFor(60, TimeUnit.SECONDS);
            check(finished && process.exitValue() == 0,
                "the fresh JVM emit subprocess exits 0");

            String manifestLine = lines.stream()
                .filter(l -> l.startsWith("EMIT_MANIFEST:")).findFirst().orElse("");
            byte[] subManifest = Base64.getDecoder()
                .decode(manifestLine.substring("EMIT_MANIFEST:".length()));
            check(java.util.Arrays.equals(SemanticIrDumper.dumpManifest(project), subManifest),
                "the manifest bytes are byte-equal across processes");

            Map<String, byte[]> subModules = new LinkedHashMap<>();
            for (String l : lines) {
                if (l.startsWith("EMIT_MODULE:")) {
                    String rest = l.substring("EMIT_MODULE:".length());
                    int colon = rest.indexOf(':');
                    subModules.put(rest.substring(0, colon),
                        Base64.getDecoder().decode(rest.substring(colon + 1)));
                }
            }
            check(subModules.keySet().equals(
                    new LinkedHashSet<>(List.of("lib.math", "app"))),
                "the fresh JVM emits one module dump per module");
            check(java.util.Arrays.equals(SemanticIrDumper.dumpModule(libUnit()),
                    subModules.get("lib.math")),
                "the lib module bytes are byte-equal across processes");
            check(java.util.Arrays.equals(SemanticIrDumper.dumpModule(richAppUnit()),
                    subModules.get("app")),
                "the app module bytes are byte-equal across processes");
        } catch (Exception e) {
            fail("cross-process determinism check failed: " + e);
        }
    }

    // =========================================================================
    // 4. LF-only line endings
    // =========================================================================

    static void assertLfOnly(byte[] content, byte[] canonicalBytes, String what) {
        check(content.length == canonicalBytes.length + 1,
            what + " is the canonical document plus exactly one terminating LF");
        if (content.length != canonicalBytes.length + 1) {
            return;
        }
        check(content[content.length - 1] == '\n',
            what + " terminates with a single LF");
        int newlines = 0;
        for (byte b : content) {
            if (b == '\n') { newlines++; }
            if (b == '\r') { fail(what + " contains a CR (LF-only line endings required)"); return; }
        }
        check(newlines == 1, what + " contains exactly one LF (the terminator); got " + newlines);
        byte[] body = java.util.Arrays.copyOf(content, content.length - 1);
        check(java.util.Arrays.equals(canonicalBytes, body),
            what + " carries the exact canonical document bytes");
    }

    static void testLfOnlyLineEndings() {
        System.out.println("-- LF-only line endings (file emission) --");

        ExecutableLoweredProject project = richProject();
        try {
            Path dir = Files.createTempDirectory("semantic-ir-dump-lf");
            Path moduleFile = dir.resolve("module.json");
            SemanticIrDumper.dumpModuleTo(moduleFile, richAppUnit());
            assertLfOnly(Files.readAllBytes(moduleFile), SemanticIrDumper.dumpModule(richAppUnit()),
                "dumpModuleTo output");

            SemanticIrDumper.dumpProjectTo(dir, project);
            Path manifestFile = dir.resolve(SemanticIrDumper.MANIFEST_FILE_NAME);
            check(Files.exists(manifestFile), "the project directory carries the pinned manifest file");
            assertLfOnly(Files.readAllBytes(manifestFile),
                SemanticIrDumper.dumpManifest(project), "project manifest file");

            Path modulesDir = dir.resolve(SemanticIrDumper.MODULES_DIR_NAME);
            check(Files.isDirectory(modulesDir), "the project directory carries the pinned modules dir");
            try (var stream = Files.list(modulesDir)) {
                List<String> names = stream.map(p -> p.getFileName().toString()).sorted().toList();
                check(names.equals(List.of("app.json", "lib.math.json")),
                    "one pinned module file per module (module path + .json); got " + names);
            }
            assertLfOnly(Files.readAllBytes(modulesDir.resolve("app.json")),
                SemanticIrDumper.dumpModule(richAppUnit()), "app module file");
            assertLfOnly(Files.readAllBytes(modulesDir.resolve("lib.math.json")),
                SemanticIrDumper.dumpModule(libUnit()), "lib module file");

            // The module file-name derivation stays inside the closed dotted form.
            try {
                SemanticIrDumper.moduleFileName(new ModuleId("../escape"));
                fail("a module path outside the closed dotted form is not accepted");
            } catch (IllegalArgumentException expected) {
                check(true, "path-traversal-shaped module paths are rejected by the file-name derivation");
            }
        } catch (Exception e) {
            fail("LF endings test failed: " + e);
        }
    }

    // =========================================================================
    // 5. ID allocation order
    // =========================================================================

    static void testIdAllocationOrder() {
        System.out.println("-- SemanticIdAllocator: pinned ID ordering --");

        // In-order allocations produce strictly increasing ids across the
        // dependency-ordered modules.
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(LIB, APP));
        long previous = -1;
        List<Long> ids = new ArrayList<>();
        ids.add(allocator.nextBlockId(LIB, 0, 0).id());
        ids.add(allocator.nextValueId(LIB, 1, 0).id());
        ids.add(allocator.nextOpId(LIB, 1, 0).id());
        ids.add(allocator.nextValueId(LIB, 2, 0).id());
        ids.add(allocator.nextOpId(LIB, 2, 0).id());
        ids.add(allocator.nextValueId(LIB, 3, 0).id());
        ids.add(allocator.nextOpId(LIB, 3, 0).id());
        ids.add(allocator.nextValueId(LIB, 4, 0).id());
        ids.add(allocator.nextOpId(LIB, 4, 0).id());
        ids.add(allocator.nextBlockId(APP, 0, 0).id());
        ids.add(allocator.nextBlockId(APP, 1, 0).id());
        ids.add(allocator.nextFunctionId(APP, 1, 0).id());
        ids.add(allocator.nextBlockId(APP, 2, 0).id());
        ids.add(allocator.nextFunctionId(APP, 2, 0).id());
        OpId importOp = allocator.nextOpId(APP, 3, 0);
        ids.add(importOp.id());
        ids.add(allocator.nextValueId(APP, 4, 0).id());
        ids.add(allocator.nextOpId(APP, 4, 0).id());
        ids.add(allocator.nextValueId(APP, 5, 0).id());
        ids.add(allocator.nextOpId(APP, 5, 0).id());
        ids.add(allocator.nextValueId(APP, 6, 0).id());
        ids.add(allocator.nextOpId(APP, 6, 0).id());
        ids.add(allocator.nextValueId(APP, 7, 0).id());
        ids.add(allocator.nextOpId(APP, 7, 0).id());
        ids.add(allocator.nextValueId(APP, 8, 0).id());
        OpId callOp = allocator.nextOpId(APP, 8, 0);
        ids.add(callOp.id());
        ids.add(allocator.nextOpId(APP, 9, 0).id());
        ids.add(allocator.nextOpId(APP, 10, 0).id());
        ids.add(allocator.nextOpId(APP, 11, 0).id());
        ids.add(allocator.nextValueId(APP, 12, 0).id());
        ids.add(allocator.nextOpId(APP, 12, 0).id());
        ids.add(allocator.nextOpId(APP, 13, 0).id());
        ids.add(allocator.nextBindingId(APP, 14, 0).id());
        for (long id : ids) {
            check(id == previous + 1, "in-order allocation yields the next id (" + id
                + " after " + previous + ")");
            previous = id;
        }
        check(importOp.module().equals(APP) && callOp.module().equals(APP),
            "allocated OpIds carry their allocating module tag");

        // Out-of-order requests are producer defects, never reordered.
        SemanticIdAllocator order = SemanticIdAllocator.over(List.of(LIB, APP));
        order.nextBlockId(LIB, 0, 0);
        order.nextBlockId(APP, 0, 0);
        expectOutOfOrder(() -> order.nextBlockId(LIB, 1, 0),
            "an allocation for an earlier dependency-ordered module is rejected");
        order.nextFunctionId(APP, 5, 0);
        expectOutOfOrder(() -> order.nextBlockId(APP, 4, 0),
            "a lower source ordinal after a higher one is rejected");
        expectOutOfOrder(() -> order.nextFunctionId(APP, 5, 0),
            "a repeated coordinate key is rejected");
        SemanticIdAllocator roles = SemanticIdAllocator.over(List.of(APP));
        roles.nextBlockId(APP, 0, 0);
        roles.nextFunctionId(APP, 0, 0);
        expectOutOfOrder(() -> roles.nextBlockId(APP, 0, 0),
            "a lower semantic role at the same source ordinal is rejected");
        roles.nextBindingId(APP, 0, 5);
        expectOutOfOrder(() -> roles.nextBindingId(APP, 0, 3),
            "a lower synthetic ordinal at equal coordinates is rejected");
        try {
            order.nextBlockId(new ModuleId("unknown"), 0, 0);
            fail("an unknown module must not allocate");
        } catch (IllegalArgumentException expected) {
            check(true, "an unknown module is rejected by the allocator");
        }

        // Determinism: a fresh allocator with the same sequence reproduces
        // the identical ids — the dump fixture's ids equal exactly one
        // allocator run in the pinned order.
        SemanticIdAllocator replay = SemanticIdAllocator.over(List.of(LIB, APP));
        check(replay.nextBlockId(LIB, 0, 0).equals(LIB_INIT_BLOCK)
                && replay.nextValueId(LIB, 1, 0).equals(LIB_CONST_VALUE)
                && replay.nextOpId(LIB, 1, 0).equals(LIB_CONST_OP)
                && replay.nextValueId(LIB, 2, 0).equals(LIB_NEG_VALUE)
                && replay.nextOpId(LIB, 2, 0).equals(LIB_UNARY_OP)
                && replay.nextValueId(LIB, 3, 0).equals(LIB_ADD_VALUE)
                && replay.nextOpId(LIB, 3, 0).equals(LIB_BINARY_OP)
                && replay.nextValueId(LIB, 4, 0).equals(LIB_CONCAT_VALUE)
                && replay.nextOpId(LIB, 4, 0).equals(LIB_CONCAT_OP)
                && replay.nextBlockId(APP, 0, 0).equals(APP_INIT_BLOCK)
                && replay.nextBlockId(APP, 1, 0).equals(INC_BODY)
                && replay.nextFunctionId(APP, 1, 0).equals(INC_FUNCTION)
                && replay.nextBlockId(APP, 2, 0).equals(MAIN_BODY)
                && replay.nextFunctionId(APP, 2, 0).equals(MAIN_FUNCTION)
                && replay.nextOpId(APP, 3, 0).equals(IMPORT_OP)
                && replay.nextValueId(APP, 4, 0).equals(CONST_VALUE)
                && replay.nextOpId(APP, 4, 0).equals(CONST_OP)
                && replay.nextValueId(APP, 5, 0).equals(NEG_VALUE)
                && replay.nextOpId(APP, 5, 0).equals(UNARY_OP)
                && replay.nextValueId(APP, 6, 0).equals(ADD_VALUE)
                && replay.nextOpId(APP, 6, 0).equals(BINARY_OP)
                && replay.nextValueId(APP, 7, 0).equals(CONCAT_VALUE)
                && replay.nextOpId(APP, 7, 0).equals(CONCAT_OP)
                && replay.nextValueId(APP, 8, 0).equals(CALL_RESULT)
                && replay.nextOpId(APP, 8, 0).equals(CALL_OP)
                && replay.nextOpId(APP, 9, 0).equals(PARAM_BOUNDARY_OP)
                && replay.nextOpId(APP, 10, 0).equals(RETURN_BOUNDARY_OP)
                && replay.nextOpId(APP, 11, 0).equals(RETURN_OP)
                && replay.nextValueId(APP, 12, 0).equals(ADAPT_VALUE)
                && replay.nextOpId(APP, 12, 0).equals(ADAPT_OP)
                && replay.nextOpId(APP, 13, 0).equals(PUBLISH_OP)
                && replay.nextBindingId(APP, 14, 0).equals(ADAPT_CELL_BINDING),
            "a fresh allocator reproduces the identical ids for the identical pinned sequence "
                + "(the dump fixture's ids equal one allocator run)");

        // ClassFactoryId follows the pinned F2 derivation order: dependency
        // order, exported classes in declaration (source) order, role
        // CLASS_FACTORY, synthetic ordinal 0 — allocatable through the same
        // contract T8's index-build allocation consumes.
        SemanticIdAllocator factories = SemanticIdAllocator.over(List.of(LIB, APP));
        factories.nextBlockId(LIB, 0, 0);
        ClassFactoryId libFactory = factories.nextClassFactoryId(LIB, 0, 0);
        ClassFactoryId appFirst = factories.nextClassFactoryId(APP, 0, 0);
        ClassFactoryId appSecond = factories.nextClassFactoryId(APP, 1, 0);
        check(libFactory.id() < appFirst.id() && appFirst.id() < appSecond.id(),
            "ClassFactoryIds follow dependency order then declaration (source) order; got "
                + libFactory + ", " + appFirst + ", " + appSecond);

        // Uniqueness across a longer sequence.
        SemanticIdAllocator unique = SemanticIdAllocator.over(List.of(LIB, APP));
        Set<Long> seen = new HashSet<>();
        for (long source = 0; source < 20; source++) {
            seen.add(unique.nextBlockId(LIB, source, 0).id());
            seen.add(unique.nextValueId(LIB, source, 0).id());
            seen.add(unique.nextTokenId(LIB, source, 0));
        }
        for (long source = 0; source < 20; source++) {
            seen.add(unique.nextAnchorId(APP, source, 0).id());
            seen.add(unique.nextOpId(APP, source, 0).id());
        }
        check(seen.size() == 100, "every allocated id is unique within the project (100/100)");
    }

    private static void expectOutOfOrder(Runnable action, String message) {
        try {
            action.run();
            fail(message + " (no exception thrown)");
        } catch (IllegalStateException expected) {
            check(true, message + " (IllegalStateException: " + expected.getMessage() + ")");
        }
    }

    // =========================================================================
    // 6. Old --dump-ir surface unchanged
    // =========================================================================

    static void testOldIrSurfaceByteUnchanged() {
        System.out.println("-- Old --dump-ir surface unchanged --");

        try {
            Path fixture = Path.of("test/ir-goldens/fixtures/literals.deal");
            String source = Files.readString(fixture);
            String filename = fixture.toString();
            LexResult lex = new Lexer(source, filename).tokenize();
            if (lex.hasErrors()) {
                fail("the literals fixture failed to lex: " + lex.diagnostics());
                return;
            }
            Parser parser = new Parser(lex.tokens(), filename, lex.directiveEvents());
            ParseResult parseResult = parser.parse();
            if (parseResult.hasErrors()) {
                fail("the literals fixture failed to parse: " + parseResult.diagnostics());
                return;
            }
            ProgramNode program = parseResult.program();
            NameResolver nr = new NameResolver(filename, new StubModuleResolver());
            SymbolTable symbolTable = nr.resolve(program);
            CheckResult result = TypeChecker.check(filename, symbolTable, nr, program);
            if (result.hasErrors()) {
                fail("the literals fixture failed to type-check: " + result.diagnostics());
                return;
            }
            String ir = IrDumper.dump(program, result, filename);
            String golden = Files.readString(Path.of("test/ir-goldens/literals.ir.txt"));
            check(ir.equals(golden),
                "the --dump-ir output of the literals fixture is byte-unchanged against the "
                    + "stored golden");
        } catch (Exception e) {
            fail("old-surface test failed: " + e);
        }

        try {
            String mainSource = Files.readString(Path.of("deal/Main.java"));
            check(mainSource.contains("--dump-ir") && mainSource.contains("case \"--dump-ir\""),
                "the --dump-ir CLI flag surface in deal/Main.java is untouched");
        } catch (Exception e) {
            fail("the --dump-ir surface check failed: " + e);
        }
    }

    // =========================================================================
    // Emit / goldens modes (test-only subprocess surfaces)
    // =========================================================================

    static void emitForCrossProcess() {
        ExecutableLoweredProject project = richProject();
        System.out.println("EMIT_MANIFEST:"
            + Base64.getEncoder().encodeToString(SemanticIrDumper.dumpManifest(project)));
        for (SemanticIrDumper.ModuleDump dump : SemanticIrDumper.dumpProject(project).modules()) {
            System.out.println("EMIT_MODULE:" + dump.moduleId().path() + ":"
                + Base64.getEncoder().encodeToString(dump.bytes()));
        }
    }

    static void printGoldens() {
        System.out.println("UNIT_GOLDEN_BEGIN");
        System.out.println(SemanticIrDumper.dumpModuleText(richAppUnit()));
        System.out.println("UNIT_GOLDEN_END");
        System.out.println("LIB_GOLDEN_BEGIN");
        System.out.println(SemanticIrDumper.dumpModuleText(libUnit()));
        System.out.println("LIB_GOLDEN_END");
        System.out.println("MANIFEST_GOLDEN_BEGIN");
        System.out.println(SemanticIrDumper.dumpManifestText(richProject()));
        System.out.println("MANIFEST_GOLDEN_END");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        if (args.length == 1 && "--emit".equals(args[0])) {
            emitForCrossProcess();
            return;
        }
        if (args.length == 1 && "--goldens".equals(args[0])) {
            printGoldens();
            return;
        }
        System.out.println("=== Running Semantic IR Dumper / ID Allocator Tests (ISSUE-0287) ===");

        testUnitDumpGoldenAndShape();
        testManifestAndProjectShape();
        testCrossProcessDeterminism();
        testLfOnlyLineEndings();
        testIdAllocationOrder();
        testOldIrSurfaceByteUnchanged();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
