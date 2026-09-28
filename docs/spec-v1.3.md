# DEAL — Language Specification v1.3

DEAL (Directly Embeddable Agentic Language) is a statically, fully invariant typed language with TypeScript syntax and runtime-enforced types. The primary target is safe, embeddable AI scripting with explicit interoperability boundaries. This document defines the feature set, type system, runtime execution model, and a basis test suite in both valid and invalid code.

Features not described in this specification do not exist in the language.

---

## Lexical elements

- Identifiers: `[a-zA-Z_$][a-zA-Z0-9_$]*`
  - User-declared identifiers must not contain `$`.
  - Compiler-generated identifiers may contain `$`.
  - Generated identifiers are source-visible only when this specification defines them, such as `C$fromJson` and `C$toJson`.
  - A user declaration, import alias, parameter, field, or local variable containing `$` is a compile-time error.
- Keywords: `let`, `class`, `function`, `async`, `await`, `return`, `if`, `else`, `while`, `for`, `break`, `continue`, `null`, `true`, `false`, `import`, `export`, `from`, `delete`, `has`, `try`, `catch`, `throw`, `of`
  - `async` and `await` are keywords. They cannot be used as identifiers, type names, field names, import aliases, or parameter names.
  - `async` is a function/type marker and does not participate in name resolution.
  - `await` is expression syntax and does not participate in name resolution.
- Literals:
 - `null`
 - boolean: `true`, `false`
 - integer: decimal digits (e.g., `123`)
 - number: decimal digits with `.` or exponent (e.g., `3.14`, `0.0`, `1e308`, `1.0e-3`)
  - string: `"..."` and `'...'` with `\n`, `\t`, `\\`, `\"`, `\'`
  - template literal: `` `...${expr}...` ``
- Operators:
 - `+ - * / %`
 - `=== !== < <= > >=`
 - `&& || !`
 - `=` (assignment)
 - `.` (member access)
 - `[]` (index access)
 - `,` (separator)
 - `|` (nullable union)
 - `?` (optional field modifier)
 - `;` (statement terminator)
- Punctuation: `{ } ( ) [ ] : ; , =>`
- Comments: `// ... end-of-line`, `/* ... */`

### Comment semantics

Line terminators are LF (`\n`), CRLF (`\r\n`), and CR (`\r`).

- `//` comments extend to end-of-line (line-ending character consumed, not emitted).
- `/* */` comments do **not** nest. `/* /* */` ends at the first `*/`.
- Comments are equivalent to whitespace except recognized compiler directive comments.
- A compiler directive comment is a line comment matching `CompilerDirectiveComment` in the lexical grammar.
- A compiler directive comment with an unrecognized directive name is a compile-time error.
- `// @deal-version VERSION` and `// @extern-c` are file directives. `// @deal-version` must occur before the first non-comment token. `// @extern-c` must occur after any leading imports and before the first declaration in a C FFI declaration file. Each file directive may occur at most once.
- `// @jsonable`, `// @c-struct`, and `// @c-pointer` are declaration directives. A declaration directive block is the maximal contiguous sequence of declaration directive comments and whitespace immediately before a declaration, with no intervening non-comment token or non-directive comment. The block attaches to that declaration.
- Attaching a declaration directive to an incompatible declaration is a compile-time error.
- Only `// @deal-version` accepts an argument, which must be exactly one non-empty version value after trimming surrounding horizontal whitespace. Every other recognized directive must have no argument other than horizontal whitespace.

### String escapes and Unicode

| Escape | Meaning |
|---|---|
| `\n` | newline (U+000A) |
| `\t` | tab (U+0009) |
| `\\` | backslash (U+005C) |
| `\"` | double quote (U+0022) |
| `\'` | single quote (U+0027) |

No octal, hexadecimal, or Unicode escape sequences. A DEAL `string` is a sequence of Unicode scalar values. Source string literals decode to scalar values. Backends may store strings in any representation, but observable string behavior is defined over scalar values. String values accepted from untrusted or backend-native boundaries must reject invalid encodings, including malformed UTF-8 byte sequences and unpaired UTF-16 surrogate code units.

### Template literals

Template literals use backtick syntax with `${expression}` interpolation:

```ts
let name: string = "Ada";
let msg: string = `Hello ${name}!`; // "Hello Ada!"
```

The expression inside `${}` must have type `string`. No implicit string conversion.

```ts
let n: int = 42;
let bad: string = `Value: ${n}`; // error: int is not string
```

Template literals nest inside `for` loops and other expressions:

```ts
let xs: string[] = ["a", "b", "c"];
let s: string = `Items: ${xs[0]}, ${xs[1]}`;
```

### Numeric overflow, NaN, and Infinity

- `int` is a signed 32-bit exact integer type with range `[-2147483648, 2147483647]`; integer literals outside this range are compile-time errors.
 - The decimal token `2147483648` is permitted only as the immediate operand of unary `-`, producing the `int` value `-2147483648`. In every other expression or literal context, `2147483648` is a compile-time error.
 - Division `a / b` on two `int` values returns `int` and uses integer division rounded toward zero: `5 / 2 === 2`, `-5 / 2 === -2`.
 - Division-by-zero of an `int` is a **runtime error**.
 - Remainder `a % b` uses truncated division.
 - All `int` arithmetic (`+ - * / %`) checks the signed 32-bit range and raises a runtime error on overflow.
 - `-0` is normalized to `0` in `int` checks and arithmetic. Negative zero does not exist in `int`.
 - Runtime check: `int(x)` rejects `NaN`, `Infinity`, non-integer values, and values outside the signed 32-bit range.

- `number` is a 64-bit IEEE 754 double.
 - `NaN`, `Infinity`, `-Infinity` are representable values. `NaN` is not equal to itself (`x === x` is false).
 - Division returns `number` only when both operands are `number`.
 - Division by zero of a `number` produces `Infinity` or `NaN`, not a runtime error.
 - `number` comparisons follow IEEE 754:
   - `NaN === NaN` is `false`.
   - `NaN !== NaN` is `true`.
   - Relational operators `<`, `>`, `<=`, `>=` return `false` when either operand is `NaN`.

### Lexical grammar (normative)

```antlr
SourceCharacter ::= /* any Unicode scalar value */

Token ::= Keyword | Identifier | Literal | Operator | Punctuator

Keyword ::= 'let' | 'class' | 'function' | 'async' | 'await' | 'return' | 'if' | 'else'
          | 'while' | 'for' | 'break' | 'continue'
 | 'null' | 'true' | 'false'
          | 'import' | 'export' | 'from' | 'delete' | 'has'
          | 'try' | 'catch' | 'throw' | 'of'

Identifier ::= [a-zA-Z_$] [a-zA-Z0-9_$]*

Literal ::= NullLiteral | BooleanLiteral | IntLiteral | NumberLiteral | StringLiteral | TemplateLiteral

NullLiteral ::= 'null'
BooleanLiteral ::= 'true' | 'false'
IntLiteral ::= [0-9]+
NumberLiteral ::= ([0-9]* '.' [0-9]+ ([eE] [+-]? [0-9]+)?)
 | ([0-9]+ [eE] [+-]? [0-9]+)
StringLiteral ::= '"' StringCharacter* '"' | '\'' StringCharacter* '\''

TemplateLiteral ::= '`' (TemplateText | '${' Expression '}')* '`'
TemplateText ::= /* one or more characters containing no line terminator, '`', or '${' */

StringCharacter ::= /* any SourceCharacter except line terminators and unescaped quote */
 | '\n' | '\t' | '\\' | '\"' | '\''

CompilerDirectiveComment ::= '//' [ \t]* '@' DirectiveName DirectiveArgument? LineTerminator?

DirectiveName ::= 'deal-version' | 'jsonable' | 'extern-c' | 'c-struct' | 'c-pointer'

DirectiveArgument ::= [^\r\n]*

LineTerminator ::= '\n' | '\r\n' | '\r'

Operator ::= '+' | '-' | '*' | '/' | '%'
 | '===' | '!==' | '<' | '<=' | '>' | '>='
 | '&&' | '||' | '!' | '=' | '.' | '=>' | '|'

Punctuator ::= '{' | '}' | '(' | ')' | '[' | ']' | ':' | ';' | ',' | '?'
```

### Syntactic grammar (normative)

This grammar defines the statement/expression separation, block semantics, assignment targets, table key syntax, function-call expression form, and operator precedence.

```antlr
Program ::= ImportDeclaration* TopLevelDeclaration*

TopLevelDeclaration ::= FunctionDeclaration
                      | ClassDeclaration
                      | ExportDeclaration

Statement       ::= ClassDeclaration
                   | FunctionDeclaration
                   | VariableDeclaration
                   | ReturnStatement
                   | IfStatement
                   | WhileStatement
                   | ForStatement
                   | ForOfStatement
                   | BreakStatement
                   | ContinueStatement
                   | ExpressionStatement
                   | DeleteStatement
                   | TryStatement
                   | ThrowStatement
                   | Block

Block ::= '{' Statement* '}'

ClassDeclaration ::= 'class' Identifier '{' ClassField* '}'

ClassField ::= Identifier '?'? ':' Type ('=' Expression)? ';'

FunctionDeclaration ::= 'async'? 'function' Identifier '(' ParameterList? ')' ':' Type Block

ExternalFunctionDeclaration ::= 'function' Identifier '(' ParameterList? ')' ':' Type ';' /* declaration files only */

ParameterList ::= Parameter (',' Parameter)*

Parameter ::= Identifier ':' Type

ReturnType ::= ':' Type

VariableDeclaration ::= 'let' Identifier TypeAnnotation? '=' Expression ';'

TypeAnnotation ::= ':' Type

ExpressionStatement ::= Expression ';'

ReturnStatement ::= 'return' Expression? ';'

IfStatement ::= 'if' '(' Expression ')' Block ('else' (IfStatement | Block))?

WhileStatement ::= 'while' '(' Expression ')' Block

ForStatement    ::= 'for' '(' ForInit? ';' Expression? ';' ForUpdate? ')' Block

ForOfStatement  ::= 'for' '(' 'let' Identifier ':' Type 'of' Expression ')' Block

ForInit ::= 'let' Identifier TypeAnnotation? '=' Expression | ForUpdate

ForUpdate ::= LeftHandSideExpression '=' AssignmentExpression

BreakStatement ::= 'break' ';'

ContinueStatement ::= 'continue' ';'

DeleteStatement ::= 'delete' DeleteTarget ';'

DeleteTarget    ::= PostfixExpression '.' Identifier
                  | PostfixExpression '[' Expression ']'

TryStatement    ::= 'try' Block 'catch' '(' Identifier ')' Block

ThrowStatement  ::= 'throw' Expression ';'

ImportDeclaration ::= 'import' '*' 'as' Identifier 'from' StringLiteral ';'

ExportDeclaration ::= ImplementationExport

ImplementationExport ::= 'export' (FunctionDeclaration | ClassDeclaration)

DeclarationExport ::= 'export' (ExternalFunctionDeclaration | ClassDeclaration)

/* Expressions — precedence groups (highest to lowest):
 * 1. Primary (literal, identifier, parenthesized expression)
 * 2. Member / Index / Call
 * 3. Unary
 * 4. Multiplicative
 * 5. Additive
 * 6. Relational
 * 7. Equality
 * 8. Logical AND
 * 9. Logical OR
 */

Expression ::= AssignmentExpression

AssignmentExpression ::= LogicalOrExpression
 | LeftHandSideExpression '=' AssignmentExpression

LogicalOrExpression ::= LogicalAndExpression ('||' LogicalAndExpression)*

LogicalAndExpression ::= EqualityExpression ('&&' EqualityExpression)*

EqualityExpression ::= RelationalExpression (('===' | '!==') RelationalExpression)?

RelationalExpression ::= AdditiveExpression (('<' | '<=' | '>' | '>=') AdditiveExpression)?

AdditiveExpression ::= MultiplicativeExpression (('+' | '-') MultiplicativeExpression)*

MultiplicativeExpression ::= UnaryExpression (('*' | '/' | '%') UnaryExpression)*

UnaryExpression ::= ('!' | '-') UnaryExpression
                  | AwaitExpression
                  | PostfixExpression

AwaitExpression ::= 'await' PostfixExpression

PostfixExpression ::= PrimaryExpression PostfixPart*

PostfixPart ::= '.' Identifier
 | '[' Expression ']'
 | Arguments

Arguments ::= '(' ArgumentList? ')'

ArgumentList ::= Expression (',' Expression)*

PrimaryExpression ::= NullLiteral
 | BooleanLiteral
 | IntLiteral
 | NumberLiteral
  | StringLiteral
  | TemplateLiteral
  | Identifier
 | '(' Expression ')'
 | ArrayLiteral
 | ObjectLiteral
 | FunctionExpression
 | HasExpression

HasExpression ::= 'has' '(' PostfixExpression '.' Identifier ')'

ArrayLiteral ::= '[' ElementList? ']'

ElementList ::= Expression (',' Expression)* ','?

ObjectLiteral ::= '{' PropertyList? '}'

PropertyList ::= Property (',' Property)* ','?

Property ::= Identifier ':' Expression

FunctionExpression ::= 'async'? 'function' '(' ParameterList? ')' ':' Type Block

LeftHandSideExpression ::= Identifier
 | PostfixExpression
```

### Operator precedence table

| Precedence | Operator | Associativity |
|---|---|---|
| 1 | `.` `[]` `()` | left |
| 2 | `!` `-` (unary) | right |
| 3 | `*` `/` `%` | left |
| 4 | `+` `-` (binary) | left |
| 5 | `<` `<=` `>` `>=` | none |
| 6 | `===` `!==` | none |
| 7 | `&&` | left |
| 8 | `\|\|` | left |

### Semicolon rules

Every statement ends with a semicolon `;`.

### Statement/expression separation

- A module consists of zero or more `ImportDeclaration`s followed by zero or more `TopLevelDeclaration`s. `ImportDeclaration` is not allowed after any non-import top-level declaration.
- At module top level, only `ImportDeclaration`, `FunctionDeclaration`, `ClassDeclaration`, and `ExportDeclaration` are allowed. Everything else is a compile-time error.
- `Statement` remains the grammar for block/function bodies; imports and exports are not statements.
- `if`, `while`, `for` bodies must be blocks `{ ... }`. No statement-without-brace forms.
- `ExpressionStatement` is a bare expression (including function calls) followed by a required semicolon.
- `Block` is a statement-list and is not an expression. Blocks do not produce values.

Semantics:

- An `if` without `else` evaluates the condition; if true the branch executes.
- A `while` loop evaluates the condition before each iteration.
- A C-style `for` loop syntactic form desugars into block-local scope plus a while loop equivalent.
- `break` exits the nearest enclosing loop.
- `continue` proceeds to the next iteration of the nearest enclosing loop.
- `return` in function body immediately transfers control to the caller. `return` with no expression is valid only for `null` return type.

### Assignment targets

Only these are valid LHS targets for `=`:

```ts
identifier // simple variable
a.b // member access
a[b] // index into array
```

No destructuring, no property shorthand mutation for class destructuring.

Assignment to member/index of an array and table respectively:

```ts
xs[0] = 5; // array element write — runtime element-type check
t.key = "value"; // table field write — no runtime type check
```

---

## Type system

### Type algebra (canonical forms)

```txt
Type :=
 null
 boolean
 int
 number
  string
  bytes
  table
  Error
  ClassName // nominal record type
 Array<Type> // surface: T[]
 Nullable<Type> // surface: T | null
 Function(sync, params, return)
 Function(async, params, return)
```

No other union types exist. `Nullable` is the sole union constructor.

### Type grammar (normative)

```antlr
Type ::= FunctionType | NullableType

NullableType ::= ArrayType ('|' 'null')?
 | 'null' '|' ArrayType

ArrayType ::= PrimaryType ('[' ']')*

PrimaryType ::= BuiltinType
 | Identifier
 | Identifier '.' Identifier
 | '(' FunctionType ')'

BuiltinType ::= 'null' | 'boolean' | 'int' | 'number' | 'string' | 'bytes' | 'table' | 'Error'

FunctionType ::= 'async'? '(' FunctionTypeParams? ')' '=>' Type

FunctionTypeParams ::= FunctionTypeParam (',' FunctionTypeParam)*

FunctionTypeParam ::= Identifier ':' Type
```

Constraints:

- `T | null` and `null | T` canonicalize to `Nullable<T>`.
- General unions such as `A | B` are invalid.
- `null | null`, `(T | null) | null`, and `T | null | null` are invalid.
- Identifier in a type context must not be a keyword.
- `Error` is a builtin nominal class type. User code must not declare a class named `Error`.

### Surface syntax

```ts
null
boolean
int
number
string
bytes
table
Error

T[] // array of T
T[][] // array of array of T

T | null // nullable wrapper; T must not be null or Nullable<U>
null | T // equivalent

(p1: T1, ..., pN: TN) => R
async (p1: T1, ..., pN: TN) => R

ClassName // nominal record
```

### Nullable semantics

`Nullable<T>` is a distinct type constructor with restricted assignment.

Assignment rules:

```txt
T -> T OK
null -> null OK
T -> T | null OK (wrapping)
null -> T | null OK
T | null -> T error (must narrow)
T | null -> T | null OK (same T)
T | null -> U | null error (different T)
```

Supports basic null flow narrowing:

```ts
let n: int | null = 1;

if (n !== null) {
 let i: int = n; // OK: narrowed to int in this block
}

if (n === null) {
 // n is null here
} else {
 let i: int = n; // OK: narrowed to int in else block
}
```

Narrowing is supported only for local variables and parameters with direct comparisons `x !== null` and `x === null`. No property-path narrowing.

Outside a narrowing block:

```ts
let i: int = n; // compile-time Error
```

Narrowing invalidation:

- Assigning to a narrowed variable invalidates its narrowed type after the assignment.
- Passing a narrowed variable to a function does not invalidate it because primitives/classes are references but the variable binding itself is unchanged.
- Property-path narrowing is not supported, so aliasing of object fields does not affect narrowing.
- Narrowing does not cross function boundaries or loop back-edges.
- Narrowing is invalidated after an `await` expression. After `await`, all narrowed variables in the enclosing async function revert to their declared types.

```ts
let x: string | null = "a";
if (x !== null) {
 let a: string = x; // OK
 x = null;
 let b: string = x; // Error
}
```

### Invariance

All type constructors are invariant. No subtyping:

- `int` is not assignable to `number` and vice versa.
- `bytes` is only assignable to `bytes`.
- `Array<int>` is not assignable to `Array<number>` and vice versa.
- `Nullable<int>` is not assignable to `Nullable<number>` and vice versa.
- `ClassName` is only assignable from itself.
- Function types must match **exactly**, including the async marker (with limited arity extension, see [Function type compatibility](#function-type-compatibility)).
- `async (...) => R` is not assignable to `(...) => R`, and `(...) => R` is not assignable to `async (...) => R`.

### Explicit conversions

Compiler-provided conversion functions:

```ts
int(x: number): int
int(x: int | null): int

number(x: int): number
number(x: number | null): number

bytes(length: int): bytes
```

Numeric conversions fail at runtime when the value is out of representable range or null. `bytes(length)` allocates a zero-filled DEAL-owned byte buffer and raises a runtime error if `length < 0`.

### Equality and comparison operand rules

Type equality:

Two types are equal iff their canonical forms are identical. Class types are equal by declared class symbol only. Function types are equal by exact async marker, parameter list, and return type.

Value equality: `===` and `!==` are valid only when operand types are equal. Exception: `T | null` may be compared with `null`.

No implicit numeric, string, bytes, boolean, class, function, array, or table cross-type equality exists. `==` and `!=` are not valid operators.

```ts
let a: int = 1;
let b: int = 2;
let ok: boolean = a === b;

let n: int | null = null;
let isNull: boolean = n === null;

let bad: boolean = 1 === 1.0; // error: int and number differ
```

Relational operators `< <= > >=` are valid only for:

```txt
int vs int
number vs number
string vs string
```

`number` comparisons follow IEEE 754 semantics. `NaN` makes relational comparisons false.

### Type-of-expression rules

String concatenation uses `+`. Both operands must be `string`. No implicit string conversions exist.

| Expression | Type |
|---|---|
| `null` | `null` |
| `true`, `false` | `boolean` |
| `123` | `int` |
| `1.5` | `number` |
| `"abc"` | `string` |
| `` `a${x}b` `` | `string` |
| `(e)` | same type as `e` |
| variable declared `let x: T` | `T` |
| `a + b` where both `int` | `int` |
| `a + b` where both `number` | `number` |
| `a + b` where both `string` | `string` (concatenation; no implicit conversions) |
| any other `+` | error |
| `a - b *` | both operands must match type exactly; `int` op `int` returns `int`, `number` op `number` returns `number` |
| `a % b` where both `int` | `int`, truncated remainder |
| `a / b` where both `int` | `int`, integer division rounded toward zero |
| `a / b` where both `number` | `number`, IEEE division |
| `=== !==` | result is `boolean` |
| `< <= > >=` | result is `boolean` |
| `&&` | both must be `boolean`, result `boolean` |
| `\|\|` | both must be `boolean`, result `boolean` |
| `!a` | `a` must be `boolean`, result `boolean` |
| `-a` where `a: int` | `int` |
| `-a` where `a: number` | `number` |
| any other unary `-` | error |
| array literal `[e1, ..., eN]` | `T[]` where all `e_i` have the same `T` |
| table literal `{ p: e, ... }` | `table` |
| class body `{ ... }` with target `ClassName` | `ClassName` (contextual) |
| `bytes(n)` where `n: int` | `bytes` |
| index `a[b]` where `a: T[]`, `b: int` | `T` |
| index `b[i]` where `b: bytes`, `i: int` | `int` byte value in `0..255` |
| member `a.p` where `a: table` | **error** unless the surrounding context provides a target type |
| member `a.p` where `a: ClassName` | required field: declared field type; optional field `p?: T`: `T \| null`; optional nullable field `p?: T \| null`: `T \| null` |
| call `f(e1, ..., eN)` where `f: (p1: T1, ..., pN: TN) => R` | `R` |
| `await f(e1, ..., eN)` where `f: async (p1: T1, ..., pN: TN) => R` | `R` |
| `e.code` where `e: Error` | `string` |
| `e.message` where `e: Error` | `string` |

### Assignment type checking

```txt
let x: T_target = expr;
```

1. Infer type of `expr` → `T_expr`
2. If `T_expr` equals `T_target` exactly → OK
3. If `T_target` is `Nullable<T>` and `T_expr` equals `T` → OK
4. If `T_target` is `Nullable<T>` and `T_expr` equals `null` → OK
5. Otherwise → compile-time Error

---

## Classes

### Class declaration

`class` declares a **nominal record type** — a sealed data shape with no inheritance, no methods, no constructors.

```ts
class User {
 id: int = 0;
 name: string = "";
 nick?: string;
 bio: string | null = null;
 active: boolean = true;
}
```

Field forms:

```txt
f: T = expr required-present, defaulted
f?: T optional, may be missing
f?: T | null optional, may be missing, present as T, or present as null
f: T | null = expr required-present, nullable, defaulted
```

The field `f: T` without a default is **not valid**. A required-present field must provide a default value expression.

### JSON serialization (`@jsonable`)

The `@jsonable` directive generates serialization functions for an `export class`:

```ts
// @jsonable
export class User {
  name: string = "";
  nick?: string;
  bio: string | null = null;
}
```

**Jsonable field types.** A `// @jsonable` class may contain fields of:

- `null`
- `boolean`
- `int`
- `number`
- `string`
- `table`
- `T[]` where `T` is jsonable
- `T | null` where `T` is jsonable
- class type `C` only if `C` has generated or declared JSON functions visible to the compiler

A type is jsonable if it is one of the primitive JSON-compatible types above, or a class type with visible `C$fromJson` and `C$toJson` functions.

If any field type is not jsonable, the compiler emits a compile-time error at the field declaration.

Circular dependencies between `@jsonable` classes are compile-time errors. This includes dependencies through `T[]` and `T | null`.

In declaration files, `// @jsonable` has no effect. Declaration files may explicitly declare compatible `C$fromJson` and `C$toJson` functions.

**Generated functions.** For a `@jsonable` class `C`, the compiler emits two module-level export functions:

```ts
C$fromJson(s: string): C | null
C$toJson(v: C): string
```

The `$` sigil is reserved for compiler-generated names (see Lexical elements).

**fromJson.** Parses the JSON string. Validates each key against declared class fields. Applies defaults for omitted required-present fields. Treats missing optional keys as absent. Rejects extra keys. Returns `null` on parse or validation failure. No throw.

**toJson.** Serializes each declared field to its JSON representation. Omits missing optional fields. Preserves `null` for nullable fields.

For a `table` field, `fromJson` accepts only a JSON object and maps it to a DEAL table as untyped JSON-shaped data. `toJson` accepts only finite acyclic JSON-shaped table values: string-keyed objects, arrays, and `null`/`boolean`/`int`/`number`/`string` leaves. Otherwise, it raises `Error`.

**Optional-nullable roundtrip.** The three states of `field?: T | null` are preserved exactly:

| State | fromJson input | toJson output |
|---|---|---|
| missing | key absent | key omitted |
| present, null | `"field": null` | `"field": null` |
| present, value | `"field": value` | `"field": value` |

**Usage:**

```ts
import * as models from "./models/user";

let u: models.User | null = models.User$fromJson("{\"name\":\"Ada\"}");

if (u !== null) {
  let s: string = models.User$toJson(u);
}
```

### Nominal typing

Classes are nominal. Two identically-shaped classes are distinct types:

```ts
class A { x: int = 0; }
class B { x: int = 0; }

let a: A = { x: 1 }; // OK
let b: B = a; // Error
let c: B = { x: 1 }; // OK
```

### Construction

Classes are initialized with **object literals** in a typed context. There is no `new` operator.

```ts
let u: User = {
 id: 1,
 name: "Ada",
 bio: null,
};
```

Omitted fields with defaults receive the default value:

```ts
let u: User = { name: "Ada" };
// equivalent to: { id: 0, name: "Ada", bio: null, active: true }
```

Default evaluation semantics:

- Defaults are evaluated per construction, not once at class declaration time.
- Mutable default arrays, tables, and nested class objects are freshly constructed for every instance.
- Defaults are deep-constructed according to their typed literal structure.
- Runtime values returned by function calls used as defaults are not deep-copied; the call is re-executed per construction.

```ts
class Bag {
 items: string[] = [];
}

let a: Bag = {};
let b: Bag = {};
a.items[0] = "x";
let n: int = b.items.length; // 0, arrays are not shared
```

Optional fields may be omitted:

```ts
let u: User = { name: "Ada", nick: "ads" };
let v: User = { name: "Ada" }; // nick missing
```

Extra fields are rejected in all cases:

```ts
let bad: User = { name: "Ada", unknown: 1 }; // Error
```

This applies to object literals, nested object literals, arrays of class literals, and runtime class checks at typed boundaries.

### Field access

Reading a required-present field yields the field type:

```ts
let n: string = u.name; // OK
```

Reading an optional field yields `T | null`. If the field is missing, the direct read produces language `null`. This keeps optional-field use null-safe while still allowing presence checks when the caller must distinguish missing from explicit JSON null.

```ts
let nick: string | null = u.nick; // OK
let nick2: string = u.nick; // error: string | null is not string
```

Optional nullable corner case:

```ts
class Profile {
 nick?: string | null;
}
```

Semantics for `nick?: string | null`:

```txt
missing -> direct read returns null, has(obj.nick) is false
present null -> direct read returns null, has(obj.nick) is true
present str -> direct read returns string, has(obj.nick) is true
```

The language provides a compiler intrinsic:

```ts
has(obj.field): boolean
```

The argument must syntactically be a class field access. The field must be a declared optional field. This avoids source-level literal-string types while keeping the field name compile-time checked.

`has(obj.field)` tests field presence only. It does not narrow the static type of `obj.field`.

```ts
class Profile {
 nick?: string | null;
}

let p: Profile = { nick: null };

if (has(p.nick)) {
 let a: string | null = p.nick; // OK
 let b: string = p.nick; // error: present field may still be null
}
```

### Nested classes and `class[]`

```ts
class Address {
 city: string = "";
 zip: int = 0;
}

class User {
 name: string = "";
 address: Address = {};
 tags: string[] = [];
 friends: User[] = [];
}
```

The nested default `{}` is contextually typed as `Address`, so its fields receive their own defaults.

Nested initialization follows target context:

```ts
let u: User = {
 name: "Ada",
 address: {
 city: "London",
 zip: 12345,
 },
 tags: ["admin", "beta"],
 friends: [],
};
```

Array of classes:

```ts
let users: User[] = [
 { name: "Ada", address: { city: "A" } },
 { name: "Bob", address: { city: "B" } },
];
```

When an array literal is contextually typed as `C[]` where `C` is a class type, each object-literal element is contextually typed as `C`.

```ts
let users2: User[] = [
 { name: "Ada" }, // OK: contextually User
];

let users3 = [
 { name: "Ada" }, // error: no array target type gives this object literal a class type
];
```

Empty arrays require type annotation:

```ts
let empty: User[] = [];
```

### Class vs table

`class` and `table` are **invariant and distinct**. No implicit conversion.

```ts
let u: User = { name: "Ada" };
let t: table = {}; 
t = u; // Error
u = t; // Error
```

### Class assignment semantics

Assignment to a class field is allowed only for declared fields:

```ts
u.name = "Bob"; // OK
u.unknown = 1; // Error
```

Required-present fields cannot be deleted:

```ts
delete u.name; // Error
```

Optional fields can be deleted, which makes them missing:

```ts
delete u.nick; // OK if nick is optional
```

Assignment to optional fields:

```ts
u.nick = "Ada"; // OK for nick?: string
u.nick = null; // error for nick?: string
```

Assignment to optional nullable fields:

```ts
u.nick = "Ada"; // OK for nick?: string | null
u.nick = null; // OK for nick?: string | null
```

After deleting an optional field, a subsequent assignment makes it present again:

```ts
class User {
 nick?: string;
}

let u: User = {};
let a: boolean = has(u.nick); // false

u.nick = "Ada";
let b: boolean = has(u.nick); // true

delete u.nick;
let c: boolean = has(u.nick); // false

u.nick = "Bob";
let d: boolean = has(u.nick); // true
```

Extra fields are rejected in object literals, nested object literals, arrays of class literals, and runtime typed boundaries.

---

## Functions

### Function declaration

```ts
function name(p1: T1, ..., pN: TN): R {
 body
 return expr;
}
```

- Parameter types required.
- Return type required.
- Return type may be `T`, `T | null`, or `null` (for no-return).
- No optional parameters.
- No nullable shorthand on parameter types; use explicit `T | null` on the parameter.

### Return type requirements

- Every `return` expression must have type `R`.
- The function body must not “fall off” without a return.
- A function with return type `null` must return `null`.

```ts
function f(): null { // ok
 return null;
}

function findName(): string | null { // ok: returns null or string
 if (true) {
 return "Ada";
 }
 return null;
}
```

### Function type compatibility

A function value `f_actual` with type `A (p1: T1, ..., pM: TM) => R` is assignable to a target of type `B (p1: T1, ..., pN: TN) => R` **if and only if**:

- Async markers are identical: `A` equals `B`, where each marker is either absent or `async`
- Return types are identical (including nullable wrapper)
- `M <= N` (target has at least as many parameters)
- For each `i` in `1..M`, `T_i` of actual equals `T_i` of target exactly

The extra `N - M` target parameters are accepted and silently ignored.

The reverse direction — actual-function-with-more-parameters to target-with-fewer — is **always rejected**.

### Nullable return types

```ts
function find(id: int): User | null {
 if (id === 0) {
 return null;
 }
 return { name: "Ada", address: { city: "X" } };
}
```

### Function values, calls, and wrappers

A function declaration produces a first-class typed function value. The source call syntax is always normal TypeScript-style syntax:

```ts
let r: int = add(1, 2);
```

Function values carry runtime type information, including whether the function is async. This is observable only through type checking and at the host interop boundary, not as a source-level value.

Compile-time call checking:

- Number of arguments must match the function type, except when calling a target produced by arity extension.
- Argument expression types must equal parameter types exactly, except assignment into `T | null` parameters accepts `T` or `null`.
- Return value has the declared return type.
- Direct calls with wrong argument types are compile-time errors.
- A direct call to an async function without `await` is a compile-time error.
- `await` may be applied only to a direct async function call.

Runtime call checking:

- Function wrappers check parameter and return values.
- Calls through imported host values are wrapped before being used as typed functions.

### Function expressions

A function expression has the same type rules as a function declaration:

```ts
let f: (x: int) => int = function(x: int): int {
 return x;
};
```

Rules:

- Parameter types are required.
- Return type annotation is required.
- Return analysis is the same as for function declarations.
- The expression produces a typed function value with the declared signature.
- Function expressions may appear wherever expressions are allowed.

### Closures and captured variables

Function expressions and nested function declarations may reference variables from enclosing scopes.

A captured variable cannot be reassigned after capture.

```ts
let x: int = 1;
let f: () => int = function(): int { return x; };
x = 2; // error: captured variable cannot be reassigned
```

```ts
let n: int = 0;
let bump: () => null = function(): null {
 n = n + 1; // error: captured variable cannot be reassigned
 return null;
};
```

```ts
class Counter { n: int = 0; }
let c: Counter = { n: 1 };
let g: () => int = function(): int {
 c.n = c.n + 1; // OK: mutating the object, not the binding
 return c.n;
};
```

```ts
let limit: int = 10;
limit = 11; // OK: not captured yet
let above: (v: int) => boolean = function(v: int): boolean { return v > limit; };
```

Captured variables keep their storage alive as long as any closure that captures them may be called.

For a `for` loop with a `let` initializer or a `for-of` loop, each iteration creates a fresh iteration binding for variables captured by closures. This matches TypeScript/JavaScript `let` closure behavior.

```ts
let fs: (() => int)[] = [];

for (let i: int = 0; i < 3; i = i + 1) {
 fs[fs.length] = function(): int {
 return i;
 };
}

let a: int = fs[0](); // 0
let b: int = fs[1](); // 1
let c: int = fs[2](); // 2
```

Narrowed flow types are not captured. A closure sees the declared type of captured variables, not a temporary narrowed type.

```ts
let n: int | null = 1;

if (n !== null) {
 let f: () => int = function(): int {
 return n; // error: captured type is int | null
 };
}
```

---

## Variables

```ts
let x: int = 1;
let y = true; // boolean inferred
let z = 1.0; // number inferred
```

### Inference rules

Inference is allowed when the initializer has a complete static type without dynamic table lookup or unknown external boundary:

```ts
let a = null; // null
let b = true; // boolean
let c = 1; // int
let d = 2.0; // number
let e = "hi"; // string
let f = [1, 2, 3]; // int[]
let g = [1.0, 2.0]; // number[]
let h = add(1, 2); // int, if add has a statically known function type
```

Object literals and empty arrays still require context.

Disallowed:

```ts
let h = t.someField; // error — dynamic table field must annotate
let i = unknown.f(1, 2); // error — dynamic table calls are forbidden
let j = []; // error — no element type
let k = [1, 1.0]; // error — mixed int / number
let l = [1, "1"]; // error — mixed types
let m = { }; // error — must annotate
```

### Redeclaration

Not allowed within the same block scope.

### Scope

- Module-level: visible from declaration to end of module.
- Block `{}`: scoped to block.

### Name resolution

Resolution order for an identifier expression:

1. Local variables and parameters in the innermost block scope.
2. Enclosing block scopes.
3. Module-level declarations.
4. Imported module bindings.
5. Compiler intrinsics (`int`, `number`, `bytes`, `has`) and prelude symbols.

Shadowing:

- Inner block variables may shadow outer block variables.
- Parameters may not shadow other parameters.
- Module-level declarations may not shadow imports.
- Imports may not shadow module-level declarations.
- Redeclaration in the same scope is an error.

Declaration order:

- `class` and `function` declarations are hoisted within the module for name resolution.
- `let` declarations are not hoisted and are visible only after their declaration.
- Function bodies may reference functions/classes declared later in the same module.
- Class fields may reference classes declared later in the same module.

### Definite return analysis

A function with return type `R` must return on all reachable paths.

Definitely-returning statements:

- `return expr;`
- `if (cond) { A } else { B }` where both `A` and `B` definitely return
- block whose final reachable statement definitely returns

Loops are not assumed to return unless they contain an unconditional `return` before any possible `break`. 

---

## Tables

### Table type and semantics

`table` is a dynamic key-value container supporting `string` keys. It is distinct from `class` types.

The value `null` is distinct from field absence. Storing `null` in a table field makes the field present. Deleting a field makes it absent. The two are distinguishable.

```ts
t.p = null; // field exists, value is null
delete t.p; // field is removed entirely
```

Tables are data containers. Calling through a table is not allowed.

```ts
let r: int = t.f(1, 2); // compile-time Error
```

### Reading table fields

```ts
let t: table = { x: 1 };

let y = t.x; // compile-time Error
let y: int = t.x; // ok — runtime check inserted
```

Contextual type checking algorithm for table reads:

Given expression `E = t.key` or `E = t[idx]` where `t: table`:

Allowed contexts:

1. `let x: T = E`
 - runtime-check `E` against `T`

2. `x = E`, where `x: T`
 - runtime-check `E` against `T`

3. `return E` inside function returning `R`
 - runtime-check `E` against `R`

4. `f(E)`, where corresponding parameter type is `T`
 - runtime-check `E` against `T`

5. `if (E)`
 - runtime-check `E` against `boolean`

Otherwise:
- compile-time error `E3003`

### Writing table fields

For `t.key = value` or `t[idx] = value` where `t: table`:

- `key` must be an identifier; `idx` must have static type `string`.
- `value` may be any type; no field-level schema is enforced at compile time or runtime.
- The stored value is written directly to the underlying container; no runtime type check is performed.

```ts
t.f1 = 1;
t.f2 = 1.0;
t.f3 = "abc";
t.f4 = null;
t.f5 = [1, 2, 3];
t.f6 = t;
```

```ts
t.key = null; // field exists, value is null
delete t.key; // field is removed
```

Index keys must be `string`.

### Table literals and key syntax

```ts
let t: table = { a: 1, b: "x" };
```

Table/object literal property names are restricted to identifiers:

```ts
{ name: "Ada", age: 36 } // OK
{ "name": "Ada" } // Error
{ [k]: 1 } // Error
```

Dynamic keys use assignment after construction:

```ts
let t: table = {};
t[key] = 1;
```

### Deletion

```ts
delete t.key;
```

Backend: removes the key from the container

## Arrays

### Array type and semantics

`T[]` is a 0-based array.

Supported element types: all types, including `class` types, nullable types, arrays, functions.

### Indexing

Arrays are 0-based.

```ts
let xs: int[] = [10, 20, 30];
let x: int = xs[0]; // ok
```

### Bounds behavior

An array read outside `0..length-1` raises an array-index-out-of-bounds runtime error.

Optional nullable arrays follow target typing:

```ts
let xs: (int | null)[] = [1, null, 3];
let x: int | null = xs[1];
```

### Array writes

For `xs[i] = value` where `xs: T[]`:

1. `i` must have static type `int`.
2. `value` must be assignable to `T` by normal assignment rules.
3. The runtime checks `0 <= i <= xs.length`.
4. `i === xs.length` appends one element.
5. `i > xs.length` or `i < 0` is a runtime error.
6. The stored value is runtime-checked against `T`.

```ts
let xs: int[] = [];
xs[0] = 1; // OK
xs[1] = "x"; // compile-time Error
xs[2] = 2; // runtime error if length is 1
```

### Length and iteration

Property `length` returns the number of elements:

```ts
for (let i: int = 0; i < xs.length; i = i + 1) {
 ...
}
```

`length` is a compiler-resolved intrinsic property available only on arrays and `bytes`. For `xs.length` where `xs: T[]`, the expression has type `int`. For `b.length` where `b: bytes`, the expression has type `int`. It is not a table field lookup, not a class field, and not dynamically dispatchable. Assignment to `.length` is a compile-time error.

## Bytes

`bytes` is a distinct DEAL-owned mutable byte buffer type.

Byte indexing is zero-based. Writes require an `int` in `0..255`; reads and writes reject indexes outside `0 <= i < b.length`. Assignment copies the buffer reference, not its contents. `bytes` is allowed as a class field and default value type, but is not jsonable.

---

## Control flow

### Truthiness

DEAL has no implicit truthiness. Conditions must be statically `boolean`.

```ts
if (x) { } // OK only if x: boolean
if (t.value) { } // error unless t.value is contextually checked as boolean
```

Dynamic table values require explicit boolean target/context:

```ts
let b: boolean = t.flag;
if (b) { }
```

### Conditional

```ts
if (boolean_expr) {
 ...
} else {
 ...
}
```

### While

```ts
while (boolean_expr) {
 ...
}
```

### For (C-style)

```ts
for (init ; test ; update) {
 ...
}
```

`init`, `test`, and `update` are optional. `init` is a `let` declaration or assignment. `test` is boolean. `update` is assignment.

If `test` is omitted, it is treated as `true`, so `for (;;) { ... }` is a valid infinite loop.

### For-of

```ts
let xs: int[] = [1, 2, 3];
for (let x: int of xs) {
  // x: int, each element in order
}

let s: string = "abc";
for (let c: string of s) {
  // c: string, one Unicode scalar value
}
```

The iterated expression must be `T[]` or `string`. The loop variable type is `T` (for arrays) or `string` (for strings). For strings, iteration yields one `string` containing exactly one Unicode scalar value per iteration, in order. The loop variable is a fresh binding per iteration (like `let` in `for-of` in TypeScript). `break` and `continue` are supported.

### Break / Continue

Supported inside loops.

---

## Error handling

### Error type

`Error` is a builtin class. Its shape is equivalent to this descriptive pseudo-source; user code must not declare it:

```ts
class Error {
  code: string = "";
  message: string = "";
}
```

`Error` values are produced by runtime exceptions or by class literal construction. Fields are readable using normal field access (`e.code`, `e.message`).

### throw

```ts
throw { message: "capacity exceeded" };
throw { code: "E_LIMIT", message: "index out of range" };
```

`throw` is a statement. The expression must have type `Error`. Execution transfers to the nearest enclosing `catch` block. If no `catch` encloses the `throw`, the error escapes to the host as a `DEALRuntimeError`.

### try / catch

```ts
try {
  let x: int = xs[99];
} catch (e) {
  // e: Error
}
```

`try`/`catch` is a statement, not an expression. The bound variable `e` has type `Error`. If no error occurs, the `catch` block is skipped. If an error occurs in the `try` block (via `throw` or a runtime error), execution jumps to `catch` and continues after the `catch` block.

If the `try` block has a definite `return`, the `catch` block must also have a definite `return` or `throw`. Both return expressions must satisfy the enclosing function's return type.

### Narrowing across try/catch

After a `try`/`catch`, all variables assigned inside the `try` block revert to their declared type.

```ts
let x: int | null = 1;

try {
  x = 2;
} catch (e) {
  // x: int | null
}

// x: int | null
```

## Async/Await

### async function

An `async` function returns its declared type directly. The `async` marker is part of the function type. Callers use `await` to suspend until the function completes.

```ts
import * as http from "host/http";

async function fetchUser(path: string): User | null {
  let json: string = await http.get(path);
  return User$fromJson(json);
}
```

`async` function expressions are supported:

```ts
let f: async (path: string) => User | null = async function(path: string): User | null {
  return await fetchUser(path);
};
```

### await

`await` suspends execution of the enclosing `async` function until the awaited `async` call completes, then evaluates to the call's return value. `await` is only valid inside an `async` function body.

```ts
let u: User | null = await fetchUser("/user/42");
```

Compile-time rules:
- `await E` is valid only inside an `async` function body.
- `E` must be a direct call expression.
- The callee of `E` must have async function type `async (...) => R`.
- The type of `await E` is `R`.
- `await` applied to a non-`async` call is a compile-time error.
- An async function call without `await` is a compile-time error.

### Async operation semantics

An async function call creates an internal async operation. The operation is not a source-language value and cannot be stored, passed, returned, compared, or inspected.

Each async operation completes exactly once, either with a value of the function's declared return type or by raising `Error`.

`await` waits for that operation to complete. If it completes with a value, `await` evaluates to that value. If it raises `Error`, `await` raises that `Error`.

An `Error` raised by an awaited operation is caught by the nearest enclosing `catch` around the `await`.

Within one async function invocation, evaluation before an `await` happens before evaluation resumed after that `await`.

DEAL defines no source-level concurrent start, scheduling, cancellation, polling, task, future, promise, or shared-memory concurrency primitive.

Mutable DEAL values are not concurrently shared by source-language semantics. Host values crossing untyped boundaries are validated as DEAL values or remain backend-defined opaque host values.

### Backend lowering

Async/await is lowered backend-specifically.

A backend must preserve these source-level rules:

- async functions have async function type `async (...) => R`
- async calls must appear as the operand of `await`
- `await` may appear only inside an async function body
- `await` evaluates to the declared return type `R`
- no source-level coroutine, promise, future, or task type exists

Backend strategies are not source-language observable.

A LuaJIT backend may implement async lowering with internal coroutines, continuation-passing style, or explicit state-machine tables.

A JVM backend may implement async lowering with virtual threads, blocking calls, futures, or explicit state machines.

All async function completion values cross the typed boundary defined in the backend conformance contract.

---

## Modules, declarations, standard library, and host ABI

### No user-defined globals

Every source file compiles to a module that returns an export table. Top-level declarations are local. User code cannot define global variables.

When a compiler invocation selects an entry module, that module must export `main` with non-async signature `(): null`; the backend invokes `main()` from that module.

```ts
export function main(): null {
 return null;
}

export function add(a: int, b: int): int {
 return a + b;
}

export class Point {
 x: number = 0.0;
 y: number = 0.0;
}
```

### Export forms

```ts
export function name(p1: T1, p2: T2): R { ... }
export class Name { ... }
```

Declaration files additionally support external function declarations:

```ts
export function name(p1: T1, p2: T2): R;
```

Declaration files may export only functions and classes. `export let` is forbidden.

No named export lists, no default export, no re-export, no namespace export.

Exporting a class exports class metadata, not a constructor or callable value. The metadata enables import-side typing and runtime class checks.

### Import forms and import typing

```ts
import * as mod from "./mod";
```

Every `import` binding has a statically known module type.

A module type is a mapping from exported names to their declared types. Accessing an export not present in the module type is a compile-time error. If the compiler cannot assign a module type to an import, compilation fails.

Example:

```ts
// mathlib.deal
export function add(a: int, b: int): int {
 return a + b;
}

// main.deal
import * as mathlib from "./mathlib";

export function main(): null {
 let x: int = mathlib.add(1, 2); // OK, add: (int, int) => int
 let y = mathlib.add(1, 2); // OK, inferred int
 let z: int = mathlib.missing(1); // error: export 'missing' is not declared
 return null;
}
```

Imported module members are not dynamic table reads. They are statically typed member accesses over the module type.

### Module resolution

For import specifier `S` from source file `A`:

1. If `S` starts with `./` or `../`, resolve relative to directory of `A`.
2. Otherwise resolve as package module using compiler search path.
3. Candidate source files, in order:
 - `S.deal`
 - `S/index.deal`
 - `S.d.deal`
 - `S/index.d.deal`
4. Candidate runtime modules, in order:
 - emitted path for `S.deal`
 - host `require(S)`
5. Resolution failure is compile-time error unless the module is explicitly marked external.

`require` is compiler/runtime-only and is not source-visible. Source code must use `import`.

The backend converts `./a/b` to a `require` path according to the configured module root. The default maps path separators to dots and strips `.deal`:

```txt
./math/vector.deal -> require("math.vector")
```

### Module initialization and cycles

- Modules initialize at most once per runtime instance.
- Module initialization is depth-first in import order.
- A module export table becomes visible only after successful initialization.
- Import cycles are compile-time errors.
- If module initialization raises an error, the module is marked failed; later imports re-raise the same error.

### Declaration-file format

Declaration files use `.d.deal`. They contain only leading imports, exports, and class declarations. No executable statements.

```ts
export function print(x: string): null;
export class Point {
 x: number = 0.0;
 y: number = 0.0;
}
```

Rules:

- Function declarations end with `;` and have no body.
- `export class` describes the runtime class shape.
- `export let` is forbidden.
- No top-level ambient declarations in implementation `.deal` files.
- Declaration files may describe host modules.

Host ABI:

- Host modules are loaded only if listed in `deal.json.externals`.
- The declaration path is resolved relative to the manifest directory unless absolute paths are permitted by host policy.
- Host module runtime object must expose exported names from its `.d.deal` declaration.
- Extra host exports are ignored; missing declared exports are load-time errors.
- Every call/value crossing the host boundary is runtime-checked.
- External declaration files may declare async functions. A host function declared as `async (...) => R` must return a backend async operation accepted by the backend's `await` lowering. Source code cannot observe that operation except through `await`.

### C FFI declaration files

A C FFI declaration file is a `.d.deal` declaration file containing `// @extern-c` after any leading imports and before its first declaration. The C library to load is specified by the importing project's `deal.json` external entry using `nativeLibrary` (see Package manifest).

`// @extern-c` marks the file. Each exported class must have exactly one of `// @c-struct` or `// @c-pointer`; `// @jsonable` has no effect. Async function declarations are compile-time errors, and each exported function name is its C symbol name.

C FFI types are exactly:

| Type | Parameter | Return |
|---|---:|---:|
| `int`, `number`, `boolean`, `string` | yes | yes |
| `bytes` | yes | no |
| `null` | no | yes |
| same-file `// @c-struct` class | yes | yes |
| same-file `// @c-pointer` class | yes | yes |

All other parameter and return types are compile-time errors.

```ts
// @extern-c

// @c-struct
export class Vec2 {
  x: number = 0.0;
  y: number = 0.0;
}

export function init(): null;
export function cos(x: number): number;
export function add(a: int, b: int): int;
export function invert(x: boolean): boolean;
export function logLine(s: string): null;
export function length(v: Vec2): number;
export function midpoint(a: Vec2, b: Vec2): Vec2;
```

#### C struct classes

A `// @c-struct` class is a nominal exported DEAL class whose fields define its C FFI struct layout.

Rules:

- Fields must be required fields with defaults.
- Valid field types are exactly `int`, `number`, `boolean`, and same-file `// @c-pointer` classes.
- All other field types are compile-time errors.
- Field order is source order.
- Field ABI mapping uses the C FFI ABI mapping table.
- C structs follow target ABI; use shims when portability matters.
- No packing, alignment, or nesting controls exist.
- Struct values cross C FFI by value.
- DEAL construction uses normal class defaults; C FFI struct returns read every field from the returned C struct.
- C mutation of a copied struct argument is not visible to DEAL unless represented by the function return value.

#### C pointer classes

A `// @c-pointer` class is a nominal exported DEAL type representing a non-null opaque `void*` token. It has no DEAL-visible fields or storage layout.

Rules:

- A non-empty `// @c-pointer` class body is a compile-time error.
- Object-literal construction of `// @c-pointer` values is a compile-time error.
- `// @c-pointer` is not jsonable.
- DEAL code may store, pass, and return `// @c-pointer` values.
- DEAL code does not automatically release `// @c-pointer` values; cleanup must use explicit C FFI functions.
- A C `NULL` pointer crossing into DEAL raises `FFI_NULL_POINTER`.

#### C FFI ABI mapping

The C ABI of an exported FFI function is derived from its DEAL function signature.

| DEAL type | C ABI type | Mapping |
|---|---|---|
| `int` | `int32_t` | signed 32-bit integer |
| `number` | `double` | IEEE 754 double |
| `boolean` | `_Bool` | `false` as 0, `true` as 1; nonzero return as `true` |
| `string` parameter | `const char*` | non-null borrowed NUL-terminated UTF-8 input string |
| `string` return | `const char*` | non-null borrowed NUL-terminated UTF-8 output string copied into DEAL |
| `bytes` parameter | `const uint8_t*`, `int32_t` length | read-only borrowed buffer and byte length |
| `null` return | `void` | returns `null` |
| `// @c-struct` class | C struct by value | source-order scalar fields |
| `// @c-pointer` class | `void*` | non-null opaque pointer token |

String arguments are encoded as temporary NUL-terminated UTF-8 buffers. Embedded U+0000 raises `FFI_INVALID_STRING`. Argument buffers remain alive until return conversion completes.

A `string` return is a non-null borrowed `const char*`. `NULL` raises `FFI_NULL_STRING`. DEAL copies bytes up to the first NUL, validates them as UTF-8, decodes them to Unicode scalar values, and never frees the pointer. Malformed UTF-8 raises `FFI_INVALID_UTF8`.

A `bytes` parameter lowers to `const uint8_t*` plus immediate `int32_t` length. The buffer is read-only, borrowed, and valid only during the call. C must copy to retain it.

C APIs that require out parameters, struct pointers, mutable buffers, caller-owned returned memory, callbacks, or complex ownership should be exposed through a small C shim that converts them into DEAL FFI shapes: scalar returns, by-value `// @c-struct` results, `// @c-pointer` handles, borrowed strings, and caller-allocated `bytes` parameters.

Declaration metadata versioning:

```ts
// @deal-version 1.3
```

If omitted, compiler assumes the current project `languageVersion`. A compiler must reject declaration files with a newer major version. Minor-version migrations may be performed only by explicit compiler migration rules. DEAL v1.3 is not source-compatible with earlier language versions; projects using v1.3 must set `languageVersion` to `"1.3"` and satisfy the v1.3 grammar.

### Package manifest

A project may define `deal.json` at its root:

```json
{
 "languageVersion": "1.3",
 "moduleRoots": ["src"],
 "output": "build/lua",
 "backend": "luajit",
 "stdlib": "1.3",
 "dependencies": {},
 "externals": {
  "host/log": {
   "declaration": "bindings/host-log.d.deal"
  }
 }
}
```

Rules:

- `languageVersion` selects grammar/type rules.
- `moduleRoots` participate in import resolution.
- DEAL has no package registry. `dependencies` is reserved for local/package-manager integration later.
- Standard library modules may be described by bundled `.d.deal` files, but are resolved as part of the language distribution rather than as project external host modules.
- `externals` declares host modules available to the compiler; importing an unlisted external is a compile-time error. A C FFI entry must include `nativeLibrary`.

```json
{
  "externals": {
    "native/math": {
      "declaration": "native/math.d.deal",
      "nativeLibrary": "math"
    }
  }
}
```

### Standard library declarations

The compiler ships practical minimal standard modules. All are imported explicitly.

#### `std/console.d.deal`

```ts
export function log(x: string): null;
export function error(x: string): null;
```

#### `std/string.d.deal`

```ts
export function length(s: string): int;
export function substring(s: string, start: int, end: int): string;
export function contains(s: string, part: string): boolean;
export function startsWith(s: string, part: string): boolean;
export function endsWith(s: string, part: string): boolean;
export function replace(s: string, from: string, to: string): string;
export function split(s: string, sep: string): string[];
export function trim(s: string): string;
```

String lengths and positions are measured in Unicode scalar values.

#### `std/table.d.deal`

```ts
export function keys(t: table): string[];
```

#### `std/json.d.deal`

```ts
export function parse(s: string): table;
export function stringify(t: table): string;
```

Integral JSON numbers within `int` range parse as `int`; others as `number`.

`parse` raises `Error` for malformed JSON or duplicate keys.

`stringify` raises `Error` for non-JSON values, non-finite numbers, or cycles.

#### `std/math.d.deal`

```ts
export function floor(x: number): number;
export function ceil(x: number): number;
export function sqrt(x: number): number;
export function absInt(x: int): int;
export function absNumber(x: number): number;
export function minInt(a: int, b: int): int;
export function maxInt(a: int, b: int): int;
```

#### `std/time.d.deal`

```ts
export function nowMillis(): number;
```

Usage:

```ts
import * as strings from "std/string";
import * as json from "std/json";

let parts: string[] = strings.split("a,b", ",");
let t: table = json.parse("{\"name\":\"Ada\"}");
```

### Host APIs

DEAL source has no implicit global namespace.

A host API is available only through an imported module with a `.d.deal` declaration.

The compiler type-checks host API use from the declaration file. Runtime values crossing the host boundary are checked according to the backend conformance contract.

Raw backend APIs, including Lua `require`, Lua `ffi`, JVM reflection, filesystem, process, networking, and debug APIs, are not source-language features unless exposed by an imported declaration module.

C FFI is available only through `// @extern-c` declaration files.

### Host ABI and interoperability

#### Value mapping

Value mapping is backend-specific. See [LuaJIT value mapping](#luajit-value-mapping) and [JVM value mapping](#jvm-value-mapping) for per-backend representations.

#### Boundary checks

Any value crossing from an untyped host context into DEAL is checked:

```ts
let f: (x: int) => int = lib.f;
```

Target-typed table member reads and declared function-signature checks are supported. Dynamic table calls are forbidden. Explicit class/table conversion syntax is deferred.

#### C FFI runtime semantics

Importing a C FFI module loads its native library and resolves all declared symbols before the module export table becomes visible. Failure raises `FFI_LIBRARY_LOAD` or `FFI_SYMBOL_MISSING` during module initialization and marks the module failed as in module initialization semantics.

Calls are synchronous. DEAL does not read or expose `errno`. C signals, `longjmp`, process aborts, and memory faults are outside DEAL semantics.

A compiler targeting a backend without C FFI support rejects `// @extern-c` with `FFI_UNSUPPORTED_BACKEND`.

#### Function ABI decision

Function values are **wrappers**. The backend always emits explicit `.f(...)` calls; it does not hide wrappers behind metatable `__call`.

```lua
{ __kind = "function", sig = "(int,int)->int", f = function(...) ... end }
```

Reason: runtime type system must preserve signatures and support runtime function type checks. Avoiding `__call` keeps generated code explicit, portable, and easier to debug.

Calling a typed function compiles to `.f(...)` internally. User syntax remains normal:

```ts
let x: int = add(1, 2);
```

Emitted:

```lua
local x = __rt.check_int(add.f(1, 2))
```

When passing a DEAL function to host code, use an adapter exported by the runtime:

```lua
__rt.as_lua_function(add) -- returns plain host function that delegates to add.f
```

When accepting a host function as a typed function, the runtime creates a checked wrapper:

```lua
__rt.from_lua_function("(int)->int", raw_f)
```

### Host error and debugging

Errors propagate through function wrappers, module boundaries, and call chains. If not caught by `catch`, an error escapes to the host as a `DEALRuntimeError` object with source location, code, message, and stack frames.

Errors caught by `catch` are reified as `Error` class values. Uncaught errors behave as described in the host ABI section.

DEALRuntimeError format:

```txt
code
message
source file
line
column
expected type (if applicable)
actual runtime kind (if applicable)
stack frames
cause (if applicable)
```

### Source maps and debugging

Generated code debugging:

- The backend emits source comments before generated statement groups.
- Compiler emits a source map sidecar file `<module>.deal.map.json`.
- Runtime errors use generated check metadata to report original `.deal` location.
- Stack traces include both generated function names and original source function names.

Source map format:

```json
{
 "version": 1,
 "source": "src/main.deal",
 "generated": "build/lua/main.lua",
 "mappings": [
 { "generatedLine": 10, "generatedColumn": 1, "sourceLine": 4, "sourceColumn": 1 }
 ]
}
```

---

---

## Runtime execution model

### Runtime sentinels

```lua
local __NULL = {} -- JSON null
local __MISSING = {} -- missing optional field
```

| Semantic value | Runtime role |
|---|---|
| `null` | JSON null / language null |
| missing optional field | field absence state |

### Backend conformance contract

A conforming backend preserves the observable behavior defined by this specification.

Observable behavior includes:

- compile-time diagnostics
- successful runtime values
- runtime error codes and source locations
- module import/export behavior
- host boundary behavior
- `null` and missing-field semantics
- class nominal identity
- function type identity, including the async marker
- evaluation order
- integer overflow and division semantics
- `@jsonable` serialization behavior

A backend may choose any internal representation, including erased, partially erased, statically typed, boxed, unboxed, interpreted, source-generated, or bytecode-generated representation, if observable behavior is unchanged.

A backend may omit a runtime check when static backend representation proves that the value already satisfies the DEAL type and no untyped boundary can have produced it.

A backend is non-conforming if it erases DEAL types in a way that allows a runtime value to cross a typed boundary without equivalent validation.

#### Typed boundaries

A typed boundary is a point where a runtime value is accepted as, stored as, returned as, exported as, or reconstructed as a declared DEAL type.

Backends must validate values at every typed boundary unless the validation is statically proven redundant.

Typed boundaries are exactly:

- variable declaration with annotation: `let x: T = e`
- assignment to a variable with declared or inferred type `T`
- assignment to a declared class field of type `T`
- assignment to an array element of `T[]`
- assignment to a byte element of `bytes`
- function parameter entry
- function return
- async function completion value
- class object literal construction
- class default field application
- class value received from an untyped boundary
- optional field read that converts missing to `null`
- table read in contextual target type `T`
- value read from imported module member
- value exposed through module export table
- value crossing from host into DEAL through `.d.deal`
- value crossing from DEAL into host through `.d.deal`
- value crossing from C FFI into DEAL
- value crossing from DEAL into C FFI
- standard-library function parameter and return
- external declaration function parameter and return
- `@jsonable` `fromJson` field validation
- `@jsonable` `toJson` field serialization input validation

#### Backend representation

The following sections define required value mappings for supported backends. These mappings are representation contracts, not additional source-language semantics.

When a backend mapping conflicts with the source-language semantics or the backend conformance contract, the source-language semantics and backend conformance contract are authoritative.

### LuaJIT value mapping

| Type | LuaJIT representation |
|---|---|
| `null` | unique sentinel `__NULL` |
| missing optional field | absent key or `__MISSING` internally |
| `boolean` | Lua boolean |
| `int` | checked Lua number in `[-2147483648, 2147483647]` |
| `number` | Lua number |
| `string` | Lua string containing valid UTF-8 |
| `bytes` | backend byte buffer object or LuaJIT `uint8_t[]` wrapper |
| `table` | Lua table |
| `ClassName` | Lua table tagged with class symbol |
| `T[]` | Lua table with 1-based contiguous storage |
| `T | null` | either representation of `T` or `__NULL` |
| `(params) => R` | wrapper table `{ __kind = "function", sig, f }` |
| module type | Lua export table |

### JVM value mapping

| Type | JVM representation |
|---|---|
| `null` | Java `null` reference |
| missing optional field | per-field presence bit or `Missing` sentinel |
| `boolean` | primitive `boolean` |
| `int` | primitive `int` |
| `number` | primitive `double` |
| `string` | `java.lang.String` with no unpaired surrogate code units |
| `bytes` | `byte[]`, `ByteBuffer`, or runtime-owned byte buffer wrapper |
| `table` | `TTable` runtime object, e.g. ordered map |
| `ClassName` | generated record class or `TClassObject` runtime shape |
| `T[]` | `TArray<T>` runtime object or specialized primitive array |
| `T | null` | nullable JVM reference or tagged nullable wrapper for primitives |
| `(params) => R` | generated function wrapper with descriptor |
| module type | generated module object/export map |

### JVM backend contract

A conforming JVM backend emits Java source, JVM bytecode, or an interpreter over checked DEAL IR.

The JVM backend must preserve the backend conformance contract.

The JVM backend may use JVM primitive types, final classes, verifier-checked bytecode, method signatures, and JIT optimization to prove typed-boundary checks redundant.

Recommended JVM representation:

| DEAL type | JVM representation |
|---|---|
| `boolean` | `boolean` where statically known; boxed `Boolean` at dynamic boundaries |
| `int` | `int` where statically known; boxed `Integer` at dynamic boundaries |
| `number` | `double` where statically known; boxed `Double` at dynamic boundaries |
| `string` | non-null `java.lang.String` with no unpaired surrogate code units |
| `null` | `DealNull.INSTANCE` at dynamic boundaries; Java `null` only where representation is statically nullable |
| required class field `T` | Java field of representation of `T` |
| required nullable field `T | null` | nullable representation or tagged wrapper |
| optional field `p?: T` | presence bit plus field storage |
| optional nullable field `p?: T | null` | presence bit plus nullable storage |
| `table` | `DealTable` |
| `bytes` | runtime-owned byte buffer wrapper over `byte[]` or `ByteBuffer` |
| `T[]` | `DealArray<T>` or specialized primitive array wrapper |
| `(…) => R` | `DealFunction` wrapper with runtime descriptor |
| `async (…) => R` | `DealAsyncFunction` wrapper with runtime descriptor |
| module type | generated module class or export object |

The JVM backend must not expose Java `null` as DEAL `null` across untyped boundaries without validation.

### Runtime type descriptor format

```txt
RuntimeTypeDescriptor :=
 PrimitiveDescriptor
 | ClassDescriptor
 | ArrayDescriptor
 | NullableDescriptor
 | FunctionDescriptor

PrimitiveDescriptor :=
 "null" | "boolean" | "int" | "number" | "string" | "bytes" | "table" | "Error"

ClassDescriptor :=
  "@" ModuleRoot "/" ModuleRelativePath "/" ClassName

ModuleRoot := /* the configured module root from deal.json, e.g. "src", "lib/utils" */
ModuleRelativePath := /* path components from module root to defining file, e.g. "models" */

ArrayDescriptor :=
 "[" RuntimeTypeDescriptor "]"

NullableDescriptor :=
 "?" RuntimeTypeDescriptor

FunctionDescriptor :=
 AsyncMarker? "(" ParamDescriptorList? ")" "->" RuntimeTypeDescriptor

AsyncMarker :=
 "async"

ParamDescriptorList :=
 ParamDescriptor ("," ParamDescriptor)*

ParamDescriptor :=
 RuntimeTypeDescriptor
```

Examples:

```txt
int // int
?string // string | null
[int] // int[]
[[int]] // int[][]
?[@src/app/User] // User[] | null
[?@src/app/User] // (User | null)[]
(int,string)->boolean // (x:int,y:string)=>boolean
()->null // () => null
async(int)->string // async (x:int)=>string
```

Constraint: `NullableDescriptor` inner type must not be `null` and must not be another `NullableDescriptor`.

Equality semantics for `===`:

- `null === null` is true by sentinel identity.
- Booleans compare by value.
- `int` compares by integer value.
- `number` compares by IEEE 754 equality: `NaN === NaN` is `false`; `NaN !== NaN` is `true`.
- Strings compare by Unicode scalar-value sequence.
- Arrays, bytes, tables, classes, and functions compare by reference identity.
- Values of different static types cannot be compared, except `T | null` vs `null`.

### Runtime library

Generated into every module or available as a shared runtime module:

```lua
local __rt = require("deal.runtime")

function __rt.check_null(v)
 if v ~= __NULL then error("runtime: expected null") end
 return v
end

function __rt.check_nullable(inner_check, v)
 if v == __NULL then return v end
 return inner_check(v)
end

function __rt.check_boolean(v)
 if type(v) ~= "boolean" then error("runtime: expected boolean") end
 return v
end

function __rt.check_int(v)
 if type(v) ~= "number" then error("runtime: expected int") end
 if v ~= v then error("runtime: expected int, got NaN") end
 v = v + 0
 if v == math.huge or v == -math.huge then error("runtime: expected int, got infinity") end
 if v % 1 ~= 0 then error("runtime: expected int") end
 if v < -2147483648 or v > 2147483647 then error("runtime: int out of range") end
 return v
end

function __rt.int_add(a, b)
 return __rt.check_int(a + b)
end

function __rt.int_sub(a, b)
 return __rt.check_int(a - b)
end

function __rt.int_mul(a, b)
 return __rt.check_int(a * b)
end

function __rt.int_div(a, b)
 if b == 0 then error("runtime: integer division by zero") end
 return __rt.check_int(math.modf(a / b))
end

function __rt.int_mod(a, b)
 if b == 0 then error("runtime: integer division by zero") end
 return __rt.check_int(a - math.modf(a / b) * b)
end

-- int % int emits __rt.int_mod(a, b)

function __rt.check_number(v)
 if type(v) ~= "number" then error("runtime: expected number") end
 return v
end

function __rt.check_string(v)
 if type(v) ~= "string" then error("runtime: expected string") end
 -- validate boundary encoding
 return v
end

function __rt.check_table(v)
 if type(v) ~= "table" then error("runtime: expected table") end
 return v
end

function __rt.check_array(array_descriptor, value)
 if type(value) ~= "table" then error("runtime: expected array") end
 local element_descriptor = __rt.array_element_descriptor(array_descriptor)
 local i = 1
 while i <= #value do
 __rt.check_type(element_descriptor, value[i])
 i = i + 1
 end
 return value
end

function __rt.check_type(expected, value)
 -- dispatched check by runtime type descriptor, including nullable, class shapes, arrays
end

function __rt.check_function_sig(expected_sig, sig, f)
 if expected_sig ~= sig then
 error("runtime: mismatched function signature")
 end
 return f
end

function __rt.class_(class_name, defaults, fields)
 -- construct a class table with defaults + provided fields
 -- validate types
end

function __rt.export_class(name)
 return {__kind = "class", __classname = name}
end

function __rt.function_(sig, f)
 return {__kind = "function", sig = sig, f = f}
end
```

### Function wrapper

Every declared function is wrapped so that argument and return checks are inlined:

```lua
local add = __rt.function_("(int,int)->int", function(x, y)
 __rt.check_int(x)
 __rt.check_int(y)
 local __ret = __rt.int_add(x, y)
 return __rt.check_int(__ret)
end)

local result = __rt.check_int(add.f(1, 2))
```

### Arity extension adapter

When a shorter function is assigned to a longer target signature, the compiler emits an adapter:

```lua
__rt.function_("(int,int)->int", function(x, y)
 __rt.check_int(x)
 __rt.check_int(y)
 return __rt.check_int(add.f(x))
end)
```

### Class runtime

```lua
__rt.class_("User",
 { id = 0, active = true, bio = __NULL }, -- defaults
 { id = 1, name = "Ada" } -- provided
)
```

The runtime:
1. Evaluates defaults per construction.
2. Deep-constructs literal defaults so mutable defaults are not shared.
3. Overrides with provided fields.
4. Rejects any extra provided field.
5. Validates all required-present and optional-present types.
6. Tags the table with class name.
7. Returns the table.

Optional fields not provided are represented internally via key absence (`nil`) or side-table metadata. Direct source-level field reads translate missing to `__NULL`; `has(obj.field)` distinguishes missing from explicit `null`.

---

## Test suite basis

### Positive test fragments

Concrete application fixtures place executable statement fragments inside `export function main(): null`; import fragments remain at the top of the module, and declaration/export fragments remain at module top level.

```ts
// --- variables + inference ---

let a: null = null;
let b = null;
let c: boolean = true;
let d = false;
let e: int = 42;
let f = 100;
let g: number = 3.14;
let h = 2.71;
let i: string = "hello";
let j = "world";

// --- arrays ---

let xs: int[] = [];
let ys = [1, 2, 3];
let zs: string[] = ["a", "b", "c"];
let ws: int[][] = [[1, 2], [3, 4]];

let first: int = ys[0];
ys[0] = 99;

// --- nullable variables ---

let n1: int | null = null;
let n2: int | null = 42;
let n3: string | null = "hello";

// --- class declaration ---

class Address {
 city: string = "";
 zip: int = 0;
}

class User {
 name: string = "";
 nick?: string;
 bio: string | null = null;
 active: boolean = true;
 home: Address = {};
}

// --- class construction ---

let u1: User = {
 name: "Ada",
 home: { city: "London", zip: 12345 },
};
let u2: User = {
 name: "Bob",
 nick: "beeb",
 bio: "developer",
 home: { city: "Paris" },
};

// --- optional field ---

let u3: User = { name: "Eve", home: { city: "Berlin" } };
// nick is missing
let hasNick: boolean = has(u3.nick);
let maybeNick: string | null = u3.nick;

// --- nullable field ---

let u4: User = {
 name: "Mallory",
 bio: null,
 home: { city: "NYC" },
};

// --- class array ---

let users: User[] = [
 { name: "A", home: { city: "A" } },
 { name: "B", home: { city: "B" } },
];

let emptyUsers: User[] = [];

// --- class field access ---

let userName: string = u1.name;
u1.active = false;

// --- nullable return ---

function findUser(id: int): User | null {
 if (id === 1) {
 return {
 name: "Ada",
 home: { city: "London" },
 };
 }
 return null;
}

let maybeUser: User | null = findUser(1);

if (maybeUser !== null) {
 let sureUser: User = maybeUser;
}

// --- function declaration ---

function add(a: int, b: int): int {
 return a + b;
}

function say(msg: string): null {
 return null;
}

// --- function value ---

let fadd: (a: int, b: int) => int = add;
let result: int = fadd(1, 2);

// --- function with nullable param ---

function maybeLog(msg: string | null): null {
 return null;
}

// --- arity extension ---

function one(x: int): int { return x; }
let takesTwo: (x: int, y: int) => int = one;
let v: int = takesTwo(10, 20);

// --- array parameter ---

function sum(values: int[]): int {
 let total: int = 0;
 for (let i: int = 0; i < values.length; i = i + 1) {
 total = total + values[i];
 }
 return total;
}

let s: int = sum([1, 2, 3, 4, 5]);

// --- table ---

let t: table = {};
t.key = "val";
t.num = 42;
t.nil = null;
let sv: string = t.key;
delete t.num;

// --- table literal ---

let items: table = { name: "Ada", age: 36 };

// --- control flow ---

let x: int = 0;

if (x === 0) {
 x = 1;
}

let wasZero: boolean = x === 0;

while (x < 10) {
 x = x + 1;
}

for (let ii: int = 0; ii < 3; ii = ii + 1) {
 x = x + ii;
}

// --- break / continue ---

let found: boolean = false;

for (let ci: int = 0; ci < 10; ci = ci + 1) {
 if (ci === 5) { break; }
}

let sum2: int = 0;
for (let ci: int = 0; ci < 5; ci = ci + 1) {
 if (ci === 2) { continue; }
 sum2 = sum2 + ci;
}

// --- explicit conversion ---

let ni: int = int(3.0);
let nf: number = number(3);

// --- module export ---

export class Point {
 x: number = 0.0;
 y: number = 0.0;
}

export function mul(a: int, b: int): int {
 return a * b;
}

// --- module import ---
// Test fixture includes ./lib.deal:
//
// export function mul(a: int, b: int): int {
// return a * b;
// }

import * as lib from "./lib";

let libResult: int = lib.mul(2, 3);
```

### Negative test fragments

Concrete application fixtures place executable statement fragments inside `export function main(): null`; import fragments remain at the top of the module, and declaration/export fragments remain at module top level.

```ts
// --- type mismatch ---

let a: int = 1.0; // error: number is not int
let b: number = 1; // error: int is not number
let c: int[] = [1.0, 2.0]; // error: number[] is not int[]

// --- mixed literal array ---

let d = [1, 1.0]; // error: mixed types
let e = [1, "one"]; // error: mixed types

// --- invalid number literal ---

let numOk: number = 0.0; // OK
let numBad: number = 0.; // parse Error

// --- untyped table access ---

let t: table = {};
let v = t.x; // error: must provide target type

// --- dynamic table call ---

let dyn: table = {};
let r: int = dyn.add(1); // error: dynamic table calls are forbidden

// --- empty array literal ---

let f = []; // error: cannot infer element type

// --- function arity (actual more params) ---

function two(a: int, b: int): int { return a + b; }
let g: (x: int) => int = two; // error: actual has more parameters

// --- function type mismatch (parameter types) ---

function takeInt(a: int): int { return a; }
let h: (x: number) => number = takeInt; // error: int ≠ number

// --- nullable value outside narrowing block ---

let n: int | null = 42;
let m: int = n; // error: int | null is not int outside null check

// --- optional field read is nullable ---

class OptUser {
 nick?: string;
}
let ou: OptUser = {};
let os: string = ou.nick; // error: string | null is not string

// --- nullable type mismatch ---

class A { x: int = 0; }
class B { x: int = 0; }
let na: A | null = { x: 1 };
let nb: B | null = na; // error: A | null is not B | null

// --- class nominal mismatch ---

class PointA { x: int = 0; y: int = 0; }
class PointB { x: int = 0; y: int = 0; }
let pa: PointA = { x: 1, y: 2 };
let pb: PointB = pa; // error: nominal mismatch
let pe: PointA = { x: 1, y: 2, z: 3 }; // error: extra field rejected

// --- class/table invariant ---

let c1: table = {};
let c2: int = 1;
let c3: PointA = c1; // error: table is not PointA
let c4: table = pa; // error: PointA is not table

// --- return type mismatch ---

function wrongReturn(): int {
 return 1.0; // error: returned number is not int
}

// --- missing return ---

function missingReturn(): int {
 let x: int = 1;
} // error: function must return int

// --- assignment to wrong type ---

let y: int = 1;
y = 2.0; // error: cannot assign number to int

// --- operator mismatches ---

let i: string = "a" + 1; // error: + requires both string or both numeric
let j: boolean = 1 < 2.0; // error: numbers of different type
let k: int = 1 + 2.0; // error: mixed types

// --- boolean logic on non-boolean ---

let l: int = 1;
let m: boolean = !l; // error: ! requires boolean
let n: boolean = l && true; // error: && requires boolean

// --- redeclaration ---

let p: int = 1;
let p: int = 2; // error: redeclaration in same scope

// --- field without default ---

class WithRequired {
 name: string = "";
 value: int; // error: field must have a default value
}
```

### Runtime-error test fragments

These should compile but fail at runtime when executed from `export function main(): null`:

```ts
// --- array index out of bounds ---

let xs: int[] = [1, 2, 3];
let x: int = xs[99]; // runtime: array index out of bounds

// --- wrong table field read ---

let t: table = { x: 1 };
let y: string = t.x; // runtime: 1 is not string

// --- null sentinel mismatch ---

let t2: table = {};
let v: int = t2.missing; // runtime: nil is not int

// --- nullable unwrapped incorrectly ---

function tryRead(t: table): int | null {
 return null;
}
let result: int = int(tryRead(t)); // runtime: attempted to convert null to int

// --- explicit conversion out of int range ---

let ni: int = int(1e308); // runtime: out of int range

```

---

## Diagnostics

### Compile-time diagnostic format

Every compiler diagnostic must contain:

```txt
code: stable diagnostic code, e.g. E1001
severity: error | warning
message: human-readable message
file
line
column
span length
optional notes
```

### Required diagnostic classes

| Code range | Category |
|---|---|
| `E1xxx` | lexical / parse errors |
| `E2xxx` | name resolution and module resolution |
| `E3xxx` | type checking |
| `E4xxx` | class shape validation |
| `E5xxx` | function signature and call validation |
| `E6xxx` | backend lowering and ABI errors |
| `E7xxx` | declaration-file errors |
| `E8xxx` | runtime errors |

Examples:

```txt
E3001: cannot assign number to int
E3002: cannot infer type of empty array literal
E3003: table field read requires contextual target type
E4001: class field without default is not valid
E5001: function argument count mismatch
E7001: declaration file cannot contain executable statement
```

### Runtime diagnostic format

Runtime errors must preserve source location when emitted from generated checks:

```txt
DEALRuntimeError {
  code: "E8001",
 message: "expected int, got null",
 file: "src/main.deal",
 line: 12,
 column: 9,
 expected: "int",
 actual: "null"
}
```

Array runtime diagnostics:

| Code | Meaning |
|---|---|
| `E8002` | array index out of bounds |
| `E8003` | array element type check failed |

C FFI runtime `Error.code` values:

`FFI_*` codes are runtime `Error.code` string values. They are not compile-time diagnostic identifiers; compile-time C FFI errors use the normal numeric diagnostic code namespace.

| Code | Meaning |
|---|---|
| `FFI_LIBRARY_LOAD` | library failed to load or configure |
| `FFI_SYMBOL_MISSING` | declared symbol not present in library |
| `FFI_INVALID_STRING` | embedded U+0000 in string input |
| `FFI_INVALID_UTF8` | C FFI string return was not valid UTF-8 |
| `FFI_NULL_STRING` | C FFI string return was `NULL` |
| `FFI_NULL_POINTER` | C FFI pointer value crossing into DEAL was `NULL` |

### Operational semantics summary

Evaluation is strict and left-to-right:

1. Evaluate receiver expression before member/index/call arguments.
2. Evaluate call arguments left-to-right.
3. Evaluate assignment RHS before LHS write check.
4. Short-circuit `&&` and `||`.
5. Function calls create a new local scope.
6. Class object literal construction evaluates provided fields left-to-right, applies defaults for omitted required-present fields, validates all fields, then tags the object.
7. Table object literal construction evaluates properties left-to-right and stores values as dynamic fields.

### Conformance tests

A conforming implementation must include tests for:

- Lexer: comments, string escapes, integer/number literals.
- Parser: precedence, blocks, assignment targets, classes, functions, imports/exports.
- Type checker: invariance, nullable assignment, arrays, bytes, class nominal typing, table dynamic reads.
- Runtime: null sentinel, missing optional fields, class defaults, array indexing, bytes indexing and byte-value checks, function wrappers.
- Runtime: `int` accepts `2147483647` and `-2147483648`, rejects values outside signed 32-bit range, and raises overflow on arithmetic outside that range.
- ABI: import/export, host function wrapping, standard library module.
- Diagnostics: stable code, location span, expected/actual type.
- Host ABI: declared external imports, missing external rejection, runtime boundary checks.
- C FFI: declaration rules for `// @extern-c`, `// @c-struct`, `// @c-pointer`, type allowlists, and async rejection.
- C FFI: ABI mapping for scalars, Unicode strings via UTF-8, `bytes`, `// @c-struct`, `// @c-pointer`, and `null` returns.
- C FFI: runtime errors for library load, symbol lookup, embedded U+0000, invalid UTF-8, null strings, and null pointers; compile-time rejection for unsupported backends and invalid manifest policy.
- Stdlib: console, string, table, JSON, math, time.
