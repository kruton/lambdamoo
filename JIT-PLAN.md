# Architecture Specification: JIT Compiler for LambdaMOO

## 1. Executive Summary

This document describes the current long-term compiler plan for LambdaMOO.
The active frontend is AST-first:

```text
source/list input
  -> parser
  -> AST
  -> compiler orchestration layer
       -> existing bytecode backend -> Program
       -> HIR frontend -> TAC -> CFG -> dominators/frontiers -> SSA
       -> optimizations -> MIR/native code
```

The interpreter and database compatibility boundary is still bytecode-based.
Compiled code must always be able to deoptimize to canonical interpreter state:
`Program *`, bytecode vector, bytecode PC, `error_pc`, runtime locals, stack,
`temp`, and any built-in continuation state. The AST-first pipeline is the
compiler construction path; bytecode remains the persistence and fallback path.

This direction avoids lowering to bytecode and raising it back into a higher
level IR. The bytecode decoder can still be added later as a compatibility or
optimization frontend, but it is no longer the v1 compiler frontend.

## 2. Core Principles

* Preserve current `parse_program()` behavior and database compatibility.
* Keep bytecode generation as the source of executable interpreter programs.
* Build JIT analysis from the AST while the compiler still owns it.
* Represent unsupported language features explicitly and fall back cleanly.
* Attach source line information throughout HIR/TAC/CFG/SSA for diagnostics.
* Treat every future native safepoint as a place where interpreter state can be
  reconstructed exactly.
* Prefer small verifier-backed IR steps over a large native-code jump.

## 3. Completed Foundation

The current branch has already established the first compiler backbone:

* arena allocation for AST/compiler transient state;
* compiler orchestration split around parsing, bytecode generation, and HIR
  hooks;
* ResumePoint groundwork for serialized suspended activations;
* structured HIR construction from the AST;
* TAC lowering for constants, locals, arithmetic, comparisons, branches,
  returns, and unsupported operations;
* gated TAC dumping behind `HIR_DUMP_TAC`;
* TAC verifier and negative tests;
* direct C unit test harness for the compiler/HIR subsystem;
* source line propagation through TAC;
* CFG construction from TAC;
* CFG verifier and negative tests;
* dominator tree using Cooper's iterative algorithm;
* dominance frontier computation;
* initial SSA construction over CFG;
* SSA verifier, including phi-shape negative tests;
* positive SSA phi tests for `if`/`else` joins and `while` loop backedges;
* critical-edge splitting and SSA destruction;
* explicit tick operations retained through native lowering;
* an optional `--enable-jit` extension using vendored MIR 1.0.0 at O0;
* lazy, per-program native generation for a guarded integer-only tier;
* native entry and return through the existing activation unwinder;
* JIT state reporting through `verb_info()` and wizard-only `jit_compile()`;
* read-only MIR output through `disassemble(..., "mir")`;
* disposable JIT state that is rebuilt from source after database reload.

## 4. Phase 1: AST to HIR

HIR is the structured compiler IR derived directly from the parser AST. It
should stay close enough to the language to preserve semantics, while exposing
control flow and values enough for lowering.

HIR should model:

* integer and float constants;
* literal values;
* local variable reads and writes;
* `temp` register use;
* arithmetic and comparison expressions;
* assignment;
* conditional branches;
* loops;
* returns;
* unsupported or bailout-first expressions/statements;
* source line information on every lowered operation.

The initial supported subset is intentionally conservative:

* integer addition, subtraction, multiplication, and comparisons;
* local loads and stores;
* simple `if`/`else`;
* simple `while`;
* returns when no active `finally`/`except` state complicates unwinding.

The v1 unsupported or bailout-first set should include:

* verb calls;
* built-in calls;
* property access and mutation;
* fork creation;
* try/except/finally;
* scatter assignment;
* list/string construction and mutation;
* WAIF-specific paths;
* any operation that can suspend, push an activation, or depend on complex
  interpreter stack markers.

Unsupported operations should remain visible in IR so verifiers, dumps, and
future lowering passes can reason about bailout boundaries.

## 5. Phase 2: TAC

TAC is the normalized pre-CFG IR. It makes expression evaluation order explicit
and assigns intermediate results to compiler temporaries.

TAC should provide:

* one explicit result for each value-producing instruction;
* local loads and stores;
* explicit labels, jumps, conditional branches, and returns;
* unsupported instructions for bailout-first operations;
* source line numbers on generated instructions;
* a verifier that catches undefined temps, duplicate defs, malformed control
  instructions, and invalid local references.

TAC is not the final optimizer IR. It is the stable handoff into CFG and SSA.

## 6. Phase 3: CFG

Build CFG blocks from TAC:

* start a block at entry, labels, branch targets, and fallthrough after
  terminators;
* retain labels as instruction anchors where useful for dumps and diagnostics;
* compute predecessor and successor sets;
* represent unsupported operations as blocks that force interpreter fallback;
* verify successor/predecessor symmetry and terminator shapes.

The CFG should remain conservative. Complex runtime constructs can become
single unsupported regions until the compiler has exact state reconstruction
for them.

## 7. Phase 4: Dominators and SSA

### 7.1 Dominator Tree

Use Cooper's iterative data-flow algorithm:

1. Compute reverse postorder over reachable CFG blocks.
2. Calculate immediate dominators for every reachable block.
3. Iterate until the IDOM array stops changing.
4. Leave unreachable blocks explicit but not part of the reachable dominator
   tree.

### 7.2 Dominance Frontiers

Compute dominance frontiers from the dominator tree. These frontiers drive phi
placement for locals and compiler temporaries whose definitions can reach a
join.

### 7.3 Phi Placement

Use iterated dominance frontiers for SSA variables:

* place phis at control-flow joins where multiple definitions may reach;
* include loop headers when a loop-carried definition reaches the next
  iteration;
* ensure phi argument count and predecessor blocks match the CFG exactly.

### 7.4 Register Renaming

SSA construction should use dominator-tree preorder traversal:

1. Maintain active version stacks for each local and compiler temporary.
2. Assign new versions at definitions and phi nodes.
3. Rewrite reads to the current active version.
4. Fill successor phi arguments from the current version stack.
5. Pop versions when backtracking out of a dominator subtree.

If the current SSA builder only handles a subset of this behavior, completing
full register renaming is the next SSA correctness milestone.

### 7.5 SSA Destruction

CPUs do not have phi instructions. Before MIR/native lowering, destroy SSA by
inserting moves along predecessor edges. Critical edges may need to be split so
phi moves can be placed without changing branch semantics.

## 8. Phase 5: Optimization Passes

### 8.1 Sparse Conditional Type Propagation

Use Wegman-Zadeck style sparse conditional propagation adapted to LambdaMOO
type tags:

* constants start with precise types;
* conflicting phi inputs degrade to `TYPE_ANY`;
* unreachable branches should not pollute downstream phi types;
* operations that can raise `E_TYPE`, `E_RANGE`, `E_DIV`, `E_QUOTA`, or
  `E_FLOAT` must retain the same observable behavior as the interpreter.

### 8.2 Simple Canonical Optimizations

Before native code, add small verifier-backed optimizations:

* constant folding for pure arithmetic/comparisons;
* dead temp elimination;
* unreachable block pruning after branch simplification;
* redundant local load/store cleanup when ownership is unaffected.

Each optimization should preserve line/resume metadata or explicitly remap it.

### 8.3 Guarded Native Operations

If an SSA value degrades to `TYPE_ANY`, native specialized operations must be
guarded. Guard failure should deoptimize to the interpreter at the attached
ResumePoint/ResumeID.

## 9. Phase 6: Runtime Semantics

### 9.1 Tick Accounting

LambdaMOO tick accounting is per ticked operation. The first native tier should
preserve this exactly by charging the same logical work as the interpreter would
have charged for the compiled region.

Later tiers may batch tick checks, but only when bailout can reconstruct an
activation at a valid resume point and preserve abort behavior for tick and
seconds exhaustion.

### 9.2 Built-In and Verb Calls

Built-ins can return, raise, call another verb, suspend, or abort. Verb calls
can push new activations and affect permissions, traceback, and suspension.

For v1:

* deopt before built-in and verb calls;
* let the existing interpreter perform the call;
* keep `bi_func_pc`, `bi_func_id`, and `bi_func_data` as interpreter-owned
  continuation state.

Built-in inlining must be opt-in and metadata-driven. A built-in may be inlined
only if its registered contract declares it continuation-free:

* it cannot return `BI_CALL`;
* it cannot return `BI_SUSPEND`;
* it cannot return `BI_ABORT`;
* it has no private `bi_func_data`;
* its error behavior and ownership behavior are fully modeled by the JIT.

Continuation-capable built-ins must remain runtime call boundaries.

### 9.3 Exceptions and Finally

The current interpreter implements exception and finally behavior through
runtime stack markers (`TYPE_CATCH`, `TYPE_FINALLY`) and `unwind_stack()`.
This is not equivalent to native exception tables alone.

For v1:

* bail out before try/except/finally regions;
* preserve stack-marker semantics in the interpreter;
* avoid drawing synthetic exceptional edges from every instruction until HIR
  explicitly models stack markers and unwind behavior.

Native landing pads may be added later as an optimization, but they must still
materialize the same activation and stack-marker state expected by
`unwind_stack()`.

## 10. Phase 7: Resume, Deoptimization, and Persistence

### 10.1 Resume Anchoring

Suspended tasks must survive database checkpoints, server restarts, compiler
updates, and the absence of JIT code. Raw native pointers and native PCs must
never be serialized.

A resume anchor identifies a point where all live execution state can be
represented in canonical interpreter activation form:

* `Program *` snapshot for the running activation;
* bytecode vector identity;
* bytecode `pc`;
* `error_pc`;
* `rt_env`;
* runtime stack contents and depth;
* `temp`;
* built-in continuation state, when present.

AST/HIR/SSA locations must map back to bytecode resume anchors before native
execution is allowed. For v1, resume resolves to bytecode PC and execution
continues in the interpreter.

### 10.2 Deep Deoptimization

When JIT code must suspend, call unsupported runtime behavior, hit a guard
failure, or abort:

1. Trap to a C deoptimization runtime.
2. Use the JIT deopt map for the current native location.
3. Materialize each native frame into a normal `activation`.
4. Populate `pc`, `error_pc`, resume metadata, `rt_env`, runtime stack, `temp`,
   and ownership-correct `Var` values.
5. Continue in the interpreter or serialize the VM if the operation suspended.

Serialized activations preserve language state, not JIT state. JIT state is
disposable and must be reconstructable from the canonical activation.

### 10.3 Future Native Resume

On database load, a future JIT may resume natively only if:

* the relevant program/vector is compiled;
* the compiled code advertises support for the activation's resume anchor;
* the compiler has a native resume stub for that anchor;
* the canonical activation can be converted into the native frame layout.

If any condition fails, resume in the interpreter.

## 11. Phase 8: Memory Safety and Reference Ownership

LambdaMOO is reference-counted. The JIT should use deopt and ownership maps,
not a tracing-GC model.

### 11.1 Reference Count Elision

SSA and escape analysis can eventually prove which values are purely local to
compiled code. Until that proof exists, prefer conservative `var_ref()` and
`free_var()` behavior at boundaries.

Only elide refcount operations when the compiler can prove:

* the value does not escape to an object property, list/string storage, another
  activation, or the interpreter;
* all bailout paths transfer ownership correctly;
* all error paths free owned values exactly once.

### 11.2 Deopt and Ownership Maps

At every trapping or bailout-capable native instruction, the JIT must know how
to reconstruct interpreter `Var` values:

* which logical locals/stack slots are live;
* whether each value is immediate, borrowed, owned, or needs `var_ref()`;
* where each value currently lives: register, native stack slot, constant, or
  materialized runtime object;
* which cleanup actions are required if deopt aborts partway through.

These maps are also the foundation for future native resume stubs.

## 12. Optional Bytecode Frontend

A bytecode decoder is no longer required for v1 HIR construction, but it may
still be valuable later for:

* compiling old programs when AST metadata is unavailable;
* validating AST-derived resume mapping against bytecode PCs;
* comparing interpreter bytecode behavior with HIR lowering;
* compiling conservative bytecode-only regions.

If added, the decoder should carry:

* bytecode vector identity (`MAIN_VECTOR` or fork vector index);
* bytecode PC;
* opcode or extended opcode;
* decoded operands using `numbytes_label`, `numbytes_literal`,
  `numbytes_fork`, `numbytes_var_name`, and `numbytes_stack`;
* stack delta and maximum stack requirements;
* tick cost according to `COUNT_TICK()` and `COUNT_EOP_TICK()`;
* whether the instruction is a resume/deopt/safepoint candidate.

The decoder should be a secondary frontend into TAC/CFG, not the primary
architecture for the current AST-first plan.

## 13. Gotchas and Landmines

* **Program snapshots:** Running activations hold refcounted `Program *`
  snapshots. Suspended activations must serialize that running program, not
  look up the current verb slot, because the verb may have been reprogrammed.
* **Bytecode compatibility:** Legacy suspended tasks store source plus bytecode
  PCs. If compiler bytecode layout changes, old PCs can become invalid. Resume
  migration exists to make this boundary explicit and versioned.
* **AST lifetime:** AST-derived JIT metadata must be generated before the AST
  is freed, or the AST must become part of a deliberate program-lifetime
  storage design.
* **ASLR and serialization:** Never serialize a raw pointer, native frame
  address, or native PC.
* **setjmp/longjmp:** Generic exception helpers use `setjmp`/`longjmp`.
  JIT-owned transient state must be released through explicit deopt/cleanup
  paths before code can enter runtime paths that may longjmp.
* **Phi lowering:** Destroy SSA before MIR lowering by inserting moves at
  predecessor edges.
* **Critical edges:** SSA destruction and some instrumentation may require CFG
  edge splitting.
* **`TYPE_ANY` fallback:** If type propagation cannot prove a specialized type,
  emit a guard or stay in the interpreter.

## 14. Near-Term Roadmap

Completed in the first native-code milestone:

* short-circuit `&&` and `||` lowering without eager right-operand evaluation;
* definition-dominates-use SSA verification with focused negative tests; and
* differential native/reference recipe tests for branching, phi copies,
  guards, and resource-limit aborts;
* sparse integer type and constant propagation; and
* safe constant folding, constant-branch simplification, and unreachable-block
  pruning;
* explicit wrapping integer arithmetic and error semantics shared by the
  interpreter and compiler; and
* checked native integer division and modulo, including division by zero and
  the minimum-integer divided by negative-one case; and
* checked native integer exponentiation and shifts, plus bitwise integer
  operators; and
* validated bytecode resume anchors carried from AST code generation through
  HIR, SSA, optimization, and native recipes; and
* canonical entry deoptimization maps; and
* deep deoptimization maps that reconstruct updated integer locals, nested
  operand stacks, bytecode and error PCs, and exact tick accounting from SSA
  values on post-entry guard failure;
* cold native abort and error exits that restore exact bytecode/error PCs and
  carry source lines without adding location stores to tick hot paths;
* guarded integer locals whose values enter through the runtime environment; and
* checked native list and argument-list indexing with bounds checking and
  element-type guards; and
* list destructuring (scatter assignment) and list construction/splicing lowered
  to TAC/SSA with bytecode anchors and native destructuring execution;
* deopt-before-call boundaries for built-in functions with seamless runtime state
  handoff at `OP_BI_FUNC_CALL`; and
* direct native inlining for pure continuation-free built-ins (`abs()`, `min()`,
  `max()`, `toint()`, `typeof()`, `length()`) eliminating deopt boundaries for
  pure operations; and
* direct native lowering for property reads (`obj.prop`) and property assignments
  (`obj.prop = rhs`) with exact deopt maps and type-safe interpreter stack restoration;
* range-based `for` loop lowering (`for i in [start..end]`) with exact opcode
  tick accounting and interpreter stack reconstruction; and
* integer list iteration lowering (`for x in (list)`) with guarded list access,
  bytecode anchors, and interpreter fallback for non-integer elements; and
* conditional expressions (`EXPR_COND` `c ? t | f`) with bytecode anchors,
  nested evaluation, and clean SSA phi join; and
* `break` and `continue`, including labeled exits from nested `while`, range,
  and list loops without losing bytecode resume anchors; and
* range expressions (`base[from..to]`) for list and string slicing, plus range
  assignments (`base[from..to] = rhs`), lowered through exact deoptimization and
  interpreter stack reconstruction boundaries; and
* deopt-before-call boundaries for verb calls (`obj:verb(args...)`), preserving
  argument stacks, permissions, traceback state, and activation-push semantics; and
* guarded SSA values for object (`TYPE_OBJ`) scalars, including object range
  loops, literal representations, comparisons, and exact deoptimization/return
  semantics; and
* native representation for double-precision, unboxed floating-point
  (`TYPE_FLOAT`) values, including local loads, arithmetic, numeric error exits,
  comparisons, branches, returns, and deoptimization; other configured float
  representations currently make affected verbs ineligible; and
* ownership-aware string values (`TYPE_STR`) and non-integer list elements
  (`TYPE_OBJ`, `TYPE_FLOAT`, `TYPE_STR`, `TYPE_LIST`) so indexing, iteration,
  locals, returns, and deoptimization preserve reference counts; and
* exception and `finally` stack markers (`TYPE_CATCH`, `TYPE_FINALLY`) modeled
  before lowering catch expressions, `try-except`, and `try-finally` statements,
  with relocated handler PCs and pre-entry deoptimization boundaries preserving
  exact interpreter stack-unwind and `finally` semantics; and
* fork and suspension deoptimization boundaries (`HIR_TAC_DEOPT`) modeling time
  expressions, argument stacks, and exact bytecode resume anchors, ensuring
  native execution materializes every continuation field required by serialized
  activations; and
* length expression (`$`, `EXPR_LENGTH`) lowering in indexed (`expr[$]`) and range
  (`expr[from..$]`) contexts, maintaining context-sensitive base value tracking
  and native length extraction; and
* expanded differential validation harness comparing native and reference execution
  across values, errors, source locations, ticks, full deoptimization state (including
  bytecode PCs and runtime operand stacks), reference ownership, nested control flow,
  forced fallbacks across all supported boundaries, and a continuous microbenchmark.

The next reviewable compiler milestones, in dependency order, are:

1. Finish common core-expression and destructuring coverage. Add membership
   (`in`) first, then optional, default, and rest scatter assignments
   (`{a, ?b = default, @rest} = expr`) in separate commits, with exact evaluation
   order, error behavior, ticks, and deoptimization stacks. These features use
   the value and ownership machinery already present without first requiring a
   new runtime object model.
3. Make code-unit identity explicit in native entry and deoptimization maps,
   then compile fork vectors independently. A fork statement should remain an
   interpreter boundary, but its separately compiled body should be eligible
   for native entry without confusing main-vector bytecode PCs, resume anchors,
   or serialized activations.
4. Add shared, ownership-audited runtime helpers for complex-value semantics,
   then use them to broaden native string and nested-list operations and to
   integrate WAIF (`TYPE_WAIF`) references and property access. Keep pointer
   identity out of language equality, truth, and ordering semantics, and test
   every helper on success, error, and deoptimization paths.
5. Define declarative built-in effect metadata (pure, may raise, may allocate,
   may call, may suspend, ownership behavior) and make JIT eligibility consume
   it. Only then expand fast paths for high-frequency, continuation-free
   built-ins; all other built-ins remain deopt-before-call boundaries.
6. Add profile-guided, semantics-preserving optimization only after the wider
   differential suite is green: redundant guards and local traffic first,
   followed by block-level tick batching where exact timeout and source-location
   behavior can be proven. Measure each optimization against interpreter, JIT
   O0, and optimized JIT runs.
7. Finish with database-scale validation and performance work: multi-verb and
   suspended-task workloads, checkpoint/reload tests, fuzzed interpreter/JIT
   comparison, compile-time and code-size accounting, and benchmarks that
   identify the next coverage or optimization bottleneck.
