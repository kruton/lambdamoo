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
* lazy, per-program native generation for a guarded multi-type tier;
* native entry and return through the existing activation unwinder;
* JIT state reporting through `verb_info()` and wizard-only `jit_compile()`;
* read-only MIR output through `disassemble(..., "mir")`;
* hexadecimal machine-code output through `disassemble(..., "machine")`;
* runtime deoptimization profiling with reason and call-site aggregation;
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

The current native subset is substantially wider than the original integer
tier. It includes structured control flow, integer and unboxed-float arithmetic,
strings and lists, scatter assignment (including optional/default/rest items),
range and list loops, catch/finally markers, property reads and writes, selected
continuation-free built-ins, and dynamically tagged values with guarded native
consumers. Unsupported operations remain visible in IR so verifiers, dumps,
and future lowering passes can reason about bailout boundaries.

JIT eligibility is no longer the limiting metric: every verb in the current
Opal.db census can produce native code. The active frontend goal is now to
increase the percentage of entered activations that run to completion without
deoptimizing. New lowering work should therefore be selected from runtime
deoptimization frequency, not merely from syntactic database prevalence.

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

LambdaMOO tick accounting is per ticked operation. The current native tier
preserves this exactly by charging the same logical work as the interpreter
would have charged for the compiled region.

Later tiers may batch tick checks, but only when bailout can reconstruct an
activation at a valid resume point and preserve abort behavior for tick and
seconds exhaustion.

### 9.2 Built-In and Verb Calls

Built-ins can return, raise, call another verb, suspend, or abort. Verb calls
can push new activations and affect permissions, traceback, and suspension.

The current tier deoptimizes before general built-in calls, but directly lowers
a reviewed set of continuation-free built-ins and runtime operations.
These include `abs()`, `min()`, `max()`, `toint()`, `typeof()`, `length()`,
`index()`, `rindex()`, `ticks_left()`, `seconds_left()`, `time()`, `valid()`, and
`parent()`. Verb calls use a distinct VM-call exit that materializes the exact
`OP_CALL_VERB` stack and transfers to the canonical activation-push path without
counting the transfer as a deoptimization. The callee can therefore enter JIT,
but the caller currently resumes in the interpreter after the callee returns.
The interpreter continues to own `bi_func_pc`, `bi_func_id`, `bi_func_data`,
activation creation, suspension, and traceback behavior.

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

HIR and deoptimization maps now model catch and finally stack markers well
enough to enter these regions and reconstruct interpreter unwind state. Native
operations may execute inside them, but an operation whose error edge cannot be
proven equivalent still deoptimizes before the interpreter-visible boundary.
Avoid synthetic exceptional edges from every instruction until HIR models the
corresponding native handler transfer explicitly.

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

## 14. Current Status and Native-Completion Roadmap

### 14.1 Current implementation

The branch now has a complete AST-to-native pipeline with verified TAC, CFG,
dominators, SSA construction and destruction, bytecode resume anchors, exact
tick accounting, source locations, deoptimization maps, MIR generation, and
lazy machine-code compilation. JIT state is observable through
`verb_info()`, `jit_compile()`, and `disassemble()`; the test tooling includes
eligibility and runtime-deoptimization censuses.

All 6,319 verbs in the current Opal.db eligibility census compile successfully.
There are no remaining top-level `unsupported-program`,
`unsupported-value-types`, `invalid-bytecode-anchor`, or `invalid-ir`
rejections. Eligibility must remain at 100%, but it is now a regression metric,
not the roadmap driver.

The current native execution surface includes:

* integer and unboxed-double arithmetic, comparisons, branches, loops, and
  object-range iteration with interpreter-compatible errors and overflow;
* strings, lists, constants, indexing, slicing, construction, splicing,
  membership, comparison, concatenation, and dynamically tagged consumers;
* local, indexed, range, and selected property reads/writes with
  ownership-aware runtime helpers;
* required, optional/default, and rest scatter assignment;
* conditional expressions, `break`, `continue`, catch/finally markers, and
  canonical deoptimization boundaries for forks and suspension;
* native truth testing and exact return/deoptimization materialization for
  integer, object, float, string, list, error, `TYPE_NONE`, and dynamically
  tagged values;
* selected continuation-free built-ins, including resource-query, string,
  numeric, and object predicates; and
* safe deopt-before-call handling for general built-ins and a dedicated VM-call
  bridge for verb calls.

Recent tagged-value work allows runtime-typed scalar and complex values to flow
through concatenation, indexing, list construction, comparisons, branches,
properties, and returns. Runtime tags are propagated through SSA copies and
dynamic-result operations. Native consumers either dispatch on the tag or
deoptimize before touching a representation they do not support.

### 14.2 Measurement

Run the compile-eligibility census with:

```sh
./tests/census.sh Opal.db ./moo
```

Run the native-completion census with:

```sh
./tests/deopt-census.sh Opal.db ./moo 0 25
```

The last two arguments select the inclusive object range. The emergency
workload may suspend before exhausting that range, so compare runs made with the
same database, object range, and server configuration. Record both entered and
completed activation counts: a lower raw deopt count can otherwise hide reduced
coverage.

A codepoint.db sample over objects #0 through #50 before the VM-call bridge
entered 1,418 compiled activations, completed 236 natively, and deoptimized
1,131. Its distribution was:

* 363 unsupported operations (32.10%);
* 345 verb calls (30.50%);
* 206 built-in calls (18.21%);
* 162 type guards (14.32%);
* 38 range operations (3.36%);
* 15 arithmetic guards (1.33%); and
* one property write and one branch-type mismatch.

These figures are workload-specific. They show that expanding complete native
execution now depends primarily on operation/call coverage and guard quality,
not on compiling more verb bodies.

After the first VM-call bridge stage, an Opal.db objects #0 through #25 sample
entered 130 compiled activations, completed 27 natively, and recorded 68
deoptimizations. No `verb_call` deoptimizations remained; the 68 exits comprised
27 built-in calls, 16 unsupported operations, 15 type guards, eight arithmetic
guards, and two range operations. The task suspended before exhausting the
range, so this confirms removal of the verb-call reason but is not a performance
comparison with the earlier codepoint.db workload.

### 14.3 Priorities for programs that remain entirely native

1. **Classify unsupported operations by HIR operation and call site.**
   Extend `tests/deopt-census.sh` output so the 363 generic
   `unsupported_operation` exits are attributable to an exact HIR operation,
   bytecode opcode, and source site. Start with the high-frequency event-handler
   and controls paths. Do not implement an operation until its resume stack,
   error behavior, tick charge, and ownership contract are known.

2. **Resume native callers after ordinary verb calls.**
   The first bridge stage now materializes the canonical `OP_CALL_VERB` stack,
   pushes a normal activation, and dispatches an eligible callee through JIT
   without reporting a caller deoptimization. Add a native continuation entry
   for the caller's `RESUME_PHASE_AFTER_CALL` key so a normal callee return can
   restore the result and live values and continue in native code. Retain the
   interpreter continuation for suspension, traceback, recursion, permissions,
   and a callee that deoptimizes. Add tail calls only after activation
   replacement is modeled. This remains the largest likely improvement to
   whole-program native completion.

3. **Replace the built-in name allowlist with effect metadata.**
   Record argument prototypes and effects such as pure, allocation, possible
   errors, permission checks, calls, suspension, abort, continuation state, and
   ownership transfer. Use the metadata both for type inference and for deciding
   whether a built-in can run through a native call bridge. Prioritize the
   highest-frequency continuation-free built-ins from the census. Never inline a
   built-in that can return `BI_CALL`, `BI_SUSPEND`, or `BI_ABORT` without a
   modeled continuation.

4. **Make every lowered boundary independently resumable.**
   A deopt map attached to a synthesized operation must reconstruct the operand
   stack expected by its bytecode PC, not merely the operation's logical SSA
   operands. Add verifier checks and negative tests for built-in argument-list
   construction, scatter, property/index write-back, range operations, caught
   errors, and other multi-bytecode lowerings. This prevents a guard miss from
   resuming with a well-typed but structurally invalid interpreter stack.

5. **Reduce type guards using consumer constraints and tagged dispatch.**
   Report local/value identity and expected/actual tags for the remaining guard
   failures. Seed only invariant runtime slots, preserve `TYPE_NONE` for
   uninitialized user locals, and infer types backward from exact built-in and
   operation contracts. When multiple types are legitimate, carry the runtime
   tag and add a guarded consumer instead of guessing a static type. Never
   weaken a guard merely to improve census numbers.

6. **Finish dynamic complex-value propagation and ownership accounting.**
   Audit every instruction that can produce a runtime-selected type—property
   reads, list indexing, joins, calls, and overloaded arithmetic—and ensure its
   tag reaches locals, copies, returns, and deopt maps. Add explicit
   borrowed/owned/immortal states so native temporaries are released on normal,
   error, and deopt exits. Include repeated-execution leak tests for strings,
   lists, properties, and call results.

7. **Lower the hottest remaining range and caught-error paths.**
   The current sample reaches range operations after earlier string/list work.
   Add native list and string range extraction/assignment only where bounds,
   Unicode indexing, allocation quotas, source locations, and catch transfer are
   exact. A caught error should enter its native handler only after stack-marker
   and tick equivalence are tested; otherwise deopt before the operation.

8. **Compile fork vectors and support native re-entry.**
   Make code-unit identity explicit in entry and deopt maps, compile fork vectors
   independently, and retain bytecode fallback for serialized tasks. A fork
   statement may remain a scheduling boundary while its body becomes eligible
   for native entry. Add checkpoint/reload and suspended-task tests before
   enabling native resume.

9. **Optimize only after coverage boundaries are trustworthy.**
   First remove redundant guards and repeated local/tag loads. Then consider
   block-level tick batching, call-site specialization, and MIR optimization
   levels. Every optimization must preserve exact timeout, source-location,
   error, and deoptimization behavior and be measured against interpreter and
   JIT O0 baselines.

10. **Expand differential and database-scale validation continuously.**
    Add generated programs covering every runtime tag at every tagged consumer,
    forced guard failures at synthesized bytecode anchors, nested catches,
    recursion, permissions, repeated complex-value execution, checkpoint/reload,
    and suspension. Track native completion percentage, reason distribution,
    compile time, code size, and execution time for stable workloads.

### 14.4 Definition of a completed coverage milestone

A new operation or call path is complete only when:

* its successful path matches the interpreter's value, ownership, ticks, and
  source location;
* every type, bounds, quota, permission, arithmetic, and timeout failure either
  matches the interpreter natively or deoptimizes before side effects;
* every deopt target reconstructs the exact bytecode stack and locals expected
  at that PC;
* catch/finally and suspension behavior remain canonical;
* focused native/reference tests include negative runtime-tag cases;
* the eligibility census has no regression; and
* a stable runtime census demonstrates movement to a later substantive boundary
  or an increased native-completion rate.
