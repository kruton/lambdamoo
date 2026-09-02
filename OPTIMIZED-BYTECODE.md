# HIR-Optimized Bytecode Backend Analysis

## Objective

LambdaMOO can use the existing AST-to-HIR compiler pipeline to produce a
second, compact execution tier: optimized bytecode interpreted by `run()`.
This would reuse control-flow, SSA, type, constant, liveness, and effect
analysis without paying for MIR construction, executable memory, native ABI
state, or native deoptimization metadata.

The useful version of this design is not simply "print the current JIT IR as
old bytecode." The current pipeline has two distinct semantic levels:

```text
AST -> HIR -> TAC -> CFG -> SSA -> semantic optimizations
                                      |
                                      +-> stackify -> optimized bytecode
                                      |
                                      +-> native specialization -> JIT IR
                                           -> MIR -> machine code
```

The bytecode branch must split before native type guards, unboxed values,
ownership-transfer assumptions, native call frames, and deoptimization exits
are introduced. Ordinary bytecode operations retain dynamic language
semantics, so an integer add proved by HIR may use the existing `OP_ADD`, but
it must not inherit a native guard whose failure means "resume the original
interpreter."

## What Can Be Reused Today

`compile_ast_to_program()` already keeps the AST alive while it builds both the
canonical `Program` and the complete HIR pipeline. It constructs TAC, CFG,
dominators, SSA, runs SSA constant optimization, destroys SSA, and only then
creates the JIT program. An optimized-bytecode backend can run at this same
point, before `hir_context_free()` releases the compiler arena.

The following machinery is directly useful:

* structured control flow and explicit expression evaluation order in HIR and
  TAC;
* CFG construction, critical-edge handling, dominators, and SSA construction;
* constant and value analysis;
* explicit tick operations and bytecode/source anchors;
* out-of-SSA parallel copies;
* the existing literal, variable-name, fork-vector, and `ResumePoint` data
  models; and
* the existing stack bytecode interpreter and its dynamic error behavior.

Not all optimizations currently described as HIR optimizations are actually
reusable yet. Several type, ownership, last-use, guard, reconstruction, and
effect passes operate on `JITProgram` after `hir_create_jit_program()`. Reusing
them requires separating their language-level facts from their native lowering
actions. For example, type inference is reusable; inserting a native type
guard and assigning an owner home are not.

The first refactoring should therefore define a backend-independent analysis
result over SSA values and instructions. Native lowering may consume all of
it. Bytecode lowering should consume only facts that prove a transformation
preserves ordinary bytecode behavior.

## Why Replacing the Canonical Program Is Risky

The current `Program` is more than an instruction vector:

* activations retain a refcounted snapshot of it;
* bytecode PCs and `error_pc` identify interpreter state;
* `find_line_number()` and the decompiler derive source behavior from its
  bytecode shape;
* verb calls and built-in continuations save operand-stack state at exact PCs;
* suspended tasks serialize a source form produced by unparsing the running
  `Program`; and
* `ResumeKey` maps serialized language-level continuation sites back to a
  vector, PC, error PC, and stack layout after reload.

General SSA optimization changes instruction order, stack shape, and PCs.
Feeding that layout to the existing decompiler is also unsafe: the decompiler
expects patterns emitted by `code_gen.c`, not arbitrary equivalent stack code.
Consequently the first implementation should retain the existing `Program` as
the canonical source, persistence, and resumption object and attach optimized
bytecode as a disposable runtime sidecar. Like native code, the sidecar is
regenerated from source and is never written to the database.

This has one important cost: every operation that can expose or preserve an
activation must either have an optimized continuation description or return to
canonical state. The existing native deoptimization and continuation work
solves much of the same state-mapping problem, but optimized bytecode should
use compact bytecode-specific maps rather than native value-location maps.

## Proposed Representation

Add a backend-neutral optimized code object owned by `Program`, separate from
`JITProgram`. A code unit should contain:

* an optimized byte vector and its maximum operand-stack depth;
* literal and fork references, preferably into the canonical `Program` rather
  than duplicated values;
* an optimized-PC-to-source-location table;
* an optimized-PC-to-canonical-state map at every observable boundary;
* a canonical resume key for every call, built-in continuation, suspension,
  catch/finally transition, and task boundary;
* explicit tick-accounting records; and
* enough stack-map information to verify every control-flow edge.

Do not add synthetic user locals merely to spill SSA values. Locals are
observable through stack introspection and are serialized by name and value.
The backend has three safe choices, in order of preference:

1. schedule expression trees so temporary values stay on the operand stack;
2. rematerialize cheap, pure values when this preserves ticks and errors; or
3. add explicitly hidden interpreter scratch slots that are not part of
   `rt_env`, variable names, introspection, or persistence and that are
   materialized away at canonical boundaries.

The first milestone should support only stackifiable regions and decline an
optimization when it would require hidden spills. This keeps the runtime and
ownership model small. A later backend can add scratch slots after measuring
how often stackification fails.

The optimized bytecode may initially use the existing opcode set. New internal
opcodes or superinstructions are worthwhile only when they reduce dispatch or
code size materially. They must be marked transient and must never reach the
database decompiler.

## Lowering Out of SSA

Lowering requires a stack scheduler, not the MIR emitter. For each CFG block it
must:

1. choose and verify one operand-stack shape at block entry;
2. schedule each SSA instruction so operands are on top of the stack in the
   interpreter's required order;
3. emit ordinary dynamic opcodes for language operations;
4. implement parallel copies on predecessor edges using source locals, stack
   shuffles, or proven rematerialization;
5. empty or canonicalize the stack at joins where predecessor schedules cannot
   agree; and
6. resolve labels and choose one-, two-, or four-byte operand widths using the
   existing `code_gen.c` fixup model.

An attractive initial restriction is to keep source local loads and stores in
their original semantic order and optimize expression values within basic
blocks. This permits constant folding, dead pure-expression removal, branch
simplification, strength reduction, and some redundant-load elimination while
avoiding a general SSA register allocator for a stack machine.

After emission, a verifier should decode the result independently and prove:

* every branch target is an instruction boundary;
* all incoming edges agree on stack depth and slot kinds;
* no read observes an uninitialized local or scratch slot;
* catch/finally marker layout is valid;
* every observable boundary has a canonical mapping;
* maximum stack depth is accurate; and
* every semantic tick and possible error point is represented in order.

## Ticks, Errors, and Observable Ordering

Tick preservation is the hardest semantic constraint. Interpreter ticks are
currently encoded by opcode ranges (`COUNT_TICK()` and `COUNT_EOP_TICK()`), and
MOO code can observe the remaining budget. Constant folding or fusing five
operations into one must not silently remove four ticks or move timeout past a
side effect.

HIR already carries explicit tick operations. The bytecode backend should make
them authoritative instead of deriving optimized-tier cost solely from the
chosen opcode. Two implementation strategies are possible:

* add a transient `CHARGE_TICK`/`CHARGE_TICKS` encoding and designate optimized
  semantic opcodes as non-charging; or
* annotate optimized instructions with a compact side table consumed by the
  dispatch loop.

A side table keeps instruction bytes smaller when most operations have the
usual cost. An explicit opcode makes verification and debugging simpler.
Whichever is chosen, batching ticks is legal only when no intermediate timeout,
`ticks_left()`, error, call, or side effect can distinguish the batching. The
safe default is to preserve each original tick boundary.

Likewise, an optimization may remove a potentially failing operation only when
HIR proves both its result and the absence of its error. Reordering is allowed
only when errors, permissions, quota checks, allocation failure behavior,
reference ownership, and side effects remain observationally equivalent.
Source line reporting should use the side table rather than attempting to make
optimized byte offsets look like canonical byte offsets.

## Integration with `run()`

The least invasive execution model adds an execution-code selector and
optimized PC to an activation while keeping `activation.prog` canonical.
`run()` selects either `prog->main_vector`/fork vector or the transient
optimized vector, but all source lookup, serialization, and program identity
continue to use `prog`.

At a simple successful instruction, execution remains entirely in the
interpreter loop. At a normal verb call, the caller can retain an optimized
resume PC if the call site has a verified continuation map. Returning then
selects the optimized vector and continues. This needs no native frame and no
MIR ABI; it is an ordinary interpreter activation with an additional transient
code identity.

Before suspension, database dump, stack introspection that exposes PCs or
locals, or any boundary without a verified optimized continuation, convert the
activation to its canonical `ResumeKey`, PC, error PC, locals, stack, and
`temp`. Clear the optimized-code selector before entering existing persistence
or introspection code. This is bytecode-tier deoptimization, but its values are
already boxed `Var`s in interpreter-owned storage, so it needs only stack/local
placement maps, not native register locations, runtime tags, or ownership
homes.

Exceptions need precise treatment. Either optimized execution preserves the
canonical catch/finally stack representation directly, or it canonicalizes
before any instruction that may raise into a protected region. The latter is a
reasonable first milestone. Once exceptional edges and marker layouts are
verified, catches can remain in optimized bytecode.

## Optimization Scope

The backend can profitably reuse or add these backend-independent passes:

* constant propagation and folding with preserved tick records;
* unreachable-block and dead pure-instruction elimination;
* branch folding and jump threading;
* redundant local-load elimination within regions where calls, introspection,
  and alias-forming operations cannot intervene;
* copy propagation and phi simplification;
* common-subexpression elimination for proven pure, non-failing operations;
* strength reduction, including power-of-two integer modulus/division where
  signed semantics and error behavior are proven equivalent;
* guard fact propagation as type information, without emitting native guards;
* dead-local-store elimination when no introspection, suspension, or exceptional
  path can observe the old environment; and
* block layout and fallthrough selection.

Native-only transformations must stay out of this branch: unboxing, borrowed
or consumed `Var` ownership, owner homes, register allocation, native calling
conventions, deopt-value pruning based on native locations, and guard exits.
Bytecode values remain ordinary owned/borrowed `Var`s according to the existing
opcode contracts.

The largest speedups are likely to require superinstructions after the semantic
optimizer works. Examples include local-load plus arithmetic plus local-store,
constant-index operations, compact calls with fixed argument counts, and fused
loop backedges with tick checks. These reduce dispatch while retaining boxed
semantics. They should be selected from interpreter profiles, not added solely
because HIR can express them.

## Recommended Delivery Sequence

1. **Separate reusable analysis.** Move type, effect, non-exit, and purity facts
   needed by both backends into HIR/SSA-owned results. Keep native ownership and
   guard construction in JIT lowering.
2. **Build a read-only stackification prototype.** Lower straight-line,
   stackifiable basic blocks to an abstract bytecode listing and verify stack
   shapes, ticks, errors, and source anchors without executing it.
3. **Emit a transient sidecar for leaf regions.** Use only existing opcodes and
   canonicalize at calls, built-ins, exceptions, suspension, and introspection.
   Fall back to canonical bytecode for any unrepresentable program.
4. **Integrate tier selection into `run()`.** Add explicit code identity and
   optimized PC, source mapping, accounting, and complete cleanup when a
   `Program` is freed or recompiled.
5. **Add optimized call continuations.** Resume an optimized caller after an
   interpreted or optimized callee without materializing unrelated frames.
6. **Expand control flow and exceptions.** Support loops, joins, forks, and
   protected regions only after the bytecode verifier covers their stack and
   marker invariants.
7. **Profile before adding superinstructions.** Record optimized entries,
   completions, canonicalizations by reason, bytes emitted, dispatch count,
   compile time, and execution time. Add fused opcodes for measured hot
   sequences.
8. **Choose policy.** Permit interpreter-only builds to use optimized bytecode,
   and optionally use it as the warm-up/fallback tier before native compilation.

Each phase should keep canonical bytecode available. A verifier failure or
unsupported lowering must discard only the optimized sidecar and leave normal
execution unchanged.

## Initial PC-Stable Implementation

The first implementation uses a deliberately narrower representation than the
eventual stackifier. The common SSA constant pass now produces a transient
`HIROptimizationPlan` while applying the same mutations consumed by native
lowering. The plan records proven integer results at their canonical bytecode
anchors. Bytecode lowering copies the canonical main vector and replaces only
eligible same-width arithmetic and comparison instructions with
`OP_OPTIMIZED_VALUE`; a sorted side table supplies the result, operand-pop
count, and number of trailing bytes belonging to an original extended opcode.

This form has useful safety properties:

* optimized and canonical PCs, branches, stacks, resume points, and source
  locations remain identical;
* the replacement remains a ticked opcode, including when it skips a formerly
  extended operation;
* operands remain boxed interpreter `Var`s and are released exactly where the
  original operation released them;
* canonical bytecode remains the input to unparsing and persistence; and
* the MIR backend receives the same optimized out-of-SSA program as before.

The native-only pass sequence is now explicit in
`jit_optimize_native_metadata()`. Tag slots, ownership escape, owner homes,
owned last uses, integer-list aliases, dead deopt locals, reconstruction-state
interning, and resume liveness remain there because their products describe
native storage and reconstruction. Their underlying type, effect, liveness,
and alias proofs should move into backend-neutral HIR analyses when a bytecode
transformation can consume them; their compact native metadata encodings
should not.

The PC-stable backend is an executable bridge, not the final bytecode
optimizer. It currently handles proven direct unary/binary integer operations
in the main vector. Fork vectors, branch rewriting, dead instruction removal,
stack scheduling, and superinstructions remain later delivery steps. Until
those are implemented, the sidecar duplicates the main byte vector; this is
still substantially smaller than native code but should eventually become a
sparse patch representation or a newly stackified compact vector.

## Tests and Acceptance Criteria

Differential tests should run the same verb with canonical and optimized
bytecode and compare:

* return value, error value, traceback line, and catch arm;
* ticks consumed and timeout boundary;
* locals visible through `task_stack()`/`callers()` and suspended-task state;
* property and database side effects, including exactly-once behavior;
* reference counts under repeated string, list, float, and waif workloads;
* calls, recursion, permissions, `caller`, player, and verb-not-found behavior;
* suspension followed by database dump/reload/resume; and
* fork-vector execution and old suspended-task compatibility.

Property-based tests should generate small programs from the supported HIR
subset and compare both tiers under several tick budgets and injected runtime
types. The existing SHA-1 workload is useful for throughput and dispatch-size
measurement but is not sufficient for correctness because it exercises a
narrow set of values and exits.

The first useful milestone should require zero semantic mismatches, zero leaked
sidecars or `Var`s, and a measurable reduction in executed dispatches or wall
time on at least one database workload. Code size alone is not enough: existing
bytecode is already compact, and a stackified SSA program can become larger if
it introduces spills, copies, or repeated constants.

## Feasibility and Expected Tradeoff

This backend is feasible and substantially simpler at runtime than native code
because values stay boxed, the interpreter already implements general errors,
and there is no machine ABI or executable-memory lifecycle. It is not free:
stackification, exact ticks, exceptional control flow, source mapping, and
suspended-task canonicalization are compiler correctness projects in their own
right.

The strongest architectural role is a transient middle tier. It can compile
quickly, occupy little memory, improve cold and moderately hot verbs, operate
when MIR is unavailable, and provide a safer execution target for new HIR
optimizations. Native code can remain the hot tier for workloads where boxed
values and dispatch dominate. Keeping both backends behind the same semantic
HIR analyses also gives each optimization one proof implementation and two
independent lowerings, which should improve the reliability of the optimizer
as a whole.
