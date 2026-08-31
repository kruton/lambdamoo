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
* an optional `--enable-jit` extension using vendored MIR master pinned at
  `a8ab7c31cd5f9b23b77d84c60b3d83e62d9d304c`, at O0;
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

Run deoptimization-point simplification after type, ownership, and effect
analysis. Treat the following as separate transformations rather than one
generic deopt-map deduplication pass:

* prove that an instruction cannot guard, raise, call, suspend, abort, time out,
  invalidate native assumptions, or exhaust resources, then remove both its
  exit code and deoptimization map;
* remove a guard only when an equivalent or stronger fact dominates it and no
  intervening operation invalidates that fact;
* intern identical reconstruction state independently of source-site identity;
  and
* share generated exit stubs when their complete observable behavior is
  identical.

The first transformation has priority because it removes branches,
deoptimization liveness, metadata, and machine code together. Merely sharing a
map representation does not remove an executing guard.

### 8.3 Guarded Native Operations

If an SSA value degrades to `TYPE_ANY` and the selected native operation is not
total over its possible runtime tags, the unsupported cases must be guarded.
An operation with complete tagged dispatch needs no type guard merely because
its input is tagged. Guard failure should deoptimize to the interpreter at the
attached ResumePoint/ResumeID.

Guard facts are attached to SSA identities, not source-local names. A precise
type fact for an immutable SSA value can survive a local reassignment and may
survive a call, while facts about object validity, permissions, protected
built-ins, property layout, or other mutable global state require an explicit
effect or epoch proof. Type proofs do not imply range, nonzero, allocation
quota, or finite-float proofs; those failure conditions remain guarded until
their own analyses discharge them.

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
`parent()`. The existing VM-call bridge can leave a compact continuation on a
canonical caller activation for verb and fixed-ID built-in calls. That bridge
is not the general native verb-frame ABI specified below: it relies on the
interpreter to own activation creation and has supported experiments in which
`BI_CALL` and `BI_SUSPEND` retained a native caller.

The native verb-frame sections below are normative for the broader
JIT-to-JIT-call milestone. Normal eligible verb calls keep a compact task-local
chain. Built-ins whose effects require canonical state promote before entry;
other built-ins may return normally or retain a modeled `BI_CALL` continuation
without promotion. Suspension, unmodeled errors or aborts, traceback or
task-stack introspection, pool invalidation, and database writes promote the
complete chain before using canonical VM machinery. Database persistence
therefore remains bytecode-based and contains no native pointers. Existing
continuation code may be reused only where it satisfies the frame, ownership,
ABI, and promotion invariants below.

Built-in inlining must be opt-in and metadata-driven. A built-in may be inlined
only if its registered contract declares it continuation-free:

* it cannot return `BI_CALL`;
* it cannot return `BI_SUSPEND`;
* it cannot return `BI_ABORT`;
* it has no private `bi_func_data`;
* its error behavior and ownership behavior are fully modeled by the JIT.

Continuation-capable built-ins must remain runtime call boundaries.

### 9.2.1 Native Verb Frame Model

The general JIT-to-JIT call path must not be implemented as a recursive C call
whose failure restarts the callee.  It is an incremental execution stack.  Each
committed general verb dispatch creates one semantic frame, just as
`call_verb2()` would create one activation, but the frame remains in compact
runtime form until it returns or the chain is promoted.  The separately
classified rollback-safe leaf optimization may return without committing such
a frame.

There are two distinct records which must not be conflated:

* A **native verb frame** describes one invoked verb and retains the generated
  code and `Program` needed to execute it.  A younger compact callee owns its
  runtime environment, native storage, value homes, referenced receiver or waif
  identity, called and canonical verb names, and other invocation metadata.
  The root frame is an overlay anchored to an existing canonical activation: it
  borrows all activation-owned environment and invocation metadata and owns
  only its additional native storage and value homes.  The overlay and
  activation must not both claim ownership of the same stored reference.
* A **caller resume record** describes the suspended call expression in the
  immediately preceding frame.  It identifies an exact deoptimization-map ID
  and owns the values needed to reconstruct or resume the caller after the
  call operands have been consumed.  It has exactly one result hole.  It does
  not own the callee environment or describe the callee's current PC.

Native execution entered from `run()` begins with a root frame overlay anchored
to the current interpreter activation.  Younger frames form a chain ordered
from that root to the currently executing leaf.  Every non-root native frame
has exactly one incoming caller resume record.  A frame may have an outgoing
resume record only while its callee exists.  Links are task-local; a
process-global pending list cannot represent nested tasks, reentrant execution,
or independent VMs safely.

Conceptually the task stack is:

```text
canonical activation A
  native root frame A             (borrows A's canonical environment)
    caller resume: A after calling B
      native verb frame B         (owns B's compact environment)
        caller resume: B after calling C
          native verb frame C     <- current frame
```

This is a semantic stack, not necessarily the C stack.  Dispatch and return
should run through a C trampoline so recursion consumes the ordinary MOO
activation-depth budget without consuming unbounded C stack.

#### Dispatch

Native dispatch must share verb lookup and environment construction with
`call_verb2()`.  Lookup validates the object or waif receiver, finds the
callable verb, and determines the verb owner and definer.  Environment
construction establishes `this`, `caller`, `player`, `verb`, `args`, command
variables, and permissions with the same reference-transfer rules as an
interpreter activation.

After lookup, dispatch has only three valid outcomes:

1. A strict rollback-safe leaf may use the existing direct-call optimization.
   It either returns normally or proves that no language-visible work occurred
   before falling back.
2. An eligible general callee consumes the call operands, freezes the caller's
   resume record, allocates its native verb frame, and becomes the current
   frame.  From this point the caller cannot be restarted.
3. An ineligible or unavailable callee causes promotion before `call_verb2()`
   is invoked.  Verb-not-found and receiver errors are delivered at the
   caller's exact call site after promotion; they are not treated as permission
   to replay the caller.

A frame becomes visible in the chain only after all references and storage
needed to destroy or promote it have been acquired.  Allocation or validation
failure before that commit point leaves the frozen caller and call request
intact so they can be promoted at the call boundary; it does not authorize
restarting earlier caller instructions.  Failure after the commit point must
promote or abort; it must never restore saved ticks, timeout state, errors, or
native storage and re-execute completed instructions.

#### Normal return

On normal return, the trampoline removes only the completed leaf frame.  The
returned `Var` is moved into the unique result hole in its caller resume record,
then the callee environment and all remaining callee-owned values are
destroyed.  The caller resumes by the recorded map ID.  No bytecode-PC search,
source-line search, or speculative re-entry is permitted.

The result transfer is a move, not a borrowed raw payload.  For complex values,
the result hole is the sole owner after transfer.  Generated code may load the
raw payload and runtime tag from that hole, but the hole remains authoritative
until the value is moved to another owned slot or the resume record is
destroyed.  An SSA register containing a copied pointer is never an ownership
root and must not be used to recover a value after another call.

#### Values retained across a call

Every value named by a caller resume map must have one stable source:

* canonical local or stack slot, whose owning `Var` remains live;
* constant or immediate scalar encoded in the map;
* the result hole; or
* a dedicated owned slot in the caller frame.

An owned slot stores the complete `Var`, including its runtime type tag.  Resume
loads both payload and tag from that slot.  Raw SSA payload slots and separately
cached tags are not stable sources for strings, lists, floats, waifs, maps, or
anonymous values across a call.

The compiler must perform forward must-availability analysis for every resume
map.  A value may be captured only if its definition dominates the call on all
incoming paths and the selected owner is initialized on all of those paths.
Phi liveness or the existence of an SSA definition is insufficient.  If
availability, the runtime tag, or unique ownership cannot be proved, the call
site is not natively resumable and dispatch promotes before executing the
callee.

The verifier must reject a resume record when a referenced value is
uninitialized, already consumed, owned by two slots, represented only by a raw
complex payload, or destroyed before every resume/promotion edge.  Runtime
debug assertions should poison consumed owner slots and check that each live
complex `Var` has exactly one designated owner within the frame.

#### Canonical promotion

Promotion converts the whole native suffix into ordinary activations before
using VM behavior that expects a canonical stack.  It is required for built-ins
classified as requiring canonical entry, unrepresentable built-in continuation
states, suspension, unmodeled errors or aborts, ordinary deoptimization,
traceback or task-stack introspection, JIT invalidation, and database dumps.  A
modeled `BI_CALL` is not intrinsically a promotion boundary.

Promotion is prepared before it mutates the VM stack:

1. Reserve activation capacity for the complete native suffix and verify the
   ordinary interpreter-plus-native depth limit.
2. Validate every program reference, current-location map, caller resume map,
   and value source.
3. Allocate any reconstruction storage and acquire any additional references
   needed by canonical activations.
4. Commit bottom-up: materialize the root overlay back into its anchored
   activation in place, then push an activation for each younger frame, ending
   with the active leaf.
5. Materialize each suspended caller at its after-dispatch continuation.  Its
   stack excludes the consumed object, verb name, and argument list and has no
   synthetic return value yet.
6. Materialize the leaf at its exact current `pc` and `error_pc`, with its
   locals, operand stack, `temp`, handler markers, and built-in continuation
   state.
7. Transfer ownership to the activations, detach the native chain, and only
   then release the compact frame containers.

If preparation fails, no partial canonical chain is published.  Once commit
begins it must be infallible.  The resulting activation order must be identical
to repeated successful `call_verb2()` calls, so the existing interpreter
unwinder can return from an interpreted leaf into a materialized caller.  A
caller may later enter native code through its ordinary resume anchor, but
promotion itself never leaves native pointers in an activation or database.

#### Required invariants

At every trampoline iteration and materialization boundary:

* canonical activation depth plus compact frames younger than the root overlay
  is within the normal activation limit; the overlay represents its anchored
  activation and is not counted twice;
* each environment, frame, resume record, result hole, and owned value has one
  owner and one destruction path;
* a dispatched call's operands have been consumed exactly once;
* completed ticks, timeout state, errors, and side effects are never rolled
  back or replayed;
* the current frame has one exact canonical location, including `error_pc`;
* every suspended caller has one exact after-call map and cannot execute until
  its result hole is filled or an exception is delivered;
* task switching, serialization, introspection, and invalidation observe only
  canonical activations; and
* normal return, exceptional unwind, abort, and promotion release the same
  references exactly once along mutually exclusive paths.

The implementation should begin with a standalone frame verifier and tests for
construction, return, and bottom-up promotion.  The general trampoline should
not be enabled for database workloads until those tests cover complex values,
recursive chains, caught errors at every depth, and promotion after an earlier
side effect.  The persisted `player:test(300000)` SHA1 loop is a hard regression
and performance gate: inability to log in, complete the loop, or keep resident
memory stable rejects the change.

### 9.2.2 JIT Execution ABI

Every native entry point receives a hidden execution-context pointer in
addition to the current native verb frame.  This is the stable semantic JIT
ABI.  Generated code must not discover task state through process globals or
assume that an interpreter activation remains at a fixed address.

Conceptually, the entry point and context are:

```c
JITRunResult jit_entry(JITExecutionContext *context,
                       JITNativeVerbFrame *frame,
                       int entry_map);

struct JITExecutionContext {
    vm task_vm;
    JITNativeVerbFrame *current_frame;
    int *ticks_remaining;
    int *task_timed_out;
    enum error *pending_error;
    unsigned native_depth;
    unsigned activation_limit;
    const JITRuntimeServices *services;
};
```

This is an illustrative interface rather than a declaration to copy directly:
the concrete structure must follow the project's C layout and dependency
rules.  Its responsibilities and ownership are normative.

The concrete foundation now uses `JITExecutionContext`, `JITNativeFrame`, and
`JITCallerResume` in `jit.h`.  The context records the root and current frames,
anchored activation index, canonical and compact depths, ordinary activation
limit, and task tick, timeout, and pending-error pointers.  A frame records its
context, JIT and bytecode programs, caller/callee and incoming/outgoing resume
links, runtime environment, receiver, player, permissions, verb identity,
native runtime allocation, authoritative home array and per-home state array,
exact entry/current maps, canonical anchor when applicable, kind, and lifecycle
state.  Root and canonical-overlay frames borrow this invocation state from
their canonical activation.  Compact frames own referenced program,
environment, receiver, and verb metadata until return or promotion releases
it.

Home state is explicit: `JIT_HOME_EMPTY` has never received a value,
`JIT_HOME_OWNED` contains the sole authoritative complete `Var`, and
`JIT_HOME_CONSUMED` is a one-way poison state after a move.  A consumed home is
not reusable within the same frame instance.  The verifier rejects a state/tag
mismatch and two owning homes containing the same complex payload.

The context is allocated for, and associated with, one running task.  It
survives every native call in that task and identifies the VM which owns the
canonical activation stack.  `current_frame` identifies the currently
executing native verb and changes on call and return.  The context does not own
language `Var` values; native frames, resume records, and canonical activations
remain their only ownership roots.

`native_depth` counts compact frames younger than the root overlay.  It does not
count the anchored activation a second time.  At every native entry,
`frame == context->current_frame` is an ABI invariant.

The two ABI operands have different lifetimes:

* `context` is stable across the complete native execution interval for a task;
* `frame` changes at each verb call and return and owns the callee-specific
  environment, runtime storage, resume location, and values.

`entry_map` selects either initial verb entry or one exact continuation map.  A
compiled verb does not search by source line or bytecode PC to resume after a
call.  Its caller resume record supplies the map ID directly.

Every native exit reports one of a small set of semantic outcomes to the
trampoline:

* **return** moves a complete result `Var` out of the current frame;
* **call** supplies a complete call request and freezes an exact caller resume
  record; the trampoline performs dynamic receiver and verb validation;
* **promote** identifies a canonical boundary and the current deoptimization
  map;
* **raise** supplies an error and the exact error location; and
* **abort** supplies the task-abort reason and exact current location.

The concrete `JITRunResult` may carry these details through out-parameters, but
the distinction is part of the ABI.  Generated code reports the outcome; it
does not recursively manipulate the interpreter activation stack or decide
whether VM policy permits a boundary to remain native.

#### Frame-to-frame calling convention

Native verb calls still require ownership and liveness information.  A machine
calling convention can specify where values travel, but it cannot determine
which reference-counted values remain live, who frees them, or how to rebuild
canonical locals and stacks during deoptimization.  The compiler therefore
uses liveness to construct the frame layout and ownership maps; the runtime
uses the resulting fixed layout rather than trying to rediscover SSA state.

At every natively resumable verb-call site, generated code spills every value
live across the call to a stable home in the caller's explicit native frame.
This storage is a JIT-managed semantic stack, not the platform C stack and not
the movable interpreter operand stack.  It remains valid across C helpers,
activation-stack growth, recursive MOO calls, and register allocation changes.

The initial calling convention is deliberately conservative:

* `context` and `frame` are the only values preserved as ABI inputs;
* ordinary machine registers containing language values are caller-clobbered;
* every live complex value is homed as a complete owning `Var`, with payload
  and runtime tag in the same slot;
* every live scalar has a typed or tagged frame slot when deoptimization or
  native resumption can observe it;
* constants remain encoded in immutable resume metadata when they need no
  runtime owner; and
* the result is moved into one designated caller result slot before the caller
  resumes.

Consequently, a call does not need to preserve an arbitrary set of SSA
registers.  Before publishing a call outcome, the caller completes all required
stores to its home slots and changes their state from uninitialized or borrowed
to the ownership state described by the call-site map.  Only then are the call
operands consumed and the caller suspended.  After return, the caller reloads
values from their homes and may place them back into registers.

The link between a callee frame and its caller must identify at least:

* the caller frame, including the root overlay when the caller is canonical;
* the exact after-call resume-map ID;
* the caller's canonical call-site `pc` and `error_pc`;
* the result-slot index and whether that slot is empty or initialized;
* the live-home layout or call-site map describing reconstructible values; and
* the lifecycle state: preparing, dispatched, returned, or promoted.

The target caller-resume representation names each reconstructed value with
one of five authoritative source classes:

* a canonical local;
* a pre-call stack slot;
* the unique result home;
* an immutable typed constant; or
* an owning native-frame home.

The legacy captured-raw source is not an authoritative source for the new
native chain and must not be admitted by general dispatch.  The first
owner-backed source is implemented for list-tail values which already have an
audited move-to-home transfer.  It stores the home index; capture and retained
native resume validate that the index is in range and the home is
`JIT_HOME_OWNED`, then reload the complete `Var`, including its runtime tag,
from `owned_values[index]`.  A map which requires this source is explicitly
non-rehydratable: canonical entry falls back instead of reading a newly
allocated, empty home array.  The raw SSA/deoptimization payload may still
contain a cache of that value, but it is never selected for owner-backed
recovery.

Owner-home admission also requires forward must-availability at the call.  The
analysis intersects availability from every reachable predecessor and then
walks definitions in instruction order within the call's block.  A definition
on only one branch, after the call, or in an unreachable predecessor is not
sufficient.  Additional producer classes remain disabled until their runtime
helpers have an explicit move/reference contract; assigning homes generically
to property results or other complex producers caused database-startup heap
corruption and is not part of the supported frame format.

Arguments are transferred according to the shared verb-environment
constructor.  The call request owns the receiver, verb name, and argument list
while dispatch is being prepared.  On successful dispatch their ownership is
moved into the callee environment and metadata.  On pre-commit failure the
request remains their authoritative owner until promotion transfers them to the
canonical call boundary or the interpreter-compatible lookup-error path
consumes them.  It must not reconstruct them by replaying the caller.  After
the dispatch commit point, no frame may retain a second owning copy of those
call operands.

Normal return produces a complete result `Var`.  The caller-resume record
retains the exact `JITContinuationFrame` whose `JIT_RESUME_RESULT` entry names
that value.  The trampoline moves the result into the continuation and only
then destroys the callee frame.  This is the actual call-result ABI; it does not
invent an owned-value home for a result that may be scalar or dynamically
tagged.  Ordinary liveness homes remain authoritative for values live across
the call.  An error or abort supplies no result; promotion reconstructs the
caller as suspended after dispatch so the interpreter unwinder can deliver the
exceptional outcome normally.

This convention reduces the amount of runtime continuation data, but it does
not eliminate compiler analysis.  Forward must-availability proves that each
home slot is initialized on every path reaching the call.  Backward liveness
determines which values require homes.  Ownership analysis selects move,
reference, or scalar storage and verifies exactly one cleanup path.  The deopt
map relates those homes to canonical locals, operand-stack entries, `temp`, and
handler markers.

The first implementation should spill all cross-call values, even when a
platform callee-saved register could retain one.  Later register allocation may
keep scalar values in callee-saved registers only if every promotion and
runtime-helper safepoint has an exact recovery rule.  Complex owning `Var`
values should continue to have authoritative frame homes; a register may cache
their payload but never replace their ownership slot.

Promotion itself is represented as a two-phase `JITPromotionPlan`.  Preparation
walks and verifies the complete root-to-leaf chain, validates the leaf's exact
current map and every suspended caller map, and snapshots the frame pointers
without mutating live execution state.  Commit first revalidates the snapshot,
then invokes an allocation-free materializer in root-to-leaf activation order.
Only after every activation has been populated does commit mark resume links
and frames promoted, detach all native links, clear the context, and release the
plan.  The interpreter-side materializer must reserve activation capacity and
all reconstruction storage before calling commit; a materializer callback is
therefore not allowed to fail or allocate.

The first concrete preparation primitive is
`jit_native_frame_prepare_activation()`.  It accepts a fresh, detached
activation whose program, environment, runtime stack, receiver, permissions,
player, verb metadata, and built-in continuation fields have already been
initialized by the interpreter side.  It validates the exact map and bounded
native runtime layout, acquires references for every reconstructed value, and
materializes locals, stack, `pc`, `error_pc`, and the resume key into that
private activation.  The current frame format requires `temp` to be empty.  It
does not consume the native frame's runtime allocation or owner homes.  A
preparation failure may leave the private
activation partially populated, so the caller destroys that private activation
and leaves the complete native chain authoritative.  The root overlay is
likewise prepared in private storage; it is not written into the anchored
activation before commit.

An active frame may instead own an exact boundary snapshot.  This is the
interpreter-ready operand stack already materialized by a non-call deopt, not a
second compact continuation.  `jit_native_frame_capture_boundary()` allocates
the destination first and then moves every `Var` from the temporary boundary
stack, recording the precise map that supplied its `pc` and `error_pc`.
Preparation takes references from that snapshot into a shadow activation and
does not consume it, so allocation or validation failure can discard the
shadow and retry promotion without reconstructing or replaying native work.
Commit releases the snapshot only after publication.  Verification rejects a
snapshot without exclusive ownership, a valid map, or agreement with the
frame's current map.  Snapshot storage is included in the program's active JIT
runtime-byte accounting from capture through release.

The interpreter-side `JITActivationPromotion` now implements that allocator and
publisher.  It verifies that the native root is the current canonical top,
checks that the complete suffix fits within the task's fixed activation limit,
and rejects built-in continuation or `temp` state not represented by the frame
format.  It prepares a private shadow activation for the root and a private
activation for each younger compact frame.  Compact preparation requires
frame-owned invocation metadata.  A failure destroys only these private
activations and the snapshot; the canonical stack and native chain remain
unchanged.

`execute_jit_commit_promotion()` revalidates the native snapshot, frees and
replaces the anchored root, appends younger activations in root-to-leaf order,
and advances the canonical top.  Its callback performs no allocation or value
reconstruction.  Only after every activation has been published does it release
the native runtime allocation and compact invocation references.  General
JIT-to-JIT dispatch remains disabled until the shared verb resolver can create
the owned compact invocation descriptor directly.

Using the platform machine stack for these homes is intentionally excluded from
the portable ABI.  C and MIR stack-frame layouts are target-specific, unwind
through C is not the MOO activation model, and suspended or promoted state must
outlive the native call stack.  A backend may address JIT frame homes relative
to a pinned frame register, giving generated code stack-like access without
making correctness depend on the host ABI.

#### Built-in continuation links and `BI_CALL`

`BI_CALL` is not intrinsically a canonical-stack operation.  The interpreter
represents it with a built-in function ID, continuation PC, and opaque
`bi_func_data`, attaches that state to the nested callee activation, and invokes
the built-in continuation when the callee unwinds.  The native ABI can retain
the same semantics with an explicit built-in continuation link, but the package
alone is insufficient: under the current API the built-in has already called
`call_verb()` or `call_verb2()` and pushed the nested interpreter activation
before returning `BI_CALL`.

Compact `BI_CALL` therefore requires shared verb dispatch to have a task-local
capture mode.  While `call_bi_func()` is entered from a compact native frame,
the execution context enables that mode.  A successful `call_verb2()` performs
the usual lookup and environment construction but commits a complete pending
call request to the execution context instead of pushing an activation.  The
built-in then returns `BI_CALL`, and the trampoline consumes both the package
and the pending request atomically.  This state belongs to
`JITExecutionContext`; it must not be a process-global pending call.

The dispatch refactoring should separate three operations currently combined
by `call_verb2()`:

1. resolve and validate the receiver and callable verb;
2. construct an ownership-complete verb environment and semantic call
   descriptor; and
3. commit that descriptor either as an interpreter activation or as a native
   verb frame.

The first two operations and the interpreter half of the third are now
factored in `execute.c`.  `ResolvedVerbCall` records the single authoritative
lookup result, including the selected verb handle, program, and receiver.
`PreparedVerbCall` then owns the program reference, complete runtime
environment, receiver reference, player and permission identities, and verb
metadata.  It is independent of an interpreter runtime stack.  Canonical
commit moves those fields into a new activation only after the ordinary depth
check has succeeded.  The strict leaf path uses the same resolved target and
commit helper, so it no longer performs one lookup to classify a callee and a
second lookup to invoke it.

`execute_jit_commit_prepared_verb_call()` is the move-only compact commit
routine.  It first validates the prepared descriptor, target JIT program,
caller continuation, result home, and combined interpreter/native depth.  A
failure through this point leaves the descriptor and all of its references
untouched.  Compact linkage then installs the descriptor's exact environment;
`jit_native_frame_take_prepared_invocation()` verifies that identity and moves
the program, environment, receiver, player and permission identities, and verb
metadata into the frame.  It marks `owns_invocation` and clears the complete
descriptor.  This post-link move performs no allocation and has no recoverable
failure path; an invariant violation is fatal rather than permission to replay
the caller.  The frame is returned to its caller only after the owned form
passes `jit_native_frame_verify()`.

No database lookup or environment reconstruction belongs in compact commit.
`execute_jit_dispatch_native_verb_call()` now performs the surrounding
allocation and publication step.  It allocates one `JITNativeCall` containing
the frame and its caller-resume record, resolves the target once, constructs
the callee environment from either a root overlay or compact caller frame, and
invokes the move-only commit.  The call arguments are borrowed by this API; the
prepared environment acquires its own reference, so every pre-publication
failure can destroy the descriptor without consuming the caller's operands.
The returned call object cannot be freed while linked into a context.

`run()` now drives this publisher from an iterative native-call trampoline.
Its caller-resume record retains the captured continuation, requires the
caller frame to own that
continuation's runtime at publication, and records the map's exact bytecode and
error PCs.  Publication suspends the caller; normal return transfers the result
to the retained continuation, destroys only the completed callee, and makes
the caller current again.  A target is compiled before publication, so a
compile failure remains a pre-publication fallback and never leaves an
unmaterializable compact callee.  Runtime
ownership at a captured boundary is now explicit: a fresh
`JITContinuationFrame` owns its allocation,
and `jit_native_frame_adopt_continuation_runtime()` moves that ownership into
the suspended caller frame without copying storage.  The frame and continuation
retain reciprocal owner/borrower links.  A resumed continuation may borrow
storage only from that exact frame; repeated capture preserves the borrowed
relationship.  Continuation destruction removes the borrower link without
freeing storage, after which frame destruction performs the single release.
Adoption also detaches the continuation from its old canonical activation; the
frame is then its only runtime owner.  The inverse
`jit_native_frame_return_continuation_runtime()` operation is allocation-free
and restores ownership to that same continuation during canonical promotion.
When the active continuation still describes the frame's current map,
promotion publishes an empty activation shell, returns the runtime allocation,
and attaches the continuation to the new canonical activation.  When it does
not, the exact boundary snapshot is authoritative and the stale borrower is
destroyed after the shadow activation has been published.  Suspended callers
with outgoing calls continue to be reconstructed as dispatched continuations.
Canonical promotion therefore releases each frame's remaining borrower,
runtime allocation, and boundary snapshot only after all shadow activations
have been published.
Frame verification rejects mismatched storage, home arrays, sizes, programs,
or ownership bits.  The exhaustive graph verifier remains directly callable
by unit tests, while automatic verification at calls, returns, resumes, and
promotion is enabled only in builds configured with
`--enable-def-JIT_VERIFY_NATIVE_FRAMES`.  Production transitions retain their
focused precondition checks, ownership moves, accounting checks, and fatal
guards against release or unbinding with a live borrower; they do not walk the
complete frame graph on every hot transition.

The interpreter loop has a final safety gate before fetching an opcode: if JIT
re-entry was skipped while the activation still owns a continuation, it
materializes that continuation first.  An eligibility change, compilation
failure, or other conservative guard therefore cannot enter the bytecode
interpreter with a compact stack layout.  An attached but undispatched
continuation is never a native-resume input: `run()` skips JIT re-entry and
lets this gate reconstruct the call operands and execute the call opcode.
Only a dispatched continuation can represent the after-call native ABI.

The initial `run()` driver supports repeated eligible verb dispatch and normal
return through arbitrary compact depth.  It gives each active compact callee a
separate materialization stack, transfers return values through the exact
caller continuation, and retains the resumed caller's runtime borrower until
the next native execution or promotion.  The driver now also admits an
explicitly registered, audited class of compact return-only built-ins.  The
initial class is `typeof()`, `equal()`, and `value_bytes()`.  At such a boundary
the frame adopts the caller continuation, moves the materialized argument list
into `call_bi_func()`, moves the `BI_RETURN` value back into the continuation,
and resumes the same frame without constructing an activation.  The call is
charged and counted once; it is never replayed.

This admission is deliberately narrower than general built-in capture.  The
runtime argument count must exactly match the fixed registration, the function
must not currently be protected, and its registration promises that every
validated call returns `BI_RETURN`.  Dynamic/spliced calls are eligible only
when their materialized list has that exact count.  A non-return package from
an admitted function is an internal contract violation, not a reason to replay
the call.  Protected overrides, `BI_CALL`, suspension, errors, aborts,
introspection, and ordinary deopts still capture the exact active boundary,
promote the complete suffix bottom-up, and reload the interpreter caches from
the newly authoritative activation.  Expanding the registered class requires
auditing argument validation and every package outcome; adding compact
`BI_CALL` requires the continuation-link mechanism below.

Extended `verb_info()` metadata records `native_chain_calls` against the
caller, `native_chain_returns` against the resumed caller, and
`native_chain_promotions` for each activation of that verb materialized during
promotion.  `native_chain_max_depth` includes the canonical root frame.
`native_chain_active_frames` and `native_chain_frame_bytes` report live compact
call containers and their retained environments; continuation and runtime
storage remain in their existing counters so they are not counted twice.

Interpreter callers use the activation commit unchanged.  A built-in running
under native capture uses the frame commit after it returns `BI_CALL`.  Lookup
errors create no pending request and retain the existing `call_verb2()` error
contract.  Capture mode is enabled only around the one `call_bi_func()` entry
and is cleared on every package outcome, including C-level failure paths.

The link is distinct from an ordinary verb caller resume record and owns:

* the built-in function ID and continuation PC;
* the opaque `bi_func_data` and its cleanup responsibility;
* the programmer identity used for the continuation call;
* the native caller frame and exact result resume map; and
* the nested callee frame currently producing the continuation input.

When a built-in that is safe to enter with a compact chain returns `BI_CALL`,
the trampoline requires exactly one pending call request, freezes the native
caller, creates this link, and commits the request as a native callee when
eligible.  Zero or multiple pending requests is an ABI violation rejected by a
verifier or runtime assertion; replaying the built-in is not a safe fallback.  A
non-`BI_CALL` package must leave no pending request.  A normal nested return is
moved into `call_bi_func()` as the continuation argument under a fresh capture
scope.  Its outcome is then handled as follows:

* `BI_RETURN` destroys the built-in link and moves the value into the original
  caller's result slot;
* another `BI_CALL` updates or replaces the link and dispatches the next nested
  verb without growing the native caller chain unnecessarily;
* `BI_SUSPEND` promotes before queuing the task until native suspension state is
  separately modeled;
* `BI_RAISE` promotes before delivering the error through the interpreter; and
* `BI_ABORT` promotes the locations needed by the ordinary abort machinery.

If the nested verb exits exceptionally, the initial implementation promotes
and lets `unwind_stack()` apply the legacy rule: invoke the built-in
continuation with zero, short-circuit further calls, and suppress continuation
errors as the interpreter currently does.  That path may remain native only
after the trampoline implements and tests the same unusual semantics exactly.

Promotion transfers the link into the nested callee activation's `bi_func_id`,
`bi_func_pc`, and `bi_func_data` fields without copying ownership of the opaque
data, exactly where `unwind_stack()` expects it.  The emptied native link must
no longer free the data; the activation cleanup path becomes its sole owner.  A
built-in continuation which cannot be represented by those canonical fields is
not eligible for compact capture and promotes before the built-in is entered.

Effect metadata decides whether a built-in may be entered while callers remain
compact.  A built-in which can inspect the task stack, suspend internally
without returning a package, invalidate executing code, or otherwise require
canonical activations promotes before `call_bi_func()`.  For a safe compact
entry, side effects completed before a later `BI_CALL`, raise, abort, or suspend
outcome are retained; outcome handling never replays the built-in.

Compact capture additionally requires an audited built-in contract: every
successful captured `call_verb2()` is followed by exactly one `BI_CALL` return,
and the built-in does not inspect or depend on the newly pushed activation
before returning.  Built-ins without that contract promote before entry even
when their registered effects merely say that they may call a verb.

Thus minimal promotion is the target: retain a `BI_CALL` when both the built-in
continuation and nested verb call are representable, and promote only for an
effect or outcome whose semantics require canonical VM state.  A conservative
implementation may initially promote all `BI_CALL` outcomes while the link and
its verifier are being developed, but that is a bring-up restriction rather
than the final ABI.

Native dispatch passes the same context to the callee, installs the callee as
`current_frame`, and enters its compiled program.  Normal return restores the
caller frame before resuming its exact map ID.  Promotion follows
`current_frame` and its task-local links to find the native suffix; it never
consults a process-global pending-frame list.

The context must provide or reach all mutable execution state whose identity is
shared across verbs, including tick accounting, timeout and kill state, native
depth, the activation limit, and the owning VM.  Runtime operations should be
accessed through an explicit service table or ABI helpers rather
than embedding arbitrary C addresses and structure offsets throughout generated
code.

This calling convention has no numeric compatibility version.  Native code is
generated within the current process, belongs to the live JIT pool, and is
discarded rather than serialized with suspended tasks or database files.  Pool
reset and process exit are its compatibility boundaries.  Direct frame/context
verification catches runtime mismatches; a persistent version would become
necessary only if native code were cached across processes or supplied by a
separately compiled module.

The portable ABI treats `context` and `frame` as hidden function arguments.
Correctness must not depend on a particular physical register.  A backend may
pin `context` in a dedicated callee-saved register and keep `frame` in another
register when the target architecture, platform ABI, and MIR integration can
reserve them reliably.  Such pinning is an optimization of the same semantic
ABI, not a separate source of VM state.

When a pinned register is used:

* every JIT entry stub initializes it before entering generated code;
* every JIT-to-JIT edge preserves it according to the platform calling
  convention;
* calls into C either preserve it as callee-saved or spill and restore it;
* signal, error, deoptimization, and promotion stubs can recover the same
  context without relying on transient C locals; and
* architecture-specific tests verify the register contract around every
  runtime helper category.

Generated code must not retain pointers to `RUN_ACTIV` or activation-stack
elements across operations that can grow or relocate that stack.  If the
context caches a canonical activation, it uses a stable index or refreshes the
pointer after every relocating operation.  Similarly, suspension stores the
task only after promoting the chain to canonical activations.  The execution
context becomes inactive before the task is queued, and neither it nor its
physical register assignment is database state.  A later task resumption
creates or reinitializes a context before entering native code again.

ABI verification should exercise native recursion, calls through C helpers,
activation-stack growth, task switching, suspension, promotion, and error
unwind with assertions that `context`, `current_frame`, tick pointers, and the
owning VM remain consistent.  Register pinning should be enabled only after the
argument-based ABI passes the full database regression suite, so backend
optimization cannot obscure frame-model correctness.

### 9.2.3 Interpreter Run-Loop Integration and Deoptimization

The interpreter `run()` loop remains the authority for canonical activations,
exception delivery, built-ins, suspension, aborts, and task completion.  The
native trampoline is entered from `run()` only when the current activation has
a compiled initial entry or an exact compiled resume map.  Entry constructs or
reinitializes a task-local `JITExecutionContext`, identifies the canonical root
activation, and creates a native view of that activation without transferring
its language values to a second owner.

While execution remains native, the trampoline repeatedly performs this state
machine:

```text
execute current frame at entry_map
  return   -> move result to caller, pop frame, resume caller map
  call     -> resolve target, push native callee or request promotion
  promote  -> materialize complete native suffix and return to run()
  raise    -> materialize complete native suffix and deliver the error
  abort    -> materialize locations needed for traceback, then abort the task
```

The trampoline, rather than generated code or recursive C calls, changes
`current_frame`.  It charges each compact frame younger than the root overlay
against the ordinary activation limit, retains code and program references, and
is the single cleanup authority for normal native call and return.  The C stack
therefore remains bounded for MOO recursion.

The canonical activation from which `run()` entered native code remains the
root of the task stack and owns its canonical environment.  Its native root
frame is an overlay which borrows that environment and owns only native homes
and metadata not already owned by the activation.  If the root calls a native
callee, its after-call resume record links the overlay to the younger native
frame.  `run()` must not interpret the root activation while its overlay or any
younger frame remains active.  It regains control either after the root verb
returns normally or after the complete native chain has been promoted.

Before entering the trampoline, `run()` stores any cached interpreter state
such as the bytecode pointer, error pointer, and runtime-stack pointer into its
activation or execution context.  After a native outcome returns control,
`run()` reloads those caches from the now-authoritative activation.  No pointer
to `RUN_ACTIV`, its runtime stack, or the activation vector may remain live
across a push, relocation, promotion, or other VM operation that can invalidate
it.

#### Deoptimization protocol

For this milestone, every ordinary deoptimization is a full native-suffix
promotion.  It is not enough to reconstruct only the leaf while leaving its
callers in private native storage: interpreter error handling, introspection,
suspension, and activation return all assume one canonical activation stack.

Each native safepoint therefore identifies a deoptimization map containing:

* the active frame's exact bytecode `pc` and `error_pc`;
* whether the boundary instruction has or has not executed;
* the operand-stack depth and complete stack reconstruction recipe;
* canonical locals, `temp`, catch/finally markers, and built-in continuation
  state;
* ownership sources and runtime tags for every reconstructed `Var`;
* ticks already charged at the safepoint; and
* the boundary kind and any operands which the interpreter must consume.

The map ID remains the exact site identity used by native continuations,
promotion, profiling, and traceback reconstruction. Its storage may be split
into a site descriptor and a shared reconstruction snapshot, but sharing the
snapshot never aliases or renumbers distinct site IDs.

Deoptimization proceeds in four phases:

1. **Freeze.** Generated code stops at the safepoint and publishes its outcome,
   current map ID, and authoritative owner slots.  It performs no more language
   operations and releases no value needed by promotion.
2. **Prepare.** The runtime validates every frame and resume map, reserves the
   complete activation suffix, allocates reconstruction storage, and acquires
   any references required for transfer.  Failure here aborts safely without
   publishing a partial interpreter stack; it never restarts completed native
   work.
3. **Commit.** The runtime writes the root overlay into its anchored activation,
   materializes younger suspended callers bottom-up and the active leaf last,
   transfers each value to exactly one canonical owner, clears native links,
   and releases only the emptied compact containers.  This phase is
   allocation-free and cannot fail.
4. **Resume.** Control returns to `run()`, which reloads its cached state and
   dispatches according to the boundary kind at the reconstructed `pc` and
   `error_pc`.

The safepoint's executed/not-executed flag determines where interpretation
continues.  A guard before an operation reconstructs its operands and resumes
at that operation.  A boundary after an operation resumes after it and must not
repeat its side effects or tick charge.  Tick reimbursement is permitted only
when the map proves the corresponding interpreter operation has not executed;
saved task counters are never restored wholesale.

Boundary handling after promotion is deliberately ordinary VM behavior:

* an unavailable or ineligible verb target promotes through the canonical
  caller call site, then uses shared verb resolution and `call_verb2()`;
* a built-in requiring canonical entry promotes before `call_bi_func()`;
  otherwise `BI_RETURN` and a representable `BI_CALL` remain in the trampoline,
  while `BI_SUSPEND`, `BI_RAISE`, `BI_ABORT`, or an unrepresentable continuation
  state request promotion and are completed by the existing run loop;
* a native error promotes first, then pushes or raises the error at the leaf's
  exact `error_pc`, allowing catches in the leaf or any caller to unwind in the
  normal order;
* timeout, tick exhaustion, and `kill_task()` preserve the exact current
  location and enter the existing abort machinery without rolling back task
  state; and
* introspection, invalidation, and database persistence promote first and see
  no native-only frames or pointers.

An interpreted callee created after promotion may return through the existing
activation unwinder.  Its caller is already a canonical activation at the
after-dispatch continuation.  If that continuation has a valid native resume
map, the next `run()` iteration may construct a fresh execution context and
re-enter compiled code; correctness never requires retaining the old native
context across promotion.

The first implementation tests should drive the trampoline with synthetic
outcomes and compare the promoted activation stack field-for-field with the
semantic stack created by ordinary interpreter calls, including value tags and
reference ownership.  Only after call, return, deopt, error, abort, and built-in
boundary transitions pass those comparisons should generated JIT-to-JIT call
instructions be enabled.

### 9.2.4 Experimental Code Disposition

The native-frame ABI is a replacement design, not a requirement to preserve
every earlier continuation experiment.  Experimental code which cannot be
adapted without retaining global chains, speculative replay, raw SSA ownership,
or activation-attached native state should be deleted.  Tests of language
semantics should be retained and redirected through the new trampoline; tests
which assert only an obsolete internal mechanism should be replaced.

The following known experiments do not fit the target model and are explicit
delete-or-replace candidates:

* In `execute.c`, `JITNativeCallFrame`, `jit_pending_native_calls`,
  `jit_native_call_depth`, `jit_retain_native_call()`, and
  `jit_promote_native_calls()` implement a process-global pending chain and
  recursive C execution.  Replace them with the task-local
  `JITExecutionContext`, root overlay, and iterative trampoline.
* `JIT_DIRECT_VERB_PROMOTED` and the `run()` branch which recognizes
  `jit_pending_native_calls` expose that global promotion protocol.  Remove
  them when explicit call and promote outcomes drive the trampoline.
* `execute_jit_direct_verb_call()` currently saves and restores ticks, timeout,
  and error state after a failed speculative callee.  Preserve a separately
  audited rollback-safe leaf helper if it remains useful, but delete this
  rollback behavior from every committed general call path.  The general ABI
  never restores task state or replays the caller.
* `jit_program_is_direct_call_safe()` currently admits transitive speculative
  verb calls, and `jit_program_note_direct_call_failure()` disables a callee
  after a failed attempt.  Restrict the classifier to the strict leaf contract;
  do not reuse dynamic failure-and-restart as general chain control flow.
* The current `JITContinuationFrame` representation in `jit_internal.h` stores
  an activation `owner`, duplicated `values` and `spare_values`, raw
  `deopt_values`, and pointers into one native runtime allocation.  Replace
  this shape with the root overlay, fixed authoritative frame homes, caller
  resume records, and built-in continuation links.  Reuse its verified
  deoptimization-map concepts, not its ambiguous ownership graph.
* The process-global `continuation_frames` list and
  `jit_continuation_attach()`, `jit_continuation_relocate()`,
  `jit_continuation_mark_dispatched()`, and
  `jit_continuation_materialize_all()` treat activation-attached continuations
  as the native-chain registry.  Replace chain ownership with task-local
  contexts.  Invalidation and database dumps must enumerate tasks and request
  promotion through their contexts rather than walking native frames owned by
  unrelated activations.
* `JIT_RESUME_CAPTURED` and the fallback capture path in `hir.c` retain values
  from raw SSA/deoptimization slots when no canonical source is available.
  Delete or disable that source.  Replace it with an explicit frame-home source
  admitted only by must-availability, runtime-tag, and unique-ownership proofs.
* `JIT_BOUNDARY_SUSPEND_ZERO`, `continuation_fast_suspends`, and the compact
  suspend branch in `run()` preserve native continuation state across scheduler
  suspension.  Suspension promotes in this milestone.  Remove this special
  path unless a later, separately specified native-suspension ABI supersedes
  the canonical-only persistence rule.
* `JIT_RUN_CALL_VERB` is currently overloaded for ordinary verb calls,
  built-in bridges, and zero-second suspension.  Replace the overload with the
  explicit call, promote, raise, abort, and return outcomes in Section 9.2.2.
* Tests in `tests/jit_test.c` which directly attach an activation-owned
  continuation, force `jit_program_note_direct_call_failure()`, or assert the
  compact-suspend mechanism should be rewritten against frame construction,
  trampoline outcomes, and canonical promotion.  Their value, tag, reference
  count, error-location, and no-replay assertions remain required.

The following foundations fit the target design and should be retained or
adapted rather than removed:

* bytecode resume points, exact deoptimization-map IDs, canonical stack-marker
  recipes, and source/error locations;
* shared verb lookup, environment construction, and activation initialization;
* the strict rollback-safe leaf optimization, provided its proof excludes all
  visible effects and post-commit fallback;
* built-in continuation import, export, and cleanup support, which canonical
  promotion uses when transferring `bi_func_data` ownership;
* native-chain and continuation profiling counters, updated to count the new
  task-local frames and their retained bytes; and
* semantic database tests, especially complex values across repeated calls,
  caught errors at each depth, side effects before later promotion, and the
  persisted `player:test(300000)` SHA1 gate.

This list should be rechecked during implementation.  A symbol being listed as
reusable does not exempt it from the new verifier and ownership rules, and an
experimental commit need not remain in history merely because some tests or
metadata from it are worth preserving.

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

The existing compact VM-call continuation paths must satisfy the same
requirement.  Calls inside protected regions remain promotion boundaries in
this milestone unless their complete handler state is represented by the new
frame ABI.  Before any native return across such a protected call is enabled,
continuation maps must preserve and reconstruct the complete caller stack
prefix, including catch/finally markers and any enclosing loop state, rather
than only call operands and live SSA values.

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
failure, or abort, it follows the freeze, prepare, commit, and resume protocol
in Section 9.2.3.  The runtime uses the current deoptimization map, writes the
root frame overlay back into its anchored activation, and materializes each
younger native frame as a normal `activation`.  It populates `pc`, `error_pc`,
resume metadata, `rt_env`, runtime stack, `temp`, and ownership-correct `Var`
values before returning control to `run()` or serializing a suspended VM.

Serialized activations preserve language state, not JIT state. JIT state is
disposable and must be reconstructable from the canonical activation.

### 10.3 Future Native Resume

On database load, a future JIT may resume natively only if:

* the relevant program/vector is compiled;
* the compiled code advertises support for the activation's resume anchor;
* the compiler has a native resume stub for that anchor;
* the canonical activation can be represented by a verified root-frame overlay
  without duplicating ownership.

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

Passing a true third argument to `verb_info()` includes per-program JIT usage
and memory statistics. These include native entries and completions, VM-call
crossings, deoptimizations by reason, last-use time and generation, compilation
attempts/results/time, persistent metadata bytes, runtime materialization
storage, and generated machine-code bytes. `accounted_bytes` is included by
`program_bytes()` and uses the proportional share of executable pages reported
by `native_allocated_bytes`, reflecting actual code-holder page utilization
and alignment across the shared context. All compiled verbs reside in a
generation-based shared `MIR_context` pool where generator scratch memory is
reclaimed immediately via `MIR_gen_finish()`, eliminating duplicate per-verb
context baselines. Whole-pool invalidation (`jit_pool_reset()`) cleanly reclaims
executable memory and MIR modules when built-in protections change or the pool
rotates, resetting active programs back to pending.

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
* VM-call bridges with SSA-liveness continuations for general built-ins and
  verb calls, including protected built-in overrides.

Recent tagged-value work allows runtime-typed scalar and complex values to flow
through concatenation, indexing, list construction, comparisons, branches,
properties, and returns. Runtime tags are propagated through SSA copies and
dynamic-result operations. Native consumers either dispatch on the tag or
deoptimize before touching a representation they do not support.

Every lowered native boundary now owns a verified deoptimization map. The map
records the canonical bytecode PC, locals, operand stack, tick state, and fixed
catch/finally marker data. Synthesized scatter operations retain the stack from
the original bytecode boundary instead of their internal temporary stack, and
materialization rebuilds handler markers from canonical metadata rather than
incidental native values. Call maps are checked against their `ResumePoint`
stack depth and marker layout before MIR lowering. Negative tests reject
mismatched call depths, marker kinds, and marker payloads.

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

After enabling the VM bridge for every fixed-ID built-in call, the same Opal.db
object range recorded 720,008 VM crossings without a `builtin_call`
deoptimization. The crossing count includes both built-in and verb boundaries.
The remaining 320,008 exits comprised 239,996 unsupported
operations, 79,999 type guards, and 13 range operations. This is a coverage
result rather than a speed comparison: bridged built-ins still execute in the
VM, but their callers can resume native execution.

Property writes now lower `HIR_TAC_PUT_PROP` directly for object receivers and
string property names, including dynamically tagged receivers and right-hand
side values. The runtime helper preserves ordinary and built-in property
permission checks, stores a referenced copy while retaining the assignment
result, and reports interpreter-compatible errors. A wizard-flag transition
still deoptimizes before mutation so the interpreter retains its canonical
traceback and audit logging behavior. Property read and write support is
therefore no longer a pending native-operation milestone; the remaining work is
the broader ownership-map and synthesized-anchor validation described below.

### 14.3 Priorities for programs that remain entirely native

1. **Classify unsupported operations by HIR operation and call site.**
   Extend `tests/deopt-census.sh` output so the 363 generic
   `unsupported_operation` exits are attributable to an exact HIR operation,
   bytecode opcode, and source site. Start with the high-frequency event-handler
   and controls paths. Do not implement an operation until its resume stack,
   error behavior, tick charge, and ownership contract are known.

2. **Replace experimental continuations with the verified native-frame ABI.**
   The existing bridge has exercised compact continuations across ordinary verb
   calls, fixed-ID built-ins, `BI_CALL`, and `BI_SUSPEND`. Those experiments are
   evidence for resume-map coverage, not the target frame model: database
   testing showed that SSA definition liveness alone can retain a stale or
   wrongly represented complex value.

   Implement Sections 9.2.1 through 9.2.3 in order: the task-local context and
   root overlay, explicit frame homes, the frame verifier, synthetic trampoline
   transitions, bottom-up promotion, and only then general native verb dispatch.
   Normal eligible verb calls are the first compact boundary. Then add verified
   built-in continuation links so safe built-ins can return `BI_CALL` without
   promotion. Built-ins requiring canonical entry, suspension, unmodeled errors
   or aborts, introspection, invalidation, and database writes still promote
   before entering existing VM behavior. `verb_info(..., 1)` reports
   continuation and native-chain calls, returns, promotions, active frames,
   maximum depth, and retained bytes.

   Resume native callers only by the exact call-site map ID; do not repeat a
   linear `ResumeKey` lookup. Do not enable arbitrary raw
   `JIT_RESUME_CAPTURED` values. Cross-call values require must-availability,
   authoritative frame homes with trustworthy runtime tags, and the ownership
   proof in priority 5. A task loaded from a database resumes canonically and
   may enter JIT at its bytecode anchor; native frames and contexts are never
   serialized. Tail-call activation replacement should wait until normal and
   exceptional frame paths have sustained database-scale validation.

3. **Use effect metadata to select direct native built-in lowering.**
   Record argument prototypes and effects such as pure, allocation, possible
   errors, permission checks, calls, suspension, abort, continuation state, and
   ownership transfer. The VM bridge is the safe default for fixed-ID calls; use
   metadata both for type inference and for deciding whether a built-in can
   bypass that bridge and execute directly in native code. Prioritize frequent,
   cheap, continuation-free built-ins where the VM crossing is measurable.
   Never directly lower a built-in that can return `BI_CALL`, `BI_SUSPEND`, or
   `BI_ABORT` without modeling that outcome.

   Built-in registration now records conservative call, suspend, abort, and
   continuation-state effects. A fixed-ID call whose registration proves it
   synchronous can return or raise directly into generated code; `tostr()` is
   the first enabled allocation-returning built-in. Protected built-ins retain
   an override guard, and complex results transfer into an explicit native
   ownership slot. Add effects to further built-ins only after auditing every
   package kind and side effect.

   Direct JIT-to-JIT verb calls no longer push an interpreter activation for a
   successful rollback-safe callee. The native ABI carries the caller's exact
   environment and permissions into a shared verb-environment constructor, so
   `caller`, command variables, waif receivers, and player propagation retain
   interpreter semantics. Verb-call instructions are admitted transitively:
   each dynamic target must satisfy the same side-effect-free contract, which
   permits `A -> B -> C` and self-recursion without a static call graph or verb
   generations. Native depth is charged against the ordinary activation limit.

   The existing direct-call path remains restricted by rollback safety. The
   general trampoline removes that restriction for normal eligible verb calls
   by committing a frame rather than restarting completed code. General
   built-ins and other stateful VM boundaries still require canonical
   interpreter activations. On deopt, a raised exception, suspension, stack
   introspection, pool invalidation, or database dump, materialize the complete
   chain into canonical interpreter activation order and continue at the
   precise callee and caller anchors. Only after this general bridge is
   benchmarked should true body inlining be reconsidered.

4. **Reduce type guards using consumer constraints and tagged dispatch.**
   Report local/value identity and expected/actual tags for the remaining guard
   failures. Seed only invariant runtime slots, preserve `TYPE_NONE` for
   uninitialized user locals, and infer types backward from exact built-in and
   operation contracts. When multiple types are legitimate, carry the runtime
   tag and add a guarded consumer instead of guessing a static type. Never
   weaken a guard merely to improve census numbers.

   Consumer contracts now centralize expected operand masks and tagged-dispatch
   capability, and deopt reports include SSA value, local, expected mask, and
   actual runtime tag. Requirements remain local to consumers: applying a
   singleton requirement as a global producer fact was shown unsound by
   `#69:_listify`, whose `args[1]` value legitimately changes type across
   invocations. Tagged `valid()` dispatch reduced a codepoint.db `#0..#50`
   sample from 151 deopts (4.02% of 3,753 entries) to 125 deopts (3.34% of
   3,743 entries). Continue with the measured `length`, dynamic string-index,
   and list-index result sites, distinguishing operand-tag failures from result
   representation failures before changing guards.

   Arithmetic contracts are now pair-sensitive: overloaded operations retain
   the valid combinations instead of treating independent operand masks as a
   cross-product. This covers matching integer, float, and string pairs for
   `+`, matching numeric pairs for the other arithmetic operations, and the
   asymmetric `FLOAT ^ INT` case. Tagged `+` dispatch currently handles integer
   addition and string concatenation; float arithmetic and exponentiation still
   deopt until their tagged MIR paths are implemented.

5. **Finish dynamic complex-value propagation and ownership accounting.**
   Audit every instruction that can produce a runtime-selected type—property
   reads, list indexing, joins, calls, and overloaded arithmetic—and ensure its
   tag reaches locals, copies, returns, and deopt maps. Add explicit
   borrowed/owned/immortal states so native temporaries are released on normal,
   error, and deopt exits. Include repeated-execution leak tests for strings,
   lists, properties, and call results.

   As the first ownership step, each compiled program records the compact set
   of interpreter locals read by its HIR. `jit_program_execute()` retains those
   locals for the complete native invocation and releases them only after a
   return, deopt materialization, or continuation capture. This prevents an
   indexed local update from freeing a list or string still borrowed by an SSA
   register. Per-value provenance now distinguishes scalars, borrowed locals,
   owned values, stable owned values, and immortal constants, and propagates
   alias roots through SSA copies. Continuations may capture retained local
   borrows, constants, property reads, and freshly produced list values whose
   ownership has not been consumed. A SHA-1 invocation now captures and resumes
   all ten of its VM/scheduler crossings, performs no interpreter
   materialization, and completes natively.

   Codepoint testing showed that capturing generic scalar liveness or older
   owned temporaries can expose stale out-of-SSA values, so both remain
   prohibited. Add compact owner slots for longer-lived native producers and
   path-sensitive value availability before broadening those cases. Then add
   last-use release on every native exit. Keep the conservative local roots
   until those proofs are verified on Codepoint. The initial ownership-safe
   capture reduced the warmed 30,000-call SHA-1 benchmark from 7 seconds to 5
   seconds; the 100,000-call sample moved from roughly 23 seconds to 22 seconds,
   making the ten continuation crossings per invocation the next measured
   bottleneck.

6. **Lower the hottest remaining range and caught-error paths.**
   The current sample reaches range operations after earlier string/list work.
   Add native list and string range extraction/assignment only where bounds,
   Unicode indexing, allocation quotas, source locations, and catch transfer are
   exact. A caught error should enter its native handler only after stack-marker
   and tick equivalence are tested; otherwise deopt before the operation.

7. **Compile fork vectors and support native re-entry.**
   Make code-unit identity explicit in entry and deopt maps, compile fork vectors
   independently, and retain bytecode fallback for serialized tasks. A fork
   statement may remain a scheduling boundary while its body becomes eligible
   for native entry. Add checkpoint/reload and suspended-task tests before
   enabling native resume.

8. **Optimize only after coverage boundaries are trustworthy.**
   MIR optimization level 1 is now the default. On Codepoint's 984-value
   `$local.crypto:sha1` verb it reduced generated machine code from 250,864 to
   72,080 bytes and compile time from about 303 ms to 225 ms. Level 2 reduced
   code further to 49,872 bytes but raised compile time to about 316 ms. Compare
   runtime with an external monotonic timer: MOO's `time()` has one-second
   granularity, and this verb suspends three times per invocation, so its
   in-database timing cannot distinguish close O1 and O2 results. Keep level 2
   as a possible hot-tier policy until that comparison shows whether its extra
   compile cost pays for hot verbs. Those figures predate the native-chain and
   ownership work. The current `$local.crypto:sha1` baseline has 928 SSA values,
   898 anchors, 243 deopt maps, approximately 118 KB of retained metadata, and
   approximately 160 KB of machine code. Use that baseline when measuring the
   transformations below rather than comparing against the earlier tier alone.

   Apply the following four transformations in order:

   1. **Exit and effect analysis.** Compute the possible exits of every
      instruction after type, ownership, and effect propagation: type or
      representation guard, range error, division by zero, quota error, float
      error, call, suspension, abort, timeout, invalidation, and promotion. If
      the set is empty, remove the exit code and its map. Calls that may promote,
      tick/timeout boundaries, and operations with an undischarged error
      condition remain safepoints.

   2. **Dominance-based guard elimination.** Track facts by SSA identity and
      expected mask or predicate. Remove a guard only when an equivalent or
      stronger dominating proof remains valid. Calls need not invalidate an
      immutable SSA type tag, but they conservatively invalidate facts about
      object validity, permissions, protected built-ins, property layout, and
      mutable global state unless effect metadata or an epoch guard says
      otherwise. A type proof alone never removes bounds, nonzero, quota, or
      finite-float checks.

   3. **Reconstruction-state interning.** Keep deopt site identity separate
      from reconstruction state. A compact site descriptor retains resume and
      error PCs, source line, reason, tick state, native handler, and other
      observable control state. Locals, stack values and markers, runtime tags,
      and owner homes form an independently interned or base-plus-delta state
      snapshot. Distinct sites may share a snapshot, but sites with different
      traceback, error, timeout, or resume behavior must not be merged.

      The initial representation assigns every site a `reconstruction_state`
      ID. The state table stores only the representative map ID; the
      representative exclusively owns the immutable stack, tag, and owner-home
      arrays, and equivalent sites borrow those arrays. State equality compares
      fully resolved locals as well as stack values and markers, runtime-tag
      values, owner homes, and boundary ownership. Local snapshots retain their
      bounded base-plus-delta encoding for now. Native-resume recipes remain
      site-owned because call operands and resume behavior are not merely frame
      reconstruction data. A verifier checks every map-to-state reference and
      every borrowed array identity after interning.

      Type guards which replace the consumer's complete exit may own that
      consumer's former site. A partial guard, such as the type half of
      `length()`, must have a distinct site from the consumer's remaining
      representation/error exit even when both sites intern to the same state.
      This prevents a guard reason from masking a later semantic failure.

   4. **Shared exit-stub lowering.** After site simplification and state
      interning, share materialization and status stubs whose complete behavior
      is identical. Distinct sites may load a compact site/map ID before
      branching to a common stub. This is code deduplication, not permission to
      discard site-specific source or error state.

      The first implemented form shares the post-materialization return tails
      by `JITRunResult`. Each site still materializes its own required SSA
      values and writes its exact map ID, then jumps to a stub which writes the
      result status and enters the common epilogue. Ordinary status exits use
      the same tails after writing their error. Source locations are interned in
      a program-owned side table: native status exits write one compact location
      ID, and the runtime expands it to canonical bytecode PC, error PC, and
      source line immediately after the native function returns. This keeps
      immutable location metadata out of the MIR instruction stream and native
      code while preserving the existing runtime ABI at its consumers. Scalar
      constants in reconstruction state use the same principle. Their SSA IDs are
      recorded in a packed bitset with a sparse value table; exit code omits
      their raw stores, and materialization or compact resume reconstructs them
      directly from metadata. Constants must be classified before local and
      stack resume sources so compact continuations never depend on an omitted
      runtime slot. These transformations are safe because the stubs consume no
      reconstruction values and therefore do not extend SSA live ranges. An
      owner-backed reconstruction value is likewise represented by the map's
      owner-slot side reference instead of a copied raw value and runtime tag,
      but only when forward analysis proves the owner home is current and the
      slot is stable (never consumed anywhere in the function). The owning
      `Var` is authoritative for both payload and dynamic type. Reused homes and
      homes which an instruction can consume before taking an exceptional exit
      continue to use raw reconstruction until the must-populated proof models
      those edge-specific transitions.

      Local reconstruction entries are pruned before local-map coalescing when
      backward CFG liveness proves the slot cannot be observed before it is
      overwritten or the activation returns. The proof unions normal and
      exceptional successors, treats verb calls, suspension, stack
      introspection, and unsupported interpreter boundaries as barriers, and
      also retains a local whenever its current SSA value has a program use.
      The SSA-use condition is required because promoted local reads consume
      the current SSA value directly and need not produce a later
      `HIR_TAC_LOAD_LOCAL`. No persistent liveness bitmap is needed: dead sparse
      local entries are removed before reconstruction states are interned.

      An experiment outlining complete materialization
      by reconstruction-state ID increased `#463:sha1` machine code because it
      kept many SSA values live to function-end stubs and caused additional
      register pressure; do not restore that form without an ABI which passes
      already-spilled reconstruction storage to the stub.

   Only after these passes should repeated local/tag-load elimination,
   block-level tick batching, call-site specialization, and additional MIR
   optimization tiers be considered. Deopt-aware liveness is intentionally
   broader than machine-operand liveness: values named by a remaining
   reconstruction snapshot are genuinely live even if no later native
   instruction reads them. Do not reduce pressure by dropping those implicit
   uses. Every transformation must preserve exact timeout, source-location,
   error, ownership, and deoptimization behavior and be measured against
   interpreter and JIT O0 baselines.

9. **Expand differential and database-scale validation continuously.**
   Add generated programs covering every runtime tag at every tagged consumer,
   forced guard failures at synthesized bytecode anchors, nested catches,
   recursion, permissions, repeated complex-value execution, checkpoint/reload,
   and suspension. Track native completion percentage, reason distribution,
   guard count, deopt-map and shared-snapshot counts, compile time, metadata,
   machine-code size, and execution time for stable workloads.

### 14.4 JIT pool efficiency roadmap

Per-program usage and retained-memory measurements are now sufficient to begin
pool policy work. Pool accounting should continue to keep these quantities
separate: compiler metadata, runtime materialization storage, live MIR heap,
used machine-code bytes, and executable pages. Add executable address-space
reservation and mapping counters through MIR's code-allocator interface before
treating `accounted_bytes` as a complete virtual-memory measurement.

Implement pool efficiency in this order:

1. **Aggregate current measurements.** Report total compiled-program count,
   bytes by category, entries, native completions, VM crossings, deoptimizations,
   compilation time, evictions, and recompilations. Preserve per-verb values in
   `verb_info()` so a global total can always be reconciled with its members.

2. **Separate native eviction from eligibility.** Releasing a MIR context,
   executable mappings, and runtime materialization buffer should return the
   program to a lazily compilable pending state. Eviction or a high deopt rate
   must never permanently prevent an interpreted verb from being compiled
   again.

3. **Add a configurable byte budget with hysteresis.** Select cold native
   programs using retained bytes, last-used generation/time, entry count,
   native-completion rate, deopt rate, and recompilation cost. Evict to a low
   watermark rather than repeatedly crossing one hard limit. Use minimum sample
   counts and cooldowns before deprioritizing a frequently deoptimizing verb.

4. **Manage shared pool memory and rotation.** Maintain the generation-based
   shared `MIR_context` pool with immediate generator scratch finalization
   (`MIR_gen_finish()`). Rotate or compact the pool when memory limits are
   reached or built-in protections change, safely returning cold or invalidated
   programs to the pending state without leaking module or executable state.

5. **Reduce deopt metadata and register pressure.** Implement the
   four deopt-point transformations described in priority 8, then measure their
   effect on guard count, site descriptors, shared reconstruction snapshots,
   live SSA values, MIR heap, machine code, executable-page utilization, and
   native completion. Add verifier checks that every remaining potentially
   exiting instruction has one exact site descriptor and one valid
   reconstruction state, whether that state is unique or shared.

   Local reconstruction snapshots now use bounded base-plus-delta chains, with
   a maximum depth of eight and tombstones for locals absent from a derived
   frame. Compiler IR is released after native compilation and rebuilt from
   bytecode for later HIR/MIR dumps or recompilation. Static snapshot types are
   derived from SSA metadata, native-resume state is allocated only for call
   boundaries, and local deltas use one slot/value entry array. In the earlier
   snapshot-compression measurement, these changes reduced `#463:sha1` retained
   metadata from 661,450 to 95,550 bytes while preserving 70,848 bytes of
   machine code and roughly 200--240 ms compilation time. After exit/effect
   analysis removes unnecessary sites, the next representation work is stack
   base/delta coalescing, interning complete reconstruction snapshots, and
   compacting site scalar fields. Metadata must fall below machine-code bytes
   without dropping reconstruction liveness dependencies or conflating
   distinct source sites.

6. **Benchmark policy rather than assuming it.** Run stable interpreter/JIT
   workloads at several pool budgets. Record peak and steady-state bytes,
   compilation and recompilation time, eviction churn, native completion, and
   execution time. A smaller pool is not an improvement if repeated compilation
   costs more than the memory it saves.

### 14.5 Definition of a completed coverage milestone

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
