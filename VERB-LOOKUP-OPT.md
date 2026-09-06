# Verb Lookup Performance Analysis and Optimization Plan

## 1. Executive Summary

### Latest result: detailed profiling is opt-in

Removed detailed per-program accounting from the default native-call path.
Aggregate entry, completion, VM-call, deoptimization, active-frame, and memory
accounting remain enabled. Per-program entry/call/depth and continuation event
statistics are now enabled explicitly by a wizard with
`jit_profile_detail(1)` and disabled with `jit_profile_detail(0)`. Detailed
entry timestamps use the server's cached clock, so they no longer call
`time()` on every native entry. Deoptimization reasons and sites remain fully
recorded because they are correctness diagnostics rather than hot-path census
data.

After one discarded warm-up, three `#168:test2(3000)` runs took **7.900724,
8.145931, and 7.964969 seconds**, median **7.964969 s**. This is **10.18% lower**
than the prior 8.867833-second median, though the measurements were sequential
rather than interleaved. A confirming profiled run took 8.537470 seconds.
`/tmp/test2-profile-detail-off.perf.data` contains 8,640 samples with zero
losses. The former profiling entries (`jit_profile_record_native_call`,
`jit_profile_record_entry`, `jit_profile_record_completed`, and `__vdso_time`)
no longer appear above the 0.4% reporting threshold. Native entry is now 17.14%,
native-chain dispatch 4.87%, verb-call preparation 4.83%, and resume
preservation 3.74%; these are the next structural costs.

This change adds no database target cache. Enabling or disabling profiling does
not affect verb lookup, protection checks, program generations, or cache
invalidation.

### Unified activation-stack experiment: performance gate failed

Evaluated the proposed architecture in which every native boundary returns
through a fully materialized interpreter activation. The opt-in prototype used
the existing canonical deopt/resume representation, ordinary activation calls
and unwinding, and no compact continuation for new entries. It passed unit and
database correctness checks, including the real Codepoint suspension path, but
missed the agreed 5% performance gate by a wide margin and was removed.

Against the 8.867833-second compact median below, the canonical prototype
warmed in 12.747875 seconds and its first profiled run took 13.656341 seconds.
The zero-loss 8,054-sample capture `/tmp/test2-unified-stack.perf.data` shows
`jit_program_execute_in_context` at 33.99% self-time and `run` at 13.53%, versus
17.33% and 5.99% in the compact profile. `malloc` was only 2.03%, so pooling
alone cannot close the regression. Per-call canonical materialization,
interpreter dispatch, unwind, and resume lookup are the dominant difference.

The production path therefore retains compact native-to-native calls and its
promotion machinery. Resume-map indexing and the immutable runtime layout are
retained because they neither cache database targets nor weaken invalidation.
Do not remove the native chain unless a future implementation preserves its hot
call behavior and meets the same warmed performance gate.

### Latest result: resume-map indexing

Implemented the metadata-search step in section 5.3. The first resume lookup
builds a sorted, per-program index of eligible map IDs keyed by both code unit
and site. Subsequent lookups use binary search; duplicate keys preserve the
old scan's first eligible map. Empty indexes are remembered without allocating.
Index storage is included in metadata byte statistics and freed with the
program. IR release and native pool rotation retain the same deopt metadata,
so the index remains valid; replacement programs get independent indexes.

Specialized built-ins are indexed even while unprotected. Lookup still checks
current protection: toggling protection must neither hide a newly eligible
resume nor expose a stale one. No database target pointers or verb handles are
cached, and the dispatch epoch requirements in section 3.3 are unchanged.

A complete warm-up took 8.556285 s. Three profiled runs took **8.959369,
8.867833, and 8.630264 seconds**, median **8.867833 s**. The capture is
`/tmp/test2-resume-index.perf.data`, with **7,919 samples, zero losses**, at
299 Hz with DWARF stacks and `/tmp/perf-2819014.map` native symbols.
`jit_program_resume_map` fell from **1.96% to 0.21% self-time** compared with
the redundant-work capture below. Estimated sampled cycles were 61.047 billion
versus 60.657 billion previously. The median is 1.84% higher, so these sequential
runs do **not** demonstrate an end-to-end speedup despite removing the targeted
linear scan. No same-build interpreter comparison was performed.

Validation passed: server build, JIT/HIR tests, isolated native-frame verifier,
and the 73/73, zero-deopt census (only execution before emergency suspension).
Regressions cover unsorted keys, distinct code units, duplicate precedence,
missing/zero keys, non-rehydratable and insufficient-stack maps, empty indexes,
and built-in protection toggles against an already-built index. The normal
Codepoint runs exercise actual suspensions.

The largest remaining self-time entries are native entry (17.33%), verb
preparation (5.20%), and resume preservation (3.86%). Stable runtime-buffer
reuse and immutable entry-layout precomputation remain the next substantial
projects; ancestor profiling walks also remain unchanged. This focused step
does not implement storage pooling or region compilation.

### Previous result: redundant-work removal

Implemented the four focused reductions from section 5.1:

* Zero-root preservation skips its second capture scan, but still validates
  candidates/owners and releases old roots. Complex-root capture is unchanged.
* The native-call container initializes its non-frame fields explicitly;
  compact push performs the only full frame clear. Failed preparation frees
  the raw container without reading the uninitialized frame.
* Entry-map metadata is filled only for compilation failure or a native exit
  without an exact map. Ordinary returns retain defined empty deopt output;
  exact boundaries fill their own map metadata without first copying map zero.
* An explicit prepared-entry argument skips the second compile validation
  immediately after successful compact commit. The trampoline resets it after
  that entry. Roots, caller resumes, built-in resumes, and standalone execution
  retain normal protection/pool-generation validation. No target pointer cache
  or new database invalidation mechanism was introduced.

After rebuilding, a complete warm-up took 8.961665 s. Three profiled
`#168:test2(3000)` runs took **8.707435, 8.711307, and 8.654280 seconds**:
median **8.707435 s**, an observed **4.18% reduction** from the 9.087201 s
baseline below. `/tmp/test2-dedup-final.perf.data` contains **7,806 samples,
zero lost samples**, collected with the same 299 Hz DWARF method and native
symbol mapping. Estimated sampled cycles fell from 63.060 billion to
60.657 billion (3.81%) across the three-run intervals. These are sequential
measurements, not an interleaved controlled experiment or an interpreter
comparison; they support a modest improvement, not parity.

| Self-time symbol | Before | After |
| :--- | ---: | ---: |
| `jit_program_execute_in_context` | 17.37% | 17.99% |
| `jit_native_frame_preserve_resume` | 4.39% | 3.40% |
| `execute_jit_dispatch_native_verb_call` | 2.71% | 2.48% |
| `jit_program_compile.part.0` | 1.29% | 1.05% |
| libc `memset` | 1.61% | 1.68% |

The dispatcher-side duplicate `memset` path is absent in the final call graph;
the remaining frame clear still accounts for 1.50% of total samples. Its
overall share did not fall, so do not attribute a measured speedup to clearing
alone. The entry wrapper's share also did not decrease. The clearest profile
reduction is resume scanning; removing these duplicates leaves substantial
runtime setup/materialization work for the next pass.

Validation passed: rebuilt server, `make test-jit test-hir-tac`, an isolated
`JIT_VERIFY_NATIVE_FRAMES` JIT test build, and the testmoo census (73/73 completed,
zero deopts, covering only execution before its emergency-mode suspension).
Added regressions check uncompiled prepared-entry fallback, compiled entry,
complex-root retention followed by zero-root replacement and byte cleanup,
and absence of stale boundary metadata after native return. Normal Codepoint
benchmark runs also completed through their real suspension paths.

An intermediate wrapper-based entry experiment is recorded in
`/tmp/test2-dedup.perf.data` (8.971575, 13.933060, 8.791285 s). The final version
uses one entry function with an explicit prepared flag to avoid wrapper-call
overhead; use the final capture above for this implementation. Remaining
projects are runtime-buffer reuse, resume-map indexing, and cheaper profiling
statistics; they are not part of this duplicate-work change.

### Baseline profile: committed compact-call implementation

Profiled commit `aeb8967` on September 5, 2026, using the existing optimized
binary and a disposable `codepoint.db` server on port 7797. Logged in as the
wizard, completed a full `#168:test2(3000)` warm-up (8.667862 s), enabled
`jit_perf_map(1)`, and attached `perf` only afterward. Three complete measured
runs took **9.182183, 8.981343, and 9.087201 seconds** (median **9.087201 s**).
These are the workload's returned elapsed times, not rounded `time()` values.

The capture is `/tmp/test2-refresh-complete.perf.data`: **8,145 samples, zero
lost samples**, 299 Hz cycles sampling with DWARF call graphs. The native symbol
map is `/tmp/perf-2814384.map`; the server log is
`/tmp/codepoint-profile-refresh.log`, and the coordinating script is
`/tmp/profile-codepoint-refresh.py`. Startup, warm-up, and symbol-map setup
were outside the sampled interval. The interval covers all three runs plus
short idle gaps. Discard `/tmp/test2-refresh.perf.data` for benchmark reporting:
its third run was interrupted by a connection handoff. The older 234-sample
profile below is superseded by this complete capture.

| Symbol or disjoint self-time group | Current share |
| :--- | ---: |
| `jit_program_execute_in_context` | 17.37% |
| `run` | 5.94% |
| `prepare_verb_call_for_caller` | 4.77% |
| `jit_native_frame_preserve_resume` | 4.39% |
| `run_jit_native_chain` | 3.99% |
| `malloc` + `cfree` + `_int_malloc` + `__libc_malloc2` | 7.77% |
| `free_rt_env` + `new_rt_env` + `set_rt_env_var` + `fill_in_rt_consts` | 6.91% |
| `execute_jit_dispatch_native_verb_call` | 2.71% |
| `jit_execution_context_return_compact` | 2.03% |
| `jit_program_resume_map` | 1.76% |
| `db_find_callable_verb` + `str_hash` + `mystrcasecmp` | 4.12% |
| libc `memset` | 1.61% |
| `jit_program_compile.part.0` | 1.29% |
| `jit_profile_record_native_call` + entry + completed | 2.88% |

These are self shares of sampled cycles, not inclusive time or predicted
savings. Generated native symbols sum to approximately 7.60%; that does not
mean the rest is removable overhead, since native runtime helpers, allocation,
reference counting, and interpreter execution perform necessary work too.
Nevertheless, entry/resume bookkeeping is now a substantially larger target
than name lookup. No same-build interpreter control was run in this refresh,
so this profile does not establish the remaining interpreter slowdown ratio.
The profiled median is approximately 15% below the historical 10.69-second
lookup baseline; the earlier unprofiled 8.75-second result remains historical,
not the median of this capture.

### Historical lookup comparison

Two warm-cache CPU profiles cover the same `#168:test2(3000)` workload, which
runs `capital_sigma0` approximately 960,000 times.  Both used an unprofiled
warm-up followed by a second run sampled at 299 Hz with DWARF call graphs and
no lost samples:

* before the pending lookup changes: `/tmp/test2-lazy-hot.perf.data`, 10.51 s;
* after the lookup and parent-invalidation changes:
  `/tmp/test2-lookup-hot.perf.data`, 10.69 s (warm-up 10.64 s).

The wall-time difference is within the observed run-to-run variation and is
not evidence of a speedup.  The flat profile nevertheless shows that cached
verb indices and cheaper global-cache probing removed work from the intended
locations.  The selected lookup and dispatch symbols fell from 15.36% to
13.93% of sampled cycles.

| Symbol | Before | After | Observation |
| :--- | ---: | ---: | :--- |
| `prepare_verb_call_for_caller` | 3.76% | 3.99% | Setup remains expensive |
| `db_find_callable_verb` | 3.49% | 2.43% | 30% lower self share |
| `execute_jit_dispatch_native_verb_call` | 2.41% | 2.24% | Slightly lower |
| `db_verb_index` | 1.90% | 0.09% | 95% lower; index caching worked |
| `mystrcasecmp` | 1.49% | 1.90% | Still hot; pointer identity rarely avoids it |
| `str_hash` | 1.36% | 2.06% | Still hot; repeated hashing remains |
| `execute_jit_direct_verb_call` | 0.95% | 1.22% | Speculative first lookup remains |

Those profiles motivated removal of double resolution before adding a
call-site cache. Any future target cache still requires the invalidation and
pointer-lifetime contract in section 3.3.

That first step is now implemented.  Native verb instructions always use the
compact trampoline, so each dynamic call performs one shared resolution.  The
speculative direct-leaf helper and its generated-code import were removed.
After one unmeasured warm-up, `#168:test2(3000)` fell to 9.07 seconds and a
subsequent final warm run measured 8.75 seconds, approximately 18% below the
10.69-second lookup baseline.  A post-change profile is stored at
`/tmp/test2-native-overhead.perf.data`; it had no lost samples, although its
234 samples are superseded by the complete capture above.

---

## 2. Why Verb Lookup Takes So Long

Analysis of the code and `perf annotate` disassemblies reveals five distinct
bottlenecks:

### 2.1 Double Resolution on Non-Leaf Native Calls (Addressed)

Before the current change, `HIR_TAC_CALL_VERB` generated a direct call to
`execute_jit_direct_verb_call()`:

1. `execute_jit_direct_verb_call()` calls `resolve_verb_call()` ->
   `db_find_callable_verb()`, consuming **1.62%** of all CPU samples.
2. It then inspects `jit_program_is_direct_leaf(callee->jit)`. If the target
   calls any other verb (as `capital_sigma0` does when calling `ROTR`), it is
   not a direct leaf and returns `0`.
3. The JIT code branches to `materialize` (`JIT_RUN_CALL_VERB`), returning to
   the native trampoline `run_jit_native_chain()`.
4. `run_jit_native_chain()` invokes `dispatch_jit_native_boundary()` ->
   `execute_jit_dispatch_native_verb_call()`.
5. `execute_jit_dispatch_native_verb_call()` invokes `resolve_verb_call()` ->
   `db_find_callable_verb()` **a second time**, consuming another **1.59%** of
   all CPU samples.

Nearly half of the samples in `db_find_callable_verb` are spent tentatively
resolving a callee that is immediately discarded and re-resolved.
The helper has now been removed; this description is retained to explain the
10.69-to-9.07-second improvement and the choice not to add another target
cache without a complete invalidation contract.

### 2.2 Hardware Integer Division (`divl`) in Cache Probing (Addressed)

Before the pending change, the global verb cache used a prime table size
(`DEFAULT_VC_SIZE` = 7507):

```c
bucket = hash % vc_size;
```

Before the pending change, a runtime variable modulo by a non-power-of-two
emitted the hardware `divl` instruction on x86_64.

The cache retains 8,192 buckets and a mask.  In the earlier receiver-key
experiment, removal of the pre-probe parent walk together with the mask reduced `db_find_callable_verb` from 3.49% to 2.43%
self-time.  The profile does not isolate the savings of the mask from the key
change, so no separate percentage should be claimed for it.

### 2.3 Parent Hierarchy Walking Before Cache Probe (Retained)

Before probing `vc_table`, `db_find_callable_verb()` executes:

```c
for (o = dbpriv_find_object(oid); o; o = dbpriv_find_object(o->parent)) {
    if (o->verbdefs != NULL)
        break;
}
```

The cache retains the first ancestor with verbs as its key, allowing receivers
with the same first ancestor to share positive and negative entries.  The
receiver-OID experiment has been removed.  On a miss, lookup continues from
that ancestor rather than repeating the walk.  Reparenting a childless object
without verbs can still skip cache invalidation because the next lookup
recomputes its ancestor key.

### 2.4 Dynamic Hashing and String Comparison on Cache Hits (Still Open)

Even though verb names at bytecode/JIT callsites are constant strings,
`str_hash(verb)` re-hashes the string character-by-character on every lookup
(1.36% flat self-time).

The cache now checks string pointer identity before `mystrcasecmp()`, but the
updated profile still attributes 2.06% to `str_hash` and 1.90% to
`mystrcasecmp`.  The pointer fast path therefore does not eliminate most name
work in this workload.  Cache or precompute the hash for literal call-site verb
names, and measure whether making cache entries retain the original shared
string identity is safe and useful.

### 2.5 Linear Linked-List Scan in `db_verb_index()` (Addressed)

In `execute.c`, `prepare_verb_call_for_caller()` calls
`db_verb_index(call->handle)`.

`db_verb_index()` sequentially iterates the singly linked list of verbs on the
defining object:

```c
o = dbpriv_find_object(h->definer);
for (v = o->verbdefs, index = 1; v; v = v->next, index++)
    if (v == h->verbdef)
        return index;
```

`perf annotate` shows that **78.37%** of the samples inside `db_verb_index`
(which accounts for **1.90%** of total server CPU time) are spent in this
pointer-chasing loop.

Handles now record the index while walking the verb list for lookup, and
`db_verb_index()` returns that cached value.  Its self-time fell from 1.90% to
0.09%.  `jit_program_note_location()` also skips an unchanged diagnostic
location and accounts for 0.31% in the updated profile.  Further work here is
lower priority than repeated resolution, hashing, allocation, and frame setup.

---

## 3. Monomorphic Callsite Trade-offs

A monomorphic callsite caches the target verb and checks if the receiver matches
the previous invocation.

### 3.1 Inlined in MIR (Machine Code Expansion)

Emitting monomorphic inline caches (MICs) directly into generated MIR requires:

* Loading and comparing the receiver object ID.
* Loading and comparing `db_verb_generation` (to invalidate on verb mutations).
* Generating fast-path invocation code and a fallback branch to slow-path dispatch.

**Drawbacks:**
* **Code Bloat**: Adds 15 to 25 machine instructions per callsite. Hot MOO
  methods often contain dozens of verb calls (e.g., cryptographic or math loops
  like `raw_hash`).
* **JIT Pool Pressure**: The JIT shares a single code pool with a hard memory
  limit (default 256 MiB). Rapid pool growth triggers expensive whole-pool
  rotations (`jit_pool_reset()`), discarding compiled code.
* **I-Cache Locality**: Larger code footprints degrade instruction cache
  utilization.

### 3.2 Out-of-Line Call-Site Inline Cache (Recommended)

As noted in `JIT-PLAN.md`, callsite profiling and cache state belong outside
generated MIR.

Instead of inlining guards in machine code, the JIT program maintains a small
array of out-of-line cache entries indexed by callsite ID:

```c
typedef struct {
    Objid cached_oid;
    uint64_t cached_epoch;
    Program *cached_program;
    db_verb_handle cached_handle;
} JITVerbCallSiteIC;
```

The generated MIR passes `&program->callsite_ics[site_id]` to the dispatch
helper. The helper executes a fast guard in C:

```c
if (MOO_LIKELY(receiver == ic->cached_oid
               && db_dispatch_epoch == ic->cached_epoch)) {
    // Fast path: callee program and handle already known.
    // Completely bypasses resolve_verb_call, db_find_callable_verb,
    // str_hash, mystrcasecmp, and db_verb_index.
} else {
    // Slow path: resolve verb and populate ic.
}
```

**Conclusion on Trade-off**: Fully inlined MIR monomorphic callsites are **not**
worth the code bloat.  An **out-of-line call-site inline cache** can avoid the
same lookup work with virtually zero generated-code growth, but the illustrative
structure above is not safe until the following lifetime rules are implemented.

### 3.3 Cache Invalidation and Pointer Lifetime

`db_verb_handle` is not stable storage.  Callable-verb-cache handles point into
entries freed by `db_priv_affected_callable_verb_lookup()`.  `Program *` is also
non-owning when obtained from a verb handle and can be freed when verb code is
replaced.  A call-site entry must either own an explicit program reference or
treat both fields as non-owning and compare the dispatch epoch before either is
dereferenced.  This is safe only within the server's single-threaded dispatch
interval; no cached pointer may escape across a callback or safepoint that can
mutate the database.

The current `db_verb_generation` is not yet a sufficient JIT dispatch epoch:

* `db_set_verb_program()` does not advance it because replacing code does not
  change which `Verbdef` the global lookup cache selects;
* `db_priv_affected_callable_verb_lookup()` returns without advancing it when
  the global cache table has not been allocated; and
* its finite-width equality guard needs explicit wrap handling to prevent an
  old entry from matching again.

Before caching a selected program, introduce a wide epoch which advances before
old target storage is released for verb addition, deletion, renaming, executable
permission or argument changes, program replacement, parent changes, object
renumbering or recycling, and relevant WAIF dispatch-class changes.  On epoch
wrap, JIT pool rotation, program destruction, or code invalidation, clear the
associated call-site entries or make them unreachable before releasing their
targets.

The global cache retains ancestor keys and the existing `db_change_parent()`
shortcut for childless objects without verbs.  A future receiver-key or
call-site cache must revisit that shortcut.  Regression checks should warm
inherited positive and negative lookups, reparent the leaf, and verify the
new ancestry; replace verb code at a hot call site; rename, delete, and recreate
the selected verb; recycle and reuse an OID; and change a WAIF dispatch class.

---

## 4. Optimization Roadmap

### Phase 1: C Runtime Lookup Optimizations (Committed, Measured)

1. **Cache `db_verb_index()` in each handle.**
   * Implemented by recording the index during the lookup walk.
   * Measured self-time fell from 1.90% to 0.09%.

2. **Use a power-of-two verb-cache size.**
   * Implemented with a fixed table of 8,192 buckets and a mask.

3. **Test string pointer identity before `mystrcasecmp()`.**
   * Implemented, but `mystrcasecmp` rose from 1.49% to 1.90% of the updated
     sample.  Do not claim the projected saving; most hot names do not appear
     to share the cache entry's retained pointer.

4. **Retain the first-ancestor-with-verbs cache key.**
   * The receiver-OID experiment was removed in favor of shared cache entries.
   * Retain the existing leaf-object reparenting invalidation shortcut.

The earlier combined measurements included the receiver-OID experiment and do
not establish the performance of this retained configuration.

### Phase 2: Eliminate JIT Double Resolution (Implemented)

1. **Avoid the rejected direct-leaf resolution.**
   * Implemented by removing the speculative path.  `HIR_TAC_CALL_VERB` now
     exits directly through the compact native-chain dispatcher.
   * This deliberately avoids retaining a volatile verb handle and needs no
     new invalidation mechanism.  The shared global lookup cache remains the
     only dispatch cache.
   * The warmed SHA workload improved by approximately 15%.  This confirms
     that the former double lookup was real end-to-end work rather than merely
     a large percentage in a shifted profile.

### Phase 3: Out-of-Line Call-Site Inline Caches

1. Implement and test the wide dispatch epoch and pointer-ownership rules from
   section 3.3 before storing any target pointer.
2. Allocate a `JITVerbCallSiteIC` table per `JITProgram` for call-site entries.
3. Direct native calls check the cache cell before falling back to
   `resolve_verb_call()`.
4. Clear entries on program destruction and JIT pool invalidation.  Verify all
   mutation regressions before enabling the fast path for database workloads.

### Phase 4: Reduce Call-Path Allocation and Frame Setup (Partially Implemented)

The historical lookup profile attributed 4.70% to `malloc`, 3.89% to `free`, 3.99%
to `prepare_verb_call_for_caller`, and 2.27% to lazy resume preservation.  After
removing duplicate resolution, measure a reusable pool for `JITNativeCall`
containers, callee environments, and resume-root arrays.  Reuse must preserve
the existing single-owner cleanup paths and clear every retained `Var`, map,
program, and cache reference before publication to another call.

Compact calls now allocate their `JITNativeCall` container and boundary stack
as one object, eliminating the separate maximum-stack allocation and copy.
Boundary materialization writes directly into that stack.  Lazy resume
preservation first classifies live values and allocates a root array only when
complex values actually require independent retention; scalar-only resumes
allocate no root array.  The production boundary path also omits the complete
runtime-tag verifier scan, which remains available under
`JIT_VERIFY_NATIVE_FRAMES`.

Together with removal of blanket production tag-slot initialization, the final
warm run measured 8.75 seconds.  The remaining large costs are the full
per-call environment construction and native runtime allocation, plus their
reference-count cleanup.  Reusing either safely requires stable depth-indexed
storage whose buffers cannot move while a caller resume references them; that
work remains the next non-region optimization.

## 5. Priorities From the Complete Post-Commit Profile

### 5.1 Remove redundant work before introducing a storage pool

The concrete duplicate-work changes below are now implemented as summarized
above. Broader entry-layout precomputation and compact diagnostic records
remain follow-up work. The percentages in this section describe the baseline.

1. **Skip the second resume scan when `root_capacity == 0`.**
   `jit_native_frame_preserve_resume()` consumes 4.39% self-time. Its first
   pass already validates candidates and owner homes and proves whether any
   independently retained roots are needed. The second pass still traverses
   every candidate, reloads dynamic tags, and repeats capture classification
   even when the count is zero. Annotated samples occur in both scans. Keep
   first-pass validation and old-root release, but bypass the second scan in
   that case. Later, compile a smaller capture recipe to avoid rediscovering
   static source/type facts at runtime. The 4.39% is the entire helper's cost,
   not the saving available from removing one loop.

2. **Clear the compact frame once.** The dispatcher zeroes the complete
   `JITNativeCall`; `jit_execution_context_push_compact()` then zeroes its
   embedded frame again. Call graphs attribute 0.81% of total samples to the
   dispatch-side libc `memset` and 0.75% to the compact-push `memset`. Initialize
   container/resume fields separately and let push initialize the frame once.
   Preserve safe cleanup on pre-publication failure; do not remove clearing
   until every failure path has a defined field/ownership contract.

3. **Split hot native entry from full deopt reporting.** The 17.37% entry
   wrapper initializes a complete `JITDeoptState`, copies map-zero metadata,
   calculates runtime layout, binds storage, and later fills boundary metadata.
   Annotation places samples in initial metadata copies, owner-state updates,
   and stack materialization, not one dominant instruction. Precompute immutable
   layout offsets and construct diagnostic/guard fields only on paths that
   consume them. Keep the exact PCs, ticks, operand ownership, and map identity
   needed for compact dispatch and promotion. A plain native return should
   avoid preparing an unused interpreter reconstruction record.

4. **Avoid duplicate compile validation within one uninterrupted entry.**
   Compact commit calls `jit_program_compile()` and execution calls it again;
   resumes also call it. Its 1.29% share includes fast validation, not evidence
   that hot verbs are being regenerated. An internal prepared-entry path can
   remove a redundant check only while no mutation/safepoint intervenes.
   Preserve built-in protection-generation checks and JIT pool-generation
   checks at appropriate entry boundaries, especially after built-in calls.

### 5.2 Reuse runtime storage, preserving actual value ownership

Allocator self-time is 7.77%, but not all of it is frame storage: the `malloc`
call graph attributes 1.24% of total samples to fixed-list construction and
1.16% through `jit_program_execute_in_context`. Freeing through that wrapper
accounts for 1.96%, including value cleanup; freeing native call containers
accounts for 0.79%. These path shares overlap the allocator row above and
must not be added to it.

Prioritize reusable runtime buffers and call containers at stable native
depths. Preserve raw capacity after releasing every owning `Var`, and never
move a buffer referenced by a suspended caller. Promotion/continuation transfer
must either transfer exclusive ownership or copy state before recycling.
The current call-owned stack already survives resumes; allocating another
stack pool solely to avoid a per-resume stack malloc would target work that
has already been removed.

Environment construction plus its direct setup/cleanup helpers accounts for
11.68% self-time (4.77% + 6.91%), excluding shared complex ref/free helpers.
However, `eval_env.c` already pools environments up to `NUM_READY_VARS`.
Another pool alone cannot remove initialization, constant filling, command
variable copying, or reference-count traffic. Measure environment sizes and
bytes/slots touched before expanding pooling. Selective initialization requires
proof that fallback, introspection, and promotion can recover all canonical
locals; raw memory reuse does not provide that proof.

### 5.3 Remove repeated metadata searches and profiling walks

`jit_program_resume_map()` formerly linearly scanned all deopt maps (1.76%
in the original profile). The immutable index is now implemented, keyed by
both `ResumeKey.code_unit` and `ResumeKey.site`, without assuming the general
deopt-map array is sorted. It is built lazily for finalized metadata and
released with that metadata. Specialized built-in protection remains a dynamic
lookup check. See the latest result above; this per-program metadata index
does not require a database dispatch epoch.

`jit_profile_record_native_call()` is 1.39% and walks every ancestor on every
call to update depth statistics. Entry recording adds 1.01% and calls `time(0)`.
Consider propagating depth maxima at return/promotion or batching timestamps,
while preserving defined statistics and pool-recency behavior. Instrumentation
should not add an O(depth) traversal to every ordinary native call.

### 5.4 Keep target caching behind the lifetime contract

Lookup, hashing, and name comparison now total 4.12% self-time. Even removing
all three would save only roughly 4% of current sampled CPU work under an
unchanged workload. A monomorphic target cache cannot by itself close the
reported interpreter gap. Prefer the redundant scans, initialization, and
runtime-storage work above first. If a target cache is later implemented,
retain all mutation/epoch/wrap requirements in section 3.3; a cached raw
`db_verb_handle` or `Program *` is still unsafe across invalidation.

For each implementation, compare complete warmed runs and allocation counts,
verify suspension/return/error cleanup, and retain the native-frame verifier
configuration for correctness checks. Rerun a same-source interpreter control
before claiming parity. Section 5 records the original profile-driven analysis;
the latest-result section identifies which changes are now implemented.
