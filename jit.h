#ifndef JIT_H
#define JIT_H 1

#include "config.h"

#include "my-time.h"

#include "program.h"
#include "structures.h"

typedef struct JITProgram JITProgram;
typedef struct JITContinuationFrame JITContinuationFrame;
typedef struct JITExecutionContext JITExecutionContext;
typedef struct JITNativeFrame JITNativeFrame;
typedef struct JITCallerResume JITCallerResume;
typedef struct JITPromotionPlan JITPromotionPlan;
struct activation;
struct PreparedVerbCall;

typedef enum {
    JIT_FRAME_ROOT_OVERLAY,
    JIT_FRAME_CANONICAL_OVERLAY,
    JIT_FRAME_COMPACT
} JITNativeFrameKind;

typedef enum {
    JIT_FRAME_PREPARING,
    JIT_FRAME_RUNNING,
    JIT_FRAME_SUSPENDED,
    JIT_FRAME_RETURNED,
    JIT_FRAME_PROMOTED,
    JIT_FRAME_DETACHED
} JITNativeFrameState;

typedef enum {
    JIT_HOME_EMPTY,
    JIT_HOME_OWNED,
    JIT_HOME_CONSUMED
} JITFrameHomeState;

typedef enum {
    JIT_RESUME_PREPARING,
    JIT_RESUME_DISPATCHED,
    JIT_RESUME_RETURNED,
    JIT_RESUME_PROMOTED
} JITCallerResumeState;

struct JITCallerResume {
    JITNativeFrame *caller;
    int map_id;
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned result_home;
    JITCallerResumeState state;
};

struct JITNativeFrame {
    JITExecutionContext *context;
    JITProgram *program;
    JITNativeFrame *caller;
    JITNativeFrame *callee;
    JITCallerResume *incoming;
    JITCallerResume *outgoing;
    Program *bytecode_program;
    Var *env;
#ifdef WAIF_CORE
    Var receiver;
#endif
    Objid this;
    Objid player;
    Objid progr;
    Objid vloc;
    const char *verb;
    const char *verbname;
    void *runtime_storage;
    Var *homes;
    unsigned char *home_states;
    size_t runtime_bytes;
    unsigned num_homes;
    unsigned canonical_index;
    int entry_map;
    int current_map;
    int debug;
    int owns_invocation;
    int owns_runtime;
    JITNativeFrameKind kind;
    JITNativeFrameState state;
};

struct JITExecutionContext {
    JITNativeFrame *root_frame;
    JITNativeFrame *current_frame;
    unsigned root_activation_index;
    unsigned canonical_depth;
    unsigned native_depth;
    unsigned activation_limit;
    int *ticks_remaining;
    int *task_timed_out;
    enum error *pending_error;
};

typedef void (*JITPromotionMaterializer) (JITNativeFrame *,
					 JITCallerResume *, void *);

typedef enum {
    JIT_STATE_PENDING,
    JIT_STATE_COMPILED,
    JIT_STATE_UNSUPPORTED,
    JIT_STATE_FAILED
} JITState;

typedef enum {
    JIT_RUN_FALLBACK,
    JIT_RUN_CALL_VERB,
    JIT_RUN_RETURNED,
    JIT_RUN_ERROR,
    JIT_RUN_ABORT_TICKS,
    JIT_RUN_ABORT_SECONDS
} JITRunResult;

typedef enum {
    JIT_DEOPT_NONE = 0,
    JIT_DEOPT_BUILTIN_CALL,
    JIT_DEOPT_VERB_CALL,
    JIT_DEOPT_PROPERTY_READ,
    JIT_DEOPT_PROPERTY_WRITE,
    JIT_DEOPT_RANGE_OP,
    JIT_DEOPT_TYPE_GUARD,
    JIT_DEOPT_BRANCH_TYPE,
    JIT_DEOPT_CONTROL_FLOW,
    JIT_DEOPT_ARITHMETIC_TYPE,
    JIT_DEOPT_UNSUPPORTED_OP,
    JIT_DEOPT_NUM_REASONS
} JITDeoptReason;

typedef enum {
    JIT_BOUNDARY_NONE,
    JIT_BOUNDARY_BUILTIN,
    JIT_BOUNDARY_VERB,
    JIT_BOUNDARY_SUSPEND_ZERO
} JITBoundaryKind;

typedef uint16_t JITTypeMask;

#define JIT_MAX_GUARD_OPERANDS 2
#define JIT_TYPE_MASK(type) \
    ((JITTypeMask) 1U << ((unsigned) (type) & TYPE_DB_MASK))

typedef struct {
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned source_lineno;
    unsigned stack_depth;
    int materialized;
    int ticks_charged;
    int builtin_func;
    int operation;
    int guard_value[JIT_MAX_GUARD_OPERANDS];
    int guard_local[JIT_MAX_GUARD_OPERANDS];
    JITTypeMask guard_expected[JIT_MAX_GUARD_OPERANDS];
    var_type guard_actual[JIT_MAX_GUARD_OPERANDS];
    JITDeoptReason reason;
    JITBoundaryKind boundary;
} JITDeoptState;

typedef struct {
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned source_lineno;
} JITSourceLocation;

typedef struct {
    uint64_t entries;
    uint64_t completions;
    uint64_t vm_calls;
    uint64_t deopts;
    uint64_t deopts_by_reason[JIT_DEOPT_NUM_REASONS];
    uint64_t last_used_generation;
    time_t last_used_time;
    uint64_t compile_attempts;
    uint64_t compile_successes;
    uint64_t compile_failures;
    uint64_t compile_time_us;
    uint64_t continuation_captures;
    uint64_t continuation_resumes;
    uint64_t continuation_materializations;
    uint64_t continuation_fast_suspends;
    uint64_t active_continuations;
    size_t continuation_bytes;
    size_t metadata_bytes;
    size_t runtime_bytes;
    size_t machine_code_bytes;
    size_t native_allocated_bytes;
    size_t accounted_bytes;
} JITProgramStats;

typedef struct {
    uint64_t generation;
    uint64_t active_programs;
    size_t total_machine_code_bytes;
    size_t total_native_allocated_bytes;
    size_t total_mir_heap_bytes;
    uint64_t active_continuations;
    size_t continuation_bytes;
} JITPoolStats;

extern const char *jit_deopt_reason_name(JITDeoptReason);
extern void jit_profile_record_entry(JITProgram *);
extern void jit_profile_record_completed(JITProgram *);
extern void jit_profile_record_vm_call(JITProgram *);
extern void jit_profile_record_deopt(JITProgram *, Objid, const char *,
				     const JITDeoptState *);
extern void jit_profile_maybe_report(int);
extern void jit_profile_report(void);
extern void jit_profile_reset(void);
extern void jit_pool_stats(JITPoolStats *);
extern void jit_pool_reset(void);
extern void jit_shutdown(void);

extern void jit_execution_context_init(JITExecutionContext *, JITNativeFrame *,
				       JITProgram *, Var *, unsigned, unsigned,
				       unsigned, int *, int *, enum error *, int);
extern int jit_execution_context_push_overlay(JITExecutionContext *,
					      JITNativeFrame *, JITProgram *, Var *,
					      unsigned, int);
extern int jit_execution_context_pop_overlay(JITExecutionContext *,
					     JITNativeFrame *);
extern int jit_execution_context_push_compact(JITExecutionContext *,
					      JITNativeFrame *, JITProgram *, Var *,
					      JITCallerResume *, int);
extern int jit_execution_context_return_compact(JITExecutionContext *,
						JITNativeFrame *, Var *);
extern JITPromotionPlan *jit_native_chain_prepare_promotion(
	JITExecutionContext *);
extern unsigned jit_native_chain_promotion_count(const JITPromotionPlan *);
extern JITNativeFrame *jit_native_chain_promotion_frame(
	const JITPromotionPlan *, unsigned);
extern int jit_native_chain_commit_promotion(JITPromotionPlan *,
	JITPromotionMaterializer, void *);
extern void jit_native_chain_discard_promotion(JITPromotionPlan *);
extern int jit_execution_context_finish(JITExecutionContext *,
					JITNativeFrame *);
extern int jit_native_frame_bind_activation(JITNativeFrame *,
					    const struct activation *);
extern int jit_native_frame_copy_invocation(JITNativeFrame *,
					    const struct activation *);
extern int jit_native_frame_take_prepared_invocation(
	JITNativeFrame *, struct PreparedVerbCall *);
extern void jit_native_frame_release_invocation(JITNativeFrame *);
extern void jit_native_frame_bind_runtime(JITNativeFrame *, void *, size_t,
					  Var *, unsigned, unsigned char *);
extern void jit_native_frame_mark_runtime_owned(JITNativeFrame *);
extern void jit_native_frame_release_runtime(JITNativeFrame *);
extern void jit_native_frame_unbind_runtime(JITNativeFrame *);
extern int jit_native_frame_verify(const JITExecutionContext *,
				   const JITNativeFrame *);
extern int jit_native_frame_home_move(JITNativeFrame *, unsigned, Var *);
extern int jit_native_frame_home_take(JITNativeFrame *, unsigned, Var *);
extern int jit_native_frame_prepare_activation(JITNativeFrame *,
					       struct activation *, int, int);

extern JITProgram *jit_program_unsupported(const char *);
extern JITProgram *jit_program_unsupported_with_diagnostic(const char *, const char *);
extern void jit_program_free(JITProgram *);
extern int jit_program_bytes(JITProgram *);
extern JITState jit_program_state(JITProgram *);
extern const char *jit_program_state_name(JITProgram *);
extern const char *jit_program_reason(JITProgram *);
extern const char *jit_program_diagnostic(JITProgram *);
extern int jit_program_is_eligible(JITProgram *);
extern int jit_program_may_error(JITProgram *);
extern int jit_program_is_direct_leaf(JITProgram *);
extern int jit_program_anchor_count(JITProgram *);
extern int jit_program_deopt_map_count(JITProgram *);
extern void jit_program_stats(JITProgram *, JITProgramStats *);
extern int jit_program_resume_map(JITProgram *, ResumeKey);
extern int jit_program_has_location(JITProgram *);
extern void jit_program_note_location(JITProgram *, Objid, unsigned);
extern int jit_program_compile(JITProgram *);
extern JITRunResult jit_program_execute_in_context(JITProgram *,
						   JITExecutionContext *,
						   JITNativeFrame *, Var *, Var *,
						   int *, int *, enum error *,
						   JITSourceLocation *, JITDeoptState *,
						   Var *, Objid, int,
						   JITContinuationFrame *,
						   JITContinuationFrame **);
extern JITRunResult jit_program_execute(JITProgram *, Var *, Var *, int *, int *,
				enum error *, JITSourceLocation *,
				JITDeoptState *, Var *, Objid, int,
				JITContinuationFrame *, JITContinuationFrame **);
extern void jit_continuation_set_result(JITContinuationFrame *, Var);
extern void jit_continuation_mark_dispatched(JITContinuationFrame *);
extern void jit_continuation_attach(JITContinuationFrame *, struct activation *);
extern void jit_continuation_relocate(JITContinuationFrame *, struct activation *);
extern int jit_continuation_materialize(struct activation *);
extern void jit_continuation_free(JITContinuationFrame *);
extern void jit_continuation_materialize_all(void);
extern int jit_program_dump_hir(JITProgram *, void (*)(const char *, void *),
				void *);
extern int jit_program_dump_mir(JITProgram *, void (*)(const char *, void *),
				void *);
extern int jit_program_dump_machine(JITProgram *, void (*)(const char *, void *),
				    void *);

#endif /* !JIT_H */
