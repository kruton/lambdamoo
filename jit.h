#ifndef JIT_H
#define JIT_H 1

#include "config.h"

#include "my-time.h"

#include "program.h"
#include "structures.h"

typedef struct JITProgram JITProgram;
typedef struct JITContinuationFrame JITContinuationFrame;
struct activation;

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
extern int jit_program_anchor_count(JITProgram *);
extern int jit_program_deopt_map_count(JITProgram *);
extern void jit_program_stats(JITProgram *, JITProgramStats *);
extern int jit_program_resume_map(JITProgram *, ResumeKey);
extern int jit_program_has_location(JITProgram *);
extern void jit_program_note_location(JITProgram *, Objid, unsigned);
extern int jit_program_compile(JITProgram *);
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
