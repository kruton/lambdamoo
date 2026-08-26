#ifndef JIT_H
#define JIT_H 1

#include "config.h"

#include "structures.h"

typedef struct JITProgram JITProgram;

typedef enum {
    JIT_STATE_PENDING,
    JIT_STATE_COMPILED,
    JIT_STATE_UNSUPPORTED,
    JIT_STATE_FAILED
} JITState;

typedef enum {
    JIT_RUN_FALLBACK,
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

typedef struct {
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned source_lineno;
    unsigned stack_depth;
    int ticks_charged;
    JITDeoptReason reason;
} JITDeoptState;

typedef struct {
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned source_lineno;
} JITSourceLocation;

extern const char *jit_deopt_reason_name(JITDeoptReason);
extern void jit_profile_record_entry(void);
extern void jit_profile_record_completed(void);
extern void jit_profile_record_deopt(Objid, const char *, const JITDeoptState *);
extern void jit_profile_maybe_report(int);
extern void jit_profile_report(void);
extern void jit_profile_reset(void);

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
extern int jit_program_compile(JITProgram *);
extern JITRunResult jit_program_execute(JITProgram *, Var *, Var *, int *, int *,
					enum error *, JITSourceLocation *,
					JITDeoptState *, Var *, Objid);
extern int jit_program_dump_mir(JITProgram *, void (*)(const char *, void *),
				void *);
extern int jit_program_dump_machine(JITProgram *, void (*)(const char *, void *),
				    void *);

#endif /* !JIT_H */
