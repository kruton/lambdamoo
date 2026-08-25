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

typedef struct {
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned stack_depth;
    int ticks_charged;
} JITDeoptState;

extern JITProgram *jit_program_unsupported(const char *);
extern void jit_program_free(JITProgram *);
extern int jit_program_bytes(JITProgram *);
extern JITState jit_program_state(JITProgram *);
extern const char *jit_program_state_name(JITProgram *);
extern const char *jit_program_reason(JITProgram *);
extern int jit_program_is_eligible(JITProgram *);
extern int jit_program_may_error(JITProgram *);
extern int jit_program_anchor_count(JITProgram *);
extern int jit_program_deopt_map_count(JITProgram *);
extern int jit_program_compile(JITProgram *);
extern JITRunResult jit_program_execute(JITProgram *, Var *, Var *, int *, int *,
					enum error *, JITDeoptState *);
extern int jit_program_dump_mir(JITProgram *, void (*)(const char *, void *),
				void *);

#endif /* !JIT_H */
