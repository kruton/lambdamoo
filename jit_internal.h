#ifndef JIT_Internal_H
#define JIT_Internal_H 1

#include "config.h"

#include "hir.h"
#include "jit.h"

typedef struct JITCopy JITCopy;
typedef struct JITInstruction JITInstruction;
typedef struct JITBlock JITBlock;
typedef struct JITDeoptMap JITDeoptMap;

struct JITDeoptMap {
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned source_lineno;
    unsigned stack_depth;
    int ticks_charged;
    int num_locals;
    int *local_values;
    var_type *local_types;
    int *stack_values;
    var_type *stack_types;
    JITDeoptReason reason;
};

struct JITCopy {
    int dst;
    int src;
    JITCopy *next;
};

struct JITInstruction {
    HIRTacKind kind;
    unsigned source_lineno;
    unsigned bytecode_pc;
    int value;
    int src1;
    int src2;
    int local_id;
    HIROp op;
    Num literal;
    var_type literal_type;
    int deopt_map;
    JITCopy *copies;
    JITInstruction *next;
};

struct JITBlock {
    int id;
    int successors[2];
    int num_successors;
    JITInstruction *first;
    JITInstruction *last;
    JITBlock *next;
};

struct JITProgram {
    JITState state;
    const char *reason;
    const char *diagnostic;
    int eligible;
    int may_error;
    int num_values;
    int num_vars;
    int num_blocks;
    int num_resume_anchors;
    int num_deopt_maps;
    JITDeoptMap *deopt_maps;
    JITBlock *blocks;
    JITBlock *last_block;
    void *mir_context;
    void *native_function;
    void *machine_code;
    size_t machine_code_len;
    Num *deopt_values;
    var_type *value_types;
    unsigned char *value_is_tagged;
};

extern int jit_rt_is_true(int64_t, int);
extern int jit_rt_equality(int64_t, int, int64_t, int, int);
extern int jit_rt_str_cmp(const char *, const char *, int);
extern const char *jit_rt_str_concat(const char *, const char *, int32_t *);
extern const char *jit_rt_str_ref(const char *, int64_t, int32_t *);
extern Var *jit_rt_list_concat(Var *, Var *, int32_t *);
extern Var *jit_rt_list_append(Var *, int64_t, int);
extern int64_t jit_rt_list_in(int64_t, int, Var *);
extern int jit_rt_get_prop(int64_t, const char *, int64_t, int64_t *, int32_t *, int32_t *);
extern int64_t jit_rt_seconds_left(void);
extern int64_t jit_rt_time(void);
extern int64_t jit_rt_index(const char *, const char *);
extern int64_t jit_rt_rindex(const char *, const char *);

#endif /* !JIT_Internal_H */
