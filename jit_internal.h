#ifndef JIT_Internal_H
#define JIT_Internal_H 1

#include "config.h"

#include "functions.h"
#include "hir.h"
#include "jit.h"

typedef struct JITCopy JITCopy;
typedef struct JITInstruction JITInstruction;
typedef struct JITBlock JITBlock;
typedef struct JITDeoptMap JITDeoptMap;
typedef struct JITResumeValue JITResumeValue;
typedef struct JITProgramUsage JITProgramUsage;

typedef enum {
    JIT_RESUME_LOCAL,
    JIT_RESUME_STACK,
    JIT_RESUME_RESULT,
    JIT_RESUME_CONSTANT
} JITResumeSource;

struct JITResumeValue {
    int value;
    JITResumeSource source;
    int index;
    Num literal;
    var_type literal_type;
};

struct JITDeoptMap {
    ResumeKey resume_key;
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
    ResumeStackSlot *stack_slots;
    int num_resume_values;
    JITResumeValue *resume_values;
    int native_resume_valid;
    int builtin_func;
    int builtin_args;
    int operation;
    int guard_value[JIT_MAX_GUARD_OPERANDS];
    int guard_local[JIT_MAX_GUARD_OPERANDS];
    JITTypeMask guard_expected[JIT_MAX_GUARD_OPERANDS];
    JITDeoptReason reason;
    int native_error_block;
};

static inline int
jit_deopt_map_is_specialized_builtin(JITDeoptMap *map)
{
    return map->reason == JIT_DEOPT_ARITHMETIC_TYPE
	&& map->builtin_func >= 0 && map->builtin_args >= 0;
}

static inline int
jit_deopt_map_can_bridge_builtin(JITDeoptMap *map)
{
    return (map->reason == JIT_DEOPT_BUILTIN_CALL && map->builtin_func >= 0)
	|| jit_deopt_map_is_specialized_builtin(map);
}

static inline int
jit_deopt_map_bridges_builtin(JITDeoptMap *map)
{
    return (map->reason == JIT_DEOPT_BUILTIN_CALL && map->builtin_func >= 0)
	|| (jit_deopt_map_is_specialized_builtin(map)
	    && builtin_function_is_protected((unsigned) map->builtin_func));
}

static inline int
jit_call_stack_operands(JITDeoptMap *map)
{
    if (jit_deopt_map_is_specialized_builtin(map))
	return map->builtin_args;
    return map->reason == JIT_DEOPT_BUILTIN_CALL ? 1 : 3;
}

struct JITCopy {
    int dst;
    int src;
    JITCopy *next;
};

struct JITInstruction {
    HIRTacKind kind;
    ResumeKey resume_key;
    unsigned source_lineno;
    unsigned bytecode_pc;
    int error_block;
    int label;
    int value;
    int src1;
    int src2;
    int local_id;
    unsigned func;
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

struct JITProgramUsage {
    uint64_t entries;
    uint64_t completions;
    uint64_t vm_calls;
    uint64_t deopts;
    uint32_t deopts_by_reason[JIT_DEOPT_NUM_REASONS];
    uint64_t last_used_generation;
    time_t last_used_time;
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
    void *native_function;
    void *machine_code;
    size_t machine_code_len;
    uint64_t pool_generation;
    JITProgram *pool_prev;
    JITProgram *pool_next;
    Num *deopt_values;
    var_type *value_types;
    unsigned char *value_is_tagged;
    unsigned protection_generation;
    JITProgramUsage *usage;
    uint32_t compile_attempts;
    uint32_t compile_successes;
    uint32_t compile_failures;
    uint64_t compile_time_us;
    Objid diagnostic_object;
    unsigned diagnostic_verb;
};

extern int jit_rt_is_true(int64_t, int);
extern int jit_rt_equality(int64_t, int, int64_t, int, int);
extern int jit_rt_str_cmp(const char *, const char *, int);
extern const char *jit_rt_str_concat(const char *, const char *, int32_t *);
extern const char *jit_rt_str_ref(const char *, int64_t, int32_t *);
extern const char *jit_rt_str_range_ref(const char *, int64_t, int64_t, int32_t *);
extern Var *jit_rt_list_range_ref(Var *, int64_t, int64_t, int32_t *);
extern Var *jit_rt_list_concat(Var *, Var *, int32_t *);
extern Var *jit_rt_make_singleton_list(int64_t, int);
extern Var *jit_rt_list_append(Var *, int64_t, int);
extern Var *jit_rt_sublist_from(Var *, int64_t);
extern int64_t jit_rt_list_in(int64_t, int, Var *);
extern int jit_rt_get_prop(int64_t, const char *, int64_t, int64_t *, int32_t *, int32_t *);
extern int jit_rt_put_prop(int64_t, const char *, int64_t, int64_t, int, int32_t *);
extern int64_t jit_rt_seconds_left(void);
extern int64_t jit_rt_time(void);
extern int64_t jit_rt_index(const char *, const char *);
extern int64_t jit_rt_rindex(const char *, const char *);
extern int64_t jit_rt_valid(int64_t);
extern int64_t jit_rt_parent(int64_t, int32_t *);
extern int64_t jit_rt_var_raw(const Var *);

#endif /* !JIT_Internal_H */
