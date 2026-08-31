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
typedef struct JITNativeResume JITNativeResume;
typedef struct JITLocalValue JITLocalValue;
typedef struct JITProgramUsage JITProgramUsage;

typedef enum {
    JIT_RESUME_LOCAL,
    JIT_RESUME_STACK,
    JIT_RESUME_RESULT,
    JIT_RESUME_CONSTANT,
    JIT_RESUME_OWNER,
    JIT_RESUME_CAPTURED,
    JIT_RESUME_OPERAND
} JITResumeSource;

typedef enum {
    JIT_OWNERSHIP_UNKNOWN,
    JIT_OWNERSHIP_SCALAR,
    JIT_OWNERSHIP_BORROWED_LOCAL,
    /* A database-backed property value without an added reference. */
    JIT_OWNERSHIP_BORROWED_PROPERTY,
    JIT_OWNERSHIP_OWNED,
    /* A property value retained for the native frame. */
    JIT_OWNERSHIP_OWNED_PROPERTY,
    JIT_OWNERSHIP_IMMORTAL
} JITValueOwnership;

typedef enum {
    JIT_ESCAPE_NONE = 0,
    JIT_ESCAPE_RETURN = 1 << 0,
    JIT_ESCAPE_CALL = 1 << 1,
    JIT_ESCAPE_STORE = 1 << 2,
    JIT_ESCAPE_MERGE = 1 << 3,
    JIT_ESCAPE_FRAME = 1 << 4,
    JIT_ESCAPE_MULTIPLE_USES = 1 << 5
} JITValueEscape;

struct JITResumeValue {
    int value;
    JITResumeSource source;
    int index;
    Num literal;
    var_type literal_type;
};

struct JITNativeResume {
    int num_values;
    JITResumeValue *values;
    int valid;
    int rehydratable;
};

struct JITContinuationFrame {
    JITProgram *program;
    struct activation *owner;
    int map_id;
    int num_retained;
    Var *retained_values;
    int retained_capacity;
    Var *spare_retained;
    int spare_retained_capacity;
    void *runtime_storage;
    Num *deopt_values;
    Var *borrowed_locals;
    Var *owned_values;
    unsigned char *home_states;
    size_t runtime_bytes;
    JITNativeFrame *runtime_owner;
    Var result;
    int has_result;
    int dispatched;
    int owns_runtime;
    JITContinuationFrame *previous;
    JITContinuationFrame *next;
};

struct JITLocalValue {
    int slot;
    int value;
};

struct JITDeoptMap {
    ResumeKey resume_key;
    unsigned bytecode_pc;
    unsigned error_pc;
    unsigned source_lineno;
    unsigned stack_depth;
    int ticks_charged;
    int num_locals;
    int num_local_values;
    int local_base;
    JITLocalValue *local_values;
    int num_tagged_values;
    int *tagged_values;
    int *stack_values;
    var_type *stack_types;
    ResumeStackSlot *stack_slots;
    int *local_owner_slots;
    int *stack_owner_slots;
    unsigned char *stack_boundary_ownership;
    JITNativeResume *native_resume;
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

typedef enum {
    JIT_OWNER_ROOT_CONFLICT = -2,
    JIT_OWNER_ROOT_NONE = -1
} JITOwnerRootSpecial;

typedef enum {
    JIT_OWNER_SLOT_NONE = -1
} JITOwnerSlotSpecial;

typedef enum {
    JIT_BOUNDARY_VALUE_RETAINED,
    JIT_BOUNDARY_VALUE_MOVED_RAW,
    JIT_BOUNDARY_VALUE_MOVED_OWNER,
    JIT_BOUNDARY_VALUE_RELEASE_AFTER_RESUME
} JITBoundaryValueOwnership;

typedef enum {
    JIT_LAST_USE_NONE = 0,
    JIT_LAST_USE_SRC1 = 1 << 0,
    JIT_LAST_USE_SRC2 = 1 << 1,
    JIT_LAST_USE_SRC3 = 1 << 2
} JITLastUseOperand;

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
    int src3;
    int local_id;
    unsigned func;
    HIROp op;
    Num literal;
    var_type literal_type;
    int deopt_map;
    JITCopy *copies;
    unsigned char direct_int_list_index_set;
    unsigned char owned_last_use;
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
    uint64_t continuation_captures;
    uint64_t continuation_resumes;
    uint64_t continuation_materializations;
    uint64_t continuation_fast_suspends;
    uint64_t native_chain_calls;
    uint64_t native_chain_returns;
    uint64_t native_chain_promotions;
    uint64_t native_chain_max_depth;
};

struct JITProgram {
    JITState state;
    const char *reason;
    const char *diagnostic;
    int eligible;
    int may_error;
    signed char direct_leaf;
    int num_values;
    int num_vars;
    int num_blocks;
    int num_resume_anchors;
    int num_deopt_maps;
    JITDeoptMap *deopt_maps;
    JITBlock *blocks;
    JITBlock *last_block;
    JITInstruction *retained_constants;
    Program *bytecode_program;
    void *native_function;
    void *machine_code;
    size_t machine_code_len;
    uint64_t pool_generation;
    JITProgram *pool_prev;
    JITProgram *pool_next;
    var_type *value_types;
    unsigned char *value_is_tagged;
    int num_tag_slots;
    int *value_tag_slots;
    unsigned char *value_ownership;
    int *value_owner_root;
    unsigned int *value_use_counts;
    unsigned char *value_escape_flags;
    int num_owned_slots;
    int *value_owned_slots;
    unsigned char *value_is_int_list;
    int num_borrowed_locals;
    int *borrowed_local_slots;
    size_t active_runtime_bytes;
    uint64_t active_native_frames;
    size_t active_native_frame_bytes;
    unsigned protection_generation;
    JITProgramUsage *usage;
    uint32_t compile_attempts;
    uint32_t compile_successes;
    uint32_t compile_failures;
    uint64_t compile_time_us;
    Objid diagnostic_object;
    unsigned diagnostic_verb;
};

extern void jit_analyze_owned_last_uses(JITProgram *);

static inline __attribute__((always_inline)) int
jit_deopt_map_local_value(JITProgram *program, JITDeoptMap *map, int slot)
{
    while (map) {
	int i;

	for (i = 0; i < map->num_local_values; i++)
	    if (map->local_values[i].slot == slot)
		return map->local_values[i].value;
	if (map->local_base <= 0 || map->local_base > program->num_deopt_maps)
	    break;
	map = &program->deopt_maps[map->local_base - 1];
    }
    return 0;
}

static inline __attribute__((always_inline)) var_type
jit_deopt_map_local_type(JITProgram *program, JITDeoptMap *map, int slot)
{
    while (map) {
	int i;

	for (i = 0; i < map->num_local_values; i++)
	    if (map->local_values[i].slot == slot) {
		int value = map->local_values[i].value;

		if (value <= 0)
		    return TYPE_INT;
		return program->value_is_tagged
		    && program->value_is_tagged[value] ? TYPE_ANY
		    : program->value_types ? program->value_types[value] : TYPE_INT;
	    }
	if (map->local_base <= 0 || map->local_base > program->num_deopt_maps)
	    break;
	map = &program->deopt_maps[map->local_base - 1];
    }
    return TYPE_INT;
}

static inline var_type
jit_deopt_map_stack_type(JITProgram *program, JITDeoptMap *map, int slot)
{
    int value;

    if (map->stack_types)
	return map->stack_types[slot];
    if (map->stack_slots && map->stack_slots[slot].kind != RSS_VALUE)
	return map->stack_slots[slot].kind == RSS_CATCH ? TYPE_CATCH
	    : map->stack_slots[slot].kind == RSS_FINALLY ? TYPE_FINALLY : TYPE_INT;
    value = map->stack_values[slot];
    return program->value_is_tagged && program->value_is_tagged[value]
	? TYPE_ANY : program->value_types ? program->value_types[value] : TYPE_INT;
}

extern int jit_rt_is_true(int64_t, int);
extern int jit_rt_equality(int64_t, int, int64_t, int, int);
extern int jit_rt_str_cmp(const char *, const char *, int);
extern const char *jit_rt_str_concat(const char *, const char *, int32_t *);
extern int jit_rt_str_concat_owned(Var *, int, const char *, const char *,
				   int, int64_t *, int32_t *);
extern const char *jit_rt_str_ref(const char *, int64_t, int32_t *);
extern const char *jit_rt_str_range_ref(const char *, int64_t, int64_t, int32_t *);
extern Var *jit_rt_list_range_ref(Var *, int64_t, int64_t, int32_t *);
extern Var *jit_rt_list_concat(Var *, Var *, int32_t *);
extern Var *jit_rt_make_singleton_list(int64_t, int);
extern Var *jit_rt_make_fixed_list_head(int64_t, int, int);
extern Var *jit_rt_list_append(Var *, int64_t, int, int);
extern Var *jit_rt_list_append_owned(Var *, int, Var *, int64_t, int);
extern Var *jit_rt_fixed_list_append_owned(Var *, int, Var *, int, int64_t,
					   int);
extern void jit_rt_owned_replace(Var *, int, int64_t, int);
extern void jit_rt_discard_owned(Var *, int, int64_t, int);
extern Var *jit_rt_list_index_set(Var *, int, Var *, int64_t, int64_t,
				  int, int32_t *);
extern Var *jit_rt_sublist_from(Var *, int64_t);
extern int64_t jit_rt_list_in(int64_t, int, Var *);
extern int jit_rt_get_prop(int64_t, const char *, int64_t, int64_t *, int64_t *, int32_t *);
extern int jit_rt_put_prop(int64_t, const char *, int64_t, int64_t, int, int32_t *);
extern int64_t jit_rt_seconds_left(void);
extern int64_t jit_rt_time(void);
extern int64_t jit_rt_index(const char *, const char *);
extern int64_t jit_rt_rindex(const char *, const char *);
extern int64_t jit_rt_valid(int64_t);
extern int64_t jit_rt_parent(int64_t, int32_t *);
extern int64_t jit_rt_var_raw(const Var *);

#endif /* !JIT_Internal_H */
