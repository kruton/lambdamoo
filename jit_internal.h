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
    unsigned stack_depth;
    int ticks_charged;
    int num_locals;
    int *local_values;
    var_type *local_types;
    int *stack_values;
    var_type *stack_types;
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
};

#endif /* !JIT_Internal_H */
