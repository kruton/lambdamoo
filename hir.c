#include "hir.h"

#include "config.h"
#include "options.h"

#if defined(ENABLE_JIT) && !defined(HIR_TESTING)
#include "jit_internal.h"
#endif

#include "my-stdio.h"

#include "arena.h"
#include "functions.h"
#include "integer_arithmetic.h"
#include "list.h"
#include "opcode.h"
#include "program.h"
#include "storage.h"
#include "utils.h"

#include <stdarg.h>
#include <stddef.h>
#include <string.h>

static int
jit_list_tail_owner_slot(int source_slot, unsigned int source_uses,
			 int next_slot)
{
    return source_slot >= 0 && source_uses == 1 ? source_slot : next_slot;
}

static int
jit_int_list_result(HIROp op, int left_is_int_list, int right_is_int_list,
		    var_type right_type)
{
    if (op == HIR_OP_LIST_ADD_TAIL)
	return left_is_int_list && right_type == TYPE_INT;
    if (op == HIR_OP_LIST_APPEND)
	return left_is_int_list && right_is_int_list;
    return 0;
}

static int
jit_all_copy_sources_are_int_lists(unsigned int sources,
				   unsigned int proven_sources)
{
    return sources > 0 && proven_sources == sources;
}

static int
jit_int_list_has_exclusive_local(unsigned int matching_locals)
{
    return matching_locals == 1;
}

static int
infer_string_add_operand(HIROp op, int other_known, var_type other_type,
			 var_type *inferred_type)
{
    if (op != HIR_OP_ADD || !other_known || other_type != TYPE_STR)
	return 0;

    *inferred_type = TYPE_STR;
    return 1;
}

static int
binary_type_pair_is_valid(HIROp op, var_type left, var_type right)
{
    switch (op) {
    case HIR_OP_ADD:
	return (left == TYPE_INT && right == TYPE_INT)
	    || (left == TYPE_FLOAT && right == TYPE_FLOAT)
	    || (left == TYPE_STR && right == TYPE_STR);
    case HIR_OP_SUB:
    case HIR_OP_MUL:
    case HIR_OP_DIV:
    case HIR_OP_MOD:
	return (left == TYPE_INT && right == TYPE_INT)
	    || (left == TYPE_FLOAT && right == TYPE_FLOAT);
    case HIR_OP_EXP:
	return (left == TYPE_INT && right == TYPE_INT)
	    || (left == TYPE_FLOAT
		&& (right == TYPE_INT || right == TYPE_FLOAT));
    default:
	return 0;
    }
}

static unsigned short
binary_operand_type_mask(HIROp op, int operand, int other_known,
			 var_type other_type)
{
    static const var_type candidates[] = { TYPE_INT, TYPE_FLOAT, TYPE_STR };
    unsigned short mask = 0;
    unsigned i;

    for (i = 0; i < sizeof(candidates) / sizeof(candidates[0]); i++) {
	var_type candidate = candidates[i];

	if (other_known) {
	    var_type left = operand == 0 ? candidate : other_type;
	    var_type right = operand == 0 ? other_type : candidate;

	    if (binary_type_pair_is_valid(op, left, right))
		mask |= (unsigned short) 1U
		    << ((unsigned) candidate & TYPE_DB_MASK);
	} else {
	    unsigned j;

	    for (j = 0; j < sizeof(candidates) / sizeof(candidates[0]); j++) {
		var_type peer = candidates[j];
		var_type left = operand == 0 ? candidate : peer;
		var_type right = operand == 0 ? peer : candidate;

		if (binary_type_pair_is_valid(op, left, right)) {
		    mask |= (unsigned short) 1U
			<< ((unsigned) candidate & TYPE_DB_MASK);
		    break;
		}
	    }
	}
    }
    return mask;
}

#ifdef HIR_TESTING
static int
unary_operand_defaults_to_list(HIROp op)
{
    return op == HIR_OP_CHECK_LIST_FOR_SPLICE;
}
#endif

static int
binary_operands_constrain_each_other(HIROp op)
{
    return op == HIR_OP_LT || op == HIR_OP_LE
	|| op == HIR_OP_GT || op == HIR_OP_GE;
}

static int
infer_min_max_result(HIROp op, var_type left, var_type right,
		     var_type *result)
{
    if ((op != HIR_OP_MIN && op != HIR_OP_MAX) || left != right
	|| (left != TYPE_INT && left != TYPE_FLOAT))
	return 0;

    *result = left;
    return 1;
}

static int
infer_builtin_result_type(const char *name, var_type *result)
{
    if (!strcmp(name, "caller_perms") || !strcmp(name, "toobj")
	|| !strcmp(name, "parent") || !strcmp(name, "owner")
	|| !strcmp(name, "location"))
	*result = TYPE_OBJ;
    else if (!strcmp(name, "tostr") || !strcmp(name, "toliteral"))
	*result = TYPE_STR;
    else if (!strcmp(name, "tonum") || !strcmp(name, "toint"))
	*result = TYPE_INT;
    else if (!strcmp(name, "tofloat"))
	*result = TYPE_FLOAT;
#ifdef WAIF_CORE
    else if (!strcmp(name, "new_waif"))
	*result = TYPE_WAIF;
#endif
    else
	return 0;
    return 1;
}

static void
initialize_inferred_value_types(var_type *types, unsigned char *known,
				unsigned char *tagged, int count)
{
    int i;

    for (i = 0; i < count; i++)
	types[i] = TYPE_ANY;
    memset(known, 0, count > 0 ? count : 1);
    memset(tagged, 0, count > 0 ? count : 1);
}

static void
tag_unknown_inferred_value_types(var_type *types, unsigned char *known,
				  unsigned char *tagged, int count)
{
    int i;

    for (i = 1; i < count; i++)
	if (!known[i]) {
	    types[i] = TYPE_ANY;
	    tagged[i] = 1;
	}
}

static int
is_uninitialized_entry_load(HIRTacKind kind, unsigned bytecode_pc,
			    int local_id, int first_user_local)
{
    return kind == HIR_TAC_LOAD_LOCAL && bytecode_pc == NO_BYTECODE_PC
	&& local_id >= first_user_local;
}

static int
builtin_entry_type(HIRTacKind kind, unsigned bytecode_pc, int local_id,
		   int first_user_local, var_type *type)
{
    if (kind != HIR_TAC_LOAD_LOCAL || bytecode_pc != NO_BYTECODE_PC
	|| local_id < 0 || local_id >= first_user_local)
	return 0;

    switch (local_id) {
    case SLOT_NUM:
    case SLOT_OBJ:
    case SLOT_STR:
    case SLOT_LIST:
    case SLOT_ERR:
    case SLOT_INT:
    case SLOT_FLOAT:
	*type = TYPE_INT;
	return 1;
    case SLOT_PLAYER:
    case SLOT_DOBJ:
    case SLOT_IOBJ:
	*type = TYPE_OBJ;
	return 1;
    case SLOT_VERB:
    case SLOT_ARGSTR:
    case SLOT_DOBJSTR:
    case SLOT_PREPSTR:
    case SLOT_IOBJSTR:
	*type = TYPE_STR;
	return 1;
    case SLOT_ARGS:
	*type = TYPE_LIST;
	return 1;
    default:
	return 0;
    }
}

#ifdef HIR_TESTING
static int
is_string_builtin_length_anchor(Bytecodes *bc, unsigned pc, unsigned func,
				HIROp op)
{
    const char *func_name = name_func_by_num(func);

    return op == HIR_OP_LENGTH && pc != NO_BYTECODE_PC && pc + 1 < bc->size
	&& bc->vector[pc] == OP_BI_FUNC_CALL && bc->vector[pc + 1] == func
	&& func_name && !strcmp(func_name, "length");
}
#endif

typedef struct HIRExpr HIRExpr;
typedef struct HIRStmt HIRStmt;
typedef struct HIRArg HIRArg;
typedef struct HIRCondArm HIRCondArm;
typedef struct HIRExceptArm HIRExceptArm;
typedef struct HIRTacInstr HIRTacInstr;
typedef struct HIRBasicBlock HIRBasicBlock;
typedef struct HIRDominatorTree HIRDominatorTree;
typedef struct HIRSSAInstr HIRSSAInstr;
typedef struct HIRSSABlock HIRSSABlock;
typedef struct HIRPhiArg HIRPhiArg;
typedef struct HIRParallelCopy HIRParallelCopy;
typedef struct HIRSSADestructionMove HIRSSADestructionMove;

typedef enum {
    HIR_VALUE_BOTTOM,
    HIR_VALUE_FACT_UNKNOWN,
    HIR_VALUE_FACT_INT,
    HIR_VALUE_FACT_CONSTANT,
    HIR_VALUE_FACT_ERROR
} HIRValueFactKind;

typedef struct {
    HIRValueFactKind kind;
    Num constant;
    enum error error;
} HIRValueFact;

struct HIRArg {
    enum Arg_Kind kind;
    HIRExpr *expr;
    unsigned bytecode_pc;
    HIRArg *next;
};

typedef struct HIRScatter HIRScatter;

struct HIRScatter {
    enum Scatter_Kind kind;
    int local_id;
    HIRExpr *expr;
    HIRScatter *next;
};

struct HIRExpr {
    HIRExprKind kind;
    HIRTypeTag type;
    unsigned source_lineno;
    unsigned bytecode_pc;
    union {
	Var literal;
	int local_id;
	struct {
	    HIROp op;
	    HIRExpr *expr;
	} unary;
	struct {
	    HIROp op;
	    HIRExpr *lhs;
	    HIRExpr *rhs;
	} binary;
	struct {
	    int local_id;
	    HIRExpr *rhs;
	} local_store;
	struct {
	    HIRExpr *condition;
	    HIRExpr *consequent;
	    HIRExpr *alternate;
	} cond;
	struct {
	    ResumeKey resume_key;
	    unsigned func;
	    HIRArg *args;
	} call;
	struct {
	    ResumeKey resume_key;
	    HIRExpr *obj;
	    HIRExpr *verb;
	    HIRArg *args;
	} verb_call;
	struct {
	    HIRExpr *lhs;
	    HIRExpr *rhs;
	} pair;
	struct {
	    HIRExpr *base;
	    HIRExpr *from;
	    HIRExpr *to;
	} range;
	struct {
	    HIRArg *items;
	} list;
	struct {
	    HIRScatter *items;
	    HIRExpr *rhs;
	} scatter;
	struct {
	    HIRExpr *obj;
	    HIRExpr *prop;
	    HIRExpr *rhs;
	} prop_store;
	struct {
	    HIRExpr *base;
	    HIRExpr *index;
	    HIRExpr *rhs;
	} index_store;
	struct {
	    HIRExpr *base;
	    HIRExpr *from;
	    HIRExpr *to;
	    HIRExpr *rhs;
	} range_store;
	struct {
	    HIRExpr *body;
	    HIRArg *codes;
	    HIRExpr *handler;
	    unsigned handler_pc;
	} catch_expr;
	struct {
	    enum Expr_Kind expr_kind;
	} unsupported;
    } u;
};

struct HIRCondArm {
    HIRExpr *condition;
    HIRStmt *body;
    unsigned bytecode_pc;
    HIRCondArm *next;
};

struct HIRExceptArm {
    int local_id;
    HIRArg *codes;
    HIRStmt *body;
    int label;
    unsigned source_lineno;
    unsigned handler_pc;
    HIRExceptArm *next;
};

struct HIRStmt {
    HIRStmtKind kind;
    unsigned source_lineno;
    unsigned bytecode_pc;
    HIRStmt *next;
    union {
	HIRStmt *sequence;
	HIRExpr *expr;
	struct {
	    HIRCondArm *arms;
	    HIRStmt *otherwise;
	} if_stmt;
	struct {
	    int local_id;
	    HIRExpr *iterable;
	    HIRStmt *body;
	} for_list;
	struct {
	    int local_id;
	    HIRExpr *from;
	    HIRExpr *to;
	    HIRStmt *body;
	} for_range;
	struct {
	    int loop_id;
	    HIRExpr *condition;
	    HIRStmt *body;
	} loop;
	struct {
	    int local_id;
	    HIRExpr *time;
	    HIRStmt *body;
	} fork;
	struct {
	    HIRStmt *body;
	    HIRExceptArm *excepts;
	} try_except;
	struct {
	    HIRStmt *body;
	    HIRStmt *handler;
	    unsigned handler_pc;
	} try_finally;
	int exit_id;
	enum Stmt_Kind stmt_kind;
    } u;
};

struct HIRProgram {
    HIRStmt *root;
};

struct HIRTacInstr {
    HIRTacKind kind;
    unsigned source_lineno;
    unsigned bytecode_pc;
    int error_label;
    int dst;
    int src1;
    int src2;
    int src3;
    int label;
    int local_id;
    HIROp op;
    Var literal;
    unsigned func;
    ResumeKey resume_key;
    int num_stack_values;
    int *stack_values;
    ResumeStackSlot *stack_slots;
    HIRTacInstr *next;
};

struct HIRTacProgram {
    HIRTacInstr *first;
    HIRTacInstr *last;
};

struct HIRBasicBlock {
    int id;
    HIRTacInstr *first;
    HIRTacInstr *last;
    HIRBasicBlock *next;
    HIRBasicBlock *successors[2];
    int num_successors;
    int predecessor_count;
    unsigned first_lineno;
    unsigned last_lineno;
    int contains_unsupported;
};

struct HIRCFG {
    HIRBasicBlock *entry;
    HIRBasicBlock *blocks;
    HIRBasicBlock *last_block;
    int num_blocks;
    int num_edges;
};

struct HIRBlockList {
    HIRBasicBlock *block;
    HIRBlockList *next;
};

struct HIRDominatorTree {
    HIRBasicBlock **block_by_id;
    HIRBasicBlock **idom;
    HIRBasicBlock **rpo;
    int *rpo_index;
    HIRBlockList **df;
    int max_block_id;
    int num_reachable;
};

struct HIRPhiArg {
    int block_id;
    int value;
    HIRPhiArg *next;
};

struct HIRParallelCopy {
    int dst;
    int src;
    HIRParallelCopy *next;
};

struct HIRSSADestructionMove {
    int pred_block_id;
    int target_block_id;
    int dst;
    int src;
    unsigned source_lineno;
    HIRSSADestructionMove *next;
};

struct HIRSSAInstr {
    HIRTacKind kind;
    unsigned source_lineno;
    unsigned bytecode_pc;
    int error_label;
    int value;
    int src1;
    int src2;
    int src3;
    int label;
    int local_id;
    HIROp op;
    Var literal;
    unsigned func;
    ResumeKey resume_key;
    int num_stack_values;
    int *stack_values;
    ResumeStackSlot *stack_slots;
    int num_local_values;
    int *local_values;
    HIRPhiArg *phi_args;
    HIRParallelCopy *copies;
    HIRSSAInstr *next;
};

struct HIRSSABlock {
    int id;
    unsigned first_lineno;
    unsigned last_lineno;
    HIRSSAInstr *first;
    HIRSSAInstr *last;
    HIRSSABlock *next;
};

struct HIRSSAProgram {
    HIRForm form;
    HIRCFG *cfg;
    HIRSSABlock *blocks;
    HIRSSABlock *last_block;
    int num_blocks;
    int num_instructions;
    int num_values;
};

struct HIRValueAnalysis {
    HIRValueFact *facts;
    int num_facts;
};

typedef struct HIRLoopContext HIRLoopContext;
typedef struct HIRFinallyContext HIRFinallyContext;

struct HIRFinallyContext {
    HIRStmt *handler;
    int base_depth;
    HIRFinallyContext *parent;
};

struct HIRLoopContext {
    int loop_id;
    int cont_label;
    int done_label;
    int saved_depth;
    HIRFinallyContext *finally_context;
    HIRLoopContext *parent;
};

struct HIRContext {
    Arena *arena;
    Names *var_names;
    int error_count;
    const char *error_msg;
    int next_temp;
    int next_label;
    int next_local;
    int first_user_local;
    unsigned current_code_unit;
    int lower_stack_depth;
    int lower_stack_capacity;
    int *lower_stack;
    ResumeStackSlot *lower_stack_slots;
    HIRLoopContext *current_loop;
    HIRFinallyContext *current_finally;
    int current_error_label;
    int current_length_base;
};

static void *hir_alloc(HIRContext *, size_t);
static HIRExpr *lift_expr(HIRContext *, Expr *);
static HIRStmt *lift_stmt_list(HIRContext *, Stmt *);
static int lower_expr(HIRContext *, HIRTacProgram *, HIRExpr *);
static void lower_stmt_list(HIRContext *, HIRTacProgram *, HIRStmt *);
static void record_unsupported(HIRContext *, const char *);
static void record_unsupported_fmt(HIRContext *, const char *, ...);
static void *
hir_calloc(HIRContext *ctx, size_t count, size_t size)
{
    void *ptr = hir_alloc(ctx, count * size);
    memset(ptr, 0, count * size);
    return ptr;
}

static int tac_is_terminator(HIRTacInstr *);

HIRContext *
hir_context_new(Names *var_names)
{
    HIRContext *ctx = mymalloc(sizeof(HIRContext), M_CODE_GEN);

    ctx->arena = arena_create(65536, M_CODE_GEN);
    ctx->var_names = var_names;
    ctx->error_count = 0;
    ctx->error_msg = 0;
    ctx->next_temp = 1;
    ctx->next_label = 1;
    ctx->next_local = var_names ? (int) var_names->size : 0;
    ctx->first_user_local = ctx->next_local;
    ctx->current_code_unit = 0;
    ctx->lower_stack_depth = 0;
    ctx->lower_stack_capacity = 0;
    ctx->lower_stack = 0;
    ctx->lower_stack_slots = 0;
    ctx->current_loop = 0;
    ctx->current_finally = 0;
    ctx->current_error_label = 0;
    ctx->current_length_base = 0;

    return ctx;
}

void
hir_context_set_first_user_local(HIRContext *ctx, int first_user_local)
{
    if (!ctx)
	return;
    if (first_user_local < 0)
	first_user_local = 0;
    if (first_user_local > ctx->next_local)
	first_user_local = ctx->next_local;
    ctx->first_user_local = first_user_local;
}

void
hir_context_free(HIRContext *ctx)
{
    if (!ctx)
	return;

    if (ctx->arena)
	arena_destroy(ctx->arena);

    myfree(ctx, M_CODE_GEN);
}

int
hir_context_error_count(HIRContext *ctx)
{
    return ctx ? ctx->error_count : 0;
}

const char *
hir_context_error_message(HIRContext *ctx)
{
    return ctx ? ctx->error_msg : 0;
}

HIRProgram *
hir_lift_ast(HIRContext *ctx, Stmt *ast)
{
    HIRProgram *program = hir_alloc(ctx, sizeof(HIRProgram));

    program->root = lift_stmt_list(ctx, ast);
    return program;
}

HIRTacProgram *
hir_lower_to_tac(HIRContext *ctx, HIRProgram *program)
{
    HIRTacProgram *tac = hir_alloc(ctx, sizeof(HIRTacProgram));

    tac->first = tac->last = 0;
    if (program)
	lower_stmt_list(ctx, tac, program->root);
    return tac;
}

static void
verify_local(HIRContext *ctx, int local_id)
{
    if (local_id < 0 || local_id >= ctx->next_local)
	record_unsupported_fmt(ctx, "tac: invalid local id %d", local_id);
}

static void
verify_temp_use(HIRContext *ctx, int temp, unsigned char *defined,
		int max_temp)
{
    if (temp <= 0 || temp > max_temp || !defined[temp])
	record_unsupported_fmt(ctx, "tac: temp %d used before definition", temp);
}

static int
unary_op_has_operand(HIROp op)
{
    return op != HIR_OP_TICKS_LEFT && op != HIR_OP_SECONDS_LEFT
	&& op != HIR_OP_TIME;
}

static void
verify_temp_def(HIRContext *ctx, int temp, unsigned char *defined,
		int max_temp)
{
    if (temp <= 0 || temp > max_temp) {
	record_unsupported_fmt(ctx, "tac: invalid temp definition %d", temp);
	return;
    }

    if (defined[temp])
	record_unsupported_fmt(ctx, "tac: duplicate temp definition %d", temp);
    defined[temp] = 1;
}

static void
verify_label_def(HIRContext *ctx, int label, unsigned char *defined,
		 int max_label)
{
    if (label <= 0 || label > max_label) {
	record_unsupported_fmt(ctx, "tac: invalid label definition %d", label);
	return;
    }

    if (defined[label])
	record_unsupported_fmt(ctx, "tac: duplicate label definition %d", label);
    defined[label] = 1;
}

static void
verify_label_use(HIRContext *ctx, int label, unsigned char *referenced,
		 int max_label)
{
    if (label <= 0 || label > max_label) {
	record_unsupported_fmt(ctx, "tac: invalid label reference %d", label);
	return;
    }

    referenced[label] = 1;
}

int
hir_verify_tac(HIRContext *ctx, HIRTacProgram *program)
{
    HIRTacInstr *instr;
    unsigned char *defined_temps;
    unsigned char *defined_labels;
    unsigned char *referenced_labels;
    int max_temp;
    int max_label;
    int errors_before;
    int i;

    if (!ctx || !program)
	return 0;

    errors_before = ctx->error_count;
    max_temp = ctx->next_temp - 1;
    max_label = ctx->next_label - 1;

    defined_temps = hir_alloc(ctx, (size_t) max_temp + 1);
    defined_labels = hir_alloc(ctx, (size_t) max_label + 1);
    referenced_labels = hir_alloc(ctx, (size_t) max_label + 1);

    for (i = 0; i <= max_temp; i++)
	defined_temps[i] = 0;
    for (i = 0; i <= max_label; i++) {
	defined_labels[i] = 0;
	referenced_labels[i] = 0;
    }

    for (instr = program->first; instr; instr = instr->next) {
	switch (instr->kind) {
	case HIR_TAC_TICK:
	case HIR_TAC_DEOPT:
	    break;
	case HIR_TAC_CONST:
	case HIR_TAC_LOAD_ERROR:
	case HIR_TAC_LOAD_LOCAL:
	    if (instr->kind == HIR_TAC_LOAD_LOCAL)
		verify_local(ctx, instr->local_id);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_STORE_LOCAL:
	    verify_local(ctx, instr->local_id);
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    break;
	case HIR_TAC_UNARY:
	    if (unary_op_has_operand(instr->op))
		verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_BINARY:
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_use(ctx, instr->src2, defined_temps, max_temp);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_CALL:
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_PUT_PROP:
	case HIR_TAC_CALL_VERB:
	case HIR_TAC_RANGE_REF:
	case HIR_TAC_RANGE_SET:
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_use(ctx, instr->src2, defined_temps, max_temp);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_INDEX_SET:
	    verify_local(ctx, instr->local_id);
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_use(ctx, instr->src2, defined_temps, max_temp);
	    verify_temp_use(ctx, instr->src3, defined_temps, max_temp);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_LABEL:
	    verify_label_def(ctx, instr->label, defined_labels, max_label);
	    break;
	case HIR_TAC_JUMP:
	    verify_label_use(ctx, instr->label, referenced_labels, max_label);
	    break;
	case HIR_TAC_BRANCH_FALSE:
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_label_use(ctx, instr->label, referenced_labels, max_label);
	    break;
	case HIR_TAC_RETURN:
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    break;
	case HIR_TAC_RETURN0:
	    break;
	case HIR_TAC_UNSUPPORTED:
	    record_unsupported(ctx, "tac: unsupported instruction");
	    if (instr->dst > 0)
		verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_PHI:
	    record_unsupported(ctx, "tac: phi node in TAC");
	    break;
	case HIR_TAC_PARALLEL_COPY:
	    record_unsupported(ctx, "tac: parallel copy in TAC");
	    break;
	}
    }

    for (i = 1; i <= max_label; i++) {
	if (referenced_labels[i] && !defined_labels[i])
	    record_unsupported_fmt(ctx, "tac: label %d referenced but not defined", i);
    }

    return ctx->error_count == errors_before;
}

static int
tac_can_raise_natively(HIRTacInstr *instr)
{
    return instr && (instr->kind == HIR_TAC_UNARY
		     || instr->kind == HIR_TAC_BINARY
		     || instr->kind == HIR_TAC_PUT_PROP
		     || instr->kind == HIR_TAC_RANGE_REF
		     || instr->kind == HIR_TAC_RANGE_SET);
}

static int
tac_is_terminator(HIRTacInstr *instr)
{
    return instr
	&& (instr->kind == HIR_TAC_JUMP
	    || instr->kind == HIR_TAC_BRANCH_FALSE
	    || instr->kind == HIR_TAC_RETURN
	    || instr->kind == HIR_TAC_RETURN0
	    || (instr->error_label > 0 && tac_can_raise_natively(instr)));
}

static HIRBasicBlock *
new_block(HIRContext *ctx, int id, HIRTacInstr *first)
{
    HIRBasicBlock *block = hir_alloc(ctx, sizeof(HIRBasicBlock));

    block->id = id;
    block->first = first;
    block->last = 0;
    block->next = 0;
    block->successors[0] = 0;
    block->successors[1] = 0;
    block->num_successors = 0;
    block->predecessor_count = 0;
    block->first_lineno = first ? first->source_lineno : 0;
    block->last_lineno = block->first_lineno;
    block->contains_unsupported = 0;

    return block;
}

static void
append_block(HIRCFG *cfg, HIRBasicBlock *block)
{
    if (cfg->last_block)
	cfg->last_block->next = block;
    else
	cfg->blocks = block;
    cfg->last_block = block;
    if (!cfg->entry)
	cfg->entry = block;
    cfg->num_blocks++;
}

static void
add_edge(HIRCFG *cfg, HIRBasicBlock *from, HIRBasicBlock *to)
{
    int i;

    if (!from || !to)
	return;

    for (i = 0; i < from->num_successors; i++) {
	if (from->successors[i] == to)
	    return;
    }

    if (from->num_successors >= 2)
	return;

    from->successors[from->num_successors++] = to;
    to->predecessor_count++;
    cfg->num_edges++;
}

static void
finish_block(HIRBasicBlock *block, HIRTacInstr **instrs, int first_index,
	     int last_index)
{
    int i;

    block->last = instrs[last_index];
    for (i = first_index; i <= last_index; i++) {
	if (instrs[i]->kind == HIR_TAC_UNSUPPORTED)
	    block->contains_unsupported = 1;
	if (instrs[i]->source_lineno != 0) {
	    if (block->first_lineno == 0
		|| instrs[i]->source_lineno < block->first_lineno)
		block->first_lineno = instrs[i]->source_lineno;
	    if (instrs[i]->source_lineno > block->last_lineno)
		block->last_lineno = instrs[i]->source_lineno;
	}
    }
}

static HIRBasicBlock *
block_for_label(HIRContext *ctx, HIRBasicBlock **label_blocks, int max_label,
		int label)
{
    if (label <= 0 || label > max_label || !label_blocks[label]) {
	record_unsupported(ctx, "cfg: edge target label has no block");
	return 0;
    }

    return label_blocks[label];
}

static int
max_cfg_block_id(HIRCFG *cfg)
{
    HIRBasicBlock *block;
    int max = 0;

    if (!cfg)
	return 0;

    for (block = cfg->blocks; block; block = block->next) {
	if (block->id > max)
	    max = block->id;
    }

    return max;
}

static void
mark_reachable_cfg_blocks(HIRCFG *cfg, unsigned char *reachable)
{
    int changed = 1;

    if (cfg->entry)
	reachable[cfg->entry->id] = 1;
    while (changed) {
	HIRBasicBlock *block;

	changed = 0;
	for (block = cfg->blocks; block; block = block->next) {
	    int i;

	    if (!reachable[block->id])
		continue;
	    for (i = 0; i < block->num_successors; i++) {
		int successor = block->successors[i]->id;

		if (!reachable[successor]) {
		    reachable[successor] = 1;
		    changed = 1;
		}
	    }
	}
    }
}

static void
prune_cfg_blocks(HIRCFG *cfg, unsigned char *reachable)
{
    HIRBasicBlock *block = cfg->blocks;
    HIRBasicBlock *previous = 0;

    cfg->num_blocks = 0;
    cfg->num_edges = 0;
    cfg->last_block = 0;
    while (block) {
	HIRBasicBlock *next = block->next;

	if (reachable[block->id]) {
	    int source;
	    int target = 0;

	    for (source = 0; source < block->num_successors; source++)
		if (reachable[block->successors[source]->id])
		    block->successors[target++] = block->successors[source];
	    block->num_successors = target;
	    block->predecessor_count = 0;
	    if (previous)
		previous->next = block;
	    else
		cfg->blocks = block;
	    previous = block;
	    cfg->last_block = block;
	    cfg->num_blocks++;
	}
	block = next;
    }
    if (previous)
	previous->next = 0;
    else
	cfg->blocks = 0;

    for (block = cfg->blocks; block; block = block->next) {
	int i;

	for (i = 0; i < block->num_successors; i++) {
	    block->successors[i]->predecessor_count++;
	    cfg->num_edges++;
	}
    }
}

HIRCFG *
hir_build_cfg(HIRContext *ctx, HIRTacProgram *program)
{
    HIRCFG *cfg;
    HIRTacInstr *instr;
    HIRTacInstr **instrs;
    unsigned char *leaders;
    HIRBasicBlock **label_blocks;
    HIRBasicBlock *block;
    int count = 0;
    int max_label = 0;
    int i;
    int block_id = 0;

    if (!ctx || !program)
	return 0;

    cfg = hir_alloc(ctx, sizeof(HIRCFG));
    cfg->entry = 0;
    cfg->blocks = 0;
    cfg->last_block = 0;
    cfg->num_blocks = 0;
    cfg->num_edges = 0;

    for (instr = program->first; instr; instr = instr->next) {
	count++;
	if (instr->label > max_label)
	    max_label = instr->label;
    }

    if (count == 0)
	return cfg;

    instrs = hir_alloc(ctx, sizeof(HIRTacInstr *) * ((size_t) count + 2));
    leaders = hir_alloc(ctx, (size_t) count + 2);
    label_blocks = hir_alloc(ctx, sizeof(HIRBasicBlock *) * ((size_t) max_label + 1));

    for (i = 0; i <= count + 1; i++) {
	leaders[i] = 0;
    }
    for (i = 0; i <= max_label; i++)
	label_blocks[i] = 0;

    i = 1;
    for (instr = program->first; instr; instr = instr->next)
	instrs[i++] = instr;

    leaders[1] = 1;
    leaders[count + 1] = 1;
    for (i = 1; i <= count; i++) {
	if (instrs[i]->kind == HIR_TAC_LABEL)
	    leaders[i] = 1;
	if (tac_is_terminator(instrs[i]) && i < count)
	    leaders[i + 1] = 1;
    }

    i = 1;
    while (i <= count) {
	int first_index = i;
	int last_index;

	block = new_block(ctx, ++block_id, instrs[first_index]);
	append_block(cfg, block);
	last_index = first_index;
	while (last_index < count && !leaders[last_index + 1])
	    last_index++;
	finish_block(block, instrs, first_index, last_index);

	if (block->first->kind == HIR_TAC_LABEL
	    && block->first->label > 0
	    && block->first->label <= max_label)
	    label_blocks[block->first->label] = block;

	i = last_index + 1;
    }

    for (block = cfg->blocks; block; block = block->next) {
	HIRTacInstr *last = block->last;

	switch (last->kind) {
	case HIR_TAC_JUMP:
	    add_edge(cfg, block,
		     block_for_label(ctx, label_blocks, max_label, last->label));
	    break;
	case HIR_TAC_BRANCH_FALSE:
	    add_edge(cfg, block,
		     block_for_label(ctx, label_blocks, max_label, last->label));
	    add_edge(cfg, block, block->next);
	    break;
	case HIR_TAC_RETURN:
	case HIR_TAC_RETURN0:
	    break;
	default:
	    if (last->error_label > 0 && tac_can_raise_natively(last))
		add_edge(cfg, block, block_for_label(ctx, label_blocks,
						       max_label, last->error_label));
	    add_edge(cfg, block, block->next);
	    break;
	}
    }

    if (cfg->entry) {
	unsigned char *reachable = hir_calloc(ctx, (size_t) max_cfg_block_id(cfg) + 1, sizeof(unsigned char));
	mark_reachable_cfg_blocks(cfg, reachable);
	prune_cfg_blocks(cfg, reachable);
    }

    return cfg;
}

static int
cfg_contains_block_ptr(HIRCFG *cfg, HIRBasicBlock *target)
{
    HIRBasicBlock *block;

    if (!cfg || !target)
	return 0;

    for (block = cfg->blocks; block; block = block->next) {
	if (block == target)
	    return 1;
    }

    return 0;
}

static int
cfg_actual_predecessor_count(HIRCFG *cfg, HIRBasicBlock *target)
{
    HIRBasicBlock *block;
    int count = 0;

    if (!cfg || !target)
	return 0;

    for (block = cfg->blocks; block; block = block->next) {
	int i;

	for (i = 0; i < block->num_successors; i++) {
	    if (block->successors[i] == target)
		count++;
	}
    }

    return count;
}

static int
cfg_expected_successors(HIRTacInstr *last)
{
    if (!last)
	return -1;

    switch (last->kind) {
    case HIR_TAC_JUMP:
	return 1;
    case HIR_TAC_BRANCH_FALSE:
	return 2;
    case HIR_TAC_RETURN:
    case HIR_TAC_RETURN0:
	return 0;
    default:
	return last->error_label > 0 && tac_can_raise_natively(last) ? 2 : -1;
    }
}

static int max_cfg_block_id(HIRCFG *);

static int
cfg_edge_is_critical(HIRBasicBlock *from, HIRBasicBlock *to)
{
    return from && to && from->num_successors > 1 && to->predecessor_count > 1;
}

static int
cfg_critical_edge_count(HIRCFG *cfg)
{
    HIRBasicBlock *block;
    int count = 0;

    if (!cfg)
	return 0;

    for (block = cfg->blocks; block; block = block->next) {
	int i;

	for (i = 0; i < block->num_successors; i++) {
	    if (cfg_edge_is_critical(block, block->successors[i]))
		count++;
	}
    }

    return count;
}

static HIRTacInstr *
new_cfg_split_jump(HIRContext *ctx, HIRBasicBlock *from, HIRBasicBlock *to)
{
    HIRTacInstr *jump = hir_alloc(ctx, sizeof(HIRTacInstr));

    memset(jump, 0, sizeof(HIRTacInstr));
    jump->kind = HIR_TAC_JUMP;
    jump->source_lineno = from && from->last ? from->last->source_lineno : 0;
    jump->bytecode_pc = NO_BYTECODE_PC;
    if (jump->source_lineno == 0 && to)
	jump->source_lineno = to->first_lineno;
    jump->label = to && to->first && to->first->kind == HIR_TAC_LABEL
	? to->first->label : 0;
    jump->local_id = -1;
    jump->op = HIR_OP_ADD;
    jump->literal.type = TYPE_NONE;

    return jump;
}

int
hir_split_critical_edges(HIRContext *ctx, HIRCFG *cfg)
{
    HIRBasicBlock *block;
    HIRBasicBlock *original_last;
    int next_id;
    int split_count = 0;

    if (!ctx || !cfg)
	return 0;

    original_last = cfg->last_block;
    next_id = max_cfg_block_id(cfg) + 1;

    for (block = cfg->blocks; block; block = block->next) {
	int i;

	for (i = 0; i < block->num_successors; i++) {
	    HIRBasicBlock *succ = block->successors[i];
	    HIRTacInstr *jump;
	    HIRBasicBlock *split;

	    if (!cfg_edge_is_critical(block, succ))
		continue;

	    jump = new_cfg_split_jump(ctx, block, succ);
	    split = new_block(ctx, next_id++, jump);
	    split->last = jump;
	    append_block(cfg, split);

	    block->successors[i] = split;
	    split->predecessor_count = 1;
	    split->successors[0] = succ;
	    split->num_successors = 1;
	    cfg->num_edges++;
	    split_count++;

	    if (original_last == block)
		original_last = split;
	}

	if (block == original_last)
	    break;
    }

    return split_count;
}

int
hir_verify_cfg(HIRContext *ctx, HIRCFG *cfg)
{
    HIRBasicBlock *block;
    int errors_before;
    int block_count = 0;

    if (!ctx || !cfg)
	return 0;

    errors_before = ctx->error_count;

    if (cfg->num_blocks == 0)
	return 1;

    if (!cfg->entry || cfg->entry != cfg->blocks)
	record_unsupported(ctx, "cfg: invalid entry block");

    for (block = cfg->blocks; block; block = block->next) {
	HIRBasicBlock *other;
	int expected_successors;
	int i;

	block_count++;
	if (block->id <= 0)
	    record_unsupported_fmt(ctx, "cfg: block has invalid id %d", block->id);
	for (other = cfg->blocks; other && other != block; other = other->next) {
	    if (other->id == block->id)
		record_unsupported_fmt(ctx, "cfg: duplicate block id %d", block->id);
	}

	if (!block->first || !block->last)
	    record_unsupported_fmt(ctx, "cfg: block %d has missing TAC bounds", block->id);

	if (block->num_successors < 0 || block->num_successors > 2)
	    record_unsupported_fmt(ctx, "cfg: block %d has invalid successor count %d", block->id, block->num_successors);

	for (i = 0; i < block->num_successors; i++) {
	    if (!block->successors[i])
		record_unsupported_fmt(ctx, "cfg: block %d has missing successor", block->id);
	    else if (!cfg_contains_block_ptr(cfg, block->successors[i]))
		record_unsupported_fmt(ctx, "cfg: block %d successor is not in block list", block->id);
	}

	expected_successors = cfg_expected_successors(block->last);
	if (expected_successors >= 0
	    && block->num_successors != expected_successors)
	    record_unsupported_fmt(ctx, "cfg: block %d has invalid terminator successors", block->id);

	if (block->predecessor_count
	    != cfg_actual_predecessor_count(cfg, block))
	    record_unsupported_fmt(ctx, "cfg: block %d predecessor count mismatch", block->id);

    }

    if (block_count != cfg->num_blocks)
	record_unsupported(ctx, "cfg: block count mismatch");
    if (cfg->last_block && cfg->last_block->next)
	record_unsupported(ctx, "cfg: last block is not terminal");

    return ctx->error_count == errors_before;
}

static void
index_cfg_blocks(HIRDominatorTree *dom, HIRCFG *cfg)
{
    HIRBasicBlock *block;
    int i;

    for (i = 0; i <= dom->max_block_id; i++)
	dom->block_by_id[i] = 0;

    for (block = cfg->blocks; block; block = block->next) {
	if (block->id > 0 && block->id <= dom->max_block_id)
	    dom->block_by_id[block->id] = block;
    }
}

static int
dom_contains_block(HIRDominatorTree *dom, HIRBasicBlock *block)
{
    return block && block->id > 0 && block->id <= dom->max_block_id
	&& dom->block_by_id[block->id] == block;
}

static void
postorder_cfg(HIRDominatorTree *dom, HIRBasicBlock *block,
	      unsigned char *visited, HIRBasicBlock **postorder, int *count)
{
    int i;

    if (!dom_contains_block(dom, block) || visited[block->id])
	return;

    visited[block->id] = 1;
    for (i = 0; i < block->num_successors; i++)
	postorder_cfg(dom, block->successors[i], visited, postorder, count);
    postorder[(*count)++] = block;
}

static HIRBasicBlock *
intersect_idom(HIRDominatorTree *dom, HIRBasicBlock *left,
	       HIRBasicBlock *right)
{
    while (left != right) {
	while (dom->rpo_index[left->id] > dom->rpo_index[right->id])
	    left = dom->idom[left->id];
	while (dom->rpo_index[right->id] > dom->rpo_index[left->id])
	    right = dom->idom[right->id];
    }

    return left;
}

static int
block_has_reachable_idom(HIRDominatorTree *dom, HIRBasicBlock *block)
{
    return block && block->id > 0 && block->id <= dom->max_block_id
	&& dom->rpo_index[block->id] >= 0 && dom->idom[block->id] != 0;
}

static HIRBasicBlock *
compute_block_idom(HIRCFG *cfg, HIRDominatorTree *dom, HIRBasicBlock *block)
{
    HIRBasicBlock *candidate = 0;
    HIRBasicBlock *pred;

    for (pred = cfg->blocks; pred; pred = pred->next) {
	int i;

	for (i = 0; i < pred->num_successors; i++) {
	    if (pred->successors[i] != block)
		continue;
	    if (!block_has_reachable_idom(dom, pred))
		continue;
	    if (!candidate)
		candidate = pred;
	    else
		candidate = intersect_idom(dom, pred, candidate);
	}
    }

    return candidate;
}

HIRDominatorTree *
hir_build_dominator_tree(HIRContext *ctx, HIRCFG *cfg)
{
    HIRDominatorTree *dom;
    HIRBasicBlock **postorder;
    unsigned char *visited;
    int postorder_count = 0;
    int changed = 1;
    int i;

    if (!ctx || !cfg)
	return 0;

    dom = hir_alloc(ctx, sizeof(HIRDominatorTree));
    dom->max_block_id = max_cfg_block_id(cfg);
    dom->num_reachable = 0;
    dom->block_by_id = hir_alloc(ctx, sizeof(HIRBasicBlock *)
				 * ((size_t) dom->max_block_id + 1));
    dom->idom = hir_alloc(ctx, sizeof(HIRBasicBlock *)
			  * ((size_t) dom->max_block_id + 1));
    dom->rpo = hir_alloc(ctx, sizeof(HIRBasicBlock *)
			 * ((size_t) cfg->num_blocks + 1));
    dom->df = hir_alloc(ctx, sizeof(HIRBlockList *)
			 * ((size_t) dom->max_block_id + 1));
    dom->rpo_index = hir_alloc(ctx, sizeof(int)
			       * ((size_t) dom->max_block_id + 1));
    postorder = hir_alloc(ctx, sizeof(HIRBasicBlock *)
			  * ((size_t) cfg->num_blocks + 1));
    visited = hir_alloc(ctx, (size_t) dom->max_block_id + 1);

    for (i = 0; i <= dom->max_block_id; i++) {
	dom->idom[i] = 0;
	dom->rpo_index[i] = -1;
	dom->df[i] = 0;
	visited[i] = 0;
    }
    index_cfg_blocks(dom, cfg);

    if (!cfg->entry)
	return dom;

    postorder_cfg(dom, cfg->entry, visited, postorder, &postorder_count);
    dom->num_reachable = postorder_count;
    for (i = 0; i < postorder_count; i++) {
	HIRBasicBlock *block = postorder[postorder_count - i - 1];

	dom->rpo[i] = block;
	dom->rpo_index[block->id] = i;
    }

    dom->idom[cfg->entry->id] = cfg->entry;
    while (changed) {
	changed = 0;
	for (i = 1; i < dom->num_reachable; i++) {
	    HIRBasicBlock *block = dom->rpo[i];
	    HIRBasicBlock *new_idom = compute_block_idom(cfg, dom, block);

	    if (new_idom && dom->idom[block->id] != new_idom) {
		dom->idom[block->id] = new_idom;
		changed = 1;
	    }
	}
    }

    {
	HIRBasicBlock *pred;
	for (pred = cfg->blocks; pred; pred = pred->next) {
	    if (!block_has_reachable_idom(dom, pred))
		continue;
	    for (i = 0; i < pred->num_successors; i++) {
		HIRBasicBlock *succ = pred->successors[i];
		if (!block_has_reachable_idom(dom, succ))
			continue;
		if (succ->predecessor_count >= 2) {
		    HIRBasicBlock *runner = pred;
		    while (runner && runner != dom->idom[succ->id]) {
			HIRBlockList *node = dom->df[runner->id];
			int found = 0;
			while (node) {
			    if (node->block == succ) { found = 1; break; }
			    node = node->next;
			}
			if (!found) {
			    node = hir_alloc(ctx, sizeof(HIRBlockList));
			    node->block = succ;
			    node->next = dom->df[runner->id];
			    dom->df[runner->id] = node;
			}
			runner = dom->idom[runner->id];
		    }
		}
	    }
	}
    }

    return dom;
}

int
hir_verify_dominator_tree(HIRContext *ctx, HIRCFG *cfg, HIRDominatorTree *dom)
{
    int errors_before;
    int i;

    if (!ctx || !cfg || !dom)
	return 0;

    errors_before = ctx->error_count;

    if (cfg->num_blocks == 0)
	return dom->num_reachable == 0;

    if (!cfg->entry || dom->num_reachable <= 0)
	record_unsupported(ctx, "dom-tree: no reachable entry");
    else if (dom->idom[cfg->entry->id] != cfg->entry)
	record_unsupported(ctx, "dom-tree: entry idom is invalid");

    for (i = 0; i < dom->num_reachable; i++) {
	HIRBasicBlock *block = dom->rpo[i];
	HIRBasicBlock *runner;
	int steps;

	if (!block || block->id <= 0 || block->id > dom->max_block_id) {
	    record_unsupported(ctx, "dom-tree: invalid RPO block");
	    continue;
	}
	if (dom->block_by_id[block->id] != block)
	    record_unsupported_fmt(ctx, "dom-tree: block %d index mismatch", block->id);
	if (dom->rpo_index[block->id] != i)
	    record_unsupported_fmt(ctx, "dom-tree: block %d RPO index mismatch", block->id);
	if (!dom->idom[block->id]) {
	    record_unsupported_fmt(ctx, "dom-tree: block %d missing reachable idom", block->id);
	    continue;
	}
	if (!dom_contains_block(dom, dom->idom[block->id])
	    || dom->rpo_index[dom->idom[block->id]->id] < 0)
	    record_unsupported_fmt(ctx, "dom-tree: block %d idom is unreachable", block->id);
	if (block != cfg->entry && dom->idom[block->id] == block)
	    record_unsupported_fmt(ctx, "dom-tree: non-entry block %d self idom", block->id);

	runner = block;
	steps = 0;
	while (runner && runner != cfg->entry && steps <= dom->num_reachable) {
	    if (!dom_contains_block(dom, runner)
		|| dom->rpo_index[runner->id] < 0)
		break;
	    runner = dom->idom[runner->id];
	    steps++;
	}
	if (runner != cfg->entry || steps > dom->num_reachable)
	    record_unsupported_fmt(ctx, "dom-tree: block %d idom chain misses entry", block->id);
    }

    return ctx->error_count == errors_before;
}

static int
ssa_defines_value(HIRSSAInstr *instr)
{
    return instr
	&& (instr->kind == HIR_TAC_CONST
	    || instr->kind == HIR_TAC_LOAD_ERROR
	    || instr->kind == HIR_TAC_LOAD_LOCAL
	    || instr->kind == HIR_TAC_UNARY
	    || instr->kind == HIR_TAC_BINARY
	    || instr->kind == HIR_TAC_CALL
	    || instr->kind == HIR_TAC_CALL_VERB
	    || instr->kind == HIR_TAC_PUT_PROP
	    || instr->kind == HIR_TAC_INDEX_SET
	    || instr->kind == HIR_TAC_RANGE_REF
	    || instr->kind == HIR_TAC_RANGE_SET
	    || instr->kind == HIR_TAC_UNSUPPORTED
	    || instr->kind == HIR_TAC_PHI);
}

static void
append_ssa_block(HIRSSAProgram *ssa, HIRSSABlock *block)
{
    if (ssa->last_block)
	ssa->last_block->next = block;
    else
	ssa->blocks = block;
    ssa->last_block = block;
    ssa->num_blocks++;
}

static void
emit_ssa_instr(HIRSSAProgram *ssa, HIRSSABlock *block, HIRSSAInstr *instr)
{
    if (block->last)
	block->last->next = instr;
    else
	block->first = instr;
    block->last = instr;
    instr->next = 0;
    ssa->num_instructions++;
    if (ssa_defines_value(instr))
	ssa->num_values++;
}

static HIRSSAInstr *
new_ssa_instr(HIRContext *ctx, HIRTacInstr *tac)
{
    HIRSSAInstr *instr = hir_alloc(ctx, sizeof(HIRSSAInstr));

    instr->kind = tac->kind;
    instr->source_lineno = tac->source_lineno;
    instr->bytecode_pc = tac->bytecode_pc;
    instr->error_label = tac->error_label;
    instr->value = tac->dst;
    instr->src1 = tac->src1;
    instr->src2 = tac->src2;
    instr->src3 = tac->src3;
    instr->label = tac->label;
    instr->local_id = tac->local_id;
    instr->op = tac->op;
    instr->literal = tac->literal;
    instr->func = tac->func;
    instr->resume_key = tac->resume_key;
    instr->num_stack_values = tac->num_stack_values;
    instr->stack_values = tac->stack_values;
    instr->stack_slots = tac->stack_slots;
    instr->num_local_values = 0;
    instr->local_values = 0;
    instr->phi_args = 0;
    instr->copies = 0;
    instr->next = 0;

    return instr;
}

static int
ssa_stack_depth(HIRContext *ctx, HIRCFG *cfg, HIRSSAInstr **placed_phis,
		int max_block_id, int num_locals)
{
    HIRBasicBlock *block;
    int *counts;
    int depth = 1;
    int i;

    if (num_locals <= 0)
	return 1;

    counts = hir_calloc(ctx, num_locals, sizeof(int));
    for (i = 0; i < num_locals; i++)
	counts[i] = 1;

    for (block = cfg->blocks; block; block = block->next) {
	HIRTacInstr *tac;

	for (tac = block->first; tac; tac = tac->next) {
	    if ((tac->kind == HIR_TAC_STORE_LOCAL
		 || tac->kind == HIR_TAC_INDEX_SET)
		&& tac->local_id >= 0 && tac->local_id < num_locals)
		counts[tac->local_id]++;
	    if (tac == block->last)
		break;
	}
    }

    for (i = 1; i <= max_block_id; i++) {
	HIRSSAInstr *phi;

	for (phi = placed_phis[i]; phi; phi = phi->next) {
	    if (phi->local_id >= 0 && phi->local_id < num_locals)
		counts[phi->local_id]++;
	}
    }

    for (i = 0; i < num_locals; i++) {
	if (counts[i] > depth)
	    depth = counts[i];
    }

    return depth + 1;
}

static int
current_version(HIRContext *ctx, int v, int num_locals, int *stacks,
		int *stack_tops, int max_depth, HIRSSABlock *entry_block,
		HIRSSAProgram *ssa)
{
    if (v < 0 || v >= num_locals) {
	record_unsupported_fmt(ctx, "ssa-build: invalid local id %d in version stack", v);
	return 0;
    }

    if (stack_tops[v] == 0) {
	/* Empty stack! Insert implicit load at entry block. */
	int t_init = ctx->next_temp++;
	HIRSSAInstr *load = hir_alloc(ctx, sizeof(HIRSSAInstr));
	int internal_local = ctx->var_names
	    && v >= (int) ctx->var_names->size;
	int uninitialized_local = !internal_local
	    && v >= ctx->first_user_local;

	memset(load, 0, sizeof(HIRSSAInstr));
	load->kind = internal_local || uninitialized_local
	    ? HIR_TAC_CONST : HIR_TAC_LOAD_LOCAL;
	load->source_lineno = entry_block ? entry_block->first_lineno : 0;
	load->bytecode_pc = NO_BYTECODE_PC;
	load->value = t_init;
	load->src1 = 0;
	load->src2 = 0;
	load->src3 = 0;
	load->label = 0;
	load->local_id = internal_local || uninitialized_local ? -1 : v;
	load->op = HIR_OP_ADD;
	load->literal.type = uninitialized_local ? TYPE_NONE : TYPE_INT;
	load->literal.v.num = 0;
	load->num_stack_values = 0;
	load->stack_values = 0;
	load->stack_slots = 0;
	load->num_local_values = 0;
	load->local_values = 0;
	load->phi_args = 0;
	load->copies = 0;

	/* Find last Phi node in entry block to insert after it. */
	HIRSSAInstr *last_phi = 0;
	HIRSSAInstr *curr = entry_block->first;
	while (curr && curr->kind == HIR_TAC_PHI) {
	    last_phi = curr;
	    curr = curr->next;
	}

	if (last_phi) {
	    load->next = last_phi->next;
	    last_phi->next = load;
	    if (entry_block->last == last_phi)
		entry_block->last = load;
	} else {
	    load->next = entry_block->first;
	    entry_block->first = load;
	    if (!entry_block->last)
		entry_block->last = load;
	}

	ssa->num_instructions++;
	ssa->num_values++;

	stacks[v * max_depth + stack_tops[v]++] = t_init;
    }
    return stacks[v * max_depth + stack_tops[v] - 1];
}

static int hir_kind_can_materialize(HIRTacKind);

static void
rename_block_recurse(HIRContext *ctx, HIRBasicBlock *b, HIRDominatorTree *dom,
		     HIRSSAInstr **placed_phis, HIRSSABlock **ssa_blocks,
		     int num_locals, int *stacks, int *stack_tops, int max_depth,
		     int *temp_map, int temp_map_size,
		     HIRSSABlock *entry_block, HIRSSAProgram *ssa,
		     unsigned char *visited)
{
    HIRSSABlock *ssa_block = ssa_blocks[b->id];
    HIRSSAInstr *curr_phi;
    HIRTacInstr *tac;
    int i;

    visited[b->id] = 1;

    /* 1. Prepend Phi nodes and push their definitions onto version stacks */
    if (placed_phis[b->id]) {
	HIRSSAInstr *prev_first = ssa_block->first;
	HIRSSAInstr *last_phi = 0;
	ssa_block->first = placed_phis[b->id];
	curr_phi = placed_phis[b->id];
	while (curr_phi) {
	    curr_phi->value = ctx->next_temp++;
	    if (curr_phi->local_id >= 0 && curr_phi->local_id < num_locals)
		stacks[curr_phi->local_id * max_depth
		       + stack_tops[curr_phi->local_id]++] = curr_phi->value;
	    else
		record_unsupported_fmt(ctx, "ssa-build: invalid phi local id %d", curr_phi->local_id);
	    last_phi = curr_phi;
	    curr_phi = curr_phi->next;
	    ssa->num_instructions++;
	    ssa->num_values++;
	}
	if (last_phi) {
	    last_phi->next = prev_first;
	    if (!ssa_block->last)
		ssa_block->last = last_phi;
	}
    }

    /* 2. Traverse instructions of b */
    for (tac = b->first; tac; tac = tac->next) {
	int src1_renamed = (tac->src1 > 0 && tac->src1 < temp_map_size) ? temp_map[tac->src1] : tac->src1;
	int src2_renamed = (tac->src2 > 0 && tac->src2 < temp_map_size) ? temp_map[tac->src2] : tac->src2;
	int src3_renamed = (tac->src3 > 0 && tac->src3 < temp_map_size) ? temp_map[tac->src3] : tac->src3;

	if (tac->kind == HIR_TAC_LOAD_LOCAL) {
	    int t_val = current_version(ctx, tac->local_id, num_locals,
					stacks, stack_tops, max_depth,
					entry_block, ssa);
	    if (tac->dst > 0 && tac->dst < temp_map_size)
		temp_map[tac->dst] = t_val;
	} else if (tac->kind == HIR_TAC_STORE_LOCAL) {
	    if (tac->local_id >= 0 && tac->local_id < num_locals)
		stacks[tac->local_id * max_depth
		       + stack_tops[tac->local_id]++] = src1_renamed;
	    else
		record_unsupported_fmt(ctx, "ssa-build: invalid store local id %d", tac->local_id);
	} else {
	    HIRSSAInstr *ssa_inst = new_ssa_instr(ctx, tac);
	    int j;

	    ssa_inst->src1 = src1_renamed;
	    ssa_inst->src2 = src2_renamed;
	    ssa_inst->src3 = src3_renamed;
	    if (tac->num_stack_values) {
		ssa_inst->stack_values = hir_alloc(ctx,
				 sizeof(int) * tac->num_stack_values);
		ssa_inst->stack_slots = hir_alloc(ctx,
				 sizeof(ResumeStackSlot) * tac->num_stack_values);
		memcpy(ssa_inst->stack_slots, tac->stack_slots,
		       sizeof(ResumeStackSlot) * tac->num_stack_values);
		for (j = 0; j < tac->num_stack_values; j++) {
		    int value = tac->stack_values[j];
		    ssa_inst->stack_values[j] =
			(value > 0 && value < temp_map_size)
			? temp_map[value] : value;
		}
	    }
	    ssa_inst->num_local_values = ctx->var_names
		&& hir_kind_can_materialize(ssa_inst->kind)
		? ctx->var_names->size : 0;
	    if (ssa_inst->num_local_values) {
		ssa_inst->local_values = hir_alloc(ctx,
				 sizeof(int) * ssa_inst->num_local_values);
		for (j = 0; j < ssa_inst->num_local_values; j++)
		    ssa_inst->local_values[j] = stack_tops[j]
			? stacks[j * max_depth + stack_tops[j] - 1] : 0;
	    }
	    if (tac->dst > 0 && tac->dst < temp_map_size)
		temp_map[tac->dst] = tac->dst;
	    emit_ssa_instr(ssa, ssa_block, ssa_inst);
	    if (tac->kind == HIR_TAC_INDEX_SET) {
		if (tac->local_id >= 0 && tac->local_id < num_locals)
		    stacks[tac->local_id * max_depth
			   + stack_tops[tac->local_id]++] = ssa_inst->value;
		else
		    record_unsupported_fmt(ctx, "ssa-build: invalid index-set local id %d", tac->local_id);
	    }
	}

	if (tac == b->last)
	    break;
    }

    /* 3. Fill in successor Phi arguments */
    for (i = 0; i < b->num_successors; i++) {
	HIRBasicBlock *succ = b->successors[i];
	curr_phi = placed_phis[succ->id];
	while (curr_phi) {
	    HIRPhiArg *arg = curr_phi->phi_args;
	    while (arg) {
		if (arg->block_id == b->id) {
		    arg->value = current_version(ctx, curr_phi->local_id,
						 num_locals, stacks,
						 stack_tops, max_depth,
						 entry_block, ssa);
		    break;
		}
		arg = arg->next;
	    }
	    curr_phi = curr_phi->next;
	}
    }

    /* 4. Recurse on dominator tree children */
    for (i = 0; i < dom->num_reachable; i++) {
	HIRBasicBlock *c = dom->rpo[i];
	if (c != b && dom->idom[c->id] == b) {
	    rename_block_recurse(ctx, c, dom, placed_phis, ssa_blocks,
				 num_locals, stacks, stack_tops, max_depth,
				 temp_map, temp_map_size,
				 entry_block, ssa, visited);
	}
    }

    /* 5. Pop Phi node definitions from version stacks */
    curr_phi = placed_phis[b->id];
    while (curr_phi) {
	if (curr_phi->local_id >= 0 && curr_phi->local_id < num_locals)
	    stack_tops[curr_phi->local_id]--;
	curr_phi = curr_phi->next;
    }

    /* 6. Pop store_local definitions from version stacks */
    for (tac = b->first; tac; tac = tac->next) {
	if ((tac->kind == HIR_TAC_STORE_LOCAL
	     || tac->kind == HIR_TAC_INDEX_SET)
	    && tac->local_id >= 0 && tac->local_id < num_locals)
	    stack_tops[tac->local_id]--;
	if (tac == b->last)
	    break;
    }
}

static int
hir_kind_can_materialize(HIRTacKind kind)
{
    switch (kind) {
    case HIR_TAC_DEOPT:
    case HIR_TAC_LOAD_LOCAL:
    case HIR_TAC_UNARY:
    case HIR_TAC_BINARY:
    case HIR_TAC_CALL:
    case HIR_TAC_CALL_VERB:
    case HIR_TAC_PUT_PROP:
    case HIR_TAC_INDEX_SET:
    case HIR_TAC_RANGE_REF:
    case HIR_TAC_RANGE_SET:
    case HIR_TAC_UNSUPPORTED:
	return 1;
    default:
	return 0;
    }
}

static unsigned char *
compute_local_live_in(HIRContext *ctx, HIRCFG *cfg, HIRBlockList **preds,
		      int max_block_id, int num_locals)
{
    size_t state_size = ((size_t) max_block_id + 1) * num_locals;
    unsigned char *defs = hir_calloc(ctx, state_size, sizeof(unsigned char));
    unsigned char *uses = hir_calloc(ctx, state_size, sizeof(unsigned char));
    unsigned char *dirty_in = hir_calloc(ctx, state_size,
					 sizeof(unsigned char));
    unsigned char *dirty_out = hir_calloc(ctx, state_size,
					  sizeof(unsigned char));
    unsigned char *live_in = hir_calloc(ctx, state_size,
					sizeof(unsigned char));
    unsigned char *live_out = hir_calloc(ctx, state_size,
					 sizeof(unsigned char));
    unsigned char *seen_def = hir_calloc(ctx, num_locals,
					 sizeof(unsigned char));
    HIRBasicBlock *block;
    int changed;
    int i;

    if (num_locals <= 0)
	return live_in;

    for (block = cfg->blocks; block; block = block->next) {
	HIRTacInstr *instr;
	unsigned char *block_defs = defs + (size_t) block->id * num_locals;

	for (instr = block->first; instr; instr = instr->next) {
	    if ((instr->kind == HIR_TAC_STORE_LOCAL
		 || instr->kind == HIR_TAC_INDEX_SET)
		&& instr->local_id >= 0 && instr->local_id < num_locals)
		block_defs[instr->local_id] = 1;
	    if (instr == block->last)
		break;
	}
    }

    do {
	changed = 0;
	for (block = cfg->blocks; block; block = block->next) {
	    unsigned char *in = dirty_in + (size_t) block->id * num_locals;
	    unsigned char *out = dirty_out + (size_t) block->id * num_locals;
	    unsigned char *block_defs = defs + (size_t) block->id * num_locals;
	    HIRBlockList *pred;

	    for (i = 0; i < num_locals; i++) {
		int new_in = 0;
		int new_out;

		for (pred = preds[block->id]; pred; pred = pred->next)
		    if (dirty_out[(size_t) pred->block->id * num_locals + i]) {
			new_in = 1;
			break;
		    }
		new_out = new_in || block_defs[i];
		if (in[i] != new_in || out[i] != new_out) {
		    in[i] = new_in;
		    out[i] = new_out;
		    changed = 1;
		}
	    }
	}
    } while (changed);

    for (block = cfg->blocks; block; block = block->next) {
	HIRTacInstr *instr;
	unsigned char *block_uses = uses + (size_t) block->id * num_locals;
	unsigned char *in = dirty_in + (size_t) block->id * num_locals;

	memset(seen_def, 0, num_locals);
	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_LOAD_LOCAL
		&& instr->local_id >= 0 && instr->local_id < num_locals
		&& !seen_def[instr->local_id])
		block_uses[instr->local_id] = 1;
	    if (hir_kind_can_materialize(instr->kind))
		for (i = 0; i < num_locals; i++)
		    if (in[i] && !seen_def[i])
			block_uses[i] = 1;
	    if ((instr->kind == HIR_TAC_STORE_LOCAL
		 || instr->kind == HIR_TAC_INDEX_SET)
		&& instr->local_id >= 0 && instr->local_id < num_locals)
		seen_def[instr->local_id] = 1;
	    if (instr == block->last)
		break;
	}
    }

    do {
	changed = 0;
	for (block = cfg->blocks; block; block = block->next) {
	    unsigned char *in = live_in + (size_t) block->id * num_locals;
	    unsigned char *out = live_out + (size_t) block->id * num_locals;
	    unsigned char *block_defs = defs + (size_t) block->id * num_locals;
	    unsigned char *block_uses = uses + (size_t) block->id * num_locals;

	    for (i = 0; i < num_locals; i++) {
		int new_out = 0;
		int new_in;
		int succ;

		for (succ = 0; succ < block->num_successors; succ++)
		    if (live_in[(size_t) block->successors[succ]->id
				* num_locals + i]) {
			new_out = 1;
			break;
		    }
		new_in = block_uses[i] || (new_out && !block_defs[i]);
		if (in[i] != new_in || out[i] != new_out) {
		    in[i] = new_in;
		    out[i] = new_out;
		    changed = 1;
		}
	    }
	}
    } while (changed);

    return live_in;
}

HIRSSAProgram *
hir_build_ssa(HIRContext *ctx, HIRCFG *cfg)
{
    HIRSSAProgram *ssa;
    HIRDominatorTree *dom;
    HIRBasicBlock *cfg_block;
    HIRBlockList **preds;
    int max_block_id;
    int num_locals;
    HIRBlockList **defs;
    HIRSSAInstr **placed_phis;
    HIRSSABlock **ssa_blocks;
    unsigned char *is_def;
    unsigned char *live_in;
    int *stacks;
    int *stack_tops;
    int max_depth;
    int *temp_map;
    int temp_map_size;
    unsigned char *visited;
    int i;

    if (!ctx || !cfg)
	return 0;

    dom = hir_build_dominator_tree(ctx, cfg);
    if (!dom)
	return 0;

    max_block_id = dom->max_block_id;
    num_locals = ctx->next_local;

    /* Build predecessors lists */
    preds = hir_calloc(ctx, max_block_id + 1, sizeof(HIRBlockList *));
    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	for (i = 0; i < cfg_block->num_successors; i++) {
	    HIRBasicBlock *succ = cfg_block->successors[i];
	    HIRBlockList *node = hir_alloc(ctx, sizeof(HIRBlockList));
	    node->block = cfg_block;
	    node->next = preds[succ->id];
	    preds[succ->id] = node;
	}
    }

    live_in = compute_local_live_in(ctx, cfg, preds, max_block_id,
				    num_locals);

    /* Find all defs for each local variable */
    defs = hir_calloc(ctx, num_locals, sizeof(HIRBlockList *));
    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	HIRTacInstr *tac;
	for (tac = cfg_block->first; tac; tac = tac->next) {
	    if (tac->kind == HIR_TAC_STORE_LOCAL
		|| tac->kind == HIR_TAC_INDEX_SET) {
		int v = tac->local_id;
		if (v >= 0 && v < num_locals) {
		    /* Check if block is already in defs[v] */
		    HIRBlockList *curr = defs[v];
		    int found = 0;
		    while (curr) {
			if (curr->block == cfg_block) { found = 1; break; }
			curr = curr->next;
		    }
		    if (!found) {
			HIRBlockList *node = hir_alloc(ctx, sizeof(HIRBlockList));
			node->block = cfg_block;
			node->next = defs[v];
			defs[v] = node;
		    }
		}
	    }
	    if (tac == cfg_block->last)
		break;
	}
    }

    /* Place Phi Nodes (Cytron's Algorithm) */
    placed_phis = hir_calloc(ctx, max_block_id + 1, sizeof(HIRSSAInstr *));
    is_def = hir_calloc(ctx, max_block_id + 1, sizeof(unsigned char));

    {
	int work_head = 0, work_tail = 0;
	HIRBasicBlock **work_list = hir_calloc(ctx, cfg->num_blocks + 1, sizeof(HIRBasicBlock *));
	unsigned char *added = hir_calloc(ctx, max_block_id + 1, sizeof(unsigned char));

	for (i = 0; i < num_locals; i++) {
	    HIRBlockList *def_node;
	    work_head = 0;
	    work_tail = 0;
	    memset(added, 0, (max_block_id + 1) * sizeof(unsigned char));

	    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next)
		is_def[cfg_block->id] = 0;

	    for (def_node = defs[i]; def_node; def_node = def_node->next) {
		is_def[def_node->block->id] = 1;
		work_list[work_tail++] = def_node->block;
	    }

	    while (work_head < work_tail) {
		HIRBasicBlock *n = work_list[work_head++];
		HIRBlockList *df_node;

		for (df_node = dom->df[n->id]; df_node; df_node = df_node->next) {
		    HIRBasicBlock *y = df_node->block;
		    if (!added[y->id]
			&& live_in[(size_t) y->id * num_locals + i]) {
			/* Insert Phi node at y for variable i */
			HIRSSAInstr *phi = hir_alloc(ctx, sizeof(HIRSSAInstr));

			memset(phi, 0, sizeof(HIRSSAInstr));
			phi->kind = HIR_TAC_PHI;
			phi->source_lineno = y->first_lineno;
			phi->bytecode_pc = NO_BYTECODE_PC;
			phi->value = 0; /* filled in renaming */
			phi->num_stack_values = 0;
			phi->stack_values = 0;
			phi->stack_slots = 0;
			phi->num_local_values = 0;
			phi->local_values = 0;
			phi->src1 = 0;
			phi->src2 = 0;
			phi->src3 = 0;
			phi->label = 0;
			phi->local_id = i;
			phi->op = HIR_OP_ADD;
			phi->literal.type = TYPE_NONE;
			phi->phi_args = 0;
			phi->copies = 0;

			/* Create Phi arguments for each predecessor of y */
			HIRBlockList *p_node = preds[y->id];
			while (p_node) {
			    HIRPhiArg *arg = hir_alloc(ctx, sizeof(HIRPhiArg));
			    arg->block_id = p_node->block->id;
			    arg->value = 0; /* filled in renaming */
			    arg->next = phi->phi_args;
			    phi->phi_args = arg;
			    p_node = p_node->next;
			}

			phi->next = placed_phis[y->id];
			placed_phis[y->id] = phi;

			added[y->id] = 1;
			if (!is_def[y->id]) {
			    is_def[y->id] = 1;
			    work_list[work_tail++] = y;
			}
		    }
		}
	    }
	}
    }

    /* Build SSA Program and SSABlocks */
    ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    ssa->form = HIR_FORM_SSA;
    ssa->cfg = cfg;
    ssa->blocks = 0;
    ssa->last_block = 0;
    ssa->num_blocks = 0;
    ssa->num_instructions = 0;
    ssa->num_values = 0;

    ssa_blocks = hir_calloc(ctx, max_block_id + 1, sizeof(HIRSSABlock *));
    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	HIRSSABlock *ssa_block = hir_alloc(ctx, sizeof(HIRSSABlock));
	ssa_block->id = cfg_block->id;
	ssa_block->first_lineno = cfg_block->first_lineno;
	ssa_block->last_lineno = cfg_block->last_lineno;
	ssa_block->first = 0;
	ssa_block->last = 0;
	ssa_block->next = 0;
	append_ssa_block(ssa, ssa_block);
	ssa_blocks[cfg_block->id] = ssa_block;
    }

    /* Setup Renaming structures */
    max_depth = ssa_stack_depth(ctx, cfg, placed_phis, max_block_id,
				num_locals);
    stacks = hir_calloc(ctx, num_locals * max_depth, sizeof(int));
    stack_tops = hir_calloc(ctx, num_locals, sizeof(int));

    temp_map_size = ctx->next_temp + cfg->num_blocks * num_locals + 1000;
    temp_map = hir_calloc(ctx, temp_map_size, sizeof(int));
    for (i = 0; i < temp_map_size; i++)
	temp_map[i] = i;

    visited = hir_calloc(ctx, max_block_id + 1, sizeof(unsigned char));

    /* Run preorder renaming from entry block */
    if (cfg->entry) {
	rename_block_recurse(ctx, cfg->entry, dom, placed_phis, ssa_blocks,
			     num_locals, stacks, stack_tops, max_depth,
			     temp_map, temp_map_size,
			     ssa_blocks[cfg->entry->id], ssa, visited);
    }

    /* For reachable blocks that become instruction-empty because local
       loads/stores disappear during SSA conversion, emit a non-semantic label
       to preserve the block and its control-flow edges for phis and SSA destruction. */
    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	HIRSSABlock *ssa_block = ssa_blocks[cfg_block->id];
	if (ssa_block && !ssa_block->first) {
	    HIRSSAInstr *label = hir_alloc(ctx, sizeof(HIRSSAInstr));

	    memset(label, 0, sizeof(HIRSSAInstr));
	    label->kind = HIR_TAC_LABEL;
	    label->source_lineno = cfg_block->first_lineno;
	    label->bytecode_pc = NO_BYTECODE_PC;
	    label->op = HIR_OP_ADD;
	    label->literal.type = TYPE_NONE;
	    emit_ssa_instr(ssa, ssa_block, label);
	}
    }

    return ssa;
}

static void
verify_ssa_value_use(HIRContext *ctx, int value, unsigned char *defined,
		     int max_value)
{
    if (value <= 0 || value > max_value || !defined[value])
	record_unsupported_fmt(ctx, "ssa: value %d used before definition", value);
}

static void
verify_ssa_value_def(HIRContext *ctx, int value, unsigned char *defined,
		     int max_value)
{
    if (value <= 0 || value > max_value) {
	record_unsupported_fmt(ctx, "ssa: invalid value definition %d", value);
	return;
    }

    if (defined[value])
	record_unsupported_fmt(ctx, "ssa: duplicate value definition %d", value);
    defined[value] = 1;
}

static HIRBasicBlock *
cfg_block_for_id(HIRCFG *cfg, int block_id)
{
    HIRBasicBlock *block;

    if (!cfg)
	return 0;

    for (block = cfg->blocks; block; block = block->next) {
	if (block->id == block_id)
	    return block;
    }

    return 0;
}

static int
cfg_has_predecessor(HIRCFG *cfg, HIRBasicBlock *block, int pred_id)
{
    HIRBasicBlock *pred;
    int i;

    if (!cfg || !block)
	return 0;

    for (pred = cfg->blocks; pred; pred = pred->next) {
	if (pred->id != pred_id)
	    continue;
	for (i = 0; i < pred->num_successors; i++) {
	    if (pred->successors[i] == block)
		return 1;
	}
    }

    return 0;
}

static void
verify_phi_shape(HIRContext *ctx, HIRSSAProgram *ssa, HIRSSABlock *block,
		 HIRSSAInstr *phi)
{
    HIRBasicBlock *cfg_block;
    HIRPhiArg *arg;
    unsigned char *seen;
    int max_block_id;
    int count = 0;

    if (!ssa->cfg)
	return;

    cfg_block = cfg_block_for_id(ssa->cfg, block->id);
    if (!cfg_block) {
	record_unsupported_fmt(ctx, "ssa: phi block %d is not in CFG", block->id);
	return;
    }

    max_block_id = max_cfg_block_id(ssa->cfg);
    seen = hir_calloc(ctx, (size_t) max_block_id + 1, sizeof(unsigned char));
    for (arg = phi->phi_args; arg; arg = arg->next) {
	HIRBasicBlock *pred = cfg_block_for_id(ssa->cfg, arg->block_id);

	count++;
	if (!pred || arg->block_id <= 0 || arg->block_id > max_block_id) {
	    record_unsupported_fmt(ctx, "ssa: phi has invalid predecessor arg %d", arg->block_id);
	    continue;
	}
	if (seen[arg->block_id])
	    record_unsupported_fmt(ctx, "ssa: phi has duplicate predecessor arg %d", arg->block_id);
	seen[arg->block_id] = 1;
	if (!cfg_has_predecessor(ssa->cfg, cfg_block, arg->block_id))
	    record_unsupported_fmt(ctx, "ssa: phi arg %d is not a CFG predecessor", arg->block_id);
    }

    if (count != cfg_block->predecessor_count)
	record_unsupported_fmt(ctx, "ssa: phi predecessor count mismatch in block %d", block->id);
}

static int
dom_block_dominates(HIRDominatorTree *dom, int dominator_id, int block_id)
{
    HIRBasicBlock *block;
    int steps = 0;

    if (!dom || dominator_id <= 0 || block_id <= 0
	|| dominator_id > dom->max_block_id || block_id > dom->max_block_id
	|| dom->rpo_index[dominator_id] < 0 || dom->rpo_index[block_id] < 0)
	return 0;

    block = dom->block_by_id[block_id];
    while (block && steps <= dom->num_reachable) {
	if (block->id == dominator_id)
	    return 1;
	if (dom->idom[block->id] == block)
	    break;
	block = dom->idom[block->id];
	steps++;
    }
    return 0;
}

static void
verify_ssa_dominating_use(HIRContext *ctx, HIRDominatorTree *dom, int value,
			   int use_block_id, int use_order, int phi_edge,
			   int max_value, int *def_block, int *def_order)
{
    if (value <= 0 || value > max_value || def_block[value] == 0)
	return;

    if (!dom || use_block_id <= 0 || use_block_id > dom->max_block_id
	|| dom->rpo_index[use_block_id] < 0)
	return;

    if (def_block[value] == use_block_id) {
	if (!phi_edge && def_order[value] >= use_order)
	    record_unsupported_fmt(ctx, "ssa: definition of value %d in block %d does not precede use", value, def_block[value]);
    } else if (!dom_block_dominates(dom, def_block[value], use_block_id)) {
	record_unsupported_fmt(ctx, "ssa: definition of value %d in block %d does not dominate use in block %d", value, def_block[value], use_block_id);
    }
}

static void
verify_ssa_dominance(HIRContext *ctx, HIRSSAProgram *ssa, int max_value)
{
    HIRDominatorTree *dom;
    HIRSSABlock *block;
    int *def_block;
    int *def_order;

    if (!ssa->cfg)
	return;

    dom = hir_build_dominator_tree(ctx, ssa->cfg);
    if (!dom)
	return;
    def_block = hir_calloc(ctx, (size_t) max_value + 1, sizeof(int));
    def_order = hir_calloc(ctx, (size_t) max_value + 1, sizeof(int));

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;
	int order = 0;

	for (instr = block->first; instr; instr = instr->next) {
	    if (ssa_defines_value(instr) && instr->value > 0
		&& instr->value <= max_value && def_block[instr->value] == 0) {
		def_block[instr->value] = block->id;
		def_order[instr->value] = order;
	    }
	    order++;
	    if (instr == block->last)
		break;
	}
    }

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;
	int order = 0;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_STORE_LOCAL:
	    case HIR_TAC_CALL:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
		verify_ssa_dominating_use(ctx, dom, instr->src1, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		break;
	    case HIR_TAC_UNARY:
		if (unary_op_has_operand(instr->op))
		    verify_ssa_dominating_use(ctx, dom, instr->src1,
					       block->id, order, 0, max_value,
					       def_block, def_order);
		break;
	    case HIR_TAC_BINARY:
	    case HIR_TAC_PUT_PROP:
	    case HIR_TAC_CALL_VERB:
	    case HIR_TAC_RANGE_REF:
	    case HIR_TAC_RANGE_SET:
		verify_ssa_dominating_use(ctx, dom, instr->src1, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		verify_ssa_dominating_use(ctx, dom, instr->src2, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		break;
	    case HIR_TAC_INDEX_SET:
		verify_ssa_dominating_use(ctx, dom, instr->src1, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		verify_ssa_dominating_use(ctx, dom, instr->src2, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		verify_ssa_dominating_use(ctx, dom, instr->src3, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		break;
	    case HIR_TAC_PHI:
		{
		    HIRPhiArg *arg;
		    for (arg = instr->phi_args; arg; arg = arg->next)
			verify_ssa_dominating_use(ctx, dom, arg->value,
					   arg->block_id, 0, 1, max_value,
					   def_block, def_order);
		}
		break;
	    default:
		break;
	    }
	    order++;
	    if (instr == block->last)
		break;
	}
    }
}

int
hir_verify_ssa(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    unsigned char *defined;
    int max_value;
    int errors_before;
    int block_count = 0;
    int instruction_count = 0;
    int value_count = 0;
    int i;

    if (!ctx || !ssa)
	return 0;

    errors_before = ctx->error_count;
    if (ssa->form != HIR_FORM_SSA)
	record_unsupported(ctx, "ssa: verifier requires SSA form");

    max_value = ctx->next_temp - 1;
    defined = hir_alloc(ctx, (size_t) max_value + 1);
    for (i = 0; i <= max_value; i++)
	defined[i] = 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;
	int seen_non_phi = 0;

	block_count++;
	if (!block->first || !block->last)
	    record_unsupported_fmt(ctx, "ssa: block %d has no instructions", block->id);

	for (instr = block->first; instr; instr = instr->next) {
	    instruction_count++;

	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_DEOPT:
		break;
	    case HIR_TAC_CONST:
	    case HIR_TAC_LOAD_ERROR:
	    case HIR_TAC_LOAD_LOCAL:
		if (instr->kind == HIR_TAC_LOAD_LOCAL)
		    verify_local(ctx, instr->local_id);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_STORE_LOCAL:
		verify_local(ctx, instr->local_id);
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_UNARY:
		if (unary_op_has_operand(instr->op))
		    verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_BINARY:
	    case HIR_TAC_PUT_PROP:
	    case HIR_TAC_CALL_VERB:
	    case HIR_TAC_RANGE_REF:
	    case HIR_TAC_RANGE_SET:
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		verify_ssa_value_use(ctx, instr->src2, defined, max_value);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_INDEX_SET:
		verify_local(ctx, instr->local_id);
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		verify_ssa_value_use(ctx, instr->src2, defined, max_value);
		verify_ssa_value_use(ctx, instr->src3, defined, max_value);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_CALL:
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_BRANCH_FALSE:
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_RETURN:
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_UNSUPPORTED:
		if (instr->value > 0) {
		    verify_ssa_value_def(ctx, instr->value, defined, max_value);
		    value_count++;
		}
		break;
	    case HIR_TAC_PHI:
		if (seen_non_phi)
		    record_unsupported_fmt(ctx, "ssa: phi appears after non-phi in block %d", block->id);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_RETURN0:
		break;
	    case HIR_TAC_PARALLEL_COPY:
		record_unsupported(ctx, "ssa: parallel copy in SSA form");
		break;
	    }

	    if (instr->kind != HIR_TAC_PHI)
		seen_non_phi = 1;

	    if (instr == block->last)
		break;
	}
    }

    /* Second pass to verify Phi arguments after all definitions are known */
    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;
	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_PHI) {
		HIRPhiArg *arg = instr->phi_args;
		verify_phi_shape(ctx, ssa, block, instr);
		while (arg) {
		    verify_ssa_value_use(ctx, arg->value, defined, max_value);
		    arg = arg->next;
		}
	    }
	    if (instr == block->last)
		break;
	}
    }

    verify_ssa_dominance(ctx, ssa, max_value);

    if (block_count != ssa->num_blocks)
	record_unsupported(ctx, "SSA block count mismatch");
    if (instruction_count != ssa->num_instructions)
	record_unsupported(ctx, "SSA instruction count mismatch");
    if (value_count != ssa->num_values)
	record_unsupported(ctx, "SSA value count mismatch");

    return ctx->error_count == errors_before;
}

static HIRValueFact
join_value_fact(HIRValueFact lhs, HIRValueFact rhs)
{
    HIRValueFact result;

    if (lhs.kind == HIR_VALUE_BOTTOM)
	return rhs;
    if (rhs.kind == HIR_VALUE_BOTTOM)
	return lhs;
    result.constant = 0;
    result.error = E_NONE;
    if (lhs.kind == HIR_VALUE_FACT_UNKNOWN
	|| rhs.kind == HIR_VALUE_FACT_UNKNOWN)
	result.kind = HIR_VALUE_FACT_UNKNOWN;
    else if (lhs.kind == HIR_VALUE_FACT_ERROR
	     && rhs.kind == HIR_VALUE_FACT_ERROR
	     && lhs.error == rhs.error)
	return lhs;
    else if (lhs.kind == HIR_VALUE_FACT_ERROR
	     || rhs.kind == HIR_VALUE_FACT_ERROR)
	result.kind = HIR_VALUE_FACT_UNKNOWN;
    else if (lhs.kind == HIR_VALUE_FACT_CONSTANT
	     && rhs.kind == HIR_VALUE_FACT_CONSTANT
	     && lhs.constant == rhs.constant)
	return lhs;
    else
	result.kind = HIR_VALUE_FACT_INT;
    return result;
}

static HIRValueFact
constant_fact(Num value)
{
    HIRValueFact fact;

    fact.kind = HIR_VALUE_FACT_CONSTANT;
    fact.constant = value;
    fact.error = E_NONE;
    return fact;
}

static HIRValueFact
integer_fact(void)
{
    HIRValueFact fact;

    fact.kind = HIR_VALUE_FACT_INT;
    fact.constant = 0;
    fact.error = E_NONE;
    return fact;
}

static HIRValueFact
unknown_fact(void)
{
    HIRValueFact fact;

    fact.kind = HIR_VALUE_FACT_UNKNOWN;
    fact.constant = 0;
    fact.error = E_NONE;
    return fact;
}

static HIRValueFact
error_fact(enum error error)
{
    HIRValueFact fact;

    fact.kind = HIR_VALUE_FACT_ERROR;
    fact.constant = 0;
    fact.error = error;
    return fact;
}

static HIRValueFact
arithmetic_fact(IntegerArithmeticOperation operation, Num lhs, Num rhs)
{
    IntegerArithmeticResult result = integer_arithmetic(operation, lhs, rhs);

    return result.succeeded
	? constant_fact(result.value) : error_fact(result.error);
}

static HIRValueFact
analyze_unary(HIROp op, HIRValueFact operand)
{
    if (operand.kind == HIR_VALUE_BOTTOM
	|| operand.kind == HIR_VALUE_FACT_UNKNOWN)
	return operand;
    if (operand.kind != HIR_VALUE_FACT_CONSTANT)
	return integer_fact();
    switch (op) {
    case HIR_OP_NEGATE:
	return arithmetic_fact(INTEGER_NEGATE, operand.constant, 0);
    case HIR_OP_NOT:
	return constant_fact(!operand.constant);
    case HIR_OP_COMPLEMENT:
	return arithmetic_fact(INTEGER_COMPLEMENT, operand.constant, 0);
    case HIR_OP_ABS:
	return operand.constant < 0
	    ? arithmetic_fact(INTEGER_NEGATE, operand.constant, 0) : operand;
    case HIR_OP_TOINT:
	return operand;
    case HIR_OP_TYPEOF:
	return constant_fact(TYPE_INT);
    case HIR_OP_LENGTH:
	return integer_fact();
    case HIR_OP_MAKE_SINGLETON_LIST:
    case HIR_OP_CHECK_LIST_FOR_SPLICE:
	return unknown_fact();
    default:
	return unknown_fact();
    }
}

static HIRValueFact
analyze_binary(HIROp op, HIRValueFact lhs, HIRValueFact rhs)
{
    if (lhs.kind == HIR_VALUE_BOTTOM || rhs.kind == HIR_VALUE_BOTTOM) {
	HIRValueFact bottom = {HIR_VALUE_BOTTOM, 0, E_NONE};
	return bottom;
    }
    if (lhs.kind == HIR_VALUE_FACT_UNKNOWN
	|| rhs.kind == HIR_VALUE_FACT_UNKNOWN)
	return unknown_fact();
    if (op == HIR_OP_LIST_ADD_TAIL || op == HIR_OP_LIST_APPEND)
	return unknown_fact();
    if (lhs.kind != HIR_VALUE_FACT_CONSTANT
	|| rhs.kind != HIR_VALUE_FACT_CONSTANT)
	return integer_fact();
    switch (op) {
    case HIR_OP_ADD:
	return arithmetic_fact(INTEGER_ADD, lhs.constant, rhs.constant);
    case HIR_OP_SUB:
	return arithmetic_fact(INTEGER_SUBTRACT, lhs.constant, rhs.constant);
    case HIR_OP_MUL:
	return arithmetic_fact(INTEGER_MULTIPLY, lhs.constant, rhs.constant);
    case HIR_OP_DIV:
	return arithmetic_fact(INTEGER_DIVIDE, lhs.constant, rhs.constant);
    case HIR_OP_MOD:
	return arithmetic_fact(INTEGER_MODULUS, lhs.constant, rhs.constant);
    case HIR_OP_EXP:
	return arithmetic_fact(INTEGER_POWER, lhs.constant, rhs.constant);
    case HIR_OP_SHL:
	return arithmetic_fact(INTEGER_SHIFT_LEFT, lhs.constant, rhs.constant);
    case HIR_OP_SHR:
	return arithmetic_fact(INTEGER_SHIFT_RIGHT, lhs.constant, rhs.constant);
    case HIR_OP_LSHR:
	return arithmetic_fact(INTEGER_LOGICAL_SHIFT_RIGHT,
			       lhs.constant, rhs.constant);
    case HIR_OP_MIN:
	return constant_fact(lhs.constant < rhs.constant
			     ? lhs.constant : rhs.constant);
    case HIR_OP_MAX:
	return constant_fact(lhs.constant > rhs.constant
			     ? lhs.constant : rhs.constant);
    case HIR_OP_EQ:
	return constant_fact(lhs.constant == rhs.constant);
    case HIR_OP_NE:
	return constant_fact(lhs.constant != rhs.constant);
    case HIR_OP_LT:
	return constant_fact(lhs.constant < rhs.constant);
    case HIR_OP_LE:
	return constant_fact(lhs.constant <= rhs.constant);
    case HIR_OP_GT:
	return constant_fact(lhs.constant > rhs.constant);
    case HIR_OP_GE:
	return constant_fact(lhs.constant >= rhs.constant);
    default:
	return integer_fact();
    }
}

static int
update_value_fact(HIRValueFact *facts, int value, HIRValueFact candidate)
{
    HIRValueFact joined = join_value_fact(facts[value], candidate);

    if (joined.kind == facts[value].kind
	&& (joined.kind != HIR_VALUE_FACT_CONSTANT
	    || joined.constant == facts[value].constant)
	&& (joined.kind != HIR_VALUE_FACT_ERROR
	    || joined.error == facts[value].error))
	return 0;
    facts[value] = joined;
    return 1;
}

HIRValueAnalysis *
hir_analyze_ssa_values(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRValueAnalysis *analysis;
    HIRSSABlock *block;
    HIRBasicBlock *cfg_block;
    unsigned char *reachable;
    unsigned char *feasible_edges;
    int max_block_id = 0;
    int changed = 1;

    if (!ctx || !ssa || !ssa->cfg || ssa->form != HIR_FORM_SSA)
	return 0;
    for (cfg_block = ssa->cfg->blocks; cfg_block; cfg_block = cfg_block->next)
	if (cfg_block->id > max_block_id)
	    max_block_id = cfg_block->id;
    analysis = hir_alloc(ctx, sizeof(HIRValueAnalysis));
    analysis->num_facts = ctx->next_temp;
    analysis->facts = hir_calloc(ctx, analysis->num_facts,
				 sizeof(HIRValueFact));
    reachable = hir_calloc(ctx, max_block_id + 1, sizeof(unsigned char));
    feasible_edges = hir_calloc(ctx,
		(size_t) (max_block_id + 1) * (max_block_id + 1),
		sizeof(unsigned char));
    if (ssa->cfg->entry)
	reachable[ssa->cfg->entry->id] = 1;

    while (changed) {
	changed = 0;
	for (block = ssa->blocks; block; block = block->next) {
	    HIRSSAInstr *instr;
	    HIRBasicBlock *basic;

	    if (!reachable[block->id])
		continue;
	    for (instr = block->first; instr; instr = instr->next) {
		HIRValueFact fact = {HIR_VALUE_BOTTOM, 0, E_NONE};

		switch (instr->kind) {
		case HIR_TAC_CONST:
		    fact = instr->literal.type == TYPE_INT
			? constant_fact(instr->literal.v.num) : unknown_fact();
		    break;
		case HIR_TAC_LOAD_LOCAL:
		    fact = integer_fact();
		    break;
		case HIR_TAC_UNARY:
		    fact = analyze_unary(instr->op,
			analysis->facts[instr->src1]);
		    break;
		case HIR_TAC_BINARY:
		    fact = analyze_binary(instr->op,
			analysis->facts[instr->src1],
			analysis->facts[instr->src2]);
		    break;
		case HIR_TAC_PHI:
		    {
			HIRPhiArg *arg;

			for (arg = instr->phi_args; arg; arg = arg->next)
			    if (feasible_edges[arg->block_id
				    * (max_block_id + 1) + block->id])
				fact = join_value_fact(fact,
					analysis->facts[arg->value]);
		    }
		    break;
		case HIR_TAC_CALL:
		case HIR_TAC_CALL_VERB:
		case HIR_TAC_PUT_PROP:
		case HIR_TAC_INDEX_SET:
		case HIR_TAC_RANGE_REF:
		case HIR_TAC_RANGE_SET:
		case HIR_TAC_UNSUPPORTED:
		    fact = unknown_fact();
		    break;
		default:
		    break;
		}
		if (ssa_defines_value(instr))
		    changed |= update_value_fact(analysis->facts,
					 instr->value, fact);
		if (instr == block->last)
		    break;
	    }

	    basic = cfg_block_for_id(ssa->cfg, block->id);
	    if (basic) {
		int first = 0;
		int last = basic->num_successors;

		if (block->last && block->last->kind == HIR_TAC_BRANCH_FALSE) {
		    HIRValueFact condition =
			analysis->facts[block->last->src1];

		    if (condition.kind == HIR_VALUE_BOTTOM)
			last = 0;
		    else if (condition.kind == HIR_VALUE_FACT_CONSTANT) {
			first = condition.constant ? 1 : 0;
			last = first + 1;
		    }
		}
		while (first < last) {
		    int successor = basic->successors[first++]->id;
		    int edge = block->id * (max_block_id + 1) + successor;

		    if (!feasible_edges[edge]) {
			feasible_edges[edge] = 1;
			changed = 1;
		    }
		    if (!reachable[successor]) {
			reachable[successor] = 1;
			changed = 1;
		    }
		}
	    }
	}
    }
    return analysis;
}

HIRValueKind
hir_value_kind(HIRValueAnalysis *analysis, int value)
{
    HIRValueFactKind kind;

    if (!analysis || value <= 0 || value >= analysis->num_facts)
	return HIR_VALUE_UNKNOWN;
    kind = analysis->facts[value].kind;
    if (kind == HIR_VALUE_FACT_CONSTANT)
	return HIR_VALUE_INT_CONSTANT;
    if (kind == HIR_VALUE_FACT_INT)
	return HIR_VALUE_INT;
    if (kind == HIR_VALUE_FACT_ERROR)
	return HIR_VALUE_ERROR;
    return HIR_VALUE_UNKNOWN;
}

Num
hir_value_constant(HIRValueAnalysis *analysis, int value)
{
    if (!analysis || value <= 0 || value >= analysis->num_facts
	|| analysis->facts[value].kind != HIR_VALUE_FACT_CONSTANT)
	return 0;
    return analysis->facts[value].constant;
}

enum error
hir_value_error(HIRValueAnalysis *analysis, int value)
{
    if (!analysis || value <= 0 || value >= analysis->num_facts
	|| analysis->facts[value].kind != HIR_VALUE_FACT_ERROR)
	return E_NONE;
    return analysis->facts[value].error;
}

static int
cfg_has_edge_id(HIRBasicBlock *from, int target_id)
{
    int i;

    for (i = 0; from && i < from->num_successors; i++)
	if (from->successors[i]->id == target_id)
	    return 1;
    return 0;
}

static void
prune_ssa_blocks(HIRSSAProgram *ssa, unsigned char *reachable)
{
    HIRSSABlock *block = ssa->blocks;
    HIRSSABlock *previous = 0;

    ssa->num_blocks = 0;
    ssa->num_instructions = 0;
    ssa->num_values = 0;
    ssa->last_block = 0;
    while (block) {
	HIRSSABlock *next = block->next;

	if (reachable[block->id]) {
	    HIRSSAInstr *instr;

	    if (previous)
		previous->next = block;
	    else
		ssa->blocks = block;
	    previous = block;
	    ssa->last_block = block;
	    ssa->num_blocks++;
	    for (instr = block->first; instr; instr = instr->next) {
		ssa->num_instructions++;
		if (ssa_defines_value(instr))
		    ssa->num_values++;
		if (instr == block->last)
		    break;
	    }
	}
	block = next;
    }
    if (previous)
	previous->next = 0;
    else
	ssa->blocks = 0;
}

static void
prune_phi_arguments(HIRSSAProgram *ssa, unsigned char *reachable)
{
    HIRSSABlock *block;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_PHI) {
		HIRPhiArg *arg = instr->phi_args;
		HIRPhiArg *previous = 0;

		while (arg) {
		    HIRPhiArg *next = arg->next;
		    HIRBasicBlock *pred = cfg_block_for_id(ssa->cfg,
						       arg->block_id);

		    if (reachable[arg->block_id]
			&& cfg_has_edge_id(pred, block->id)) {
			if (previous)
			    previous->next = arg;
			else
			    instr->phi_args = arg;
			previous = arg;
		    }
		    arg = next;
		}
		if (previous)
		    previous->next = 0;
		else
		    instr->phi_args = 0;
	    }
	    if (instr == block->last)
		break;
	}
    }
}

static void
ssa_block_normalize_phi_order(HIRSSABlock *block)
{
    HIRSSAInstr *instr;
    HIRSSAInstr *phis_head = 0, *phis_tail = 0;
    HIRSSAInstr *non_phis_head = 0, *non_phis_tail = 0;
    HIRSSAInstr *next;

    if (!block || !block->first)
	return;

    for (instr = block->first; instr; instr = next) {
	next = (instr == block->last) ? 0 : instr->next;
	instr->next = 0;

	if (instr->kind == HIR_TAC_PHI) {
	    if (phis_tail)
		phis_tail->next = instr;
	    else
		phis_head = instr;
	    phis_tail = instr;
	} else {
	    if (non_phis_tail)
		non_phis_tail->next = instr;
	    else
		non_phis_head = instr;
	    non_phis_tail = instr;
	}
    }

    if (phis_head) {
	block->first = phis_head;
	if (non_phis_head) {
	    phis_tail->next = non_phis_head;
	    block->last = non_phis_tail;
	} else {
	    block->last = phis_tail;
	}
    } else {
	block->first = non_phis_head;
	block->last = non_phis_tail;
    }
}

int
hir_optimize_ssa_constants(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRValueAnalysis *analysis;
    HIRSSABlock *block;
    HIRBasicBlock *cfg_block;
    unsigned char *reachable;
    int max_block_id = 0;
    int changes = 0;

    if (!ctx || !ssa || !ssa->cfg || ssa->form != HIR_FORM_SSA)
	return 0;
    analysis = hir_analyze_ssa_values(ctx, ssa);
    if (!analysis)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if ((instr->kind == HIR_TAC_UNARY
		 || instr->kind == HIR_TAC_BINARY
		 || instr->kind == HIR_TAC_PHI)
		&& hir_value_kind(analysis, instr->value)
		== HIR_VALUE_INT_CONSTANT) {
		instr->kind = HIR_TAC_CONST;
		instr->literal.type = TYPE_INT;
		instr->literal.v.num = hir_value_constant(analysis,
							  instr->value);
		instr->src1 = instr->src2 = instr->src3 = 0;
		instr->phi_args = 0;
		changes++;
	    }
	    if (instr == block->last)
		break;
	}
	ssa_block_normalize_phi_order(block);
	if (block->last && block->last->kind == HIR_TAC_BRANCH_FALSE
	    && hir_value_kind(analysis, block->last->src1)
	    == HIR_VALUE_INT_CONSTANT) {
	    HIRBasicBlock *basic = cfg_block_for_id(ssa->cfg, block->id);
	    int successor_index = hir_value_constant(analysis,
						block->last->src1) ? 1 : 0;

	    if (basic && basic->num_successors == 2) {
		HIRBasicBlock *successor = basic->successors[successor_index];

		basic->successors[0] = successor;
		basic->num_successors = 1;
		block->last->kind = HIR_TAC_JUMP;
		block->last->src1 = 0;
		block->last->bytecode_pc = NO_BYTECODE_PC;
		if (basic->last) {
		    basic->last->kind = HIR_TAC_JUMP;
		    basic->last->bytecode_pc = NO_BYTECODE_PC;
		    basic->last->label = successor->first
			&& successor->first->kind == HIR_TAC_LABEL
			? successor->first->label : 0;
		}
		changes++;
	    }
	}
    }

    for (cfg_block = ssa->cfg->blocks; cfg_block; cfg_block = cfg_block->next)
	if (cfg_block->id > max_block_id)
	    max_block_id = cfg_block->id;
    reachable = hir_calloc(ctx, max_block_id + 1, sizeof(unsigned char));
    mark_reachable_cfg_blocks(ssa->cfg, reachable);
    prune_cfg_blocks(ssa->cfg, reachable);
    prune_ssa_blocks(ssa, reachable);
    prune_phi_arguments(ssa, reachable);
    return changes;
}

static HIRSSABlock *
ssa_block_for_id(HIRSSAProgram *ssa, int block_id)
{
    HIRSSABlock *block;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	if (block->id == block_id)
	    return block;
    }

    return 0;
}

static HIRSSABlock *
new_ssa_block_for_cfg(HIRContext *ctx, HIRBasicBlock *cfg_block)
{
    HIRSSABlock *block = hir_alloc(ctx, sizeof(HIRSSABlock));

    block->id = cfg_block->id;
    block->first_lineno = cfg_block->first_lineno;
    block->last_lineno = cfg_block->last_lineno;
    block->first = 0;
    block->last = 0;
    block->next = 0;

    return block;
}

static HIRSSADestructionMove *
append_destruction_move(HIRContext *ctx, HIRSSADestructionMove **moves,
			int pred_block_id, int target_block_id,
			int dst, int src, unsigned source_lineno)
{
    HIRSSADestructionMove *move = hir_alloc(ctx, sizeof(HIRSSADestructionMove));
    HIRSSADestructionMove *tail;

    move->pred_block_id = pred_block_id;
    move->target_block_id = target_block_id;
    move->dst = dst;
    move->src = src;
    move->source_lineno = source_lineno;
    move->next = 0;

    if (!*moves) {
	*moves = move;
	return move;
    }

    for (tail = *moves; tail->next; tail = tail->next)
	;
    tail->next = move;
    return move;
}

static HIRSSADestructionMove *
plan_ssa_destruction(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRSSADestructionMove *moves = 0;
    HIRSSABlock *block;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    HIRPhiArg *arg;

	    if (instr->kind != HIR_TAC_PHI)
		break;

	    for (arg = instr->phi_args; arg; arg = arg->next) {
		append_destruction_move(ctx, &moves, arg->block_id, block->id,
					instr->value, arg->value,
					instr->source_lineno);
	    }
	    if (instr == block->last)
		break;
	}
    }

    return moves;
}

static int
cfg_has_edge(HIRBasicBlock *from, HIRBasicBlock *to)
{
    int i;

    if (!from || !to)
	return 0;

    for (i = 0; i < from->num_successors; i++) {
	if (from->successors[i] == to)
	    return 1;
    }

    return 0;
}

static HIRBasicBlock *
cfg_split_block_for_edge(HIRCFG *cfg, HIRBasicBlock *pred,
			 HIRBasicBlock *target)
{
    int i;

    if (!cfg || !pred || !target)
	return 0;

    if (cfg_has_edge(pred, target))
	return pred;

    for (i = 0; i < pred->num_successors; i++) {
	HIRBasicBlock *candidate = pred->successors[i];

	if (candidate && candidate->num_successors == 1
	    && candidate->successors[0] == target)
	    return candidate;
    }

    return 0;
}

static void
ensure_ssa_blocks_for_cfg(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRBasicBlock *cfg_block;

    for (cfg_block = ssa->cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	HIRSSABlock *block;

	if (ssa_block_for_id(ssa, cfg_block->id))
	    continue;

	block = new_ssa_block_for_cfg(ctx, cfg_block);
	append_ssa_block(ssa, block);
	if (cfg_block->first) {
	    HIRSSAInstr *instr = new_ssa_instr(ctx, cfg_block->first);
	    emit_ssa_instr(ssa, block, instr);
	}
    }
}

static int
ssa_instr_is_terminator(HIRSSAInstr *instr)
{
    return instr
	&& (instr->kind == HIR_TAC_JUMP
	    || instr->kind == HIR_TAC_BRANCH_FALSE
	    || instr->kind == HIR_TAC_RETURN
	    || instr->kind == HIR_TAC_RETURN0);
}

static HIRSSAInstr *
ensure_parallel_copy(HIRContext *ctx, HIRSSAProgram *ssa, HIRSSABlock *block,
		     unsigned source_lineno)
{
    HIRSSAInstr *copy;
    HIRSSAInstr *prev = 0;
    HIRSSAInstr *last = block->last;
    HIRSSAInstr *curr;

    if (last && ssa_instr_is_terminator(last)) {
	for (curr = block->first; curr && curr != last; curr = curr->next)
	    prev = curr;
	if (prev && prev->kind == HIR_TAC_PARALLEL_COPY)
	    return prev;
    } else if (last && last->kind == HIR_TAC_PARALLEL_COPY) {
	return last;
    }

    copy = hir_alloc(ctx, sizeof(HIRSSAInstr));
    memset(copy, 0, sizeof(HIRSSAInstr));
    copy->kind = HIR_TAC_PARALLEL_COPY;
    copy->source_lineno = source_lineno;
    copy->bytecode_pc = NO_BYTECODE_PC;
    copy->value = 0;
    copy->src1 = 0;
    copy->src2 = 0;
    copy->src3 = 0;
    copy->label = 0;
    copy->local_id = -1;
    copy->op = HIR_OP_ADD;
    copy->num_stack_values = 0;
    copy->stack_values = 0;
    copy->stack_slots = 0;
    copy->num_local_values = 0;
    copy->local_values = 0;
    copy->literal.type = TYPE_NONE;
    copy->phi_args = 0;
    copy->copies = 0;
    copy->next = 0;

    if (last && ssa_instr_is_terminator(last)) {
	if (prev)
	    prev->next = copy;
	else
	    block->first = copy;
	copy->next = last;
    } else {
	emit_ssa_instr(ssa, block, copy);
	return copy;
    }

    ssa->num_instructions++;
    return copy;
}

static void
append_parallel_copy_pair(HIRContext *ctx, HIRSSAProgram *ssa,
			  HIRSSAInstr *instr, int dst, int src)
{
    HIRParallelCopy *copy = hir_alloc(ctx, sizeof(HIRParallelCopy));
    HIRParallelCopy *tail;

    copy->dst = dst;
    copy->src = src;
    copy->next = 0;

    if (!instr->copies) {
	instr->copies = copy;
    } else {
	for (tail = instr->copies; tail->next; tail = tail->next)
	    ;
	tail->next = copy;
    }

    ssa->num_values++;
}

static void
materialize_destruction_moves(HIRContext *ctx, HIRSSAProgram *ssa,
			      HIRSSADestructionMove *moves)
{
    HIRSSADestructionMove *move;

    hir_split_critical_edges(ctx, ssa->cfg);
    ensure_ssa_blocks_for_cfg(ctx, ssa);

    for (move = moves; move; move = move->next) {
	HIRBasicBlock *pred = cfg_block_for_id(ssa->cfg, move->pred_block_id);
	HIRBasicBlock *target = cfg_block_for_id(ssa->cfg, move->target_block_id);
	HIRBasicBlock *copy_cfg_block = cfg_split_block_for_edge(ssa->cfg,
								 pred, target);
	HIRSSABlock *copy_block;
	HIRSSAInstr *copy_instr;

	if (!copy_cfg_block) {
	    record_unsupported(ctx, "ssa-destroy: could not find copy edge");
	    continue;
	}

	copy_block = ssa_block_for_id(ssa, copy_cfg_block->id);
	if (!copy_block) {
	    record_unsupported(ctx, "ssa-destroy: missing copy block");
	    continue;
	}

	copy_instr = ensure_parallel_copy(ctx, ssa, copy_block,
					  move->source_lineno);
	append_parallel_copy_pair(ctx, ssa, copy_instr, move->dst, move->src);
    }
}

static void
remove_phi_nodes(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;

    for (block = ssa->blocks; block; block = block->next) {
	while (block->first && block->first->kind == HIR_TAC_PHI) {
	    HIRSSAInstr *phi = block->first;

	    block->first = phi->next;
	    if (block->last == phi)
		block->last = block->first;
	    ssa->num_instructions--;
	    ssa->num_values--;
	}
    }
}

int
hir_destroy_ssa(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRSSADestructionMove *moves;

    if (!ctx || !ssa)
	return 0;
    if (ssa->form == HIR_FORM_OUT_OF_SSA)
	return 1;
    if (ssa->form != HIR_FORM_SSA) {
	record_unsupported(ctx, "ssa-destroy: cannot destroy non-SSA form");
	return 0;
    }

    moves = plan_ssa_destruction(ctx, ssa);
    materialize_destruction_moves(ctx, ssa, moves);
    remove_phi_nodes(ssa);
    ssa->form = HIR_FORM_OUT_OF_SSA;

    return hir_verify_out_of_ssa(ctx, ssa);
}

static void
mark_out_ssa_def(int value, unsigned char *defined, int max_value)
{
    if (value > 0 && value <= max_value)
	defined[value] = 1;
}

static void
verify_out_ssa_use(HIRContext *ctx, int value, unsigned char *defined,
		   int max_value)
{
    if (value <= 0 || value > max_value || !defined[value])
	record_unsupported_fmt(ctx, "out-of-ssa: value %d used before definition", value);
}

int
hir_verify_out_of_ssa(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    unsigned char *defined;
    int max_value;
    int errors_before;
    int block_count = 0;
    int instruction_count = 0;
    int value_count = 0;
    int i;

    if (!ctx || !ssa)
	return 0;

    errors_before = ctx->error_count;
    if (ssa->form != HIR_FORM_OUT_OF_SSA)
	record_unsupported(ctx, "out-of-ssa: verifier requires out-of-SSA form");
    (void) hir_verify_cfg(ctx, ssa->cfg);

    max_value = ctx->next_temp - 1;
    defined = hir_alloc(ctx, (size_t) max_value + 1);
    for (i = 0; i <= max_value; i++)
	defined[i] = 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	block_count++;
	if (!block->first || !block->last)
	    record_unsupported_fmt(ctx, "out-of-ssa: block %d has no instructions", block->id);

	for (instr = block->first; instr; instr = instr->next) {
	    instruction_count++;
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_DEOPT:
		break;
	    case HIR_TAC_CONST:
	    case HIR_TAC_LOAD_ERROR:
	    case HIR_TAC_LOAD_LOCAL:
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BINARY:
	    case HIR_TAC_CALL:
	    case HIR_TAC_CALL_VERB:
	    case HIR_TAC_PUT_PROP:
	    case HIR_TAC_INDEX_SET:
	    case HIR_TAC_RANGE_REF:
	    case HIR_TAC_RANGE_SET:
		mark_out_ssa_def(instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_UNSUPPORTED:
		if (instr->value > 0) {
		    mark_out_ssa_def(instr->value, defined, max_value);
		    value_count++;
		}
		break;
	    case HIR_TAC_PARALLEL_COPY:
		{
		    HIRParallelCopy *copy;
		    for (copy = instr->copies; copy; copy = copy->next) {
			mark_out_ssa_def(copy->dst, defined, max_value);
			value_count++;
		    }
		}
		break;
	    case HIR_TAC_PHI:
		record_unsupported_fmt(ctx, "out-of-ssa: phi node in block %d", block->id);
		break;
	    case HIR_TAC_STORE_LOCAL:
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
	    case HIR_TAC_RETURN0:
		break;
	    }
	    if (instr == block->last)
		break;
	}
    }

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_STORE_LOCAL:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_CALL:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_UNARY:
		if (unary_op_has_operand(instr->op))
		    verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_BINARY:
	    case HIR_TAC_PUT_PROP:
	    case HIR_TAC_CALL_VERB:
	    case HIR_TAC_RANGE_REF:
	    case HIR_TAC_RANGE_SET:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		verify_out_ssa_use(ctx, instr->src2, defined, max_value);
		break;
	    case HIR_TAC_INDEX_SET:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		verify_out_ssa_use(ctx, instr->src2, defined, max_value);
		verify_out_ssa_use(ctx, instr->src3, defined, max_value);
		break;
	    case HIR_TAC_BRANCH_FALSE:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_RETURN:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_PARALLEL_COPY:
		{
		    HIRParallelCopy *copy;
		    for (copy = instr->copies; copy; copy = copy->next) {
			verify_out_ssa_use(ctx, copy->src, defined, max_value);
			if (copy->dst <= 0 || copy->dst > max_value)
			    record_unsupported_fmt(ctx,
						   "out-of-ssa: invalid copy destination %d in block %d", copy->dst, block->id);
		    }
		}
		break;
	    default:
		break;
	    }
	    if (instr == block->last)
		break;
	}
    }

    if (block_count != ssa->num_blocks)
	record_unsupported_fmt(ctx, "out-of-ssa: block count mismatch (got %d, expected %d)", block_count, ssa->num_blocks);
    if (instruction_count != ssa->num_instructions)
	record_unsupported_fmt(ctx, "out-of-ssa: instruction count mismatch (got %d, expected %d)", instruction_count, ssa->num_instructions);
    if (value_count != ssa->num_values)
	record_unsupported_fmt(ctx, "out-of-ssa: value count mismatch (got %d, expected %d)", value_count, ssa->num_values);
    if (cfg_critical_edge_count(ssa->cfg) != 0)
	record_unsupported(ctx, "out-of-ssa: CFG still has critical edges");

    return ctx->error_count == errors_before;
}

#ifdef HIR_TESTING
static int
resume_stack_is_safe(var_type *stack_types, unsigned stack_depth,
		     int call_operands)
{
    int outer_depth;
    int i;

    if (stack_depth < (unsigned) call_operands)
	return 0;
    outer_depth = stack_depth - call_operands;
    for (i = 0; i < outer_depth; i++)
	if (stack_types[i] == TYPE_CATCH || stack_types[i] == TYPE_FINALLY)
	    return 0;
    return 1;
}
#endif

static int
resume_stack_matches_point(ResumeStackSlot *stack_slots, unsigned stack_depth,
			   const ResumePoint *point, int call_operands)
{
    int i;

    if (!point || call_operands < 0
	|| stack_depth < (unsigned) call_operands
	|| point->stack_depth != stack_depth - call_operands
	|| (point->stack_depth && (!stack_slots || !point->stack_slots)))
	return 0;
    for (i = 0; i < (int) point->stack_depth; i++)
	if (stack_slots[i].kind != point->stack_slots[i].kind
	    || (stack_slots[i].kind != RSS_VALUE
		&& stack_slots[i].data != point->stack_slots[i].data))
	    return 0;
    return 1;
}

static int
jit_boundary_ticks_charged(HIRTacKind kind, HIROp op)
{
	return kind == HIR_TAC_UNARY || kind == HIR_TAC_BINARY
	    || kind == HIR_TAC_BRANCH_FALSE || kind == HIR_TAC_CALL_VERB
	    || kind == HIR_TAC_PUT_PROP || kind == HIR_TAC_RANGE_REF
	    || kind == HIR_TAC_RANGE_SET || kind == HIR_TAC_INDEX_SET
	    || (kind == HIR_TAC_DEOPT && op == HIR_OP_SCATTER);
}

#if defined(ENABLE_JIT) && !defined(HIR_TESTING)
static int
jit_resume_stack_is_safe(JITDeoptMap *map, int call_operands)
{
    int outer_depth;
    int i;

    if (map->stack_depth < (unsigned) call_operands)
	return 0;
    outer_depth = map->stack_depth - call_operands;
    for (i = 0; i < outer_depth; i++)
	if (map->stack_slots[i].kind == RSS_CATCH
	    || map->stack_slots[i].kind == RSS_FINALLY)
	    return 0;
    return 1;
}

static int
jit_op_is_supported(HIROp op)
{
    switch (op) {
    case HIR_OP_NEGATE:
    case HIR_OP_NOT:
    case HIR_OP_COMPLEMENT:
    case HIR_OP_ADD:
    case HIR_OP_SUB:
    case HIR_OP_MUL:
    case HIR_OP_DIV:
    case HIR_OP_MOD:
    case HIR_OP_EXP:
    case HIR_OP_BITOR:
    case HIR_OP_BITXOR:
    case HIR_OP_BITAND:
    case HIR_OP_SHL:
    case HIR_OP_SHR:
    case HIR_OP_LSHR:
    case HIR_OP_INDEX:
    case HIR_OP_MAKE_SINGLETON_LIST:
    case HIR_OP_CHECK_LIST_FOR_SPLICE:
    case HIR_OP_LIST_ADD_TAIL:
    case HIR_OP_LIST_APPEND:
    case HIR_OP_ABS:
    case HIR_OP_MIN:
    case HIR_OP_MAX:
    case HIR_OP_TOINT:
    case HIR_OP_TYPEOF:
    case HIR_OP_LENGTH:
    case HIR_OP_GET_PROP:
    case HIR_OP_EQ:
    case HIR_OP_NE:
    case HIR_OP_LT:
    case HIR_OP_LE:
    case HIR_OP_GT:
    case HIR_OP_GE:
    case HIR_OP_IN:
    case HIR_OP_TICKS_LEFT:
    case HIR_OP_SECONDS_LEFT:
    case HIR_OP_TIME:
    case HIR_OP_INDEX_BF:
    case HIR_OP_RINDEX_BF:
    case HIR_OP_VALID:
    case HIR_OP_PARENT:
	return 1;
    default:
	return 0;
    }
}

static const char *
tac_kind_name(HIRTacKind kind)
{
    switch (kind) {
    case HIR_TAC_TICK: return "tick";
    case HIR_TAC_DEOPT: return "deopt";
    case HIR_TAC_CONST: return "const";
    case HIR_TAC_LOAD_ERROR: return "load-error";
    case HIR_TAC_LOAD_LOCAL: return "load-local";
    case HIR_TAC_STORE_LOCAL: return "store-local";
    case HIR_TAC_UNARY: return "unary";
    case HIR_TAC_BINARY: return "binary";
    case HIR_TAC_CALL: return "call";
    case HIR_TAC_CALL_VERB: return "call-verb";
    case HIR_TAC_PUT_PROP: return "put-prop";
    case HIR_TAC_INDEX_SET: return "index-set";
    case HIR_TAC_RANGE_REF: return "range-ref";
    case HIR_TAC_RANGE_SET: return "range-set";
    case HIR_TAC_LABEL: return "label";
    case HIR_TAC_JUMP: return "jump";
    case HIR_TAC_BRANCH_FALSE: return "branch-false";
    case HIR_TAC_RETURN: return "return";
    case HIR_TAC_RETURN0: return "return0";
    case HIR_TAC_PHI: return "phi";
    case HIR_TAC_PARALLEL_COPY: return "parallel-copy";
    case HIR_TAC_UNSUPPORTED: return "unsupported";
    }
    return "unknown";
}

static int
jit_ssa_is_supported(HIRContext *ctx, HIRSSAProgram *ssa)
{
    HIRSSABlock *block;

    if (!ssa || ssa->form != HIR_FORM_OUT_OF_SSA) {
	record_unsupported(ctx, "ssa-support: program is not in out-of-ssa form");
	return 0;
    }

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_DEOPT:
	    case HIR_TAC_LOAD_ERROR:
	    case HIR_TAC_LOAD_LOCAL:
	    case HIR_TAC_CALL:
	    case HIR_TAC_CALL_VERB:
	    case HIR_TAC_PUT_PROP:
	    case HIR_TAC_INDEX_SET:
	    case HIR_TAC_RANGE_REF:
	    case HIR_TAC_RANGE_SET:
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
	    case HIR_TAC_RETURN0:
	    case HIR_TAC_CONST:
	    case HIR_TAC_PARALLEL_COPY:
		break;
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BINARY:
		if (!jit_op_is_supported(instr->op)) {
		    record_unsupported_fmt(ctx, "ssa-support: unsupported operation %d", (int) instr->op);
		    return 0;
		}
		break;
	    case HIR_TAC_STORE_LOCAL:
		record_unsupported(ctx, "ssa-support: store-local instruction in out-of-ssa");
		return 0;
	    case HIR_TAC_UNSUPPORTED:
		record_unsupported(ctx, "ssa-support: unsupported instruction kind");
		return 0;
	    case HIR_TAC_PHI:
		record_unsupported(ctx, "ssa-support: phi instruction in out-of-ssa");
		return 0;
	    }
	    if (instr == block->last)
		break;
	}
    }
    return 1;
}

static HIRSSAInstr *
ssa_definition_for_value(HIRSSAProgram *ssa, int value)
{
    HIRSSABlock *block;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->value == value && ssa_defines_value(instr))
		return instr;
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

static int
ssa_first_list_element(HIRSSAProgram *ssa, int value)
{
    HIRSSAInstr *def;

    while ((def = ssa_definition_for_value(ssa, value)) != 0) {
	if (def->kind == HIR_TAC_UNARY
	    && def->op == HIR_OP_MAKE_SINGLETON_LIST)
	    return def->src1;
	if (def->kind != HIR_TAC_BINARY
	    || def->op != HIR_OP_LIST_ADD_TAIL)
	    return 0;
	value = def->src1;
    }
    return 0;
}

static int
jit_extended_anchor_matches(Bytecodes *bc, unsigned pc, Extended_Opcode op)
{
    return pc + 1 < bc->size && bc->vector[pc] == OP_EXTENDED
	&& bc->vector[pc + 1] == op;
}

static int
jit_operation_anchor_matches(Bytecodes *bc, HIRSSAInstr *instr)
{
    Byte op = bc->vector[instr->bytecode_pc];

    if (instr->kind == HIR_TAC_UNARY) {
	if (instr->op == HIR_OP_NEGATE)
	    return op == OP_UNARY_MINUS;
	if (instr->op == HIR_OP_NOT)
	    return op == OP_NOT;
	if (instr->op == HIR_OP_MAKE_SINGLETON_LIST)
	    return op == OP_MAKE_SINGLETON_LIST;
	if (instr->op == HIR_OP_CHECK_LIST_FOR_SPLICE)
	    return op == OP_CHECK_LIST_FOR_SPLICE;
	if (instr->op == HIR_OP_LENGTH)
	    return (instr->bytecode_pc + 1 < bc->size
		    && bc->vector[instr->bytecode_pc] == OP_BI_FUNC_CALL
		    && bc->vector[instr->bytecode_pc + 1] == instr->func)
		|| op == OP_FOR_LIST
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_SCATTER)
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_LENGTH);
	if (instr->op == HIR_OP_ABS || instr->op == HIR_OP_TOINT
	    || instr->op == HIR_OP_TYPEOF || instr->op == HIR_OP_TICKS_LEFT
	    || instr->op == HIR_OP_SECONDS_LEFT || instr->op == HIR_OP_TIME
	    || instr->op == HIR_OP_VALID || instr->op == HIR_OP_PARENT)
	    return instr->bytecode_pc + 1 < bc->size
		&& bc->vector[instr->bytecode_pc] == OP_BI_FUNC_CALL
		&& bc->vector[instr->bytecode_pc + 1] == instr->func;
	return jit_extended_anchor_matches(bc, instr->bytecode_pc,
					   EOP_COMPLEMENT);
    }
    if (instr->kind == HIR_TAC_BINARY) {
	switch (instr->op) {
	case HIR_OP_ADD:
	    return op == OP_ADD || op == OP_FOR_RANGE || op == OP_FOR_LIST;
	case HIR_OP_SUB: return op == OP_MINUS;
	case HIR_OP_MUL: return op == OP_MULT;
	case HIR_OP_DIV: return op == OP_DIV;
	case HIR_OP_MOD: return op == OP_MOD;
	case HIR_OP_EXP:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_EXP);
	case HIR_OP_INDEX:
	    return op == OP_REF
		|| op == OP_PUSH_REF
		|| op == OP_FOR_LIST
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_SCATTER);
	case HIR_OP_LIST_ADD_TAIL: return op == OP_LIST_ADD_TAIL;
	case HIR_OP_LIST_APPEND: return op == OP_LIST_APPEND;
	case HIR_OP_GET_PROP:
	    return op == OP_GET_PROP || op == OP_PUSH_GET_PROP;
	case HIR_OP_MIN:
	case HIR_OP_MAX:
	case HIR_OP_INDEX_BF:
	case HIR_OP_RINDEX_BF:
	    return instr->bytecode_pc + 1 < bc->size
		&& bc->vector[instr->bytecode_pc] == OP_BI_FUNC_CALL
		&& bc->vector[instr->bytecode_pc + 1] == instr->func;
	case HIR_OP_EQ:
	    return op == OP_EQ
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_SCATTER);
	case HIR_OP_NE: return op == OP_NE;
	case HIR_OP_LT:
	    return op == OP_LT || op == OP_FOR_RANGE || op == OP_FOR_LIST
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_SCATTER);
	case HIR_OP_LE:
	    return op == OP_LE || op == OP_FOR_RANGE || op == OP_FOR_LIST
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_SCATTER);
	case HIR_OP_GT: return op == OP_GT;
	case HIR_OP_GE:
	    return op == OP_GE
		|| jit_extended_anchor_matches(bc, instr->bytecode_pc,
					       EOP_SCATTER);
	case HIR_OP_IN: return op == OP_IN;
	case HIR_OP_BITOR:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_BITOR);
	case HIR_OP_BITXOR:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_BITXOR);
	case HIR_OP_BITAND:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_BITAND);
	case HIR_OP_SHL:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_SHL);
	case HIR_OP_SHR:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_SHR);
	case HIR_OP_LSHR:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_LSHR);
	default: return 0;
	}
    }
    return 1;
}

static int
jit_ssa_anchors_are_valid(HIRContext *ctx, HIRSSAProgram *ssa, Program *bytecode_program)
{
    HIRSSABlock *block;
    Bytecodes *bc;

    if (!bytecode_program || !bytecode_program->main_vector.vector) {
	record_unsupported(ctx, "anchor: missing bytecode program vector");
	return 0;
    }
    bc = &bytecode_program->main_vector;
    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_DEOPT:
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BINARY:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
	    case HIR_TAC_RETURN0:
		if (instr->bytecode_pc == NO_BYTECODE_PC) {
		    record_unsupported_fmt(ctx, "anchor: %s missing bytecode pc", tac_kind_name(instr->kind));
		    return 0;
		}
		if (instr->bytecode_pc >= bc->size) {
		    record_unsupported_fmt(ctx, "anchor: pc %u out of bounds (size %u)", instr->bytecode_pc, bc->size);
		    return 0;
		}
		if ((instr->kind == HIR_TAC_UNARY || instr->kind == HIR_TAC_BINARY)
		    && !jit_operation_anchor_matches(bc, instr)) {
		    record_unsupported_fmt(ctx, "anchor: pc %u op %d mismatch (got opcode %u)",
					   instr->bytecode_pc, (int) instr->op, (unsigned) bc->vector[instr->bytecode_pc]);
		    return 0;
		}
		if (instr->kind == HIR_TAC_RETURN
		    && bc->vector[instr->bytecode_pc] != OP_RETURN) {
		    record_unsupported_fmt(ctx, "anchor: pc %u return expected OP_RETURN (got opcode %u)",
					   instr->bytecode_pc, (unsigned) bc->vector[instr->bytecode_pc]);
		    return 0;
		}
		if (instr->kind == HIR_TAC_RETURN0
		    && bc->vector[instr->bytecode_pc] != OP_RETURN0) {
		    record_unsupported_fmt(ctx, "anchor: pc %u return0 expected OP_RETURN0 (got opcode %u)",
					   instr->bytecode_pc, (unsigned) bc->vector[instr->bytecode_pc]);
		    return 0;
		}
		if (instr->kind == HIR_TAC_BRANCH_FALSE
		    && bc->vector[instr->bytecode_pc] != OP_AND
		    && bc->vector[instr->bytecode_pc] != OP_OR
		    && bc->vector[instr->bytecode_pc] != OP_IF
		    && bc->vector[instr->bytecode_pc] != OP_IF_QUES
		    && bc->vector[instr->bytecode_pc] != OP_EIF
		    && bc->vector[instr->bytecode_pc] != OP_WHILE
		    && bc->vector[instr->bytecode_pc] != OP_FOR_RANGE
		    && bc->vector[instr->bytecode_pc] != OP_FOR_LIST
		    && !jit_extended_anchor_matches(bc, instr->bytecode_pc,
						    EOP_SCATTER)
		    && !jit_extended_anchor_matches(bc, instr->bytecode_pc,
						    EOP_WHILE_ID)) {
		    record_unsupported_fmt(ctx, "anchor: pc %u branch_false opcode mismatch (got opcode %u)",
					   instr->bytecode_pc, (unsigned) bc->vector[instr->bytecode_pc]);
		    return 0;
		}
		break;
	    case HIR_TAC_CONST:
	    case HIR_TAC_LOAD_ERROR:
	    case HIR_TAC_LOAD_LOCAL:
		if (instr->bytecode_pc != NO_BYTECODE_PC
		    && instr->bytecode_pc >= bc->size) {
		    record_unsupported_fmt(ctx, "anchor: pc %u out of bounds (size %u)", instr->bytecode_pc, bc->size);
		    return 0;
		}
		break;
	    case HIR_TAC_JUMP:
		if (instr->bytecode_pc != NO_BYTECODE_PC
		    && (instr->bytecode_pc >= bc->size
			|| (!jit_extended_anchor_matches(bc,
						 instr->bytecode_pc, EOP_EXIT)
			    && !jit_extended_anchor_matches(bc,
						    instr->bytecode_pc,
						    EOP_EXIT_ID)))) {
		    record_unsupported_fmt(ctx, "anchor: pc %u jump expected EOP_EXIT/EOP_EXIT_ID (got opcode %u)",
					   instr->bytecode_pc, (unsigned) bc->vector[instr->bytecode_pc]);
		    return 0;
		}
		break;
	    case HIR_TAC_CALL:
		if (instr->bytecode_pc == NO_BYTECODE_PC || instr->bytecode_pc >= bc->size
		    || bc->vector[instr->bytecode_pc] != OP_BI_FUNC_CALL) {
		    record_unsupported_fmt(ctx, "anchor: pc %u call expected OP_BI_FUNC_CALL (got opcode %u)",
					   instr->bytecode_pc, instr->bytecode_pc < bc->size ? (unsigned) bc->vector[instr->bytecode_pc] : 0);
		    return 0;
		}
		break;
	    case HIR_TAC_CALL_VERB:
		if (instr->bytecode_pc == NO_BYTECODE_PC || instr->bytecode_pc >= bc->size
		    || bc->vector[instr->bytecode_pc] != OP_CALL_VERB) {
		    record_unsupported_fmt(ctx, "anchor: pc %u call_verb expected OP_CALL_VERB (got opcode %u)",
					   instr->bytecode_pc, instr->bytecode_pc < bc->size ? (unsigned) bc->vector[instr->bytecode_pc] : 0);
		    return 0;
		}
		break;
	    case HIR_TAC_PUT_PROP:
		if (instr->bytecode_pc == NO_BYTECODE_PC || instr->bytecode_pc >= bc->size
		    || bc->vector[instr->bytecode_pc] != OP_PUT_PROP) {
		    record_unsupported_fmt(ctx, "anchor: pc %u put_prop expected OP_PUT_PROP (got opcode %u)",
					   instr->bytecode_pc, instr->bytecode_pc < bc->size ? (unsigned) bc->vector[instr->bytecode_pc] : 0);
		    return 0;
		}
		break;
	    case HIR_TAC_INDEX_SET:
		if (instr->bytecode_pc == NO_BYTECODE_PC
		    || instr->bytecode_pc + 1 >= bc->size
		    || bc->vector[instr->bytecode_pc] != OP_PUT_TEMP
		    || bc->vector[instr->bytecode_pc + 1] != OP_INDEXSET) {
		    record_unsupported_fmt(ctx, "anchor: pc %u index_set expected OP_PUT_TEMP/OP_INDEXSET (got opcode %u)",
					   instr->bytecode_pc,
					   instr->bytecode_pc < bc->size
					   ? (unsigned) bc->vector[instr->bytecode_pc] : 0);
		    return 0;
		}
		break;
	    case HIR_TAC_RANGE_REF:
		if (instr->bytecode_pc == NO_BYTECODE_PC || instr->bytecode_pc >= bc->size
		    || bc->vector[instr->bytecode_pc] != OP_RANGE_REF) {
		    record_unsupported_fmt(ctx, "anchor: pc %u range_ref expected OP_RANGE_REF (got opcode %u)",
					   instr->bytecode_pc, instr->bytecode_pc < bc->size ? (unsigned) bc->vector[instr->bytecode_pc] : 0);
		    return 0;
		}
		break;
	    case HIR_TAC_RANGE_SET:
		if (instr->bytecode_pc == NO_BYTECODE_PC || instr->bytecode_pc >= bc->size
		    || (bc->vector[instr->bytecode_pc] != OP_PUT_TEMP
			&& !jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_RANGESET))) {
		    record_unsupported_fmt(ctx, "anchor: pc %u range_set expected OP_PUT_TEMP/EOP_RANGESET (got opcode %u)",
					   instr->bytecode_pc, instr->bytecode_pc < bc->size ? (unsigned) bc->vector[instr->bytecode_pc] : 0);
		    return 0;
		}
		break;
	    case HIR_TAC_LABEL:
	    case HIR_TAC_PARALLEL_COPY:
		break;
	    case HIR_TAC_STORE_LOCAL:
	    case HIR_TAC_UNSUPPORTED:
	    case HIR_TAC_PHI:
		record_unsupported_fmt(ctx, "anchor: unexpected instruction %s", tac_kind_name(instr->kind));
		return 0;
	    }
	    if (instr == block->last)
		break;
	}
    }
    return 1;
}

typedef struct {
    JITTypeMask operands[JIT_MAX_GUARD_OPERANDS];
    int tagged_dispatch;
} JITConsumerContract;

static JITConsumerContract
jit_consumer_contract(HIRSSAInstr *instr)
{
    JITConsumerContract contract;
    JITTypeMask numeric = JIT_TYPE_MASK(TYPE_INT) | JIT_TYPE_MASK(TYPE_FLOAT);

    memset(&contract, 0, sizeof(contract));
    if (instr->kind == HIR_TAC_UNARY) {
	switch (instr->op) {
	case HIR_OP_COMPLEMENT:
	case HIR_OP_TOINT:
	    contract.operands[0] = JIT_TYPE_MASK(TYPE_INT);
	    break;
	case HIR_OP_NEGATE:
	case HIR_OP_ABS:
	    contract.operands[0] = numeric;
	    contract.tagged_dispatch = instr->op == HIR_OP_ABS;
	    break;
	case HIR_OP_LENGTH:
	    contract.operands[0] = JIT_TYPE_MASK(TYPE_STR)
		| JIT_TYPE_MASK(TYPE_LIST);
	    contract.tagged_dispatch = 1;
	    break;
	case HIR_OP_CHECK_LIST_FOR_SPLICE:
	    contract.operands[0] = JIT_TYPE_MASK(TYPE_LIST);
	    contract.tagged_dispatch = 1;
	    break;
	case HIR_OP_PARENT:
	case HIR_OP_VALID:
	    contract.operands[0] = JIT_TYPE_MASK(TYPE_OBJ);
	    contract.tagged_dispatch = 1;
	    break;
	case HIR_OP_NOT:
	case HIR_OP_TYPEOF:
	case HIR_OP_MAKE_SINGLETON_LIST:
	    contract.tagged_dispatch = 1;
	    break;
	default:
	    break;
	}
	return contract;
    }
    if (instr->kind != HIR_TAC_BINARY)
	return contract;
    switch (instr->op) {
    case HIR_OP_ADD:
    case HIR_OP_SUB:
    case HIR_OP_MUL:
    case HIR_OP_DIV:
    case HIR_OP_MOD:
    case HIR_OP_EXP:
	contract.operands[0] = binary_operand_type_mask(instr->op, 0, 0,
						       TYPE_NONE);
	contract.operands[1] = binary_operand_type_mask(instr->op, 1, 0,
						       TYPE_NONE);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_BITOR:
    case HIR_OP_BITXOR:
    case HIR_OP_BITAND:
    case HIR_OP_SHL:
    case HIR_OP_SHR:
    case HIR_OP_LSHR:
	contract.operands[0] = contract.operands[1] = JIT_TYPE_MASK(TYPE_INT);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_INDEX:
	contract.operands[0] = JIT_TYPE_MASK(TYPE_LIST)
	    | JIT_TYPE_MASK(TYPE_STR);
	contract.operands[1] = JIT_TYPE_MASK(TYPE_INT);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_INDEX_BF:
    case HIR_OP_RINDEX_BF:
	contract.operands[0] = contract.operands[1] = JIT_TYPE_MASK(TYPE_STR);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_GET_PROP:
	contract.operands[0] = JIT_TYPE_MASK(TYPE_OBJ) | JIT_TYPE_MASK(TYPE_WAIF);
	contract.operands[1] = JIT_TYPE_MASK(TYPE_STR);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_SUBLIST_FROM:
	contract.operands[0] = JIT_TYPE_MASK(TYPE_LIST);
	contract.operands[1] = JIT_TYPE_MASK(TYPE_INT);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_LIST_APPEND:
	contract.operands[0] = contract.operands[1] = JIT_TYPE_MASK(TYPE_LIST);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_LIST_ADD_TAIL:
	contract.operands[0] = JIT_TYPE_MASK(TYPE_LIST);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_IN:
	contract.operands[1] = JIT_TYPE_MASK(TYPE_LIST);
	contract.tagged_dispatch = 1;
	break;
    case HIR_OP_EQ:
    case HIR_OP_NE:
    case HIR_OP_LT:
    case HIR_OP_LE:
    case HIR_OP_GT:
    case HIR_OP_GE:
	contract.tagged_dispatch = 1;
	break;
    default:
	break;
    }
    return contract;
}

static int
jit_tagged_consumer_is_supported(HIRSSAInstr *instr)
{
    if (instr->kind == HIR_TAC_BRANCH_FALSE || instr->kind == HIR_TAC_RETURN
	|| instr->kind == HIR_TAC_CALL_VERB || instr->kind == HIR_TAC_CALL
	|| instr->kind == HIR_TAC_RANGE_REF)
	return 1;
    return jit_consumer_contract(instr).tagged_dispatch;
}

static int
jit_guard_contract(HIRSSAInstr *instr, var_type *value_types,
		   unsigned char *value_is_tagged, int num_values,
		   int *values, int *locals, JITTypeMask *expected)
{
    JITConsumerContract contract;

    values[0] = values[1] = 0;
    locals[0] = locals[1] = -1;
    expected[0] = expected[1] = 0;
    if (instr->kind == HIR_TAC_LOAD_LOCAL && instr->value > 0
	&& instr->value < num_values && !value_is_tagged[instr->value]
	&& value_types[instr->value] != TYPE_ANY) {
	values[0] = instr->value;
	locals[0] = instr->local_id;
	expected[0] = JIT_TYPE_MASK(value_types[instr->value]);
	return 1;
    }
    contract = jit_consumer_contract(instr);
    values[0] = instr->src1;
    values[1] = instr->src2;
    expected[0] = contract.operands[0];
    expected[1] = contract.operands[1];
    if (instr->kind == HIR_TAC_BINARY) {
	int left_known = instr->src1 > 0 && instr->src1 < num_values
	    && !value_is_tagged[instr->src1]
	    && value_types[instr->src1] != TYPE_ANY
	    && value_types[instr->src1] != TYPE_NONE;
	int right_known = instr->src2 > 0 && instr->src2 < num_values
	    && !value_is_tagged[instr->src2]
	    && value_types[instr->src2] != TYPE_ANY
	    && value_types[instr->src2] != TYPE_NONE;
	JITTypeMask left = binary_operand_type_mask(instr->op, 0, right_known,
						    right_known
						    ? value_types[instr->src2]
						    : TYPE_NONE);
	JITTypeMask right = binary_operand_type_mask(instr->op, 1, left_known,
						     left_known
						     ? value_types[instr->src1]
						     : TYPE_NONE);

	if (left)
	    expected[0] = left;
	if (right)
	    expected[1] = right;
    }
    return expected[0] != 0 || expected[1] != 0;
}

static int
jit_add_deopt_map(JITProgram *program, HIRSSAInstr *instr,
		  Bytecodes *bytecodes, var_type *value_types,
		  unsigned char *value_is_tagged)
{
    JITDeoptMap *map;
    int i;

    if (instr->bytecode_pc == NO_BYTECODE_PC)
	return 0;
    if (instr->num_stack_values < 0
	|| (unsigned) instr->num_stack_values > bytecodes->max_stack
	|| instr->num_local_values != program->num_vars)
	return -1;
    for (i = 0; i < instr->num_stack_values; i++)
	if (instr->stack_values[i] <= 0
	    || instr->stack_values[i] >= program->num_values)
	    return -1;
    for (i = 0; i < instr->num_local_values; i++)
	if (instr->local_values[i] < 0
	    || instr->local_values[i] >= program->num_values)
	    return -1;

    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap)
				    * (program->num_deopt_maps + 1), M_PROGRAM);
    map = &program->deopt_maps[program->num_deopt_maps];
    memset(map, 0, sizeof(JITDeoptMap));
    map->resume_key = instr->resume_key;
    map->bytecode_pc = instr->bytecode_pc;
    map->error_pc = instr->bytecode_pc;
    map->source_lineno = instr->source_lineno;
    map->stack_depth = instr->num_stack_values;
    map->ticks_charged = jit_boundary_ticks_charged(instr->kind, instr->op);
    map->num_locals = instr->num_local_values;
    map->builtin_func = -1;
    map->builtin_args = -1;
    map->operation = -1;
    map->guard_local[0] = map->guard_local[1] = -1;
    (void) jit_guard_contract(instr, value_types, value_is_tagged,
			      program->num_values, map->guard_value,
			      map->guard_local, map->guard_expected);
    if (instr->kind == HIR_TAC_UNARY || instr->kind == HIR_TAC_BINARY
	|| instr->kind == HIR_TAC_DEOPT)
	map->operation = instr->op;
    if (instr->kind == HIR_TAC_UNARY && instr->func < FUNC_NOT_FOUND) {
	map->builtin_func = instr->func;
	map->builtin_args = instr->src1 ? 1 : 0;
    } else if (instr->kind == HIR_TAC_BINARY
	       && instr->func < FUNC_NOT_FOUND) {
	map->builtin_func = instr->func;
	map->builtin_args = 2;
    }

    switch (instr->kind) {
    case HIR_TAC_CALL:
	map->reason = JIT_DEOPT_BUILTIN_CALL;
	map->builtin_func = instr->func;
	break;
    case HIR_TAC_CALL_VERB:
	map->reason = JIT_DEOPT_VERB_CALL;
	break;
    case HIR_TAC_PUT_PROP:
	map->reason = JIT_DEOPT_PROPERTY_WRITE;
	break;
    case HIR_TAC_INDEX_SET:
	map->reason = JIT_DEOPT_UNSUPPORTED_OP;
	break;
    case HIR_TAC_RANGE_REF:
    case HIR_TAC_RANGE_SET:
	map->reason = JIT_DEOPT_RANGE_OP;
	break;
    case HIR_TAC_BRANCH_FALSE:
	map->reason = JIT_DEOPT_BRANCH_TYPE;
	break;
    case HIR_TAC_BINARY:
	if (instr->op == HIR_OP_GET_PROP)
	    map->reason = JIT_DEOPT_PROPERTY_READ;
	else
	    map->reason = JIT_DEOPT_ARITHMETIC_TYPE;
	break;
    case HIR_TAC_UNARY:
	if (instr->op == HIR_OP_MAKE_SINGLETON_LIST
	    || instr->op == HIR_OP_CHECK_LIST_FOR_SPLICE)
	    map->reason = JIT_DEOPT_UNSUPPORTED_OP;
	else
	    map->reason = JIT_DEOPT_ARITHMETIC_TYPE;
	break;
    case HIR_TAC_LOAD_LOCAL:
    case HIR_TAC_STORE_LOCAL:
	map->reason = JIT_DEOPT_TYPE_GUARD;
	break;
    default:
	map->reason = JIT_DEOPT_UNSUPPORTED_OP;
	break;
    }
    for (i = 0; i < map->num_locals; i++)
	if (instr->local_values[i] > 0)
	    map->num_local_values++;
    if (map->num_local_values) {
	int entry = 0;

	map->local_values = mymalloc(sizeof(JITLocalValue)
				     * map->num_local_values, M_PROGRAM);
	for (i = 0; i < map->num_locals; i++) {
	    int value = instr->local_values[i];

	    if (value <= 0)
		continue;
	    map->local_values[entry].slot = i;
	    map->local_values[entry].value = value;
	    entry++;
	}
    }
    if (map->stack_depth) {
	map->stack_values = mymalloc(sizeof(int) * map->stack_depth, M_PROGRAM);
	map->stack_slots = mymalloc(sizeof(ResumeStackSlot) * map->stack_depth,
				   M_PROGRAM);
	memcpy(map->stack_values, instr->stack_values,
	       sizeof(int) * map->stack_depth);
	memcpy(map->stack_slots, instr->stack_slots,
	       sizeof(ResumeStackSlot) * map->stack_depth);
    }
    return program->num_deopt_maps++;
}

static int
jit_instr_defines_value(JITInstruction *instr)
{
    return instr->kind == HIR_TAC_CONST || instr->kind == HIR_TAC_LOAD_LOCAL
	|| instr->kind == HIR_TAC_LOAD_ERROR
	|| instr->kind == HIR_TAC_UNARY || instr->kind == HIR_TAC_BINARY
	|| instr->kind == HIR_TAC_CALL || instr->kind == HIR_TAC_CALL_VERB
	|| instr->kind == HIR_TAC_PUT_PROP || instr->kind == HIR_TAC_INDEX_SET
	|| instr->kind == HIR_TAC_RANGE_REF
	|| instr->kind == HIR_TAC_RANGE_SET || instr->kind == HIR_TAC_UNSUPPORTED;
}

static int
jit_instr_can_materialize(JITInstruction *instr)
{
    return hir_kind_can_materialize(instr->kind);
}

static int
jit_deopt_maps_are_valid(HIRContext *ctx, JITProgram *program,
			 Program *bytecode_program)
{
	JITBlock *block;
	unsigned char *seen;
	int i;

	if (!program || program->num_deopt_maps <= 0) {
		record_unsupported(ctx, "deopt-map: missing canonical entry map");
		return 0;
	}
	seen = mymalloc(program->num_deopt_maps, M_PROGRAM);
	memset(seen, 0, program->num_deopt_maps);
	seen[0] = 1;
	for (block = program->blocks; block; block = block->next) {
		JITInstruction *instr;

		for (instr = block->first; instr; instr = instr->next) {
			JITDeoptMap *map;
			const ResumePoint *point;
			int operands;

			if (instr->deopt_map == 0)
				goto next_instruction;
			if (instr->deopt_map < 0
			    || instr->deopt_map >= program->num_deopt_maps) {
				record_unsupported_fmt(ctx,
				    "deopt-map: invalid map %d at pc %u",
				    instr->deopt_map, instr->bytecode_pc);
				goto invalid;
			}
			map = &program->deopt_maps[instr->deopt_map];
			if (seen[instr->deopt_map]) {
				record_unsupported_fmt(ctx,
				    "deopt-map: map %d is shared by multiple boundaries",
				    instr->deopt_map);
				goto invalid;
			}
			seen[instr->deopt_map] = 1;
			if (instr->bytecode_pc == NO_BYTECODE_PC
			    || map->bytecode_pc != instr->bytecode_pc
			    || map->bytecode_pc >= bytecode_program->main_vector.size) {
				record_unsupported_fmt(ctx,
				    "deopt-map: map %d has invalid pc %u for boundary pc %u",
				    instr->deopt_map, map->bytecode_pc,
				    instr->bytecode_pc);
				goto invalid;
			}
			if (map->num_locals != program->num_vars
			    || map->stack_depth > bytecode_program->main_vector.max_stack
			    || map->local_base < 0
			    || map->local_base > instr->deopt_map
			    || map->num_local_values < 0
			    || map->num_local_values > map->num_locals
			    || (map->num_local_values && !map->local_values)
			    || (map->stack_depth && (!map->stack_values
					      || !map->stack_slots))) {
				record_unsupported_fmt(ctx,
				    "deopt-map: map %d has incomplete frame at pc %u",
				    instr->deopt_map, map->bytecode_pc);
				goto invalid;
			}
			if (map->local_base > 0
			    && program->deopt_maps[map->local_base - 1].num_locals
			       != map->num_locals) {
				record_unsupported_fmt(ctx,
				    "deopt-map: map %d has incompatible local base %d",
				    instr->deopt_map, map->local_base - 1);
				goto invalid;
			}
			for (i = 0; i < map->num_local_values; i++)
				if (map->local_values[i].slot < 0
				    || map->local_values[i].slot >= map->num_locals
				    || (i > 0 && map->local_values[i].slot
					<= map->local_values[i - 1].slot)
				    || map->local_values[i].value < 0
				    || map->local_values[i].value >= program->num_values) {
					record_unsupported_fmt(ctx,
					    "deopt-map: map %d local %d has invalid value %d",
					    instr->deopt_map, i,
					    map->local_values[i].value);
					goto invalid;
				}
			for (i = 0; i < map->num_locals; i++) {
				int value = jit_deopt_map_local_value(program, map, i);

				if (value < 0 || value >= program->num_values) {
					record_unsupported_fmt(ctx,
					    "deopt-map: map %d resolves local %d to invalid value %d",
					    instr->deopt_map, i, value);
					goto invalid;
				}
			}
			for (i = 0; i < (int) map->stack_depth; i++)
				if (map->stack_slots[i].kind > RSS_FINALLY
				    || map->stack_values[i] <= 0
				    || map->stack_values[i] >= program->num_values) {
					record_unsupported_fmt(ctx,
					    "deopt-map: map %d stack slot %d has invalid value %d",
					    instr->deopt_map, i, map->stack_values[i]);
					goto invalid;
				}
			if (instr->kind != HIR_TAC_CALL
			    && instr->kind != HIR_TAC_CALL_VERB)
				goto next_instruction;
			if (!resume_key_is_valid(map->resume_key))
				goto next_instruction;
			point = resume_point_for_key(bytecode_program, map->resume_key);
			if (!point || point->vector != MAIN_VECTOR
			    || point->error_pc != map->bytecode_pc) {
				record_unsupported_fmt(ctx,
				    "deopt-map: map %d has mismatched resume key at pc %u (resume pc %u error pc %u)",
				    instr->deopt_map, map->bytecode_pc,
				    point ? point->pc : NO_BYTECODE_PC,
				    point ? point->error_pc : NO_BYTECODE_PC);
				goto invalid;
			}
			operands = instr->kind == HIR_TAC_CALL_VERB ? 3
			    : instr->kind == HIR_TAC_CALL ? 1 : -1;
			if (!resume_stack_matches_point(map->stack_slots,
						map->stack_depth, point, operands)) {
				record_unsupported_fmt(ctx,
				    "deopt-map: map %d call at line %u has stack depth %u, expected resume depth %u plus %d operands",
				    instr->deopt_map, instr->source_lineno,
				    map->stack_depth, point->stack_depth, operands);
				goto invalid;
			}
next_instruction:
			if (instr == block->last)
				break;
		}
	}
	for (i = 1; i < program->num_deopt_maps; i++)
		if (!seen[i]) {
			record_unsupported_fmt(ctx,
			    "deopt-map: map %d has no owning boundary", i);
			goto invalid;
		}
	myfree(seen, M_PROGRAM);
	return 1;

invalid:
	myfree(seen, M_PROGRAM);
	return 0;
}

#define JIT_LOCAL_BASE_WINDOW 32
#define JIT_LOCAL_BASE_DEPTH 8

static void
jit_coalesce_deopt_locals(JITProgram *program)
{
    unsigned char *depth;
    int map_id;

    if (!program || program->num_deopt_maps <= 1 || program->num_vars <= 0)
	return;
    depth = mymalloc(program->num_deopt_maps, M_PROGRAM);
    memset(depth, 0, program->num_deopt_maps);
    for (map_id = 1; map_id < program->num_deopt_maps; map_id++) {
	JITDeoptMap *map = &program->deopt_maps[map_id];
	int first = map_id > JIT_LOCAL_BASE_WINDOW
	    ? map_id - JIT_LOCAL_BASE_WINDOW : 0;
	int best = -1;
	int best_count = map->num_local_values;
	int candidate;

	for (candidate = map_id - 1; candidate >= first; candidate--) {
	    JITDeoptMap *base = &program->deopt_maps[candidate];
	    int count = 0;
	    int slot;

	    if (depth[candidate] >= JIT_LOCAL_BASE_DEPTH
		|| base->num_locals != map->num_locals)
		continue;
	    for (slot = 0; slot < map->num_locals; slot++) {
		int value = jit_deopt_map_local_value(program, map, slot);
		int base_value = jit_deopt_map_local_value(program, base, slot);

		if (value != base_value)
		    count++;
	    }
	    if (count < best_count) {
		best = candidate;
		best_count = count;
	    }
	}
	if (best >= 0) {
	    JITDeoptMap *base = &program->deopt_maps[best];
	    JITLocalValue *values = best_count
		? mymalloc(sizeof(JITLocalValue) * best_count, M_PROGRAM) : 0;
	    int entry = 0;
	    int slot;

	    for (slot = 0; slot < map->num_locals; slot++) {
		int value = jit_deopt_map_local_value(program, map, slot);
		int base_value = jit_deopt_map_local_value(program, base, slot);

		if (value == base_value)
		    continue;
		values[entry].slot = slot;
		values[entry].value = value;
		entry++;
	    }
	    if (map->local_values)
		myfree(map->local_values, M_PROGRAM);
	    map->local_values = values;
	    map->num_local_values = best_count;
	    map->local_base = best + 1;
	    depth[map_id] = depth[best] + 1;
	}
    }
    myfree(depth, M_PROGRAM);
}

static void
jit_build_tag_slots(JITProgram *program)
{
    int value;

    if (!program || program->num_values <= 0)
	return;
    program->value_tag_slots = mymalloc(sizeof(int) * program->num_values,
					M_PROGRAM);
    for (value = 0; value < program->num_values; value++) {
	program->value_tag_slots[value] = -1;
	if (program->value_is_tagged[value])
	    program->value_tag_slots[value] = program->num_tag_slots++;
    }
}

static void
jit_build_deopt_tag_values(JITProgram *program)
{
    unsigned char *seen;
    int map_id;

    if (!program || program->num_values <= 0)
	return;
    seen = mymalloc(program->num_values, M_PROGRAM);
    for (map_id = 0; map_id < program->num_deopt_maps; map_id++) {
	JITDeoptMap *map = &program->deopt_maps[map_id];
	int count = 0;
	int slot;

	memset(seen, 0, program->num_values);
	for (slot = 0; slot < map->num_locals; slot++) {
	    int value = jit_deopt_map_local_value(program, map, slot);

	    if (value > 0 && value < program->num_values
		&& program->value_is_tagged[value] && !seen[value]) {
		seen[value] = 1;
		count++;
	    }
	}
	for (slot = 0; slot < (int) map->stack_depth; slot++) {
	    int value;

	    if (map->stack_slots && map->stack_slots[slot].kind != RSS_VALUE)
		continue;
	    value = map->stack_values[slot];
	    if (value > 0 && value < program->num_values
		&& program->value_is_tagged[value] && !seen[value]) {
		seen[value] = 1;
		count++;
	    }
	}
	map->num_tagged_values = count;
	map->tagged_values = count
	    ? mymalloc(sizeof(int) * count, M_PROGRAM) : 0;
	count = 0;
	for (slot = 1; slot < program->num_values; slot++)
	    if (seen[slot])
		map->tagged_values[count++] = slot;
    }
    myfree(seen, M_PROGRAM);
}

static void
jit_instr_liveness(JITProgram *program, JITInstruction *instr,
		   unsigned char *uses, unsigned char *defs)
{
    JITCopy *copy;
    JITDeoptMap *map;
    int i;

    if (jit_instr_defines_value(instr) && instr->value > 0
	&& instr->value < program->num_values)
	defs[instr->value] = 1;
    if (instr->kind == HIR_TAC_PARALLEL_COPY)
	for (copy = instr->copies; copy; copy = copy->next) {
	    if (copy->src > 0 && copy->src < program->num_values)
		uses[copy->src] = 1;
	    if (copy->dst > 0 && copy->dst < program->num_values)
		defs[copy->dst] = 1;
	}
    if (instr->src1 > 0 && instr->src1 < program->num_values)
	uses[instr->src1] = 1;
    if (instr->src2 > 0 && instr->src2 < program->num_values)
	uses[instr->src2] = 1;
    if (instr->src3 > 0 && instr->src3 < program->num_values)
	uses[instr->src3] = 1;
    if (!jit_instr_can_materialize(instr) || instr->deopt_map <= 0
	|| instr->deopt_map >= program->num_deopt_maps)
	return;
    map = &program->deopt_maps[instr->deopt_map];
    for (i = 0; i < map->num_locals; i++) {
	int value = jit_deopt_map_local_value(program, map, i);

	if (value > 0 && value < program->num_values && !defs[value])
	    uses[value] = 1;
    }
    for (i = 0; i < (int) map->stack_depth; i++)
	if (map->stack_values[i] > 0
	    && map->stack_values[i] < program->num_values
	    && !defs[map->stack_values[i]])
	    uses[map->stack_values[i]] = 1;
}

static int
jit_value_type_is_scalar(JITProgram *program, int value)
{
    var_type type;

    if (!program->value_types || !program->value_is_tagged
	|| program->value_is_tagged[value])
	return 0;
    type = program->value_types[value];
    return type != TYPE_ANY && type != TYPE_STR && type != TYPE_LIST
	&& type != TYPE_WAIF;
}

static void
jit_build_value_ownership(JITProgram *program)
{
    unsigned int *uses;
    JITBlock *block;
    int changed;
    int i;

    program->value_ownership = mymalloc(program->num_values, M_PROGRAM);
    program->value_owner_root = mymalloc(sizeof(int) * program->num_values,
					 M_PROGRAM);
    program->value_owned_slots = mymalloc(sizeof(int) * program->num_values,
					  M_PROGRAM);
    uses = mymalloc(sizeof(unsigned int) * program->num_values, M_PROGRAM);
    memset(uses, 0, sizeof(unsigned int) * program->num_values);
    memset(program->value_ownership, JIT_OWNERSHIP_UNKNOWN,
	   program->num_values);
    for (i = 0; i < program->num_values; i++) {
	program->value_owner_root[i] = -1;
	program->value_owned_slots[i] = -1;
	if (jit_value_type_is_scalar(program, i))
	    program->value_ownership[i] = JIT_OWNERSHIP_SCALAR;
    }
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->value > 0 && instr->value < program->num_values) {
		if (instr->kind == HIR_TAC_LOAD_LOCAL) {
		    program->value_ownership[instr->value] =
			JIT_OWNERSHIP_BORROWED_LOCAL;
		    program->value_owner_root[instr->value] = instr->local_id;
		} else if (instr->kind == HIR_TAC_CONST
			   && !jit_value_type_is_scalar(program, instr->value))
		    program->value_ownership[instr->value] =
			JIT_OWNERSHIP_IMMORTAL;
		else if ((instr->kind == HIR_TAC_UNARY
			  && instr->op == HIR_OP_MAKE_SINGLETON_LIST)
			 || (instr->kind == HIR_TAC_BINARY
			     && (instr->op == HIR_OP_LIST_ADD_TAIL
				 || instr->op == HIR_OP_LIST_APPEND
				 || instr->op == HIR_OP_SUBLIST_FROM)))
		    program->value_ownership[instr->value] = JIT_OWNERSHIP_OWNED;
		else if (instr->kind == HIR_TAC_BINARY
			 && instr->op == HIR_OP_GET_PROP)
		    program->value_ownership[instr->value] =
			JIT_OWNERSHIP_STABLE_OWNED;
	    }
	    if (instr == block->last)
		break;
	}
    }
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;

	    if (instr->src1 > 0 && instr->src1 < program->num_values)
		uses[instr->src1]++;
	    if (instr->src2 > 0 && instr->src2 < program->num_values)
		uses[instr->src2]++;
	    if (instr->src3 > 0 && instr->src3 < program->num_values)
		uses[instr->src3]++;
	    for (copy = instr->copies; copy; copy = copy->next)
		if (copy->src > 0 && copy->src < program->num_values)
		    uses[copy->src]++;
	    if (instr == block->last)
		break;
	}
    }
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->value > 0 && instr->value < program->num_values
		&& instr->kind == HIR_TAC_BINARY
		&& instr->op == HIR_OP_LIST_ADD_TAIL
		&& program->value_owned_slots[instr->value] < 0) {
		if (instr->src1 > 0 && instr->src1 < program->num_values
		    && program->value_owned_slots[instr->src1] >= 0
		    && uses[instr->src1] == 1) {
		    program->value_owned_slots[instr->value] =
			jit_list_tail_owner_slot(
			    program->value_owned_slots[instr->src1],
			    uses[instr->src1], program->num_owned_slots);
		} else
		    program->value_owned_slots[instr->value] =
			jit_list_tail_owner_slot(-1, 0,
			    program->num_owned_slots++);
	    }
	    if (instr == block->last)
		break;
	}
    }
    myfree(uses, M_PROGRAM);
    do {
	changed = 0;
	for (block = program->blocks; block; block = block->next) {
	    JITInstruction *instr;

	    for (instr = block->first; instr; instr = instr->next) {
		JITCopy *copy;

		for (copy = instr->copies; copy; copy = copy->next)
		    if (copy->src > 0 && copy->src < program->num_values
			&& copy->dst > 0 && copy->dst < program->num_values
			&& program->value_ownership[copy->src]
			   != JIT_OWNERSHIP_UNKNOWN
			&& program->value_ownership[copy->dst]
			   == JIT_OWNERSHIP_UNKNOWN) {
			program->value_ownership[copy->dst] =
			    program->value_ownership[copy->src];
			program->value_owner_root[copy->dst] =
			    program->value_owner_root[copy->src];
			changed = 1;
		    }
		if (instr == block->last)
		    break;
	    }
	}
    } while (changed);
}

static int
jit_literal_is_int_list(JITInstruction *instr)
{
    Var *list;
    int i;

    if (instr->kind != HIR_TAC_CONST || instr->literal_type != TYPE_LIST
	|| !instr->literal)
	return 0;
    list = (Var *) (intptr_t) instr->literal;
    for (i = 1; i <= list[0].v.num; i++)
	if (list[i].type != TYPE_INT)
	    return 0;
    return 1;
}

static void
jit_build_int_list_values(JITProgram *program)
{
    unsigned int *copy_sources;
    unsigned int *proven_sources;
    unsigned char *instruction_definitions;
    unsigned char *valid_definitions;
    JITBlock *block;
    int changed;
    int value;

    program->value_is_int_list = mymalloc(program->num_values, M_PROGRAM);
    copy_sources = mymalloc(sizeof(unsigned int) * program->num_values,
			    M_PROGRAM);
    proven_sources = mymalloc(sizeof(unsigned int) * program->num_values,
			      M_PROGRAM);
    instruction_definitions = mymalloc(program->num_values, M_PROGRAM);
    valid_definitions = mymalloc(program->num_values, M_PROGRAM);
    memset(program->value_is_int_list, 0, program->num_values);
    memset(copy_sources, 0, sizeof(unsigned int) * program->num_values);
    memset(instruction_definitions, 0, program->num_values);
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;

	    if (instr->value > 0 && instr->value < program->num_values
		&& jit_instr_defines_value(instr)) {
		instruction_definitions[instr->value] = 1;
		if (jit_literal_is_int_list(instr))
		    program->value_is_int_list[instr->value] = 1;
	    }
	    for (copy = instr->copies; copy; copy = copy->next)
		if (copy->src > 0 && copy->src < program->num_values
		    && copy->dst > 0 && copy->dst < program->num_values)
		    copy_sources[copy->dst]++;
	    if (instr == block->last)
		break;
	}
    }
    do {
	changed = 0;
	memset(proven_sources, 0,
	       sizeof(unsigned int) * program->num_values);
	for (block = program->blocks; block; block = block->next) {
	    JITInstruction *instr;

	    for (instr = block->first; instr; instr = instr->next) {
		JITCopy *copy;
		int result_is_int_list = 0;

		if (instr->value > 0 && instr->value < program->num_values) {
		    if (instr->kind == HIR_TAC_UNARY
			&& instr->op == HIR_OP_MAKE_SINGLETON_LIST
			&& instr->src1 > 0 && instr->src1 < program->num_values
			&& !program->value_is_tagged[instr->src1]
			&& program->value_types[instr->src1] == TYPE_INT)
			result_is_int_list = 1;
		    else if (instr->kind == HIR_TAC_BINARY)
			result_is_int_list = jit_int_list_result(instr->op,
			    instr->src1 > 0 && instr->src1 < program->num_values
				&& program->value_is_int_list[instr->src1],
			    instr->src2 > 0 && instr->src2 < program->num_values
				&& program->value_is_int_list[instr->src2],
			    instr->src2 > 0 && instr->src2 < program->num_values
				? program->value_types[instr->src2] : TYPE_ANY);
		    else if (instr->kind == HIR_TAC_INDEX_SET
			&& instr->src1 > 0 && instr->src1 < program->num_values
			&& program->value_is_int_list[instr->src1]
			&& instr->src3 > 0 && instr->src3 < program->num_values
			&& !program->value_is_tagged[instr->src3]
			&& program->value_types[instr->src3] == TYPE_INT)
			result_is_int_list = 1;
		    if (result_is_int_list
			&& !program->value_is_int_list[instr->value]) {
			program->value_is_int_list[instr->value] = 1;
			changed = 1;
		    }
		}
		for (copy = instr->copies; copy; copy = copy->next)
		    if (copy->src > 0 && copy->src < program->num_values
			&& copy->dst > 0 && copy->dst < program->num_values
			&& program->value_is_int_list[copy->src])
			proven_sources[copy->dst]++;
		if (instr == block->last)
		    break;
	    }
	}
	for (value = 1; value < program->num_values; value++)
	    if (proven_sources[value] > 0
		&& !program->value_is_int_list[value]) {
		program->value_is_int_list[value] = 1;
		changed = 1;
	    }
    } while (changed);

    do {
	changed = 0;
	memset(proven_sources, 0,
	       sizeof(unsigned int) * program->num_values);
	memset(valid_definitions, 0, program->num_values);
	for (block = program->blocks; block; block = block->next) {
	    JITInstruction *instr;

	    for (instr = block->first; instr; instr = instr->next) {
		JITCopy *copy;
		int definition_is_valid = jit_literal_is_int_list(instr);

		if (instr->kind == HIR_TAC_UNARY
		    && instr->op == HIR_OP_MAKE_SINGLETON_LIST
		    && instr->src1 > 0 && instr->src1 < program->num_values
		    && !program->value_is_tagged[instr->src1]
		    && program->value_types[instr->src1] == TYPE_INT)
		    definition_is_valid = 1;
		else if (instr->kind == HIR_TAC_BINARY)
		    definition_is_valid = jit_int_list_result(instr->op,
			instr->src1 > 0 && instr->src1 < program->num_values
			    && program->value_is_int_list[instr->src1],
			instr->src2 > 0 && instr->src2 < program->num_values
			    && program->value_is_int_list[instr->src2],
			instr->src2 > 0 && instr->src2 < program->num_values
			    ? program->value_types[instr->src2] : TYPE_ANY);
		else if (instr->kind == HIR_TAC_INDEX_SET)
		    definition_is_valid = instr->src1 > 0
			&& instr->src1 < program->num_values
			&& program->value_is_int_list[instr->src1]
			&& instr->src3 > 0
			&& instr->src3 < program->num_values
			&& !program->value_is_tagged[instr->src3]
			&& program->value_types[instr->src3] == TYPE_INT;
		if (instr->value > 0 && instr->value < program->num_values
		    && definition_is_valid)
		    valid_definitions[instr->value] = 1;
		for (copy = instr->copies; copy; copy = copy->next)
		    if (copy->src > 0 && copy->src < program->num_values
			&& copy->dst > 0 && copy->dst < program->num_values
			&& program->value_is_int_list[copy->src])
			proven_sources[copy->dst]++;
		if (instr == block->last)
		    break;
	    }
	}
	for (value = 1; value < program->num_values; value++)
	    if (program->value_is_int_list[value]
		&& ((instruction_definitions[value]
		     && !valid_definitions[value])
		    || (copy_sources[value] > 0
			&& !jit_all_copy_sources_are_int_lists(
			    copy_sources[value], proven_sources[value]))
		    || (!instruction_definitions[value]
			&& copy_sources[value] == 0))) {
		program->value_is_int_list[value] = 0;
		changed = 1;
	    }
    } while (changed);
    myfree(valid_definitions, M_PROGRAM);
    myfree(instruction_definitions, M_PROGRAM);
    myfree(proven_sources, M_PROGRAM);
    myfree(copy_sources, M_PROGRAM);
}

static int
jit_int_list_alias_root(int *roots, int value)
{
    while (roots[value] != value) {
	roots[value] = roots[roots[value]];
	value = roots[value];
    }
    return value;
}

static void
jit_join_int_list_aliases(int *roots, int left, int right)
{
    left = jit_int_list_alias_root(roots, left);
    right = jit_int_list_alias_root(roots, right);
    if (left != right)
	roots[right] = left;
}

static void
jit_build_direct_int_list_updates(JITProgram *program)
{
    JITBlock *block;
    int *roots;
    int value;

    roots = mymalloc(sizeof(int) * program->num_values, M_PROGRAM);
    for (value = 0; value < program->num_values; value++)
	roots[value] = value;
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;

	    for (copy = instr->copies; copy; copy = copy->next)
		if (copy->src > 0 && copy->src < program->num_values
		    && copy->dst > 0 && copy->dst < program->num_values)
		    jit_join_int_list_aliases(roots, copy->src, copy->dst);
	    if (instr == block->last)
		break;
	}
    }
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_INDEX_SET
		&& instr->src1 > 0 && instr->src1 < program->num_values
		&& instr->src3 > 0 && instr->src3 < program->num_values
		&& program->value_is_int_list[instr->src1]
		&& !program->value_is_tagged[instr->src3]
		&& program->value_types[instr->src3] == TYPE_INT
		&& instr->deopt_map > 0
		&& instr->deopt_map < program->num_deopt_maps) {
		JITDeoptMap *map = &program->deopt_maps[instr->deopt_map];
		unsigned int matching_locals = 0;
		int base_root = jit_int_list_alias_root(roots, instr->src1);
		int slot;

		for (slot = 0; slot < map->num_locals; slot++) {
		    int local = jit_deopt_map_local_value(program, map, slot);

		    if (local > 0 && local < program->num_values
			&& jit_int_list_alias_root(roots, local) == base_root)
			matching_locals++;
		}
		instr->direct_int_list_index_set =
		    jit_int_list_has_exclusive_local(matching_locals);
	    }
	    if (instr == block->last)
		break;
	}
    }
    myfree(roots, M_PROGRAM);
}

static int
jit_value_defined_by_instruction(JITProgram *program, int value)
{
    JITBlock *block;

    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->value == value && jit_instr_defines_value(instr))
		return 1;
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

static int
jit_value_must_be_available(JITProgram *program, JITInstruction *call,
			    int value)
{
    JITBlock *block;
    unsigned char *available_in;
    unsigned char *available_out;
    unsigned char *reachable;
    int max_block = 0;
    int changed;
    int result = 0;

    for (block = program->blocks; block; block = block->next)
	if (block->id > max_block)
	    max_block = block->id;
    available_in = mymalloc(max_block + 1, M_PROGRAM);
    available_out = mymalloc(max_block + 1, M_PROGRAM);
    reachable = mymalloc(max_block + 1, M_PROGRAM);
    memset(available_in, 0, max_block + 1);
    memset(available_out, 0, max_block + 1);
    memset(reachable, 0, max_block + 1);
    do {
	changed = 0;
	for (block = program->blocks; block; block = block->next) {
	    JITBlock *predecessor;
	    int in = 1;
	    int has_predecessor = 0;
	    int out;

	    if (block == program->blocks) {
		in = 0;
		if (!reachable[block->id]) {
		    reachable[block->id] = 1;
		    changed = 1;
		}
	    } else {
		for (predecessor = program->blocks; predecessor;
		     predecessor = predecessor->next) {
		    int successor;

		    if (!reachable[predecessor->id])
			continue;
		    for (successor = 0;
			 successor < predecessor->num_successors; successor++)
			if (predecessor->successors[successor] == block->id) {
			    has_predecessor = 1;
			    in = in && available_out[predecessor->id];
			}
		}
		if (!has_predecessor)
		    continue;
		if (!reachable[block->id]) {
		    reachable[block->id] = 1;
		    changed = 1;
		}
	    }
	    if (available_in[block->id] != in) {
		available_in[block->id] = in;
		changed = 1;
	    }
	    out = in;
	    if (!out) {
		JITInstruction *instr;

		for (instr = block->first; instr; instr = instr->next) {
		    JITCopy *copy;

		    if (instr->value == value && jit_instr_defines_value(instr))
			out = 1;
		    for (copy = instr->copies; copy; copy = copy->next)
			if (copy->dst == value)
			    out = 1;
		    if (instr == block->last)
			break;
		}
	    }
	    if (available_out[block->id] != out) {
		available_out[block->id] = out;
		changed = 1;
	    }
	}
    } while (changed);

    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;
	int available;

	if (!reachable[block->id])
	    continue;
	available = available_in[block->id];
	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;

	    if (instr == call) {
		result = available;
		goto done;
	    }
	    if (instr->value == value && jit_instr_defines_value(instr))
		available = 1;
	    for (copy = instr->copies; copy; copy = copy->next)
		if (copy->dst == value)
		    available = 1;
	    if (instr == block->last)
		break;
	}
    }
done:
    myfree(reachable, M_PROGRAM);
    myfree(available_out, M_PROGRAM);
    myfree(available_in, M_PROGRAM);
    return result;
}

static int
jit_resume_source(JITProgram *program, JITDeoptMap *map,
		  JITInstruction *call, int value, JITResumeValue *resume)
{
    JITBlock *block;
    int call_operands = jit_call_stack_operands(map);
    int i;

    resume->value = value;
    if (value == call->value) {
	resume->source = JIT_RESUME_RESULT;
	return 1;
    }
    for (i = 0; i < map->num_locals; i++)
	if (jit_deopt_map_local_value(program, map, i) == value) {
	    resume->source = JIT_RESUME_LOCAL;
	    resume->index = i;
	    return 1;
	}
    for (i = 0; i + call_operands < (int) map->stack_depth; i++)
	if (map->stack_values[i] == value) {
	    resume->source = JIT_RESUME_STACK;
	    resume->index = i;
	    return 1;
	}
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_CONST && instr->value == value) {
		resume->source = JIT_RESUME_CONSTANT;
		resume->literal = instr->literal;
		resume->literal_type = instr->literal_type;
		return 1;
	    }
	    if (instr == block->last)
		break;
	}
    }
    if (program->value_owned_slots
	&& program->value_ownership
	&& program->value_owned_slots[value] >= 0
	&& (program->value_ownership[value] == JIT_OWNERSHIP_OWNED
	    || program->value_ownership[value] == JIT_OWNERSHIP_STABLE_OWNED)
	&& jit_value_defined_by_instruction(program, value)
	&& jit_value_must_be_available(program, call, value)) {
	resume->source = JIT_RESUME_OWNER;
	resume->index = program->value_owned_slots[value];
	return 1;
    }
    return 0;
}

static int
jit_owned_value_is_fresh(JITProgram *program, JITInstruction *call, int value)
{
    JITBlock *block;

    if (program->value_ownership[value] != JIT_OWNERSHIP_OWNED
	&& program->value_ownership[value] != JIT_OWNERSHIP_STABLE_OWNED)
	return 0;
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;
	int found = 0;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr == call)
		return found;
	    if (found) {
		JITCopy *copy;

		if (instr->src1 == value || instr->src2 == value
		    || instr->src3 == value || instr->kind == HIR_TAC_CALL
		    || instr->kind == HIR_TAC_CALL_VERB
		    || instr->kind == HIR_TAC_PUT_PROP
		    || instr->kind == HIR_TAC_INDEX_SET
		    || instr->kind == HIR_TAC_RANGE_SET)
		    return 0;
		for (copy = instr->copies; copy; copy = copy->next)
		    if (copy->src == value || copy->dst == value)
			return 0;
	    }
	    if (instr->value == value && jit_instr_defines_value(instr))
		found = 1;
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

static int
jit_resume_value_can_capture(JITProgram *program, JITInstruction *call,
			     int value)
{
    if (value <= 0 || value >= program->num_values
	|| !program->value_ownership)
	return 0;
    return program->value_ownership[value] == JIT_OWNERSHIP_BORROWED_LOCAL
	|| program->value_ownership[value] == JIT_OWNERSHIP_IMMORTAL
	|| jit_owned_value_is_fresh(program, call, value);
}

static void
jit_build_resume_liveness(JITProgram *program)
{
    JITBlock *block;
    unsigned char **live_in, **live_out, **block_use, **block_def;
    int max_block = 0, changed, i;

    for (block = program->blocks; block; block = block->next)
	if (block->id > max_block)
	    max_block = block->id;
    live_in = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    live_out = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    block_use = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    block_def = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    memset(live_in, 0, sizeof(unsigned char *) * (max_block + 1));
    memset(live_out, 0, sizeof(unsigned char *) * (max_block + 1));
    memset(block_use, 0, sizeof(unsigned char *) * (max_block + 1));
    memset(block_def, 0, sizeof(unsigned char *) * (max_block + 1));
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;
	unsigned char *seen_defs;

	live_in[block->id] = mymalloc(program->num_values, M_PROGRAM);
	live_out[block->id] = mymalloc(program->num_values, M_PROGRAM);
	block_use[block->id] = mymalloc(program->num_values, M_PROGRAM);
	block_def[block->id] = mymalloc(program->num_values, M_PROGRAM);
	seen_defs = mymalloc(program->num_values, M_PROGRAM);
	memset(live_in[block->id], 0, program->num_values);
	memset(live_out[block->id], 0, program->num_values);
	memset(block_use[block->id], 0, program->num_values);
	memset(block_def[block->id], 0, program->num_values);
	memset(seen_defs, 0, program->num_values);
	for (instr = block->first; instr; instr = instr->next) {
	    unsigned char *uses = mymalloc(program->num_values, M_PROGRAM);
	    unsigned char *defs = mymalloc(program->num_values, M_PROGRAM);
	    int value;
	    memset(uses, 0, program->num_values);
	    memset(defs, 0, program->num_values);
	    jit_instr_liveness(program, instr, uses, defs);
	    for (value = 1; value < program->num_values; value++) {
		if (uses[value] && !seen_defs[value])
		    block_use[block->id][value] = 1;
		if (defs[value]) {
		    seen_defs[value] = 1;
		    block_def[block->id][value] = 1;
		}
	    }
	    myfree(defs, M_PROGRAM);
	    myfree(uses, M_PROGRAM);
	    if (instr == block->last)
		break;
	}
	myfree(seen_defs, M_PROGRAM);
    }
    do {
	changed = 0;
	for (block = program->blocks; block; block = block->next) {
	    int value, successor;
	    for (value = 1; value < program->num_values; value++) {
		int out = 0;
		for (successor = 0; successor < block->num_successors; successor++)
		    if (live_in[block->successors[successor]]
			&& live_in[block->successors[successor]][value])
			out = 1;
		if (live_out[block->id][value] != out) {
		    live_out[block->id][value] = out;
		    changed = 1;
		}
		out = block_use[block->id][value]
		    || (out && !block_def[block->id][value]);
		if (live_in[block->id][value] != out) {
		    live_in[block->id][value] = out;
		    changed = 1;
		}
	    }
	}
    } while (changed);

    for (block = program->blocks; block; block = block->next) {
	JITInstruction **instructions;
	JITInstruction *instr;
	unsigned char *live;
	int count = 0, index;

	for (instr = block->first; instr; instr = instr->next) {
	    count++;
	    if (instr == block->last)
		break;
	}
	instructions = mymalloc(sizeof(JITInstruction *) * count, M_PROGRAM);
	count = 0;
	for (instr = block->first; instr; instr = instr->next) {
	    instructions[count++] = instr;
	    if (instr == block->last)
		break;
	}
	live = mymalloc(program->num_values, M_PROGRAM);
	memcpy(live, live_out[block->id], program->num_values);
	for (index = count - 1; index >= 0; index--) {
	    unsigned char *uses = mymalloc(program->num_values, M_PROGRAM);
	    unsigned char *defs = mymalloc(program->num_values, M_PROGRAM);
	    int value, live_count = 0;
	    instr = instructions[index];
	    if (instr->deopt_map > 0
		&& instr->deopt_map < program->num_deopt_maps
		&& (instr->kind == HIR_TAC_CALL_VERB
		 || jit_deopt_map_can_bridge_builtin(
		     &program->deopt_maps[instr->deopt_map]))) {
		JITDeoptMap *map = &program->deopt_maps[instr->deopt_map];
		JITNativeResume *resume = mymalloc(sizeof(JITNativeResume),
						   M_PROGRAM);
		unsigned char *needed = mymalloc(program->num_values, M_PROGRAM);
		int call_operands = jit_call_stack_operands(map);
		const char *call_name = instr->kind == HIR_TAC_CALL
		    ? name_func_by_num(instr->func) : 0;
		int saved_stack_depth = map->stack_depth;
		int slot;

		if (call_name && !strcmp(call_name, "suspend"))
		    saved_stack_depth -= call_operands;

		memcpy(needed, live, program->num_values);
		for (slot = 0; slot < map->num_locals; slot++) {
		    value = jit_deopt_map_local_value(program, map, slot);
		    if (value > 0 && value < program->num_values)
			needed[value] = 1;
		}
		for (slot = 0; slot < saved_stack_depth; slot++)
		    if ((!map->stack_slots
			 || map->stack_slots[slot].kind == RSS_VALUE)
			&& map->stack_values[slot] > 0
			&& map->stack_values[slot] < program->num_values)
			needed[map->stack_values[slot]] = 1;
		for (value = 1; value < program->num_values; value++)
		    if (needed[value])
			live_count++;
		memset(resume, 0, sizeof(JITNativeResume));
		map->native_resume = resume;
		resume->values = live_count
		    ? mymalloc(sizeof(JITResumeValue) * live_count, M_PROGRAM) : 0;
		resume->num_values = live_count;
		resume->valid = 1;
		resume->rehydratable = jit_resume_stack_is_safe(map,
							    call_operands);
		live_count = 0;
		for (value = 1; value < program->num_values; value++) {
		    if (!needed[value])
			continue;
		    if (!jit_resume_source(program, map, instr, value,
			&resume->values[live_count++])) {
			const char *func_name = instr->kind == HIR_TAC_CALL
			    ? name_func_by_num(instr->func) : 0;

			if ((func_name && !strcmp(func_name, "suspend"))
			    || jit_resume_value_can_capture(program, instr, value)) {
			    resume->values[live_count - 1].source =
				JIT_RESUME_CAPTURED;
			    resume->rehydratable = 0;
			} else {
			    resume->valid = 0;
			    resume->values[live_count - 1].index = -1;
			}
		    } else if (resume->values[live_count - 1].source
			       == JIT_RESUME_OWNER)
			resume->rehydratable = 0;
		}
		myfree(needed, M_PROGRAM);
	    }
	    memset(uses, 0, program->num_values);
	    memset(defs, 0, program->num_values);
	    jit_instr_liveness(program, instr, uses, defs);
	    for (value = 1; value < program->num_values; value++)
		live[value] = uses[value] || (live[value] && !defs[value]);
	    myfree(defs, M_PROGRAM);
	    myfree(uses, M_PROGRAM);
	}
	myfree(live, M_PROGRAM);
	myfree(instructions, M_PROGRAM);
    }
    for (i = 0; i <= max_block; i++) {
	if (live_in[i]) myfree(live_in[i], M_PROGRAM);
	if (live_out[i]) myfree(live_out[i], M_PROGRAM);
	if (block_use[i]) myfree(block_use[i], M_PROGRAM);
	if (block_def[i]) myfree(block_def[i], M_PROGRAM);
    }
    myfree(block_def, M_PROGRAM);
    myfree(block_use, M_PROGRAM);
    myfree(live_out, M_PROGRAM);
    myfree(live_in, M_PROGRAM);
}

JITProgram *
hir_create_jit_program(HIRContext *ctx, HIRSSAProgram *ssa,
		       Program *bytecode_program)
{
    JITProgram *program;
    HIRSSABlock *ssa_block;
    var_type *value_types;
    unsigned char *value_types_known;
    unsigned char *value_types_conflicted;
    unsigned char *value_is_tagged;
    const char *value_type_diagnostic = 0;
    int types_changed;
    int i;

    if (!ctx || ctx->error_count || !jit_ssa_is_supported(ctx, ssa)) {
	const char *diag = ctx ? hir_context_error_message(ctx) : 0;
	return jit_program_unsupported_with_diagnostic("unsupported-program", diag);
    }
    if (!jit_ssa_anchors_are_valid(ctx, ssa, bytecode_program)) {
	const char *diag = ctx ? hir_context_error_message(ctx) : 0;
	return jit_program_unsupported_with_diagnostic("invalid-bytecode-anchor", diag);
    }

    program = mymalloc(sizeof(JITProgram), M_PROGRAM);
    memset(program, 0, sizeof(JITProgram));
    program->state = JIT_STATE_PENDING;
    program->bytecode_program = bytecode_program;
    program->reason = str_dup("none");
    program->diagnostic = str_dup("none");
    program->eligible = 1;
    program->num_values = ctx->next_temp;
    program->num_vars = ctx->var_names ? ctx->var_names->size : 0;
    program->num_deopt_maps = 1;
    program->deopt_maps = mymalloc(sizeof(JITDeoptMap), M_PROGRAM);
    memset(&program->deopt_maps[0], 0, sizeof(JITDeoptMap));
    program->deopt_maps[0].bytecode_pc = 0;
    program->deopt_maps[0].builtin_func = -1;
    program->deopt_maps[0].builtin_args = -1;
    program->deopt_maps[0].operation = -1;
    program->deopt_maps[0].error_pc = 0;
    program->deopt_maps[0].source_lineno = 1;
    program->deopt_maps[0].reason = JIT_DEOPT_TYPE_GUARD;
    program->deopt_maps[0].stack_depth = 0;
    program->deopt_maps[0].ticks_charged = 0;
    program->deopt_maps[0].num_locals = program->num_vars;
    program->deopt_maps[0].stack_values = 0;
    program->deopt_maps[0].stack_types = 0;

    value_types = mymalloc(sizeof(var_type) * (program->num_values > 0
					       ? program->num_values : 1),
			   M_PROGRAM);
    value_types_known = mymalloc(program->num_values > 0
				 ? program->num_values : 1, M_PROGRAM);
    value_types_conflicted = mymalloc(program->num_values > 0
				      ? program->num_values : 1, M_PROGRAM);
    value_is_tagged = mymalloc(program->num_values > 0
			      ? program->num_values : 1, M_PROGRAM);
    initialize_inferred_value_types(value_types, value_types_known,
				    value_is_tagged, program->num_values);
    memset(value_types_conflicted, 0, program->num_values > 0
	   ? program->num_values : 1);

    for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	HIRSSAInstr *si;
	for (si = ssa_block->first; si; si = si->next) {
	    if (si->value > 0 && si->value < program->num_values) {
		var_type entry_type;

		if (si->kind == HIR_TAC_CONST) {
		    value_types[si->value] = si->literal.type;
		    value_types_known[si->value] = 1;
		} else if (si->kind == HIR_TAC_LOAD_ERROR) {
		    value_types[si->value] = TYPE_ERR;
		    value_types_known[si->value] = 1;
		} else if (builtin_entry_type(si->kind, si->bytecode_pc,
					   si->local_id,
					   first_user_slot(bytecode_program->version),
					   &entry_type)) {
		    value_types[si->value] = entry_type;
		    value_types_known[si->value] = 1;
		} else if (is_uninitialized_entry_load(si->kind,
						       si->bytecode_pc,
						       si->local_id,
						       first_user_slot(bytecode_program->version))) {
		    value_types[si->value] = TYPE_NONE;
		    value_types_known[si->value] = 1;
		} else if (si->kind == HIR_TAC_UNARY) {
		    if (si->op == HIR_OP_MAKE_SINGLETON_LIST
			|| si->op == HIR_OP_CHECK_LIST_FOR_SPLICE) {
			value_types[si->value] = TYPE_LIST;
			value_types_known[si->value] = 1;
		    } else if (si->op == HIR_OP_NOT || si->op == HIR_OP_TYPEOF
			       || si->op == HIR_OP_TOINT || si->op == HIR_OP_LENGTH
			       || si->op == HIR_OP_ABS || si->op == HIR_OP_TICKS_LEFT
			       || si->op == HIR_OP_SECONDS_LEFT || si->op == HIR_OP_TIME
			       || si->op == HIR_OP_VALID) {
			value_types[si->value] = TYPE_INT;
			value_types_known[si->value] = 1;
		    } else if (si->op == HIR_OP_PARENT) {
			value_types[si->value] = TYPE_OBJ;
			value_types_known[si->value] = 1;
		    }
		} else if (si->kind == HIR_TAC_BINARY) {
		    if (si->op == HIR_OP_LIST_ADD_TAIL
			|| si->op == HIR_OP_LIST_APPEND
			|| si->op == HIR_OP_SUBLIST_FROM) {
			value_types[si->value] = TYPE_LIST;
			value_types_known[si->value] = 1;
		    } else if (si->op == HIR_OP_EQ || si->op == HIR_OP_NE
			       || si->op == HIR_OP_LT || si->op == HIR_OP_LE
			       || si->op == HIR_OP_GT || si->op == HIR_OP_GE
			       || si->op == HIR_OP_IN || si->op == HIR_OP_BITOR
			       || si->op == HIR_OP_BITXOR || si->op == HIR_OP_BITAND
			       || si->op == HIR_OP_SHL || si->op == HIR_OP_SHR
			       || si->op == HIR_OP_LSHR
			       || si->op == HIR_OP_INDEX_BF
			       || si->op == HIR_OP_RINDEX_BF) {
			value_types[si->value] = TYPE_INT;
			value_types_known[si->value] = 1;
		    }
		} else if (si->kind == HIR_TAC_INDEX_SET) {
		    value_types[si->value] = TYPE_LIST;
		    value_types_known[si->value] = 1;
		}
	    }
	    if (si == ssa_block->last)
		break;
	}
    }

    /* Operand constraints below can seed types that must propagate through
       parallel-copy joins. */
    infer_value_types:
    do {
	types_changed = 0;
	for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	    HIRSSAInstr *si;
	    for (si = ssa_block->first; si; si = si->next) {
		HIRParallelCopy *copy;

		for (copy = si->copies; copy; copy = copy->next)
		    if (copy->src > 0 && copy->src < program->num_values
			&& copy->dst > 0 && copy->dst < program->num_values
			&& value_types_known[copy->src]) {
			if (!value_types_known[copy->dst]) {
			    value_types[copy->dst] = value_types[copy->src];
			    value_types_known[copy->dst] = 1;
			    types_changed = 1;
			} else if (value_types[copy->dst]
				   != value_types[copy->src]) {
			    if (value_types[copy->dst] == TYPE_FLOAT
				|| value_types[copy->src] == TYPE_FLOAT)
				value_type_diagnostic = "value-types: parallel-copy float conflict";
			    value_types_conflicted[copy->dst] = 1;
			}
		    }
		if (si->kind == HIR_TAC_UNARY
		    && (si->op == HIR_OP_NEGATE || si->op == HIR_OP_ABS)
		    && si->value > 0 && si->value < program->num_values
		    && si->src1 > 0 && si->src1 < program->num_values
		    && value_types_known[si->src1]) {
		    var_type inferred = value_types[si->src1];

		    if (inferred == TYPE_INT || inferred == TYPE_FLOAT) {
			if (!value_types_known[si->value]) {
			    value_types[si->value] = inferred;
			    value_types_known[si->value] = 1;
			    types_changed = 1;
			} else if (value_types[si->value] != inferred) {
			    if (value_types[si->value] == TYPE_FLOAT
				|| inferred == TYPE_FLOAT)
				value_type_diagnostic = "value-types: unary float conflict";
			    value_types_conflicted[si->value] = 1;
			}
		    }
		}
		if (si->kind == HIR_TAC_BINARY
		    && (si->op == HIR_OP_ADD || si->op == HIR_OP_SUB
			|| si->op == HIR_OP_MUL || si->op == HIR_OP_DIV
			|| si->op == HIR_OP_MOD || si->op == HIR_OP_EXP)
		    && si->value > 0 && si->value < program->num_values) {
		    int src1_known = si->src1 > 0
			&& si->src1 < program->num_values
			&& value_types_known[si->src1];
		    int src2_known = si->src2 > 0
			&& si->src2 < program->num_values
			&& value_types_known[si->src2];

		    if (!src2_known
			&& infer_string_add_operand(si->op, src1_known,
					    src1_known
					    ? value_types[si->src1] : TYPE_NONE,
					    &value_types[si->src2])) {
			    value_types_known[si->src2] = 1;
			    src2_known = 1;
			    types_changed = 1;
		    } else if (!src1_known
			       && infer_string_add_operand(si->op, src2_known,
						   src2_known
						   ? value_types[si->src2] : TYPE_NONE,
						   &value_types[si->src1])) {
			    value_types_known[si->src1] = 1;
			    src1_known = 1;
			    types_changed = 1;
		    }

		    if (src1_known && src2_known) {
			var_type t1 = value_types[si->src1];
			var_type t2 = value_types[si->src2];
			var_type inferred = TYPE_INT;
			int valid = 1;
			int object_range_add = si->op == HIR_OP_ADD
			    && si->bytecode_pc != NO_BYTECODE_PC
			    && bytecode_program->main_vector.vector[si->bytecode_pc]
			       == OP_FOR_RANGE
			    && t1 == TYPE_OBJ && t2 == TYPE_INT;

			if (object_range_add)
			    inferred = TYPE_OBJ;
			else if (binary_type_pair_is_valid(si->op, t1, t2))
			    inferred = t1;
			else
			    valid = 0;
			if (valid && !value_types_known[si->value]) {
			    value_types[si->value] = inferred;
			    value_types_known[si->value] = 1;
			    types_changed = 1;
			} else if (valid && value_types[si->value] != inferred) {
			    if (value_types[si->value] == TYPE_FLOAT
				|| inferred == TYPE_FLOAT)
				value_type_diagnostic = "value-types: arithmetic float conflict";
			    value_types_conflicted[si->value] = 1;
			}
		    }
		}
		if (si->kind == HIR_TAC_BINARY
		    && (si->op == HIR_OP_MIN || si->op == HIR_OP_MAX)
		    && si->value > 0 && si->value < program->num_values
		    && si->src1 > 0 && si->src1 < program->num_values
		    && si->src2 > 0 && si->src2 < program->num_values
		    && value_types_known[si->src1]
		    && value_types_known[si->src2]) {
		    var_type inferred;

		    if (infer_min_max_result(si->op, value_types[si->src1],
					value_types[si->src2], &inferred)) {
			if (!value_types_known[si->value]) {
			    value_types[si->value] = inferred;
			    value_types_known[si->value] = 1;
			    types_changed = 1;
			} else if (value_types[si->value] != inferred)
			    value_types_conflicted[si->value] = 1;
		    }
		}
		if (si->kind == HIR_TAC_BINARY
		    && binary_operands_constrain_each_other(si->op)) {
		    int src1_known = si->src1 > 0 && si->src1 < program->num_values
			&& value_types_known[si->src1];
		    int src2_known = si->src2 > 0 && si->src2 < program->num_values
			&& value_types_known[si->src2];

		    if (src1_known && (value_types[si->src1] == TYPE_OBJ
				       || value_types[si->src1] == TYPE_FLOAT)
			&& !src2_known) {
			value_types[si->src2] = value_types[si->src1];
			value_types_known[si->src2] = 1;
			types_changed = 1;
		    } else if (src2_known && (value_types[si->src2] == TYPE_OBJ
					      || value_types[si->src2] == TYPE_FLOAT)
			       && !src1_known) {
			value_types[si->src1] = value_types[si->src2];
			value_types_known[si->src1] = 1;
			types_changed = 1;
		    }
		}
		if (si->kind == HIR_TAC_RANGE_REF
		    && si->value > 0 && si->value < program->num_values
		    && si->src1 > 0 && si->src1 < program->num_values
		    && value_types_known[si->src1]) {
		    var_type base_t = value_types[si->src1];
		    if (base_t == TYPE_STR || base_t == TYPE_LIST) {
			if (!value_types_known[si->value]) {
			    value_types[si->value] = base_t;
			    value_types_known[si->value] = 1;
			    types_changed = 1;
			}
		    }
		}
		if (si == ssa_block->last)
		    break;
	    }
	}
    } while (types_changed);

    for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	HIRSSAInstr *si;
	for (si = ssa_block->first; si; si = si->next) {
	    if (si->kind == HIR_TAC_BINARY && si->op == HIR_OP_SUBLIST_FROM) {
		value_types[si->value] = TYPE_LIST;
		value_types_known[si->value] = 1;
	    }
	    if (si->kind == HIR_TAC_RANGE_REF) {
		int from = si->src2;
		if (from > 0 && from < program->num_values
		    && !value_types_known[from]) {
		    value_types[from] = TYPE_INT;
		    value_types_known[from] = 1;
		    types_changed = 1;
		}
	    }
	    if (si->kind == HIR_TAC_INDEX_SET
		&& si->src2 > 0 && si->src2 < program->num_values
		&& !value_types_known[si->src2]) {
		value_types[si->src2] = TYPE_INT;
		value_types_known[si->src2] = 1;
		types_changed = 1;
	    }
	    if (si->kind == HIR_TAC_PUT_PROP) {
		int rhs = si->num_stack_values >= 1
		    ? si->stack_values[si->num_stack_values - 1] : 0;

		if (rhs > 0 && rhs < program->num_values
		    && value_types_known[rhs] && !value_types_known[si->value]) {
		    value_types[si->value] = value_types[rhs];
		    value_types_known[si->value] = 1;
		    types_changed = 1;
		}
	    }
	    if (si->kind == HIR_TAC_DEOPT && si->op == HIR_OP_INDEX
		&& si->num_stack_values >= 3) {
		int index = si->stack_values[si->num_stack_values - 2];

		if (index > 0 && index < program->num_values
		    && !value_types_known[index]) {
		    value_types[index] = TYPE_INT;
		    value_types_known[index] = 1;
		    types_changed = 1;
		}
	    }
	    if (si->kind == HIR_TAC_DEOPT && si->op == HIR_OP_SCATTER
		&& si->num_stack_values == 1) {
		int rhs = si->stack_values[0];

		if (rhs > 0 && rhs < program->num_values
		    && !value_types_known[rhs]) {
		    value_types[rhs] = TYPE_LIST;
		    value_types_known[rhs] = 1;
		    types_changed = 1;
		}
	    }

	    if (si->kind == HIR_TAC_RANGE_SET && si->num_stack_values >= 4) {
		int from = si->stack_values[si->num_stack_values - 3];
		int to = si->stack_values[si->num_stack_values - 2];

		if (from > 0 && from < program->num_values
		    && !value_types_known[from]) {
		    value_types[from] = TYPE_INT;
		    value_types_known[from] = 1;
		    types_changed = 1;
		}
		if (to > 0 && to < program->num_values
		    && !value_types_known[to]) {
		    value_types[to] = TYPE_INT;
		    value_types_known[to] = 1;
		    types_changed = 1;
		}
	    }
	    if (si->kind == HIR_TAC_CALL_VERB) {
		if (si->src2 > 0 && si->src2 < program->num_values
		    && !value_types_known[si->src2]) {
		    value_types[si->src2] = TYPE_STR;
		    value_types_known[si->src2] = 1;
		    types_changed = 1;
		}
		if (si->num_stack_values > 0) {
		    int args_val = si->stack_values[si->num_stack_values - 1];

		    if (args_val > 0 && args_val < program->num_values
			&& !value_types_known[args_val]) {
			value_types[args_val] = TYPE_LIST;
			value_types_known[args_val] = 1;
			types_changed = 1;
		    }
		}
	    }
	    if (si->kind == HIR_TAC_CALL) {
		const char *func_name = name_func_by_num(si->func);
		int first_arg = ssa_first_list_element(ssa, si->src1);

		if (func_name
		    && (!strcmp(func_name, "valid") || !strcmp(func_name, "notify"))
		    && first_arg > 0 && first_arg < program->num_values
		    && !value_types_known[first_arg]) {
		    value_types[first_arg] = TYPE_OBJ;
		    value_types_known[first_arg] = 1;
		    types_changed = 1;
		}
		if (func_name && si->value > 0 && si->value < program->num_values
		    && !value_types_known[si->value]) {
		    var_type result_type;

		    if (infer_builtin_result_type(func_name, &result_type)) {
			value_types[si->value] = result_type;
			value_types_known[si->value] = 1;
			types_changed = 1;
		    }
		}
	    }
	    if (si == ssa_block->last)
		break;
	}
    }
    if (types_changed)
	goto infer_value_types;
    for (i = 1; i < program->num_values; i++)
	if (value_types_conflicted[i]) {
	    value_is_tagged[i] = 1;
	    value_types[i] = TYPE_ANY;
	    value_types_known[i] = 0;
	}
    tag_unknown_inferred_value_types(value_types, value_types_known,
				     value_is_tagged, program->num_values);
    /* Preserve runtime tags for values whose result type is selected at run
       time.  Parallel-copy destinations need a tag as well, including joins
       with a statically typed default value. */
    for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	HIRSSAInstr *si;

	for (si = ssa_block->first; si; si = si->next) {
	    if (si->kind == HIR_TAC_CALL_VERB
		&& si->value > 0 && si->value < program->num_values) {
		value_is_tagged[si->value] = 1;
		value_types[si->value] = TYPE_ANY;
		value_types_known[si->value] = 0;
	    }
	    if ((si->kind == HIR_TAC_CALL || si->kind == HIR_TAC_RANGE_REF)
		&& si->value > 0 && si->value < program->num_values
		&& !value_types_known[si->value])
		value_is_tagged[si->value] = 1;
	    if (si->kind == HIR_TAC_PUT_PROP) {
		int rhs = si->num_stack_values >= 1
		    ? si->stack_values[si->num_stack_values - 1] : 0;

		if (rhs > 0 && rhs < program->num_values && value_is_tagged[rhs]) {
		    value_is_tagged[si->value] = 1;
		    value_types[si->value] = TYPE_ANY;
		    value_types_known[si->value] = 0;
		}
	    }
	    if (si->kind == HIR_TAC_BINARY
		&& (si->op == HIR_OP_INDEX || si->op == HIR_OP_GET_PROP)
		&& si->value > 0 && si->value < program->num_values
		&& !value_types_known[si->value])
		value_is_tagged[si->value] = 1;
	    if (si->kind == HIR_TAC_LOAD_LOCAL && si->bytecode_pc == NO_BYTECODE_PC
		&& si->value > 0 && si->value < program->num_values
		&& !value_types_known[si->value])
		value_is_tagged[si->value] = 1;
	    if (si == ssa_block->last)
		break;
	}
    }
    do {
	types_changed = 0;
	for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	    HIRSSAInstr *si;

	    for (si = ssa_block->first; si; si = si->next) {
		HIRParallelCopy *copy;
		int tagged_operand = (si->src1 > 0
				      && si->src1 < program->num_values
				      && value_is_tagged[si->src1])
		    || (si->src2 > 0 && si->src2 < program->num_values
			&& value_is_tagged[si->src2]);

		if (si->kind == HIR_TAC_BINARY && si->op == HIR_OP_ADD
		    && tagged_operand && si->value > 0
		    && si->value < program->num_values
		    && !value_is_tagged[si->value]) {
		    value_is_tagged[si->value] = 1;
		    types_changed = 1;
		}
		if (si->kind == HIR_TAC_BINARY && si->op == HIR_OP_GET_PROP
		    && si->value > 0 && si->value < program->num_values
		    && !value_is_tagged[si->value]) {
		    value_is_tagged[si->value] = 1;
		    types_changed = 1;
		}

		for (copy = si->copies; copy; copy = copy->next)
		    if (copy->src > 0 && copy->src < program->num_values
			&& copy->dst > 0 && copy->dst < program->num_values
			&& value_is_tagged[copy->src]
			&& !value_is_tagged[copy->dst]) {
			value_is_tagged[copy->dst] = 1;
			types_changed = 1;
		    }
		if (si == ssa_block->last)
		    break;
	    }
	}
    } while (types_changed);
    for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	HIRSSAInstr *si;
	for (si = ssa_block->first; si; si = si->next) {
	    HIRParallelCopy *copy;
	    for (copy = si->copies; copy; copy = copy->next)
		if (copy->src > 0 && copy->src < program->num_values
		    && copy->dst > 0 && copy->dst < program->num_values) {
		    int src_fl = value_types[copy->src] == TYPE_FLOAT;
		    int dst_fl = value_types[copy->dst] == TYPE_FLOAT;
		    if (src_fl != dst_fl)
			value_types_conflicted[copy->dst] = 1;
		}
	    if (si == ssa_block->last)
		break;
	}
    }
    if (value_type_diagnostic) {
	myfree(value_types_conflicted, M_PROGRAM);
	myfree(value_types_known, M_PROGRAM);
	myfree(value_is_tagged, M_PROGRAM);
	myfree(value_types, M_PROGRAM);
	jit_program_free(program);
	return jit_program_unsupported_with_diagnostic("unsupported-value-types",
						       value_type_diagnostic);
    }
#if FLOATING_TYPE != FT_DOUBLE || FLOATS_ARE_BOXED
    for (i = 1; i < program->num_values; i++)
	if (value_types_known[i] && value_types[i] == TYPE_FLOAT) {
	    myfree(value_types_conflicted, M_PROGRAM);
	    myfree(value_types_known, M_PROGRAM);
	    myfree(value_is_tagged, M_PROGRAM);
	    myfree(value_types, M_PROGRAM);
	    jit_program_free(program);
	    return jit_program_unsupported_with_diagnostic("unsupported-float-representation",
							   "float-representation: unsupported float boxing");
	}
#endif

    for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	HIRBasicBlock *cfg_block = cfg_block_for_id(ssa->cfg, ssa_block->id);
	HIRSSAInstr *ssa_instr;
	JITBlock *block = mymalloc(sizeof(JITBlock), M_PROGRAM);

	memset(block, 0, sizeof(JITBlock));
	block->id = ssa_block->id;
	if (cfg_block) {
	    block->num_successors = cfg_block->num_successors;
	    for (i = 0; i < cfg_block->num_successors; i++)
		block->successors[i] = cfg_block->successors[i]->id;
	}
	if (program->last_block)
	    program->last_block->next = block;
	else
	    program->blocks = block;
	program->last_block = block;
	program->num_blocks++;

	for (ssa_instr = ssa_block->first; ssa_instr;
	     ssa_instr = ssa_instr->next) {
	    HIRParallelCopy *ssa_copy;
	    JITInstruction *instr = mymalloc(sizeof(JITInstruction), M_PROGRAM);
	    int uses_conflicted = (ssa_instr->src1 > 0
				   && ssa_instr->src1 < program->num_values
				   && value_types_conflicted[ssa_instr->src1]
				   && !value_is_tagged[ssa_instr->src1])
		|| (ssa_instr->src2 > 0
		    && ssa_instr->src2 < program->num_values
		    && value_types_conflicted[ssa_instr->src2]
		    && !value_is_tagged[ssa_instr->src2])
		|| (ssa_instr->src3 > 0
		    && ssa_instr->src3 < program->num_values
		    && value_types_conflicted[ssa_instr->src3]
		    && !value_is_tagged[ssa_instr->src3]);
	    int uses_tagged = (ssa_instr->src1 > 0
			       && ssa_instr->src1 < program->num_values
			       && value_is_tagged[ssa_instr->src1])
		|| (ssa_instr->src2 > 0
		    && ssa_instr->src2 < program->num_values
		    && value_is_tagged[ssa_instr->src2])
		|| (ssa_instr->src3 > 0
		    && ssa_instr->src3 < program->num_values
		    && value_is_tagged[ssa_instr->src3]);

	    memset(instr, 0, sizeof(JITInstruction));
	    instr->kind = ssa_instr->kind;
	    instr->resume_key = ssa_instr->resume_key;
	    instr->source_lineno = ssa_instr->source_lineno;
	    instr->bytecode_pc = ssa_instr->bytecode_pc;
	    instr->error_block = ssa_instr->error_label > 0 && cfg_block
		&& cfg_block->num_successors > 0
		? cfg_block->successors[0]->id : 0;
	    instr->label = ssa_instr->label;
	    if (ssa_instr->bytecode_pc != NO_BYTECODE_PC)
		program->num_resume_anchors++;
	    instr->value = ssa_instr->value;
	    instr->src1 = ssa_instr->src1;
	    instr->src2 = ssa_instr->src2;
	    instr->src3 = ssa_instr->src3;
	    instr->local_id = ssa_instr->local_id;
	    instr->func = ssa_instr->func;
	    instr->op = ssa_instr->op;
	    if (((ssa_instr->src1 > 0
		  && ssa_instr->src1 < program->num_values
		  && value_types[ssa_instr->src1] == TYPE_NONE
		  && !value_is_tagged[ssa_instr->src1])
		 || (ssa_instr->src2 > 0
		     && ssa_instr->src2 < program->num_values
		     && value_types[ssa_instr->src2] == TYPE_NONE
		     && !value_is_tagged[ssa_instr->src2]))
		&& (ssa_instr->kind == HIR_TAC_UNARY
		    || ssa_instr->kind == HIR_TAC_BINARY
		    || ssa_instr->kind == HIR_TAC_BRANCH_FALSE
		    || ssa_instr->kind == HIR_TAC_RETURN))
		instr->kind = HIR_TAC_DEOPT;
	    if (uses_conflicted && (ssa_instr->kind == HIR_TAC_UNARY
				    || ssa_instr->kind == HIR_TAC_BINARY
				    || ssa_instr->kind == HIR_TAC_RETURN
				    || ssa_instr->kind == HIR_TAC_BRANCH_FALSE))
		instr->kind = HIR_TAC_DEOPT;
	    if (uses_tagged && !jit_tagged_consumer_is_supported(ssa_instr)
		&& (ssa_instr->kind == HIR_TAC_UNARY
		    || ssa_instr->kind == HIR_TAC_BINARY
		    || ssa_instr->kind == HIR_TAC_RETURN
		    || ssa_instr->kind == HIR_TAC_CALL
		    || ssa_instr->kind == HIR_TAC_CALL_VERB
		    || ssa_instr->kind == HIR_TAC_BRANCH_FALSE))
		instr->kind = HIR_TAC_DEOPT;
	    if (!uses_tagged && ssa_instr->kind == HIR_TAC_UNARY
		&& (ssa_instr->op == HIR_OP_COMPLEMENT
		    || ssa_instr->op == HIR_OP_NEGATE || ssa_instr->op == HIR_OP_ABS)) {
		int src1_known = ssa_instr->src1 > 0
		    && ssa_instr->src1 < program->num_values
		    && value_types_known[ssa_instr->src1];
		var_type t1 = src1_known ? value_types[ssa_instr->src1] : TYPE_INT;

		if (ssa_instr->op == HIR_OP_COMPLEMENT) {
		    if (src1_known && t1 != TYPE_INT)
			instr->kind = HIR_TAC_DEOPT;
		} else {
		    if (src1_known && t1 != TYPE_INT && t1 != TYPE_FLOAT)
			instr->kind = HIR_TAC_DEOPT;
		}
	    }
	    if (ssa_instr->kind == HIR_TAC_BINARY
		&& (ssa_instr->op == HIR_OP_ADD || ssa_instr->op == HIR_OP_SUB
		    || ssa_instr->op == HIR_OP_MUL || ssa_instr->op == HIR_OP_DIV
		    || ssa_instr->op == HIR_OP_MOD || ssa_instr->op == HIR_OP_EXP)) {
		int src1_known = ssa_instr->src1 > 0
		    && ssa_instr->src1 < program->num_values
		    && value_types_known[ssa_instr->src1];
		int src2_known = ssa_instr->src2 > 0
		    && ssa_instr->src2 < program->num_values
		    && value_types_known[ssa_instr->src2];
		var_type t1 = src1_known ? value_types[ssa_instr->src1] : TYPE_INT;
		var_type t2 = src2_known ? value_types[ssa_instr->src2] : TYPE_INT;
		int object_range_add = ssa_instr->op == HIR_OP_ADD
		    && ssa_instr->bytecode_pc != NO_BYTECODE_PC
		    && bytecode_program->main_vector.vector[ssa_instr->bytecode_pc]
		       == OP_FOR_RANGE
		    && t1 == TYPE_OBJ && t2 == TYPE_INT;

		if (!uses_tagged && (src1_known || src2_known)
		    && !object_range_add
		    && !binary_type_pair_is_valid(ssa_instr->op, t1, t2))
		    instr->kind = HIR_TAC_DEOPT;
	    }
	    if (ssa_instr->kind == HIR_TAC_BINARY
		&& (ssa_instr->op == HIR_OP_MIN || ssa_instr->op == HIR_OP_MAX)
		&& (value_is_tagged[ssa_instr->value]
		    || value_types[ssa_instr->value] != TYPE_INT
		    || value_types[ssa_instr->src1] != TYPE_INT
		    || value_types[ssa_instr->src2] != TYPE_INT))
		instr->kind = HIR_TAC_DEOPT;
	    if (!uses_tagged && ssa_instr->kind == HIR_TAC_BINARY
		&& (ssa_instr->op == HIR_OP_EQ || ssa_instr->op == HIR_OP_NE
		    || ssa_instr->op == HIR_OP_LT || ssa_instr->op == HIR_OP_LE
		    || ssa_instr->op == HIR_OP_GT || ssa_instr->op == HIR_OP_GE
		    || ssa_instr->op == HIR_OP_BITOR || ssa_instr->op == HIR_OP_BITXOR
		    || ssa_instr->op == HIR_OP_BITAND || ssa_instr->op == HIR_OP_SHL
		    || ssa_instr->op == HIR_OP_SHR || ssa_instr->op == HIR_OP_LSHR)) {
		int src1_known = ssa_instr->src1 > 0
		    && ssa_instr->src1 < program->num_values
		    && value_types_known[ssa_instr->src1];
		int src2_known = ssa_instr->src2 > 0
		    && ssa_instr->src2 < program->num_values
		    && value_types_known[ssa_instr->src2];
		var_type t1 = src1_known ? value_types[ssa_instr->src1] : TYPE_INT;
		var_type t2 = src2_known ? value_types[ssa_instr->src2] : TYPE_INT;

		if (ssa_instr->op == HIR_OP_EQ || ssa_instr->op == HIR_OP_NE) {
		    if ((src1_known || src2_known)
			&& !(t1 == TYPE_INT && t2 == TYPE_INT)
			&& !(t1 == TYPE_OBJ && t2 == TYPE_OBJ)
			&& !(t1 == TYPE_FLOAT && t2 == TYPE_FLOAT)
			&& !(t1 == TYPE_STR && t2 == TYPE_STR)
			&& !(t1 == TYPE_LIST && t2 == TYPE_LIST))
			instr->kind = HIR_TAC_DEOPT;
		} else if (ssa_instr->op == HIR_OP_LT || ssa_instr->op == HIR_OP_LE
			   || ssa_instr->op == HIR_OP_GT || ssa_instr->op == HIR_OP_GE) {
		    if ((src1_known || src2_known)
			&& !(t1 == TYPE_INT && t2 == TYPE_INT)
			&& !(t1 == TYPE_FLOAT && t2 == TYPE_FLOAT)
			&& !(t1 == TYPE_STR && t2 == TYPE_STR))
			instr->kind = HIR_TAC_DEOPT;
		} else {
		    if ((src1_known || src2_known)
			&& !(t1 == TYPE_INT && t2 == TYPE_INT))
			instr->kind = HIR_TAC_DEOPT;
		}
	    }
	    instr->deopt_map = jit_instr_can_materialize(instr)
		? jit_add_deopt_map(program, ssa_instr,
				    &bytecode_program->main_vector,
				    value_types, value_is_tagged)
		: 0;
	    if (instr->deopt_map < 0) {
		myfree(instr, M_PROGRAM);
		myfree(value_types_conflicted, M_PROGRAM);
		myfree(value_types_known, M_PROGRAM);
		myfree(value_is_tagged, M_PROGRAM);
		myfree(value_types, M_PROGRAM);
		jit_program_free(program);
		return jit_program_unsupported_with_diagnostic("invalid-deopt-map",
							       "deopt-map: map allocation or stack value failed");
	    }
	    if (instr->deopt_map > 0 && instr->error_block > 0)
		program->deopt_maps[instr->deopt_map].native_error_block
		    = instr->error_block;
	    if (ssa_instr->kind == HIR_TAC_BINARY
		&& (ssa_instr->op == HIR_OP_DIV || ssa_instr->op == HIR_OP_MOD
		    || ssa_instr->op == HIR_OP_EXP || ssa_instr->op == HIR_OP_SHL
		    || ssa_instr->op == HIR_OP_SHR || ssa_instr->op == HIR_OP_LSHR
		    || ssa_instr->op == HIR_OP_INDEX))
		program->may_error = 1;
	    instr->literal_type = ssa_instr->kind == HIR_TAC_CONST
		? ssa_instr->literal.type
		: (ssa_instr->kind == HIR_TAC_LOAD_LOCAL
		   && ssa_instr->value > 0
		   && ssa_instr->value < program->num_values
		   ? value_types[ssa_instr->value]
		   : (ssa_instr->kind == HIR_TAC_RETURN
		      && ssa_instr->src1 > 0
		      && ssa_instr->src1 < program->num_values
		      ? value_types[ssa_instr->src1] : TYPE_INT));
	    if (ssa_instr->kind == HIR_TAC_UNARY
		&& ssa_instr->op == HIR_OP_TYPEOF
		&& ssa_instr->src1 > 0
		&& ssa_instr->src1 < program->num_values)
		instr->literal = value_types[ssa_instr->src1];
	    if (ssa_instr->kind == HIR_TAC_CONST) {
		if (ssa_instr->literal.type == TYPE_STR) {
		    const char *str = str_ref(ssa_instr->literal.v.str);
		    instr->literal = (uintptr_t) str;
		}
		else if (ssa_instr->literal.type == TYPE_LIST) {
		    if (ssa_instr->literal.v.list == 0) {
			Var empty = new_list(0);
			instr->literal = (uintptr_t) empty.v.list;
		    } else {
			Var list_var = var_ref(ssa_instr->literal);
			instr->literal = (uintptr_t) list_var.v.list;
		    }
		}
		else if (ssa_instr->literal.type == TYPE_OBJ)
		    instr->literal = ssa_instr->literal.v.obj;
		else if (ssa_instr->literal.type == TYPE_ERR)
		    instr->literal = ssa_instr->literal.v.err;
		else if (ssa_instr->literal.type == TYPE_INT)
		    instr->literal = ssa_instr->literal.v.num;
		else if (ssa_instr->literal.type == TYPE_CATCH
			 || ssa_instr->literal.type == TYPE_FINALLY)
		    instr->literal = ssa_instr->literal.v.num;
		else if (ssa_instr->literal.type == TYPE_FLOAT) {
		    FlNum f = fl_unbox(ssa_instr->literal.v.fnum);
		    memcpy(&instr->literal, &f, sizeof(Num));
		}
		else
		    instr->literal = 0;
	    }
	    for (ssa_copy = ssa_instr->copies; ssa_copy;
		 ssa_copy = ssa_copy->next) {
		JITCopy *copy = mymalloc(sizeof(JITCopy), M_PROGRAM);
		JITCopy **tail = &instr->copies;
		copy->dst = ssa_copy->dst;
		copy->src = ssa_copy->src;
		copy->next = 0;
		while (*tail)
		    tail = &(*tail)->next;
		*tail = copy;
	    }
	    if (block->last)
		block->last->next = instr;
	    else
		block->first = instr;
	    block->last = instr;
	    if (ssa_instr == ssa_block->last)
		break;
	}
    }

    myfree(value_types_conflicted, M_PROGRAM);
    myfree(value_types_known, M_PROGRAM);
    program->value_types = value_types;
    program->value_is_tagged = value_is_tagged;
    jit_build_tag_slots(program);
    jit_build_value_ownership(program);
    jit_build_int_list_values(program);
    jit_build_direct_int_list_updates(program);
    jit_coalesce_deopt_locals(program);
    if (!jit_deopt_maps_are_valid(ctx, program, bytecode_program)) {
	const char *diag = hir_context_error_message(ctx);
	JITProgram *unsupported;

	unsupported = jit_program_unsupported_with_diagnostic("invalid-deopt-map",
							 diag);
	jit_program_free(program);
	return unsupported;
    }
    jit_build_deopt_tag_values(program);
    jit_build_resume_liveness(program);
    return program;
}
#endif /* ENABLE_JIT && !HIR_TESTING */

#if defined(HIR_DUMP_TAC) || defined(HIR_DUMP_SSA)
static const char *tac_kind_name(HIRTacKind);
static const char *op_name(HIROp);
static void dump_var(FILE *, Var);
#endif

#ifdef HIR_DUMP_TAC
void
hir_dump_tac(HIRTacProgram *program)
{
    HIRTacInstr *instr;

    fprintf(stderr, "HIR TAC BEGIN\n");
    if (!program) {
	fprintf(stderr, "HIR TAC END\n");
	return;
    }

    for (instr = program->first; instr; instr = instr->next) {
	fprintf(stderr, "  line %-5u %-14s", instr->source_lineno,
		tac_kind_name(instr->kind));

	switch (instr->kind) {
	case HIR_TAC_TICK:
	case HIR_TAC_DEOPT:
	    break;
	case HIR_TAC_CONST:
	    fprintf(stderr, " t%d = ", instr->dst);
	    dump_var(stderr, instr->literal);
	    break;
	case HIR_TAC_LOAD_LOCAL:
	    fprintf(stderr, " t%d = local[%d]", instr->dst, instr->local_id);
	    break;
	case HIR_TAC_STORE_LOCAL:
	    fprintf(stderr, " local[%d] = t%d", instr->local_id, instr->src1);
	    break;
	case HIR_TAC_INDEX_SET:
	    fprintf(stderr, " t%d = local[%d] = index_set(t%d, t%d, t%d)",
		    instr->dst, instr->local_id, instr->src1, instr->src2,
		    instr->src3);
	    break;
	case HIR_TAC_UNARY:
	    fprintf(stderr, " t%d = %s t%d", instr->dst,
		    op_name(instr->op), instr->src1);
	    break;
	case HIR_TAC_BINARY:
	    fprintf(stderr, " t%d = t%d %s t%d", instr->dst, instr->src1,
		    op_name(instr->op), instr->src2);
	    break;
	case HIR_TAC_LABEL:
	    fprintf(stderr, " L%d:", instr->label);
	    break;
	case HIR_TAC_JUMP:
	    fprintf(stderr, " L%d", instr->label);
	    break;
	case HIR_TAC_BRANCH_FALSE:
	    fprintf(stderr, " if_false t%d goto L%d", instr->src1,
		    instr->label);
	    break;
	case HIR_TAC_RETURN:
	    fprintf(stderr, " t%d", instr->src1);
	    break;
	case HIR_TAC_RETURN0:
	    break;
	case HIR_TAC_CALL:
	    fprintf(stderr, " t%d = call func(%u) t%d", instr->dst,
		    instr->func, instr->src1);
	    break;
	case HIR_TAC_CALL_VERB:
	    fprintf(stderr, " t%d = call_verb(t%d, t%d)", instr->dst,
		    instr->src1, instr->src2);
	    break;
	case HIR_TAC_PUT_PROP:
	    fprintf(stderr, " t%d = prop_put(t%d, t%d)", instr->dst,
		    instr->src1, instr->src2);
	    break;
	case HIR_TAC_RANGE_REF:
	    fprintf(stderr, " t%d = range_ref(t%d, t%d)", instr->dst,
		    instr->src1, instr->src2);
	    break;
	case HIR_TAC_RANGE_SET:
	    fprintf(stderr, " t%d = range_set(t%d, t%d)", instr->dst,
		    instr->src1, instr->src2);
	    break;
	case HIR_TAC_UNSUPPORTED:
	    fprintf(stderr, " t%d", instr->dst);
	    break;
	case HIR_TAC_PHI:
	    fprintf(stderr, " t%d = phi(...)", instr->dst);
	    break;
	case HIR_TAC_PARALLEL_COPY:
	    fprintf(stderr, " parallel_copy");
	    break;
	}

	fprintf(stderr, "\n");
    }

    fprintf(stderr, "HIR TAC END\n");
}
#endif

#ifdef HIR_DUMP_SSA
static void
dump_ssa_block_list(FILE *file, HIRCFG *cfg, HIRSSABlock *block,
		    int predecessors)
{
    HIRBasicBlock *cfg_block;
    int max_block_id;
    int printed = 0;
    int i;

    fprintf(file, "[");
    if (!cfg || !block) {
	fprintf(file, "]");
	return;
    }

    cfg_block = cfg_block_for_id(cfg, block->id);
    max_block_id = max_cfg_block_id(cfg);
    for (i = 1; i <= max_block_id; i++) {
	HIRBasicBlock *candidate = cfg_block_for_id(cfg, i);
	int has_edge = 0;
	int j;

	if (!candidate)
	    continue;
	if (predecessors) {
	    if (!cfg_block)
		continue;
	    for (j = 0; j < candidate->num_successors; j++) {
		if (candidate->successors[j] == cfg_block) {
		    has_edge = 1;
		    break;
		}
	    }
	} else if (cfg_block) {
	    for (j = 0; j < cfg_block->num_successors; j++) {
		if (cfg_block->successors[j] == candidate) {
		    has_edge = 1;
		    break;
		}
	    }
	}

	if (has_edge) {
	    fprintf(file, "%sB%d", printed ? "," : "", i);
	    printed = 1;
	}
    }
    fprintf(file, "]");
}

static void
dump_ssa_phi_args(FILE *file, HIRSSAProgram *ssa, HIRSSAInstr *instr)
{
    int max_block_id = ssa && ssa->cfg ? max_cfg_block_id(ssa->cfg) : 0;
    int printed = 0;
    int i;

    fprintf(file, "[");
    for (i = 1; i <= max_block_id; i++) {
	HIRPhiArg *arg;

	for (arg = instr->phi_args; arg; arg = arg->next) {
	    if (arg->block_id == i) {
		fprintf(file, "%sB%d:t%d", printed ? ", " : "", arg->block_id,
			arg->value);
		printed = 1;
		break;
	    }
	}
    }
    fprintf(file, "]");
}

void
hir_dump_ssa_to_file(FILE *file, HIRSSAProgram *ssa)
{
    HIRSSABlock *block;

    if (!file)
	return;

    fprintf(file, "HIR SSA BEGIN\n");
    if (!ssa) {
	fprintf(file, "HIR SSA END\n");
	return;
    }

    fprintf(file, "form=%s blocks=%d instructions=%d values=%d\n",
	    ssa->form == HIR_FORM_OUT_OF_SSA ? "out-of-ssa" : "ssa",
	    ssa->num_blocks, ssa->num_instructions, ssa->num_values);

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	fprintf(file, "B%d lines=%u..%u preds=", block->id,
		block->first_lineno, block->last_lineno);
	dump_ssa_block_list(file, ssa->cfg, block, 1);
	fprintf(file, " succs=");
	dump_ssa_block_list(file, ssa->cfg, block, 0);
	fprintf(file, "\n");

	for (instr = block->first; instr; instr = instr->next) {
	    fprintf(file, "  line %-5u %-14s", instr->source_lineno,
		    tac_kind_name(instr->kind));

	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_DEOPT:
		break;
	    case HIR_TAC_CONST:
		fprintf(file, " t%d = ", instr->value);
		dump_var(file, instr->literal);
		break;
	    case HIR_TAC_LOAD_ERROR:
		fprintf(file, " t%d = current_error", instr->value);
		break;
	    case HIR_TAC_LOAD_LOCAL:
		fprintf(file, " t%d = local[%d]", instr->value,
			instr->local_id);
		break;
	    case HIR_TAC_STORE_LOCAL:
		fprintf(file, " local[%d] = t%d", instr->local_id,
			instr->src1);
		break;
	    case HIR_TAC_INDEX_SET:
		fprintf(file, " t%d = local[%d] = index_set(t%d, t%d, t%d)",
			instr->value, instr->local_id, instr->src1, instr->src2,
			instr->src3);
		break;
	    case HIR_TAC_UNARY:
		fprintf(file, " t%d = %s t%d", instr->value,
			op_name(instr->op), instr->src1);
		break;
	    case HIR_TAC_BINARY:
		fprintf(file, " t%d = t%d %s t%d", instr->value,
			instr->src1, op_name(instr->op), instr->src2);
		break;
	    case HIR_TAC_LABEL:
		fprintf(file, " L%d:", instr->label);
		break;
	    case HIR_TAC_JUMP:
		fprintf(file, " L%d", instr->label);
		break;
	    case HIR_TAC_BRANCH_FALSE:
		fprintf(file, " if_false t%d goto L%d", instr->src1,
			instr->label);
		break;
	    case HIR_TAC_RETURN:
		fprintf(file, " t%d", instr->src1);
		break;
	    case HIR_TAC_RETURN0:
		break;
	    case HIR_TAC_CALL:
		fprintf(file, " t%d = call func(%u) t%d", instr->value,
			instr->func, instr->src1);
		break;
	    case HIR_TAC_CALL_VERB:
		fprintf(file, " t%d = call_verb(t%d, t%d)", instr->value,
			instr->src1, instr->src2);
		break;
	    case HIR_TAC_PUT_PROP:
		fprintf(file, " t%d = prop_put(t%d, t%d)", instr->value,
			instr->src1, instr->src2);
		break;
	    case HIR_TAC_RANGE_REF:
		fprintf(file, " t%d = range_ref(t%d, t%d)", instr->value,
			instr->src1, instr->src2);
		break;
	    case HIR_TAC_RANGE_SET:
		fprintf(file, " t%d = range_set(t%d, t%d)", instr->value,
			instr->src1, instr->src2);
		break;
	    case HIR_TAC_UNSUPPORTED:
		if (instr->value > 0)
		    fprintf(file, " t%d", instr->value);
		break;
	    case HIR_TAC_PHI:
		fprintf(file, " t%d = phi local[%d] ", instr->value,
			instr->local_id);
		dump_ssa_phi_args(file, ssa, instr);
		break;
	    case HIR_TAC_PARALLEL_COPY:
		{
		    HIRParallelCopy *copy;
		    int printed = 0;

		    fprintf(file, " [");
		    for (copy = instr->copies; copy; copy = copy->next) {
			fprintf(file, "%st%d=t%d", printed ? ", " : "",
				copy->dst, copy->src);
			printed = 1;
		    }
		    fprintf(file, "]");
		}
		break;
	    }

	    fprintf(file, "\n");
	    if (instr == block->last)
		break;
	}
    }

    fprintf(file, "HIR SSA END\n");
}

void
hir_dump_ssa(HIRSSAProgram *ssa)
{
    hir_dump_ssa_to_file(stderr, ssa);
}
#endif

#if defined(HIR_DUMP_TAC) || defined(HIR_DUMP_SSA)
static const char *
tac_kind_name(HIRTacKind kind)
{
    switch (kind) {
    case HIR_TAC_TICK:
	return "tick";
    case HIR_TAC_DEOPT:
	return "deopt";
    case HIR_TAC_CONST:
	return "const";
    case HIR_TAC_LOAD_ERROR:
	return "load_error";
    case HIR_TAC_LOAD_LOCAL:
	return "load_local";
    case HIR_TAC_STORE_LOCAL:
	return "store_local";
    case HIR_TAC_INDEX_SET:
	return "index_set";
    case HIR_TAC_UNARY:
	return "unary";
    case HIR_TAC_BINARY:
	return "binary";
    case HIR_TAC_LABEL:
	return "label";
    case HIR_TAC_JUMP:
	return "jump";
    case HIR_TAC_BRANCH_FALSE:
	return "branch_false";
    case HIR_TAC_RETURN:
	return "return";
    case HIR_TAC_RETURN0:
	return "return0";
    case HIR_TAC_CALL:
	return "call";
    case HIR_TAC_CALL_VERB:
	return "call_verb";
    case HIR_TAC_PUT_PROP:
	return "put_prop";
    case HIR_TAC_RANGE_REF:
	return "range_ref";
    case HIR_TAC_RANGE_SET:
	return "range_set";
    case HIR_TAC_UNSUPPORTED:
	    return "unsupported";
    case HIR_TAC_PHI:
	    return "phi";
    case HIR_TAC_PARALLEL_COPY:
	    return "parallel_copy";
    }

    return "unknown";
}

static const char *
op_name(HIROp op)
{
    switch (op) {
    case HIR_OP_NEGATE:
	return "neg";
    case HIR_OP_NOT:
	return "not";
    case HIR_OP_COMPLEMENT:
	return "bitnot";
    case HIR_OP_ADD:
	return "+";
    case HIR_OP_SUB:
	return "-";
    case HIR_OP_MUL:
	return "*";
    case HIR_OP_DIV:
	return "/";
    case HIR_OP_MOD:
	return "%";
    case HIR_OP_EXP:
	return "^";
    case HIR_OP_EQ:
	return "==";
    case HIR_OP_NE:
	return "!=";
    case HIR_OP_LT:
	return "<";
    case HIR_OP_LE:
	return "<=";
    case HIR_OP_GT:
	return ">";
    case HIR_OP_GE:
	return ">=";
    case HIR_OP_IN:
	return "in";
    case HIR_OP_AND:
	return "&&";
    case HIR_OP_OR:
	return "||";
    case HIR_OP_BITOR:
	return "|";
    case HIR_OP_BITXOR:
	return "xor";
    case HIR_OP_BITAND:
	return "&";
    case HIR_OP_SHL:
	return "<<";
    case HIR_OP_SHR:
	return ">>";
    case HIR_OP_LSHR:
	return ">>>";
    case HIR_OP_INDEX:
	return "INDEX";
    case HIR_OP_MAKE_SINGLETON_LIST:
	return "MAKE_SINGLETON_LIST";
    case HIR_OP_CHECK_LIST_FOR_SPLICE:
	return "CHECK_LIST_FOR_SPLICE";
    case HIR_OP_LIST_ADD_TAIL:
	return "LIST_ADD_TAIL";
    case HIR_OP_LIST_APPEND:
	return "LIST_APPEND";
    case HIR_OP_ABS:
	return "ABS";
    case HIR_OP_MIN:
	return "MIN";
    case HIR_OP_MAX:
	return "MAX";
    case HIR_OP_TOINT:
	return "TOINT";
    case HIR_OP_TYPEOF:
	return "TYPEOF";
    case HIR_OP_LENGTH:
	return "LENGTH";
    case HIR_OP_GET_PROP:
	return "GET_PROP";
    case HIR_OP_SCATTER:
	return "SCATTER";
    case HIR_OP_CHARGE_TICK:
	return "CHARGE_TICK";
    case HIR_OP_TICKS_LEFT:
	return "TICKS_LEFT";
    case HIR_OP_SECONDS_LEFT:
	return "SECONDS_LEFT";
    case HIR_OP_TIME:
	return "TIME";
    case HIR_OP_INDEX_BF:
	return "INDEX";
    case HIR_OP_RINDEX_BF:
	return "RINDEX";
    case HIR_OP_VALID:
	return "VALID";
    case HIR_OP_PARENT:
	return "PARENT";
    case HIR_OP_SUBLIST_FROM:
	return "SUBLIST_FROM";
    case HIR_OP_FORK:
	return "FORK";
    }

    return "?";
}

static void
dump_var(FILE *file, Var var)
{
    switch (var.type) {
    case TYPE_INT:
	fprintf(file, "%" PRIdN, var.v.num);
	break;
    case TYPE_OBJ:
	fprintf(file, "#%" PRIdN, var.v.obj);
	break;
    case TYPE_STR:
	fprintf(file, "\"%s\"", var.v.str);
	break;
    case TYPE_ERR:
	fprintf(file, "error(%d)", var.v.err);
	break;
    case TYPE_FLOAT:
	fprintf(file, "float");
	break;
    case TYPE_LIST:
	fprintf(file, "list");
	break;
    default:
	fprintf(file, "type(%d)", var.type);
	break;
    }
}
#endif

#ifdef HIR_TESTING
int
hir_tac_count_kind(HIRTacProgram *program, HIRTacKind kind)
{
    HIRTacInstr *instr;
    int count = 0;

    if (!program)
	return 0;

    for (instr = program->first; instr; instr = instr->next) {
	if (instr->kind == kind)
	    count++;
    }

    return count;
}

int
hir_tac_count_unary_op(HIRTacProgram *program, HIROp op)
{
    HIRTacInstr *instr;
    int count = 0;

    if (!program)
	return 0;

    for (instr = program->first; instr; instr = instr->next) {
	if (instr->kind == HIR_TAC_UNARY && instr->op == op)
	    count++;
    }

    return count;
}

int
hir_tac_count_binary_op(HIRTacProgram *program, HIROp op)
{
    HIRTacInstr *instr;
    int count = 0;

    if (!program)
	return 0;

    for (instr = program->first; instr; instr = instr->next) {
	if (instr->kind == HIR_TAC_BINARY && instr->op == op)
	    count++;
    }

    return count;
}

int
hir_tac_instruction_count(HIRTacProgram *program)
{
    HIRTacInstr *instr;
    int count = 0;

    if (!program)
	return 0;

    for (instr = program->first; instr; instr = instr->next)
	count++;

    return count;
}

int
hir_tac_count_lineno(HIRTacProgram *program, unsigned lineno)
{
    HIRTacInstr *instr;
    int count = 0;

    if (!program)
	return 0;

    for (instr = program->first; instr; instr = instr->next) {
	if (instr->source_lineno == lineno)
	    count++;
    }

    return count;
}

int
hir_tac_count_bytecode_pc(HIRTacProgram *program, unsigned bytecode_pc)
{
    HIRTacInstr *instr;
    int count = 0;

    for (instr = program ? program->first : 0; instr; instr = instr->next)
	if (instr->bytecode_pc == bytecode_pc)
	    count++;
    return count;
}

int
hir_tac_stack_depth_at_bytecode_pc(HIRTacProgram *program,
				   unsigned bytecode_pc)
{
    HIRTacInstr *instr;

    for (instr = program ? program->first : 0; instr; instr = instr->next)
	if (instr->bytecode_pc == bytecode_pc)
	    return instr->num_stack_values;
    return -1;
}

int
hir_tac_stack_depth_mismatch_count(HIRTacProgram *program,
				   unsigned bytecode_pc, int expected_depth)
{
	HIRTacInstr *instr;
	int count = 0;

	for (instr = program ? program->first : 0; instr; instr = instr->next)
		if (instr->bytecode_pc == bytecode_pc
		    && instr->num_stack_values != expected_depth)
			count++;
	return count;
}

int
hir_ssa_count_bytecode_pc(HIRSSAProgram *program, unsigned bytecode_pc)
{
    HIRSSABlock *block;
    int count = 0;

    for (block = program ? program->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->bytecode_pc == bytecode_pc)
		count++;
	    if (instr == block->last)
		break;
	}
    }
    return count;
}

int
hir_ssa_stack_depth_at_bytecode_pc(HIRSSAProgram *program,
				   unsigned bytecode_pc)
{
    HIRSSABlock *block;

    for (block = program ? program->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->bytecode_pc == bytecode_pc)
		return instr->num_stack_values;
	    if (instr == block->last)
		break;
	}
    }
    return -1;
}

int
hir_ssa_stack_value_at_bytecode_pc(HIRSSAProgram *program,
				   unsigned bytecode_pc, int stack_slot)
{
    HIRSSABlock *block;

    for (block = program ? program->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->bytecode_pc == bytecode_pc
		&& stack_slot >= 0 && stack_slot < instr->num_stack_values)
		return instr->stack_values[stack_slot];
	    if (instr == block->last)
		break;
	}
    }
    return -1;
}

int
hir_ssa_binary_value_at_bytecode_pc(HIRSSAProgram *program,
				    unsigned bytecode_pc, HIROp op)
{
    HIRSSABlock *block;

    for (block = program ? program->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_BINARY && instr->op == op
		&& instr->bytecode_pc == bytecode_pc)
		return instr->value;
	    if (instr == block->last)
		break;
	}
    }
    return -1;
}

int
hir_ssa_local_value_at_bytecode_pc(HIRSSAProgram *program,
				   unsigned bytecode_pc, int local_id)
{
    HIRSSABlock *block;

    for (block = program ? program->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->bytecode_pc == bytecode_pc
		&& local_id >= 0 && local_id < instr->num_local_values)
		return instr->local_values[local_id];
	    if (instr == block->last)
		break;
	}
    }
    return -1;
}

int
hir_ssa_local_snapshot_count(HIRSSAProgram *program)
{
    HIRSSABlock *block;
    int count = 0;

    for (block = program ? program->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->num_local_values > 0)
		count++;
	    if (instr == block->last)
		break;
	}
    }
    return count;
}

int
hir_cfg_block_count(HIRCFG *cfg)
{
    return cfg ? cfg->num_blocks : 0;
}

int
hir_cfg_edge_count(HIRCFG *cfg)
{
    return cfg ? cfg->num_edges : 0;
}

int
hir_cfg_unsupported_block_count(HIRCFG *cfg)
{
    HIRBasicBlock *block;
    int count = 0;

    if (!cfg)
	return 0;

    for (block = cfg->blocks; block; block = block->next) {
	if (block->contains_unsupported)
	    count++;
    }

    return count;
}

int
hir_cfg_critical_edge_count(HIRCFG *cfg)
{
    return cfg_critical_edge_count(cfg);
}

int
hir_dom_reachable_block_count(HIRDominatorTree *dom)
{
    return dom ? dom->num_reachable : 0;
}

int
hir_dom_idom_block(HIRDominatorTree *dom, int block_id)
{
    if (!dom || block_id <= 0 || block_id > dom->max_block_id
	|| !dom->idom[block_id])
	return 0;

    return dom->idom[block_id]->id;
}

int
hir_dom_df_count(HIRDominatorTree *dom, int block_id)
{
    HIRBlockList *node;
    int count = 0;

    if (!dom || block_id <= 0 || block_id > dom->max_block_id)
	return 0;

    for (node = dom->df[block_id]; node; node = node->next)
	count++;

    return count;
}

int
hir_ssa_block_count(HIRSSAProgram *ssa)
{
    return ssa ? ssa->num_blocks : 0;
}

int
hir_ssa_instruction_count(HIRSSAProgram *ssa)
{
    return ssa ? ssa->num_instructions : 0;
}

int
hir_ssa_value_count(HIRSSAProgram *ssa)
{
    return ssa ? ssa->num_values : 0;
}

int
hir_ssa_count_kind(HIRSSAProgram *ssa, HIRTacKind kind)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == kind)
		count++;
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

int
hir_ssa_out_of_range_load_count(HIRSSAProgram *ssa, int num_vars)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;
    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_LOAD_LOCAL
		&& (instr->local_id < 0 || instr->local_id >= num_vars))
		count++;
	    if (instr == block->last)
		break;
	}
    }
    return count;
}

int
hir_ssa_phi_arg_count(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_PHI) {
		HIRPhiArg *arg;

		for (arg = instr->phi_args; arg; arg = arg->next)
		    count++;
	    }
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

int
hir_ssa_zero_phi_arg_count(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_PHI) {
		HIRPhiArg *arg;

		for (arg = instr->phi_args; arg; arg = arg->next) {
		    if (arg->value == 0)
			count++;
		}
	    }
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

static int
ssa_value_is_phi(HIRSSAProgram *ssa, int value)
{
    HIRSSABlock *block;

    if (!ssa || value <= 0)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_PHI && instr->value == value)
		return 1;
	    if (instr == block->last)
		break;
	}
    }

    return 0;
}

int
hir_ssa_return_uses_phi_count(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_RETURN
		&& ssa_value_is_phi(ssa, instr->src1))
		count++;
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

int
hir_ssa_branch_uses_phi_count(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_BRANCH_FALSE
		&& ssa_value_is_phi(ssa, instr->src1))
		count++;
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

int
hir_ssa_binary_uses_phi_count(HIRSSAProgram *ssa, HIROp op)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_BINARY && instr->op == op
		&& (ssa_value_is_phi(ssa, instr->src1)
		    || ssa_value_is_phi(ssa, instr->src2)))
		count++;
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

int
hir_ssa_parallel_copy_pair_count(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;
    int count = 0;

    if (!ssa)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_PARALLEL_COPY) {
		HIRParallelCopy *copy;

		for (copy = instr->copies; copy; copy = copy->next)
		    count++;
	    }
	    if (instr == block->last)
		break;
	}
    }

    return count;
}

int
hir_ssa_form(HIRSSAProgram *ssa)
{
    return ssa ? (int) ssa->form : -1;
}

int
hir_ssa_cfg_block_count(HIRSSAProgram *ssa)
{
    return ssa ? hir_cfg_block_count(ssa->cfg) : 0;
}

int
hir_ssa_cfg_edge_count(HIRSSAProgram *ssa)
{
    return ssa ? hir_cfg_edge_count(ssa->cfg) : 0;
}

int
hir_ssa_cfg_critical_edge_count(HIRSSAProgram *ssa)
{
    return ssa ? hir_cfg_critical_edge_count(ssa->cfg) : 0;
}

HIRValueKind
hir_ssa_return_value_kind(HIRSSAProgram *ssa, HIRValueAnalysis *analysis)
{
    HIRSSABlock *block;

    for (block = ssa ? ssa->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_RETURN)
		return hir_value_kind(analysis, instr->src1);
	    if (instr == block->last)
		break;
	}
    }
    return HIR_VALUE_UNKNOWN;
}

Num
hir_ssa_return_constant(HIRSSAProgram *ssa, HIRValueAnalysis *analysis)
{
    HIRSSABlock *block;

    for (block = ssa ? ssa->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_RETURN)
		return hir_value_constant(analysis, instr->src1);
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

enum error
hir_ssa_return_error(HIRSSAProgram *ssa, HIRValueAnalysis *analysis)
{
    HIRSSABlock *block;

    for (block = ssa ? ssa->blocks : 0; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_RETURN)
		return hir_value_error(analysis, instr->src1);
	    if (instr == block->last)
		break;
	}
    }
    return E_NONE;
}
#endif

static void *
hir_alloc(HIRContext *ctx, size_t size)
{
    return arena_alloc(ctx->arena, size);
}

static void
record_unsupported(HIRContext *ctx, const char *message)
{
    ctx->error_count++;
    if (!ctx->error_msg)
	ctx->error_msg = message;
}

static void
record_unsupported_fmt(HIRContext *ctx, const char *fmt, ...)
{
    char buf[256];
    va_list args;

    va_start(args, fmt);
    vsnprintf(buf, sizeof(buf), fmt, args);
    va_end(args);

    char *copy = hir_alloc(ctx, strlen(buf) + 1);
    strcpy(copy, buf);
    record_unsupported(ctx, copy);
}

static HIRTypeTag
type_tag_for_var_type(var_type type)
{
    switch (type) {
    case TYPE_INT:
	return HIR_TYPE_INT;
    case TYPE_FLOAT:
	return HIR_TYPE_FLOAT;
    case TYPE_STR:
	return HIR_TYPE_STR;
    case TYPE_LIST:
	return HIR_TYPE_LIST;
    case TYPE_OBJ:
	return HIR_TYPE_OBJ;
    case TYPE_ERR:
	return HIR_TYPE_ERR;
    default:
	return HIR_TYPE_ANY;
    }
}

static HIRExpr *
new_expr(HIRContext *ctx, HIRExprKind kind)
{
    HIRExpr *expr = hir_alloc(ctx, sizeof(HIRExpr));

    expr->kind = kind;
    expr->type = HIR_TYPE_ANY;
    expr->source_lineno = 0;
    expr->bytecode_pc = NO_BYTECODE_PC;
    return expr;
}

static HIRStmt *
new_stmt(HIRContext *ctx, HIRStmtKind kind)
{
    HIRStmt *stmt = hir_alloc(ctx, sizeof(HIRStmt));

    stmt->kind = kind;
    stmt->source_lineno = 0;
    stmt->bytecode_pc = NO_BYTECODE_PC;
    stmt->next = 0;
    return stmt;
}

static HIRArg *
lift_arg_list(HIRContext *ctx, Arg_List *args)
{
    HIRArg *first = 0;
    HIRArg *last = 0;

    for (; args; args = args->next) {
	HIRArg *arg = hir_alloc(ctx, sizeof(HIRArg));

	arg->kind = args->kind;
	arg->expr = lift_expr(ctx, args->expr);
	arg->bytecode_pc = args->bytecode_pc;
	arg->next = 0;

	if (last)
	    last->next = arg;
	else
	    first = arg;
	last = arg;
    }

    return first;
}

static int
binary_op_for_expr(enum Expr_Kind kind, HIROp *op)
{
    switch (kind) {
    case EXPR_PLUS:
	*op = HIR_OP_ADD;
	return 1;
    case EXPR_MINUS:
	*op = HIR_OP_SUB;
	return 1;
    case EXPR_TIMES:
	*op = HIR_OP_MUL;
	return 1;
    case EXPR_DIVIDE:
	*op = HIR_OP_DIV;
	return 1;
    case EXPR_MOD:
	*op = HIR_OP_MOD;
	return 1;
    case EXPR_EXP:
	*op = HIR_OP_EXP;
	return 1;
    case EXPR_EQ:
	*op = HIR_OP_EQ;
	return 1;
    case EXPR_NE:
	*op = HIR_OP_NE;
	return 1;
    case EXPR_LT:
	*op = HIR_OP_LT;
	return 1;
    case EXPR_LE:
	*op = HIR_OP_LE;
	return 1;
    case EXPR_GT:
	*op = HIR_OP_GT;
	return 1;
    case EXPR_GE:
	*op = HIR_OP_GE;
	return 1;
    case EXPR_IN:
	*op = HIR_OP_IN;
	return 1;
    case EXPR_AND:
	*op = HIR_OP_AND;
	return 1;
    case EXPR_OR:
	*op = HIR_OP_OR;
	return 1;
    case EXPR_BITOR:
	*op = HIR_OP_BITOR;
	return 1;
    case EXPR_BITXOR:
	*op = HIR_OP_BITXOR;
	return 1;
    case EXPR_BITAND:
	*op = HIR_OP_BITAND;
	return 1;
    case EXPR_SHL:
	*op = HIR_OP_SHL;
	return 1;
    case EXPR_SHR:
	*op = HIR_OP_SHR;
	return 1;
    case EXPR_LSHR:
	*op = HIR_OP_LSHR;
	return 1;
    default:
	return 0;
    }
}

static const char *
ast_expr_kind_name(enum Expr_Kind kind)
{
    switch (kind) {
    case EXPR_VAR: return "var";
    case EXPR_ID: return "id";
    case EXPR_PROP: return "prop";
    case EXPR_VERB: return "verb";
    case EXPR_INDEX: return "index";
    case EXPR_RANGE: return "range";
    case EXPR_CALL: return "call";
    case EXPR_PLUS: return "plus";
    case EXPR_MINUS: return "minus";
    case EXPR_TIMES: return "times";
    case EXPR_DIVIDE: return "divide";
    case EXPR_MOD: return "mod";
    case EXPR_EXP: return "exp";
    case EXPR_NEGATE: return "negate";
    case EXPR_NOT: return "not";
    case EXPR_AND: return "and";
    case EXPR_OR: return "or";
    case EXPR_COND: return "cond";
    case EXPR_LIST: return "list";
    case EXPR_LENGTH: return "length";
    case EXPR_CATCH: return "catch";
    case EXPR_ASGN: return "asgn";
    case EXPR_SCATTER: return "scatter";
    case EXPR_EQ: return "eq";
    case EXPR_NE: return "ne";
    case EXPR_LT: return "lt";
    case EXPR_LE: return "le";
    case EXPR_GT: return "gt";
    case EXPR_GE: return "ge";
    case EXPR_IN: return "in";
    case EXPR_BITOR: return "bitor";
    case EXPR_BITXOR: return "bitxor";
    case EXPR_BITAND: return "bitand";
    case EXPR_COMPLEMENT: return "complement";
    case EXPR_SHL: return "shl";
    case EXPR_SHR: return "shr";
    case EXPR_LSHR: return "lshr";
    default: return "unknown";
    }
}

static HIRExpr *
unsupported_expr(HIRContext *ctx, Expr *ast)
{
    HIRExpr *expr = new_expr(ctx, HIR_EXPR_UNSUPPORTED);

    expr->source_lineno = ast ? ast->lineno : 0;
    expr->u.unsupported.expr_kind = ast ? ast->kind : SizeOf_Expr_Kind;
    record_unsupported_fmt(ctx, "ast-expr: %s", ast ? ast_expr_kind_name(ast->kind) : "unknown");
    return expr;
}

static HIRExpr *
lift_binary_expr(HIRContext *ctx, Expr *ast)
{
    HIROp op;
    HIRExpr *expr;

    if (!binary_op_for_expr(ast->kind, &op))
	return unsupported_expr(ctx, ast);

    expr = new_expr(ctx, HIR_EXPR_BINARY);
    expr->source_lineno = ast->lineno;
    expr->bytecode_pc = ast->bytecode_pc;
    expr->u.binary.op = op;
    expr->u.binary.lhs = lift_expr(ctx, ast->e.bin.lhs);
    expr->u.binary.rhs = lift_expr(ctx, ast->e.bin.rhs);

    return expr;
}

static HIRExpr *
lift_assignment(HIRContext *ctx, Expr *ast)
{
    if (ast->e.bin.lhs->kind == EXPR_ID) {
	HIRExpr *expr = new_expr(ctx, HIR_EXPR_LOCAL_STORE);

	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.local_store.local_id = ast->e.bin.lhs->e.id;
	expr->u.local_store.rhs = lift_expr(ctx, ast->e.bin.rhs);
	return expr;
    }
    if (ast->e.bin.lhs->kind == EXPR_SCATTER) {
	HIRScatter *first = 0;
	HIRScatter *last = 0;
	Scatter *sc;
	HIRExpr *expr = new_expr(ctx, HIR_EXPR_SCATTER);

	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.scatter.rhs = lift_expr(ctx, ast->e.bin.rhs);
	for (sc = ast->e.bin.lhs->e.scatter; sc; sc = sc->next) {
	    HIRScatter *item = hir_alloc(ctx, sizeof(HIRScatter));
	    item->kind = sc->kind;
	    item->local_id = sc->id;
	    item->expr = sc->expr ? lift_expr(ctx, sc->expr) : 0;
	    item->next = 0;
	    if (last)
		last->next = item;
	    else
		first = item;
	    last = item;
	}
	expr->u.scatter.items = first;
	return expr;
    }
    if (ast->e.bin.lhs->kind == EXPR_PROP) {
	HIRExpr *expr = new_expr(ctx, HIR_EXPR_PROP_STORE);

	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.prop_store.obj = lift_expr(ctx, ast->e.bin.lhs->e.bin.lhs);
	expr->u.prop_store.prop = lift_expr(ctx, ast->e.bin.lhs->e.bin.rhs);
	expr->u.prop_store.rhs = lift_expr(ctx, ast->e.bin.rhs);
	return expr;
    }

    if (ast->e.bin.lhs->kind == EXPR_INDEX) {
	Expr *base = ast->e.bin.lhs;

	while (base->kind == EXPR_INDEX)
	    base = base->e.bin.lhs;
	if (base->kind == EXPR_ID || base->kind == EXPR_PROP) {
	    HIRExpr *expr = new_expr(ctx, HIR_EXPR_INDEX_STORE);

	    expr->source_lineno = ast->lineno;
	    expr->bytecode_pc = ast->bytecode_pc;
	    expr->u.index_store.base = lift_expr(ctx, ast->e.bin.lhs->e.bin.lhs);
	    expr->u.index_store.index = lift_expr(ctx, ast->e.bin.lhs->e.bin.rhs);
	    expr->u.index_store.rhs = lift_expr(ctx, ast->e.bin.rhs);
	    return expr;
	}
    }
    if (ast->e.bin.lhs->kind == EXPR_RANGE) {
	HIRExpr *expr = new_expr(ctx, HIR_EXPR_RANGE_STORE);

	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.range_store.base = lift_expr(ctx, ast->e.bin.lhs->e.range.base);
	expr->u.range_store.from = lift_expr(ctx, ast->e.bin.lhs->e.range.from);
	expr->u.range_store.to = lift_expr(ctx, ast->e.bin.lhs->e.range.to);
	expr->u.range_store.rhs = lift_expr(ctx, ast->e.bin.rhs);
	return expr;
    }

    record_unsupported(ctx, "ast-asgn: unsupported non-local assignment");
    return unsupported_expr(ctx, ast);
}

static HIRExpr *
lift_expr(HIRContext *ctx, Expr *ast)
{
    HIRExpr *expr;

    if (!ast)
	return 0;

    switch (ast->kind) {
    case EXPR_VAR:
	expr = new_expr(ctx, HIR_EXPR_LITERAL);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->type = type_tag_for_var_type(ast->e.var.type);
	expr->u.literal = ast->e.var;
	return expr;
    case EXPR_ID:
	expr = new_expr(ctx, HIR_EXPR_LOCAL_LOAD);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.local_id = ast->e.id;
	return expr;
    case EXPR_ASGN:
	return lift_assignment(ctx, ast);
    case EXPR_NEGATE:
    case EXPR_NOT:
    case EXPR_COMPLEMENT:
	expr = new_expr(ctx, HIR_EXPR_UNARY);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.unary.op = (ast->kind == EXPR_NEGATE
			    ? HIR_OP_NEGATE
			    : (ast->kind == EXPR_NOT
			       ? HIR_OP_NOT : HIR_OP_COMPLEMENT));
	expr->u.unary.expr = lift_expr(ctx, ast->e.expr);
	return expr;
    case EXPR_PLUS:
    case EXPR_MINUS:
    case EXPR_TIMES:
    case EXPR_DIVIDE:
    case EXPR_MOD:
    case EXPR_EXP:
    case EXPR_EQ:
    case EXPR_NE:
    case EXPR_LT:
    case EXPR_LE:
    case EXPR_GT:
    case EXPR_GE:
    case EXPR_IN:
    case EXPR_AND:
    case EXPR_OR:
    case EXPR_BITOR:
    case EXPR_BITXOR:
    case EXPR_BITAND:
    case EXPR_SHL:
    case EXPR_SHR:
    case EXPR_LSHR:
	return lift_binary_expr(ctx, ast);
    case EXPR_COND:
	expr = new_expr(ctx, HIR_EXPR_COND);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.cond.condition = lift_expr(ctx, ast->e.cond.condition);
	expr->u.cond.consequent = lift_expr(ctx, ast->e.cond.consequent);
	expr->u.cond.alternate = lift_expr(ctx, ast->e.cond.alternate);
	return expr;
    case EXPR_CALL:
	expr = new_expr(ctx, HIR_EXPR_CALL);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.call.resume_key.code_unit = ctx->current_code_unit;
	expr->u.call.resume_key.site = ast->e.call.resume_site;
	expr->u.call.func = ast->e.call.func;
	expr->u.call.args = lift_arg_list(ctx, ast->e.call.args);
	return expr;
    case EXPR_VERB:
	expr = new_expr(ctx, HIR_EXPR_VERB_CALL);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.verb_call.resume_key.code_unit = ctx->current_code_unit;
	expr->u.verb_call.resume_key.site = ast->e.verb.resume_site;
	expr->u.verb_call.obj = lift_expr(ctx, ast->e.verb.obj);
	expr->u.verb_call.verb = lift_expr(ctx, ast->e.verb.verb);
	expr->u.verb_call.args = lift_arg_list(ctx, ast->e.verb.args);
	return expr;
    case EXPR_PROP:
	expr = new_expr(ctx, HIR_EXPR_PROP);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.pair.lhs = lift_expr(ctx, ast->e.bin.lhs);
	expr->u.pair.rhs = lift_expr(ctx, ast->e.bin.rhs);
	return expr;
    case EXPR_INDEX:
	expr = new_expr(ctx, HIR_EXPR_INDEX);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.pair.lhs = lift_expr(ctx, ast->e.bin.lhs);
	expr->u.pair.rhs = lift_expr(ctx, ast->e.bin.rhs);
	return expr;
    case EXPR_RANGE:
	expr = new_expr(ctx, HIR_EXPR_RANGE);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.range.base = lift_expr(ctx, ast->e.range.base);
	expr->u.range.from = lift_expr(ctx, ast->e.range.from);
	expr->u.range.to = lift_expr(ctx, ast->e.range.to);
	return expr;
    case EXPR_LIST:
	expr = new_expr(ctx, HIR_EXPR_LIST);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.list.items = lift_arg_list(ctx, ast->e.list);
	return expr;
    case EXPR_CATCH:
	expr = new_expr(ctx, HIR_EXPR_CATCH);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	expr->u.catch_expr.body = lift_expr(ctx, ast->e.catch.try);
	expr->u.catch_expr.codes = lift_arg_list(ctx, ast->e.catch.codes);
	expr->u.catch_expr.handler = lift_expr(ctx, ast->e.catch.except);
	expr->u.catch_expr.handler_pc = ast->e.catch.handler_pc;
	return expr;
    case EXPR_SCATTER:
	return unsupported_expr(ctx, ast);
    case EXPR_LENGTH:
	expr = new_expr(ctx, HIR_EXPR_LENGTH);
	expr->source_lineno = ast->lineno;
	expr->bytecode_pc = ast->bytecode_pc;
	return expr;
    default:
	return unsupported_expr(ctx, ast);
    }
}

static HIRCondArm *
lift_cond_arms(HIRContext *ctx, Cond_Arm *arms)
{
    HIRCondArm *first = 0;
    HIRCondArm *last = 0;

    for (; arms; arms = arms->next) {
	HIRCondArm *arm = hir_alloc(ctx, sizeof(HIRCondArm));

	arm->condition = lift_expr(ctx, arms->condition);
	arm->body = lift_stmt_list(ctx, arms->stmt);
	arm->bytecode_pc = arms->bytecode_pc;
	arm->next = 0;

	if (last)
	    last->next = arm;
	else
	    first = arm;
	last = arm;
    }

    return first;
}

static HIRExceptArm *
lift_except_arms(HIRContext *ctx, Except_Arm *excepts)
{
    HIRExceptArm *first = 0;
    HIRExceptArm *last = 0;

    for (; excepts; excepts = excepts->next) {
	HIRExceptArm *arm = hir_alloc(ctx, sizeof(HIRExceptArm));

	arm->local_id = excepts->id;
	arm->codes = lift_arg_list(ctx, excepts->codes);
	arm->body = lift_stmt_list(ctx, excepts->stmt);
	arm->source_lineno = excepts->stmt ? excepts->stmt->lineno : 0;
	arm->label = -1;
	arm->handler_pc = excepts->handler_pc;
	arm->next = 0;

	if (last)
	    last->next = arm;
	else
	    first = arm;
	last = arm;
    }

    return first;
}

static const char *
ast_stmt_kind_name(enum Stmt_Kind kind)
{
    switch (kind) {
    case STMT_COND: return "cond";
    case STMT_LIST: return "for-list";
    case STMT_RANGE: return "for-range";
    case STMT_WHILE: return "while";
    case STMT_FORK: return "fork";
    case STMT_EXPR: return "expr";
    case STMT_RETURN: return "return";
    case STMT_TRY_EXCEPT: return "try-except";
    case STMT_TRY_FINALLY: return "try-finally";
    case STMT_BREAK: return "break";
    case STMT_CONTINUE: return "continue";
    default: return "unknown";
    }
}

static HIRStmt *
unsupported_stmt(HIRContext *ctx, Stmt *ast)
{
    HIRStmt *stmt = new_stmt(ctx, HIR_STMT_UNSUPPORTED);

    stmt->source_lineno = ast ? ast->lineno : 0;
    stmt->u.stmt_kind = ast ? ast->kind : STMT_EXPR;
    record_unsupported_fmt(ctx, "ast-stmt: %s", ast ? ast_stmt_kind_name(ast->kind) : "unknown");
    return stmt;
}

static HIRStmt *
lift_stmt(HIRContext *ctx, Stmt *ast)
{
    HIRStmt *stmt;

    switch (ast->kind) {
    case STMT_EXPR:
	stmt = new_stmt(ctx, HIR_STMT_EXPR);
	stmt->source_lineno = ast->lineno;
	stmt->u.expr = lift_expr(ctx, ast->s.expr);
	return stmt;
    case STMT_RETURN:
	stmt = new_stmt(ctx, HIR_STMT_RETURN);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.expr = lift_expr(ctx, ast->s.expr);
	return stmt;
    case STMT_COND:
	stmt = new_stmt(ctx, HIR_STMT_IF);
	stmt->source_lineno = ast->lineno;
	stmt->u.if_stmt.arms = lift_cond_arms(ctx, ast->s.cond.arms);
	stmt->u.if_stmt.otherwise = lift_stmt_list(ctx, ast->s.cond.otherwise);
	return stmt;
    case STMT_WHILE:
	stmt = new_stmt(ctx, HIR_STMT_WHILE);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.loop.loop_id = ast->s.loop.id;
	stmt->u.loop.condition = lift_expr(ctx, ast->s.loop.condition);
	stmt->u.loop.body = lift_stmt_list(ctx, ast->s.loop.body);
	return stmt;
    case STMT_LIST:
	stmt = new_stmt(ctx, HIR_STMT_FOR_LIST);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.for_list.local_id = ast->s.list.id;
	stmt->u.for_list.iterable = lift_expr(ctx, ast->s.list.expr);
	stmt->u.for_list.body = lift_stmt_list(ctx, ast->s.list.body);
	return stmt;
    case STMT_RANGE:
	stmt = new_stmt(ctx, HIR_STMT_FOR_RANGE);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.for_range.local_id = ast->s.range.id;
	stmt->u.for_range.from = lift_expr(ctx, ast->s.range.from);
	stmt->u.for_range.to = lift_expr(ctx, ast->s.range.to);
	stmt->u.for_range.body = lift_stmt_list(ctx, ast->s.range.body);
	return stmt;
    case STMT_FORK:
	stmt = new_stmt(ctx, HIR_STMT_FORK);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.fork.local_id = ast->s.fork.id;
	stmt->u.fork.time = lift_expr(ctx, ast->s.fork.time);
	return stmt;
    case STMT_TRY_EXCEPT:
	stmt = new_stmt(ctx, HIR_STMT_TRY_EXCEPT);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.try_except.body = lift_stmt_list(ctx, ast->s.catch.body);
	stmt->u.try_except.excepts = lift_except_arms(ctx, ast->s.catch.excepts);
	return stmt;
    case STMT_TRY_FINALLY:
	stmt = new_stmt(ctx, HIR_STMT_TRY_FINALLY);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.try_finally.body = lift_stmt_list(ctx, ast->s.finally.body);
	stmt->u.try_finally.handler = lift_stmt_list(ctx, ast->s.finally.handler);
	stmt->u.try_finally.handler_pc = ast->s.finally.handler_pc;
	return stmt;
    case STMT_BREAK:
	stmt = new_stmt(ctx, HIR_STMT_BREAK);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.exit_id = ast->s.exit;
	return stmt;
    case STMT_CONTINUE:
	stmt = new_stmt(ctx, HIR_STMT_CONTINUE);
	stmt->source_lineno = ast->lineno;
	stmt->bytecode_pc = ast->bytecode_pc;
	stmt->u.exit_id = ast->s.exit;
	return stmt;
    default:
	return unsupported_stmt(ctx, ast);
    }
}

static HIRStmt *
lift_stmt_list(HIRContext *ctx, Stmt *ast)
{
    HIRStmt *sequence = new_stmt(ctx, HIR_STMT_SEQUENCE);
    HIRStmt *first = 0;
    HIRStmt *last = 0;

    if (ast)
	sequence->source_lineno = ast->lineno;

    for (; ast; ast = ast->next) {
	HIRStmt *stmt = lift_stmt(ctx, ast);

	if (last)
	    last->next = stmt;
	else
	    first = stmt;
	last = stmt;
    }

    sequence->u.sequence = first;
    return sequence;
}

static int
new_temp(HIRContext *ctx)
{
    return ctx->next_temp++;
}

static int
new_label(HIRContext *ctx)
{
    return ctx->next_label++;
}

static HIRTacInstr *
new_tac(HIRContext *ctx, HIRTacKind kind, unsigned source_lineno)
{
    HIRTacInstr *instr = hir_alloc(ctx, sizeof(HIRTacInstr));

    memset(instr, 0, sizeof(HIRTacInstr));
    instr->kind = kind;
    instr->source_lineno = source_lineno;
    instr->bytecode_pc = NO_BYTECODE_PC;
    instr->error_label = ctx->current_error_label;
    instr->local_id = -1;
    instr->op = HIR_OP_ADD;
    instr->func = FUNC_NOT_FOUND;
    return instr;
}

static void
push_lower_stack_slot(HIRContext *ctx, int value, ResumeStackSlotKind kind,
		      unsigned data)
{
    if (ctx->lower_stack_depth == ctx->lower_stack_capacity) {
	int new_capacity = ctx->lower_stack_capacity
	    ? ctx->lower_stack_capacity * 2 : 8;
	int *new_stack = hir_alloc(ctx, sizeof(int) * new_capacity);
	ResumeStackSlot *new_slots = hir_alloc(ctx,
				      sizeof(ResumeStackSlot) * new_capacity);

	if (ctx->lower_stack_depth) {
	    memcpy(new_stack, ctx->lower_stack,
		   sizeof(int) * ctx->lower_stack_depth);
	    memcpy(new_slots, ctx->lower_stack_slots,
		   sizeof(ResumeStackSlot) * ctx->lower_stack_depth);
	}
	ctx->lower_stack = new_stack;
	ctx->lower_stack_slots = new_slots;
	ctx->lower_stack_capacity = new_capacity;
    }
    ctx->lower_stack[ctx->lower_stack_depth] = value;
    ctx->lower_stack_slots[ctx->lower_stack_depth].kind = kind;
    ctx->lower_stack_slots[ctx->lower_stack_depth].data = data;
    ctx->lower_stack_depth++;
}

static void
push_lower_stack(HIRContext *ctx, int value)
{
    push_lower_stack_slot(ctx, value, RSS_VALUE, 0);
}

static void
replace_lower_stack(HIRContext *ctx, int index, int value)
{
    ctx->lower_stack[index] = value;
    ctx->lower_stack_slots[index].kind = RSS_VALUE;
    ctx->lower_stack_slots[index].data = 0;
}

static void
snapshot_lower_stack_depth(HIRContext *ctx, HIRTacInstr *instr, int depth)
{
	if (depth < 0 || depth > ctx->lower_stack_depth) {
		record_unsupported(ctx, "lowering: invalid resume stack depth");
		depth = ctx->lower_stack_depth;
	}
	instr->num_stack_values = depth;
	if (depth) {
		instr->stack_values = hir_alloc(ctx, sizeof(int) * depth);
		instr->stack_slots = hir_alloc(ctx,
					 sizeof(ResumeStackSlot) * depth);
		memcpy(instr->stack_values, ctx->lower_stack,
		       sizeof(int) * depth);
		memcpy(instr->stack_slots, ctx->lower_stack_slots,
		       sizeof(ResumeStackSlot) * depth);
	}
}

static void
snapshot_lower_stack(HIRContext *ctx, HIRTacInstr *instr)
{
	snapshot_lower_stack_depth(ctx, instr, ctx->lower_stack_depth);
}

static void
append_tac(HIRTacProgram *program, HIRTacInstr *instr)
{
    instr->next = 0;
    if (program->last)
	program->last->next = instr;
    else
	program->first = instr;
    program->last = instr;
}

static void
append_tick(HIRContext *ctx, HIRTacProgram *program, unsigned source_lineno,
	    unsigned bytecode_pc)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_TICK, source_lineno);

    instr->bytecode_pc = bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
}

static void
append_charge_tick(HIRContext *ctx, HIRTacProgram *program,
		   unsigned source_lineno, unsigned bytecode_pc)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_TICK, source_lineno);

    instr->op = HIR_OP_CHARGE_TICK;
    instr->bytecode_pc = bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
}

static void
append_label(HIRContext *ctx, HIRTacProgram *program, int label,
	     unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_LABEL, source_lineno);

    instr->label = label;
    append_tac(program, instr);
}

static void
append_jump(HIRContext *ctx, HIRTacProgram *program, int label,
	    unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_JUMP, source_lineno);

    instr->label = label;
    append_tac(program, instr);
}

static void
append_branch_false_internal(HIRContext *ctx, HIRTacProgram *program, int src,
			     int label, unsigned source_lineno,
			     unsigned bytecode_pc, int tick)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_BRANCH_FALSE, source_lineno);

    if (tick)
	append_tick(ctx, program, source_lineno, bytecode_pc);
    instr->bytecode_pc = bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    instr->src1 = src;
    instr->label = label;
    append_tac(program, instr);
}

static void
append_branch_false(HIRContext *ctx, HIRTacProgram *program, int src, int label,
		    unsigned source_lineno, unsigned bytecode_pc)
{
    append_branch_false_internal(ctx, program, src, label, source_lineno,
				 bytecode_pc, 1);
}

static void
append_unticked_branch_false(HIRContext *ctx, HIRTacProgram *program, int src,
			     int label, unsigned source_lineno,
			     unsigned bytecode_pc)
{
    append_branch_false_internal(ctx, program, src, label, source_lineno,
				 bytecode_pc, 0);
}

static void
append_unticked_branch_false_at_depth(HIRContext *ctx, HIRTacProgram *program,
				      int src, int label,
				      unsigned source_lineno,
				      unsigned bytecode_pc, int resume_depth)
{
	HIRTacInstr *instr = new_tac(ctx, HIR_TAC_BRANCH_FALSE, source_lineno);

	instr->bytecode_pc = bytecode_pc;
	snapshot_lower_stack_depth(ctx, instr, resume_depth);
	instr->src1 = src;
	instr->label = label;
	append_tac(program, instr);
}

static void
append_internal_store(HIRContext *ctx, HIRTacProgram *program, int local_id,
		      int src, unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_STORE_LOCAL, source_lineno);

    instr->dst = src;
    instr->src1 = src;
    instr->local_id = local_id;
    append_tac(program, instr);
}

static int
append_internal_load(HIRContext *ctx, HIRTacProgram *program, int local_id,
		     unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_LOAD_LOCAL, source_lineno);

    instr->dst = new_temp(ctx);
    instr->local_id = local_id;
    append_tac(program, instr);
    return instr->dst;
}

static int
lower_short_circuit(HIRContext *ctx, HIRTacProgram *program, HIRExpr *expr)
{
    int base_depth = ctx->lower_stack_depth;
    int lhs = lower_expr(ctx, program, expr->u.binary.lhs);
    int result_local = ctx->next_local++;
    int done_label = new_label(ctx);

    append_internal_store(ctx, program, result_local, lhs,
			  expr->source_lineno);
    if (expr->u.binary.op == HIR_OP_AND) {
	int rhs;

	append_branch_false(ctx, program, lhs, done_label,
			    expr->source_lineno, expr->bytecode_pc);
	ctx->lower_stack_depth = base_depth;
	rhs = lower_expr(ctx, program, expr->u.binary.rhs);
	append_internal_store(ctx, program, result_local, rhs,
			      expr->source_lineno);
    } else {
	int rhs_label = new_label(ctx);
	int rhs;

	append_branch_false(ctx, program, lhs, rhs_label,
			    expr->source_lineno, expr->bytecode_pc);
	append_jump(ctx, program, done_label, expr->source_lineno);
	append_label(ctx, program, rhs_label, expr->source_lineno);
	ctx->lower_stack_depth = base_depth;
	rhs = lower_expr(ctx, program, expr->u.binary.rhs);
	append_internal_store(ctx, program, result_local, rhs,
			      expr->source_lineno);
    }
    append_label(ctx, program, done_label, expr->source_lineno);
    lhs = append_internal_load(ctx, program, result_local,
			       expr->source_lineno);
    ctx->lower_stack_depth = base_depth;
    push_lower_stack(ctx, lhs);
    return lhs;
}

static int
lower_cond_expr(HIRContext *ctx, HIRTacProgram *program, HIRExpr *expr)
{
    int base_depth = ctx->lower_stack_depth;
    int cond = lower_expr(ctx, program, expr->u.cond.condition);
    int result_local = ctx->next_local++;
    int alt_label = new_label(ctx);
    int done_label = new_label(ctx);
    int cons_val;
    int alt_val;
    int result_temp;

    append_branch_false(ctx, program, cond, alt_label,
			expr->source_lineno, expr->bytecode_pc);
    ctx->lower_stack_depth = base_depth;
    cons_val = lower_expr(ctx, program, expr->u.cond.consequent);
    append_internal_store(ctx, program, result_local, cons_val,
			  expr->source_lineno);
    append_jump(ctx, program, done_label, expr->source_lineno);
    append_label(ctx, program, alt_label, expr->source_lineno);
    ctx->lower_stack_depth = base_depth;
    alt_val = lower_expr(ctx, program, expr->u.cond.alternate);
    append_internal_store(ctx, program, result_local, alt_val,
			  expr->source_lineno);
    append_label(ctx, program, done_label, expr->source_lineno);
    result_temp = append_internal_load(ctx, program, result_local,
				       expr->source_lineno);
    ctx->lower_stack_depth = base_depth;
    push_lower_stack(ctx, result_temp);
    return result_temp;
}

static int
lower_codes(HIRContext *ctx, HIRTacProgram *program, HIRArg *codes,
	    unsigned source_lineno, unsigned bytecode_pc)
{
    if (codes) {
	HIRExpr list_expr;
	memset(&list_expr, 0, sizeof(list_expr));
	list_expr.kind = HIR_EXPR_LIST;
	list_expr.source_lineno = source_lineno;
	list_expr.bytecode_pc = bytecode_pc;
	list_expr.u.list.items = codes;
	return lower_expr(ctx, program, &list_expr);
    } else {
	int zero_val = new_temp(ctx);
	HIRTacInstr *zero_codes = new_tac(ctx, HIR_TAC_CONST, source_lineno);
	zero_codes->dst = zero_val;
	zero_codes->literal.type = TYPE_INT;
	zero_codes->literal.v.num = 0;
	zero_codes->bytecode_pc = bytecode_pc;
	snapshot_lower_stack(ctx, zero_codes);
	append_tac(program, zero_codes);
	push_lower_stack(ctx, zero_val);
	return zero_val;
    }
}

static void
append_deopt_boundary(HIRContext *ctx, HIRTacProgram *program,
		      unsigned source_lineno, unsigned bytecode_pc)
{
    HIRTacInstr *deopt = new_tac(ctx, HIR_TAC_DEOPT, source_lineno);

    deopt->op = HIR_OP_FORK;
    deopt->bytecode_pc = bytecode_pc;
    snapshot_lower_stack(ctx, deopt);
    append_tac(program, deopt);
}

static void
append_index_store_deopt(HIRContext *ctx, HIRTacProgram *program,
			 unsigned source_lineno, unsigned bytecode_pc)
{
    HIRTacInstr *deopt = new_tac(ctx, HIR_TAC_DEOPT, source_lineno);

    deopt->op = HIR_OP_INDEX;
    deopt->bytecode_pc = bytecode_pc;
    snapshot_lower_stack(ctx, deopt);
    append_tac(program, deopt);
}

static void
append_scatter_deopt(HIRContext *ctx, HIRTacProgram *program,
		     unsigned source_lineno, unsigned bytecode_pc,
		     int resume_depth)
{
    HIRTacInstr *deopt = new_tac(ctx, HIR_TAC_DEOPT, source_lineno);

    deopt->op = HIR_OP_SCATTER;
    deopt->bytecode_pc = bytecode_pc;
    snapshot_lower_stack_depth(ctx, deopt, resume_depth);
    append_tac(program, deopt);
}

static int
append_scatter_constant(HIRContext *ctx, HIRTacProgram *program, Num value,
			unsigned source_lineno, unsigned bytecode_pc,
			int resume_depth)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_CONST, source_lineno);

    instr->bytecode_pc = bytecode_pc;
    instr->dst = new_temp(ctx);
    instr->literal.type = TYPE_INT;
    instr->literal.v.num = value;
    snapshot_lower_stack_depth(ctx, instr, resume_depth);
    append_tac(program, instr);
    return instr->dst;
}

static int
append_scatter_unary(HIRContext *ctx, HIRTacProgram *program, HIROp op,
		     int src, unsigned source_lineno, unsigned bytecode_pc,
		     int resume_depth)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_UNARY, source_lineno);

    instr->bytecode_pc = bytecode_pc;
    instr->dst = new_temp(ctx);
    instr->src1 = src;
    instr->op = op;
    snapshot_lower_stack_depth(ctx, instr, resume_depth);
    append_tac(program, instr);
    return instr->dst;
}

static int
append_scatter_binary(HIRContext *ctx, HIRTacProgram *program, HIROp op,
		      int lhs, int rhs, unsigned source_lineno,
		      unsigned bytecode_pc, int resume_depth)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_BINARY, source_lineno);

    instr->bytecode_pc = bytecode_pc;
    instr->dst = new_temp(ctx);
    instr->src1 = lhs;
    instr->src2 = rhs;
    instr->op = op;
    snapshot_lower_stack_depth(ctx, instr, resume_depth);
    append_tac(program, instr);
    return instr->dst;
}

static int
lower_scatter(HIRContext *ctx, HIRTacProgram *program, HIRExpr *expr)
{
    HIRScatter *item;
    int saved_depth = ctx->lower_stack_depth;
    int rhs = lower_expr(ctx, program, expr->u.scatter.rhs);
    int scatter_depth = ctx->lower_stack_depth;
    int required = 0;
    int optional = 0;
    int have_rest = 0;
    int seen_optional = 0;
    int seen_rest = 0;
    int position = 0;
    int invalid_label = new_label(ctx);
    int done_label = new_label(ctx);
    int length;
    int limit;
    int condition;

    for (item = expr->u.scatter.items; item; item = item->next) {
	if (item->kind == SCAT_REST) {
	    if (seen_rest) {
		append_scatter_deopt(ctx, program, expr->source_lineno,
				     expr->bytecode_pc, scatter_depth);
		ctx->lower_stack_depth = saved_depth;
		push_lower_stack(ctx, rhs);
		return rhs;
	    }
	    seen_rest = 1;
	    have_rest = 1;
	}
	else if (item->kind == SCAT_REQUIRED) {
	    if (seen_optional || seen_rest) {
		append_scatter_deopt(ctx, program, expr->source_lineno,
				     expr->bytecode_pc, scatter_depth);
		ctx->lower_stack_depth = saved_depth;
		push_lower_stack(ctx, rhs);
		return rhs;
	    }
	    required++;
	}
	else if (item->kind == SCAT_OPTIONAL) {
	    if (seen_rest) {
		append_scatter_deopt(ctx, program, expr->source_lineno,
				     expr->bytecode_pc, scatter_depth);
		ctx->lower_stack_depth = saved_depth;
		push_lower_stack(ctx, rhs);
		return rhs;
	    }
	    seen_optional = 1;
	    optional++;
	    if (!item->expr) {
		append_scatter_deopt(ctx, program, expr->source_lineno,
				     expr->bytecode_pc, scatter_depth);
		ctx->lower_stack_depth = saved_depth;
		push_lower_stack(ctx, rhs);
		return rhs;
	    }
	}
    }

    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
    length = append_scatter_unary(ctx, program, HIR_OP_LENGTH, rhs,
				  expr->source_lineno, expr->bytecode_pc,
				  scatter_depth);
    limit = append_scatter_constant(ctx, program, required,
				    expr->source_lineno, expr->bytecode_pc,
				    scatter_depth);
    condition = append_scatter_binary(ctx, program, HIR_OP_GE, length, limit,
				      expr->source_lineno, expr->bytecode_pc,
				      scatter_depth);
    append_unticked_branch_false_at_depth(ctx, program, condition,
					  invalid_label, expr->source_lineno,
					  expr->bytecode_pc, scatter_depth);

    if (!have_rest) {
	limit = append_scatter_constant(ctx, program, required + optional,
					expr->source_lineno, expr->bytecode_pc,
					scatter_depth);
	condition = append_scatter_binary(ctx, program, HIR_OP_LE, length, limit,
					  expr->source_lineno, expr->bytecode_pc,
					  scatter_depth);
	append_unticked_branch_false_at_depth(ctx, program, condition,
					      invalid_label, expr->source_lineno,
					      expr->bytecode_pc, scatter_depth);
    }

    for (item = expr->u.scatter.items; item; item = item->next) {
	int index;
	int value;

	position++;
	index = append_scatter_constant(ctx, program, position,
					 expr->source_lineno, expr->bytecode_pc,
					 scatter_depth);
	if (item->kind == SCAT_OPTIONAL) {
	    int default_label = new_label(ctx);
	    int item_done_label = new_label(ctx);

	    condition = append_scatter_binary(ctx, program, HIR_OP_GE,
					 length, index, expr->source_lineno,
					 expr->bytecode_pc, scatter_depth);
	    append_unticked_branch_false_at_depth(ctx, program, condition,
						 default_label,
						 expr->source_lineno,
						 expr->bytecode_pc,
						 scatter_depth);
	    value = append_scatter_binary(ctx, program, HIR_OP_INDEX, rhs, index,
					  expr->source_lineno,
					  expr->bytecode_pc, scatter_depth);
	    append_internal_store(ctx, program, item->local_id, value,
				  expr->source_lineno);
	    append_jump(ctx, program, item_done_label, expr->source_lineno);
	    append_label(ctx, program, default_label, expr->source_lineno);
	    ctx->lower_stack_depth = scatter_depth;
	    value = lower_expr(ctx, program, item->expr);
	    append_internal_store(ctx, program, item->local_id, value,
				  expr->source_lineno);
	    ctx->lower_stack_depth = scatter_depth;
	    append_label(ctx, program, item_done_label, expr->source_lineno);
	} else if (item->kind == SCAT_REST) {
	    value = append_scatter_binary(ctx, program, HIR_OP_SUBLIST_FROM,
					  rhs, index, expr->source_lineno,
					  expr->bytecode_pc, scatter_depth);
	    append_internal_store(ctx, program, item->local_id, value,
				  expr->source_lineno);
	} else {
	    value = append_scatter_binary(ctx, program, HIR_OP_INDEX, rhs, index,
					  expr->source_lineno,
					  expr->bytecode_pc, scatter_depth);
	    append_internal_store(ctx, program, item->local_id, value,
				  expr->source_lineno);
	}
    }
    append_jump(ctx, program, done_label, expr->source_lineno);
    append_label(ctx, program, invalid_label, expr->source_lineno);
    append_scatter_deopt(ctx, program, expr->source_lineno,
			 expr->bytecode_pc, scatter_depth);
    append_label(ctx, program, done_label, expr->source_lineno);
    ctx->lower_stack_depth = scatter_depth;
    return rhs;
}

static int
lower_catch_expr(HIRContext *ctx, HIRTacProgram *program, HIRExpr *expr)
{
    int base_depth = ctx->lower_stack_depth;
    int handler_label = new_label(ctx);
    int done_label = new_label(ctx);
    int result_local = ctx->next_local++;
    int handler_pc_val = new_temp(ctx);
    int catch_marker_val = new_temp(ctx);
    HIRTacInstr *handler_pc_tac;
    HIRTacInstr *catch_marker_tac;
    int codes_val;
    int try_val;
    int handler_val;
    int result_temp;
    int saved_error_label = ctx->current_error_label;

    codes_val = lower_codes(ctx, program, expr->u.catch_expr.codes,
			    expr->source_lineno, expr->bytecode_pc);
    (void) codes_val;

    handler_pc_tac = new_tac(ctx, HIR_TAC_CONST, expr->source_lineno);
    handler_pc_tac->dst = handler_pc_val;
    handler_pc_tac->literal.type = TYPE_INT;
    handler_pc_tac->literal.v.num = expr->u.catch_expr.handler_pc;
    handler_pc_tac->bytecode_pc = expr->bytecode_pc;
    snapshot_lower_stack(ctx, handler_pc_tac);
    append_tac(program, handler_pc_tac);
    push_lower_stack_slot(ctx, handler_pc_val, RSS_HANDLER_PC,
			  expr->u.catch_expr.handler_pc);

    catch_marker_tac = new_tac(ctx, HIR_TAC_CONST, expr->source_lineno);
    catch_marker_tac->dst = catch_marker_val;
    catch_marker_tac->literal.type = TYPE_CATCH;
    catch_marker_tac->literal.v.num = 1;
    catch_marker_tac->bytecode_pc = expr->bytecode_pc;
    snapshot_lower_stack(ctx, catch_marker_tac);
    append_tac(program, catch_marker_tac);
    push_lower_stack_slot(ctx, catch_marker_val, RSS_CATCH, 1);

    if (!expr->u.catch_expr.codes)
	ctx->current_error_label = handler_label;
    try_val = lower_expr(ctx, program, expr->u.catch_expr.body);
    ctx->current_error_label = saved_error_label;
    append_internal_store(ctx, program, result_local, try_val,
			  expr->source_lineno);

    ctx->lower_stack_depth = base_depth;
    append_jump(ctx, program, done_label, expr->source_lineno);

    append_label(ctx, program, handler_label, expr->source_lineno);
    if (expr->u.catch_expr.handler)
	handler_val = lower_expr(ctx, program, expr->u.catch_expr.handler);
    else {
	HIRTacInstr *load_error = new_tac(ctx, HIR_TAC_LOAD_ERROR,
					 expr->source_lineno);

	load_error->dst = new_temp(ctx);
	load_error->literal.type = TYPE_ERR;
	append_tac(program, load_error);
	push_lower_stack(ctx, load_error->dst);
	handler_val = load_error->dst;
    }

    append_internal_store(ctx, program, result_local, handler_val,
			  expr->source_lineno);
    append_label(ctx, program, done_label, expr->source_lineno);

    result_temp = append_internal_load(ctx, program, result_local,
				       expr->source_lineno);
    ctx->lower_stack_depth = base_depth;
    push_lower_stack(ctx, result_temp);
    return result_temp;
}

static int
append_unsupported_tac(HIRContext *ctx, HIRTacProgram *program,
		       const char *message, unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_UNSUPPORTED, source_lineno);

    instr->dst = new_temp(ctx);
    record_unsupported(ctx, message);
    append_tac(program, instr);
    push_lower_stack(ctx, instr->dst);
    return instr->dst;
}

static int
lower_index_lvalue_base(HIRContext *ctx, HIRTacProgram *program, HIRExpr *expr)
{
    HIRTacInstr *instr;
    int base;
    int index;

    if (expr->kind == HIR_EXPR_PROP) {
	base = lower_expr(ctx, program, expr->u.pair.lhs);
	index = lower_expr(ctx, program, expr->u.pair.rhs);
	append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	instr = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->src1 = base;
	instr->src2 = index;
	instr->op = HIR_OP_GET_PROP;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	push_lower_stack(ctx, instr->dst);
	return instr->dst;
    }
    if (expr->kind != HIR_EXPR_INDEX)
	return lower_expr(ctx, program, expr);

    int prev_base = ctx->current_length_base;
    base = lower_index_lvalue_base(ctx, program, expr->u.pair.lhs);
    ctx->current_length_base = base;
    index = lower_expr(ctx, program, expr->u.pair.rhs);
    ctx->current_length_base = prev_base;
    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
    instr = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
    instr->bytecode_pc = expr->bytecode_pc;
    instr->dst = new_temp(ctx);
    instr->src1 = base;
    instr->src2 = index;
    instr->op = HIR_OP_INDEX;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
    push_lower_stack(ctx, instr->dst);
    return instr->dst;
}

static int
lower_expr(HIRContext *ctx, HIRTacProgram *program, HIRExpr *expr)
{
    HIRTacInstr *instr;
    int lhs;
    int rhs;

    if (!expr)
	return 0;

    switch (expr->kind) {
    case HIR_EXPR_LITERAL:
	instr = new_tac(ctx, HIR_TAC_CONST, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->literal = expr->u.literal;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	push_lower_stack(ctx, instr->dst);
	return instr->dst;
    case HIR_EXPR_LOCAL_LOAD:
	instr = new_tac(ctx, HIR_TAC_LOAD_LOCAL, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->local_id = expr->u.local_id;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	push_lower_stack(ctx, instr->dst);
	return instr->dst;
    case HIR_EXPR_LOCAL_STORE:
	rhs = lower_expr(ctx, program, expr->u.local_store.rhs);
	append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	instr = new_tac(ctx, HIR_TAC_STORE_LOCAL, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = rhs;
	instr->src1 = rhs;
	instr->local_id = expr->u.local_store.local_id;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	return rhs;
    case HIR_EXPR_UNARY:
	lhs = lower_expr(ctx, program, expr->u.unary.expr);
	append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	instr = new_tac(ctx, HIR_TAC_UNARY, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->src1 = lhs;
	instr->op = expr->u.unary.op;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	replace_lower_stack(ctx, ctx->lower_stack_depth - 1, instr->dst);
	return instr->dst;
    case HIR_EXPR_BINARY:
	if (expr->u.binary.op == HIR_OP_AND
	    || expr->u.binary.op == HIR_OP_OR)
	    return lower_short_circuit(ctx, program, expr);
	lhs = lower_expr(ctx, program, expr->u.binary.lhs);
	rhs = lower_expr(ctx, program, expr->u.binary.rhs);
	append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	instr = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->src1 = lhs;
	instr->src2 = rhs;
	instr->op = expr->u.binary.op;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	ctx->lower_stack_depth -= 2;
	push_lower_stack(ctx, instr->dst);
	return instr->dst;
    case HIR_EXPR_INDEX:
	{
	    int prev_base = ctx->current_length_base;
	    lhs = lower_expr(ctx, program, expr->u.pair.lhs);
	    ctx->current_length_base = lhs;
	    rhs = lower_expr(ctx, program, expr->u.pair.rhs);
	    ctx->current_length_base = prev_base;
	    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	    instr = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
	    instr->bytecode_pc = expr->bytecode_pc;
	    instr->dst = new_temp(ctx);
	    instr->src1 = lhs;
	    instr->src2 = rhs;
	    instr->op = HIR_OP_INDEX;
	    snapshot_lower_stack(ctx, instr);
	    append_tac(program, instr);
	    ctx->lower_stack_depth -= 2;
	    push_lower_stack(ctx, instr->dst);
	    return instr->dst;
	}
    case HIR_EXPR_PROP:
	lhs = lower_expr(ctx, program, expr->u.pair.lhs);
	rhs = lower_expr(ctx, program, expr->u.pair.rhs);
	append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	instr = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->src1 = lhs;
	instr->src2 = rhs;
	instr->op = HIR_OP_GET_PROP;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	ctx->lower_stack_depth -= 2;
	push_lower_stack(ctx, instr->dst);
	return instr->dst;
    case HIR_EXPR_PROP_STORE:
	{
	    int obj_temp = lower_expr(ctx, program, expr->u.prop_store.obj);
	    int prop_temp = lower_expr(ctx, program, expr->u.prop_store.prop);
	    int rhs_temp = lower_expr(ctx, program, expr->u.prop_store.rhs);
	    int dst_temp = new_temp(ctx);
	    (void) rhs_temp;
	    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	    instr = new_tac(ctx, HIR_TAC_PUT_PROP, expr->source_lineno);
	    instr->bytecode_pc = expr->bytecode_pc;
	    instr->dst = dst_temp;
	    instr->src1 = obj_temp;
	    instr->src2 = prop_temp;
	    snapshot_lower_stack(ctx, instr);
	    append_tac(program, instr);
	    ctx->lower_stack_depth -= 3;
	    push_lower_stack(ctx, dst_temp);
	    return dst_temp;
	}
    case HIR_EXPR_INDEX_STORE:
	{
	    int saved_depth = ctx->lower_stack_depth;
	    int prev_base = ctx->current_length_base;
	    int base_temp = lower_index_lvalue_base(ctx, program,
					     expr->u.index_store.base);
	    int index_temp;
	    int rhs_temp;

	    ctx->current_length_base = base_temp;
	    index_temp = lower_expr(ctx, program, expr->u.index_store.index);
	    ctx->current_length_base = prev_base;
	    rhs_temp = lower_expr(ctx, program, expr->u.index_store.rhs);

	    if (expr->u.index_store.base->kind == HIR_EXPR_LOCAL_LOAD) {
		append_tick(ctx, program, expr->source_lineno,
			    expr->bytecode_pc);
		instr = new_tac(ctx, HIR_TAC_INDEX_SET, expr->source_lineno);
		instr->bytecode_pc = expr->bytecode_pc;
		instr->dst = new_temp(ctx);
		instr->src1 = base_temp;
		instr->src2 = index_temp;
		instr->src3 = rhs_temp;
		instr->local_id = expr->u.index_store.base->u.local_id;
		snapshot_lower_stack(ctx, instr);
		append_tac(program, instr);
	    } else {
		append_index_store_deopt(ctx, program, expr->source_lineno,
					 expr->bytecode_pc);
	    }
	    ctx->lower_stack_depth = saved_depth;
	    push_lower_stack(ctx, rhs_temp);
	    return rhs_temp;
	}
    case HIR_EXPR_RANGE:
	{
	    int prev_base = ctx->current_length_base;
	    int base_temp = lower_expr(ctx, program, expr->u.range.base);
	    int from_temp;
	    int to_temp;
	    int dst_temp = new_temp(ctx);

	    ctx->current_length_base = base_temp;
	    from_temp = lower_expr(ctx, program, expr->u.range.from);
	    to_temp = lower_expr(ctx, program, expr->u.range.to);
	    ctx->current_length_base = prev_base;
	    (void) from_temp;
	    (void) to_temp;

	    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	    instr = new_tac(ctx, HIR_TAC_RANGE_REF, expr->source_lineno);
	    instr->bytecode_pc = expr->bytecode_pc;
	    instr->dst = dst_temp;
	    instr->src1 = base_temp;
	    instr->src2 = from_temp;
	    snapshot_lower_stack(ctx, instr);
	    append_tac(program, instr);
	    ctx->lower_stack_depth -= 3;
	    push_lower_stack(ctx, dst_temp);
	    return dst_temp;
	}
    case HIR_EXPR_RANGE_STORE:
	{
	    int prev_base = ctx->current_length_base;
	    int base_temp = lower_expr(ctx, program, expr->u.range_store.base);
	    int from_temp;
	    int to_temp;
	    int rhs_temp;
	    int dst_temp = new_temp(ctx);

	    ctx->current_length_base = base_temp;
	    from_temp = lower_expr(ctx, program, expr->u.range_store.from);
	    to_temp = lower_expr(ctx, program, expr->u.range_store.to);
	    ctx->current_length_base = prev_base;
	    rhs_temp = lower_expr(ctx, program, expr->u.range_store.rhs);
	    (void) to_temp;
	    (void) rhs_temp;

	    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	    instr = new_tac(ctx, HIR_TAC_RANGE_SET, expr->source_lineno);
	    instr->bytecode_pc = expr->bytecode_pc;
	    instr->dst = dst_temp;
	    instr->src1 = base_temp;
	    instr->src2 = from_temp;
	    snapshot_lower_stack(ctx, instr);
	    append_tac(program, instr);
	    ctx->lower_stack_depth -= 4;
	    push_lower_stack(ctx, dst_temp);
	    return dst_temp;
	}
    case HIR_EXPR_SCATTER:
	return lower_scatter(ctx, program, expr);
    case HIR_EXPR_LIST:
	{
	    HIRArg *item = expr->u.list.items;
	    int list_temp;

	    if (!item) {
		HIRTacInstr *empty_tac = new_tac(ctx, HIR_TAC_CONST,
						 expr->source_lineno);
		empty_tac->dst = new_temp(ctx);
		empty_tac->literal.type = TYPE_LIST;
		empty_tac->literal.v.list = 0;
		empty_tac->bytecode_pc = expr->bytecode_pc;
		snapshot_lower_stack(ctx, empty_tac);
		append_tac(program, empty_tac);
		push_lower_stack(ctx, empty_tac->dst);
		return empty_tac->dst;
	    }

	    if (!item->next && item->kind == ARG_NORMAL) {
		int elem_temp = lower_expr(ctx, program, item->expr);
		HIRTacInstr *single_tac = new_tac(ctx, HIR_TAC_UNARY,
						  expr->source_lineno);
		single_tac->dst = new_temp(ctx);
		single_tac->src1 = elem_temp;
		single_tac->op = HIR_OP_MAKE_SINGLETON_LIST;
		single_tac->bytecode_pc = item->bytecode_pc;
		snapshot_lower_stack(ctx, single_tac);
		append_tac(program, single_tac);
	    replace_lower_stack(ctx, ctx->lower_stack_depth - 1,
				single_tac->dst);
		return single_tac->dst;
	    }

	    if (item->kind == ARG_NORMAL) {
		int elem_temp = lower_expr(ctx, program, item->expr);
		HIRTacInstr *single_tac = new_tac(ctx, HIR_TAC_UNARY,
						  expr->source_lineno);
		single_tac->dst = new_temp(ctx);
		single_tac->src1 = elem_temp;
		single_tac->op = HIR_OP_MAKE_SINGLETON_LIST;
		single_tac->bytecode_pc = item->bytecode_pc;
		snapshot_lower_stack(ctx, single_tac);
		append_tac(program, single_tac);
		replace_lower_stack(ctx, ctx->lower_stack_depth - 1,
				    single_tac->dst);
		list_temp = single_tac->dst;
	    } else {
		int elem_temp = lower_expr(ctx, program, item->expr);
		HIRTacInstr *check_tac = new_tac(ctx, HIR_TAC_UNARY,
						 expr->source_lineno);
		check_tac->dst = new_temp(ctx);
		check_tac->src1 = elem_temp;
		check_tac->op = HIR_OP_CHECK_LIST_FOR_SPLICE;
		check_tac->bytecode_pc = item->bytecode_pc;
		snapshot_lower_stack(ctx, check_tac);
		append_tac(program, check_tac);
		replace_lower_stack(ctx, ctx->lower_stack_depth - 1,
				    check_tac->dst);
		list_temp = check_tac->dst;
	    }

	    for (item = item->next; item; item = item->next) {
		int elem_temp = lower_expr(ctx, program, item->expr);
		int next_list_temp = new_temp(ctx);
		HIRTacInstr *tail_tac = new_tac(ctx, HIR_TAC_BINARY,
						expr->source_lineno);
		tail_tac->dst = next_list_temp;
		tail_tac->src1 = list_temp;
		tail_tac->src2 = elem_temp;
		tail_tac->op = (item->kind == ARG_NORMAL
				? HIR_OP_LIST_ADD_TAIL
				: HIR_OP_LIST_APPEND);
		tail_tac->bytecode_pc = item->bytecode_pc;
		snapshot_lower_stack(ctx, tail_tac);
		append_tac(program, tail_tac);
		ctx->lower_stack_depth -= 2;
		push_lower_stack(ctx, next_list_temp);
		list_temp = next_list_temp;
	    }
	    return list_temp;
	}
    case HIR_EXPR_CALL:
	{
	    const char *func_name = name_func_by_num(expr->u.call.func);
	    HIRArg *args = expr->u.call.args;

	    if (func_name && (!strcmp(func_name, "ticks_left")
			      || !strcmp(func_name, "seconds_left")
			      || !strcmp(func_name, "time"))
		&& !args) {
		int dst_temp = new_temp(ctx);
		HIRTacInstr *tac = new_tac(ctx, HIR_TAC_UNARY, expr->source_lineno);
		append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
		tac->dst = dst_temp;
		tac->src1 = 0;
		if (!strcmp(func_name, "ticks_left"))
		    tac->op = HIR_OP_TICKS_LEFT;
		else if (!strcmp(func_name, "seconds_left"))
		    tac->op = HIR_OP_SECONDS_LEFT;
		else
		    tac->op = HIR_OP_TIME;
		tac->func = expr->u.call.func;
		tac->bytecode_pc = expr->bytecode_pc;
		snapshot_lower_stack(ctx, tac);
		append_tac(program, tac);
		push_lower_stack(ctx, dst_temp);
		return dst_temp;
	    }

	    if (func_name && (!strcmp(func_name, "abs")
			      || !strcmp(func_name, "toint")
			      || !strcmp(func_name, "tonum")
			      || !strcmp(func_name, "typeof")
			      || !strcmp(func_name, "length")
			      || !strcmp(func_name, "valid")
			      || !strcmp(func_name, "parent"))
		&& args && !args->next && args->kind == ARG_NORMAL) {
		int arg_temp = lower_expr(ctx, program, args->expr);
		int dst_temp = new_temp(ctx);
		HIRTacInstr *tac = new_tac(ctx, HIR_TAC_UNARY, expr->source_lineno);
		tac->dst = dst_temp;
		tac->src1 = arg_temp;
		if (!strcmp(func_name, "abs"))
		    tac->op = HIR_OP_ABS;
		else if (!strcmp(func_name, "typeof"))
		    tac->op = HIR_OP_TYPEOF;
		else if (!strcmp(func_name, "length"))
		    tac->op = HIR_OP_LENGTH;
		else if (!strcmp(func_name, "valid"))
		    tac->op = HIR_OP_VALID;
		else if (!strcmp(func_name, "parent"))
		    tac->op = HIR_OP_PARENT;
		else
		    tac->op = HIR_OP_TOINT;
		tac->func = expr->u.call.func;
		tac->bytecode_pc = expr->bytecode_pc;
		snapshot_lower_stack(ctx, tac);
		append_tac(program, tac);
		replace_lower_stack(ctx, ctx->lower_stack_depth - 1, dst_temp);
		return dst_temp;
	    }
	    if (func_name && (!strcmp(func_name, "min") || !strcmp(func_name, "max")
			      || !strcmp(func_name, "index") || !strcmp(func_name, "rindex"))
		&& args && args->kind == ARG_NORMAL
		&& args->next && args->next->kind == ARG_NORMAL
		&& !args->next->next) {
		int arg1_temp = lower_expr(ctx, program, args->expr);
		int arg2_temp = lower_expr(ctx, program, args->next->expr);
		int dst_temp = new_temp(ctx);
		HIRTacInstr *tac = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
		tac->dst = dst_temp;
		tac->src1 = arg1_temp;
		tac->src2 = arg2_temp;
		if (!strcmp(func_name, "min"))
		    tac->op = HIR_OP_MIN;
		else if (!strcmp(func_name, "max"))
		    tac->op = HIR_OP_MAX;
		else if (!strcmp(func_name, "index"))
		    tac->op = HIR_OP_INDEX_BF;
		else
		    tac->op = HIR_OP_RINDEX_BF;
		tac->func = expr->u.call.func;
		tac->bytecode_pc = expr->bytecode_pc;
		snapshot_lower_stack(ctx, tac);
		append_tac(program, tac);
		ctx->lower_stack_depth -= 2;
		push_lower_stack(ctx, dst_temp);
		return dst_temp;
	    }

	    HIRExpr list_expr;
	    int args_temp;
	    HIRTacInstr *call_tac;

	    memset(&list_expr, 0, sizeof(list_expr));
	    list_expr.kind = HIR_EXPR_LIST;
	    list_expr.source_lineno = expr->source_lineno;
	    list_expr.bytecode_pc = expr->bytecode_pc;
	    list_expr.u.list.items = expr->u.call.args;
	    args_temp = lower_expr(ctx, program, &list_expr);

	    call_tac = new_tac(ctx, HIR_TAC_CALL, expr->source_lineno);
	    call_tac->dst = new_temp(ctx);
	    call_tac->src1 = args_temp;
	    call_tac->func = expr->u.call.func;
	    call_tac->resume_key = expr->u.call.resume_key;
	    call_tac->bytecode_pc = expr->bytecode_pc;
	    snapshot_lower_stack(ctx, call_tac);
	    append_tac(program, call_tac);
	    replace_lower_stack(ctx, ctx->lower_stack_depth - 1,
				call_tac->dst);
	    return call_tac->dst;
	}
    case HIR_EXPR_VERB_CALL:
	{
	    int obj_temp = lower_expr(ctx, program, expr->u.verb_call.obj);
	    int verb_temp = lower_expr(ctx, program, expr->u.verb_call.verb);
	    HIRExpr list_expr;
	    int args_temp;
	    HIRTacInstr *call_tac;

	    memset(&list_expr, 0, sizeof(list_expr));
	    list_expr.kind = HIR_EXPR_LIST;
	    list_expr.source_lineno = expr->source_lineno;
	    list_expr.bytecode_pc = expr->bytecode_pc;
	    list_expr.u.list.items = expr->u.verb_call.args;
	    args_temp = lower_expr(ctx, program, &list_expr);
	    (void) args_temp;

	    append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	    call_tac = new_tac(ctx, HIR_TAC_CALL_VERB, expr->source_lineno);
	    call_tac->dst = new_temp(ctx);
	    call_tac->src1 = obj_temp;
	    call_tac->src2 = verb_temp;
	    call_tac->resume_key = expr->u.verb_call.resume_key;
	    call_tac->bytecode_pc = expr->bytecode_pc;
	    snapshot_lower_stack(ctx, call_tac);
	    append_tac(program, call_tac);
	    ctx->lower_stack_depth -= 3;
	    push_lower_stack(ctx, call_tac->dst);
	    return call_tac->dst;
	}
    case HIR_EXPR_COND:
	return lower_cond_expr(ctx, program, expr);
    case HIR_EXPR_CATCH:
	return lower_catch_expr(ctx, program, expr);
    case HIR_EXPR_LENGTH:
	{
	    if (ctx->current_length_base > 0) {
		int len_temp = new_temp(ctx);
		instr = new_tac(ctx, HIR_TAC_UNARY, expr->source_lineno);
		instr->bytecode_pc = expr->bytecode_pc;
		instr->dst = len_temp;
		instr->src1 = ctx->current_length_base;
		instr->op = HIR_OP_LENGTH;
		snapshot_lower_stack(ctx, instr);
		append_tac(program, instr);
		push_lower_stack(ctx, len_temp);
		return len_temp;
	    }
	    return append_unsupported_tac(ctx, program,
					  "Length expression ($) used outside indexed context",
					  expr->source_lineno);
	}
    default:
	return append_unsupported_tac(ctx, program,
				      "Unsupported HIR expression in TAC lowering",
				      expr->source_lineno);
    }
}

static void
lower_if(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    HIRCondArm *arm;
    int base_depth = ctx->lower_stack_depth;
    int done_label = new_label(ctx);

    for (arm = stmt->u.if_stmt.arms; arm; arm = arm->next) {
	int next_label = new_label(ctx);
	int cond;

	ctx->lower_stack_depth = base_depth;
	cond = lower_expr(ctx, program, arm->condition);

	append_branch_false(ctx, program, cond, next_label, stmt->source_lineno,
			    arm->bytecode_pc);
	ctx->lower_stack_depth--;
	lower_stmt_list(ctx, program, arm->body);
	append_jump(ctx, program, done_label, stmt->source_lineno);
	append_label(ctx, program, next_label, stmt->source_lineno);
    }

    ctx->lower_stack_depth = base_depth;
    lower_stmt_list(ctx, program, stmt->u.if_stmt.otherwise);
    append_label(ctx, program, done_label, stmt->source_lineno);
	ctx->lower_stack_depth = base_depth;
}

static void
lower_while(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    int top_label = new_label(ctx);
    int done_label = new_label(ctx);
    int cond;
    HIRLoopContext loop;

    loop.loop_id = stmt->u.loop.loop_id;
    loop.cont_label = top_label;
    loop.done_label = done_label;
    loop.saved_depth = ctx->lower_stack_depth;
    loop.finally_context = ctx->current_finally;
    loop.parent = ctx->current_loop;
    ctx->current_loop = &loop;

    append_label(ctx, program, top_label, stmt->source_lineno);
    cond = lower_expr(ctx, program, stmt->u.loop.condition);
    append_branch_false(ctx, program, cond, done_label, stmt->source_lineno,
			stmt->bytecode_pc);
    ctx->lower_stack_depth--;
    lower_stmt_list(ctx, program, stmt->u.loop.body);
    append_jump(ctx, program, top_label, stmt->source_lineno);
    append_label(ctx, program, done_label, stmt->source_lineno);

    ctx->current_loop = loop.parent;
}

static void
lower_for_range(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    int base_depth = ctx->lower_stack_depth;
    int top_label = new_label(ctx);
    int cont_label = new_label(ctx);
    int done_label = new_label(ctx);
    int from_temp = lower_expr(ctx, program, stmt->u.for_range.from);
    int to_temp = lower_expr(ctx, program, stmt->u.for_range.to);
    int cond_temp;
    int curr_local;
    int is_last;
    int one_temp;
    int next_local;
    HIRTacInstr *instr;
    HIRTacInstr *const_tac;
    HIRTacInstr *add_tac;
    HIRLoopContext loop;

    loop.loop_id = stmt->u.for_range.local_id;
    loop.cont_label = cont_label;
    loop.done_label = done_label;
    loop.saved_depth = base_depth;
    loop.finally_context = ctx->current_finally;
    loop.parent = ctx->current_loop;
    ctx->current_loop = &loop;

    append_internal_store(ctx, program, stmt->u.for_range.local_id, from_temp,
			  stmt->source_lineno);

    /* top_label: start of each iteration */
    append_label(ctx, program, top_label, stmt->source_lineno);

    /* OP_FOR_RANGE charges one tick at the start of each iteration. */
    append_tick(ctx, program, stmt->source_lineno, stmt->bytecode_pc);

    /* Check if current loop variable <= to_temp (handles from > to on entry) */
    curr_local = append_internal_load(ctx, program, stmt->u.for_range.local_id,
				     stmt->source_lineno);
    replace_lower_stack(ctx, base_depth, curr_local);
    cond_temp = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_BINARY, stmt->source_lineno);
    instr->dst = cond_temp;
    instr->src1 = curr_local;
    instr->src2 = to_temp;
    instr->op = HIR_OP_LE;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
    append_unticked_branch_false(ctx, program, cond_temp, done_label,
				 stmt->source_lineno, stmt->bytecode_pc);

    append_internal_store(ctx, program, stmt->u.for_range.local_id, curr_local,
			  stmt->source_lineno);

    /* Lower loop body */
    lower_stmt_list(ctx, program, stmt->u.for_range.body);

    /* cont_label: continue lands here to step to next iteration */
    append_label(ctx, program, cont_label, stmt->source_lineno);

    /* Check if current loop variable has reached or exceeded to_temp */
    curr_local = append_internal_load(ctx, program, stmt->u.for_range.local_id,
				     stmt->source_lineno);
    is_last = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_BINARY, stmt->source_lineno);
    instr->dst = is_last;
    instr->src1 = curr_local;
    instr->src2 = to_temp;
    instr->op = HIR_OP_LT;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);

    /* If !(curr_local < to_temp), i.e. curr_local >= to_temp, exit loop */
    append_unticked_branch_false(ctx, program, is_last, done_label,
				 stmt->source_lineno, stmt->bytecode_pc);

    /* Increment loop variable */
    one_temp = new_temp(ctx);
    const_tac = new_tac(ctx, HIR_TAC_CONST, stmt->source_lineno);
    const_tac->dst = one_temp;
    const_tac->literal.type = TYPE_INT;
    const_tac->literal.v.num = 1;
    const_tac->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, const_tac);
    append_tac(program, const_tac);

    next_local = new_temp(ctx);
    add_tac = new_tac(ctx, HIR_TAC_BINARY, stmt->source_lineno);
    add_tac->dst = next_local;
    add_tac->src1 = curr_local;
    add_tac->src2 = one_temp;
    add_tac->op = HIR_OP_ADD;
    add_tac->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, add_tac);
    append_tac(program, add_tac);

    append_internal_store(ctx, program, stmt->u.for_range.local_id, next_local,
			  stmt->source_lineno);
    append_jump(ctx, program, top_label, stmt->source_lineno);

    /* done_label: loop exit */
    append_label(ctx, program, done_label, stmt->source_lineno);
    ctx->lower_stack_depth = base_depth;
    ctx->current_loop = loop.parent;
}

static void
lower_for_list(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    int base_depth = ctx->lower_stack_depth;
    int top_label = new_label(ctx);
    int done_label = new_label(ctx);
    int list_temp = lower_expr(ctx, program, stmt->u.for_list.iterable);
    int index_local = ctx->next_local++;
    int index_temp = new_temp(ctx);
    int length_temp;
    int cond_temp;
    int value_temp;
    int one_temp;
    int next_index;
    HIRTacInstr *instr;
    HIRLoopContext loop;

    loop.loop_id = stmt->u.for_list.local_id;
    loop.cont_label = top_label;
    loop.done_label = done_label;
    loop.saved_depth = base_depth;
    loop.finally_context = ctx->current_finally;
    loop.parent = ctx->current_loop;
    ctx->current_loop = &loop;

    instr = new_tac(ctx, HIR_TAC_CONST, stmt->source_lineno);
    instr->dst = index_temp;
    instr->literal.type = TYPE_INT;
    instr->literal.v.num = 1;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
    push_lower_stack(ctx, index_temp);
    append_internal_store(ctx, program, index_local, index_temp,
			  stmt->source_lineno);

    append_label(ctx, program, top_label, stmt->source_lineno);
    append_tick(ctx, program, stmt->source_lineno, stmt->bytecode_pc);
    index_temp = append_internal_load(ctx, program, index_local,
				      stmt->source_lineno);
    replace_lower_stack(ctx, ctx->lower_stack_depth - 1, index_temp);

    length_temp = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_UNARY, stmt->source_lineno);
    instr->dst = length_temp;
    instr->src1 = list_temp;
    instr->op = HIR_OP_LENGTH;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);

    cond_temp = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_BINARY, stmt->source_lineno);
    instr->dst = cond_temp;
    instr->src1 = index_temp;
    instr->src2 = length_temp;
    instr->op = HIR_OP_LE;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
    append_unticked_branch_false(ctx, program, cond_temp, done_label,
				 stmt->source_lineno, stmt->bytecode_pc);

    value_temp = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_BINARY, stmt->source_lineno);
    instr->dst = value_temp;
    instr->src1 = list_temp;
    instr->src2 = index_temp;
    instr->op = HIR_OP_INDEX;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
    append_internal_store(ctx, program, stmt->u.for_list.local_id, value_temp,
			  stmt->source_lineno);

    one_temp = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_CONST, stmt->source_lineno);
    instr->dst = one_temp;
    instr->literal.type = TYPE_INT;
    instr->literal.v.num = 1;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);

    next_index = new_temp(ctx);
    instr = new_tac(ctx, HIR_TAC_BINARY, stmt->source_lineno);
    instr->dst = next_index;
    instr->src1 = index_temp;
    instr->src2 = one_temp;
    instr->op = HIR_OP_ADD;
    instr->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, instr);
    append_tac(program, instr);
    append_internal_store(ctx, program, index_local, next_index,
			  stmt->source_lineno);
    replace_lower_stack(ctx, ctx->lower_stack_depth - 1, next_index);

    lower_stmt_list(ctx, program, stmt->u.for_list.body);
    append_jump(ctx, program, top_label, stmt->source_lineno);
    append_label(ctx, program, done_label, stmt->source_lineno);
    ctx->lower_stack_depth = base_depth;
    ctx->current_loop = loop.parent;
}

static void
lower_finally_handlers(HIRContext *ctx, HIRTacProgram *program,
		       HIRFinallyContext *stop)
{
    HIRFinallyContext *saved = ctx->current_finally;
    HIRFinallyContext *current;

    for (current = saved; current && current != stop; current = current->parent) {
	ctx->current_finally = current->parent;
	ctx->lower_stack_depth = current->base_depth;
	lower_stmt_list(ctx, program, current->handler);
    }
    ctx->current_finally = saved;
}

static void
lower_break(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    HIRLoopContext *loop = ctx->current_loop;
    HIRTacInstr *instr;

    if (stmt->u.exit_id != -1) {
	while (loop && loop->loop_id != stmt->u.exit_id)
	    loop = loop->parent;
    }

    if (!loop) {
	record_unsupported(ctx, "Unmatched break statement target");
	return;
    }

    lower_finally_handlers(ctx, program, loop->finally_context);
    ctx->lower_stack_depth = loop->saved_depth;
    append_charge_tick(ctx, program, stmt->source_lineno, stmt->bytecode_pc);
    instr = new_tac(ctx, HIR_TAC_JUMP, stmt->source_lineno);
    instr->label = loop->done_label;
    instr->bytecode_pc = stmt->bytecode_pc;
    append_tac(program, instr);
}

static void
lower_continue(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    HIRLoopContext *loop = ctx->current_loop;
    HIRTacInstr *instr;

    if (stmt->u.exit_id != -1) {
	while (loop && loop->loop_id != stmt->u.exit_id)
	    loop = loop->parent;
    }

    if (!loop) {
	record_unsupported(ctx, "Unmatched continue statement target");
	return;
    }

    lower_finally_handlers(ctx, program, loop->finally_context);
    ctx->lower_stack_depth = loop->saved_depth;
    append_charge_tick(ctx, program, stmt->source_lineno, stmt->bytecode_pc);
    instr = new_tac(ctx, HIR_TAC_JUMP, stmt->source_lineno);
    instr->label = loop->cont_label;
    instr->bytecode_pc = stmt->bytecode_pc;
    append_tac(program, instr);
}

static void
lower_try_finally(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    int base_depth = ctx->lower_stack_depth;
    int finally_val = new_temp(ctx);
    HIRTacInstr *finally_marker;
    HIRFinallyContext finally_context;

    finally_marker = new_tac(ctx, HIR_TAC_CONST, stmt->source_lineno);
    finally_marker->dst = finally_val;
    finally_marker->literal.type = TYPE_FINALLY;
    finally_marker->literal.v.num = stmt->u.try_finally.handler_pc;
    finally_marker->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, finally_marker);
    append_tac(program, finally_marker);
    push_lower_stack_slot(ctx, finally_val, RSS_FINALLY,
			  stmt->u.try_finally.handler_pc);

    finally_context.handler = stmt->u.try_finally.handler;
    finally_context.base_depth = base_depth;
    finally_context.parent = ctx->current_finally;
    ctx->current_finally = &finally_context;
    lower_stmt_list(ctx, program, stmt->u.try_finally.body);
    ctx->current_finally = finally_context.parent;

    ctx->lower_stack_depth = base_depth;
    lower_stmt_list(ctx, program, stmt->u.try_finally.handler);
}

static void
lower_try_except(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    int base_depth = ctx->lower_stack_depth;
    int saved_error_label = ctx->current_error_label;
    HIRExceptArm *ex;
    int arm_count = 0;
    int done_label = new_label(ctx);
    int catch_marker_val;
    HIRTacInstr *catch_marker;

    for (ex = stmt->u.try_except.excepts; ex; ex = ex->next)
	arm_count++;

    for (ex = stmt->u.try_except.excepts; ex; ex = ex->next) {
	int codes_val = lower_codes(ctx, program, ex->codes,
				    ex->source_lineno, stmt->bytecode_pc);
	int handler_label = new_label(ctx);
	int handler_pc_val = new_temp(ctx);
	HIRTacInstr *handler_pc;

	(void) codes_val;
	ex->label = handler_label;
	handler_pc = new_tac(ctx, HIR_TAC_CONST, ex->source_lineno);
	handler_pc->dst = handler_pc_val;
	handler_pc->literal.type = TYPE_INT;
	handler_pc->literal.v.num = ex->handler_pc;
	handler_pc->bytecode_pc = stmt->bytecode_pc;
	snapshot_lower_stack(ctx, handler_pc);
	append_tac(program, handler_pc);
	push_lower_stack_slot(ctx, handler_pc_val, RSS_HANDLER_PC,
			      ex->handler_pc);
    }

    catch_marker_val = new_temp(ctx);
    catch_marker = new_tac(ctx, HIR_TAC_CONST, stmt->source_lineno);
    catch_marker->dst = catch_marker_val;
    catch_marker->literal.type = TYPE_CATCH;
    catch_marker->literal.v.num = arm_count;
    catch_marker->bytecode_pc = stmt->bytecode_pc;
    snapshot_lower_stack(ctx, catch_marker);
    append_tac(program, catch_marker);
    push_lower_stack_slot(ctx, catch_marker_val, RSS_CATCH, arm_count);

    if (arm_count == 1 && !stmt->u.try_except.excepts->codes
	&& stmt->u.try_except.excepts->local_id < 0)
	ctx->current_error_label = stmt->u.try_except.excepts->label;
    lower_stmt_list(ctx, program, stmt->u.try_except.body);
    ctx->current_error_label = saved_error_label;

    ctx->lower_stack_depth = base_depth;
    append_jump(ctx, program, done_label, stmt->source_lineno);

    for (ex = stmt->u.try_except.excepts; ex; ex = ex->next) {
	append_label(ctx, program, ex->label, ex->source_lineno);
	lower_stmt_list(ctx, program, ex->body);
	if (ex->next)
	    append_jump(ctx, program, done_label, ex->source_lineno);
    }

    append_label(ctx, program, done_label, stmt->source_lineno);
}

static void
lower_fork(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    (void) lower_expr(ctx, program, stmt->u.fork.time);
    append_deopt_boundary(ctx, program, stmt->source_lineno, stmt->bytecode_pc);
    if (ctx->lower_stack_depth)
	ctx->lower_stack_depth--;
}

static void
lower_stmt(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    HIRTacInstr *instr;
    int result = 0;

    switch (stmt->kind) {
    case HIR_STMT_SEQUENCE:
	lower_stmt_list(ctx, program, stmt);
	break;
    case HIR_STMT_EXPR:
	if (stmt->u.expr && (stmt->u.expr->kind == HIR_EXPR_LITERAL
			     || stmt->u.expr->kind == HIR_EXPR_LOCAL_LOAD))
	    break;
	(void) lower_expr(ctx, program, stmt->u.expr);
	if (ctx->lower_stack_depth)
	    ctx->lower_stack_depth--;
	break;
    case HIR_STMT_RETURN:
	if (stmt->u.expr) {
	    result = lower_expr(ctx, program, stmt->u.expr);
	    lower_finally_handlers(ctx, program, 0);
	    ctx->lower_stack_depth = 0;
	    push_lower_stack(ctx, result);
	}
	else
	    lower_finally_handlers(ctx, program, 0);
	instr = new_tac(ctx, stmt->u.expr ? HIR_TAC_RETURN : HIR_TAC_RETURN0,
			stmt->source_lineno);
	instr->bytecode_pc = stmt->bytecode_pc;
	if (stmt->u.expr)
	    instr->src1 = result;
	snapshot_lower_stack(ctx, instr);
	append_tac(program, instr);
	ctx->lower_stack_depth = 0;
	break;
    case HIR_STMT_IF:
	lower_if(ctx, program, stmt);
	break;
    case HIR_STMT_WHILE:
	lower_while(ctx, program, stmt);
	break;
    case HIR_STMT_FOR_RANGE:
	lower_for_range(ctx, program, stmt);
	break;
    case HIR_STMT_FOR_LIST:
	lower_for_list(ctx, program, stmt);
	break;
    case HIR_STMT_FORK:
	lower_fork(ctx, program, stmt);
	break;
    case HIR_STMT_TRY_FINALLY:
	lower_try_finally(ctx, program, stmt);
	break;
    case HIR_STMT_TRY_EXCEPT:
	lower_try_except(ctx, program, stmt);
	break;
    case HIR_STMT_BREAK:
	lower_break(ctx, program, stmt);
	break;
    case HIR_STMT_CONTINUE:
	lower_continue(ctx, program, stmt);
	break;
    default:
	(void) append_unsupported_tac(ctx, program,
				      "Unsupported HIR statement in TAC lowering",
				      stmt->source_lineno);
	break;
    }
}

static void
lower_stmt_list(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    HIRStmt *item;

    if (!stmt)
	return;

    if (stmt->kind == HIR_STMT_SEQUENCE)
	item = stmt->u.sequence;
    else
	item = stmt;

    for (; item; item = item->next)
	lower_stmt(ctx, program, item);
}

#ifdef HIR_TESTING
int
hir_test_resume_stack_is_safe(var_type *stack_types, unsigned stack_depth,
			      int call_operands)
{
    return resume_stack_is_safe(stack_types, stack_depth, call_operands);
}

int
hir_test_resume_stack_matches_point(ResumeStackSlot *stack_slots,
				    unsigned stack_depth,
				    const ResumePoint *point, int call_operands)
{
    return resume_stack_matches_point(stack_slots, stack_depth, point,
				      call_operands);
}

int
hir_test_boundary_ticks_charged(HIRTacKind kind, HIROp op)
{
	return jit_boundary_ticks_charged(kind, op);
}

int
hir_test_list_tail_owner_slot(int source_slot, unsigned int source_uses,
			      int next_slot)
{
    return jit_list_tail_owner_slot(source_slot, source_uses, next_slot);
}

int
hir_test_int_list_result(HIROp op, int left_is_int_list,
			 int right_is_int_list, var_type right_type)
{
    return jit_int_list_result(op, left_is_int_list, right_is_int_list,
			       right_type);
}

int
hir_test_all_copy_sources_are_int_lists(unsigned int sources,
					unsigned int proven_sources)
{
    return jit_all_copy_sources_are_int_lists(sources, proven_sources);
}

int
hir_test_int_list_has_exclusive_local(unsigned int matching_locals)
{
    return jit_int_list_has_exclusive_local(matching_locals);
}

int
hir_test_string_builtin_length_anchor(Bytecodes *bc, unsigned pc,
				      unsigned func, HIROp op)
{
    return is_string_builtin_length_anchor(bc, pc, func, op);
}

int
hir_test_infer_string_add_operand(HIROp op, int other_known,
				  var_type other_type, var_type *inferred_type)
{
    return infer_string_add_operand(op, other_known, other_type, inferred_type);
}

int
hir_test_binary_type_pair_is_valid(HIROp op, var_type left, var_type right)
{
    return binary_type_pair_is_valid(op, left, right);
}

unsigned short
hir_test_binary_operand_type_mask(HIROp op, int operand, int other_known,
				  var_type other_type)
{
    return binary_operand_type_mask(op, operand, other_known, other_type);
}

int
hir_test_unary_operand_defaults_to_list(HIROp op)
{
    return unary_operand_defaults_to_list(op);
}

int
hir_test_binary_operands_constrain_each_other(HIROp op)
{
    return binary_operands_constrain_each_other(op);
}

int
hir_test_infer_min_max_result(HIROp op, var_type left, var_type right,
			      var_type *result)
{
    return infer_min_max_result(op, left, right, result);
}

int
hir_test_infer_builtin_result_type(const char *name, var_type *result)
{
    return infer_builtin_result_type(name, result);
}

void
hir_test_initialize_inferred_value_types(var_type *types,
					 unsigned char *known,
					 unsigned char *tagged, int count)
{
    initialize_inferred_value_types(types, known, tagged, count);
}

void
hir_test_tag_unknown_inferred_value_types(var_type *types,
					  unsigned char *known,
					  unsigned char *tagged, int count)
{
    tag_unknown_inferred_value_types(types, known, tagged, count);
}

int
hir_test_is_uninitialized_entry_load(HIRTacKind kind, unsigned bytecode_pc,
				     int local_id, int first_user_local)
{
    return is_uninitialized_entry_load(kind, bytecode_pc, local_id,
				       first_user_local);
}

int
hir_test_builtin_entry_type(HIRTacKind kind, unsigned bytecode_pc,
			    int local_id, int first_user_local, var_type *type)
{
    return builtin_entry_type(kind, bytecode_pc, local_id, first_user_local,
			      type);
}

static HIRTacProgram *
new_test_tac_program(HIRContext *ctx)
{
    HIRTacProgram *program = hir_alloc(ctx, sizeof(HIRTacProgram));

    program->first = 0;
    program->last = 0;
    return program;
}

HIRTacProgram *
hir_test_tac_with_undefined_return(HIRContext *ctx)
{
    HIRTacProgram *program = new_test_tac_program(ctx);
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_RETURN, 1001);

    instr->src1 = 1;
    append_tac(program, instr);
    return program;
}

HIRTacProgram *
hir_test_tac_with_duplicate_temp(HIRContext *ctx)
{
    HIRTacProgram *program = new_test_tac_program(ctx);
    HIRTacInstr *first = new_tac(ctx, HIR_TAC_CONST, 1002);
    HIRTacInstr *second = new_tac(ctx, HIR_TAC_CONST, 1003);

    ctx->next_temp = 2;
    first->dst = 1;
    second->dst = 1;
    append_tac(program, first);
    append_tac(program, second);
    return program;
}

HIRCFG *
hir_test_cfg_with_missing_successor(HIRContext *ctx)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_RETURN0, 1004);
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *block = hir_alloc(ctx, sizeof(HIRBasicBlock));

    cfg->entry = block;
    cfg->blocks = block;
    cfg->last_block = block;
    cfg->num_blocks = 1;
    cfg->num_edges = 1;

    block->id = 1;
    block->first = instr;
    block->last = instr;
    block->next = 0;
    block->successors[0] = 0;
    block->successors[1] = 0;
    block->num_successors = 1;
    block->predecessor_count = 0;
    block->first_lineno = instr->source_lineno;
    block->last_lineno = instr->source_lineno;
    block->contains_unsupported = 0;

    return cfg;
}

static void
init_test_block(HIRBasicBlock *block, int id, HIRTacInstr *instr)
{
    block->id = id;
    block->first = instr;
    block->last = instr;
    block->next = 0;
    block->successors[0] = 0;
    block->successors[1] = 0;
    block->num_successors = 0;
    block->predecessor_count = 0;
    block->first_lineno = instr ? instr->source_lineno : 0;
    block->last_lineno = block->first_lineno;
    block->contains_unsupported = 0;
}

HIRCFG *
hir_test_cfg_with_external_successor(HIRContext *ctx)
{
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_JUMP, 1010);
    HIRTacInstr *external_tac = new_tac(ctx, HIR_TAC_RETURN0, 1011);
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *external = hir_alloc(ctx, sizeof(HIRBasicBlock));

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = entry;
    cfg->num_blocks = 1;
    cfg->num_edges = 1;

    init_test_block(entry, 1, entry_tac);
    init_test_block(external, 2, external_tac);
    entry->successors[0] = external;
    entry->num_successors = 1;
    external->predecessor_count = 1;

    return cfg;
}

HIRCFG *
hir_test_cfg_with_predecessor_mismatch(HIRContext *ctx)
{
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_JUMP, 1012);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN0, 1013);
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = join;
    cfg->num_blocks = 2;
    cfg->num_edges = 1;

    init_test_block(entry, 1, entry_tac);
    init_test_block(join, 2, join_tac);
    entry->next = join;
    entry->successors[0] = join;
    entry->num_successors = 1;
    join->predecessor_count = 0;

    return cfg;
}

HIRCFG *
hir_test_cfg_with_duplicate_block_id(HIRContext *ctx)
{
    HIRTacInstr *first_tac = new_tac(ctx, HIR_TAC_RETURN0, 1014);
    HIRTacInstr *second_tac = new_tac(ctx, HIR_TAC_RETURN0, 1015);
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *first = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *second = hir_alloc(ctx, sizeof(HIRBasicBlock));

    cfg->entry = first;
    cfg->blocks = first;
    cfg->last_block = second;
    cfg->num_blocks = 2;
    cfg->num_edges = 0;

    init_test_block(first, 1, first_tac);
    init_test_block(second, 1, second_tac);
    first->next = second;

    return cfg;
}

HIRCFG *
hir_test_cfg_with_critical_edge(HIRContext *ctx)
{
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_BRANCH_FALSE, 1016);
    HIRTacInstr *then_tac = new_tac(ctx, HIR_TAC_JUMP, 1017);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN0, 1018);
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *then_block = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));

    entry_tac->src1 = 1;
    entry_tac->label = 1;
    then_tac->label = 1;

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = join;
    cfg->num_blocks = 3;
    cfg->num_edges = 3;

    init_test_block(entry, 1, entry_tac);
    init_test_block(then_block, 2, then_tac);
    init_test_block(join, 3, join_tac);

    entry->next = then_block;
    then_block->next = join;

    entry->successors[0] = join;
    entry->successors[1] = then_block;
    entry->num_successors = 2;
    then_block->successors[0] = join;
    then_block->num_successors = 1;
    then_block->predecessor_count = 1;
    join->predecessor_count = 2;

    return cfg;
}

static HIRSSAProgram *
new_test_ssa_program(HIRContext *ctx, HIRSSAInstr *first, HIRSSAInstr *last,
		     int instruction_count, int value_count)
{
    HIRSSAProgram *ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    HIRSSABlock *block = hir_alloc(ctx, sizeof(HIRSSABlock));

    block->id = 1;
    block->first_lineno = first ? first->source_lineno : 0;
    block->last_lineno = last ? last->source_lineno : block->first_lineno;
    block->first = first;
    block->last = last;
    block->next = 0;

    ssa->form = HIR_FORM_SSA;
    ssa->cfg = 0;
    ssa->blocks = block;
    ssa->last_block = block;
    ssa->num_blocks = 1;
    ssa->num_instructions = instruction_count;
    ssa->num_values = value_count;

    return ssa;
}

static HIRSSAInstr *
new_test_ssa_instr(HIRContext *ctx, HIRTacKind kind, unsigned lineno, int value)
{
    HIRSSAInstr *instr = hir_alloc(ctx, sizeof(HIRSSAInstr));

    memset(instr, 0, sizeof(HIRSSAInstr));
    instr->kind = kind;
    instr->source_lineno = lineno;
    instr->bytecode_pc = NO_BYTECODE_PC;
    instr->value = value;
    instr->local_id = -1;
    instr->op = HIR_OP_ADD;
    return instr;
}

static HIRPhiArg *
new_test_phi_arg(HIRContext *ctx, int block_id, int value, HIRPhiArg *next)
{
    HIRPhiArg *arg = hir_alloc(ctx, sizeof(HIRPhiArg));

    arg->block_id = block_id;
    arg->value = value;
    arg->next = next;
    return arg;
}

static HIRSSABlock *
new_test_ssa_block(HIRContext *ctx, int id, HIRSSAInstr *first,
		   HIRSSAInstr *last)
{
    HIRSSABlock *block = hir_alloc(ctx, sizeof(HIRSSABlock));

    block->id = id;
    block->first_lineno = first ? first->source_lineno : 0;
    block->last_lineno = last ? last->source_lineno : block->first_lineno;
    block->first = first;
    block->last = last;
    block->next = 0;
    return block;
}

HIRSSAProgram *
hir_test_ssa_with_use_before_def(HIRContext *ctx)
{
    HIRSSAInstr *instr = hir_alloc(ctx, sizeof(HIRSSAInstr));

    ctx->next_temp = 2;
    instr->kind = HIR_TAC_RETURN;
    instr->source_lineno = 1005;
    instr->value = 0;
    instr->src1 = 1;
    instr->src2 = 0;
    instr->label = 0;
    instr->local_id = -1;
    instr->op = HIR_OP_ADD;
    instr->next = 0;

    return new_test_ssa_program(ctx, instr, instr, 1, 0);
}

HIRSSAProgram *
hir_test_ssa_with_duplicate_def(HIRContext *ctx)
{
    HIRSSAInstr *first = hir_alloc(ctx, sizeof(HIRSSAInstr));
    HIRSSAInstr *second = hir_alloc(ctx, sizeof(HIRSSAInstr));

    ctx->next_temp = 2;
    first->kind = HIR_TAC_CONST;
    first->source_lineno = 1006;
    first->value = 1;
    first->src1 = 0;
    first->src2 = 0;
    first->label = 0;
    first->local_id = -1;
    first->op = HIR_OP_ADD;
    first->next = second;

    second->kind = HIR_TAC_CONST;
    second->source_lineno = 1007;
    second->value = 1;
    second->src1 = 0;
    second->src2 = 0;
    second->label = 0;
    second->local_id = -1;
    second->op = HIR_OP_ADD;
    second->next = 0;

    return new_test_ssa_program(ctx, first, second, 2, 2);
}

HIRSSAProgram *
hir_test_ssa_with_nondominating_use(HIRContext *ctx)
{
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *left = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *right = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRSSABlock *entry_ssa;
    HIRSSABlock *left_ssa;
    HIRSSABlock *right_ssa;
    HIRSSABlock *join_ssa;
    HIRSSAProgram *ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_BRANCH_FALSE, 1030);
    HIRTacInstr *left_tac = new_tac(ctx, HIR_TAC_JUMP, 1031);
    HIRTacInstr *right_tac = new_tac(ctx, HIR_TAC_JUMP, 1032);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN, 1033);
    HIRSSAInstr *condition = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1030, 1);
    HIRSSAInstr *branch = new_test_ssa_instr(ctx, HIR_TAC_BRANCH_FALSE, 1030, 0);
    HIRSSAInstr *left_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1031, 2);
    HIRSSAInstr *left_jump = new_test_ssa_instr(ctx, HIR_TAC_JUMP, 1031, 0);
    HIRSSAInstr *right_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1032, 3);
    HIRSSAInstr *right_jump = new_test_ssa_instr(ctx, HIR_TAC_JUMP, 1032, 0);
    HIRSSAInstr *ret = new_test_ssa_instr(ctx, HIR_TAC_RETURN, 1033, 0);

    ctx->next_temp = 4;
    entry_tac->src1 = 1;
    join_tac->src1 = 2;
    init_test_block(entry, 1, entry_tac);
    init_test_block(left, 2, left_tac);
    init_test_block(right, 3, right_tac);
    init_test_block(join, 4, join_tac);
    entry->next = left;
    left->next = right;
    right->next = join;
    entry->successors[0] = right;
    entry->successors[1] = left;
    entry->num_successors = 2;
    left->successors[0] = join;
    left->num_successors = 1;
    left->predecessor_count = 1;
    right->successors[0] = join;
    right->num_successors = 1;
    right->predecessor_count = 1;
    join->predecessor_count = 2;

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = join;
    cfg->num_blocks = 4;
    cfg->num_edges = 4;

    condition->next = branch;
    branch->src1 = 1;
    left_def->next = left_jump;
    right_def->next = right_jump;
    ret->src1 = 2;
    entry_ssa = new_test_ssa_block(ctx, 1, condition, branch);
    left_ssa = new_test_ssa_block(ctx, 2, left_def, left_jump);
    right_ssa = new_test_ssa_block(ctx, 3, right_def, right_jump);
    join_ssa = new_test_ssa_block(ctx, 4, ret, ret);
    entry_ssa->next = left_ssa;
    left_ssa->next = right_ssa;
    right_ssa->next = join_ssa;

    ssa->form = HIR_FORM_SSA;
    ssa->cfg = cfg;
    ssa->blocks = entry_ssa;
    ssa->last_block = join_ssa;
    ssa->num_blocks = 4;
    ssa->num_instructions = 7;
    ssa->num_values = 3;
    return ssa;
}

HIRSSAProgram *
hir_test_ssa_with_bad_phi_shape(HIRContext *ctx)
{
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_CONST, 1008);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN, 1009);
    HIRSSAProgram *ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    HIRSSABlock *entry_block = hir_alloc(ctx, sizeof(HIRSSABlock));
    HIRSSABlock *join_block = hir_alloc(ctx, sizeof(HIRSSABlock));
    HIRSSAInstr *def = hir_alloc(ctx, sizeof(HIRSSAInstr));
    HIRSSAInstr *phi = hir_alloc(ctx, sizeof(HIRSSAInstr));
    HIRPhiArg *first_arg = hir_alloc(ctx, sizeof(HIRPhiArg));
    HIRPhiArg *second_arg = hir_alloc(ctx, sizeof(HIRPhiArg));

    ctx->next_temp = 3;

    entry_tac->dst = 1;
    join_tac->src1 = 2;

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = join;
    cfg->num_blocks = 2;
    cfg->num_edges = 1;

    entry->id = 1;
    entry->first = entry_tac;
    entry->last = entry_tac;
    entry->next = join;
    entry->successors[0] = join;
    entry->successors[1] = 0;
    entry->num_successors = 1;
    entry->predecessor_count = 0;
    entry->first_lineno = 1008;
    entry->last_lineno = 1008;
    entry->contains_unsupported = 0;

    join->id = 2;
    join->first = join_tac;
    join->last = join_tac;
    join->next = 0;
    join->successors[0] = 0;
    join->successors[1] = 0;
    join->num_successors = 0;
    join->predecessor_count = 1;
    join->first_lineno = 1009;
    join->last_lineno = 1009;
    join->contains_unsupported = 0;

    def->kind = HIR_TAC_CONST;
    def->source_lineno = 1008;
    def->value = 1;
    def->src1 = 0;
    def->src2 = 0;
    def->label = 0;
    def->local_id = -1;
    def->op = HIR_OP_ADD;
    def->phi_args = 0;
    def->copies = 0;
    def->next = 0;

    first_arg->block_id = 1;
    first_arg->value = 1;
    first_arg->next = second_arg;
    second_arg->block_id = 1;
    second_arg->value = 1;
    second_arg->next = 0;

    phi->kind = HIR_TAC_PHI;
    phi->source_lineno = 1009;
    phi->value = 2;
    phi->src1 = 0;
    phi->src2 = 0;
    phi->label = 0;
    phi->local_id = 16;
    phi->op = HIR_OP_ADD;
    phi->phi_args = first_arg;
    phi->copies = 0;
    phi->next = 0;

    entry_block->id = 1;
    entry_block->first_lineno = 1008;
    entry_block->last_lineno = 1008;
    entry_block->first = def;
    entry_block->last = def;
    entry_block->next = join_block;

    join_block->id = 2;
    join_block->first_lineno = 1009;
    join_block->last_lineno = 1009;
    join_block->first = phi;
    join_block->last = phi;
    join_block->next = 0;

    ssa->form = HIR_FORM_SSA;
    ssa->cfg = cfg;
    ssa->blocks = entry_block;
    ssa->last_block = join_block;
    ssa->num_blocks = 2;
    ssa->num_instructions = 2;
    ssa->num_values = 2;

    return ssa;
}

HIRSSAProgram *
hir_test_ssa_with_late_phi(HIRContext *ctx)
{
    HIRSSAInstr *def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1016, 1);
    HIRSSAInstr *phi = new_test_ssa_instr(ctx, HIR_TAC_PHI, 1017, 2);

    ctx->next_temp = 3;
    def->next = phi;
    phi->local_id = 16;
    phi->phi_args = 0;

    return new_test_ssa_program(ctx, def, phi, 2, 2);
}

HIRSSAProgram *
hir_test_ssa_with_missing_phi_arg(HIRContext *ctx)
{
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *first = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *second = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRTacInstr *first_tac = new_tac(ctx, HIR_TAC_JUMP, 1018);
    HIRTacInstr *second_tac = new_tac(ctx, HIR_TAC_JUMP, 1019);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN, 1020);
    HIRSSAProgram *ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    HIRSSAInstr *first_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1018, 1);
    HIRSSAInstr *second_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1019, 2);
    HIRSSAInstr *phi = new_test_ssa_instr(ctx, HIR_TAC_PHI, 1020, 3);
    HIRSSABlock *first_block = new_test_ssa_block(ctx, 1, first_def, first_def);
    HIRSSABlock *second_block =
	new_test_ssa_block(ctx, 2, second_def, second_def);
    HIRSSABlock *join_block = new_test_ssa_block(ctx, 3, phi, phi);

    ctx->next_temp = 4;
    join_tac->src1 = 3;

    cfg->entry = first;
    cfg->blocks = first;
    cfg->last_block = join;
    cfg->num_blocks = 3;
    cfg->num_edges = 2;

    init_test_block(first, 1, first_tac);
    init_test_block(second, 2, second_tac);
    init_test_block(join, 3, join_tac);
    first->next = second;
    second->next = join;
    first->successors[0] = join;
    first->num_successors = 1;
    second->successors[0] = join;
    second->num_successors = 1;
    join->predecessor_count = 2;

    phi->local_id = 16;
    phi->phi_args = new_test_phi_arg(ctx, 1, 1, 0);

    first_block->next = second_block;
    second_block->next = join_block;
    ssa->cfg = cfg;
    ssa->blocks = first_block;
    ssa->last_block = join_block;
    ssa->num_blocks = 3;
    ssa->num_instructions = 3;
    ssa->num_values = 3;

    return ssa;
}

HIRSSAProgram *
hir_test_ssa_with_nonpred_phi_arg(HIRContext *ctx)
{
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *extra = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_JUMP, 1021);
    HIRTacInstr *extra_tac = new_tac(ctx, HIR_TAC_RETURN0, 1022);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN, 1023);
    HIRSSAProgram *ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    HIRSSAInstr *entry_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1021, 1);
    HIRSSAInstr *extra_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1022, 2);
    HIRSSAInstr *phi = new_test_ssa_instr(ctx, HIR_TAC_PHI, 1023, 3);
    HIRSSABlock *entry_block = new_test_ssa_block(ctx, 1, entry_def, entry_def);
    HIRSSABlock *extra_block = new_test_ssa_block(ctx, 2, extra_def, extra_def);
    HIRSSABlock *join_block = new_test_ssa_block(ctx, 3, phi, phi);

    ctx->next_temp = 4;
    join_tac->src1 = 3;

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = join;
    cfg->num_blocks = 3;
    cfg->num_edges = 1;

    init_test_block(entry, 1, entry_tac);
    init_test_block(extra, 2, extra_tac);
    init_test_block(join, 3, join_tac);
    entry->next = extra;
    extra->next = join;
    entry->successors[0] = join;
    entry->num_successors = 1;
    join->predecessor_count = 1;

    phi->local_id = 16;
    phi->phi_args = new_test_phi_arg(ctx, 2, 2, 0);

    entry_block->next = extra_block;
    extra_block->next = join_block;
    ssa->cfg = cfg;
    ssa->blocks = entry_block;
    ssa->last_block = join_block;
    ssa->num_blocks = 3;
    ssa->num_instructions = 3;
    ssa->num_values = 3;

    return ssa;
}

HIRSSAProgram *
hir_test_ssa_with_critical_phi_edge(HIRContext *ctx)
{
    HIRCFG *cfg = hir_alloc(ctx, sizeof(HIRCFG));
    HIRBasicBlock *entry = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *then_block = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRBasicBlock *join = hir_alloc(ctx, sizeof(HIRBasicBlock));
    HIRTacInstr *entry_tac = new_tac(ctx, HIR_TAC_BRANCH_FALSE, 1024);
    HIRTacInstr *then_tac = new_tac(ctx, HIR_TAC_JUMP, 1025);
    HIRTacInstr *join_tac = new_tac(ctx, HIR_TAC_RETURN, 1026);
    HIRSSAProgram *ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    HIRSSAInstr *entry_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1024, 1);
    HIRSSAInstr *entry_branch =
	new_test_ssa_instr(ctx, HIR_TAC_BRANCH_FALSE, 1024, 0);
    HIRSSAInstr *then_def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1025, 2);
    HIRSSAInstr *then_jump = new_test_ssa_instr(ctx, HIR_TAC_JUMP, 1025, 0);
    HIRSSAInstr *phi = new_test_ssa_instr(ctx, HIR_TAC_PHI, 1026, 3);
    HIRSSAInstr *ret = new_test_ssa_instr(ctx, HIR_TAC_RETURN, 1026, 0);
    HIRSSABlock *entry_block;
    HIRSSABlock *then_ssa_block;
    HIRSSABlock *join_block;

    ctx->next_temp = 4;
    entry_tac->src1 = 1;
    entry_tac->label = 1;
    then_tac->label = 1;
    join_tac->src1 = 3;

    cfg->entry = entry;
    cfg->blocks = entry;
    cfg->last_block = join;
    cfg->num_blocks = 3;
    cfg->num_edges = 3;

    init_test_block(entry, 1, entry_tac);
    init_test_block(then_block, 2, then_tac);
    init_test_block(join, 3, join_tac);
    entry->next = then_block;
    then_block->next = join;
    entry->successors[0] = join;
    entry->successors[1] = then_block;
    entry->num_successors = 2;
    then_block->successors[0] = join;
    then_block->num_successors = 1;
    then_block->predecessor_count = 1;
    join->predecessor_count = 2;

    entry_def->next = entry_branch;
    entry_branch->src1 = 1;
    entry_branch->label = 1;
    then_def->next = then_jump;
    then_jump->label = 1;
    phi->local_id = 16;
    phi->phi_args = new_test_phi_arg(ctx, 1, 1,
				     new_test_phi_arg(ctx, 2, 2, 0));
    phi->next = ret;
    ret->src1 = 3;

    entry_block = new_test_ssa_block(ctx, 1, entry_def, entry_branch);
    then_ssa_block = new_test_ssa_block(ctx, 2, then_def, then_jump);
    join_block = new_test_ssa_block(ctx, 3, phi, ret);
    entry_block->next = then_ssa_block;
    then_ssa_block->next = join_block;

    ssa->form = HIR_FORM_SSA;
    ssa->cfg = cfg;
    ssa->blocks = entry_block;
    ssa->last_block = join_block;
    ssa->num_blocks = 3;
    ssa->num_instructions = 6;
    ssa->num_values = 3;

    return ssa;
}

HIRSSAProgram *
hir_test_out_ssa_with_phi(HIRContext *ctx)
{
    HIRSSAInstr *def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1027, 1);
    HIRSSAInstr *phi = new_test_ssa_instr(ctx, HIR_TAC_PHI, 1028, 2);
    HIRSSAProgram *ssa;

    ctx->next_temp = 3;
    def->next = phi;
    phi->local_id = 16;
    ssa = new_test_ssa_program(ctx, def, phi, 2, 2);
    ssa->form = HIR_FORM_OUT_OF_SSA;

    return ssa;
}

HIRSSAProgram *
hir_test_out_ssa_with_bad_copy_source(HIRContext *ctx)
{
    HIRSSAInstr *def = new_test_ssa_instr(ctx, HIR_TAC_CONST, 1029, 1);
    HIRSSAInstr *copy_instr =
	new_test_ssa_instr(ctx, HIR_TAC_PARALLEL_COPY, 1030, 0);
    HIRParallelCopy *copy = hir_alloc(ctx, sizeof(HIRParallelCopy));
    HIRSSAProgram *ssa;

    ctx->next_temp = 3;
    copy->dst = 2;
    copy->src = 99;
    copy->next = 0;
    copy_instr->copies = copy;
    def->next = copy_instr;

    ssa = new_test_ssa_program(ctx, def, copy_instr, 2, 2);
    ssa->form = HIR_FORM_OUT_OF_SSA;

    return ssa;
}
#endif
