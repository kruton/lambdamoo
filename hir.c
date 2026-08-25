#include "hir.h"

#include "config.h"
#include "options.h"

#if defined(ENABLE_JIT) && !defined(HIR_TESTING)
#include "jit_internal.h"
#endif

#include "my-stdio.h"

#include "arena.h"
#include "integer_arithmetic.h"
#include "opcode.h"
#include "program.h"
#include "storage.h"

#include <stddef.h>
#include <string.h>

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
    HIRArg *next;
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
	    HIRExpr *body;
	    HIRArg *codes;
	    HIRExpr *handler;
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
    int dst;
    int src1;
    int src2;
    int label;
    int local_id;
    HIROp op;
    Var literal;
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
    int value;
    int src1;
    int src2;
    int label;
    int local_id;
    HIROp op;
    Var literal;
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

struct HIRContext {
    Arena *arena;
    Names *var_names;
    int error_count;
    const char *error_msg;
    int next_temp;
    int next_label;
    int next_local;
    unsigned current_code_unit;
};

static void *hir_alloc(HIRContext *, size_t);
static HIRExpr *lift_expr(HIRContext *, Expr *);
static HIRStmt *lift_stmt_list(HIRContext *, Stmt *);
static int lower_expr(HIRContext *, HIRTacProgram *, HIRExpr *);
static void lower_stmt_list(HIRContext *, HIRTacProgram *, HIRStmt *);
static void record_unsupported(HIRContext *, const char *);
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
    ctx->current_code_unit = 0;

    return ctx;
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
	record_unsupported(ctx, "Invalid local id in TAC");
}

static void
verify_temp_use(HIRContext *ctx, int temp, unsigned char *defined,
		int max_temp)
{
    if (temp <= 0 || temp > max_temp || !defined[temp])
	record_unsupported(ctx, "TAC temp used before definition");
}

static void
verify_temp_def(HIRContext *ctx, int temp, unsigned char *defined,
		int max_temp)
{
    if (temp <= 0 || temp > max_temp) {
	record_unsupported(ctx, "Invalid TAC temp definition");
	return;
    }

    if (defined[temp])
	record_unsupported(ctx, "Duplicate TAC temp definition");
    defined[temp] = 1;
}

static void
verify_label_def(HIRContext *ctx, int label, unsigned char *defined,
		 int max_label)
{
    if (label <= 0 || label > max_label) {
	record_unsupported(ctx, "Invalid TAC label definition");
	return;
    }

    if (defined[label])
	record_unsupported(ctx, "Duplicate TAC label definition");
    defined[label] = 1;
}

static void
verify_label_use(HIRContext *ctx, int label, unsigned char *referenced,
		 int max_label)
{
    if (label <= 0 || label > max_label) {
	record_unsupported(ctx, "Invalid TAC label reference");
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
	    break;
	case HIR_TAC_CONST:
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
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_BINARY:
	    verify_temp_use(ctx, instr->src1, defined_temps, max_temp);
	    verify_temp_use(ctx, instr->src2, defined_temps, max_temp);
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
	    record_unsupported(ctx, "Unsupported TAC instruction");
	    if (instr->dst > 0)
		verify_temp_def(ctx, instr->dst, defined_temps, max_temp);
	    break;
	case HIR_TAC_PHI:
	    record_unsupported(ctx, "Phi node in TAC");
	    break;
	case HIR_TAC_PARALLEL_COPY:
	    record_unsupported(ctx, "Parallel copy in TAC");
	    break;
	}
    }

    for (i = 1; i <= max_label; i++) {
	if (referenced_labels[i] && !defined_labels[i])
	    record_unsupported(ctx, "TAC label referenced but not defined");
    }

    return ctx->error_count == errors_before;
}

static int
tac_is_terminator(HIRTacInstr *instr)
{
    return instr
	&& (instr->kind == HIR_TAC_JUMP
	    || instr->kind == HIR_TAC_BRANCH_FALSE
	    || instr->kind == HIR_TAC_RETURN
	    || instr->kind == HIR_TAC_RETURN0);
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
	record_unsupported(ctx, "CFG edge target label has no block");
	return 0;
    }

    return label_blocks[label];
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
	    add_edge(cfg, block, block->next);
	    break;
	}
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
	return -1;
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

    jump->kind = HIR_TAC_JUMP;
    jump->source_lineno = from && from->last ? from->last->source_lineno : 0;
    jump->bytecode_pc = NO_BYTECODE_PC;
    if (jump->source_lineno == 0 && to)
	jump->source_lineno = to->first_lineno;
    jump->dst = 0;
    jump->src1 = 0;
    jump->src2 = 0;
    jump->label = to && to->first && to->first->kind == HIR_TAC_LABEL
	? to->first->label : 0;
    jump->local_id = -1;
    jump->op = HIR_OP_ADD;
    jump->literal.type = TYPE_NONE;
    jump->next = 0;

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
	record_unsupported(ctx, "CFG has invalid entry block");

    for (block = cfg->blocks; block; block = block->next) {
	HIRBasicBlock *other;
	int expected_successors;
	int i;

	block_count++;
	if (block->id <= 0)
	    record_unsupported(ctx, "CFG block has invalid id");
	for (other = cfg->blocks; other && other != block; other = other->next) {
	    if (other->id == block->id)
		record_unsupported(ctx, "CFG has duplicate block id");
	}

	if (!block->first || !block->last)
	    record_unsupported(ctx, "CFG block has missing TAC bounds");

	if (block->num_successors < 0 || block->num_successors > 2)
	    record_unsupported(ctx, "CFG block has invalid successor count");

	for (i = 0; i < block->num_successors; i++) {
	    if (!block->successors[i])
		record_unsupported(ctx, "CFG block has missing successor");
	    else if (!cfg_contains_block_ptr(cfg, block->successors[i]))
		record_unsupported(ctx, "CFG successor is not in CFG block list");
	}

	expected_successors = cfg_expected_successors(block->last);
	if (expected_successors >= 0
	    && block->num_successors != expected_successors)
	    record_unsupported(ctx, "CFG block has invalid terminator successors");

	if (block->predecessor_count
	    != cfg_actual_predecessor_count(cfg, block))
	    record_unsupported(ctx, "CFG predecessor count mismatch");

    }

    if (block_count != cfg->num_blocks)
	record_unsupported(ctx, "CFG block count mismatch");
    if (cfg->last_block && cfg->last_block->next)
	record_unsupported(ctx, "CFG last block is not terminal");

    return ctx->error_count == errors_before;
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
	record_unsupported(ctx, "Dominator tree has no reachable entry");
    else if (dom->idom[cfg->entry->id] != cfg->entry)
	record_unsupported(ctx, "Dominator tree entry idom is invalid");

    for (i = 0; i < dom->num_reachable; i++) {
	HIRBasicBlock *block = dom->rpo[i];
	HIRBasicBlock *runner;
	int steps;

	if (!block || block->id <= 0 || block->id > dom->max_block_id) {
	    record_unsupported(ctx, "Dominator tree has invalid RPO block");
	    continue;
	}
	if (dom->block_by_id[block->id] != block)
	    record_unsupported(ctx, "Dominator tree block index mismatch");
	if (dom->rpo_index[block->id] != i)
	    record_unsupported(ctx, "Dominator tree RPO index mismatch");
	if (!dom->idom[block->id]) {
	    record_unsupported(ctx, "Dominator tree missing reachable idom");
	    continue;
	}
	if (!dom_contains_block(dom, dom->idom[block->id])
	    || dom->rpo_index[dom->idom[block->id]->id] < 0)
	    record_unsupported(ctx, "Dominator tree idom is unreachable");
	if (block != cfg->entry && dom->idom[block->id] == block)
	    record_unsupported(ctx, "Dominator tree non-entry self idom");

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
	    record_unsupported(ctx, "Dominator tree idom chain misses entry");
    }

    return ctx->error_count == errors_before;
}

static int
ssa_defines_value(HIRSSAInstr *instr)
{
    return instr
	&& (instr->kind == HIR_TAC_CONST
	    || instr->kind == HIR_TAC_LOAD_LOCAL
	    || instr->kind == HIR_TAC_UNARY
	    || instr->kind == HIR_TAC_BINARY
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
    instr->value = tac->dst;
    instr->src1 = tac->src1;
    instr->src2 = tac->src2;
    instr->label = tac->label;
    instr->local_id = tac->local_id;
    instr->op = tac->op;
    instr->literal = tac->literal;
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
	    if (tac->kind == HIR_TAC_STORE_LOCAL
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
	record_unsupported(ctx, "Invalid SSA local version stack");
	return 0;
    }

    if (stack_tops[v] == 0) {
	/* Empty stack! Insert implicit load at entry block. */
	int t_init = ctx->next_temp++;
	HIRSSAInstr *load = hir_alloc(ctx, sizeof(HIRSSAInstr));
	load->kind = HIR_TAC_LOAD_LOCAL;
	load->source_lineno = entry_block ? entry_block->first_lineno : 0;
	load->bytecode_pc = NO_BYTECODE_PC;
	load->value = t_init;
	load->src1 = 0;
	load->src2 = 0;
	load->label = 0;
	load->local_id = v;
	load->op = HIR_OP_ADD;
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
	ssa_block->first = placed_phis[b->id];
	HIRSSAInstr *last_phi = 0;
	curr_phi = placed_phis[b->id];
	while (curr_phi) {
	    curr_phi->value = ctx->next_temp++;
	    if (curr_phi->local_id >= 0 && curr_phi->local_id < num_locals)
		stacks[curr_phi->local_id * max_depth
		       + stack_tops[curr_phi->local_id]++] = curr_phi->value;
	    else
		record_unsupported(ctx, "Invalid SSA phi local id");
	    last_phi = curr_phi;
	    curr_phi = curr_phi->next;
	    ssa->num_instructions++;
	    ssa->num_values++;
	}
	ssa_block->last = last_phi;
    }

    /* 2. Traverse instructions of b */
    for (tac = b->first; tac; tac = tac->next) {
	int src1_renamed = (tac->src1 > 0 && tac->src1 < temp_map_size) ? temp_map[tac->src1] : tac->src1;
	int src2_renamed = (tac->src2 > 0 && tac->src2 < temp_map_size) ? temp_map[tac->src2] : tac->src2;

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
		record_unsupported(ctx, "Invalid SSA store local id");
	} else {
	    HIRSSAInstr *ssa_inst = new_ssa_instr(ctx, tac);
	    ssa_inst->src1 = src1_renamed;
	    ssa_inst->src2 = src2_renamed;
	    if (tac->dst > 0 && tac->dst < temp_map_size)
		temp_map[tac->dst] = tac->dst;
	    emit_ssa_instr(ssa, ssa_block, ssa_inst);
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
	if (tac->kind == HIR_TAC_STORE_LOCAL
	    && tac->local_id >= 0 && tac->local_id < num_locals)
	    stack_tops[tac->local_id]--;
	if (tac == b->last)
	    break;
    }
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

    /* Find all defs for each local variable */
    defs = hir_calloc(ctx, num_locals, sizeof(HIRBlockList *));
    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	HIRTacInstr *tac;
	for (tac = cfg_block->first; tac; tac = tac->next) {
	    if (tac->kind == HIR_TAC_STORE_LOCAL) {
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
		    if (!added[y->id]) {
			/* Insert Phi node at y for variable i */
			HIRSSAInstr *phi = hir_alloc(ctx, sizeof(HIRSSAInstr));
			phi->kind = HIR_TAC_PHI;
			phi->source_lineno = y->first_lineno;
			phi->bytecode_pc = NO_BYTECODE_PC;
			phi->value = 0; /* filled in renaming */
			phi->src1 = 0;
			phi->src2 = 0;
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

    /* Copy instructions of unreachable blocks as-is */
    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	if (!visited[cfg_block->id]) {
	    HIRSSABlock *ssa_block = ssa_blocks[cfg_block->id];
	    HIRTacInstr *tac;
	    for (tac = cfg_block->first; tac; tac = tac->next) {
		emit_ssa_instr(ssa, ssa_block, new_ssa_instr(ctx, tac));
		if (tac == cfg_block->last)
		    break;
	    }
	}
    }

    return ssa;
}

static void
verify_ssa_value_use(HIRContext *ctx, int value, unsigned char *defined,
		     int max_value)
{
    if (value <= 0 || value > max_value || !defined[value])
	record_unsupported(ctx, "SSA value used before definition");
}

static void
verify_ssa_value_def(HIRContext *ctx, int value, unsigned char *defined,
		     int max_value)
{
    if (value <= 0 || value > max_value) {
	record_unsupported(ctx, "Invalid SSA value definition");
	return;
    }

    if (defined[value])
	record_unsupported(ctx, "Duplicate SSA value definition");
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
	record_unsupported(ctx, "SSA phi block is not in CFG");
	return;
    }

    max_block_id = max_cfg_block_id(ssa->cfg);
    seen = hir_calloc(ctx, (size_t) max_block_id + 1, sizeof(unsigned char));
    for (arg = phi->phi_args; arg; arg = arg->next) {
	HIRBasicBlock *pred = cfg_block_for_id(ssa->cfg, arg->block_id);

	count++;
	if (!pred || arg->block_id <= 0 || arg->block_id > max_block_id) {
	    record_unsupported(ctx, "SSA phi has invalid predecessor arg");
	    continue;
	}
	if (seen[arg->block_id])
	    record_unsupported(ctx, "SSA phi has duplicate predecessor arg");
	seen[arg->block_id] = 1;
	if (!cfg_has_predecessor(ssa->cfg, cfg_block, arg->block_id))
	    record_unsupported(ctx, "SSA phi arg is not a CFG predecessor");
    }

    if (count != cfg_block->predecessor_count)
	record_unsupported(ctx, "SSA phi predecessor count mismatch");
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

    if (def_block[value] == use_block_id) {
	if (!phi_edge && def_order[value] >= use_order)
	    record_unsupported(ctx, "SSA definition does not precede use");
    } else if (!dom_block_dominates(dom, def_block[value], use_block_id)) {
	record_unsupported(ctx, "SSA definition does not dominate use");
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
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
		verify_ssa_dominating_use(ctx, dom, instr->src1, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		break;
	    case HIR_TAC_BINARY:
		verify_ssa_dominating_use(ctx, dom, instr->src1, block->id,
					   order, 0, max_value,
					   def_block, def_order);
		verify_ssa_dominating_use(ctx, dom, instr->src2, block->id,
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
	record_unsupported(ctx, "SSA verifier requires SSA form");

    max_value = ctx->next_temp - 1;
    defined = hir_alloc(ctx, (size_t) max_value + 1);
    for (i = 0; i <= max_value; i++)
	defined[i] = 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;
	int seen_non_phi = 0;

	block_count++;
	if (!block->first || !block->last)
	    record_unsupported(ctx, "SSA block has no instructions");

	for (instr = block->first; instr; instr = instr->next) {
	    instruction_count++;

	    switch (instr->kind) {
	    case HIR_TAC_TICK:
		break;
	    case HIR_TAC_CONST:
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
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_BINARY:
		verify_ssa_value_use(ctx, instr->src1, defined, max_value);
		verify_ssa_value_use(ctx, instr->src2, defined, max_value);
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
		    record_unsupported(ctx, "SSA phi appears after non-phi");
		verify_ssa_value_def(ctx, instr->value, defined, max_value);
		value_count++;
		break;
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_RETURN0:
		break;
	    case HIR_TAC_PARALLEL_COPY:
		record_unsupported(ctx, "Parallel copy in SSA form");
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
		instr->src1 = instr->src2 = 0;
		instr->phi_args = 0;
		changes++;
	    }
	    if (instr == block->last)
		break;
	}
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
		if (basic->last) {
		    basic->last->kind = HIR_TAC_JUMP;
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
    copy->kind = HIR_TAC_PARALLEL_COPY;
    copy->source_lineno = source_lineno;
    copy->bytecode_pc = NO_BYTECODE_PC;
    copy->value = 0;
    copy->src1 = 0;
    copy->src2 = 0;
    copy->label = 0;
    copy->local_id = -1;
    copy->op = HIR_OP_ADD;
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
	    record_unsupported(ctx, "SSA destruction could not find copy edge");
	    continue;
	}

	copy_block = ssa_block_for_id(ssa, copy_cfg_block->id);
	if (!copy_block) {
	    record_unsupported(ctx, "SSA destruction missing copy block");
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
	record_unsupported(ctx, "Cannot destroy unknown SSA form");
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
	record_unsupported(ctx, "Out-of-SSA value used before definition");
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
	record_unsupported(ctx, "Out-of-SSA verifier requires out-of-SSA form");
    (void) hir_verify_cfg(ctx, ssa->cfg);

    max_value = ctx->next_temp - 1;
    defined = hir_alloc(ctx, (size_t) max_value + 1);
    for (i = 0; i <= max_value; i++)
	defined[i] = 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	block_count++;
	if (!block->first || !block->last)
	    record_unsupported(ctx, "Out-of-SSA block has no instructions");

	for (instr = block->first; instr; instr = instr->next) {
	    instruction_count++;
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
		break;
	    case HIR_TAC_CONST:
	    case HIR_TAC_LOAD_LOCAL:
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BINARY:
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
		record_unsupported(ctx, "Phi node in out-of-SSA form");
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
	    case HIR_TAC_UNARY:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		break;
	    case HIR_TAC_BINARY:
		verify_out_ssa_use(ctx, instr->src1, defined, max_value);
		verify_out_ssa_use(ctx, instr->src2, defined, max_value);
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
			    record_unsupported(ctx,
					       "Invalid out-of-SSA copy destination");
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
	record_unsupported(ctx, "Out-of-SSA block count mismatch");
    if (instruction_count != ssa->num_instructions)
	record_unsupported(ctx, "Out-of-SSA instruction count mismatch");
    if (value_count != ssa->num_values)
	record_unsupported(ctx, "Out-of-SSA value count mismatch");
    if (cfg_critical_edge_count(ssa->cfg) != 0)
	record_unsupported(ctx, "Out-of-SSA CFG still has critical edges");

    return ctx->error_count == errors_before;
}

#if defined(ENABLE_JIT) && !defined(HIR_TESTING)
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
    case HIR_OP_EQ:
    case HIR_OP_NE:
    case HIR_OP_LT:
    case HIR_OP_LE:
    case HIR_OP_GT:
    case HIR_OP_GE:
	return 1;
    default:
	return 0;
    }
}

static int
jit_ssa_is_supported(HIRSSAProgram *ssa)
{
    HIRSSABlock *block;

    if (!ssa || ssa->form != HIR_FORM_OUT_OF_SSA)
	return 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_LOAD_LOCAL:
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
	    case HIR_TAC_RETURN0:
	    case HIR_TAC_PARALLEL_COPY:
		break;
	    case HIR_TAC_CONST:
		if (instr->literal.type != TYPE_INT)
		    return 0;
		break;
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BINARY:
		if (!jit_op_is_supported(instr->op))
		    return 0;
		break;
	    case HIR_TAC_STORE_LOCAL:
	    case HIR_TAC_UNSUPPORTED:
	    case HIR_TAC_PHI:
		return 0;
	    }
	    if (instr == block->last)
		break;
	}
    }
    return 1;
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
	return jit_extended_anchor_matches(bc, instr->bytecode_pc,
					   EOP_COMPLEMENT);
    }
    if (instr->kind == HIR_TAC_BINARY) {
	switch (instr->op) {
	case HIR_OP_ADD: return op == OP_ADD;
	case HIR_OP_SUB: return op == OP_MINUS;
	case HIR_OP_MUL: return op == OP_MULT;
	case HIR_OP_DIV: return op == OP_DIV;
	case HIR_OP_MOD: return op == OP_MOD;
	case HIR_OP_EXP:
	    return jit_extended_anchor_matches(bc, instr->bytecode_pc, EOP_EXP);
	case HIR_OP_EQ: return op == OP_EQ;
	case HIR_OP_NE: return op == OP_NE;
	case HIR_OP_LT: return op == OP_LT;
	case HIR_OP_LE: return op == OP_LE;
	case HIR_OP_GT: return op == OP_GT;
	case HIR_OP_GE: return op == OP_GE;
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
jit_ssa_anchors_are_valid(HIRSSAProgram *ssa, Program *bytecode_program)
{
    HIRSSABlock *block;
    Bytecodes *bc;

    if (!bytecode_program || !bytecode_program->main_vector.vector)
	return 0;
    bc = &bytecode_program->main_vector;
    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
	    case HIR_TAC_CONST:
	    case HIR_TAC_LOAD_LOCAL:
	    case HIR_TAC_UNARY:
	    case HIR_TAC_BINARY:
	    case HIR_TAC_BRANCH_FALSE:
	    case HIR_TAC_RETURN:
	    case HIR_TAC_RETURN0:
		if (instr->bytecode_pc == NO_BYTECODE_PC
		    || instr->bytecode_pc >= bc->size)
		    return 0;
		if ((instr->kind == HIR_TAC_UNARY
		     || instr->kind == HIR_TAC_BINARY)
		    && !jit_operation_anchor_matches(bc, instr))
		    return 0;
		if (instr->kind == HIR_TAC_RETURN
		    && bc->vector[instr->bytecode_pc] != OP_RETURN)
		    return 0;
		if (instr->kind == HIR_TAC_RETURN0
		    && bc->vector[instr->bytecode_pc] != OP_RETURN0)
		    return 0;
		if (instr->kind == HIR_TAC_BRANCH_FALSE
		    && bc->vector[instr->bytecode_pc] != OP_AND
		    && bc->vector[instr->bytecode_pc] != OP_OR
		    && bc->vector[instr->bytecode_pc] != OP_IF
		    && bc->vector[instr->bytecode_pc] != OP_EIF
		    && bc->vector[instr->bytecode_pc] != OP_WHILE
		    && !jit_extended_anchor_matches(bc, instr->bytecode_pc,
						    EOP_WHILE_ID))
		    return 0;
		break;
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_PARALLEL_COPY:
		break;
	    case HIR_TAC_STORE_LOCAL:
	    case HIR_TAC_UNSUPPORTED:
	    case HIR_TAC_PHI:
		return 0;
	    }
	    if (instr == block->last)
		break;
	}
    }
    return 1;
}

JITProgram *
hir_create_jit_program(HIRContext *ctx, HIRSSAProgram *ssa,
		       Program *bytecode_program)
{
    JITProgram *program;
    HIRSSABlock *ssa_block;

    if (!ctx || ctx->error_count || !jit_ssa_is_supported(ssa))
	return jit_program_unsupported("unsupported-program");
    if (!jit_ssa_anchors_are_valid(ssa, bytecode_program))
	return jit_program_unsupported("invalid-bytecode-anchor");

    program = mymalloc(sizeof(JITProgram), M_PROGRAM);
    memset(program, 0, sizeof(JITProgram));
    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = ctx->next_temp;
    program->num_vars = ctx->var_names ? ctx->var_names->size : 0;

    for (ssa_block = ssa->blocks; ssa_block; ssa_block = ssa_block->next) {
	HIRBasicBlock *cfg_block = cfg_block_for_id(ssa->cfg, ssa_block->id);
	HIRSSAInstr *ssa_instr;
	JITBlock *block = mymalloc(sizeof(JITBlock), M_PROGRAM);

	memset(block, 0, sizeof(JITBlock));
	block->id = ssa_block->id;
	if (cfg_block) {
	    int i;
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

	    memset(instr, 0, sizeof(JITInstruction));
	    instr->kind = ssa_instr->kind;
	    instr->source_lineno = ssa_instr->source_lineno;
	    instr->bytecode_pc = ssa_instr->bytecode_pc;
	    if (ssa_instr->bytecode_pc != NO_BYTECODE_PC)
		program->num_resume_anchors++;
	    instr->value = ssa_instr->value;
	    instr->src1 = ssa_instr->src1;
	    instr->src2 = ssa_instr->src2;
	    instr->local_id = ssa_instr->local_id;
	    instr->op = ssa_instr->op;
	    if (ssa_instr->kind == HIR_TAC_BINARY
		&& (ssa_instr->op == HIR_OP_DIV || ssa_instr->op == HIR_OP_MOD
		    || ssa_instr->op == HIR_OP_EXP || ssa_instr->op == HIR_OP_SHL
		    || ssa_instr->op == HIR_OP_SHR || ssa_instr->op == HIR_OP_LSHR))
		program->may_error = 1;
	    instr->literal = ssa_instr->kind == HIR_TAC_CONST
		? ssa_instr->literal.v.num : 0;
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
		break;
	    case HIR_TAC_CONST:
		fprintf(file, " t%d = ", instr->value);
		dump_var(file, instr->literal);
		break;
	    case HIR_TAC_LOAD_LOCAL:
		fprintf(file, " t%d = local[%d]", instr->value,
			instr->local_id);
		break;
	    case HIR_TAC_STORE_LOCAL:
		fprintf(file, " local[%d] = t%d", instr->local_id,
			instr->src1);
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
    case HIR_TAC_CONST:
	return "const";
    case HIR_TAC_LOAD_LOCAL:
	return "load_local";
    case HIR_TAC_STORE_LOCAL:
	return "store_local";
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
    return ssa ? ssa->form : -1;
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

static HIRExpr *
unsupported_expr(HIRContext *ctx, Expr *ast)
{
    HIRExpr *expr = new_expr(ctx, HIR_EXPR_UNSUPPORTED);

    expr->source_lineno = ast ? ast->lineno : 0;
    expr->u.unsupported.expr_kind = ast ? ast->kind : SizeOf_Expr_Kind;
    record_unsupported(ctx, "Unsupported AST expression in HIR lift");
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

    record_unsupported(ctx, "Unsupported non-local assignment in HIR lift");
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
	expr->u.cond.condition = lift_expr(ctx, ast->e.cond.condition);
	expr->u.cond.consequent = lift_expr(ctx, ast->e.cond.consequent);
	expr->u.cond.alternate = lift_expr(ctx, ast->e.cond.alternate);
	return expr;
    case EXPR_CALL:
	expr = new_expr(ctx, HIR_EXPR_CALL);
	expr->source_lineno = ast->lineno;
	expr->u.call.resume_key.code_unit = ctx->current_code_unit;
	expr->u.call.resume_key.site = ast->e.call.resume_site;
	expr->u.call.resume_key.phase = RESUME_PHASE_AFTER_CALL;
	expr->u.call.func = ast->e.call.func;
	expr->u.call.args = lift_arg_list(ctx, ast->e.call.args);
	record_unsupported(ctx, "Call expression is not yet lowerable to TAC");
	return expr;
    case EXPR_VERB:
	expr = new_expr(ctx, HIR_EXPR_VERB_CALL);
	expr->source_lineno = ast->lineno;
	expr->u.verb_call.resume_key.code_unit = ctx->current_code_unit;
	expr->u.verb_call.resume_key.site = ast->e.verb.resume_site;
	expr->u.verb_call.resume_key.phase = RESUME_PHASE_AFTER_CALL;
	expr->u.verb_call.obj = lift_expr(ctx, ast->e.verb.obj);
	expr->u.verb_call.verb = lift_expr(ctx, ast->e.verb.verb);
	expr->u.verb_call.args = lift_arg_list(ctx, ast->e.verb.args);
	record_unsupported(ctx, "Verb-call expression is not yet lowerable to TAC");
	return expr;
    case EXPR_PROP:
	expr = new_expr(ctx, HIR_EXPR_PROP);
	expr->source_lineno = ast->lineno;
	expr->u.pair.lhs = lift_expr(ctx, ast->e.bin.lhs);
	expr->u.pair.rhs = lift_expr(ctx, ast->e.bin.rhs);
	record_unsupported(ctx, "Property expression is not yet lowerable to TAC");
	return expr;
    case EXPR_INDEX:
	expr = new_expr(ctx, HIR_EXPR_INDEX);
	expr->source_lineno = ast->lineno;
	expr->u.pair.lhs = lift_expr(ctx, ast->e.bin.lhs);
	expr->u.pair.rhs = lift_expr(ctx, ast->e.bin.rhs);
	record_unsupported(ctx, "Index expression is not yet lowerable to TAC");
	return expr;
    case EXPR_RANGE:
	expr = new_expr(ctx, HIR_EXPR_RANGE);
	expr->source_lineno = ast->lineno;
	expr->u.range.base = lift_expr(ctx, ast->e.range.base);
	expr->u.range.from = lift_expr(ctx, ast->e.range.from);
	expr->u.range.to = lift_expr(ctx, ast->e.range.to);
	record_unsupported(ctx, "Range expression is not yet lowerable to TAC");
	return expr;
    case EXPR_LIST:
	expr = new_expr(ctx, HIR_EXPR_LIST);
	expr->source_lineno = ast->lineno;
	expr->u.list.items = lift_arg_list(ctx, ast->e.list);
	record_unsupported(ctx, "List expression is not yet lowerable to TAC");
	return expr;
    case EXPR_CATCH:
	expr = new_expr(ctx, HIR_EXPR_CATCH);
	expr->source_lineno = ast->lineno;
	expr->u.catch_expr.body = lift_expr(ctx, ast->e.catch.try);
	expr->u.catch_expr.codes = lift_arg_list(ctx, ast->e.catch.codes);
	expr->u.catch_expr.handler = lift_expr(ctx, ast->e.catch.except);
	record_unsupported(ctx, "Catch expression is not yet lowerable to TAC");
	return expr;
    case EXPR_SCATTER:
	return unsupported_expr(ctx, ast);
    case EXPR_LENGTH:
	return unsupported_expr(ctx, ast);
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
	arm->next = 0;

	if (last)
	    last->next = arm;
	else
	    first = arm;
	last = arm;
    }

    return first;
}

static HIRStmt *
unsupported_stmt(HIRContext *ctx, Stmt *ast)
{
    HIRStmt *stmt = new_stmt(ctx, HIR_STMT_UNSUPPORTED);

    stmt->source_lineno = ast ? ast->lineno : 0;
    stmt->u.stmt_kind = ast ? ast->kind : STMT_EXPR;
    record_unsupported(ctx, "Unsupported AST statement in HIR lift");
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
	stmt->u.for_list.local_id = ast->s.list.id;
	stmt->u.for_list.iterable = lift_expr(ctx, ast->s.list.expr);
	stmt->u.for_list.body = lift_stmt_list(ctx, ast->s.list.body);
	record_unsupported(ctx, "For-list statement is not yet lowerable to TAC");
	return stmt;
    case STMT_RANGE:
	stmt = new_stmt(ctx, HIR_STMT_FOR_RANGE);
	stmt->source_lineno = ast->lineno;
	stmt->u.for_range.local_id = ast->s.range.id;
	stmt->u.for_range.from = lift_expr(ctx, ast->s.range.from);
	stmt->u.for_range.to = lift_expr(ctx, ast->s.range.to);
	stmt->u.for_range.body = lift_stmt_list(ctx, ast->s.range.body);
	record_unsupported(ctx, "For-range statement is not yet lowerable to TAC");
	return stmt;
    case STMT_FORK:
	{
	    unsigned enclosing_code_unit = ctx->current_code_unit;

	    stmt = new_stmt(ctx, HIR_STMT_FORK);
	    stmt->source_lineno = ast->lineno;
	    stmt->u.fork.local_id = ast->s.fork.id;
	    stmt->u.fork.time = lift_expr(ctx, ast->s.fork.time);
	    ctx->current_code_unit = ast->s.fork.code_unit;
	    stmt->u.fork.body = lift_stmt_list(ctx, ast->s.fork.body);
	    ctx->current_code_unit = enclosing_code_unit;
	    record_unsupported(ctx, "Fork statement is not yet lowerable to TAC");
	    return stmt;
	}
    case STMT_TRY_EXCEPT:
	stmt = new_stmt(ctx, HIR_STMT_TRY_EXCEPT);
	stmt->source_lineno = ast->lineno;
	stmt->u.try_except.body = lift_stmt_list(ctx, ast->s.catch.body);
	stmt->u.try_except.excepts = lift_except_arms(ctx, ast->s.catch.excepts);
	record_unsupported(ctx, "Try-except statement is not yet lowerable to TAC");
	return stmt;
    case STMT_TRY_FINALLY:
	stmt = new_stmt(ctx, HIR_STMT_TRY_FINALLY);
	stmt->source_lineno = ast->lineno;
	stmt->u.try_finally.body = lift_stmt_list(ctx, ast->s.finally.body);
	stmt->u.try_finally.handler = lift_stmt_list(ctx, ast->s.finally.handler);
	record_unsupported(ctx, "Try-finally statement is not yet lowerable to TAC");
	return stmt;
    case STMT_BREAK:
	stmt = new_stmt(ctx, HIR_STMT_BREAK);
	stmt->source_lineno = ast->lineno;
	stmt->u.exit_id = ast->s.exit;
	record_unsupported(ctx, "Break statement is not yet lowerable to TAC");
	return stmt;
    case STMT_CONTINUE:
	stmt = new_stmt(ctx, HIR_STMT_CONTINUE);
	stmt->source_lineno = ast->lineno;
	stmt->u.exit_id = ast->s.exit;
	record_unsupported(ctx, "Continue statement is not yet lowerable to TAC");
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

    instr->kind = kind;
    instr->source_lineno = source_lineno;
    instr->bytecode_pc = NO_BYTECODE_PC;
    instr->dst = 0;
    instr->src1 = 0;
    instr->src2 = 0;
    instr->label = 0;
    instr->local_id = -1;
    instr->op = HIR_OP_ADD;
    return instr;
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
append_branch_false(HIRContext *ctx, HIRTacProgram *program, int src, int label,
		    unsigned source_lineno, unsigned bytecode_pc)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_BRANCH_FALSE, source_lineno);

    append_tick(ctx, program, source_lineno, bytecode_pc);
    instr->bytecode_pc = bytecode_pc;
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
    int lhs = lower_expr(ctx, program, expr->u.binary.lhs);
    int result_local = ctx->next_local++;
    int done_label = new_label(ctx);

    append_internal_store(ctx, program, result_local, lhs,
			  expr->source_lineno);
    if (expr->u.binary.op == HIR_OP_AND) {
	int rhs;

	append_branch_false(ctx, program, lhs, done_label,
			    expr->source_lineno, expr->bytecode_pc);
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
	rhs = lower_expr(ctx, program, expr->u.binary.rhs);
	append_internal_store(ctx, program, result_local, rhs,
			      expr->source_lineno);
    }
    append_label(ctx, program, done_label, expr->source_lineno);
    return append_internal_load(ctx, program, result_local,
				expr->source_lineno);
}

static int
append_unsupported_tac(HIRContext *ctx, HIRTacProgram *program,
		       const char *message, unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_UNSUPPORTED, source_lineno);

    instr->dst = new_temp(ctx);
    record_unsupported(ctx, message);
    append_tac(program, instr);
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
	append_tac(program, instr);
	return instr->dst;
    case HIR_EXPR_LOCAL_LOAD:
	instr = new_tac(ctx, HIR_TAC_LOAD_LOCAL, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = new_temp(ctx);
	instr->local_id = expr->u.local_id;
	append_tac(program, instr);
	return instr->dst;
    case HIR_EXPR_LOCAL_STORE:
	rhs = lower_expr(ctx, program, expr->u.local_store.rhs);
	append_tick(ctx, program, expr->source_lineno, expr->bytecode_pc);
	instr = new_tac(ctx, HIR_TAC_STORE_LOCAL, expr->source_lineno);
	instr->bytecode_pc = expr->bytecode_pc;
	instr->dst = rhs;
	instr->src1 = rhs;
	instr->local_id = expr->u.local_store.local_id;
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
	append_tac(program, instr);
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
	append_tac(program, instr);
	return instr->dst;
    case HIR_EXPR_COND:
	return append_unsupported_tac(ctx, program,
				      "Conditional expression is not yet lowerable to TAC",
				      expr->source_lineno);
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
    int done_label = new_label(ctx);

    for (arm = stmt->u.if_stmt.arms; arm; arm = arm->next) {
	int next_label = new_label(ctx);
	int cond = lower_expr(ctx, program, arm->condition);

	append_branch_false(ctx, program, cond, next_label, stmt->source_lineno,
			    arm->bytecode_pc);
	lower_stmt_list(ctx, program, arm->body);
	append_jump(ctx, program, done_label, stmt->source_lineno);
	append_label(ctx, program, next_label, stmt->source_lineno);
    }

    lower_stmt_list(ctx, program, stmt->u.if_stmt.otherwise);
    append_label(ctx, program, done_label, stmt->source_lineno);
}

static void
lower_while(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    int top_label = new_label(ctx);
    int done_label = new_label(ctx);
    int cond;

    append_label(ctx, program, top_label, stmt->source_lineno);
    cond = lower_expr(ctx, program, stmt->u.loop.condition);
    append_branch_false(ctx, program, cond, done_label, stmt->source_lineno,
			stmt->bytecode_pc);
    lower_stmt_list(ctx, program, stmt->u.loop.body);
    append_jump(ctx, program, top_label, stmt->source_lineno);
    append_label(ctx, program, done_label, stmt->source_lineno);
}

static void
lower_stmt(HIRContext *ctx, HIRTacProgram *program, HIRStmt *stmt)
{
    HIRTacInstr *instr;
    int result;

    switch (stmt->kind) {
    case HIR_STMT_SEQUENCE:
	lower_stmt_list(ctx, program, stmt);
	break;
    case HIR_STMT_EXPR:
	(void) lower_expr(ctx, program, stmt->u.expr);
	break;
    case HIR_STMT_RETURN:
	instr = new_tac(ctx, stmt->u.expr ? HIR_TAC_RETURN : HIR_TAC_RETURN0,
			stmt->source_lineno);
	instr->bytecode_pc = stmt->bytecode_pc;
	if (stmt->u.expr) {
	    result = lower_expr(ctx, program, stmt->u.expr);
	    instr->src1 = result;
	}
	append_tac(program, instr);
	break;
    case HIR_STMT_IF:
	lower_if(ctx, program, stmt);
	break;
    case HIR_STMT_WHILE:
	lower_while(ctx, program, stmt);
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
