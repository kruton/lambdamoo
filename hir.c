#include "hir.h"

#include "arena.h"
#include "program.h"
#include "my-stdio.h"
#include "storage.h"

#include <stddef.h>

typedef struct HIRExpr HIRExpr;
typedef struct HIRStmt HIRStmt;
typedef struct HIRArg HIRArg;
typedef struct HIRCondArm HIRCondArm;
typedef struct HIRExceptArm HIRExceptArm;
typedef struct HIRTacInstr HIRTacInstr;
typedef struct HIRBasicBlock HIRBasicBlock;
typedef struct HIRSSAInstr HIRSSAInstr;
typedef struct HIRSSABlock HIRSSABlock;

struct HIRArg {
    enum Arg_Kind kind;
    HIRExpr *expr;
    HIRArg *next;
};

struct HIRExpr {
    HIRExprKind kind;
    HIRTypeTag type;
    unsigned source_lineno;
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

struct HIRSSAInstr {
    HIRTacKind kind;
    unsigned source_lineno;
    int value;
    int src1;
    int src2;
    int label;
    int local_id;
    HIROp op;
    Var literal;
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
    HIRSSABlock *blocks;
    HIRSSABlock *last_block;
    int num_blocks;
    int num_instructions;
    int num_values;
};

struct HIRContext {
    Arena *arena;
    Names *var_names;
    int error_count;
    const char *error_msg;
    int next_temp;
    int next_label;
    unsigned current_code_unit;
};

static void *hir_alloc(HIRContext *, size_t);
static HIRExpr *lift_expr(HIRContext *, Expr *);
static HIRStmt *lift_stmt_list(HIRContext *, Stmt *);
static int lower_expr(HIRContext *, HIRTacProgram *, HIRExpr *);
static void lower_stmt_list(HIRContext *, HIRTacProgram *, HIRStmt *);
static void record_unsupported(HIRContext *, const char *);
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
    if (local_id < 0
	|| (ctx->var_names && local_id >= (int) ctx->var_names->size))
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

int
hir_verify_cfg(HIRContext *ctx, HIRCFG *cfg)
{
    HIRBasicBlock *block;
    int errors_before;

    if (!ctx || !cfg)
	return 0;

    errors_before = ctx->error_count;

    if (cfg->num_blocks == 0)
	return 1;

    if (!cfg->entry || cfg->entry != cfg->blocks)
	record_unsupported(ctx, "CFG has invalid entry block");

    for (block = cfg->blocks; block; block = block->next) {
	int i;

	if (!block->first || !block->last)
	    record_unsupported(ctx, "CFG block has missing TAC bounds");

	if (block->num_successors < 0 || block->num_successors > 2)
	    record_unsupported(ctx, "CFG block has invalid successor count");

	for (i = 0; i < block->num_successors; i++) {
	    if (!block->successors[i])
		record_unsupported(ctx, "CFG block has missing successor");
	}

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
	    || instr->kind == HIR_TAC_UNSUPPORTED);
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
append_ssa_instr(HIRSSAProgram *ssa, HIRSSABlock *block, HIRSSAInstr *instr)
{
    if (block->last)
	block->last->next = instr;
    else
	block->first = instr;
    block->last = instr;
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
    instr->value = tac->dst;
    instr->src1 = tac->src1;
    instr->src2 = tac->src2;
    instr->label = tac->label;
    instr->local_id = tac->local_id;
    instr->op = tac->op;
    instr->literal = tac->literal;
    instr->next = 0;

    return instr;
}

HIRSSAProgram *
hir_build_ssa(HIRContext *ctx, HIRCFG *cfg)
{
    HIRSSAProgram *ssa;
    HIRBasicBlock *cfg_block;

    if (!ctx || !cfg)
	return 0;

    ssa = hir_alloc(ctx, sizeof(HIRSSAProgram));
    ssa->blocks = 0;
    ssa->last_block = 0;
    ssa->num_blocks = 0;
    ssa->num_instructions = 0;
    ssa->num_values = 0;

    for (cfg_block = cfg->blocks; cfg_block; cfg_block = cfg_block->next) {
	HIRSSABlock *ssa_block = hir_alloc(ctx, sizeof(HIRSSABlock));
	HIRTacInstr *tac;

	ssa_block->id = cfg_block->id;
	ssa_block->first_lineno = cfg_block->first_lineno;
	ssa_block->last_lineno = cfg_block->last_lineno;
	ssa_block->first = 0;
	ssa_block->last = 0;
	ssa_block->next = 0;
	append_ssa_block(ssa, ssa_block);

	for (tac = cfg_block->first; tac; tac = tac->next) {
	    append_ssa_instr(ssa, ssa_block, new_ssa_instr(ctx, tac));
	    if (tac == cfg_block->last)
		break;
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
    max_value = ctx->next_temp - 1;
    defined = hir_alloc(ctx, (size_t) max_value + 1);
    for (i = 0; i <= max_value; i++)
	defined[i] = 0;

    for (block = ssa->blocks; block; block = block->next) {
	HIRSSAInstr *instr;

	block_count++;
	if (!block->first || !block->last)
	    record_unsupported(ctx, "SSA block has no instructions");

	for (instr = block->first; instr; instr = instr->next) {
	    instruction_count++;

	    switch (instr->kind) {
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
	    case HIR_TAC_LABEL:
	    case HIR_TAC_JUMP:
	    case HIR_TAC_RETURN0:
		break;
	    }

	    if (instr == block->last)
		break;
	}
    }

    if (block_count != ssa->num_blocks)
	record_unsupported(ctx, "SSA block count mismatch");
    if (instruction_count != ssa->num_instructions)
	record_unsupported(ctx, "SSA instruction count mismatch");
    if (value_count != ssa->num_values)
	record_unsupported(ctx, "SSA value count mismatch");

    return ctx->error_count == errors_before;
}

#ifdef HIR_DUMP_TAC
static const char *tac_kind_name(HIRTacKind);
static const char *op_name(HIROp);
static void dump_var(FILE *, Var);

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
	}

	fprintf(stderr, "\n");
    }

    fprintf(stderr, "HIR TAC END\n");
}

static const char *
tac_kind_name(HIRTacKind kind)
{
    switch (kind) {
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
    return expr;
}

static HIRStmt *
new_stmt(HIRContext *ctx, HIRStmtKind kind)
{
    HIRStmt *stmt = hir_alloc(ctx, sizeof(HIRStmt));

    stmt->kind = kind;
    stmt->source_lineno = 0;
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
	expr->type = type_tag_for_var_type(ast->e.var.type);
	expr->u.literal = ast->e.var;
	return expr;
    case EXPR_ID:
	expr = new_expr(ctx, HIR_EXPR_LOCAL_LOAD);
	expr->source_lineno = ast->lineno;
	expr->u.local_id = ast->e.id;
	return expr;
    case EXPR_ASGN:
	return lift_assignment(ctx, ast);
    case EXPR_NEGATE:
    case EXPR_NOT:
    case EXPR_COMPLEMENT:
	expr = new_expr(ctx, HIR_EXPR_UNARY);
	expr->source_lineno = ast->lineno;
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
		    unsigned source_lineno)
{
    HIRTacInstr *instr = new_tac(ctx, HIR_TAC_BRANCH_FALSE, source_lineno);

    instr->src1 = src;
    instr->label = label;
    append_tac(program, instr);
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
	instr->dst = new_temp(ctx);
	instr->literal = expr->u.literal;
	append_tac(program, instr);
	return instr->dst;
    case HIR_EXPR_LOCAL_LOAD:
	instr = new_tac(ctx, HIR_TAC_LOAD_LOCAL, expr->source_lineno);
	instr->dst = new_temp(ctx);
	instr->local_id = expr->u.local_id;
	append_tac(program, instr);
	return instr->dst;
    case HIR_EXPR_LOCAL_STORE:
	rhs = lower_expr(ctx, program, expr->u.local_store.rhs);
	instr = new_tac(ctx, HIR_TAC_STORE_LOCAL, expr->source_lineno);
	instr->dst = rhs;
	instr->src1 = rhs;
	instr->local_id = expr->u.local_store.local_id;
	append_tac(program, instr);
	return rhs;
    case HIR_EXPR_UNARY:
	lhs = lower_expr(ctx, program, expr->u.unary.expr);
	instr = new_tac(ctx, HIR_TAC_UNARY, expr->source_lineno);
	instr->dst = new_temp(ctx);
	instr->src1 = lhs;
	instr->op = expr->u.unary.op;
	append_tac(program, instr);
	return instr->dst;
    case HIR_EXPR_BINARY:
	lhs = lower_expr(ctx, program, expr->u.binary.lhs);
	rhs = lower_expr(ctx, program, expr->u.binary.rhs);
	instr = new_tac(ctx, HIR_TAC_BINARY, expr->source_lineno);
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

	append_branch_false(ctx, program, cond, next_label, stmt->source_lineno);
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
    append_branch_false(ctx, program, cond, done_label, stmt->source_lineno);
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

    ssa->blocks = block;
    ssa->last_block = block;
    ssa->num_blocks = 1;
    ssa->num_instructions = instruction_count;
    ssa->num_values = value_count;

    return ssa;
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
#endif
