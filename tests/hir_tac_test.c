#define HIR_TESTING 1

#include "hir.h"

#include "integer_arithmetic.h"
#include "storage.h"

#include <limits.h>
#include <stdio.h>
#include <string.h>

static int failures = 0;

static void
check_int(const char *name, int actual, int expected)
{
    if (actual != expected) {
	fprintf(stderr, "%s: expected %d, got %d\n", name, expected, actual);
	failures++;
    }
}

static void
check_rejected(const char *name, int accepted, int before_errors,
	       int after_errors)
{
    if (accepted) {
	fprintf(stderr, "%s: verifier unexpectedly accepted malformed IR\n",
		name);
	failures++;
    }
    if (after_errors <= before_errors) {
	fprintf(stderr, "%s: verifier did not record an error\n", name);
	failures++;
    }
}

#ifdef HIR_DUMP_SSA
static void
check_ssa_dump_contains(const char *name, HIRSSAProgram *ssa,
			const char *needle)
{
    FILE *file = tmpfile();
    char line[512];
    int found = 0;

    if (!file) {
	fprintf(stderr, "%s: failed to create dump comparison file\n", name);
	failures++;
	return;
    }

    hir_dump_ssa_to_file(file, ssa);
    rewind(file);
    while (fgets(line, sizeof(line), file)) {
	if (strstr(line, needle)) {
	    found = 1;
	    break;
	}
    }
    fclose(file);

    if (!found) {
	fprintf(stderr, "%s: SSA dump missing '%s'\n", name, needle);
	failures++;
    }
}
#endif

static Expr
int_expr(Num value, unsigned lineno)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = EXPR_VAR;
    expr.lineno = lineno;
    expr.bytecode_pc = NO_BYTECODE_PC;
    expr.e.var.type = TYPE_INT;
    expr.e.var.v.num = value;

    return expr;
}

static Expr
id_expr(int id, unsigned lineno)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = EXPR_ID;
    expr.lineno = lineno;
    expr.bytecode_pc = NO_BYTECODE_PC;
    expr.e.id = id;

    return expr;
}

static Expr
binary_expr(enum Expr_Kind kind, Expr *lhs, Expr *rhs)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = kind;
    expr.lineno = lhs ? lhs->lineno : 0;
    expr.bytecode_pc = NO_BYTECODE_PC;
    expr.e.bin.lhs = lhs;
    expr.e.bin.rhs = rhs;

    return expr;
}

static Stmt
expr_stmt(Expr *expr)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_EXPR;
    stmt.lineno = expr ? expr->lineno : 0;
    stmt.bytecode_pc = NO_BYTECODE_PC;
    stmt.s.expr = expr;

    return stmt;
}

static Stmt
return_stmt(Expr *expr)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_RETURN;
    stmt.lineno = expr ? expr->lineno : 0;
    stmt.bytecode_pc = NO_BYTECODE_PC;
    stmt.s.expr = expr;

    return stmt;
}

static HIRTacProgram *
lower_stmt(Names *names, Stmt *stmt, HIRContext **ctx_out, HIRCFG **cfg_out,
	   HIRDominatorTree **dom_out, HIRSSAProgram **ssa_out)
{
    HIRContext *ctx = hir_context_new(names);
    HIRProgram *program = hir_lift_ast(ctx, stmt);
    HIRTacProgram *tac = hir_lower_to_tac(ctx, program);
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;

    (void) hir_verify_tac(ctx, tac);
    cfg = hir_build_cfg(ctx, tac);
    (void) hir_verify_cfg(ctx, cfg);
    dom = hir_build_dominator_tree(ctx, cfg);
    (void) hir_verify_dominator_tree(ctx, cfg, dom);
    ssa = hir_build_ssa(ctx, cfg);
    (void) hir_verify_ssa(ctx, ssa);
    *ctx_out = ctx;
    *cfg_out = cfg;
    *dom_out = dom;
    *ssa_out = ssa;

    return tac;
}

static void
test_arithmetic_and_local_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;
    Expr one = int_expr(1, 10);
    Expr two = int_expr(2, 10);
    Expr three = int_expr(3, 11);
    Expr local_x_lhs = id_expr(16, 10);
    Expr local_x_rhs = id_expr(16, 11);
    Expr add = binary_expr(EXPR_PLUS, &one, &two);
    Expr assign = binary_expr(EXPR_ASGN, &local_x_lhs, &add);
    Expr mult = binary_expr(EXPR_TIMES, &local_x_rhs, &three);
    Stmt assign_stmt_node = expr_stmt(&assign);
    Stmt return_stmt_node = return_stmt(&mult);

    memset(&names, 0, sizeof(names));
    names.size = 32;
    one.bytecode_pc = 1;
    two.bytecode_pc = 2;
    add.bytecode_pc = 5;
    assign.bytecode_pc = 6;
    local_x_rhs.bytecode_pc = 7;
    three.bytecode_pc = 8;
    mult.bytecode_pc = 9;
    return_stmt_node.bytecode_pc = 10;
    assign_stmt_node.next = &return_stmt_node;

    tac = lower_stmt(&names, &assign_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("arith const count", hir_tac_count_kind(tac, HIR_TAC_CONST), 3);
    check_int("arith load count", hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 1);
    check_int("arith store count", hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 1);
    check_int("arith return count", hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("arith add count", hir_tac_count_binary_op(tac, HIR_OP_ADD), 1);
    check_int("arith mul count", hir_tac_count_binary_op(tac, HIR_OP_MUL), 1);
    check_int("arith tick count", hir_tac_count_kind(tac, HIR_TAC_TICK), 3);
    check_int("arith line 10 count", hir_tac_count_lineno(tac, 10), 6);
    check_int("arith line 11 count", hir_tac_count_lineno(tac, 11), 5);
    check_int("arith add anchor count",
	      hir_tac_count_bytecode_pc(tac, 5), 2);
    check_int("arith add stack depth",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 5), 2);
    check_int("arith return anchor count",
	      hir_tac_count_bytecode_pc(tac, 10), 1);
    check_int("arith cfg blocks", hir_cfg_block_count(cfg), 1);
    check_int("arith cfg edges", hir_cfg_edge_count(cfg), 0);
    check_int("arith dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 1);
    check_int("arith dom entry idom", hir_dom_idom_block(dom, 1), 1);
    check_int("arith ssa blocks", hir_ssa_block_count(ssa), 1);
    check_int("arith ssa instructions", hir_ssa_instruction_count(ssa), 9);
    check_int("arith ssa values", hir_ssa_value_count(ssa), 5);
    check_int("arith ssa binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 2);
    check_int("arith SSA add anchor count",
	      hir_ssa_count_bytecode_pc(ssa, 5), 2);
    check_int("arith SSA add stack depth",
	      hir_ssa_stack_depth_at_bytecode_pc(ssa, 5), 2);
    check_int("arith SSA updated local",
	      hir_ssa_local_value_at_bytecode_pc(ssa, 9, 16) > 0, 1);
    check_int("arith verify errors", hir_context_error_count(ctx), 0);
    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("arith return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT_CONSTANT);
    check_int("arith return constant",
	      (int) hir_ssa_return_constant(ssa, analysis), 9);
    check_int("arith constant optimization changed",
	      hir_optimize_ssa_constants(ctx, ssa), 2);
    check_int("arith optimized binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 0);
    check_int("arith optimized verify", hir_verify_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_control_flow_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Cond_Arm arm;
    Expr one = int_expr(1, 20);
    Expr two = int_expr(2, 20);
    Expr cond = binary_expr(EXPR_LT, &one, &two);
    Expr ret_val = int_expr(3, 21);
    Stmt ret = return_stmt(&ret_val);
    Stmt if_stmt_node;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&arm, 0, sizeof(arm));
    arm.condition = &cond;
    arm.stmt = &ret;

    memset(&if_stmt_node, 0, sizeof(if_stmt_node));
    if_stmt_node.kind = STMT_COND;
    if_stmt_node.lineno = 20;
    if_stmt_node.s.cond.arms = &arm;
    if_stmt_node.s.cond.otherwise = 0;

    tac = lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("control branch count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 1);
    check_int("control jump count", hir_tac_count_kind(tac, HIR_TAC_JUMP), 1);
    check_int("control label count", hir_tac_count_kind(tac, HIR_TAC_LABEL), 2);
    check_int("control lt count", hir_tac_count_binary_op(tac, HIR_OP_LT), 1);
    check_int("control tick count", hir_tac_count_kind(tac, HIR_TAC_TICK), 2);
    check_int("control line 20 count", hir_tac_count_lineno(tac, 20), 9);
    check_int("control line 21 count", hir_tac_count_lineno(tac, 21), 2);
    check_int("control cfg blocks", hir_cfg_block_count(cfg), 5);
    check_int("control cfg edges", hir_cfg_edge_count(cfg), 4);
    check_int("control dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 4);
    check_int("control dom entry idom", hir_dom_idom_block(dom, 1), 1);
    check_int("control dom then idom", hir_dom_idom_block(dom, 2), 1);
    check_int("control dom unreachable idom", hir_dom_idom_block(dom, 3), 0);
    check_int("control dom else-label idom", hir_dom_idom_block(dom, 4), 1);
    check_int("control dom done idom", hir_dom_idom_block(dom, 5), 4);
    check_int("control ssa blocks", hir_ssa_block_count(ssa), 5);
    check_int("control ssa instructions", hir_ssa_instruction_count(ssa), 11);
    check_int("control ssa values", hir_ssa_value_count(ssa), 4);
    check_int("control ssa branch count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BRANCH_FALSE), 1);
    check_int("control verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_short_circuit_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr zero = int_expr(0, 25);
    Expr nine = int_expr(9, 25);
    Expr and_expr = binary_expr(EXPR_AND, &zero, &nine);
    Expr or_expr = binary_expr(EXPR_OR, &zero, &nine);
    Stmt ret = return_stmt(&and_expr);

    memset(&names, 0, sizeof(names));
    names.size = 32;
    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("and binary count", hir_tac_count_binary_op(tac, HIR_OP_AND), 0);
    check_int("and branch count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 1);
    check_int("and jump count", hir_tac_count_kind(tac, HIR_TAC_JUMP), 0);
    check_int("and tick count", hir_tac_count_kind(tac, HIR_TAC_TICK), 1);
    check_int("and synthetic stores",
	      hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 2);
    check_int("and synthetic loads",
	      hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 1);
    check_int("and phi count", hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("and verify errors", hir_context_error_count(ctx), 0);
    hir_context_free(ctx);

    ret = return_stmt(&or_expr);
    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("or binary count", hir_tac_count_binary_op(tac, HIR_OP_OR), 0);
    check_int("or branch count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 1);
    check_int("or jump count", hir_tac_count_kind(tac, HIR_TAC_JUMP), 1);
    check_int("or tick count", hir_tac_count_kind(tac, HIR_TAC_TICK), 1);
    check_int("or synthetic stores",
	      hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 2);
    check_int("or synthetic loads",
	      hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 1);
    check_int("or phi count", hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("or verify errors", hir_context_error_count(ctx), 0);
    hir_context_free(ctx);
}

static void
test_constant_analysis_overflow(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    Expr maximum = int_expr(NUM_MAX, 26);
    Expr one = int_expr(1, 26);
    Expr add = binary_expr(EXPR_PLUS, &maximum, &one);
    Stmt ret = return_stmt(&add);

    memset(&names, 0, sizeof(names));
    names.size = 32;
    (void) lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    analysis = hir_analyze_ssa_values(ctx, ssa);

    check_int("overflow return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT_CONSTANT);
    check_int("overflow wrapped constant",
	      hir_ssa_return_constant(ssa, analysis) == NUM_MIN, 1);
    check_int("overflow optimization changed",
	      hir_optimize_ssa_constants(ctx, ssa), 1);
    check_int("overflow binary retained",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 0);
    check_int("overflow optimized verify", hir_verify_ssa(ctx, ssa), 1);
    check_int("overflow verify errors", hir_context_error_count(ctx), 0);
    hir_context_free(ctx);
}

static void
test_integer_arithmetic_model(void)
{
    IntegerArithmeticResult result;

    result = integer_arithmetic(INTEGER_NEGATE, NUM_MIN, 0);
    check_int("model negate minimum succeeds", result.succeeded, 1);
    check_int("model negate minimum wraps", result.value == NUM_MIN, 1);
    result = integer_arithmetic(INTEGER_MULTIPLY, NUM_MAX, 2);
    check_int("model multiply wraps", result.value == -2, 1);
    result = integer_arithmetic(INTEGER_DIVIDE, NUM_MIN, -1);
    check_int("model divide overflow succeeds", result.succeeded, 1);
    check_int("model divide overflow wraps", result.value == NUM_MIN, 1);
    result = integer_arithmetic(INTEGER_MODULUS, NUM_MIN, -1);
    check_int("model modulus overflow succeeds", result.succeeded, 1);
    check_int("model modulus overflow value", result.value, 0);
    result = integer_arithmetic(INTEGER_DIVIDE, 1, 0);
    check_int("model divide zero fails", result.succeeded, 0);
    check_int("model divide zero error", result.error, E_DIV);
    result = integer_arithmetic(INTEGER_POWER, 0, -1);
    check_int("model power zero negative fails", result.succeeded, 0);
    check_int("model power zero negative error", result.error, E_DIV);
    result = integer_arithmetic(INTEGER_SHIFT_LEFT, 1,
				sizeof(Num) * CHAR_BIT);
    check_int("model invalid shift fails", result.succeeded, 0);
    check_int("model invalid shift error", result.error, E_INVARG);
}

static void
test_constant_analysis_error(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    Expr one = int_expr(1, 27);
    Expr zero = int_expr(0, 27);
    Expr divide = binary_expr(EXPR_DIVIDE, &one, &zero);
    Stmt ret = return_stmt(&divide);

    memset(&names, 0, sizeof(names));
    names.size = 32;
    (void) lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    analysis = hir_analyze_ssa_values(ctx, ssa);

    check_int("constant error return fact",
	      hir_ssa_return_value_kind(ssa, analysis), HIR_VALUE_ERROR);
    check_int("constant error return value",
	      hir_ssa_return_error(ssa, analysis), E_DIV);
    check_int("constant error is not folded",
	      hir_optimize_ssa_constants(ctx, ssa), 0);
    hir_context_free(ctx);
}

static void
test_unsupported_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr unsupp_expr;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&unsupp_expr, 0, sizeof(unsupp_expr));
    unsupp_expr.kind = EXPR_LENGTH;
    unsupp_expr.lineno = 30;
    ret = return_stmt(&unsupp_expr);

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("unsupported tac count",
	      hir_tac_count_kind(tac, HIR_TAC_UNSUPPORTED), 1);
    check_int("unsupported return count", hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("unsupported line 30 count", hir_tac_count_lineno(tac, 30), 2);
    check_int("unsupported cfg blocks", hir_cfg_block_count(cfg), 1);
    check_int("unsupported cfg unsupported blocks",
	      hir_cfg_unsupported_block_count(cfg), 1);
    check_int("unsupported dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 1);
    check_int("unsupported ssa blocks", hir_ssa_block_count(ssa), 1);
    check_int("unsupported ssa values", hir_ssa_value_count(ssa), 1);
    check_int("unsupported ssa unsupported count",
	      hir_ssa_count_kind(ssa, HIR_TAC_UNSUPPORTED), 1);
    if (hir_context_error_count(ctx) == 0) {
	fprintf(stderr, "unsupported case should record HIR errors\n");
	failures++;
    }

    hir_context_free(ctx);
}

static void
test_negative_tac_verifier_cases(void)
{
    Names names;
    HIRContext *ctx;
    HIRTacProgram *tac;
    int before;
    int accepted;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    ctx = hir_context_new(&names);
    tac = hir_test_tac_with_undefined_return(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_tac(ctx, tac);
    check_rejected("negative tac undefined return", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    tac = hir_test_tac_with_duplicate_temp(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_tac(ctx, tac);
    check_rejected("negative tac duplicate temp", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);
}

static void
test_negative_cfg_verifier_cases(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    int before;
    int accepted;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    ctx = hir_context_new(&names);
    cfg = hir_test_cfg_with_missing_successor(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_cfg(ctx, cfg);
    check_rejected("negative cfg missing successor", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    cfg = hir_test_cfg_with_external_successor(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_cfg(ctx, cfg);
    check_rejected("negative cfg external successor", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    cfg = hir_test_cfg_with_predecessor_mismatch(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_cfg(ctx, cfg);
    check_rejected("negative cfg predecessor mismatch", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    cfg = hir_test_cfg_with_duplicate_block_id(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_cfg(ctx, cfg);
    check_rejected("negative cfg duplicate block id", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);
}

static void
test_negative_ssa_verifier_cases(void)
{
    Names names;
    HIRContext *ctx;
    HIRSSAProgram *ssa;
    int before;
    int accepted;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_use_before_def(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa use before def", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_duplicate_def(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa duplicate def", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_nondominating_use(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa nondominating use", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_bad_phi_shape(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa bad phi shape", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_late_phi(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa late phi", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_missing_phi_arg(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa missing phi arg", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_nonpred_phi_arg(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("negative ssa nonpred phi arg", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_out_ssa_with_phi(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_out_of_ssa(ctx, ssa);
    check_rejected("negative out ssa remaining phi", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);

    ctx = hir_context_new(&names);
    ssa = hir_test_out_ssa_with_bad_copy_source(ctx);
    before = hir_context_error_count(ctx);
    accepted = hir_verify_out_of_ssa(ctx, ssa);
    check_rejected("negative out ssa bad copy source", accepted, before,
		   hir_context_error_count(ctx));
    hir_context_free(ctx);
}

static Stmt
while_stmt(Expr *condition, Stmt *body, int loop_id, unsigned lineno)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_WHILE;
    stmt.lineno = lineno;
    stmt.s.loop.id = loop_id;
    stmt.s.loop.condition = condition;
    stmt.s.loop.body = body;

    return stmt;
}

static Stmt
range_stmt(int id, Expr *from, Expr *to, Stmt *body, unsigned lineno)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_RANGE;
    stmt.lineno = lineno;
    stmt.s.range.id = id;
    stmt.s.range.from = from;
    stmt.s.range.to = to;
    stmt.s.range.body = body;

    return stmt;
}

static Stmt
list_stmt(int id, Expr *iterable, Stmt *body, unsigned lineno)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_LIST;
    stmt.lineno = lineno;
    stmt.s.list.id = id;
    stmt.s.list.expr = iterable;
    stmt.s.list.body = body;

    return stmt;
}

static Expr
cond_expr_ast(Expr *cond, Expr *consequent, Expr *alternate, unsigned lineno)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = EXPR_COND;
    expr.lineno = lineno;
    expr.bytecode_pc = NO_BYTECODE_PC;
    expr.e.cond.condition = cond;
    expr.e.cond.consequent = consequent;
    expr.e.cond.alternate = alternate;

    return expr;
}

static Stmt
break_stmt(int exit_id, unsigned lineno)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_BREAK;
    stmt.lineno = lineno;
    stmt.bytecode_pc = NO_BYTECODE_PC;
    stmt.s.exit = exit_id;

    return stmt;
}

static Stmt
continue_stmt(int exit_id, unsigned lineno)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_CONTINUE;
    stmt.lineno = lineno;
    stmt.bytecode_pc = NO_BYTECODE_PC;
    stmt.s.exit = exit_id;

    return stmt;
}

static Cond_Arm
cond_arm_ast(Expr *cond, Stmt *body)
{
    Cond_Arm arm;

    memset(&arm, 0, sizeof(arm));
    arm.condition = cond;
    arm.stmt = body;

    return arm;
}

static Stmt
cond_stmt_ast(Cond_Arm *arms, Stmt *otherwise, unsigned lineno)
{
    Stmt stmt;

    memset(&stmt, 0, sizeof(stmt));
    stmt.kind = STMT_COND;
    stmt.lineno = lineno;
    stmt.s.cond.arms = arms;
    stmt.s.cond.otherwise = otherwise;

    return stmt;
}

static Expr
range_expr_ast(Expr *base, Expr *from, Expr *to, unsigned lineno)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = EXPR_RANGE;
    expr.lineno = lineno;
    expr.bytecode_pc = NO_BYTECODE_PC;
    expr.e.range.base = base;
    expr.e.range.from = from;
    expr.e.range.to = to;

    return expr;
}

static void
test_loop_dominator_tree(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;

    Expr one_init = int_expr(1, 60);
    Expr local_x_init = id_expr(16, 60);
    Expr assign_init = binary_expr(EXPR_ASGN, &local_x_init, &one_init);
    Stmt init_stmt = expr_stmt(&assign_init);

    Expr ten = int_expr(10, 61);
    Expr local_x_cond = id_expr(16, 61);
    Expr cond = binary_expr(EXPR_LT, &local_x_cond, &ten);

    Expr local_x_lhs = id_expr(16, 62);
    Expr local_x_rhs = id_expr(16, 62);
    Expr one = int_expr(1, 62);
    Expr add = binary_expr(EXPR_PLUS, &local_x_rhs, &one);
    Expr assign = binary_expr(EXPR_ASGN, &local_x_lhs, &add);
    Stmt body_stmt = expr_stmt(&assign);

    Stmt loop = while_stmt(&cond, &body_stmt, 1, 61);
    Expr local_x_ret = id_expr(16, 63);
    Stmt ret = return_stmt(&local_x_ret);

    init_stmt.next = &loop;
    loop.next = &ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    (void) lower_stmt(&names, &init_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("loop dom cfg blocks", hir_cfg_block_count(cfg), 4);
    check_int("loop dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 4);
    check_int("loop dom entry idom", hir_dom_idom_block(dom, 1), 1);
    check_int("loop dom header idom", hir_dom_idom_block(dom, 2), 1);
    check_int("loop dom body idom", hir_dom_idom_block(dom, 3), 2);
    check_int("loop dom exit idom", hir_dom_idom_block(dom, 4), 2);
    check_int("loop dom verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_while_loop_phi_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;

    Expr one_init = int_expr(1, 9);
    Expr local_x_init = id_expr(16, 9);
    Expr assign_init = binary_expr(EXPR_ASGN, &local_x_init, &one_init);
    Stmt init_stmt = expr_stmt(&assign_init);

    Expr ten = int_expr(10, 10);
    Expr local_x_cond = id_expr(16, 10);
    Expr cond = binary_expr(EXPR_LT, &local_x_cond, &ten);

    Expr local_x_lhs = id_expr(16, 11);
    Expr local_x_rhs = id_expr(16, 11);
    Expr one = int_expr(1, 11);
    Expr add = binary_expr(EXPR_PLUS, &local_x_rhs, &one);
    Expr assign = binary_expr(EXPR_ASGN, &local_x_lhs, &add);
    Stmt body_stmt = expr_stmt(&assign);

    Stmt loop = while_stmt(&cond, &body_stmt, 1, 10);
    init_stmt.next = &loop;

    Expr local_x_ret = id_expr(16, 12);
    Stmt ret = return_stmt(&local_x_ret);
    loop.next = &ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    (void) lower_stmt(&names, &init_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("loop cfg blocks", hir_cfg_block_count(cfg), 4);
    check_int("loop dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 4);

    check_int("df block 1 count", hir_dom_df_count(dom, 1), 0);
    check_int("df block 2 count", hir_dom_df_count(dom, 2), 1);
    check_int("df block 3 count", hir_dom_df_count(dom, 3), 1);
    check_int("df block 4 count", hir_dom_df_count(dom, 4), 0);

    check_int("loop ssa blocks", hir_ssa_block_count(ssa), 4);
    check_int("loop ssa instructions", hir_ssa_instruction_count(ssa), 16);
    check_int("loop ssa values", hir_ssa_value_count(ssa), 6);
    check_int("loop ssa phi count", hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("loop ssa loads", hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 0);
    check_int("loop ssa stores",
	      hir_ssa_count_kind(ssa, HIR_TAC_STORE_LOCAL), 0);
    check_int("loop ssa phi args", hir_ssa_phi_arg_count(ssa), 2);
    check_int("loop ssa zero phi args", hir_ssa_zero_phi_arg_count(ssa), 0);
    check_int("loop ssa branch uses phi",
	      hir_ssa_branch_uses_phi_count(ssa), 0);
    check_int("loop ssa lt uses phi",
	      hir_ssa_binary_uses_phi_count(ssa, HIR_OP_LT), 1);
    check_int("loop ssa add uses phi",
	      hir_ssa_binary_uses_phi_count(ssa, HIR_OP_ADD), 1);
    check_int("loop ssa return uses phi",
	      hir_ssa_return_uses_phi_count(ssa), 1);
    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("loop return fact",
	      hir_ssa_return_value_kind(ssa, analysis), HIR_VALUE_INT);
    check_int("loop constant optimization changed",
	      hir_optimize_ssa_constants(ctx, ssa), 0);
    check_int("loop optimized blocks", hir_ssa_block_count(ssa), 4);
    check_int("loop optimized verify", hir_verify_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_if_else_phi_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    HIRValueAnalysis *analysis;
    Cond_Arm arm;

    Expr one = int_expr(1, 70);
    Expr two = int_expr(2, 70);
    Expr cond = binary_expr(EXPR_LT, &one, &two);

    Expr then_value = int_expr(3, 71);
    Expr then_lhs = id_expr(16, 71);
    Expr then_assign = binary_expr(EXPR_ASGN, &then_lhs, &then_value);
    Stmt then_stmt = expr_stmt(&then_assign);

    Expr else_value = int_expr(4, 72);
    Expr else_lhs = id_expr(16, 72);
    Expr else_assign = binary_expr(EXPR_ASGN, &else_lhs, &else_value);
    Stmt else_stmt = expr_stmt(&else_assign);

    Expr ret_expr = id_expr(16, 73);
    Stmt ret = return_stmt(&ret_expr);
    Stmt if_stmt_node;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&arm, 0, sizeof(arm));
    arm.condition = &cond;
    arm.stmt = &then_stmt;

    memset(&if_stmt_node, 0, sizeof(if_stmt_node));
    if_stmt_node.kind = STMT_COND;
    if_stmt_node.lineno = 70;
    if_stmt_node.s.cond.arms = &arm;
    if_stmt_node.s.cond.otherwise = &else_stmt;
    if_stmt_node.next = &ret;

    tac = lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("ifelse tac stores",
	      hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 2);
    check_int("ifelse cfg blocks", hir_cfg_block_count(cfg), 4);
    check_int("ifelse cfg edges", hir_cfg_edge_count(cfg), 4);
    check_int("ifelse dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 4);
    check_int("ifelse ssa blocks", hir_ssa_block_count(ssa), 4);
    check_int("ifelse ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("ifelse ssa loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 0);
    check_int("ifelse ssa stores",
	      hir_ssa_count_kind(ssa, HIR_TAC_STORE_LOCAL), 0);
    check_int("ifelse ssa phi args", hir_ssa_phi_arg_count(ssa), 2);
    check_int("ifelse ssa zero phi args", hir_ssa_zero_phi_arg_count(ssa), 0);
    check_int("ifelse ssa return uses phi",
	      hir_ssa_return_uses_phi_count(ssa), 1);
#ifdef HIR_DUMP_SSA
    check_ssa_dump_contains("ifelse ssa dump header", ssa, "HIR SSA BEGIN");
    check_ssa_dump_contains("ifelse ssa dump counts", ssa,
			    "blocks=4 instructions=");
    check_ssa_dump_contains("ifelse ssa dump branch topology", ssa,
			    "preds=[] succs=[B2,B3]");
    check_ssa_dump_contains("ifelse ssa dump join topology", ssa,
			    "preds=[B2,B3] succs=[]");
    check_ssa_dump_contains("ifelse ssa dump phi", ssa,
			    "phi local[16] [B2:t");
    check_ssa_dump_contains("ifelse ssa dump phi arg", ssa, ", B3:t");
    check_ssa_dump_contains("ifelse ssa dump footer", ssa, "HIR SSA END");
#endif
    check_int("ifelse verify errors", hir_context_error_count(ctx), 0);
    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("ifelse sparse return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT_CONSTANT);
    check_int("ifelse sparse return constant",
	      (int) hir_ssa_return_constant(ssa, analysis), 3);
    check_int("ifelse constant optimization changed",
	      hir_optimize_ssa_constants(ctx, ssa), 3);
    check_int("ifelse optimized blocks", hir_ssa_block_count(ssa), 3);
    check_int("ifelse optimized edges", hir_ssa_cfg_edge_count(ssa), 2);
    check_int("ifelse optimized binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 0);
    check_int("ifelse optimized phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 0);
    check_int("ifelse optimized verify", hir_verify_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_if_then_phi_uses_entry_local_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Cond_Arm arm;

    Expr one = int_expr(1, 80);
    Expr two = int_expr(2, 80);
    Expr cond = binary_expr(EXPR_LT, &one, &two);

    Expr then_value = int_expr(3, 81);
    Expr then_lhs = id_expr(16, 81);
    Expr then_assign = binary_expr(EXPR_ASGN, &then_lhs, &then_value);
    Stmt then_stmt = expr_stmt(&then_assign);

    Expr ret_expr = id_expr(16, 82);
    Stmt ret = return_stmt(&ret_expr);
    Stmt if_stmt_node;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&arm, 0, sizeof(arm));
    arm.condition = &cond;
    arm.stmt = &then_stmt;

    memset(&if_stmt_node, 0, sizeof(if_stmt_node));
    if_stmt_node.kind = STMT_COND;
    if_stmt_node.lineno = 80;
    if_stmt_node.s.cond.arms = &arm;
    if_stmt_node.s.cond.otherwise = 0;
    if_stmt_node.next = &ret;

    tac = lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("ifthen tac stores",
	      hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 1);
    check_int("ifthen ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("ifthen ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 1);
    check_int("ifthen ssa stores",
	      hir_ssa_count_kind(ssa, HIR_TAC_STORE_LOCAL), 0);
    check_int("ifthen ssa phi args", hir_ssa_phi_arg_count(ssa), 2);
    check_int("ifthen ssa zero phi args", hir_ssa_zero_phi_arg_count(ssa), 0);
    check_int("ifthen ssa return uses phi",
	      hir_ssa_return_uses_phi_count(ssa), 1);
    check_int("ifthen verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_guarded_environment_local_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;

    Expr local_x = id_expr(0, 10);
    Expr one = int_expr(1, 10);
    Expr add = binary_expr(EXPR_PLUS, &local_x, &one);
    Stmt ret = return_stmt(&add);

    memset(&names, 0, sizeof(names));
    names.size = 1;
    local_x.bytecode_pc = 1;
    one.bytecode_pc = 2;
    add.bytecode_pc = 3;
    ret.bytecode_pc = 4;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("env local tac load count",
	      hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 1);
    check_int("env local tac const count",
	      hir_tac_count_kind(tac, HIR_TAC_CONST), 1);
    check_int("env local tac add count",
	      hir_tac_count_binary_op(tac, HIR_OP_ADD), 1);
    check_int("env local ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 1);
    check_int("env local ssa binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 1);
    check_int("env local verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("env local return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT);

    check_int("env local destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    check_int("env local out of ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 1);

    hir_context_free(ctx);
}

static void
test_multiple_guarded_environment_locals_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;

    Expr local_x = id_expr(0, 10);
    Expr local_y = id_expr(1, 10);
    Expr mult = binary_expr(EXPR_TIMES, &local_x, &local_y);
    Stmt ret = return_stmt(&mult);

    memset(&names, 0, sizeof(names));
    names.size = 2;
    local_x.bytecode_pc = 1;
    local_y.bytecode_pc = 2;
    mult.bytecode_pc = 3;
    ret.bytecode_pc = 4;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("multi env local tac load count",
	      hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 2);
    check_int("multi env local ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 2);
    check_int("multi env local ssa binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 1);
    check_int("multi env local verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("multi env local return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT);

    check_int("multi env local destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    check_int("multi env local out of ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 2);

    hir_context_free(ctx);
}

static void
test_conditional_local_assignment_with_entry_local_analysis(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;
    Cond_Arm arm;

    Expr cond_x = id_expr(0, 80);
    Expr then_value = int_expr(3, 81);
    Expr then_lhs = id_expr(1, 81);
    Expr then_assign = binary_expr(EXPR_ASGN, &then_lhs, &then_value);
    Stmt then_stmt = expr_stmt(&then_assign);

    Expr ret_local = id_expr(1, 82);
    Expr two = int_expr(2, 82);
    Expr ret_add = binary_expr(EXPR_PLUS, &ret_local, &two);
    Stmt ret = return_stmt(&ret_add);
    Stmt if_stmt_node;

    memset(&names, 0, sizeof(names));
    names.size = 2;
    memset(&arm, 0, sizeof(arm));
    arm.condition = &cond_x;
    arm.stmt = &then_stmt;

    memset(&if_stmt_node, 0, sizeof(if_stmt_node));
    if_stmt_node.kind = STMT_COND;
    if_stmt_node.lineno = 80;
    if_stmt_node.s.cond.arms = &arm;
    if_stmt_node.s.cond.otherwise = 0;
    if_stmt_node.next = &ret;

    tac = lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("cond assign tac not null", tac != 0, 1);
    check_int("cond assign ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("cond assign ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 2);
    check_int("cond assign verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("cond assign return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT);

    check_int("cond assign destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    check_int("cond assign out of ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 2);

    hir_context_free(ctx);
}

static void
test_list_index_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;

    Expr local_args = id_expr(0, 10);
    Expr one = int_expr(1, 10);
    Expr index_node = binary_expr(EXPR_INDEX, &local_args, &one);
    Stmt ret = return_stmt(&index_node);

    memset(&names, 0, sizeof(names));
    names.size = 1;
    local_args.bytecode_pc = 1;
    one.bytecode_pc = 2;
    index_node.bytecode_pc = 3;
    ret.bytecode_pc = 4;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("list index tac load count",
	      hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 1);
    check_int("list index tac const count",
	      hir_tac_count_kind(tac, HIR_TAC_CONST), 1);
    check_int("list index tac binary count",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX), 1);
    check_int("list index ssa entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 1);
    check_int("list index ssa binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 1);
    check_int("list index verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("list index return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT);

    check_int("list index destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    check_int("list index out of ssa binary",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 1);

    hir_context_free(ctx);
}

static void
test_list_index_in_arithmetic_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;

    Expr local_args1 = id_expr(0, 10);
    Expr one = int_expr(1, 10);
    Expr idx1 = binary_expr(EXPR_INDEX, &local_args1, &one);
    Expr local_args2 = id_expr(0, 10);
    Expr two = int_expr(2, 10);
    Expr idx2 = binary_expr(EXPR_INDEX, &local_args2, &two);
    Expr add = binary_expr(EXPR_PLUS, &idx1, &idx2);
    Stmt ret = return_stmt(&add);

    memset(&names, 0, sizeof(names));
    names.size = 1;
    local_args1.bytecode_pc = 1;
    one.bytecode_pc = 2;
    idx1.bytecode_pc = 3;
    local_args2.bytecode_pc = 4;
    two.bytecode_pc = 5;
    idx2.bytecode_pc = 6;
    add.bytecode_pc = 7;
    ret.bytecode_pc = 8;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("arith index tac binary index count",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX), 2);
    check_int("arith index tac binary add count",
	      hir_tac_count_binary_op(tac, HIR_OP_ADD), 1);
    check_int("arith index verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("arith index return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT);

    check_int("arith index destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_scatter_destructuring_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRValueAnalysis *analysis;
    HIRTacProgram *tac;
    Scatter sc1, sc2;
    Expr scatter_lhs, args_rhs, asgn_expr, ret_add, ret_x, ret_y;
    Stmt asgn_stmt_node, ret_stmt_node;

    memset(&sc1, 0, sizeof(sc1));
    sc1.kind = SCAT_REQUIRED;
    sc1.id = 1;
    sc1.next = &sc2;

    memset(&sc2, 0, sizeof(sc2));
    sc2.kind = SCAT_REQUIRED;
    sc2.id = 2;
    sc2.next = 0;

    memset(&scatter_lhs, 0, sizeof(scatter_lhs));
    scatter_lhs.kind = EXPR_SCATTER;
    scatter_lhs.lineno = 10;
    scatter_lhs.e.scatter = &sc1;

    args_rhs = id_expr(0, 10);
    asgn_expr = binary_expr(EXPR_ASGN, &scatter_lhs, &args_rhs);
    asgn_stmt_node = expr_stmt(&asgn_expr);

    ret_x = id_expr(1, 11);
    ret_y = id_expr(2, 11);
    ret_add = binary_expr(EXPR_PLUS, &ret_x, &ret_y);
    ret_stmt_node = return_stmt(&ret_add);
    asgn_stmt_node.next = &ret_stmt_node;

    memset(&names, 0, sizeof(names));
    names.size = 3;
    args_rhs.bytecode_pc = 1;
    asgn_expr.bytecode_pc = 2;
    asgn_stmt_node.bytecode_pc = 3;
    ret_x.bytecode_pc = 4;
    ret_y.bytecode_pc = 5;
    ret_add.bytecode_pc = 6;
    ret_stmt_node.bytecode_pc = 7;

    tac = lower_stmt(&names, &asgn_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("scatter tac not null", tac != 0, 1);
    check_int("scatter tac store count",
	      hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 2);
    check_int("scatter tac binary index count",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX), 2);
    check_int("scatter tac binary add count",
	      hir_tac_count_binary_op(tac, HIR_OP_ADD), 1);
    check_int("scatter verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("scatter return fact",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT);

    check_int("scatter destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_list_construction_and_splicing_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Arg_List a1, a2, a3;
    Expr e1, e2, e3, list_expr;
    Stmt ret;

    e1 = int_expr(1, 10);
    e2 = id_expr(0, 10);
    e3 = int_expr(2, 10);

    memset(&a1, 0, sizeof(a1));
    a1.kind = ARG_NORMAL;
    a1.expr = &e1;
    a1.next = &a2;

    memset(&a2, 0, sizeof(a2));
    a2.kind = ARG_SPLICE;
    a2.expr = &e2;
    a2.next = &a3;

    memset(&a3, 0, sizeof(a3));
    a3.kind = ARG_NORMAL;
    a3.expr = &e3;
    a3.next = 0;

    memset(&list_expr, 0, sizeof(list_expr));
    list_expr.kind = EXPR_LIST;
    list_expr.lineno = 10;
    list_expr.e.list = &a1;

    ret = return_stmt(&list_expr);

    memset(&names, 0, sizeof(names));
    names.size = 2;
    e1.bytecode_pc = 1;
    e2.bytecode_pc = 2;
    e3.bytecode_pc = 3;
    list_expr.bytecode_pc = 4;
    ret.bytecode_pc = 5;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("list splice tac not null", tac != 0, 1);
    check_int("list splice singleton count",
	      hir_tac_count_unary_op(tac, HIR_OP_MAKE_SINGLETON_LIST), 1);
    check_int("list splice append count",
	      hir_tac_count_binary_op(tac, HIR_OP_LIST_APPEND), 1);
    check_int("list splice add tail count",
	      hir_tac_count_binary_op(tac, HIR_OP_LIST_ADD_TAIL), 1);
    check_int("list splice verify errors", hir_context_error_count(ctx), 0);

    check_int("list splice destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_builtin_call_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Arg_List arg;
    Expr call_arg, call_expr;
    Stmt ret;

    call_arg = int_expr(123, 10);
    memset(&arg, 0, sizeof(arg));
    arg.kind = ARG_NORMAL;
    arg.expr = &call_arg;
    arg.next = 0;

    memset(&call_expr, 0, sizeof(call_expr));
    call_expr.kind = EXPR_CALL;
    call_expr.lineno = 10;
    call_expr.e.call.func = 99;
    call_expr.e.call.args = &arg;

    ret = return_stmt(&call_expr);

    memset(&names, 0, sizeof(names));
    names.size = 2;
    call_arg.bytecode_pc = 1;
    arg.bytecode_pc = 2;
    call_expr.bytecode_pc = 3;
    ret.bytecode_pc = 4;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("builtin call tac not null", tac != 0, 1);
    check_int("builtin call tac count",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 1);
    check_int("builtin call singleton count",
	      hir_tac_count_unary_op(tac, HIR_OP_MAKE_SINGLETON_LIST), 1);
    check_int("builtin call verify errors", hir_context_error_count(ctx), 0);

    check_int("builtin call destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_pure_builtin_inlining_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    HIRValueAnalysis *analysis;
    Arg_List a1, a2;
    Expr e1, e2, call_abs, call_min;
    Stmt ret;

    e1 = int_expr(-42, 10);
    memset(&a1, 0, sizeof(a1));
    a1.kind = ARG_NORMAL;
    a1.expr = &e1;
    a1.next = 0;

    memset(&call_abs, 0, sizeof(call_abs));
    call_abs.kind = EXPR_CALL;
    call_abs.lineno = 10;
    call_abs.e.call.func = 3; /* abs */
    call_abs.e.call.args = &a1;

    ret = return_stmt(&call_abs);

    memset(&names, 0, sizeof(names));
    names.size = 2;
    e1.bytecode_pc = 1;
    a1.bytecode_pc = 2;
    call_abs.bytecode_pc = 3;
    ret.bytecode_pc = 4;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("abs inline tac not null", tac != 0, 1);
    check_int("abs inline unary count",
	      hir_tac_count_unary_op(tac, HIR_OP_ABS), 1);
    check_int("abs inline call count",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 0);
    check_int("abs inline verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("abs inline return kind",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT_CONSTANT);
    check_int("abs inline return constant",
	      hir_ssa_return_constant(ssa, analysis), 42);

    check_int("abs inline destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);

    /* Test min(10, 20) inlining */
    e1 = int_expr(10, 10);
    e2 = int_expr(20, 10);
    memset(&a2, 0, sizeof(a2));
    a2.kind = ARG_NORMAL;
    a2.expr = &e2;
    a2.next = 0;

    memset(&a1, 0, sizeof(a1));
    a1.kind = ARG_NORMAL;
    a1.expr = &e1;
    a1.next = &a2;

    memset(&call_min, 0, sizeof(call_min));
    call_min.kind = EXPR_CALL;
    call_min.lineno = 10;
    call_min.e.call.func = 4; /* min */
    call_min.e.call.args = &a1;

    ret = return_stmt(&call_min);

    memset(&names, 0, sizeof(names));
    names.size = 2;
    e1.bytecode_pc = 1;
    e2.bytecode_pc = 2;
    a1.bytecode_pc = 3;
    a2.bytecode_pc = 4;
    call_min.bytecode_pc = 5;
    ret.bytecode_pc = 6;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("min inline tac not null", tac != 0, 1);
    check_int("min inline binary count",
	      hir_tac_count_binary_op(tac, HIR_OP_MIN), 1);
    check_int("min inline call count",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 0);
    check_int("min inline verify errors", hir_context_error_count(ctx), 0);

    analysis = hir_analyze_ssa_values(ctx, ssa);
    check_int("min inline return kind",
	      hir_ssa_return_value_kind(ssa, analysis),
	      HIR_VALUE_INT_CONSTANT);
    check_int("min inline return constant",
	      hir_ssa_return_constant(ssa, analysis), 10);

    check_int("min inline destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_property_read_and_write_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr obj, name, prop_read, val, prop_write;
    Stmt asgn, ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    obj = id_expr(0, 10);
    name = id_expr(1, 10);
    prop_read = binary_expr(EXPR_PROP, &obj, &name);

    val = int_expr(42, 10);
    prop_write = binary_expr(EXPR_ASGN, &prop_read, &val);

    asgn = expr_stmt(&prop_write);
    ret = return_stmt(&prop_read);
    asgn.next = &ret;

    obj.bytecode_pc = 1;
    name.bytecode_pc = 2;
    prop_read.bytecode_pc = 3;
    val.bytecode_pc = 4;
    prop_write.bytecode_pc = 5;
    asgn.bytecode_pc = 6;
    ret.bytecode_pc = 7;

    tac = lower_stmt(&names, &asgn, &ctx, &cfg, &dom, &ssa);

    check_int("prop tac not null", tac != 0, 1);
    check_int("prop get_prop count",
	      hir_tac_count_binary_op(tac, HIR_OP_GET_PROP), 1);
    check_int("prop put_prop count",
	      hir_tac_count_kind(tac, HIR_TAC_PUT_PROP), 1);
    check_int("prop verify errors", hir_context_error_count(ctx), 0);

    check_int("prop destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_for_range_loop_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;

    /* sum = 0; */
    Expr sum_lhs = id_expr(1, 10);
    Expr zero = int_expr(0, 10);
    Expr init_assign = binary_expr(EXPR_ASGN, &sum_lhs, &zero);
    Stmt init_stmt = expr_stmt(&init_assign);

    /* for i in [1..5] sum = sum + i; endfor */
    Expr from = int_expr(1, 11);
    Expr to = int_expr(5, 11);
    Expr sum_body_lhs = id_expr(1, 12);
    Expr sum_body_rhs = id_expr(1, 12);
    Expr i_rhs = id_expr(2, 12);
    Expr add = binary_expr(EXPR_PLUS, &sum_body_rhs, &i_rhs);
    Expr body_assign = binary_expr(EXPR_ASGN, &sum_body_lhs, &add);
    Stmt body_stmt = expr_stmt(&body_assign);

    Stmt loop = range_stmt(2, &from, &to, &body_stmt, 11);

    /* return sum; */
    Expr sum_ret = id_expr(1, 13);
    Stmt ret = return_stmt(&sum_ret);

    init_stmt.next = &loop;
    loop.next = &ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &init_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("for range tac not null", tac != 0, 1);
    check_int("for range verify errors", hir_context_error_count(ctx), 0);
    check_int("for range branch false count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 2);
    check_int("for range jump count",
	      hir_tac_count_kind(tac, HIR_TAC_JUMP), 1);
    check_int("for range tick count",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 4);
    check_int("for range ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI) >= 2, 1);

    check_int("for range destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_for_list_loop_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr iterable = id_expr(3, 11);
    Expr sum_lhs = id_expr(1, 12);
    Expr sum_rhs = id_expr(1, 12);
    Expr item = id_expr(2, 12);
    Expr add = binary_expr(EXPR_PLUS, &sum_rhs, &item);
    Expr assign = binary_expr(EXPR_ASGN, &sum_lhs, &add);
    Stmt body = expr_stmt(&assign);
    Stmt loop = list_stmt(2, &iterable, &body, 11);
    Expr result = id_expr(1, 13);
    Stmt ret = return_stmt(&result);

    loop.next = &ret;
    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &loop, &ctx, &cfg, &dom, &ssa);

    check_int("for list tac not null", tac != 0, 1);
    check_int("for list verify errors", hir_context_error_count(ctx), 0);
    check_int("for list length count",
	      hir_tac_count_unary_op(tac, HIR_OP_LENGTH), 1);
    check_int("for list index count",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX), 1);
    check_int("for list branch false count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 1);
    check_int("for list tick count",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 3);
    check_int("for list ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI) >= 2, 1);

    check_int("for list destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_cond_expr_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;

    /* x = 1 > 0 ? 10 | (0 ? 20 | 30); return x; */
    Expr one = int_expr(1, 10);
    Expr zero = int_expr(0, 10);
    Expr cond = binary_expr(EXPR_GT, &one, &zero);
    Expr ten = int_expr(10, 10);
    Expr twenty = int_expr(20, 10);
    Expr thirty = int_expr(30, 10);
    Expr nested = cond_expr_ast(&zero, &twenty, &thirty, 10);
    Expr ternary = cond_expr_ast(&cond, &ten, &nested, 10);
    Expr x_lhs = id_expr(1, 10);
    Expr assign = binary_expr(EXPR_ASGN, &x_lhs, &ternary);
    Stmt assign_stmt = expr_stmt(&assign);
    Expr x_ret = id_expr(1, 11);
    Stmt ret = return_stmt(&x_ret);

    assign_stmt.next = &ret;
    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &assign_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("cond expr tac not null", tac != 0, 1);
    check_int("cond expr verify errors", hir_context_error_count(ctx), 0);
    check_int("cond expr branch false count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 2);
    check_int("cond expr jump count",
	      hir_tac_count_kind(tac, HIR_TAC_JUMP), 2);
    check_int("cond expr ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI) >= 2, 1);
    check_int("cond expr tick count",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 4);
    check_int("cond expr optimize", hir_optimize_ssa_constants(ctx, ssa) > 0,
	      1);
    check_int("cond expr optimized verify", hir_verify_ssa(ctx, ssa), 1);
    check_int("cond expr optimized branches",
	      hir_ssa_count_kind(ssa, HIR_TAC_BRANCH_FALSE), 0);

    check_int("cond expr destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_break_and_continue_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;

    /*
     * for i in [1..10]
     *   if (i == 3)
     *     continue;
     *   endif
     *   if (i > 8)
     *     break;
     *   endif
     *   sum = sum + i;
     * endfor
     * return sum;
     */
    Expr from = int_expr(1, 10);
    Expr to = int_expr(10, 10);
    Expr i_ref1 = id_expr(2, 11);
    Expr three = int_expr(3, 11);
    Expr cond1 = binary_expr(EXPR_EQ, &i_ref1, &three);
    Stmt cont = continue_stmt(-1, 12);
    Cond_Arm arm1 = cond_arm_ast(&cond1, &cont);
    Stmt if_cont = cond_stmt_ast(&arm1, 0, 11);

    Expr i_ref2 = id_expr(2, 14);
    Expr eight = int_expr(8, 14);
    Expr cond2 = binary_expr(EXPR_GT, &i_ref2, &eight);
    Stmt brk = break_stmt(-1, 15);
    Cond_Arm arm2 = cond_arm_ast(&cond2, &brk);
    Stmt if_brk = cond_stmt_ast(&arm2, 0, 14);

    Expr sum_lhs = id_expr(1, 17);
    Expr sum_rhs = id_expr(1, 17);
    Expr i_ref3 = id_expr(2, 17);
    Expr add = binary_expr(EXPR_PLUS, &sum_rhs, &i_ref3);
    Expr assign = binary_expr(EXPR_ASGN, &sum_lhs, &add);
    Stmt body_assign = expr_stmt(&assign);

    if_cont.next = &if_brk;
    if_brk.next = &body_assign;

    Stmt loop = range_stmt(2, &from, &to, &if_cont, 10);
    Expr sum_ret = id_expr(1, 19);
    Stmt ret = return_stmt(&sum_ret);

    loop.next = &ret;
    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &loop, &ctx, &cfg, &dom, &ssa);

    check_int("break/cont tac not null", tac != 0, 1);
    check_int("break/cont verify errors", hir_context_error_count(ctx), 0);
    check_int("break/cont ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI) >= 2, 1);
    check_int("break/cont tick count",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 9);

    check_int("break/cont destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_labeled_break_nested_loops_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;

    /*
     * for i in [1..10]
     *   for j in [1..10]
     *     if (j == 5)
     *       break i;
     *     endif
     *     sum = sum + j;
     *   endfor
     * endfor
     * return sum;
     */
    Expr from1 = int_expr(1, 10);
    Expr to1 = int_expr(10, 10);
    Expr from2 = int_expr(1, 11);
    Expr to2 = int_expr(10, 11);

    Expr j_ref1 = id_expr(3, 12);
    Expr five = int_expr(5, 12);
    Expr cond = binary_expr(EXPR_EQ, &j_ref1, &five);
    Stmt brk_outer = break_stmt(2, 13); /* break i */
    Cond_Arm arm = cond_arm_ast(&cond, &brk_outer);
    Stmt if_brk = cond_stmt_ast(&arm, 0, 12);

    Expr sum_lhs = id_expr(1, 14);
    Expr sum_rhs = id_expr(1, 14);
    Expr j_ref2 = id_expr(3, 14);
    Expr add = binary_expr(EXPR_PLUS, &sum_rhs, &j_ref2);
    Expr assign = binary_expr(EXPR_ASGN, &sum_lhs, &add);
    Stmt body_assign = expr_stmt(&assign);

    if_brk.next = &body_assign;

    Stmt inner_loop = range_stmt(3, &from2, &to2, &if_brk, 11);
    Stmt outer_loop = range_stmt(2, &from1, &to1, &inner_loop, 10);

    Expr sum_ret = id_expr(1, 16);
    Stmt ret = return_stmt(&sum_ret);

    outer_loop.next = &ret;
    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &outer_loop, &ctx, &cfg, &dom, &ssa);

    check_int("labeled break tac not null", tac != 0, 1);
    check_int("labeled break verify errors", hir_context_error_count(ctx), 0);
    check_int("labeled break ssa phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI) >= 2, 1);
    check_int("labeled break tick count",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 7);

    check_int("labeled break destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_range_expr_and_assignment_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;

    /*
     * sub = list[2..4];
     * list[2..4] = {10, 20};
     * return sub;
     */
    Expr list_id = id_expr(1, 10);
    Expr from1 = int_expr(2, 10);
    Expr to1 = int_expr(4, 10);
    Expr slice = range_expr_ast(&list_id, &from1, &to1, 10);
    Expr sub_id = id_expr(2, 10);
    Expr assign_sub = binary_expr(EXPR_ASGN, &sub_id, &slice);
    Stmt stmt1 = expr_stmt(&assign_sub);

    Expr list_id2 = id_expr(1, 11);
    Expr from2 = int_expr(2, 11);
    Expr to2 = int_expr(4, 11);
    Expr lhs_range = range_expr_ast(&list_id2, &from2, &to2, 11);
    Expr ten = int_expr(10, 11);
    Expr twenty = int_expr(20, 11);
    Arg_List a2;
    Arg_List a1;
    Expr rhs_list;

    memset(&a2, 0, sizeof(a2));
    a2.kind = ARG_NORMAL;
    a2.expr = &twenty;
    a2.next = 0;

    memset(&a1, 0, sizeof(a1));
    a1.kind = ARG_NORMAL;
    a1.expr = &ten;
    a1.next = &a2;

    memset(&rhs_list, 0, sizeof(rhs_list));
    rhs_list.kind = EXPR_LIST;
    rhs_list.lineno = 11;
    rhs_list.bytecode_pc = NO_BYTECODE_PC;
    rhs_list.e.list = &a1;

    Expr assign_range = binary_expr(EXPR_ASGN, &lhs_range, &rhs_list);
    Stmt stmt2 = expr_stmt(&assign_range);

    Expr ret_expr = id_expr(2, 12);
    Stmt ret = return_stmt(&ret_expr);

    stmt1.next = &stmt2;
    stmt2.next = &ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &stmt1, &ctx, &cfg, &dom, &ssa);

    check_int("range tac not null", tac != 0, 1);
    check_int("range ref count", hir_tac_count_kind(tac, HIR_TAC_RANGE_REF), 1);
    check_int("range set count", hir_tac_count_kind(tac, HIR_TAC_RANGE_SET), 1);
    check_int("range tick count", hir_tac_count_kind(tac, HIR_TAC_TICK), 3);
    check_int("range verify errors", hir_context_error_count(ctx), 0);
    check_int("range destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_verb_call_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr verb_call, obj, name, arg_val;
    Arg_List arg;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    obj = id_expr(0, 30);
    name = id_expr(1, 30);
    arg_val = int_expr(42, 30);
    memset(&arg, 0, sizeof(arg));
    arg.kind = ARG_NORMAL;
    arg.expr = &arg_val;
    arg.next = 0;

    memset(&verb_call, 0, sizeof(verb_call));
    verb_call.kind = EXPR_VERB;
    verb_call.lineno = 30;
    verb_call.e.verb.obj = &obj;
    verb_call.e.verb.verb = &name;
    verb_call.e.verb.args = &arg;
    ret = return_stmt(&verb_call);

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("verb call tac not null", tac != 0, 1);
    check_int("verb call count", hir_tac_count_kind(tac, HIR_TAC_CALL_VERB), 1);
    check_int("verb call verify errors", hir_context_error_count(ctx), 0);
    check_int("verb call destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_object_scalars_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr from_expr, to_expr, o_lhs, o_rhs, one, add, assign, ret_expr;
    Stmt for_stmt, ret_stmt, body_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    /* Object range loop: for o in [#0..#5] ... endfor */
    memset(&from_expr, 0, sizeof(from_expr));
    from_expr.kind = EXPR_VAR;
    from_expr.lineno = 10;
    from_expr.e.var.type = TYPE_OBJ;
    from_expr.e.var.v.obj = 0;

    memset(&to_expr, 0, sizeof(to_expr));
    to_expr.kind = EXPR_VAR;
    to_expr.lineno = 10;
    to_expr.e.var.type = TYPE_OBJ;
    to_expr.e.var.v.obj = 5;

    o_lhs = id_expr(1, 11);
    o_rhs = id_expr(1, 11);
    one = int_expr(1, 11);
    add = binary_expr(EXPR_PLUS, &o_rhs, &one);
    assign = binary_expr(EXPR_ASGN, &o_lhs, &add);
    body_stmt = expr_stmt(&assign);

    for_stmt = range_stmt(1, &from_expr, &to_expr, &body_stmt, 10);

    ret_expr = id_expr(1, 12);
    ret_stmt = return_stmt(&ret_expr);
    ret_stmt.lineno = 12;

    for_stmt.next = &ret_stmt;

    tac = lower_stmt(&names, &for_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("obj range tac not null", tac != 0, 1);
    check_int("obj range verify errors", hir_context_error_count(ctx), 0);
    check_int("obj range destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_float_scalars_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr f1, f2, add;
    Stmt ret_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    memset(&f1, 0, sizeof(f1));
    f1.kind = EXPR_VAR;
    f1.lineno = 10;
    f1.e.var.type = TYPE_FLOAT;
    f1.e.var.v.fnum = box_fl(3.14);

    memset(&f2, 0, sizeof(f2));
    f2.kind = EXPR_VAR;
    f2.lineno = 10;
    f2.e.var.type = TYPE_FLOAT;
    f2.e.var.v.fnum = box_fl(2.71);

    add = binary_expr(EXPR_PLUS, &f1, &f2);
    ret_stmt = return_stmt(&add);
    ret_stmt.lineno = 10;

    tac = lower_stmt(&names, &ret_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("float scalar tac not null", tac != 0, 1);
    check_int("float scalar verify errors", hir_context_error_count(ctx), 0);
    check_int("float scalar destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_string_scalars_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr s1;
    Stmt ret_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    memset(&s1, 0, sizeof(s1));
    s1.kind = EXPR_VAR;
    s1.lineno = 10;
    s1.e.var.type = TYPE_STR;
    s1.e.var.v.str = str_dup("hello string");

    ret_stmt = return_stmt(&s1);
    ret_stmt.lineno = 10;

    tac = lower_stmt(&names, &ret_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("string scalar tac not null", tac != 0, 1);
    check_int("string scalar verify errors", hir_context_error_count(ctx), 0);
    check_int("string scalar const count",
	      hir_tac_count_kind(tac, HIR_TAC_CONST), 1);
    check_int("string scalar return count",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("string scalar destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
    free_str(s1.e.var.v.str);
}

static void
test_cfg_critical_edge_splitting(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    int before_blocks;
    int before_edges;
    int split_count;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    ctx = hir_context_new(&names);
    cfg = hir_test_cfg_with_critical_edge(ctx);
    (void) hir_verify_cfg(ctx, cfg);

    before_blocks = hir_cfg_block_count(cfg);
    before_edges = hir_cfg_edge_count(cfg);
    check_int("critical cfg initial edges",
	      hir_cfg_critical_edge_count(cfg), 1);

    split_count = hir_split_critical_edges(ctx, cfg);
    check_int("critical cfg split count", split_count, 1);
    check_int("critical cfg final edges",
	      hir_cfg_critical_edge_count(cfg), 0);
    check_int("critical cfg split blocks",
	      hir_cfg_block_count(cfg), before_blocks + 1);
    check_int("critical cfg split edges",
	      hir_cfg_edge_count(cfg), before_edges + 1);
    check_int("critical cfg resplit count",
	      hir_split_critical_edges(ctx, cfg), 0);
    check_int("critical cfg resplit blocks",
	      hir_cfg_block_count(cfg), before_blocks + 1);
    check_int("critical cfg resplit edges",
	      hir_cfg_edge_count(cfg), before_edges + 1);
    (void) hir_verify_cfg(ctx, cfg);
    check_int("critical cfg verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_if_else_ssa_destruction(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    Cond_Arm arm;
    Expr one = int_expr(1, 100);
    Expr two = int_expr(2, 100);
    Expr cond = binary_expr(EXPR_LT, &one, &two);
    Expr then_value = int_expr(3, 101);
    Expr then_lhs = id_expr(16, 101);
    Expr then_assign = binary_expr(EXPR_ASGN, &then_lhs, &then_value);
    Stmt then_stmt = expr_stmt(&then_assign);
    Expr else_value = int_expr(4, 102);
    Expr else_lhs = id_expr(16, 102);
    Expr else_assign = binary_expr(EXPR_ASGN, &else_lhs, &else_value);
    Stmt else_stmt = expr_stmt(&else_assign);
    Expr ret_expr = id_expr(16, 103);
    Stmt ret = return_stmt(&ret_expr);
    Stmt if_stmt_node;
    int before_errors;
    int accepted;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&arm, 0, sizeof(arm));
    arm.condition = &cond;
    arm.stmt = &then_stmt;

    memset(&if_stmt_node, 0, sizeof(if_stmt_node));
    if_stmt_node.kind = STMT_COND;
    if_stmt_node.lineno = 100;
    if_stmt_node.s.cond.arms = &arm;
    if_stmt_node.s.cond.otherwise = &else_stmt;
    if_stmt_node.next = &ret;

    (void) lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);
    check_int("ifelse destroy initial form", hir_ssa_form(ssa), HIR_FORM_SSA);
    check_int("ifelse destroy initial phi",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);

    accepted = hir_destroy_ssa(ctx, ssa);
    check_int("ifelse destroy accepted", accepted, 1);
    check_int("ifelse destroy form", hir_ssa_form(ssa),
	      HIR_FORM_OUT_OF_SSA);
    check_int("ifelse destroy phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 0);
    check_int("ifelse destroy copy instrs",
	      hir_ssa_count_kind(ssa, HIR_TAC_PARALLEL_COPY), 2);
    check_int("ifelse destroy copy pairs",
	      hir_ssa_parallel_copy_pair_count(ssa), 2);
    check_int("ifelse destroy critical edges",
	      hir_cfg_critical_edge_count(cfg), 0);
    check_int("ifelse destroy out verify",
	      hir_verify_out_of_ssa(ctx, ssa), 1);

    before_errors = hir_context_error_count(ctx);
    accepted = hir_verify_ssa(ctx, ssa);
    check_rejected("ifelse destroy strict ssa rejected", accepted,
		   before_errors, hir_context_error_count(ctx));

    hir_context_free(ctx);
}

static void
test_loop_ssa_destruction(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    Expr one_init = int_expr(1, 110);
    Expr local_x_init = id_expr(16, 110);
    Expr assign_init = binary_expr(EXPR_ASGN, &local_x_init, &one_init);
    Stmt init_stmt = expr_stmt(&assign_init);
    Expr ten = int_expr(10, 111);
    Expr local_x_cond = id_expr(16, 111);
    Expr cond = binary_expr(EXPR_LT, &local_x_cond, &ten);
    Expr local_x_lhs = id_expr(16, 112);
    Expr local_x_rhs = id_expr(16, 112);
    Expr one = int_expr(1, 112);
    Expr add = binary_expr(EXPR_PLUS, &local_x_rhs, &one);
    Expr assign = binary_expr(EXPR_ASGN, &local_x_lhs, &add);
    Stmt body_stmt = expr_stmt(&assign);
    Stmt loop = while_stmt(&cond, &body_stmt, 1, 111);
    Expr local_x_ret = id_expr(16, 113);
    Stmt ret = return_stmt(&local_x_ret);

    init_stmt.next = &loop;
    loop.next = &ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    (void) lower_stmt(&names, &init_stmt, &ctx, &cfg, &dom, &ssa);
    check_int("loop destroy initial phi",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);

    check_int("loop destroy accepted", hir_destroy_ssa(ctx, ssa), 1);
    check_int("loop destroy form", hir_ssa_form(ssa),
	      HIR_FORM_OUT_OF_SSA);
    check_int("loop destroy phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 0);
    check_int("loop destroy copy pairs",
	      hir_ssa_parallel_copy_pair_count(ssa), 2);
    check_int("loop destroy out verify",
	      hir_verify_out_of_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_critical_edge_ssa_destruction(void)
{
    Names names;
    HIRContext *ctx;
    HIRSSAProgram *ssa;
    int before_blocks;
    int before_edges;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    ctx = hir_context_new(&names);
    ssa = hir_test_ssa_with_critical_phi_edge(ctx);

    check_int("critical destroy initial verify", hir_verify_ssa(ctx, ssa), 1);
    check_int("critical destroy initial edges",
	      hir_ssa_cfg_critical_edge_count(ssa), 1);
    before_blocks = hir_ssa_cfg_block_count(ssa);
    before_edges = hir_ssa_cfg_edge_count(ssa);

    check_int("critical destroy accepted", hir_destroy_ssa(ctx, ssa), 1);
    check_int("critical destroy form", hir_ssa_form(ssa),
	      HIR_FORM_OUT_OF_SSA);
    check_int("critical destroy phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 0);
    check_int("critical destroy copy instrs",
	      hir_ssa_count_kind(ssa, HIR_TAC_PARALLEL_COPY), 2);
    check_int("critical destroy copy pairs",
	      hir_ssa_parallel_copy_pair_count(ssa), 2);
    check_int("critical destroy split blocks",
	      hir_ssa_cfg_block_count(ssa), before_blocks + 1);
    check_int("critical destroy split edges",
	      hir_ssa_cfg_edge_count(ssa), before_edges + 1);
    check_int("critical destroy final edges",
	      hir_ssa_cfg_critical_edge_count(ssa), 0);
    check_int("critical destroy out verify",
	      hir_verify_out_of_ssa(ctx, ssa), 1);
    check_int("critical destroy idempotent", hir_destroy_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_repeated_local_assignment_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr values[6];
    Expr lhs[6];
    Expr assigns[6];
    Stmt stmts[6];
    Expr ret_expr;
    Stmt ret;
    int i;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    for (i = 0; i < 6; i++) {
	values[i] = int_expr(i + 1, 40 + (unsigned) i);
	lhs[i] = id_expr(16, 40 + (unsigned) i);
	assigns[i] = binary_expr(EXPR_ASGN, &lhs[i], &values[i]);
	stmts[i] = expr_stmt(&assigns[i]);
	if (i > 0)
	    stmts[i - 1].next = &stmts[i];
    }

    ret_expr = id_expr(16, 50);
    ret = return_stmt(&ret_expr);
    stmts[5].next = &ret;

    tac = lower_stmt(&names, &stmts[0], &ctx, &cfg, &dom, &ssa);

    check_int("repeat assign tac stores",
	      hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 6);
    check_int("repeat assign cfg blocks", hir_cfg_block_count(cfg), 1);
    check_int("repeat assign ssa instructions",
	      hir_ssa_instruction_count(ssa), 13);
    check_int("repeat assign ssa values", hir_ssa_value_count(ssa), 6);
    check_int("repeat assign ssa loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 0);
    check_int("repeat assign ssa stores",
	      hir_ssa_count_kind(ssa, HIR_TAC_STORE_LOCAL), 0);
    check_int("repeat assign verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_catch_expr_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr catch_expr, try_expr, handler_expr;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    try_expr = id_expr(0, 30);
    handler_expr = int_expr(42, 30);
    memset(&catch_expr, 0, sizeof(catch_expr));
    catch_expr.kind = EXPR_CATCH;
    catch_expr.lineno = 30;
    catch_expr.e.catch.try = &try_expr;
    catch_expr.e.catch.codes = 0;
    catch_expr.e.catch.except = &handler_expr;
    ret = return_stmt(&catch_expr);

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("catch expr tac returns",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("catch expr cfg blocks", hir_cfg_block_count(cfg) > 1, 1);
    check_int("catch expr ssa blocks", hir_ssa_block_count(ssa) > 1, 1);
    check_int("catch expr verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_try_except_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr val_expr, handler_val;
    Stmt body_stmt, handler_stmt, try_stmt;
    Except_Arm except_arm;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    val_expr = int_expr(10, 40);
    body_stmt = return_stmt(&val_expr);
    handler_val = int_expr(20, 42);
    handler_stmt = return_stmt(&handler_val);

    memset(&except_arm, 0, sizeof(except_arm));
    except_arm.id = -1;
    except_arm.codes = 0;
    except_arm.stmt = &handler_stmt;

    memset(&try_stmt, 0, sizeof(try_stmt));
    try_stmt.kind = STMT_TRY_EXCEPT;
    try_stmt.lineno = 40;
    try_stmt.s.catch.body = &body_stmt;
    try_stmt.s.catch.excepts = &except_arm;

    tac = lower_stmt(&names, &try_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("try except tac returns",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 2);
    check_int("try except cfg blocks", hir_cfg_block_count(cfg) > 1, 1);
    check_int("try except ssa blocks", hir_ssa_block_count(ssa) > 1, 1);
    check_int("try except verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_try_finally_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr body_val, handler_val;
    Stmt body_stmt, handler_stmt, try_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    body_val = int_expr(100, 50);
    body_stmt = expr_stmt(&body_val);
    handler_val = int_expr(200, 52);
    handler_stmt = return_stmt(&handler_val);

    memset(&try_stmt, 0, sizeof(try_stmt));
    try_stmt.kind = STMT_TRY_FINALLY;
    try_stmt.lineno = 50;
    try_stmt.s.finally.body = &body_stmt;
    try_stmt.s.finally.handler = &handler_stmt;

    tac = lower_stmt(&names, &try_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("try finally tac returns",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("try finally cfg blocks", hir_cfg_block_count(cfg) > 1, 1);
    check_int("try finally ssa blocks", hir_ssa_block_count(ssa) > 1, 1);
    check_int("try finally verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

int
main(void)
{
    test_arithmetic_and_local_tac();
    test_control_flow_tac();
    test_short_circuit_tac();
    test_constant_analysis_overflow();
    test_integer_arithmetic_model();
    test_constant_analysis_error();
    test_loop_dominator_tree();
    test_while_loop_phi_ssa();
    test_if_else_phi_ssa();
    test_if_then_phi_uses_entry_local_ssa();
    test_guarded_environment_local_tac_ssa();
    test_multiple_guarded_environment_locals_ssa();
    test_conditional_local_assignment_with_entry_local_analysis();
    test_list_index_tac_ssa();
    test_list_index_in_arithmetic_tac_ssa();
    test_scatter_destructuring_tac_ssa();
    test_list_construction_and_splicing_tac_ssa();
    test_builtin_call_tac_ssa();
    test_pure_builtin_inlining_tac_ssa();
    test_property_read_and_write_tac_ssa();
    test_for_range_loop_tac_ssa();
    test_for_list_loop_tac_ssa();
    test_cond_expr_tac_ssa();
    test_break_and_continue_tac_ssa();
    test_labeled_break_nested_loops_tac_ssa();
    test_range_expr_and_assignment_tac_ssa();
    test_verb_call_tac_ssa();
    test_object_scalars_tac_ssa();
    test_float_scalars_tac_ssa();
    test_string_scalars_tac_ssa();
    test_catch_expr_tac_ssa();
    test_try_except_tac_ssa();
    test_try_finally_tac_ssa();
    test_cfg_critical_edge_splitting();
    test_if_else_ssa_destruction();
    test_loop_ssa_destruction();
    test_critical_edge_ssa_destruction();
    test_repeated_local_assignment_ssa();
    test_unsupported_tac();
    test_negative_tac_verifier_cases();
    test_negative_cfg_verifier_cases();
    test_negative_ssa_verifier_cases();

    return failures ? 1 : 0;
}
