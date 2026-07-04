#define HIR_TESTING 1

#include "hir.h"

#include "storage.h"

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

static Expr
int_expr(Num value, unsigned lineno)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = EXPR_VAR;
    expr.lineno = lineno;
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
    assign_stmt_node.next = &return_stmt_node;

    tac = lower_stmt(&names, &assign_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("arith const count", hir_tac_count_kind(tac, HIR_TAC_CONST), 3);
    check_int("arith load count", hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 1);
    check_int("arith store count", hir_tac_count_kind(tac, HIR_TAC_STORE_LOCAL), 1);
    check_int("arith return count", hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("arith add count", hir_tac_count_binary_op(tac, HIR_OP_ADD), 1);
    check_int("arith mul count", hir_tac_count_binary_op(tac, HIR_OP_MUL), 1);
    check_int("arith line 10 count", hir_tac_count_lineno(tac, 10), 4);
    check_int("arith line 11 count", hir_tac_count_lineno(tac, 11), 4);
    check_int("arith cfg blocks", hir_cfg_block_count(cfg), 1);
    check_int("arith cfg edges", hir_cfg_edge_count(cfg), 0);
    check_int("arith dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 1);
    check_int("arith dom entry idom", hir_dom_idom_block(dom, 1), 1);
    check_int("arith ssa blocks", hir_ssa_block_count(ssa), 1);
    check_int("arith ssa instructions", hir_ssa_instruction_count(ssa), 6);
    check_int("arith ssa values", hir_ssa_value_count(ssa), 5);
    check_int("arith ssa binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 2);
    check_int("arith verify errors", hir_context_error_count(ctx), 0);

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
    check_int("control line 20 count", hir_tac_count_lineno(tac, 20), 7);
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
    check_int("control ssa instructions", hir_ssa_instruction_count(ssa), 9);
    check_int("control ssa values", hir_ssa_value_count(ssa), 4);
    check_int("control ssa branch count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BRANCH_FALSE), 1);
    check_int("control verify errors", hir_context_error_count(ctx), 0);

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
    Expr list;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&list, 0, sizeof(list));
    list.kind = EXPR_LIST;
    list.lineno = 30;
    list.e.list = 0;
    ret = return_stmt(&list);

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
test_dominance_frontier_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;

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
    check_int("loop ssa instructions", hir_ssa_instruction_count(ssa), 11);
    check_int("loop ssa values", hir_ssa_value_count(ssa), 6);
    check_int("loop ssa phi count", hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);

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
	      hir_ssa_instruction_count(ssa), 7);
    check_int("repeat assign ssa values", hir_ssa_value_count(ssa), 6);
    check_int("repeat assign verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

int
main(void)
{
    test_arithmetic_and_local_tac();
    test_control_flow_tac();
    test_loop_dominator_tree();
    test_dominance_frontier_tac();
    test_repeated_local_assignment_ssa();
    test_unsupported_tac();
    test_negative_tac_verifier_cases();
    test_negative_cfg_verifier_cases();
    test_negative_ssa_verifier_cases();

    return failures ? 1 : 0;
}
