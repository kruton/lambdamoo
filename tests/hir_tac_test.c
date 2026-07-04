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
lower_stmt(Names *names, Stmt *stmt, HIRContext **ctx_out, HIRCFG **cfg_out)
{
    HIRContext *ctx = hir_context_new(names);
    HIRProgram *program = hir_lift_ast(ctx, stmt);
    HIRTacProgram *tac = hir_lower_to_tac(ctx, program);
    HIRCFG *cfg;

    (void) hir_verify_tac(ctx, tac);
    cfg = hir_build_cfg(ctx, tac);
    (void) hir_verify_cfg(ctx, cfg);
    *ctx_out = ctx;
    *cfg_out = cfg;

    return tac;
}

static void
test_arithmetic_and_local_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
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

    tac = lower_stmt(&names, &assign_stmt_node, &ctx, &cfg);

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
    check_int("arith verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_control_flow_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
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

    tac = lower_stmt(&names, &if_stmt_node, &ctx, &cfg);

    check_int("control branch count",
	      hir_tac_count_kind(tac, HIR_TAC_BRANCH_FALSE), 1);
    check_int("control jump count", hir_tac_count_kind(tac, HIR_TAC_JUMP), 1);
    check_int("control label count", hir_tac_count_kind(tac, HIR_TAC_LABEL), 2);
    check_int("control lt count", hir_tac_count_binary_op(tac, HIR_OP_LT), 1);
    check_int("control line 20 count", hir_tac_count_lineno(tac, 20), 7);
    check_int("control line 21 count", hir_tac_count_lineno(tac, 21), 2);
    check_int("control cfg blocks", hir_cfg_block_count(cfg), 5);
    check_int("control cfg edges", hir_cfg_edge_count(cfg), 4);
    check_int("control verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_unsupported_tac(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
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

    tac = lower_stmt(&names, &ret, &ctx, &cfg);

    check_int("unsupported tac count",
	      hir_tac_count_kind(tac, HIR_TAC_UNSUPPORTED), 1);
    check_int("unsupported return count", hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("unsupported line 30 count", hir_tac_count_lineno(tac, 30), 2);
    check_int("unsupported cfg blocks", hir_cfg_block_count(cfg), 1);
    check_int("unsupported cfg unsupported blocks",
	      hir_cfg_unsupported_block_count(cfg), 1);
    if (hir_context_error_count(ctx) == 0) {
	fprintf(stderr, "unsupported case should record HIR errors\n");
	failures++;
    }

    hir_context_free(ctx);
}

int
main(void)
{
    test_arithmetic_and_local_tac();
    test_control_flow_tac();
    test_unsupported_tac();

    return failures ? 1 : 0;
}
