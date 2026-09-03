#define HIR_TESTING 1

#include "hir.h"

#include "integer_arithmetic.h"
#include "opcode.h"
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

static void
test_ast_and_operation_tables(void)
{
    static const struct {
	var_type type;
	HIRTypeTag tag;
    } type_tags[] = {
	{TYPE_INT, HIR_TYPE_INT},
	{TYPE_FLOAT, HIR_TYPE_FLOAT},
	{TYPE_STR, HIR_TYPE_STR},
	{TYPE_LIST, HIR_TYPE_LIST},
	{TYPE_OBJ, HIR_TYPE_OBJ},
	{TYPE_ERR, HIR_TYPE_ERR},
	{TYPE_CLEAR, HIR_TYPE_ANY},
	{TYPE_NONE, HIR_TYPE_ANY},
	{TYPE_CATCH, HIR_TYPE_ANY},
	{TYPE_FINALLY, HIR_TYPE_ANY},
	{TYPE_WAIF, HIR_TYPE_ANY}
    };
    HIROp op;
    Num value;
    int binary_kinds = 0;
    int kind;
    unsigned i;

    for (i = 0; i < sizeof(type_tags) / sizeof(type_tags[0]); i++)
	check_int("MOO type maps to HIR tag",
	    hir_test_type_tag_for_var_type(type_tags[i].type),
	    type_tags[i].tag);

    for (kind = 0; kind < SizeOf_Expr_Kind; kind++) {
	check_int("known expression kind name",
	    !!strcmp(hir_test_expr_kind_name((enum Expr_Kind) kind), "unknown"),
	    1);
	if (hir_test_binary_op_for_expr((enum Expr_Kind) kind, &op))
	    binary_kinds++;
    }
    check_int("unknown expression kind name",
	      !strcmp(hir_test_expr_kind_name(SizeOf_Expr_Kind), "unknown"), 1);
    check_int("binary expression kind count", binary_kinds, 21);
    check_int("non-binary expression rejected",
	      hir_test_binary_op_for_expr(EXPR_VAR, &op), 0);

    for (kind = STMT_COND; kind <= STMT_CONTINUE; kind++)
	check_int("known statement kind name",
	    !!strcmp(hir_test_stmt_kind_name((enum Stmt_Kind) kind), "unknown"),
	    1);
    check_int("unknown statement kind name",
	      !strcmp(hir_test_stmt_kind_name((enum Stmt_Kind) -1), "unknown"), 1);

    for (kind = HIR_TAC_TICK; kind <= HIR_TAC_PARALLEL_COPY; kind++)
	check_int("known TAC kind name",
	    !!strcmp(hir_test_tac_kind_name((HIRTacKind) kind), "unknown"), 1);
    check_int("unknown TAC kind name",
	      !strcmp(hir_test_tac_kind_name((HIRTacKind) -1), "unknown"), 1);

    for (kind = HIR_OP_NEGATE; kind <= HIR_OP_ROTL32; kind++)
	check_int("known HIR operation name",
	    !!strcmp(hir_test_op_name((HIROp) kind), "?"), 1);
    check_int("unknown HIR operation name",
	      !strcmp(hir_test_op_name((HIROp) -1), "?"), 1);

    check_int("constant unary negate analysis",
	      hir_test_analyze_unary(HIR_OP_NEGATE, 7, &value),
	      HIR_VALUE_INT_CONSTANT);
    check_int("constant unary negate value", value, -7);
    hir_test_analyze_unary(HIR_OP_NOT, 7, &value);
    hir_test_analyze_unary(HIR_OP_COMPLEMENT, 7, &value);
    hir_test_analyze_unary(HIR_OP_ABS, -7, &value);
    hir_test_analyze_unary(HIR_OP_ABS, 7, &value);
    hir_test_analyze_unary(HIR_OP_TOINT, 7, &value);
    hir_test_analyze_unary(HIR_OP_TYPEOF, 7, &value);
    hir_test_analyze_unary(HIR_OP_LENGTH, 7, &value);
    hir_test_analyze_unary(HIR_OP_MAKE_SINGLETON_LIST, 7, &value);
    hir_test_analyze_unary(HIR_OP_CHECK_LIST_FOR_SPLICE, 7, &value);
    hir_test_analyze_unary(HIR_OP_ROTL32, 7, &value);

    for (kind = HIR_OP_NEGATE; kind <= HIR_OP_ROTL32; kind++)
	hir_test_analyze_binary((HIROp) kind, 7, 2, &value);
    check_int("binary analysis handles nonconstant lattice inputs",
	      hir_test_analyze_binary_nonconstant_cases(), 4);
    check_int("value-fact joins cover lattice combinations",
	      hir_test_join_value_fact_cases(), 9);
    check_int("rotate matcher rejects malformed SSA shapes",
	      hir_test_match_rotate32_and_cases(), 13);
    check_int("SSA use replacement covers all operand homes",
	      hir_test_replace_ssa_value_uses(), 12);
    check_int("SSA local versioning covers implicit definitions",
	      hir_test_current_version_cases(), 12);
#ifdef HIR_DUMP_SSA
    check_int("SSA dumping covers sparse and parallel-copy forms",
	      hir_test_dump_ssa_cases(), 1);
#endif
    check_int("SSA inspection handles absent and out-of-range values",
	      hir_test_inspection_edge_cases(), 22);
}

static void
test_optimized_bytecode_shapes(void)
{
    static const struct {
	HIROp op;
	Byte opcode;
	Byte extended_opcode;
    } binary_cases[] = {
	{HIR_OP_ADD, OP_ADD, 0},
	{HIR_OP_SUB, OP_MINUS, 0},
	{HIR_OP_MUL, OP_MULT, 0},
	{HIR_OP_DIV, OP_DIV, 0},
	{HIR_OP_MOD, OP_MOD, 0},
	{HIR_OP_EQ, OP_EQ, 0},
	{HIR_OP_NE, OP_NE, 0},
	{HIR_OP_LT, OP_LT, 0},
	{HIR_OP_LE, OP_LE, 0},
	{HIR_OP_GT, OP_GT, 0},
	{HIR_OP_GE, OP_GE, 0},
	{HIR_OP_EXP, OP_EXTENDED, EOP_EXP},
	{HIR_OP_BITOR, OP_EXTENDED, EOP_BITOR},
	{HIR_OP_BITXOR, OP_EXTENDED, EOP_BITXOR},
	{HIR_OP_BITAND, OP_EXTENDED, EOP_BITAND},
	{HIR_OP_SHL, OP_EXTENDED, EOP_SHL},
	{HIR_OP_SHR, OP_EXTENDED, EOP_SHR},
	{HIR_OP_LSHR, OP_EXTENDED, EOP_LSHR},
	{HIR_OP_ROTL32, OP_EXTENDED, EOP_LSHR}
    };
    Byte pop_count;
    Byte skip_count;
    unsigned i;

    check_int("unary negate bytecode shape",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_NEGATE,
	    OP_UNARY_MINUS, 0, 0, &pop_count, &skip_count), 1);
    check_int("unary negate pop count", pop_count, 1);
    check_int("unary negate skip count", skip_count, 0);
    check_int("unary not bytecode shape",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_NOT,
	    OP_NOT, 0, 0, &pop_count, &skip_count), 1);
    check_int("unary complement bytecode shape",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_COMPLEMENT,
	    OP_EXTENDED, EOP_COMPLEMENT, 1, &pop_count, &skip_count), 1);
    check_int("unary complement skip count", skip_count, 1);
    check_int("truncated unary complement rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_COMPLEMENT,
	    OP_EXTENDED, EOP_COMPLEMENT, 0, &pop_count, &skip_count), 0);
    check_int("wrong unary complement opcode rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_COMPLEMENT,
	    OP_NOT, EOP_COMPLEMENT, 1, &pop_count, &skip_count), 0);
    check_int("wrong extended complement rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_COMPLEMENT,
	    OP_EXTENDED, EOP_BITOR, 1, &pop_count, &skip_count), 0);
    check_int("wrong unary opcode rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_NEGATE,
	    OP_NOT, 0, 0, &pop_count, &skip_count), 0);
    check_int("unknown unary operation rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_UNARY, HIR_OP_ADD,
	    OP_ADD, 0, 0, &pop_count, &skip_count), 0);

    for (i = 0; i < sizeof(binary_cases) / sizeof(binary_cases[0]); i++) {
	int extended = binary_cases[i].opcode == OP_EXTENDED;

	check_int("binary bytecode shape",
	    hir_test_optimized_bytecode_shape(HIR_TAC_BINARY,
		binary_cases[i].op, binary_cases[i].opcode,
		binary_cases[i].extended_opcode, extended, &pop_count,
		&skip_count), 1);
	check_int("binary bytecode pop count", pop_count, 2);
	check_int("binary bytecode skip count", skip_count, extended);
	check_int("wrong binary opcode rejected",
	    hir_test_optimized_bytecode_shape(HIR_TAC_BINARY,
		binary_cases[i].op, OP_RETURN,
		binary_cases[i].extended_opcode, extended, &pop_count,
		&skip_count), 0);
	if (extended)
	    check_int("wrong extended binary opcode rejected",
		hir_test_optimized_bytecode_shape(HIR_TAC_BINARY,
		    binary_cases[i].op, OP_EXTENDED, EOP_COMPLEMENT, 1,
		    &pop_count, &skip_count), 0);
    }
    check_int("wrong binary opcode rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_BINARY, HIR_OP_ADD,
	    OP_MINUS, 0, 0, &pop_count, &skip_count), 0);
    check_int("truncated extended binary rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_BINARY, HIR_OP_EXP,
	    OP_EXTENDED, EOP_EXP, 0, &pop_count, &skip_count), 0);
    check_int("wrong extended binary rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_BINARY, HIR_OP_BITOR,
	    OP_EXTENDED, EOP_BITXOR, 1, &pop_count, &skip_count), 0);
    check_int("truncated bitwise binary rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_BINARY, HIR_OP_BITOR,
	    OP_EXTENDED, EOP_BITOR, 0, &pop_count, &skip_count), 0);
    check_int("unknown binary operation rejected",
	hir_test_optimized_bytecode_shape(HIR_TAC_BINARY, HIR_OP_FORK,
	    OP_EXTENDED, 0, 1, &pop_count, &skip_count), 0);
    check_int("optimized bytecode lowering covers edge cases",
	hir_test_optimized_bytecode_lowering_cases(), 11);
}

static void
test_null_analysis_accessors(void)
{
    Names names;
    HIRContext *ctx;
    HIRTacProgram *empty_tac;
    HIRCFG *empty_cfg;
    HIRDominatorTree *empty_dom;
    HIRSSAProgram *empty_ssa;

    memset(&names, 0, sizeof(names));
    ctx = hir_context_new(&names);

    check_int("null TAC verifier context", hir_verify_tac(0, 0), 0);
    check_int("null TAC verifier program", hir_verify_tac(ctx, 0), 0);
    check_int("null CFG builder context", hir_build_cfg(0, 0) == 0, 1);
    check_int("null CFG builder program", hir_build_cfg(ctx, 0) == 0, 1);
    check_int("null CFG verifier context", hir_verify_cfg(0, 0), 0);
    check_int("null CFG verifier graph", hir_verify_cfg(ctx, 0), 0);
    check_int("null dominator builder context",
	      hir_build_dominator_tree(0, 0) == 0, 1);
    check_int("null dominator builder graph",
	      hir_build_dominator_tree(ctx, 0) == 0, 1);
    check_int("null dominator verifier context",
	      hir_verify_dominator_tree(0, 0, 0), 0);
    check_int("null dominator verifier graph",
	      hir_verify_dominator_tree(ctx, 0, 0), 0);
    check_int("null SSA builder context", hir_build_ssa(0, 0) == 0, 1);
    check_int("null SSA builder graph", hir_build_ssa(ctx, 0) == 0, 1);
    check_int("null SSA verifier context", hir_verify_ssa(0, 0), 0);
    check_int("null SSA verifier program", hir_verify_ssa(ctx, 0), 0);
    check_int("null SSA analyzer context",
	      hir_analyze_ssa_values(0, 0) == 0, 1);
    check_int("null SSA analyzer program",
	      hir_analyze_ssa_values(ctx, 0) == 0, 1);
    check_int("null SSA optimizer context",
	      hir_optimize_ssa_for_backends(0, 0) == 0, 1);
    check_int("null SSA optimizer program",
	      hir_optimize_ssa_for_backends(ctx, 0) == 0, 1);
    check_int("null SSA destroy context", hir_destroy_ssa(0, 0), 0);
    check_int("null SSA destroy program", hir_destroy_ssa(ctx, 0), 0);
    check_int("null out-of-SSA verifier context",
	      hir_verify_out_of_ssa(0, 0), 0);
    check_int("null out-of-SSA verifier program",
	      hir_verify_out_of_ssa(ctx, 0), 0);

    check_int("null context error count", hir_context_error_count(0), 0);
    check_int("null context error message", hir_context_error_message(0) == 0,
	      1);
    check_int("null value kind", hir_value_kind(0, 1), HIR_VALUE_UNKNOWN);
    check_int("null value constant", hir_value_constant(0, 1), 0);
    check_int("null value error", hir_value_error(0, 1), E_NONE);
    check_int("null optimization count", hir_optimization_change_count(0), 0);
    hir_context_set_first_user_local(0, 0);
    hir_context_set_first_user_local(ctx, -1);
    hir_context_set_first_user_local(ctx, 1);

    check_int("null TAC kind count", hir_tac_count_kind(0, HIR_TAC_CONST), 0);
    check_int("null TAC unary count",
	      hir_tac_count_unary_op(0, HIR_OP_NEGATE), 0);
    check_int("null TAC binary count",
	      hir_tac_count_binary_op(0, HIR_OP_ADD), 0);
    check_int("null TAC instruction count", hir_tac_instruction_count(0), 0);
    check_int("null TAC line count", hir_tac_count_lineno(0, 1), 0);
    check_int("null TAC pc count", hir_tac_count_bytecode_pc(0, 1), 0);
    check_int("null TAC stack depth",
	      hir_tac_stack_depth_at_bytecode_pc(0, 1), -1);
    check_int("null TAC stack mismatch count",
	      hir_tac_stack_depth_mismatch_count(0, 1, 0), 0);

    check_int("null CFG block count", hir_cfg_block_count(0), 0);
    check_int("null CFG edge count", hir_cfg_edge_count(0), 0);
    check_int("null CFG unsupported count",
	      hir_cfg_unsupported_block_count(0), 0);
    check_int("null CFG critical edge count",
	      hir_cfg_critical_edge_count(0), 0);
    check_int("null critical-edge split context",
	      hir_split_critical_edges(0, 0), 0);
    check_int("null critical-edge split graph",
	      hir_split_critical_edges(ctx, 0), 0);
    check_int("null dominator reachable count",
	      hir_dom_reachable_block_count(0), 0);
    check_int("null immediate dominator", hir_dom_idom_block(0, 1), 0);
    check_int("null dominance frontier count", hir_dom_df_count(0, 1), 0);

    check_int("null SSA block count", hir_ssa_block_count(0), 0);
    check_int("null SSA instruction count", hir_ssa_instruction_count(0), 0);
    check_int("null SSA value count", hir_ssa_value_count(0), 0);
    check_int("null SSA kind count", hir_ssa_count_kind(0, HIR_TAC_CONST), 0);
    check_int("null SSA invalid-load count",
	      hir_ssa_out_of_range_load_count(0, 0), 0);
    check_int("null SSA pc count", hir_ssa_count_bytecode_pc(0, 1), 0);
    check_int("null SSA stack depth",
	      hir_ssa_stack_depth_at_bytecode_pc(0, 1), -1);
    check_int("null SSA stack value",
	      hir_ssa_stack_value_at_bytecode_pc(0, 1, 0), -1);
    check_int("null SSA binary value",
	      hir_ssa_binary_value_at_bytecode_pc(0, 1, HIR_OP_ADD), -1);
    check_int("null SSA local value",
	      hir_ssa_local_value_at_bytecode_pc(0, 1, 0), -1);
    check_int("null SSA local snapshots", hir_ssa_local_snapshot_count(0), 0);
    check_int("null SSA phi arguments", hir_ssa_phi_arg_count(0), 0);
    check_int("null SSA empty phi arguments", hir_ssa_zero_phi_arg_count(0), 0);
    check_int("null SSA return phi uses", hir_ssa_return_uses_phi_count(0), 0);
    check_int("null SSA branch phi uses", hir_ssa_branch_uses_phi_count(0), 0);
    check_int("null SSA binary phi uses",
	      hir_ssa_binary_uses_phi_count(0, HIR_OP_ADD), 0);
    check_int("null SSA parallel copies",
	      hir_ssa_parallel_copy_pair_count(0), 0);
    check_int("null SSA form", hir_ssa_form(0), -1);
    check_int("null SSA CFG block count", hir_ssa_cfg_block_count(0), 0);
    check_int("null SSA CFG edge count", hir_ssa_cfg_edge_count(0), 0);
    check_int("null SSA CFG critical edge count",
	      hir_ssa_cfg_critical_edge_count(0), 0);

    empty_tac = hir_lower_to_tac(ctx, 0);
    check_int("empty TAC verifies", hir_verify_tac(ctx, empty_tac), 1);
    check_int("empty TAC has no instructions",
	      hir_tac_instruction_count(empty_tac), 0);
    empty_cfg = hir_build_cfg(ctx, empty_tac);
    check_int("empty CFG has no blocks", hir_cfg_block_count(empty_cfg), 0);
    check_int("empty CFG verifies", hir_verify_cfg(ctx, empty_cfg), 1);
    empty_dom = hir_build_dominator_tree(ctx, empty_cfg);
    check_int("empty dominator tree has no reachable blocks",
	      hir_dom_reachable_block_count(empty_dom), 0);
    check_int("empty dominator tree verifies",
	      hir_verify_dominator_tree(ctx, empty_cfg, empty_dom), 1);
    empty_ssa = hir_build_ssa(ctx, empty_cfg);
    check_int("empty SSA has no blocks", hir_ssa_block_count(empty_ssa), 0);
    check_int("empty SSA verifies", hir_verify_ssa(ctx, empty_ssa), 1);

    hir_context_free(ctx);
    hir_context_free(0);
}

static void
test_resume_stack_safety(void)
{
    var_type plain[] = {TYPE_INT, TYPE_STR, TYPE_LIST};
    var_type caught[] = {TYPE_INT, TYPE_CATCH, TYPE_STR};
    var_type finalizing[] = {TYPE_FINALLY, TYPE_INT, TYPE_STR};

    check_int("plain resume stack accepted",
	      hir_test_resume_stack_is_safe(plain, 3, 1), 1);
    check_int("call operands may contain catch values",
	      hir_test_resume_stack_is_safe(caught, 3, 2), 1);
    check_int("catch marker in outer stack rejected",
	      hir_test_resume_stack_is_safe(caught, 3, 1), 0);
    check_int("finally marker in outer stack rejected",
	      hir_test_resume_stack_is_safe(finalizing, 3, 1), 0);
    check_int("insufficient resume stack rejected",
	      hir_test_resume_stack_is_safe(plain, 1, 2), 0);
}

static void
test_resume_stack_shape(void)
{
    ResumeStackSlot point_slots[2];
    ResumeStackSlot boundary_slots[3];
    ResumePoint point;

    memset(&point, 0, sizeof(point));
    memset(point_slots, 0, sizeof(point_slots));
    memset(boundary_slots, 0, sizeof(boundary_slots));
    check_int("missing resume point rejected",
	      hir_test_resume_stack_matches_point(0, 0, 0, 0), 0);
    point.stack_depth = 2;
    point.stack_slots = point_slots;
    point_slots[0].kind = RSS_FINALLY;
    point_slots[0].data = 41;
    point_slots[1].kind = RSS_VALUE;
    boundary_slots[0] = point_slots[0];
    boundary_slots[1] = point_slots[1];
    boundary_slots[2].kind = RSS_VALUE;

    check_int("canonical resume stack accepted",
	      hir_test_resume_stack_matches_point(boundary_slots, 3,
					  &point, 1), 1);
    check_int("wrong resume stack depth rejected",
	      hir_test_resume_stack_matches_point(boundary_slots, 2,
					  &point, 1), 0);
    check_int("negative call operand count rejected",
	      hir_test_resume_stack_matches_point(boundary_slots, 3,
					  &point, -1), 0);
    check_int("short operand stack rejected",
	      hir_test_resume_stack_matches_point(boundary_slots, 0,
					  &point, 1), 0);
    check_int("missing boundary slots rejected",
	      hir_test_resume_stack_matches_point(0, 3, &point, 1), 0);
    point.stack_slots = 0;
    check_int("missing point slots rejected",
	      hir_test_resume_stack_matches_point(boundary_slots, 3,
					  &point, 1), 0);
    point.stack_slots = point_slots;
    boundary_slots[0].kind = RSS_VALUE;
    check_int("wrong resume stack marker rejected",
	      hir_test_resume_stack_matches_point(boundary_slots, 3,
					  &point, 1), 0);
    boundary_slots[0].kind = RSS_FINALLY;
    boundary_slots[0].data++;
    check_int("wrong resume stack marker data rejected",
	      hir_test_resume_stack_matches_point(boundary_slots, 3,
					  &point, 1), 0);
}

static void
test_boundary_tick_refunds(void)
{
	check_int("arithmetic boundary refunds tick",
		  hir_test_boundary_ticks_charged(HIR_TAC_BINARY, HIR_OP_ADD), 1);
	check_int("property write boundary refunds tick",
		  hir_test_boundary_ticks_charged(HIR_TAC_PUT_PROP,
					  HIR_OP_GET_PROP), 1);
	check_int("range boundary refunds tick",
		  hir_test_boundary_ticks_charged(HIR_TAC_RANGE_SET,
					  HIR_OP_INDEX), 1);
	check_int("native index-store boundary refunds tick",
		  hir_test_boundary_ticks_charged(HIR_TAC_INDEX_SET,
					  HIR_OP_INDEX), 1);
	check_int("scatter boundary refunds tick",
		  hir_test_boundary_ticks_charged(HIR_TAC_DEOPT,
					  HIR_OP_SCATTER), 1);
	check_int("index-store boundary has no tick to refund",
		  hir_test_boundary_ticks_charged(HIR_TAC_DEOPT,
					  HIR_OP_INDEX), 0);
	check_int("batched deopt refunds current and future ticks",
		  hir_test_tick_batch_deopt_ticks_charged(1, 3), 4);
	check_int("batched deopt without current tick refunds future ticks",
		  hir_test_tick_batch_deopt_ticks_charged(0, 3), 3);
}

static void
test_list_tail_ownership_slots(void)
{
    check_int("last-use list tail reuses ownership slot",
	      hir_test_list_tail_owner_slot(3, 1, 7), 3);
    check_int("shared list tail gets new ownership slot",
	      hir_test_list_tail_owner_slot(3, 2, 7), 7);
    check_int("unowned list tail gets new ownership slot",
	      hir_test_list_tail_owner_slot(-1, 1, 7), 7);
    check_int("integer tail preserves integer-list proof",
	      hir_test_int_list_result(HIR_OP_LIST_ADD_TAIL, 1, 0,
				       TYPE_INT), 1);
    check_int("mixed tail rejects integer-list proof",
	      hir_test_int_list_result(HIR_OP_LIST_ADD_TAIL, 1, 0,
				       TYPE_STR), 0);
    check_int("integer-list append preserves proof",
	      hir_test_int_list_result(HIR_OP_LIST_APPEND, 1, 1,
				       TYPE_LIST), 1);
    check_int("unknown append rejects integer-list proof",
	      hir_test_int_list_result(HIR_OP_LIST_APPEND, 1, 0,
				       TYPE_LIST), 0);
    check_int("all integer-list phi inputs preserve proof",
	      hir_test_all_copy_sources_are_int_lists(2, 2), 1);
    check_int("mixed phi inputs reject integer-list proof",
	      hir_test_all_copy_sources_are_int_lists(2, 1), 0);
    check_int("missing phi inputs reject integer-list proof",
	      hir_test_all_copy_sources_are_int_lists(0, 0), 0);
    check_int("one local permits direct integer-list update",
	      hir_test_int_list_has_exclusive_local(1), 1);
    check_int("no local rejects direct integer-list update",
	      hir_test_int_list_has_exclusive_local(0), 0);
    check_int("aliased locals reject direct integer-list update",
	      hir_test_int_list_has_exclusive_local(2), 0);
}

static void
test_string_concat_ownership_slots(void)
{
    check_int("string concat reuses last left ownership slot",
	      hir_test_string_concat_owner_slot(3, 1, 4, 0, 7), 3);
    check_int("string concat reuses last right ownership slot",
	      hir_test_string_concat_owner_slot(3, 0, 4, 1, 7), 4);
    check_int("string concat prefers last left ownership slot",
	      hir_test_string_concat_owner_slot(3, 1, 4, 1, 7), 3);
    check_int("string concat allocates for an unowned last value",
	      hir_test_string_concat_owner_slot(-1, 1, -1, 0, 7), 7);
    check_int("string concat does not consume a live owner",
	      hir_test_string_concat_owner_slot(3, 0, 4, 0, 7), 7);
}

static void
test_string_builtin_length_anchor(void)
{
    Byte vector[] = {OP_BI_FUNC_CALL, 6};
    Bytecodes bytecodes;

    memset(&bytecodes, 0, sizeof(bytecodes));
    bytecodes.vector = vector;
    bytecodes.size = sizeof(vector);
    check_int("string length built-in anchor",
	      hir_test_string_builtin_length_anchor(&bytecodes, 0, 6,
						    HIR_OP_LENGTH), 1);
    vector[1] = 1;
    check_int("other built-in rejected as string length",
	      hir_test_string_builtin_length_anchor(&bytecodes, 0, 1,
						    HIR_OP_LENGTH), 0);
    check_int("mismatched encoded built-in rejected as string length",
	      hir_test_string_builtin_length_anchor(&bytecodes, 0, 6,
						    HIR_OP_LENGTH), 0);
    vector[1] = 6;
    check_int("non-length operation rejected at length built-in",
	      hir_test_string_builtin_length_anchor(&bytecodes, 0, 6,
						    HIR_OP_ABS), 0);
    check_int("truncated built-in rejected as string length",
	      hir_test_string_builtin_length_anchor(&bytecodes, 1, 6,
						    HIR_OP_LENGTH), 0);
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

static Expr
unary_expr(enum Expr_Kind kind, Expr *operand)
{
    Expr expr;

    memset(&expr, 0, sizeof(expr));
    expr.kind = kind;
    expr.lineno = operand ? operand->lineno : 0;
    expr.bytecode_pc = NO_BYTECODE_PC;
    expr.e.expr = operand;
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
#ifdef HIR_DUMP_SSA
    check_ssa_dump_contains("lowered SSA dump", ssa, "HIR SSA END");
#endif
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
    HIROptimizationPlan *optimization_plan;
    HIRTacProgram *tac;
    OptimizedBytecode *optimized;
    Program bytecode_program;
    Byte vector[11];
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
    memset(&bytecode_program, 0, sizeof(bytecode_program));
    memset(vector, OP_DONE, sizeof(vector));
    vector[5] = OP_ADD;
    vector[9] = OP_MULT;
    bytecode_program.main_vector.vector = vector;
    bytecode_program.main_vector.size = sizeof(vector);
    optimization_plan = hir_optimize_ssa_for_backends(ctx, ssa);
    check_int("arith constant optimization changed",
	      hir_optimization_change_count(optimization_plan), 2);
    optimized = hir_lower_optimized_bytecode(ctx, optimization_plan,
					      &bytecode_program);
    check_int("arith optimized bytecode produced", optimized != 0, 1);
    check_int("arith optimized bytecode replacement count",
	      optimized ? (int) optimized->num_replacements : 0, 2);
    check_int("arith add lowered to optimized bytecode",
	      optimized ? optimized->main_vector.vector[5] : 0,
	      OP_OPTIMIZED_VALUE);
    check_int("arith multiply lowered to optimized bytecode",
	      optimized ? optimized->main_vector.vector[9] : 0,
	      OP_OPTIMIZED_VALUE);
    check_int("arith optimized add value",
	      optimized ? (int) optimized->replacements[0].value : 0, 3);
    check_int("arith optimized multiply value",
	      optimized ? (int) optimized->replacements[1].value : 0, 9);
    check_int("arith optimized binary count",
	      hir_ssa_count_kind(ssa, HIR_TAC_BINARY), 0);
    check_int("arith optimized verify", hir_verify_ssa(ctx, ssa), 1);

    if (optimized) {
	myfree(optimized->main_vector.vector, M_BYTECODES);
	myfree(optimized->replacements, M_PROGRAM);
	myfree(optimized, M_PROGRAM);
    }

    hir_context_free(ctx);
}

static void
test_unary_and_empty_list_tac(void)
{
    static const struct {
	enum Expr_Kind kind;
	HIROp op;
    } cases[] = {
	{EXPR_NEGATE, HIR_OP_NEGATE},
	{EXPR_NOT, HIR_OP_NOT},
	{EXPR_COMPLEMENT, HIR_OP_COMPLEMENT}
    };
    Names names;
    unsigned i;

    memset(&names, 0, sizeof(names));
    names.size = 2;
    for (i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
	HIRContext *ctx;
	HIRCFG *cfg;
	HIRDominatorTree *dom;
	HIRSSAProgram *ssa;
	Expr value = int_expr(7, 12);
	Expr unary = unary_expr(cases[i].kind, &value);
	Stmt ret = return_stmt(&unary);
	HIRTacProgram *tac;

	unary.bytecode_pc = 2;
	tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
	check_int("unary expression lowered",
	    hir_tac_count_unary_op(tac, cases[i].op), 1);
	check_int("unary expression verifies", hir_context_error_count(ctx), 0);
	hir_context_free(ctx);
    }
    {
	HIRContext *ctx;
	HIRCFG *cfg;
	HIRDominatorTree *dom;
	HIRSSAProgram *ssa;
	Expr empty;
	Stmt ret;
	HIRTacProgram *tac;

	memset(&empty, 0, sizeof(empty));
	empty.kind = EXPR_LIST;
	empty.lineno = 13;
	empty.bytecode_pc = 1;
	ret = return_stmt(&empty);
	tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
	check_int("empty list lowered as a constant",
	    hir_tac_count_kind(tac, HIR_TAC_CONST), 1);
	check_int("empty list verifies", hir_context_error_count(ctx), 0);
	hir_context_free(ctx);
    }
}

static void
test_empty_and_discarded_statements(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr literal = int_expr(1, 13);
    Expr local = id_expr(0, 13);
    Stmt literal_stmt = expr_stmt(&literal);
    Stmt local_stmt = expr_stmt(&local);
    Stmt empty_expr_stmt = expr_stmt(0);
    Stmt empty_return = return_stmt(0);

    memset(&names, 0, sizeof(names));
    names.size = 2;
    literal_stmt.next = &local_stmt;
    local_stmt.next = &empty_expr_stmt;
    empty_expr_stmt.next = &empty_return;
    tac = lower_stmt(&names, &literal_stmt, &ctx, &cfg, &dom, &ssa);
    check_int("discarded trivial expressions emit no values",
	      hir_tac_count_kind(tac, HIR_TAC_CONST)
	      + hir_tac_count_kind(tac, HIR_TAC_LOAD_LOCAL), 0);
    check_int("empty return lowers directly",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN0), 1);
    check_int("empty and discarded statements verify",
	      hir_context_error_count(ctx), 0);
    hir_context_free(ctx);
}

static void
check_inline_builtin(unsigned func, HIROp op, int argc)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr first = int_expr(7, 14);
    Expr second = int_expr(9, 14);
    Expr call;
    Arg_List args[2];
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 2;
    memset(args, 0, sizeof(args));
    args[0].kind = args[1].kind = ARG_NORMAL;
    args[0].expr = &first;
    args[1].expr = &second;
    args[0].next = argc == 2 ? &args[1] : 0;
    memset(&call, 0, sizeof(call));
    call.kind = EXPR_CALL;
    call.lineno = 14;
    call.bytecode_pc = 3;
    call.e.call.func = func;
    call.e.call.args = argc ? &args[0] : 0;
    ret = return_stmt(&call);

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("pure builtin lowered inline",
	      hir_tac_count_unary_op(tac, op)
	      + hir_tac_count_binary_op(tac, op), 1);
    check_int("pure builtin omitted generic call",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 0);
    check_int("pure builtin verifies", hir_context_error_count(ctx), 0);
    hir_context_free(ctx);
}

static void
check_builtin_not_inlined(unsigned func, HIROp op, int argc,
			  enum Arg_Kind first_kind, enum Arg_Kind second_kind)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr values[3];
    Expr call;
    Arg_List args[3];
    Stmt ret;
    int i;

    memset(&names, 0, sizeof(names));
    names.size = 2;
    memset(args, 0, sizeof(args));
    for (i = 0; i < 3; i++) {
	values[i] = int_expr(i + 1, 15);
	args[i].kind = ARG_NORMAL;
	args[i].expr = &values[i];
	args[i].next = i + 1 < argc ? &args[i + 1] : 0;
    }
    args[0].kind = first_kind;
    args[1].kind = second_kind;
    memset(&call, 0, sizeof(call));
    call.kind = EXPR_CALL;
    call.lineno = 15;
    call.e.call.func = func;
    call.e.call.args = argc ? &args[0] : 0;
    ret = return_stmt(&call);
    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("malformed pure builtin uses generic call",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 1);
    check_int("malformed pure builtin is not inlined",
	      hir_tac_count_unary_op(tac, op)
	      + hir_tac_count_binary_op(tac, op), 0);
    check_int("malformed pure builtin verifies",
	      hir_context_error_count(ctx), 0);
    hir_context_free(ctx);
}

static void
test_pure_builtin_inlining_matrix(void)
{
    check_inline_builtin(1, HIR_OP_TOINT, 1);
    check_inline_builtin(2, HIR_OP_TYPEOF, 1);
    check_inline_builtin(5, HIR_OP_MAX, 2);
    check_inline_builtin(6, HIR_OP_LENGTH, 1);
    check_inline_builtin(12, HIR_OP_TICKS_LEFT, 0);
    check_inline_builtin(13, HIR_OP_SECONDS_LEFT, 0);
    check_inline_builtin(14, HIR_OP_VALID, 1);
    check_inline_builtin(15, HIR_OP_PARENT, 1);
    check_builtin_not_inlined(12, HIR_OP_TICKS_LEFT, 1, ARG_NORMAL,
	ARG_NORMAL);
    check_builtin_not_inlined(1, HIR_OP_TOINT, 0, ARG_NORMAL, ARG_NORMAL);
    check_builtin_not_inlined(1, HIR_OP_TOINT, 1, ARG_SPLICE, ARG_NORMAL);
    check_builtin_not_inlined(4, HIR_OP_MIN, 1, ARG_NORMAL, ARG_NORMAL);
    check_builtin_not_inlined(4, HIR_OP_MIN, 2, ARG_SPLICE, ARG_NORMAL);
    check_builtin_not_inlined(4, HIR_OP_MIN, 2, ARG_NORMAL, ARG_SPLICE);
    check_builtin_not_inlined(4, HIR_OP_MIN, 3, ARG_NORMAL, ARG_NORMAL);
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
    check_int("control cfg blocks", hir_cfg_block_count(cfg), 4);
    check_int("control cfg edges", hir_cfg_edge_count(cfg), 3);
    check_int("control dom reachable blocks",
	      hir_dom_reachable_block_count(dom), 4);
    check_int("control dom entry idom", hir_dom_idom_block(dom, 1), 1);
    check_int("control dom then idom", hir_dom_idom_block(dom, 2), 1);
    check_int("control dom unreachable idom", hir_dom_idom_block(dom, 3), 0);
    check_int("control dom else-label idom", hir_dom_idom_block(dom, 4), 1);
    check_int("control dom done idom", hir_dom_idom_block(dom, 5), 4);
    check_int("control ssa blocks", hir_ssa_block_count(ssa), 4);
    check_int("control ssa instructions", hir_ssa_instruction_count(ssa), 10);
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
    check_int("and internal locals are not environment loads",
	      hir_ssa_out_of_range_load_count(ssa, names.size), 0);
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
    check_int("or internal locals are not environment loads",
	      hir_ssa_out_of_range_load_count(ssa, names.size), 0);
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
test_negative_tac_verifier_matrix(void)
{
    Names names;
    int corruption;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    for (corruption = 0; corruption <= HIR_TEST_TAC_CORRUPTION_COUNT;
	 corruption++) {
	HIRContext *ctx = hir_context_new(&names);
	HIRTacProgram *tac = hir_test_corrupt_tac(ctx,
	    (HIRTestTacCorruption) corruption);
	int before = hir_context_error_count(ctx);
	int accepted = hir_verify_tac(ctx, tac);

	if (corruption == HIR_TEST_TAC_CORRUPTION_COUNT)
	    check_int("valid TAC verifier edge case", accepted, 1);
	else
	    check_rejected("negative TAC verifier matrix", accepted, before,
		 hir_context_error_count(ctx));
	hir_context_free(ctx);
    }
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
test_negative_cfg_verifier_matrix(void)
{
    Names names;
    int corruption;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    for (corruption = 0; corruption <= HIR_TEST_CFG_CORRUPTION_COUNT;
	 corruption++) {
	HIRContext *ctx = hir_context_new(&names);
	HIRCFG *cfg = hir_test_corrupt_cfg(ctx,
	    (HIRTestCFGCorruption) corruption);
	int before = hir_context_error_count(ctx);
	int accepted = hir_verify_cfg(ctx, cfg);

	if (corruption == HIR_TEST_CFG_ZERO_BLOCKS
	    || corruption == HIR_TEST_CFG_CORRUPTION_COUNT)
	    check_int("valid CFG verifier edge case", accepted, 1);
	else
	    check_rejected("negative CFG verifier matrix", accepted, before,
		hir_context_error_count(ctx));
	hir_context_free(ctx);
    }
}

static void
test_negative_dominator_verifier_cases(void)
{
    Names names;
    int corruption;

    memset(&names, 0, sizeof(names));
    names.size = 2;
    for (corruption = HIR_TEST_DOM_NO_REACHABLE;
	 corruption <= HIR_TEST_DOM_SELF_IDOM; corruption++) {
	HIRContext *ctx;
	HIRCFG *cfg;
	HIRDominatorTree *dom;
	HIRSSAProgram *ssa;
	Expr condition = id_expr(0, 20);
	Expr value = int_expr(1, 21);
	Stmt body = expr_stmt(&value);
	Stmt loop;
	int before;
	int accepted;

	memset(&loop, 0, sizeof(loop));
	loop.kind = STMT_WHILE;
	loop.lineno = 20;
	loop.s.loop.id = -1;
	loop.s.loop.condition = &condition;
	loop.s.loop.body = &body;
	(void) lower_stmt(&names, &loop, &ctx, &cfg, &dom, &ssa);
	check_int("dominator corruption fixture has multiple blocks",
	    hir_dom_reachable_block_count(dom) > 1, 1);
	before = hir_context_error_count(ctx);
	accepted = hir_test_verify_corrupt_dominator(ctx, cfg, dom,
	    (HIRTestDominatorCorruption) corruption);
	check_rejected("negative dominator verifier", accepted, before,
	    hir_context_error_count(ctx));
	hir_context_free(ctx);
    }
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

static void
test_negative_ssa_verifier_matrix(void)
{
    Names names;
    int corruption;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    for (corruption = 0; corruption <= HIR_TEST_SSA_CORRUPTION_COUNT;
	 corruption++) {
	HIRContext *ctx = hir_context_new(&names);
	HIRSSAProgram *ssa = hir_test_corrupt_ssa(ctx,
	    (HIRTestSSACorruption) corruption);
	int before = hir_context_error_count(ctx);
	int accepted = hir_verify_ssa(ctx, ssa);

	if (corruption == HIR_TEST_SSA_CORRUPTION_COUNT)
	    check_int("valid SSA verifier edge case", accepted, 1);
	else
	    check_rejected("negative SSA verifier matrix", accepted, before,
		hir_context_error_count(ctx));
	hir_context_free(ctx);
    }
}

static void
test_negative_out_ssa_verifier_matrix(void)
{
    Names names;
    int corruption;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    for (corruption = 0;
	 corruption <= HIR_TEST_OUT_SSA_CORRUPTION_COUNT; corruption++) {
	HIRContext *ctx = hir_context_new(&names);
	HIRSSAProgram *ssa = hir_test_corrupt_out_ssa(ctx,
	    (HIRTestOutSSACorruption) corruption);
	int before = hir_context_error_count(ctx);
	int accepted = hir_verify_out_of_ssa(ctx, ssa);

	if (corruption == HIR_TEST_OUT_SSA_UNSUPPORTED_DEF
	    || corruption == HIR_TEST_OUT_SSA_UNSUPPORTED_NODEF
	    || corruption == HIR_TEST_OUT_SSA_CORRUPTION_COUNT)
	    check_int("supported out-of-ssa placeholder verifies", accepted, 1);
	else
	    check_rejected("negative out-of-ssa verifier matrix", accepted,
		before, hir_context_error_count(ctx));
	hir_context_free(ctx);
    }
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
test_dead_if_else_local_has_no_phi(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    Cond_Arm arm;
    Expr one = int_expr(1, 90);
    Expr two = int_expr(2, 90);
    Expr cond = binary_expr(EXPR_LT, &one, &two);
    Expr then_value = int_expr(3, 91);
    Expr then_lhs = id_expr(16, 91);
    Expr then_assign = binary_expr(EXPR_ASGN, &then_lhs, &then_value);
    Stmt then_stmt = expr_stmt(&then_assign);
    Expr else_value = int_expr(4, 92);
    Expr else_lhs = id_expr(16, 92);
    Expr else_assign = binary_expr(EXPR_ASGN, &else_lhs, &else_value);
    Stmt else_stmt = expr_stmt(&else_assign);
    Expr ret_expr = int_expr(5, 93);
    Stmt ret = return_stmt(&ret_expr);
    Stmt if_stmt_node;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&arm, 0, sizeof(arm));
    arm.condition = &cond;
    arm.stmt = &then_stmt;

    memset(&if_stmt_node, 0, sizeof(if_stmt_node));
    if_stmt_node.kind = STMT_COND;
    if_stmt_node.lineno = 90;
    if_stmt_node.s.cond.arms = &arm;
    if_stmt_node.s.cond.otherwise = &else_stmt;
    if_stmt_node.next = &ret;

    (void) lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);

    check_int("dead ifelse local phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 0);
    check_int("dead ifelse local entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 0);
    check_int("dead ifelse local verify errors",
	      hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_uninitialized_user_local_is_none_constant(void)
{
    Names names;
    HIRContext *ctx;
    HIRProgram *program;
    HIRTacProgram *tac;
    HIRCFG *cfg;
    HIRSSAProgram *ssa;
    Expr local = id_expr(18, 95);
    Stmt ret = return_stmt(&local);

    memset(&names, 0, sizeof(names));
    names.size = 19;
    ctx = hir_context_new(&names);
    hir_context_set_first_user_local(ctx, 18);
    program = hir_lift_ast(ctx, &ret);
    tac = hir_lower_to_tac(ctx, program);
    cfg = hir_build_cfg(ctx, tac);
    ssa = hir_build_ssa(ctx, cfg);

    check_int("uninitialized local entry loads",
	      hir_ssa_count_kind(ssa, HIR_TAC_LOAD_LOCAL), 0);
    check_int("uninitialized local none constants",
	      hir_ssa_count_kind(ssa, HIR_TAC_CONST), 1);
    check_int("uninitialized local verify", hir_verify_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_deopt_live_if_else_local_keeps_phi(void)
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
    Expr numerator = int_expr(6, 103);
    Expr denominator = int_expr(2, 103);
    Expr divide = binary_expr(EXPR_DIVIDE, &numerator, &denominator);
    Stmt ret = return_stmt(&divide);
    Stmt if_stmt_node;

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

    check_int("deopt-live ifelse local phi count",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI), 1);
    check_int("deopt-live ifelse materialization snapshots",
	      hir_ssa_local_snapshot_count(ssa), 2);
    check_int("deopt-live ifelse local verify errors",
	      hir_context_error_count(ctx), 0);

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
test_direct_index_assignment_native(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr list = id_expr(0, 10);
    Expr index = int_expr(2, 10);
    Expr lhs = binary_expr(EXPR_INDEX, &list, &index);
    Expr value = int_expr(42, 10);
    Expr assign = binary_expr(EXPR_ASGN, &lhs, &value);
    Stmt ret = return_stmt(&assign);

    memset(&names, 0, sizeof(names));
    names.size = 1;
    list.bytecode_pc = 1;
    index.bytecode_pc = 2;
    value.bytecode_pc = 3;
    assign.bytecode_pc = 4;
    ret.bytecode_pc = 5;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("index assignment accepted", hir_context_error_count(ctx), 0);
	check_int("index assignment native count",
	      hir_tac_count_kind(tac, HIR_TAC_INDEX_SET), 1);
    check_int("index assignment deopt count",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 0);
    check_int("index assignment resume stack",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 4), 3);
    check_int("index assignment ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("index assignment ssa count",
	      hir_ssa_count_kind(ssa, HIR_TAC_INDEX_SET), 1);
    check_int("index assignment destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_nested_index_assignment_deopt(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr list = id_expr(0, 10);
    Expr first_index = int_expr(1, 10);
    Expr inner = binary_expr(EXPR_INDEX, &list, &first_index);
    Expr second_index = int_expr(2, 10);
    Expr lhs = binary_expr(EXPR_INDEX, &inner, &second_index);
    Expr value = int_expr(42, 10);
    Expr assign = binary_expr(EXPR_ASGN, &lhs, &value);
    Stmt ret = return_stmt(&assign);

    memset(&names, 0, sizeof(names));
    names.size = 1;
    list.bytecode_pc = 1;
    first_index.bytecode_pc = 2;
    inner.bytecode_pc = 3;
    second_index.bytecode_pc = 4;
    value.bytecode_pc = 5;
    assign.bytecode_pc = 6;
    ret.bytecode_pc = 7;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("nested index assignment accepted",
	      hir_context_error_count(ctx), 0);
    check_int("nested index assignment preserved ref",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX), 1);
    check_int("nested index assignment deopt stack",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 6), 5);
    check_int("nested index assignment ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("nested index assignment destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_property_index_assignment_deopt(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr object = id_expr(0, 10);
    Expr property;
    Expr property_ref;
    Expr index = int_expr(2, 10);
    Expr lhs;
    Expr value = int_expr(42, 10);
    Expr assign;
    Stmt ret;

    memset(&property, 0, sizeof(property));
    property.kind = EXPR_VAR;
    property.lineno = 10;
    property.e.var.type = TYPE_STR;
    property.e.var.v.str = "items";
    property_ref = binary_expr(EXPR_PROP, &object, &property);
    lhs = binary_expr(EXPR_INDEX, &property_ref, &index);
    assign = binary_expr(EXPR_ASGN, &lhs, &value);
    ret = return_stmt(&assign);

    memset(&names, 0, sizeof(names));
    names.size = 1;
    object.bytecode_pc = 1;
    property.bytecode_pc = 2;
    property_ref.bytecode_pc = 3;
    index.bytecode_pc = 4;
    value.bytecode_pc = 5;
    assign.bytecode_pc = 6;
    ret.bytecode_pc = 7;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("property index assignment accepted",
	      hir_context_error_count(ctx), 0);
    check_int("property index assignment preserved property",
	      hir_tac_count_binary_op(tac, HIR_OP_GET_PROP), 1);
    check_int("property index assignment deopt stack",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 6), 5);
    check_int("property index assignment ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("property index assignment destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
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
    check_int("scatter tac deopt count",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 1);
    check_int("scatter tac deopt stack",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 2), 1);
    check_int("scatter boundaries preserve canonical stack",
	      hir_tac_stack_depth_mismatch_count(tac, 2, 1), 0);
    check_int("scatter tac binary add count",
	      hir_tac_count_binary_op(tac, HIR_OP_ADD), 1);
    check_int("scatter verify errors", hir_context_error_count(ctx), 0);

    check_int("scatter destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_optional_rest_scatter_deopt(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Scatter required, optional, rest;
    Expr default_value = int_expr(10, 10);
    Expr scatter_lhs;
    Expr rhs = id_expr(0, 10);
    Expr assign;
    Stmt ret;

    memset(&required, 0, sizeof(required));
    required.kind = SCAT_REQUIRED;
    required.id = 1;
    required.next = &optional;
    memset(&optional, 0, sizeof(optional));
    optional.kind = SCAT_OPTIONAL;
    optional.id = 2;
    optional.expr = &default_value;
    optional.next = &rest;
    memset(&rest, 0, sizeof(rest));
    rest.kind = SCAT_REST;
    rest.id = 3;

    memset(&scatter_lhs, 0, sizeof(scatter_lhs));
    scatter_lhs.kind = EXPR_SCATTER;
    scatter_lhs.lineno = 10;
    scatter_lhs.e.scatter = &required;
    assign = binary_expr(EXPR_ASGN, &scatter_lhs, &rhs);
    ret = return_stmt(&assign);

    memset(&names, 0, sizeof(names));
    names.size = 4;
    rhs.bytecode_pc = 1;
    assign.bytecode_pc = 2;
    ret.bytecode_pc = 3;
    default_value.bytecode_pc = 99;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("optional rest scatter accepted",
	      hir_context_error_count(ctx), 0);
    check_int("optional rest scatter deopt count",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 1);
    check_int("optional rest scatter deopt stack",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 2), 1);
    check_int("optional rest boundaries preserve canonical stack",
	      hir_tac_stack_depth_mismatch_count(tac, 2, 1), 0);
    check_int("optional rest scatter default lowered",
	      hir_tac_count_bytecode_pc(tac, default_value.bytecode_pc) > 0, 1);
    check_int("optional rest scatter sublist op",
	      hir_tac_count_binary_op(tac, HIR_OP_SUBLIST_FROM), 1);
    check_int("optional rest scatter ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("optional rest scatter destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_optional_scatter_default_lowering(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Scatter required1, required2, optional1, optional2;
    Expr default_value = int_expr(0, 10);
    Expr second_default = int_expr(1, 10);
    Expr scatter_lhs;
    Expr rhs = id_expr(0, 10);
    Expr assign;
    Stmt ret;

    memset(&required1, 0, sizeof(required1));
    required1.kind = SCAT_REQUIRED;
    required1.id = 1;
    required1.next = &required2;
    memset(&required2, 0, sizeof(required2));
    required2.kind = SCAT_REQUIRED;
    required2.id = 2;
    required2.next = &optional1;
    memset(&optional1, 0, sizeof(optional1));
    optional1.kind = SCAT_OPTIONAL;
    optional1.id = 3;
    optional1.expr = &default_value;
    optional1.next = &optional2;
    memset(&optional2, 0, sizeof(optional2));
    optional2.kind = SCAT_OPTIONAL;
    optional2.id = 4;
    optional2.expr = &second_default;

    memset(&scatter_lhs, 0, sizeof(scatter_lhs));
    scatter_lhs.kind = EXPR_SCATTER;
    scatter_lhs.lineno = 10;
    scatter_lhs.e.scatter = &required1;
    assign = binary_expr(EXPR_ASGN, &scatter_lhs, &rhs);
    ret = return_stmt(&assign);

    memset(&names, 0, sizeof(names));
    names.size = 5;
    rhs.bytecode_pc = 1;
    assign.bytecode_pc = 2;
    default_value.bytecode_pc = 3;
    second_default.bytecode_pc = 5;
    ret.bytecode_pc = 4;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("optional scatter accepted", hir_context_error_count(ctx), 0);
    check_int("optional scatter indexes all targets",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX), 4);
    check_int("optional scatter lowers default",
	      hir_tac_count_bytecode_pc(tac, default_value.bytecode_pc), 1);
    check_int("optional scatter lowers second default",
	      hir_tac_count_bytecode_pc(tac, second_default.bytecode_pc), 1);
    check_int("optional scatter charges one opcode tick",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 1);
    check_int("optional scatter has invalid-shape deopt",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 1);
    check_int("optional scatter invalid deopt preserves rhs",
	      hir_tac_stack_depth_at_bytecode_pc(tac, assign.bytecode_pc), 1);
    check_int("optional scatter boundaries preserve canonical stack",
	      hir_tac_stack_depth_mismatch_count(tac, assign.bytecode_pc, 1), 0);
    check_int("optional scatter ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("optional scatter destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    check_int("optional scatter out-of-ssa valid",
	      hir_verify_out_of_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_malformed_scatter_lowering(void)
{
    static const struct {
	enum Scatter_Kind first_kind;
	enum Scatter_Kind second_kind;
	int first_has_default;
	int second_has_default;
    } cases[] = {
	{SCAT_REST, SCAT_REST, 0, 0},
	{SCAT_OPTIONAL, SCAT_REQUIRED, 1, 0},
	{SCAT_REST, SCAT_REQUIRED, 0, 0},
	{SCAT_REST, SCAT_OPTIONAL, 0, 1},
	{SCAT_REQUIRED, SCAT_OPTIONAL, 0, 0}
    };
    unsigned i;

    for (i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
	Names names;
	HIRContext *ctx;
	HIRCFG *cfg;
	HIRDominatorTree *dom;
	HIRSSAProgram *ssa;
	HIRTacProgram *tac;
	Scatter first, second;
	Expr default_value = int_expr(10, 10);
	Expr scatter_lhs;
	Expr rhs = id_expr(0, 10);
	Expr assign;
	Stmt ret;

	memset(&first, 0, sizeof(first));
	first.kind = cases[i].first_kind;
	first.id = 1;
	first.expr = cases[i].first_has_default ? &default_value : 0;
	first.next = &second;
	memset(&second, 0, sizeof(second));
	second.kind = cases[i].second_kind;
	second.id = 2;
	second.expr = cases[i].second_has_default ? &default_value : 0;

	memset(&scatter_lhs, 0, sizeof(scatter_lhs));
	scatter_lhs.kind = EXPR_SCATTER;
	scatter_lhs.lineno = 10;
	scatter_lhs.e.scatter = &first;
	assign = binary_expr(EXPR_ASGN, &scatter_lhs, &rhs);
	ret = return_stmt(&assign);
	memset(&names, 0, sizeof(names));
	names.size = 3;
	rhs.bytecode_pc = 1;
	assign.bytecode_pc = 2;
	ret.bytecode_pc = 3;

	tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
	check_int("malformed scatter lowers to one safe deopt",
		  hir_tac_count_kind(tac, HIR_TAC_DEOPT), 1);
	check_int("malformed scatter preserves rhs for deopt",
		  hir_tac_stack_depth_at_bytecode_pc(tac,
		      assign.bytecode_pc), 1);
	check_int("malformed scatter has no native indexing",
		  hir_tac_count_binary_op(tac, HIR_OP_INDEX)
		  + hir_tac_count_binary_op(tac, HIR_OP_SUBLIST_FROM), 0);
	check_int("malformed scatter TAC verifies",
		  hir_context_error_count(ctx), 0);
	hir_context_free(ctx);
    }
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
    a1.bytecode_pc = 4;
    a2.bytecode_pc = 5;
    a3.bytecode_pc = 6;
    list_expr.bytecode_pc = 7;
    ret.bytecode_pc = 8;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("list splice tac not null", tac != 0, 1);
    check_int("list splice singleton count",
	      hir_tac_count_unary_op(tac, HIR_OP_MAKE_SINGLETON_LIST), 1);
    check_int("list splice append count",
	      hir_tac_count_binary_op(tac, HIR_OP_LIST_APPEND), 1);
    check_int("list splice add tail count",
	      hir_tac_count_binary_op(tac, HIR_OP_LIST_ADD_TAIL), 1);
    check_int("list splice first item pc",
	      hir_tac_count_bytecode_pc(tac, 4), 1);
    check_int("list splice second item pc",
	      hir_tac_count_bytecode_pc(tac, 5), 1);
    check_int("list splice third item pc",
	      hir_tac_count_bytecode_pc(tac, 6), 1);
    check_int("list splice verify errors", hir_context_error_count(ctx), 0);

    check_int("list splice destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_initial_list_splice_anchor(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Arg_List arg;
    Expr value, list_expr;
    Stmt ret;

    value = id_expr(0, 10);
    memset(&arg, 0, sizeof(arg));
    arg.kind = ARG_SPLICE;
    arg.expr = &value;
    arg.bytecode_pc = 2;

    memset(&list_expr, 0, sizeof(list_expr));
    list_expr.kind = EXPR_LIST;
    list_expr.lineno = 10;
    list_expr.e.list = &arg;
    list_expr.bytecode_pc = 3;
    ret = return_stmt(&list_expr);
    ret.bytecode_pc = 4;

    memset(&names, 0, sizeof(names));
    names.size = 2;
    value.bytecode_pc = 1;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("initial splice check count",
	      hir_tac_count_unary_op(tac, HIR_OP_CHECK_LIST_FOR_SPLICE), 1);
    check_int("initial splice check pc",
	      hir_tac_count_bytecode_pc(tac, 2), 1);
    check_int("initial splice verify errors", hir_context_error_count(ctx), 0);

    check_int("initial splice destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
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
    check_int("builtin call singleton pc",
	      hir_tac_count_bytecode_pc(tac, 2), 1);
    check_int("builtin call call pc",
	      hir_tac_count_bytecode_pc(tac, 3), 1);
    check_int("builtin call verify errors", hir_context_error_count(ctx), 0);

    check_int("builtin call destroy ssa", hir_destroy_ssa(ctx, ssa), 1);
    hir_context_free(ctx);
}

static void
test_zero_argument_builtin_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr call_expr;
    Stmt ret;

    memset(&call_expr, 0, sizeof(call_expr));
    call_expr.kind = EXPR_CALL;
    call_expr.lineno = 10;
    call_expr.bytecode_pc = 1;
    call_expr.e.call.func = 10; /* time */
    call_expr.e.call.args = 0;

    ret = return_stmt(&call_expr);
    ret.bytecode_pc = 3;

    memset(&names, 0, sizeof(names));
    names.size = 2;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("zero-argument builtin unary count",
	      hir_tac_count_unary_op(tac, HIR_OP_TIME), 1);
    check_int("zero-argument builtin verify errors",
	      hir_context_error_count(ctx), 0);
    check_int("zero-argument builtin destroy ssa",
	      hir_destroy_ssa(ctx, ssa), 1);
    check_int("zero-argument builtin out-of-ssa valid",
	      hir_verify_out_of_ssa(ctx, ssa), 1);

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
test_string_search_builtin_inlining(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Arg_List a1, a2, a3;
    Expr source, needle, case_matters, call;
    Stmt ret;

    memset(&source, 0, sizeof(source));
    source.kind = EXPR_VAR;
    source.lineno = 10;
    source.e.var.type = TYPE_STR;
    source.e.var.v.str = str_dup("LambdaMOO");
    memset(&needle, 0, sizeof(needle));
    needle.kind = EXPR_VAR;
    needle.lineno = 10;
    needle.e.var.type = TYPE_STR;
    needle.e.var.v.str = str_dup("moo");
    case_matters = int_expr(1, 10);

    memset(&a2, 0, sizeof(a2));
    a2.kind = ARG_NORMAL;
    a2.expr = &needle;
    memset(&a1, 0, sizeof(a1));
    a1.kind = ARG_NORMAL;
    a1.expr = &source;
    a1.next = &a2;
    memset(&call, 0, sizeof(call));
    call.kind = EXPR_CALL;
    call.lineno = 10;
    call.e.call.func = 7;
    call.e.call.args = &a1;
    call.bytecode_pc = 5;
    ret = return_stmt(&call);
    ret.bytecode_pc = 7;
    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("index inline binary count",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX_BF), 1);
    check_int("index inline call count",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 0);
    check_int("index inline verify errors", hir_context_error_count(ctx), 0);
    hir_context_free(ctx);

    call.e.call.func = 8;
    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("rindex inline binary count",
	      hir_tac_count_binary_op(tac, HIR_OP_RINDEX_BF), 1);
    check_int("rindex inline call count",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 0);
    hir_context_free(ctx);

    memset(&a3, 0, sizeof(a3));
    a3.kind = ARG_NORMAL;
    a3.expr = &case_matters;
    a2.next = &a3;
    call.e.call.func = 7;
    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("three-argument index remains a call",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 1);
    check_int("three-argument index is not inlined",
	      hir_tac_count_binary_op(tac, HIR_OP_INDEX_BF), 0);
    hir_context_free(ctx);

    a2.next = 0;
    call.e.call.func = 9;
    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("other two-argument built-in remains a call",
	      hir_tac_count_kind(tac, HIR_TAC_CALL), 1);
    hir_context_free(ctx);

    free_str(source.e.var.v.str);
    free_str(needle.e.var.v.str);
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

    add.bytecode_pc = 42;
    loop.bytecode_pc = 41;
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
    check_int("for list body stack uses incremented index",
	      hir_ssa_stack_value_at_bytecode_pc(ssa, 42, 1),
	      hir_ssa_binary_value_at_bytecode_pc(ssa, 41, HIR_OP_ADD));

    (void) hir_optimize_ssa_constants(ctx, ssa);
    check_int("for list optimization keeps loop phis",
	      hir_ssa_count_kind(ssa, HIR_TAC_PHI) >= 2, 1);
    check_int("for list bound keeps loop index phi",
	      hir_ssa_binary_uses_phi_count(ssa, HIR_OP_LE), 1);
    check_int("for list lookup keeps loop index phi",
	      hir_ssa_binary_uses_phi_count(ssa, HIR_OP_INDEX) >= 1, 1);

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
    Expr call_obj = id_expr(0, 16);
    Expr call_name = id_expr(3, 16);
    Expr call_arg = int_expr(0, 16);
    Arg_List call_args;
    Expr call_expr;
    Stmt call_stmt;

    Expr sum_lhs = id_expr(1, 17);
    Expr sum_rhs = id_expr(1, 17);
    Expr i_ref3 = id_expr(2, 17);
    Expr add = binary_expr(EXPR_PLUS, &sum_rhs, &i_ref3);
    Expr assign = binary_expr(EXPR_ASGN, &sum_lhs, &add);
    Stmt body_assign = expr_stmt(&assign);

    memset(&call_args, 0, sizeof(call_args));
    call_args.kind = ARG_NORMAL;
    call_args.expr = &call_arg;
    call_args.bytecode_pc = 29;
    memset(&call_expr, 0, sizeof(call_expr));
    call_expr.kind = EXPR_VERB;
    call_expr.lineno = 16;
    call_expr.bytecode_pc = 30;
    call_expr.e.verb.obj = &call_obj;
    call_expr.e.verb.verb = &call_name;
    call_expr.e.verb.args = &call_args;
    call_stmt = expr_stmt(&call_expr);
    call_obj.bytecode_pc = 27;
    call_name.bytecode_pc = 28;
    call_arg.bytecode_pc = 29;

    if_cont.next = &call_stmt;
    call_stmt.next = &if_brk;
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
    check_int("break/cont call preserves loop stack",
	      hir_tac_stack_depth_at_bytecode_pc(tac, 30), 5);
    check_int("break/cont tick count",
	      hir_tac_count_kind(tac, HIR_TAC_TICK), 10);

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
test_labeled_continue_and_unmatched_exits(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr outer_from = int_expr(1, 20);
    Expr outer_to = int_expr(2, 20);
    Expr inner_from = int_expr(1, 21);
    Expr inner_to = int_expr(2, 21);
    Stmt cont_outer = continue_stmt(2, 22);
    Stmt inner_loop = range_stmt(3, &inner_from, &inner_to, &cont_outer, 21);
    Stmt outer_loop = range_stmt(2, &outer_from, &outer_to, &inner_loop, 20);
    Stmt bad_break = break_stmt(99, 30);
    Stmt bad_continue = continue_stmt(99, 31);
    Expr result = int_expr(1, 32);
    Stmt ret = return_stmt(&result);

    memset(&names, 0, sizeof(names));
    names.size = 32;
    tac = lower_stmt(&names, &outer_loop, &ctx, &cfg, &dom, &ssa);
    check_int("labeled continue verifies", hir_context_error_count(ctx), 0);
    check_int("labeled continue has loop jumps",
	      hir_tac_count_kind(tac, HIR_TAC_JUMP) >= 3, 1);
    hir_context_free(ctx);

    bad_break.next = &bad_continue;
    bad_continue.next = &ret;
    tac = lower_stmt(&names, &bad_break, &ctx, &cfg, &dom, &ssa);
    check_int("unmatched exits report both errors",
	      hir_context_error_count(ctx) >= 2, 1);
    check_int("unmatched exits retain following return",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
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
    check_int("repeat assign materialization snapshots",
	      hir_ssa_local_snapshot_count(ssa), 0);
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
    Expr catch_expr, try_expr, lhs_expr, rhs_expr, handler_expr;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    lhs_expr = int_expr(1, 30);
    rhs_expr = int_expr(0, 30);
    try_expr = binary_expr(EXPR_DIVIDE, &lhs_expr, &rhs_expr);
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
    check_int("catch expr deopt boundary",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 0);
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
    Expr val_expr, divisor_expr, try_expr, handler_val;
    Stmt body_stmt, handler_stmt, try_stmt;
    Except_Arm except_arm;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    val_expr = int_expr(10, 40);
    divisor_expr = int_expr(0, 40);
    try_expr = binary_expr(EXPR_DIVIDE, &val_expr, &divisor_expr);
    body_stmt = expr_stmt(&try_expr);
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
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("try except deopt boundary",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 0);
    check_int("try except cfg blocks", hir_cfg_block_count(cfg) > 1, 1);
    check_int("try except ssa blocks", hir_ssa_block_count(ssa) > 1, 1);
    check_int("try except verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_native_error_edge_kinds(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr unary_value, unary;
    Expr dividend, divisor, divide;
    Expr range_base, range_from, range_to, range;
    Expr store_base, store_from, store_to, store_range, store_value, assign;
    Expr handler_value;
    Stmt unary_stmt, divide_stmt, range_stmt, store_stmt, handler_stmt;
    Stmt try_stmt;
    Except_Arm except_arm;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    unary_value = id_expr(0, 43);
    unary = unary_expr(EXPR_NEGATE, &unary_value);
    unary_stmt = expr_stmt(&unary);

    dividend = id_expr(1, 44);
    divisor = id_expr(2, 44);
    divide = binary_expr(EXPR_DIVIDE, &dividend, &divisor);
    divide_stmt = expr_stmt(&divide);

    range_base = id_expr(3, 45);
    range_from = int_expr(1, 45);
    range_to = int_expr(2, 45);
    range = range_expr_ast(&range_base, &range_from, &range_to, 45);
    range_stmt = expr_stmt(&range);

    store_base = id_expr(3, 46);
    store_from = int_expr(1, 46);
    store_to = int_expr(2, 46);
    store_range = range_expr_ast(&store_base, &store_from, &store_to, 46);
    store_value = id_expr(4, 46);
    assign = binary_expr(EXPR_ASGN, &store_range, &store_value);
    store_stmt = expr_stmt(&assign);

    unary_stmt.next = &divide_stmt;
    divide_stmt.next = &range_stmt;
    range_stmt.next = &store_stmt;

    handler_value = int_expr(0, 47);
    handler_stmt = return_stmt(&handler_value);
    memset(&except_arm, 0, sizeof(except_arm));
    except_arm.id = -1;
    except_arm.stmt = &handler_stmt;
    memset(&try_stmt, 0, sizeof(try_stmt));
    try_stmt.kind = STMT_TRY_EXCEPT;
    try_stmt.lineno = 43;
    try_stmt.s.catch.body = &unary_stmt;
    try_stmt.s.catch.excepts = &except_arm;

    tac = lower_stmt(&names, &try_stmt, &ctx, &cfg, &dom, &ssa);
    check_int("native error edge unary count",
	      hir_tac_count_kind(tac, HIR_TAC_UNARY), 1);
    check_int("native error edge binary count",
	      hir_tac_count_kind(tac, HIR_TAC_BINARY), 1);
    check_int("native error edge range read count",
	      hir_tac_count_kind(tac, HIR_TAC_RANGE_REF), 1);
    check_int("native error edge range write count",
	      hir_tac_count_kind(tac, HIR_TAC_RANGE_SET), 1);
    check_int("native error edge CFG edge count", hir_cfg_edge_count(cfg), 9);
    check_int("native error edge verify errors", hir_context_error_count(ctx),
	      0);
    hir_context_free(ctx);
}

static void
test_multi_arm_try_except_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr body_val = int_expr(1, 45);
    Expr first_val = int_expr(2, 46);
    Expr second_val = int_expr(3, 47);
    Stmt body = expr_stmt(&body_val);
    Stmt first_handler = expr_stmt(&first_val);
    Stmt second_handler = return_stmt(&second_val);
    Except_Arm first;
    Except_Arm second;
    Stmt try_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    memset(&first, 0, sizeof(first));
    memset(&second, 0, sizeof(second));
    first.id = 1;
    first.stmt = &first_handler;
    first.handler_pc = 100;
    first.next = &second;
    second.id = -1;
    second.stmt = &second_handler;
    second.handler_pc = 101;
    memset(&try_stmt, 0, sizeof(try_stmt));
    try_stmt.kind = STMT_TRY_EXCEPT;
    try_stmt.lineno = 45;
    try_stmt.s.catch.body = &body;
    try_stmt.s.catch.excepts = &first;

    tac = lower_stmt(&names, &try_stmt, &ctx, &cfg, &dom, &ssa);
    check_int("multi-arm try except verifies", hir_context_error_count(ctx), 0);
    check_int("multi-arm try except branches to done",
	      hir_tac_count_kind(tac, HIR_TAC_JUMP), 2);
    check_int("multi-arm try except return",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
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
    check_int("try finally deopt boundary",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 0);
    check_int("try finally cfg blocks", hir_cfg_block_count(cfg), 1);
    check_int("try finally ssa blocks", hir_ssa_block_count(ssa), 1);
    check_int("try finally verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_loop_exit_through_finally_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr from = int_expr(1, 55);
    Expr to = int_expr(2, 55);
    Stmt brk = break_stmt(-1, 56);
    Expr handler_lhs = int_expr(9, 57);
    Expr handler_rhs = int_expr(1, 57);
    Expr handler_val = binary_expr(EXPR_PLUS, &handler_lhs, &handler_rhs);
    Stmt handler = expr_stmt(&handler_val);
    Stmt try_stmt;
    Stmt loop;

    memset(&try_stmt, 0, sizeof(try_stmt));
    try_stmt.kind = STMT_TRY_FINALLY;
    try_stmt.lineno = 56;
    try_stmt.s.finally.body = &brk;
    try_stmt.s.finally.handler = &handler;
    try_stmt.s.finally.handler_pc = 110;
    loop = range_stmt(1, &from, &to, &try_stmt, 55);
    memset(&names, 0, sizeof(names));
    names.size = 32;

    tac = lower_stmt(&names, &loop, &ctx, &cfg, &dom, &ssa);
    check_int("break through finally verifies", hir_context_error_count(ctx), 0);
    check_int("break through finally lowers handler twice",
	      hir_tac_count_lineno(tac, 57), 8);
    check_int("break through finally emits loop jumps",
	      hir_tac_count_kind(tac, HIR_TAC_JUMP) >= 2, 1);
    hir_context_free(ctx);
}

static void
test_fork_stmt_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr time_expr, body_val;
    Stmt body_stmt, fork_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    time_expr = int_expr(5, 60);
    body_val = int_expr(1, 61);
    body_stmt = expr_stmt(&body_val);

    memset(&fork_stmt, 0, sizeof(fork_stmt));
    fork_stmt.kind = STMT_FORK;
    fork_stmt.lineno = 60;
    fork_stmt.s.fork.time = &time_expr;
    fork_stmt.s.fork.id = 0;
    fork_stmt.s.fork.body = &body_stmt;
    fork_stmt.s.fork.code_unit = 1;

    tac = lower_stmt(&names, &fork_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("fork stmt deopt boundary",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 1);
    check_int("fork stmt verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_fork_body_does_not_reject_enclosing_hir(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr time_expr, unsupported_body_expr;
    Stmt body_stmt, fork_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    time_expr = int_expr(5, 65);
    memset(&unsupported_body_expr, 0, sizeof(unsupported_body_expr));
    unsupported_body_expr.kind = EXPR_LENGTH;
    unsupported_body_expr.lineno = 66;
    body_stmt = expr_stmt(&unsupported_body_expr);

    memset(&fork_stmt, 0, sizeof(fork_stmt));
    fork_stmt.kind = STMT_FORK;
    fork_stmt.lineno = 65;
    fork_stmt.s.fork.time = &time_expr;
    fork_stmt.s.fork.id = 0;
    fork_stmt.s.fork.body = &body_stmt;
    fork_stmt.s.fork.code_unit = 1;

    tac = lower_stmt(&names, &fork_stmt, &ctx, &cfg, &dom, &ssa);

    check_int("fork body does not add unsupported tac",
	      hir_tac_count_kind(tac, HIR_TAC_UNSUPPORTED), 0);
    check_int("fork body does not add hir errors",
	      hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_length_expr_in_index_tac_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr local_base, len_expr, idx_expr;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    local_base = id_expr(0, 70);
    memset(&len_expr, 0, sizeof(len_expr));
    len_expr.kind = EXPR_LENGTH;
    len_expr.lineno = 70;
    idx_expr = binary_expr(EXPR_INDEX, &local_base, &len_expr);
    ret = return_stmt(&idx_expr);

    tac = lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);

    check_int("length in index tac returns",
	      hir_tac_count_kind(tac, HIR_TAC_RETURN), 1);
    check_int("length in index tac unaries",
	      hir_tac_count_kind(tac, HIR_TAC_UNARY), 1);
    check_int("length in index verify errors", hir_context_error_count(ctx), 0);

    hir_context_free(ctx);
}

static void
test_unreachable_dead_code_and_folded_phi_ssa(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr cond, one, two, comment, dead_var;
    Stmt then_stmt, else_stmt, if_stmt_node, dead_stmt, final_ret;
    Cond_Arm arm;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    cond = int_expr(1, 80);
    one = int_expr(1, 81);
    two = int_expr(2, 82);
    then_stmt = return_stmt(&one);
    else_stmt = return_stmt(&two);
    arm = cond_arm_ast(&cond, &then_stmt);
    if_stmt_node = cond_stmt_ast(&arm, &else_stmt, 80);

    comment = int_expr(999, 85);
    dead_var = id_expr(0, 85);
    dead_stmt = expr_stmt(&comment);
    final_ret = return_stmt(&dead_var);
    if_stmt_node.next = &dead_stmt;
    dead_stmt.next = &final_ret;

    tac = lower_stmt(&names, &if_stmt_node, &ctx, &cfg, &dom, &ssa);
    check_int("dead code verify errors", hir_context_error_count(ctx), 0);
    check_int("dead code ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("dead code adds no synthetic ticks",
	      hir_ssa_count_kind(ssa, HIR_TAC_TICK),
	      hir_tac_count_kind(tac, HIR_TAC_TICK));
    (void) hir_optimize_ssa_constants(ctx, ssa);
    check_int("dead code ssa valid after opt", hir_verify_ssa(ctx, ssa), 1);
    check_int("dead code out-of-ssa destroy", hir_destroy_ssa(ctx, ssa), 1);
    check_int("dead code out-of-ssa verify", hir_verify_out_of_ssa(ctx, ssa), 1);

    hir_context_free(ctx);
}

static void
test_string_add_operand_inference(void)
{
    var_type inferred = TYPE_NONE;

    check_int("string add infers unknown right operand",
	      hir_test_infer_string_add_operand(HIR_OP_ADD, 1, TYPE_STR,
						&inferred), 1);
    check_int("string add inferred type", inferred, TYPE_STR);

    inferred = TYPE_NONE;
    check_int("integer add does not infer string operand",
	      hir_test_infer_string_add_operand(HIR_OP_ADD, 1, TYPE_INT,
						&inferred), 0);
    check_int("integer add leaves inferred type alone", inferred, TYPE_NONE);

    check_int("non-add does not infer string operand",
	      hir_test_infer_string_add_operand(HIR_OP_SUB, 1, TYPE_STR,
						&inferred), 0);
    check_int("unknown peer does not infer string operand",
	      hir_test_infer_string_add_operand(HIR_OP_ADD, 0, TYPE_STR,
						&inferred), 0);
}

static unsigned short
type_mask(var_type type)
{
    return (unsigned short) 1U << ((unsigned) type & TYPE_DB_MASK);
}

static void
test_binary_type_pair_contracts(void)
{
    unsigned short numeric = type_mask(TYPE_INT) | type_mask(TYPE_FLOAT);

    check_int("integer addition pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_ADD, TYPE_INT,
						 TYPE_INT), 1);
    check_int("float addition pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_ADD, TYPE_FLOAT,
						 TYPE_FLOAT), 1);
    check_int("string addition pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_ADD, TYPE_STR,
						 TYPE_STR), 1);
    check_int("mixed string addition pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_ADD, TYPE_STR,
						 TYPE_INT), 0);
    check_int("mixed numeric addition pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_ADD, TYPE_INT,
						 TYPE_FLOAT), 0);
    check_int("integer subtraction pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_SUB, TYPE_INT,
						 TYPE_INT), 1);
    check_int("float multiplication pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_MUL, TYPE_FLOAT,
						 TYPE_FLOAT), 1);
    check_int("string division pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_DIV, TYPE_STR,
						 TYPE_STR), 0);
    check_int("mixed modulus pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_MOD, TYPE_INT,
						 TYPE_FLOAT), 0);
    check_int("integer comparison pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_LT, TYPE_INT,
						 TYPE_INT), 1);
    check_int("float comparison pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_GE, TYPE_FLOAT,
						 TYPE_FLOAT), 1);
    check_int("string comparison pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_LE, TYPE_STR,
						 TYPE_STR), 1);
    check_int("mixed comparison pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_GT, TYPE_STR,
						 TYPE_INT), 0);
    check_int("integer exponent pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_EXP, TYPE_INT,
						 TYPE_INT), 1);
    check_int("string exponent pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_EXP, TYPE_STR,
						 TYPE_INT), 0);
    check_int("unrelated operation pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_IN, TYPE_INT,
						 TYPE_INT), 0);
    check_int("unknown addition left mask",
	      hir_test_binary_operand_type_mask(HIR_OP_ADD, 0, 0, TYPE_NONE),
	      numeric | type_mask(TYPE_STR));
    check_int("unknown addition right mask",
	      hir_test_binary_operand_type_mask(HIR_OP_ADD, 1, 0, TYPE_NONE),
	      numeric | type_mask(TYPE_STR));
    check_int("string peer narrows addition left mask",
	      hir_test_binary_operand_type_mask(HIR_OP_ADD, 0, 1, TYPE_STR),
	      type_mask(TYPE_STR));
    check_int("float peer narrows addition right mask",
	      hir_test_binary_operand_type_mask(HIR_OP_ADD, 1, 1, TYPE_FLOAT),
	      type_mask(TYPE_FLOAT));

    check_int("float modulus pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_MOD, TYPE_FLOAT,
						 TYPE_FLOAT), 1);
    check_int("float-to-integer exponent pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_EXP, TYPE_FLOAT,
						 TYPE_INT), 1);
    check_int("float exponent pair is valid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_EXP, TYPE_FLOAT,
						 TYPE_FLOAT), 1);
    check_int("integer-to-float exponent pair is invalid",
	      hir_test_binary_type_pair_is_valid(HIR_OP_EXP, TYPE_INT,
						 TYPE_FLOAT), 0);
    check_int("integer base narrows exponent mask",
	      hir_test_binary_operand_type_mask(HIR_OP_EXP, 1, 1, TYPE_INT),
	      type_mask(TYPE_INT));
    check_int("unknown subtraction mask is numeric",
	      hir_test_binary_operand_type_mask(HIR_OP_SUB, 0, 0, TYPE_NONE),
	      numeric);
    check_int("unknown exponent base mask is numeric",
	      hir_test_binary_operand_type_mask(HIR_OP_EXP, 0, 0, TYPE_NONE),
	      numeric);
    check_int("string exponent peer permits no base",
	      hir_test_binary_operand_type_mask(HIR_OP_EXP, 0, 1, TYPE_STR), 0);
}

static void
test_list_operand_inference(void)
{
    check_int("splice check infers list operand",
	      hir_test_unary_operand_defaults_to_list(
		  HIR_OP_CHECK_LIST_FOR_SPLICE), 1);
    check_int("length does not default unknown operand to list",
	      hir_test_unary_operand_defaults_to_list(HIR_OP_LENGTH), 0);
    check_int("unrelated unary op does not infer list operand",
	      hir_test_unary_operand_defaults_to_list(HIR_OP_NOT), 0);
}

static void
test_unknown_type_inference(void)
{
    var_type types[4] = { TYPE_INT, TYPE_INT, TYPE_STR, TYPE_OBJ };
    unsigned char known[4] = { 1, 1, 1, 1 };
    unsigned char tagged[4] = { 1, 1, 1, 1 };

    hir_test_initialize_inferred_value_types(types, known, tagged, 4);
    check_int("unknown inference initializes value to any", types[1], TYPE_ANY);
    check_int("unknown inference initializes value as unknown", known[1], 0);
    check_int("unknown inference does not tag before analysis", tagged[1], 0);

    types[2] = TYPE_STR;
    known[2] = 1;
    hir_test_tag_unknown_inferred_value_types(types, known, tagged, 4);
    check_int("unresolved value remains any", types[1], TYPE_ANY);
    check_int("unresolved value is runtime tagged", tagged[1], 1);
    check_int("known value retains inferred type", types[2], TYPE_STR);
    check_int("known value is not needlessly tagged", tagged[2], 0);
    check_int("second unresolved value remains any", types[3], TYPE_ANY);
    check_int("second unresolved value is runtime tagged", tagged[3], 1);

    check_int("equality does not constrain operand types",
	      hir_test_binary_operands_constrain_each_other(HIR_OP_EQ), 0);
    check_int("inequality does not constrain operand types",
	      hir_test_binary_operands_constrain_each_other(HIR_OP_NE), 0);
    check_int("ordering constrains operand types",
	      hir_test_binary_operands_constrain_each_other(HIR_OP_LT), 1);

    check_int("integer min result is inferred",
	      hir_test_infer_min_max_result(HIR_OP_MIN, TYPE_INT, TYPE_INT,
					    &types[1]), 1);
    check_int("integer min result type", types[1], TYPE_INT);
    check_int("float max result is inferred",
	      hir_test_infer_min_max_result(HIR_OP_MAX, TYPE_FLOAT, TYPE_FLOAT,
					    &types[1]), 1);
    check_int("float max result type", types[1], TYPE_FLOAT);
    check_int("mixed min result is not inferred",
	      hir_test_infer_min_max_result(HIR_OP_MIN, TYPE_INT, TYPE_FLOAT,
					    &types[1]), 0);
    check_int("unrelated binary result is not inferred",
	      hir_test_infer_min_max_result(HIR_OP_ADD, TYPE_INT, TYPE_INT,
					    &types[1]), 0);
}

static void
test_builtin_result_type_inference(void)
{
    static const struct {
	const char *name;
	var_type type;
    } cases[] = {
	{"caller_perms", TYPE_OBJ},
	{"toobj", TYPE_OBJ},
	{"parent", TYPE_OBJ},
	{"owner", TYPE_OBJ},
	{"location", TYPE_OBJ},
	{"tostr", TYPE_STR},
	{"toliteral", TYPE_STR},
	{"tonum", TYPE_INT},
	{"toint", TYPE_INT},
	{"tofloat", TYPE_FLOAT}
    };
    var_type inferred = TYPE_NONE;
    unsigned i;

    for (i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
	inferred = TYPE_NONE;
	check_int("builtin result type is inferred",
	    hir_test_infer_builtin_result_type(cases[i].name, &inferred), 1);
	check_int("builtin result has expected type", inferred, cases[i].type);
    }
#ifdef WAIF_CORE
    inferred = TYPE_NONE;
    check_int("new_waif result type is inferred",
	      hir_test_infer_builtin_result_type("new_waif", &inferred), 1);
    check_int("new_waif result is waif", inferred, TYPE_WAIF);
#endif
    inferred = TYPE_NONE;
    check_int("unknown builtin result type is not inferred",
	      hir_test_infer_builtin_result_type("not_new_waif", &inferred), 0);
    check_int("unknown builtin leaves result type alone", inferred, TYPE_NONE);
}

static void
test_uninitialized_entry_load_classification(void)
{
    int first_user = SLOT_FLOAT + 1;

    check_int("user local entry load is uninitialized",
	      hir_test_is_uninitialized_entry_load(HIR_TAC_LOAD_LOCAL,
						   NO_BYTECODE_PC,
						   first_user, first_user), 1);
    check_int("built-in local entry load is initialized",
	      hir_test_is_uninitialized_entry_load(HIR_TAC_LOAD_LOCAL,
						   NO_BYTECODE_PC,
						   SLOT_ARGS, first_user), 0);
    check_int("anchored user local load is not an entry load",
	      hir_test_is_uninitialized_entry_load(HIR_TAC_LOAD_LOCAL, 0,
						   first_user, first_user), 0);
    check_int("entry instruction must be a local load",
	      hir_test_is_uninitialized_entry_load(HIR_TAC_CONST,
						   NO_BYTECODE_PC,
						   first_user, first_user), 0);
}

static void
test_builtin_entry_types(void)
{
    int first_user = SLOT_FLOAT + 1;
    var_type type = TYPE_ANY;

    check_int("player entry load has object type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, NO_BYTECODE_PC,
					  SLOT_PLAYER, first_user, &type), 1);
    check_int("player entry load type", type, TYPE_OBJ);
    check_int("args entry load has list type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, NO_BYTECODE_PC,
					  SLOT_ARGS, first_user, &type), 1);
    check_int("args entry load type", type, TYPE_LIST);
    check_int("verb entry load has string type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, NO_BYTECODE_PC,
					  SLOT_VERB, first_user, &type), 1);
    check_int("verb entry load type", type, TYPE_STR);
    check_int("NUM entry load has integer type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, NO_BYTECODE_PC,
					  SLOT_NUM, first_user, &type), 1);
    check_int("NUM entry load type", type, TYPE_INT);
    check_int("user local has no built-in type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, NO_BYTECODE_PC,
					  first_user, first_user, &type), 0);
    check_int("waif-capable this has no fixed type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, NO_BYTECODE_PC,
					  SLOT_THIS, first_user, &type), 0);
    check_int("anchored load has no entry type",
	      hir_test_builtin_entry_type(HIR_TAC_LOAD_LOCAL, 0, SLOT_THIS,
					  first_user, &type), 0);
}

static void
test_length_expr_in_stores_and_negatives(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIRTacProgram *tac;
    Expr local_base, len_expr, one_expr, val_expr, idx_expr, range_expr;
    Expr assign_idx, assign_range, assign_chained, unindexed_len, bad_assign;
    Stmt stmt_idx, stmt_range, stmt_chained, bad_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    local_base = id_expr(0, 71);
    memset(&len_expr, 0, sizeof(len_expr));
    len_expr.kind = EXPR_LENGTH;
    len_expr.lineno = 71;
    one_expr = int_expr(1, 71);
    val_expr = int_expr(42, 71);

    /* 1. local[$] = 42 */
    idx_expr = binary_expr(EXPR_INDEX, &local_base, &len_expr);
    assign_idx = binary_expr(EXPR_ASGN, &idx_expr, &val_expr);
    stmt_idx = expr_stmt(&assign_idx);
    tac = lower_stmt(&names, &stmt_idx, &ctx, &cfg, &dom, &ssa);
    check_int("length in index store verify errors", hir_context_error_count(ctx), 0);
    check_int("length in index store native count",
	      hir_tac_count_kind(tac, HIR_TAC_INDEX_SET), 1);
    check_int("length in index store deopt count",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 0);
    hir_context_free(ctx);

    /* 2. local[1..$] = 42 */
    range_expr = range_expr_ast(&local_base, &one_expr, &len_expr, 71);
    assign_range = binary_expr(EXPR_ASGN, &range_expr, &val_expr);
    stmt_range = expr_stmt(&assign_range);
    tac = lower_stmt(&names, &stmt_range, &ctx, &cfg, &dom, &ssa);
    check_int("length in range store verify errors", hir_context_error_count(ctx), 0);
    check_int("length in range store range_set count",
	      hir_tac_count_kind(tac, HIR_TAC_RANGE_SET), 1);
    hir_context_free(ctx);

    /* 3. local[1][$] = 42 (chained index store) */
    Expr outer_base = binary_expr(EXPR_INDEX, &local_base, &one_expr);
    Expr chained_idx = binary_expr(EXPR_INDEX, &outer_base, &len_expr);
    assign_chained = binary_expr(EXPR_ASGN, &chained_idx, &val_expr);
    stmt_chained = expr_stmt(&assign_chained);
    tac = lower_stmt(&names, &stmt_chained, &ctx, &cfg, &dom, &ssa);
    check_int("length in chained index store verify errors", hir_context_error_count(ctx), 0);
    check_int("length in chained index store deopt count",
	      hir_tac_count_kind(tac, HIR_TAC_DEOPT), 1);
    hir_context_free(ctx);

    /* 4. Negative test: unindexed $ (e.g. x = $) */
    Expr target_var = id_expr(1, 72);
    unindexed_len.kind = EXPR_LENGTH;
    unindexed_len.lineno = 72;
    unindexed_len.bytecode_pc = NO_BYTECODE_PC;
    bad_assign = binary_expr(EXPR_ASGN, &target_var, &unindexed_len);
    bad_stmt = expr_stmt(&bad_assign);
    tac = lower_stmt(&names, &bad_stmt, &ctx, &cfg, &dom, &ssa);
    check_int("unindexed length reports error", hir_context_error_count(ctx) > 0, 1);
    check_int("unindexed length unsupported tac count",
	      hir_tac_count_kind(tac, HIR_TAC_UNSUPPORTED), 1);
    hir_context_free(ctx);
}

static void
test_rotate32_optimization(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIROptimizationPlan *plan;
    Expr source, left_count, right_count, mask, modulus;
    Expr shift_left, shift_right, bit_and, bit_or, rotate;
    Stmt ret;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    source = id_expr(0, 89);
    left_count = int_expr(5, 89);
    right_count = int_expr(27, 89);
    mask = int_expr(31, 89);
    modulus = int_expr((Num) ((UNum) 1 << 32), 89);
    shift_left = binary_expr(EXPR_SHL, &source, &left_count);
    shift_right = binary_expr(EXPR_SHR, &source, &right_count);
    bit_and = binary_expr(EXPR_BITAND, &shift_right, &mask);
    bit_or = binary_expr(EXPR_BITOR, &shift_left, &bit_and);
    rotate = binary_expr(EXPR_MOD, &bit_or, &modulus);
    ret = return_stmt(&rotate);

    (void) lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    check_int("rotate32 input verifies", hir_context_error_count(ctx), 0);
    plan = hir_optimize_ssa_for_backends(ctx, ssa);
    check_int("rotate32 optimization changed",
	      hir_optimization_change_count(plan), 1);
    check_int("rotate32 optimized SSA verifies", hir_verify_ssa(ctx, ssa), 1);
#ifdef HIR_DUMP_SSA
    check_ssa_dump_contains("rotate32 optimized operation", ssa, "ROTL32");
#endif
    hir_context_free(ctx);
}

typedef enum {
    ROTATE32_SWAPPED_OR,
    ROTATE32_MASK_FIRST,
    ROTATE32_WRONG_MODULUS,
    ROTATE32_WRONG_OUTER_OP,
    ROTATE32_WRONG_OR_OP,
    ROTATE32_WRONG_LEFT_SHIFT,
    ROTATE32_WRONG_AND_OP,
    ROTATE32_WRONG_RIGHT_SHIFT,
    ROTATE32_ZERO_LEFT_COUNT,
    ROTATE32_LARGE_LEFT_COUNT,
    ROTATE32_WRONG_RIGHT_COUNT,
    ROTATE32_WRONG_MASK,
    ROTATE32_DIFFERENT_SOURCE,
    ROTATE32_MISSING_OR,
    ROTATE32_NONCONSTANT_MODULUS,
    ROTATE32_NONCONSTANT_LEFT_COUNT,
    ROTATE32_NONCONSTANT_RIGHT_COUNT,
    ROTATE32_NONCONSTANT_MASK
} Rotate32Variant;

static int
rotate32_variant_change_count(Rotate32Variant variant)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    HIROptimizationPlan *plan;
    Expr source, other_source, left_count, right_count, mask, modulus;
    Expr shift_left, shift_right, bit_and, bit_or, rotate;
    Stmt ret;
    int changes;

    memset(&names, 0, sizeof(names));
    names.size = 32;
    source = id_expr(0, 89);
    other_source = id_expr(1, 89);
    left_count = int_expr(5, 89);
    right_count = int_expr(27, 89);
    mask = int_expr(31, 89);
    modulus = int_expr((Num) ((UNum) 1 << 32), 89);
    shift_left = binary_expr(EXPR_SHL, &source, &left_count);
    shift_right = binary_expr(EXPR_SHR, &source, &right_count);
    bit_and = binary_expr(EXPR_BITAND, &shift_right, &mask);
    bit_or = binary_expr(EXPR_BITOR, &shift_left, &bit_and);
    rotate = binary_expr(EXPR_MOD, &bit_or, &modulus);

    switch (variant) {
    case ROTATE32_SWAPPED_OR:
	bit_or.e.bin.lhs = &bit_and;
	bit_or.e.bin.rhs = &shift_left;
	break;
    case ROTATE32_MASK_FIRST:
	bit_and.e.bin.lhs = &mask;
	bit_and.e.bin.rhs = &shift_right;
	break;
    case ROTATE32_WRONG_MODULUS:
	modulus.e.var.v.num--;
	break;
    case ROTATE32_WRONG_OUTER_OP:
	rotate.kind = EXPR_DIVIDE;
	break;
    case ROTATE32_WRONG_OR_OP:
	bit_or.kind = EXPR_BITXOR;
	break;
    case ROTATE32_WRONG_LEFT_SHIFT:
	shift_left.kind = EXPR_SHR;
	break;
    case ROTATE32_WRONG_AND_OP:
	bit_and.kind = EXPR_BITOR;
	break;
    case ROTATE32_WRONG_RIGHT_SHIFT:
	shift_right.kind = EXPR_LSHR;
	break;
    case ROTATE32_ZERO_LEFT_COUNT:
	left_count.e.var.v.num = 0;
	break;
    case ROTATE32_LARGE_LEFT_COUNT:
	left_count.e.var.v.num = 32;
	break;
    case ROTATE32_WRONG_RIGHT_COUNT:
	right_count.e.var.v.num = 26;
	break;
    case ROTATE32_WRONG_MASK:
	mask.e.var.v.num = 30;
	break;
    case ROTATE32_DIFFERENT_SOURCE:
	shift_right.e.bin.lhs = &other_source;
	break;
    case ROTATE32_MISSING_OR:
	rotate.e.bin.lhs = &source;
	break;
    case ROTATE32_NONCONSTANT_MODULUS:
	rotate.e.bin.rhs = &other_source;
	break;
    case ROTATE32_NONCONSTANT_LEFT_COUNT:
	shift_left.e.bin.rhs = &other_source;
	break;
    case ROTATE32_NONCONSTANT_RIGHT_COUNT:
	shift_right.e.bin.rhs = &other_source;
	break;
    case ROTATE32_NONCONSTANT_MASK:
	bit_and.e.bin.rhs = &other_source;
	break;
    }
    ret = return_stmt(&rotate);
    (void) lower_stmt(&names, &ret, &ctx, &cfg, &dom, &ssa);
    plan = hir_optimize_ssa_for_backends(ctx, ssa);
    changes = hir_optimization_change_count(plan);
    hir_context_free(ctx);
    return changes;
}

static void
test_rotate32_optimization_matrix(void)
{
    int variant;

    check_int("rotate32 accepts swapped or operands",
	rotate32_variant_change_count(ROTATE32_SWAPPED_OR), 1);
    check_int("rotate32 accepts a leading mask",
	rotate32_variant_change_count(ROTATE32_MASK_FIRST), 1);
    for (variant = ROTATE32_WRONG_MODULUS;
	 variant <= ROTATE32_NONCONSTANT_MASK; variant++)
	check_int("malformed rotate32 pattern rejected",
	    rotate32_variant_change_count((Rotate32Variant) variant), 0);
}

static void
test_constant_folded_branch_clears_bytecode_pc(void)
{
    Names names;
    HIRContext *ctx;
    HIRCFG *cfg;
    HIRDominatorTree *dom;
    HIRSSAProgram *ssa;
    Expr cond, ret_val;
    Stmt body_stmt, loop_stmt;

    memset(&names, 0, sizeof(names));
    names.size = 32;

    /* Build while (1) return 42; endwhile */
    cond = int_expr(1, 90);
    ret_val = int_expr(42, 91);
    body_stmt = return_stmt(&ret_val);
    body_stmt.bytecode_pc = 2;

    memset(&loop_stmt, 0, sizeof(loop_stmt));
    loop_stmt.kind = STMT_WHILE;
    loop_stmt.lineno = 90;
    loop_stmt.bytecode_pc = 0;
    loop_stmt.s.loop.id = -1;
    loop_stmt.s.loop.condition = &cond;
    loop_stmt.s.loop.body = &body_stmt;

    (void) lower_stmt(&names, &loop_stmt, &ctx, &cfg, &dom, &ssa);
    check_int("constant while loop ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("constant while loop has branch before opt",
	      hir_ssa_count_kind(ssa, HIR_TAC_BRANCH_FALSE), 1);
    check_int("constant while loop has branch anchor before opt",
	      hir_ssa_count_bytecode_pc(ssa, 0), 2);

    (void) hir_optimize_ssa_constants(ctx, ssa);
    check_int("constant while loop opt ssa valid", hir_verify_ssa(ctx, ssa), 1);
    check_int("constant while loop branch folded",
	      hir_ssa_count_kind(ssa, HIR_TAC_BRANCH_FALSE), 0);
    check_int("folded branch clears branch bytecode_pc anchor",
	      hir_ssa_count_bytecode_pc(ssa, 0), 1);
    check_int("folded branch destroys ssa", hir_destroy_ssa(ctx, ssa), 1);
    check_int("folded branch verifies out of ssa", hir_verify_out_of_ssa(ctx, ssa), 1);
    check_int("out-of-ssa form is not analyzed",
	      hir_analyze_ssa_values(ctx, ssa) == 0, 1);
    check_int("out-of-ssa form is not optimized",
	      hir_optimize_ssa_for_backends(ctx, ssa) == 0, 1);

    hir_context_free(ctx);
}

int
main(void)
{
    test_ast_and_operation_tables();
    test_optimized_bytecode_shapes();
    test_null_analysis_accessors();
    test_resume_stack_safety();
    test_resume_stack_shape();
    test_boundary_tick_refunds();
    test_list_tail_ownership_slots();
    test_string_concat_ownership_slots();
    test_string_builtin_length_anchor();
    test_string_add_operand_inference();
    test_binary_type_pair_contracts();
    test_list_operand_inference();
    test_unknown_type_inference();
    test_builtin_result_type_inference();
    test_uninitialized_entry_load_classification();
    test_builtin_entry_types();
    test_arithmetic_and_local_tac();
    test_unary_and_empty_list_tac();
    test_empty_and_discarded_statements();
    test_control_flow_tac();
    test_short_circuit_tac();
    test_constant_analysis_overflow();
    test_integer_arithmetic_model();
    test_constant_analysis_error();
    test_loop_dominator_tree();
    test_while_loop_phi_ssa();
    test_if_else_phi_ssa();
    test_if_then_phi_uses_entry_local_ssa();
    test_dead_if_else_local_has_no_phi();
    test_uninitialized_user_local_is_none_constant();
    test_deopt_live_if_else_local_keeps_phi();
    test_guarded_environment_local_tac_ssa();
    test_multiple_guarded_environment_locals_ssa();
    test_conditional_local_assignment_with_entry_local_analysis();
    test_list_index_tac_ssa();
    test_direct_index_assignment_native();
    test_nested_index_assignment_deopt();
    test_property_index_assignment_deopt();
    test_list_index_in_arithmetic_tac_ssa();
    test_scatter_destructuring_tac_ssa();
    test_optional_rest_scatter_deopt();
    test_optional_scatter_default_lowering();
    test_malformed_scatter_lowering();
    test_list_construction_and_splicing_tac_ssa();
    test_initial_list_splice_anchor();
    test_builtin_call_tac_ssa();
    test_zero_argument_builtin_tac_ssa();
    test_pure_builtin_inlining_tac_ssa();
    test_pure_builtin_inlining_matrix();
    test_string_search_builtin_inlining();
    test_property_read_and_write_tac_ssa();
    test_for_range_loop_tac_ssa();
    test_for_list_loop_tac_ssa();
    test_cond_expr_tac_ssa();
    test_break_and_continue_tac_ssa();
    test_labeled_break_nested_loops_tac_ssa();
    test_labeled_continue_and_unmatched_exits();
    test_range_expr_and_assignment_tac_ssa();
    test_verb_call_tac_ssa();
    test_object_scalars_tac_ssa();
    test_float_scalars_tac_ssa();
    test_string_scalars_tac_ssa();
    test_catch_expr_tac_ssa();
    test_try_except_tac_ssa();
    test_native_error_edge_kinds();
    test_multi_arm_try_except_tac_ssa();
    test_try_finally_tac_ssa();
    test_loop_exit_through_finally_tac_ssa();
    test_fork_stmt_tac_ssa();
    test_fork_body_does_not_reject_enclosing_hir();
    test_length_expr_in_index_tac_ssa();
    test_length_expr_in_stores_and_negatives();
    test_rotate32_optimization();
    test_rotate32_optimization_matrix();
    test_constant_folded_branch_clears_bytecode_pc();
    test_cfg_critical_edge_splitting();
    test_if_else_ssa_destruction();
    test_loop_ssa_destruction();
    test_critical_edge_ssa_destruction();
    test_repeated_local_assignment_ssa();
    test_unreachable_dead_code_and_folded_phi_ssa();
    test_unsupported_tac();
    test_negative_tac_verifier_cases();
    test_negative_tac_verifier_matrix();
    test_negative_cfg_verifier_cases();
    test_negative_cfg_verifier_matrix();
    test_negative_dominator_verifier_cases();
    test_negative_ssa_verifier_cases();
    test_negative_ssa_verifier_matrix();
    test_negative_out_ssa_verifier_matrix();

    return failures ? 1 : 0;
}
