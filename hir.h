#ifndef HIR_h
#define HIR_h 1

#include "ast.h"
#include "structures.h"
#include "sym_table.h"

typedef struct HIRContext HIRContext;
typedef struct HIRProgram HIRProgram;
typedef struct HIRTacProgram HIRTacProgram;
typedef struct HIRCFG HIRCFG;
typedef struct HIRDominatorTree HIRDominatorTree;
typedef struct HIRBlockList HIRBlockList;
typedef struct HIRSSAProgram HIRSSAProgram;

typedef enum {
    HIR_TYPE_INT,
    HIR_TYPE_FLOAT,
    HIR_TYPE_STR,
    HIR_TYPE_LIST,
    HIR_TYPE_OBJ,
    HIR_TYPE_ERR,
    HIR_TYPE_ANY
} HIRTypeTag;

typedef enum {
    HIR_EXPR_LITERAL,
    HIR_EXPR_LOCAL_LOAD,
    HIR_EXPR_LOCAL_STORE,
    HIR_EXPR_UNARY,
    HIR_EXPR_BINARY,
    HIR_EXPR_COND,
    HIR_EXPR_CALL,
    HIR_EXPR_VERB_CALL,
    HIR_EXPR_PROP,
    HIR_EXPR_INDEX,
    HIR_EXPR_RANGE,
    HIR_EXPR_LIST,
    HIR_EXPR_CATCH,
    HIR_EXPR_SCATTER,
    HIR_EXPR_UNSUPPORTED
} HIRExprKind;

typedef enum {
    HIR_STMT_SEQUENCE,
    HIR_STMT_EXPR,
    HIR_STMT_RETURN,
    HIR_STMT_IF,
    HIR_STMT_WHILE,
    HIR_STMT_FOR_LIST,
    HIR_STMT_FOR_RANGE,
    HIR_STMT_FORK,
    HIR_STMT_TRY_EXCEPT,
    HIR_STMT_TRY_FINALLY,
    HIR_STMT_BREAK,
    HIR_STMT_CONTINUE,
    HIR_STMT_UNSUPPORTED
} HIRStmtKind;

typedef enum {
    HIR_OP_NEGATE,
    HIR_OP_NOT,
    HIR_OP_COMPLEMENT,
    HIR_OP_ADD,
    HIR_OP_SUB,
    HIR_OP_MUL,
    HIR_OP_DIV,
    HIR_OP_MOD,
    HIR_OP_EXP,
    HIR_OP_EQ,
    HIR_OP_NE,
    HIR_OP_LT,
    HIR_OP_LE,
    HIR_OP_GT,
    HIR_OP_GE,
    HIR_OP_IN,
    HIR_OP_AND,
    HIR_OP_OR,
    HIR_OP_BITOR,
    HIR_OP_BITXOR,
    HIR_OP_BITAND,
    HIR_OP_SHL,
    HIR_OP_SHR,
    HIR_OP_LSHR
} HIROp;

typedef enum {
    HIR_TAC_CONST,
    HIR_TAC_LOAD_LOCAL,
    HIR_TAC_STORE_LOCAL,
    HIR_TAC_UNARY,
    HIR_TAC_BINARY,
    HIR_TAC_LABEL,
    HIR_TAC_JUMP,
    HIR_TAC_BRANCH_FALSE,
    HIR_TAC_RETURN,
    HIR_TAC_RETURN0,
    HIR_TAC_UNSUPPORTED,
    HIR_TAC_PHI
} HIRTacKind;

extern HIRContext *hir_context_new(Names *);
extern void hir_context_free(HIRContext *);
extern int hir_context_error_count(HIRContext *);
extern const char *hir_context_error_message(HIRContext *);

extern HIRProgram *hir_lift_ast(HIRContext *, Stmt *);
extern HIRTacProgram *hir_lower_to_tac(HIRContext *, HIRProgram *);
extern int hir_verify_tac(HIRContext *, HIRTacProgram *);
extern HIRCFG *hir_build_cfg(HIRContext *, HIRTacProgram *);
extern int hir_verify_cfg(HIRContext *, HIRCFG *);
extern HIRDominatorTree *hir_build_dominator_tree(HIRContext *, HIRCFG *);
extern int hir_verify_dominator_tree(HIRContext *, HIRCFG *,
				     HIRDominatorTree *);
extern HIRSSAProgram *hir_build_ssa(HIRContext *, HIRCFG *);
extern int hir_verify_ssa(HIRContext *, HIRSSAProgram *);

#ifdef HIR_DUMP_TAC
extern void hir_dump_tac(HIRTacProgram *);
#endif

#ifdef HIR_TESTING
extern int hir_tac_count_kind(HIRTacProgram *, HIRTacKind);
extern int hir_tac_count_binary_op(HIRTacProgram *, HIROp);
extern int hir_tac_instruction_count(HIRTacProgram *);
extern int hir_tac_count_lineno(HIRTacProgram *, unsigned);
extern int hir_cfg_block_count(HIRCFG *);
extern int hir_cfg_edge_count(HIRCFG *);
extern int hir_cfg_unsupported_block_count(HIRCFG *);
extern int hir_dom_reachable_block_count(HIRDominatorTree *);
extern int hir_dom_idom_block(HIRDominatorTree *, int);
extern int hir_dom_df_count(HIRDominatorTree *, int);
extern int hir_ssa_block_count(HIRSSAProgram *);
extern int hir_ssa_instruction_count(HIRSSAProgram *);
extern int hir_ssa_value_count(HIRSSAProgram *);
extern int hir_ssa_count_kind(HIRSSAProgram *, HIRTacKind);
extern int hir_ssa_phi_arg_count(HIRSSAProgram *);
extern int hir_ssa_zero_phi_arg_count(HIRSSAProgram *);
extern int hir_ssa_return_uses_phi_count(HIRSSAProgram *);
extern int hir_ssa_branch_uses_phi_count(HIRSSAProgram *);
extern int hir_ssa_binary_uses_phi_count(HIRSSAProgram *, HIROp);
extern HIRTacProgram *hir_test_tac_with_undefined_return(HIRContext *);
extern HIRTacProgram *hir_test_tac_with_duplicate_temp(HIRContext *);
extern HIRCFG *hir_test_cfg_with_missing_successor(HIRContext *);
extern HIRCFG *hir_test_cfg_with_external_successor(HIRContext *);
extern HIRCFG *hir_test_cfg_with_predecessor_mismatch(HIRContext *);
extern HIRCFG *hir_test_cfg_with_duplicate_block_id(HIRContext *);
extern HIRSSAProgram *hir_test_ssa_with_use_before_def(HIRContext *);
extern HIRSSAProgram *hir_test_ssa_with_duplicate_def(HIRContext *);
extern HIRSSAProgram *hir_test_ssa_with_bad_phi_shape(HIRContext *);
extern HIRSSAProgram *hir_test_ssa_with_late_phi(HIRContext *);
extern HIRSSAProgram *hir_test_ssa_with_missing_phi_arg(HIRContext *);
extern HIRSSAProgram *hir_test_ssa_with_nonpred_phi_arg(HIRContext *);
#endif

#endif /* !HIR_h */
