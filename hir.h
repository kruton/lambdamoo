#ifndef HIR_h
#define HIR_h 1

#include "ast.h"
#include "structures.h"
#include "sym_table.h"

typedef struct HIRContext HIRContext;
typedef struct HIRProgram HIRProgram;
typedef struct HIRTacProgram HIRTacProgram;

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
    HIR_TAC_UNSUPPORTED
} HIRTacKind;

extern HIRContext *hir_context_new(Names *);
extern void hir_context_free(HIRContext *);
extern int hir_context_error_count(HIRContext *);
extern const char *hir_context_error_message(HIRContext *);

extern HIRProgram *hir_lift_ast(HIRContext *, Stmt *);
extern HIRTacProgram *hir_lower_to_tac(HIRContext *, HIRProgram *);
extern int hir_verify_tac(HIRContext *, HIRTacProgram *);

#ifdef HIR_DUMP_TAC
extern void hir_dump_tac(HIRTacProgram *);
#endif

#endif /* !HIR_h */
