/******************************************************************************
  Copyright (c) 1992, 1995, 1996 Xerox Corporation.  All rights reserved.
  Portions of this code were written by Stephen White, aka ghond.
  Use and copying of this software and preparation of derivative works based
  upon this software are permitted.  Any distribution of this software or
  derivative works must comply with all applicable United States export
  control laws.  This software is made available AS IS, and Xerox Corporation
  makes no warranty about the software, its performance or its conformity to
  any specification.  Any person obtaining a copy of this software is requested
  to send their name and post office or electronic mail address to:
    Pavel Curtis
    Xerox PARC
    3333 Coyote Hill Rd.
    Palo Alto, CA 94304
    Pavel@Xerox.Com
 *****************************************************************************/

#include "ast.h"

#include "my-string.h"

#include "arena.h"
#include "list.h"
#include "log.h"
#include "program.h"
#include "storage.h"
#include "structures.h"
#include "sym_table.h"
#include "utils.h"

static Arena *ast_arena = NULL;

static char **tracked_strings = NULL;
static int tracked_strings_count = 0;
static int tracked_strings_size = 0;

#if FLOATS_ARE_BOXED
static FlBox *tracked_floats = NULL;
static int tracked_floats_count = 0;
static int tracked_floats_size = 0;
#endif

static void
track_string(char *str)
{
    if (tracked_strings_count >= tracked_strings_size) {
	tracked_strings_size =
	    tracked_strings_size == 0 ? 16 : tracked_strings_size * 2;
	tracked_strings = myrealloc(tracked_strings,
				    tracked_strings_size * sizeof(char *),
				    M_AST_POOL);
    }
    tracked_strings[tracked_strings_count++] = str;
}

#if FLOATS_ARE_BOXED
static void
track_float(FlBox fnum)
{
    if (tracked_floats_count >= tracked_floats_size) {
	tracked_floats_size = tracked_floats_size == 0 ? 8 : tracked_floats_size * 2;
	tracked_floats = myrealloc(tracked_floats,
				   tracked_floats_size * sizeof(FlBox),
				   M_AST_POOL);
    }
    tracked_floats[tracked_floats_count++] = fnum;
}
#endif

static void
release_ast(void)
{
    int i;

    for (i = 0; i < tracked_strings_count; i++)
	free_str(tracked_strings[i]);

#if FLOATS_ARE_BOXED
    for (i = 0; i < tracked_floats_count; i++) {
	Var value;

	value.type = TYPE_FLOAT;
	value.v.fnum = tracked_floats[i];
	free_var(value);
    }
#endif

    if (tracked_strings) {
	myfree(tracked_strings, M_AST_POOL);
	tracked_strings = NULL;
    }
    tracked_strings_count = 0;
    tracked_strings_size = 0;

#if FLOATS_ARE_BOXED
    if (tracked_floats) {
	myfree(tracked_floats, M_AST_POOL);
	tracked_floats = NULL;
    }
    tracked_floats_count = 0;
    tracked_floats_size = 0;
#endif

    if (ast_arena) {
	arena_destroy(ast_arena);
	ast_arena = NULL;
    }
}

void
begin_code_allocation(void)
{
    ast_arena = arena_create(4096, M_AST_POOL);
}

void
end_code_allocation(int aborted)
{
    if (aborted)
	release_ast();
}

static inline void *
allocate(int size, Memory_Type type)
{
    if (type == M_STRING) {
	char *str = mymalloc(size, M_STRING);
	track_string(str);
	return str;
    }
    (void)type;
    return arena_alloc(ast_arena, size);
}

char *
alloc_string(const char *buffer)
{
    char *string = allocate(strlen(buffer) + 1, M_STRING);

    strcpy(string, buffer);
    return string;
}

void
dealloc_string(char *str)
{
    int i;
    /* Backwards; most strings are released right after they're added */
    for (i = tracked_strings_count; i-- > 0;) {
	if (tracked_strings[i] == str) {
	    free_str(str);
	    tracked_strings[i] = tracked_strings[--tracked_strings_count];
	    return;
	}
    }
    free_str(str);
}

#if FLOATS_ARE_BOXED

FlBox
astpool_recv_float(FlBox fnump)
{
    track_float(fnump);
    return fnump;
}

/*
 *  Theoretically, we could also use the rigorously correct version of
 *
    void flbox_negate_in_place(FlBox *fp)
    {
	FlBox fpnew = allocate(sizeof(FlNum), M_FLOAT);
	*fpnew = -fl_unbox(*fp);
	deallocate(*fp);
	*fp = fpnew;
    }
 *  except this is unbelievably painful behind the scenes and would
 *  *still* fail if floats were interned because end_code_allocation()
 *  does not check reference counts in the 'aborted' case.
 */
#endif	/* FLOATS_ARE_BOXED */

Var
astpool_ref_var(Var value)
{
    value = var_ref(value);

    if (value.type == TYPE_STR)
	track_string((char *) value.v.str);
#if FLOATS_ARE_BOXED
    else if (value.type == TYPE_FLOAT)
	track_float(value.v.fnum);
#endif

    return value;
}

Stmt *
alloc_stmt(enum Stmt_Kind kind)
{
    Stmt *result = allocate(sizeof(Stmt), M_AST);

    result->kind = kind;
    result->next = 0;
    return result;
}

Cond_Arm *
alloc_cond_arm(Expr * condition, Stmt * stmt)
{
    Cond_Arm *result = allocate(sizeof(Cond_Arm), M_AST);

    result->condition = condition;
    result->stmt = stmt;
    result->next = 0;
    return result;
}

Except_Arm *
alloc_except(int id, Arg_List * codes, Stmt * stmt)
{
    Except_Arm *result = allocate(sizeof(Except_Arm), M_AST);

    result->id = id;
    result->codes = codes;
    result->stmt = stmt;
    result->label = 0;
    result->next = 0;
    return result;
}

Expr *
alloc_expr(enum Expr_Kind kind)
{
    Expr *result = allocate(sizeof(Expr), M_AST);

    result->kind = kind;
    return result;
}

Expr *
alloc_var(var_type type)
{
    Expr *result = alloc_expr(EXPR_VAR);

    result->e.var.type = type;
    return result;
}

Expr *
alloc_binary(enum Expr_Kind kind, Expr * lhs, Expr * rhs)
{
    Expr *result = alloc_expr(kind);

    result->e.bin.lhs = lhs;
    result->e.bin.rhs = rhs;
    return result;
}

Expr *
alloc_verb(Expr * obj, Expr * verb, Arg_List * args)
{
    Expr *result = alloc_expr(EXPR_VERB);

    result->e.verb.obj = obj;
    result->e.verb.verb = verb;
    result->e.verb.args = args;
    return result;
}

Arg_List *
alloc_arg_list(enum Arg_Kind kind, Expr * expr)
{
    Arg_List *result = allocate(sizeof(Arg_List), M_AST);

    result->kind = kind;
    result->expr = expr;
    result->next = 0;
    return result;
}

Scatter *
alloc_scatter(enum Scatter_Kind kind, int id, Expr * expr)
{
    Scatter *sc = allocate(sizeof(Scatter), M_AST);

    sc->kind = kind;
    sc->id = id;
    sc->expr = expr;
    sc->next = 0;
    sc->label = sc->next_label = 0;

    return sc;
}

static void assign_expr_resume_ids(Expr *, unsigned *, unsigned *);

static void
assign_arg_list_resume_ids(Arg_List * args, unsigned *current_site,
			   unsigned *next_code_unit)
{
    for (; args; args = args->next)
	assign_expr_resume_ids(args->expr, current_site, next_code_unit);
}

static void
assign_expr_resume_ids(Expr * expr, unsigned *current_site,
		       unsigned *next_code_unit)
{
    if (!expr)
	return;

    switch (expr->kind) {
    case EXPR_VAR:
    case EXPR_ID:
    case EXPR_LENGTH:
	break;
    case EXPR_PROP:
    case EXPR_INDEX:
    case EXPR_EQ:
    case EXPR_NE:
    case EXPR_LT:
    case EXPR_LE:
    case EXPR_GT:
    case EXPR_GE:
    case EXPR_IN:
    case EXPR_PLUS:
    case EXPR_MINUS:
    case EXPR_TIMES:
    case EXPR_DIVIDE:
    case EXPR_MOD:
    case EXPR_EXP:
    case EXPR_AND:
    case EXPR_OR:
    case EXPR_BITOR:
    case EXPR_BITXOR:
    case EXPR_BITAND:
    case EXPR_SHL:
    case EXPR_SHR:
    case EXPR_LSHR:
	assign_expr_resume_ids(expr->e.bin.lhs, current_site,
			       next_code_unit);
	assign_expr_resume_ids(expr->e.bin.rhs, current_site,
			       next_code_unit);
	break;
    case EXPR_RANGE:
	assign_expr_resume_ids(expr->e.range.base, current_site,
			       next_code_unit);
	assign_expr_resume_ids(expr->e.range.from, current_site,
			       next_code_unit);
	assign_expr_resume_ids(expr->e.range.to, current_site,
			       next_code_unit);
	break;
    case EXPR_ASGN:
	if (expr->e.bin.lhs->kind == EXPR_SCATTER) {
	    Scatter *sc;

	    assign_expr_resume_ids(expr->e.bin.rhs, current_site,
				   next_code_unit);
	    for (sc = expr->e.bin.lhs->e.scatter; sc; sc = sc->next)
		if (sc->expr)
		    assign_expr_resume_ids(sc->expr, current_site,
					   next_code_unit);
	} else {
	    assign_expr_resume_ids(expr->e.bin.lhs, current_site,
				   next_code_unit);
	    assign_expr_resume_ids(expr->e.bin.rhs, current_site,
				   next_code_unit);
	}
	break;
    case EXPR_CALL:
	assign_arg_list_resume_ids(expr->e.call.args, current_site,
				   next_code_unit);
	expr->e.call.resume_site = (*current_site)++;
	break;
    case EXPR_VERB:
	assign_expr_resume_ids(expr->e.verb.obj, current_site,
			       next_code_unit);
	assign_expr_resume_ids(expr->e.verb.verb, current_site,
			       next_code_unit);
	assign_arg_list_resume_ids(expr->e.verb.args, current_site,
				   next_code_unit);
	expr->e.verb.resume_site = (*current_site)++;
	break;
    case EXPR_NEGATE:
    case EXPR_NOT:
    case EXPR_COMPLEMENT:
	assign_expr_resume_ids(expr->e.expr, current_site, next_code_unit);
	break;
    case EXPR_LIST:
	assign_arg_list_resume_ids(expr->e.list, current_site, next_code_unit);
	break;
    case EXPR_COND:
	assign_expr_resume_ids(expr->e.cond.condition, current_site,
			       next_code_unit);
	assign_expr_resume_ids(expr->e.cond.consequent, current_site,
			       next_code_unit);
	assign_expr_resume_ids(expr->e.cond.alternate, current_site,
			       next_code_unit);
	break;
    case EXPR_CATCH:
	assign_expr_resume_ids(expr->e.catch.try, current_site,
			       next_code_unit);
	assign_arg_list_resume_ids(expr->e.catch.codes, current_site,
				   next_code_unit);
	assign_expr_resume_ids(expr->e.catch.except, current_site,
			       next_code_unit);
	break;
    case EXPR_SCATTER:
	/* Handled as the left-hand side of EXPR_ASGN. */
	break;
    default:
	panic("Unknown expression kind in ASSIGN_EXPR_RESUME_IDS()");
    }
}

static void
assign_stmt_resume_ids(Stmt * stmt, unsigned *current_site,
		       unsigned *next_code_unit)
{
    for (; stmt; stmt = stmt->next) {
	switch (stmt->kind) {
	case STMT_COND:
	    {
		Cond_Arm *arm;

		for (arm = stmt->s.cond.arms; arm; arm = arm->next) {
		    assign_expr_resume_ids(arm->condition, current_site,
					   next_code_unit);
		    assign_stmt_resume_ids(arm->stmt, current_site,
					   next_code_unit);
		}
		assign_stmt_resume_ids(stmt->s.cond.otherwise, current_site,
				       next_code_unit);
	    }
	    break;
	case STMT_LIST:
	    assign_expr_resume_ids(stmt->s.list.expr, current_site,
				   next_code_unit);
	    assign_stmt_resume_ids(stmt->s.list.body, current_site,
				   next_code_unit);
	    break;
	case STMT_RANGE:
	    assign_expr_resume_ids(stmt->s.range.from, current_site,
				   next_code_unit);
	    assign_expr_resume_ids(stmt->s.range.to, current_site,
				   next_code_unit);
	    assign_stmt_resume_ids(stmt->s.range.body, current_site,
				   next_code_unit);
	    break;
	case STMT_WHILE:
	    assign_expr_resume_ids(stmt->s.loop.condition, current_site,
				   next_code_unit);
	    assign_stmt_resume_ids(stmt->s.loop.body, current_site,
				   next_code_unit);
	    break;
	case STMT_FORK:
	    {
		unsigned fork_site = 1;

		assign_expr_resume_ids(stmt->s.fork.time, current_site,
				       next_code_unit);
		stmt->s.fork.code_unit = (*next_code_unit)++;
		assign_stmt_resume_ids(stmt->s.fork.body, &fork_site,
				       next_code_unit);
	    }
	    break;
	case STMT_EXPR:
	case STMT_RETURN:
	    assign_expr_resume_ids(stmt->s.expr, current_site,
				   next_code_unit);
	    break;
	case STMT_TRY_EXCEPT:
	    {
		Except_Arm *except;

		assign_stmt_resume_ids(stmt->s.catch.body, current_site,
				       next_code_unit);
		for (except = stmt->s.catch.excepts; except;
		     except = except->next) {
		    assign_arg_list_resume_ids(except->codes, current_site,
					       next_code_unit);
		    assign_stmt_resume_ids(except->stmt, current_site,
					   next_code_unit);
		}
	    }
	    break;
	case STMT_TRY_FINALLY:
	    assign_stmt_resume_ids(stmt->s.finally.body, current_site,
				   next_code_unit);
	    assign_stmt_resume_ids(stmt->s.finally.handler, current_site,
				   next_code_unit);
	    break;
	case STMT_BREAK:
	case STMT_CONTINUE:
	    break;
	default:
	    panic("Unknown statement kind in ASSIGN_STMT_RESUME_IDS()");
	}
    }
}

void
assign_resume_ids(Stmt * stmt)
{
    unsigned current_site = 1, next_code_unit = 1;

    assign_stmt_resume_ids(stmt, &current_site, &next_code_unit);
}

void
free_stmt(Stmt * stmt UNUSED_)
{
    release_ast();
}


/*
 * $Log$
 * Revision 2.4  1996/02/08  07:11:54  pavel
 * Updated copyright notice for 1996.  Release 1.8.0beta1 (again).
 *
 * Revision 2.3  1996/02/08  05:49:08  pavel
 * Renamed err/logf() to errlog/oklog().  Added support for floating-point and
 * the X^Y expression.  Added named WHILE loops and the BREAK and CONTINUE
 * statements.  Release 1.8.0beta1.
 *
 * Revision 2.2  1996/01/16  07:11:46  pavel
 * Added alloc/free for scatters.  Release 1.8.0alpha6.
 *
 * Revision 2.1  1995/12/31  03:14:13  pavel
 * Added EXPR_LENGTH case to free_expr().  Release 1.8.0alpha4.
 *
 * Revision 2.0  1995/11/30  04:16:25  pavel
 * New baseline version, corresponding to release 1.8.0alpha1.
 *
 * Revision 1.12  1992/10/23  23:03:47  pavel
 * Added copyright notice.
 *
 * Revision 1.11  1992/10/23  19:16:20  pavel
 * Eliminated all uses of the useless macro NULL.
 *
 * Revision 1.10  1992/10/21  03:02:35  pavel
 * Converted to use new automatic configuration system.
 *
 * Revision 1.9  1992/08/31  22:21:28  pjames
 * Changed some `char *'s to `const char *'
 *
 * Revision 1.8  1992/08/28  23:12:13  pjames
 * Added ASGN_RANGE arm of `free_expr()'.
 *
 * Revision 1.7  1992/08/28  16:11:25  pjames
 * Changed myfree(*, M_STRING) to free_str(*).
 * Removed free_ast_var.  Use free_var instead.
 * Removed ak_dealloc_string.  Use free_str instead.
 *
 * Revision 1.6  1992/08/14  00:01:17  pavel
 * Converted to a typedef of `var_type' = `enum var_type'.
 *
 * Revision 1.5  1992/08/10  16:53:07  pjames
 * Updated #includes.
 *
 * Revision 1.4  1992/07/30  21:20:25  pjames
 * Checks for NULL before freeing M_STRINGS.
 *
 * Revision 1.3  1992/07/27  17:57:06  pjames
 * Changed myfree(*, M_AST) to (*, M_STRING) when * was a (char *)
 * because that is how they are allocated.
 *
 * Revision 1.2  1992/07/20  23:48:48  pavel
 * Added rcsid_<filename-root> declaration to hold the RCS identification
 * string.
 *
 * Revision 1.1  1992/07/20  23:23:12  pavel
 * Initial RCS-controlled version.
 */
