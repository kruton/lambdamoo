/******************************************************************************
  Copyright (c) 1994, 1995, 1996 Xerox Corporation.  All rights reserved.
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

#include "compiler.h"

#include "code_gen.h"
#include "hir.h"
#include "storage.h"

Program *
compile_ast_to_program(Stmt * ast, Names * var_names, DB_Version version)
{
    HIRContext *hir_ctx;
    HIRProgram *hir_program;
    HIRTacProgram *tac_program;
    Program *program;

    assign_resume_ids(ast);
    hir_ctx = hir_context_new(var_names);
    hir_program = hir_lift_ast(hir_ctx, ast);
    tac_program = hir_lower_to_tac(hir_ctx, hir_program);
    (void) tac_program;
    hir_context_free(hir_ctx);

    program = generate_code(ast, version);

    program->num_var_names = var_names->size;
    program->var_names = var_names->names;

    myfree(var_names, M_NAMES);
    free_stmt(ast);

    return program;
}
