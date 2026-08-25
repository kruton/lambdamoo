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

#include "config.h"
#include "options.h"

#include "code_gen.h"
#include "hir.h"
#ifdef ENABLE_JIT
#include "jit.h"
#endif
#include "storage.h"

Program *
compile_ast_to_program(Stmt * ast, Names * var_names, DB_Version version)
{
    HIRContext *hir_ctx;
    HIRProgram *hir_program;
    HIRTacProgram *tac_program;
    HIRCFG *cfg;
    HIRDominatorTree *dom_tree;
    HIRSSAProgram *ssa_program;
    Program *program;
    int hir_valid;
    int hir_supported;
#ifdef ENABLE_JIT
    JITProgram *jit_program;
#endif

    assign_resume_ids(ast);
    hir_ctx = hir_context_new(var_names);
    hir_program = hir_lift_ast(hir_ctx, ast);
    tac_program = hir_lower_to_tac(hir_ctx, hir_program);
    hir_supported = hir_context_error_count(hir_ctx) == 0;
    hir_valid = hir_supported;
    hir_valid = hir_verify_tac(hir_ctx, tac_program) && hir_valid;
    cfg = hir_build_cfg(hir_ctx, tac_program);
    hir_valid = hir_verify_cfg(hir_ctx, cfg) && hir_valid;
    dom_tree = hir_build_dominator_tree(hir_ctx, cfg);
    hir_valid = hir_verify_dominator_tree(hir_ctx, cfg, dom_tree) && hir_valid;
    ssa_program = hir_build_ssa(hir_ctx, cfg);
    hir_valid = hir_verify_ssa(hir_ctx, ssa_program) && hir_valid;
    if (hir_valid)
	hir_valid = hir_destroy_ssa(hir_ctx, ssa_program)
	    && hir_verify_out_of_ssa(hir_ctx, ssa_program);
#ifdef ENABLE_JIT
    if (hir_valid)
	jit_program = hir_create_jit_program(hir_ctx, ssa_program);
    else
	jit_program = jit_program_unsupported(hir_supported
					      ? "invalid-ir"
					      : "unsupported-program");
#else
    (void) hir_valid;
    (void) hir_supported;
#endif
#ifdef HIR_DUMP_TAC
    hir_dump_tac(tac_program);
#endif
#ifdef HIR_DUMP_SSA
    hir_dump_ssa(ssa_program);
#endif
    (void) ssa_program;
    (void) dom_tree;
    (void) cfg;
    (void) tac_program;
    hir_context_free(hir_ctx);

    program = generate_code(ast, version);

#ifdef ENABLE_JIT
    program->jit = jit_program;
#endif

    program->num_var_names = var_names->size;
    program->var_names = var_names->names;

    myfree(var_names, M_NAMES);
    free_stmt(ast);

    return program;
}
