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
#include "decompile.h"
#include "hir.h"
#ifdef ENABLE_JIT
#include "jit.h"
#endif
#include "storage.h"
#include "sym_table.h"

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
    program = generate_code(ast, version);
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
    if (hir_valid) {
	(void) hir_optimize_ssa_constants(hir_ctx, ssa_program);
	hir_valid = hir_verify_ssa(hir_ctx, ssa_program) && hir_valid;
    }
    if (hir_valid)
	hir_valid = hir_destroy_ssa(hir_ctx, ssa_program)
	    && hir_verify_out_of_ssa(hir_ctx, ssa_program);
#ifdef ENABLE_JIT
    if (hir_valid)
	jit_program = hir_create_jit_program(hir_ctx, ssa_program, program);
    else {
	const char *reason = hir_supported ? "invalid-ir" : "unsupported-program";
	const char *diag = hir_context_error_message(hir_ctx);
	jit_program = jit_program_unsupported_with_diagnostic(reason, diag);
    }
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

#ifdef ENABLE_JIT
    program->jit = jit_program;
#endif

    program->num_var_names = var_names->size;
    program->var_names = var_names->names;

    myfree(var_names, M_NAMES);
    free_stmt(ast);

    return program;
}

#ifdef ENABLE_JIT
JITProgram *
compile_program_to_jit(Program *source)
{
    Names *names;
    Program *copy;
    JITProgram *jit;
    unsigned i;

    if (!source)
	return 0;
    names = new_builtin_names(source->version);
    for (i = names->size; i < source->num_var_names; i++)
	if (find_or_add_name(&names, source->var_names[i]) != i) {
	    free_names(names);
	    return 0;
	}
    copy = compile_ast_to_program(decompile_program(source, MAIN_VECTOR),
				  names, source->version);
    if (!copy)
	return 0;
    jit = copy->jit;
    copy->jit = 0;
    free_program(copy);
    return jit;
}
#endif
