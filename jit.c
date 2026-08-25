#include "jit.h"

#include "config.h"
#include "options.h"

#include "my-stdio.h"

#include "jit_internal.h"
#include "storage.h"

#include "mir.h"
#include "mir-gen.h"

#include <stddef.h>
#include <string.h>

typedef int64_t (*NativeFunction) (Var *, Var *, int *, int *);

typedef struct {
    MIR_context_t context;
    MIR_module_t module;
    MIR_item_t function;
} MIRBuild;

static void
append(MIRBuild *build, MIR_insn_t instruction)
{
    MIR_append_insn(build->context, build->function, instruction);
}

static MIR_reg_t
new_reg(MIRBuild *build, const char *name)
{
    return MIR_new_func_reg(build->context, build->function->u.func,
			    MIR_T_I64, name);
}

static MIR_insn_code_t
binary_code(HIROp op)
{
    switch (op) {
    case HIR_OP_ADD:
	return MIR_ADD;
    case HIR_OP_SUB:
	return MIR_SUB;
    case HIR_OP_MUL:
	return MIR_MUL;
    case HIR_OP_EQ:
	return MIR_EQ;
    case HIR_OP_NE:
	return MIR_NE;
    case HIR_OP_LT:
	return MIR_LT;
    case HIR_OP_LE:
	return MIR_LE;
    case HIR_OP_GT:
	return MIR_GT;
    case HIR_OP_GE:
	return MIR_GE;
    default:
	return MIR_INVALID_INSN;
    }
}

static void
finish_build(MIRBuild *build)
{
    MIR_finish_func(build->context);
    MIR_finish_module(build->context);
}

static int
build_mir(JITProgram *program, MIRBuild *build)
{
    MIR_type_t result_type = MIR_T_I64;
    MIR_reg_t env, result, ticks, timed_out, tick_result, timeout_value;
    MIR_reg_t *values;
    MIR_label_t *labels;
    MIR_label_t fallback, tick_abort, seconds_abort;
    JITBlock *block;
    int max_block_id = 0;
    int i;

    memset(build, 0, sizeof(MIRBuild));
    build->context = MIR_init();
    if (!build->context)
	return 0;
    build->module = MIR_new_module(build->context, "lambda_moo_jit");
    build->function = MIR_new_func(build->context, "jit_verb", 1,
				   &result_type, 4,
				   MIR_T_P, "env", MIR_T_P, "result",
				   MIR_T_P, "ticks", MIR_T_P, "timed_out");
    env = MIR_reg(build->context, "env", build->function->u.func);
    result = MIR_reg(build->context, "result", build->function->u.func);
    ticks = MIR_reg(build->context, "ticks", build->function->u.func);
    timed_out = MIR_reg(build->context, "timed_out", build->function->u.func);
    tick_result = new_reg(build, "tick_result");
    timeout_value = new_reg(build, "timeout_value");
    fallback = MIR_new_label(build->context);
    tick_abort = MIR_new_label(build->context);
    seconds_abort = MIR_new_label(build->context);

    values = mymalloc(sizeof(MIR_reg_t) * program->num_values, M_PROGRAM);
    memset(values, 0, sizeof(MIR_reg_t) * program->num_values);
    for (i = 1; i < program->num_values; i++) {
	char name[32];
	sprintf(name, "v%d", i);
	values[i] = new_reg(build, name);
    }
    for (block = program->blocks; block; block = block->next)
	if (block->id > max_block_id)
	    max_block_id = block->id;
    labels = mymalloc(sizeof(MIR_label_t) * (max_block_id + 1), M_PROGRAM);
    memset(labels, 0, sizeof(MIR_label_t) * (max_block_id + 1));
    for (block = program->blocks; block; block = block->next)
	labels[block->id] = MIR_new_label(build->context);

    for (block = program->blocks; block; block = block->next) {
	    JITInstruction *instr;

	    append(build, labels[block->id]);
	    for (instr = block->first; instr; instr = instr->next) {
		switch (instr->kind) {
		case HIR_TAC_TICK:
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_mem_op(build->context, MIR_T_I32,
								 0, ticks, 0, 1)));
		    append(build, MIR_new_insn(build->context, MIR_SUB,
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_int_op(build->context, 1)));
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context, MIR_T_I32,
								 0, ticks, 0, 1),
						  MIR_new_reg_op(build->context,
								 tick_result)));
		    append(build, MIR_new_insn(build->context, MIR_BLE,
						  MIR_new_label_op(build->context,
								   tick_abort),
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_int_op(build->context, 0)));
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 timeout_value),
						  MIR_new_mem_op(build->context, MIR_T_I32,
								 0, timed_out, 0, 1)));
		    append(build, MIR_new_insn(build->context, MIR_BT,
						  MIR_new_label_op(build->context,
								   seconds_abort),
						  MIR_new_reg_op(build->context,
								 timeout_value)));
		    break;
		case HIR_TAC_CONST:
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_int_op(build->context,
								 instr->literal)));
		    break;
		case HIR_TAC_LOAD_LOCAL:
		    append(build, MIR_new_insn(build->context, MIR_BNE,
						  MIR_new_label_op(build->context,
								   fallback),
						  MIR_new_mem_op(build->context,
								 MIR_T_I32,
								 instr->local_id * sizeof(Var)
								 + offsetof(Var, type),
								 env, 0, 1),
						  MIR_new_int_op(build->context,
								 TYPE_INT)));
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_mem_op(build->context,
								 sizeof(Num) == 8
								 ? MIR_T_I64 : MIR_T_I32,
								 instr->local_id * sizeof(Var)
								 + offsetof(Var, v.num),
								 env, 0, 1)));
		    break;
		case HIR_TAC_UNARY:
		    if (instr->op == HIR_OP_NEGATE)
			append(build, MIR_new_insn(build->context, MIR_NEG,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1])));
		    else if (instr->op == HIR_OP_NOT)
			append(build, MIR_new_insn(build->context, MIR_EQ,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1]),
						      MIR_new_int_op(build->context, 0)));
		    else
			append(build, MIR_new_insn(build->context, MIR_XOR,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1]),
						      MIR_new_int_op(build->context, -1)));
		    break;
		case HIR_TAC_BINARY:
		    append(build, MIR_new_insn(build->context,
						  binary_code(instr->op),
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_reg_op(build->context,
								 values[instr->src1]),
						  MIR_new_reg_op(build->context,
								 values[instr->src2])));
		    break;
		case HIR_TAC_PARALLEL_COPY:
		    {
			JITCopy *copy;
			int count = 0;
			int n = 0;
			MIR_reg_t *temps;
			for (copy = instr->copies; copy; copy = copy->next)
			    count++;
			temps = mymalloc(sizeof(MIR_reg_t) * count, M_PROGRAM);
			for (copy = instr->copies; copy; copy = copy->next) {
			    char name[32];
			    sprintf(name, "copy%d", n);
			    temps[n] = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
							  MIR_new_reg_op(build->context,
									 temps[n]),
							  MIR_new_reg_op(build->context,
									 values[copy->src])));
			    n++;
			}
			n = 0;
			for (copy = instr->copies; copy; copy = copy->next) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
							  MIR_new_reg_op(build->context,
									 values[copy->dst]),
							  MIR_new_reg_op(build->context,
									 temps[n])));
			    n++;
			}
			myfree(temps, M_PROGRAM);
		    }
		    break;
		case HIR_TAC_JUMP:
		    if (block->num_successors == 1)
			append(build, MIR_new_insn(build->context, MIR_JMP,
						      MIR_new_label_op(build->context,
							 labels[block->successors[0]])));
		    break;
		case HIR_TAC_BRANCH_FALSE:
		    if (block->num_successors == 2) {
			append(build, MIR_new_insn(build->context, MIR_BF,
						      MIR_new_label_op(build->context,
							 labels[block->successors[0]]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1])));
			append(build, MIR_new_insn(build->context, MIR_JMP,
						      MIR_new_label_op(build->context,
							 labels[block->successors[1]])));
		    }
		    break;
		case HIR_TAC_RETURN:
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context,
								 sizeof(Num) == 8
								 ? MIR_T_I64 : MIR_T_I32,
								 offsetof(Var, v.num),
								 result, 0, 1),
						  MIR_new_reg_op(build->context,
								 values[instr->src1])));
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context, MIR_T_I32,
								 offsetof(Var, type), result, 0, 1),
						  MIR_new_int_op(build->context, TYPE_INT)));
		    append(build, MIR_new_ret_insn(build->context, 1,
						      MIR_new_int_op(build->context,
								     JIT_RUN_RETURNED)));
		    break;
		case HIR_TAC_RETURN0:
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context,
								 sizeof(Num) == 8
								 ? MIR_T_I64 : MIR_T_I32,
								 offsetof(Var, v.num), result, 0, 1),
						  MIR_new_int_op(build->context, 0)));
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context, MIR_T_I32,
								 offsetof(Var, type), result, 0, 1),
						  MIR_new_int_op(build->context, TYPE_INT)));
		    append(build, MIR_new_ret_insn(build->context, 1,
						      MIR_new_int_op(build->context,
								     JIT_RUN_RETURNED)));
		    break;
		case HIR_TAC_LABEL:
		case HIR_TAC_STORE_LOCAL:
		case HIR_TAC_UNSUPPORTED:
		case HIR_TAC_PHI:
		    break;
		}
		if (instr == block->last)
		    break;
	    }
	    if ((!block->last || (block->last->kind != HIR_TAC_JUMP
				 && block->last->kind != HIR_TAC_BRANCH_FALSE
				 && block->last->kind != HIR_TAC_RETURN
				 && block->last->kind != HIR_TAC_RETURN0))
		&& block->num_successors == 1)
		append(build, MIR_new_insn(build->context, MIR_JMP,
					    MIR_new_label_op(build->context,
							     labels[block->successors[0]])));
    }

    append(build, fallback);
    append(build, MIR_new_ret_insn(build->context, 1,
				  MIR_new_int_op(build->context,
						 JIT_RUN_FALLBACK)));
    append(build, tick_abort);
    append(build, MIR_new_ret_insn(build->context, 1,
				  MIR_new_int_op(build->context,
						 JIT_RUN_ABORT_TICKS)));
    append(build, seconds_abort);
    append(build, MIR_new_ret_insn(build->context, 1,
				  MIR_new_int_op(build->context,
						 JIT_RUN_ABORT_SECONDS)));
    finish_build(build);
    myfree(labels, M_PROGRAM);
    myfree(values, M_PROGRAM);
    return 1;
}

JITProgram *
jit_program_unsupported(const char *reason)
{
    JITProgram *program = mymalloc(sizeof(JITProgram), M_PROGRAM);

    memset(program, 0, sizeof(JITProgram));
    program->state = JIT_STATE_UNSUPPORTED;
    program->reason = reason;
    return program;
}

void
jit_program_free(JITProgram *program)
{
    JITBlock *block;

    if (!program)
	return;
    if (program->mir_context) {
	MIR_gen_finish((MIR_context_t) program->mir_context);
	MIR_finish((MIR_context_t) program->mir_context);
    }
    block = program->blocks;
    while (block) {
	JITBlock *next_block = block->next;
	JITInstruction *instr = block->first;
	while (instr) {
	    JITInstruction *next_instr = instr->next;
	    JITCopy *copy = instr->copies;
	    while (copy) {
		JITCopy *next_copy = copy->next;
		myfree(copy, M_PROGRAM);
		copy = next_copy;
	    }
	    myfree(instr, M_PROGRAM);
	    instr = next_instr;
	}
	myfree(block, M_PROGRAM);
	block = next_block;
    }
    myfree(program, M_PROGRAM);
}

int
jit_program_bytes(JITProgram *program)
{
    int bytes = 0;
    JITBlock *block;

    if (!program)
	return 0;
    bytes = sizeof(JITProgram);
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;
	bytes += sizeof(JITBlock);
	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;
	    bytes += sizeof(JITInstruction);
	    for (copy = instr->copies; copy; copy = copy->next)
		bytes += sizeof(JITCopy);
	}
    }
    return bytes;
}

JITState
jit_program_state(JITProgram *program)
{
    return program ? program->state : JIT_STATE_UNSUPPORTED;
}

const char *
jit_program_state_name(JITProgram *program)
{
    switch (jit_program_state(program)) {
    case JIT_STATE_PENDING:
	return "pending";
    case JIT_STATE_COMPILED:
	return "compiled";
    case JIT_STATE_UNSUPPORTED:
	return "unsupported";
    case JIT_STATE_FAILED:
	return "failed";
    }
    return "failed";
}

const char *
jit_program_reason(JITProgram *program)
{
    return program ? program->reason : "unsupported-program";
}

int
jit_program_is_eligible(JITProgram *program)
{
    return program && program->eligible;
}

int
jit_program_compile(JITProgram *program)
{
    MIRBuild build;

    if (!program || program->state == JIT_STATE_UNSUPPORTED
	|| program->state == JIT_STATE_FAILED)
	return 0;
    if (program->state == JIT_STATE_COMPILED)
	return 1;
    if (!build_mir(program, &build)) {
	program->state = JIT_STATE_FAILED;
	program->reason = "code-generation-failed";
	return 0;
    }
    MIR_load_module(build.context, build.module);
    MIR_gen_init(build.context);
    MIR_gen_set_optimize_level(build.context, 0);
    program->native_function = MIR_gen(build.context, build.function);
    if (!program->native_function) {
	MIR_gen_finish(build.context);
	MIR_finish(build.context);
	program->state = JIT_STATE_FAILED;
	program->reason = "code-generation-failed";
	return 0;
    }
    program->mir_context = build.context;
    program->state = JIT_STATE_COMPILED;
    return 1;
}

JITRunResult
jit_program_execute(JITProgram *program, Var *env, Var *result,
		    int *ticks, int *timed_out)
{
    NativeFunction function;
    int64_t native_result;

    if (!jit_program_compile(program))
	return JIT_RUN_FALLBACK;
    function = (NativeFunction) program->native_function;
    native_result = function(env, result, ticks, timed_out);
    return native_result;
}

int
jit_program_dump_mir(JITProgram *program, void (*add_line)(const char *, void *),
		     void *data)
{
    MIRBuild build;
    FILE *file;
    char line[1024];

    if (!program || !program->eligible || !build_mir(program, &build))
	return 0;
    file = tmpfile();
    if (!file) {
	MIR_finish(build.context);
	return 0;
    }
    MIR_output_module(build.context, file, build.module);
    rewind(file);
    while (fgets(line, sizeof(line), file)) {
	size_t length = strlen(line);
	if (length && line[length - 1] == '\n')
	    line[length - 1] = '\0';
	add_line(line, data);
    }
    fclose(file);
    MIR_finish(build.context);
    return 1;
}
