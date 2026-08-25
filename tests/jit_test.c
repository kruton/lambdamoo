#include "jit_internal.h"

#include "my-stdio.h"

#include "integer_arithmetic.h"
#include "storage.h"

#include <string.h>

static int failures;

static void check(int, const char *);

static void *
allocate(size_t size)
{
    void *result = mymalloc(size, M_PROGRAM);

    memset(result, 0, size);
    return result;
}

static JITInstruction *
instruction(HIRTacKind kind)
{
    JITInstruction *result = allocate(sizeof(JITInstruction));

    result->kind = kind;
    return result;
}

static JITProgram *
arithmetic_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *one = instruction(HIR_TAC_CONST);
    JITInstruction *two = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *add = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_blocks = 1;
    program->blocks = program->last_block = block;
    block->id = 1;
    one->value = 1;
    one->literal = 1;
    two->value = 2;
    two->literal = 2;
    tick->source_lineno = 7;
    add->value = 3;
    add->src1 = 1;
    add->src2 = 2;
    add->op = HIR_OP_ADD;
    ret->src1 = 3;
    one->next = two;
    two->next = tick;
    tick->next = add;
    add->next = ret;
    block->first = one;
    block->last = ret;
    return program;
}

static JITProgram *
division_program(Num lhs, Num rhs, HIROp op)
{
    JITProgram *program = arithmetic_program();
    JITInstruction *one = program->blocks->first;
    JITInstruction *two = one->next;
    JITInstruction *binary = two->next->next;

    one->literal = lhs;
    two->literal = rhs;
    binary->op = op;
    program->may_error = 1;
    return program;
}

static JITProgram *
guard_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 2;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->next = ret;
    ret->src1 = 1;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
branch_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *entry = allocate(sizeof(JITBlock));
    JITBlock *truth = allocate(sizeof(JITBlock));
    JITBlock *falsehood = allocate(sizeof(JITBlock));
    JITBlock *join = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *branch = instruction(HIR_TAC_BRANCH_FALSE);
    JITInstruction *ten = instruction(HIR_TAC_CONST);
    JITInstruction *truth_copy = instruction(HIR_TAC_PARALLEL_COPY);
    JITInstruction *truth_jump = instruction(HIR_TAC_JUMP);
    JITInstruction *twenty = instruction(HIR_TAC_CONST);
    JITInstruction *false_copy = instruction(HIR_TAC_PARALLEL_COPY);
    JITInstruction *false_jump = instruction(HIR_TAC_JUMP);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITCopy *copy1 = allocate(sizeof(JITCopy));
    JITCopy *copy2 = allocate(sizeof(JITCopy));

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 5;
    program->num_vars = 1;
    program->num_blocks = 4;
    program->blocks = entry;
    program->last_block = join;
    entry->id = 1;
    entry->successors[0] = 3;
    entry->successors[1] = 2;
    entry->num_successors = 2;
    entry->next = truth;
    load->value = 1;
    load->local_id = 0;
    load->next = tick;
    tick->next = branch;
    branch->src1 = 1;
    entry->first = load;
    entry->last = branch;
    truth->id = 2;
    truth->successors[0] = 4;
    truth->num_successors = 1;
    truth->next = falsehood;
    ten->value = 2;
    ten->literal = 10;
    ten->next = truth_copy;
    copy1->dst = 4;
    copy1->src = 2;
    truth_copy->copies = copy1;
    truth_copy->next = truth_jump;
    truth->first = ten;
    truth->last = truth_jump;
    falsehood->id = 3;
    falsehood->successors[0] = 4;
    falsehood->num_successors = 1;
    falsehood->next = join;
    twenty->value = 3;
    twenty->literal = 20;
    twenty->next = false_copy;
    copy2->dst = 4;
    copy2->src = 3;
    false_copy->copies = copy2;
    false_copy->next = false_jump;
    falsehood->first = twenty;
    falsehood->last = false_jump;
    join->id = 4;
    ret->src1 = 4;
    join->first = join->last = ret;
    return program;
}

static JITBlock *
find_block(JITProgram *program, int id)
{
    JITBlock *block;

    for (block = program->blocks; block; block = block->next)
	if (block->id == id)
	    return block;
    return 0;
}

static JITRunResult
reference_execute(JITProgram *program, Var *env, Var *result, int *ticks,
		  int *timed_out, enum error *error)
{
    Num *values = allocate(sizeof(Num) * (program->num_values + 1));
    JITBlock *block = program->blocks;

    while (block) {
	JITInstruction *instr;
	JITBlock *next = block->next;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
		if (--*ticks <= 0) {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_ABORT_TICKS;
		}
		if (*timed_out) {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_ABORT_SECONDS;
		}
		break;
	    case HIR_TAC_CONST:
		values[instr->value] = instr->literal;
		break;
	    case HIR_TAC_LOAD_LOCAL:
		if (env[instr->local_id].type != TYPE_INT) {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_FALLBACK;
		}
		values[instr->value] = env[instr->local_id].v.num;
		break;
	    case HIR_TAC_BINARY:
		if (instr->op == HIR_OP_ADD)
		    values[instr->value] = values[instr->src1]
			+ values[instr->src2];
		else if (instr->op == HIR_OP_DIV || instr->op == HIR_OP_MOD) {
		    IntegerArithmeticResult arithmetic = integer_arithmetic(
			instr->op == HIR_OP_DIV ? INTEGER_DIVIDE
			: INTEGER_MODULUS, values[instr->src1],
			values[instr->src2]);

		    if (!arithmetic.succeeded) {
			*error = arithmetic.error;
			myfree(values, M_PROGRAM);
			return JIT_RUN_ERROR;
		    }
		    values[instr->value] = arithmetic.value;
		}
		else {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_FALLBACK;
		}
		break;
	case HIR_TAC_PARALLEL_COPY:
		{
		    JITCopy *copy;
		    Num *saved;
		    int count = 0;

		    for (copy = instr->copies; copy; copy = copy->next)
			count++;
		    saved = allocate(sizeof(Num) * count);
		    count = 0;
		    for (copy = instr->copies; copy; copy = copy->next)
			saved[count++] = values[copy->src];
		    count = 0;
		    for (copy = instr->copies; copy; copy = copy->next)
			values[copy->dst] = saved[count++];
		    myfree(saved, M_PROGRAM);
		}
		break;
	    case HIR_TAC_JUMP:
		next = find_block(program, block->successors[0]);
		break;
	    case HIR_TAC_BRANCH_FALSE:
		next = find_block(program, block->successors[
			values[instr->src1] ? 1 : 0]);
		break;
	    case HIR_TAC_RETURN:
		result->type = TYPE_INT;
		result->v.num = values[instr->src1];
		myfree(values, M_PROGRAM);
		return JIT_RUN_RETURNED;
	    default:
		break;
	    }
	    if (instr == block->last)
		break;
	}
	block = next;
    }
    myfree(values, M_PROGRAM);
    return JIT_RUN_FALLBACK;
}

static void
check_differential(JITProgram *program, Var *env, int initial_ticks,
		   int timed_out, const char *message)
{
    Var native_result;
    Var reference_result;
    int native_ticks = initial_ticks;
    int reference_ticks = initial_ticks;
    enum error native_error = E_NONE;
    enum error reference_error = E_NONE;
    JITRunResult native_status;
    JITRunResult reference_status;

    native_status = jit_program_execute(program, env, &native_result,
					&native_ticks, &timed_out,
					&native_error);
    reference_status = reference_execute(program, env, &reference_result,
					 &reference_ticks, &timed_out,
					 &reference_error);
    check(native_status == reference_status && native_ticks == reference_ticks
	  && (native_status != JIT_RUN_ERROR
	      || native_error == reference_error)
	  && (native_status != JIT_RUN_RETURNED
	      || (native_result.type == reference_result.type
		  && native_result.v.num == reference_result.v.num)), message);
}

static void
count_line(const char *line, void *data)
{
    int *count = data;

    if (line && *line)
	(*count)++;
}

static void
check(int condition, const char *message)
{
    if (!condition) {
	fprintf(stderr, "%s\n", message);
	failures++;
    }
}

int
main(void)
{
    JITProgram *program = arithmetic_program();
    JITProgram *guard = guard_program();
    JITProgram *branch = branch_program();
    JITProgram *divide = division_program(20, 4, HIR_OP_DIV);
    JITProgram *divide_zero = division_program(20, 0, HIR_OP_DIV);
    JITProgram *divide_overflow = division_program(NUM_MIN, -1, HIR_OP_DIV);
    JITProgram *modulus_overflow = division_program(NUM_MIN, -1, HIR_OP_MOD);
    Var env[1];
    Var result;
    int ticks = 10;
    int timed_out = 0;
    enum error error = E_NONE;
    int lines = 0;

    check(jit_program_dump_mir(program, count_line, &lines),
	  "MIR dump failed");
    check(lines > 0, "MIR dump was empty");
    check(jit_program_state(program) == JIT_STATE_PENDING,
	  "MIR dump changed JIT state");
    check(jit_program_execute(program, env, &result, &ticks, &timed_out,
			      &error) == JIT_RUN_RETURNED,
	  "native execution failed");
    check(result.type == TYPE_INT && result.v.num == 3,
	  "native execution returned the wrong value");
    check(ticks == 9, "native execution consumed the wrong tick count");
    check(jit_program_state(program) == JIT_STATE_COMPILED,
	  "native execution did not compile lazily");
    ticks = 1;
    check(jit_program_execute(program, env, &result, &ticks, &timed_out,
			      &error)
	  == JIT_RUN_ABORT_TICKS, "tick exhaustion did not abort");
    check(ticks == 0, "tick exhaustion left the wrong tick count");
    ticks = 10;
    timed_out = 1;
    check(jit_program_execute(program, env, &result, &ticks, &timed_out,
			      &error)
	  == JIT_RUN_ABORT_SECONDS, "seconds exhaustion did not abort");
    check(ticks == 9, "seconds exhaustion consumed the wrong tick count");
    timed_out = 0;
    check_differential(divide, env, 10, 0,
		       "division differed from reference execution");
    check_differential(divide_zero, env, 10, 0,
		       "division error differed from reference execution");
    check_differential(divide_overflow, env, 10, 0,
		       "division overflow differed from reference execution");
    check_differential(modulus_overflow, env, 10, 0,
		       "modulus overflow differed from reference execution");

    env[0].type = TYPE_INT;
    env[0].v.num = 0;
    check_differential(branch, env, 10, 0,
		       "false branch differed from reference execution");
    env[0].v.num = 7;
    check_differential(branch, env, 10, 0,
		       "true branch differed from reference execution");
    check_differential(branch, env, 1, 0,
		       "tick abort differed from reference execution");
    check_differential(branch, env, 10, 1,
		       "seconds abort differed from reference execution");

    env[0].type = TYPE_STR;
    env[0].v.str = "not an integer";
    check(jit_program_execute(guard, env, &result, &ticks, &timed_out,
			      &error)
	  == JIT_RUN_FALLBACK, "type guard did not request fallback");
    check_differential(branch, env, 10, 0,
		       "guard fallback differed from reference execution");

    jit_program_free(program);
    jit_program_free(guard);
    jit_program_free(branch);
    jit_program_free(divide);
    jit_program_free(divide_zero);
    jit_program_free(divide_overflow);
    jit_program_free(modulus_overflow);
    return failures != 0;
}
