#include "jit_internal.h"

#include "my-stdio.h"

#include "storage.h"

#include <string.h>

static int failures;

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
    Var env[1];
    Var result;
    int ticks = 10;
    int timed_out = 0;
    int lines = 0;

    check(jit_program_dump_mir(program, count_line, &lines),
	  "MIR dump failed");
    check(lines > 0, "MIR dump was empty");
    check(jit_program_state(program) == JIT_STATE_PENDING,
	  "MIR dump changed JIT state");
    check(jit_program_execute(program, env, &result, &ticks, &timed_out)
	  == JIT_RUN_RETURNED, "native execution failed");
    check(result.type == TYPE_INT && result.v.num == 3,
	  "native execution returned the wrong value");
    check(ticks == 9, "native execution consumed the wrong tick count");
    check(jit_program_state(program) == JIT_STATE_COMPILED,
	  "native execution did not compile lazily");
    ticks = 1;
    check(jit_program_execute(program, env, &result, &ticks, &timed_out)
	  == JIT_RUN_ABORT_TICKS, "tick exhaustion did not abort");
    check(ticks == 0, "tick exhaustion left the wrong tick count");
    ticks = 10;
    timed_out = 1;
    check(jit_program_execute(program, env, &result, &ticks, &timed_out)
	  == JIT_RUN_ABORT_SECONDS, "seconds exhaustion did not abort");
    check(ticks == 9, "seconds exhaustion consumed the wrong tick count");
    timed_out = 0;

    env[0].type = TYPE_STR;
    env[0].v.str = "not an integer";
    check(jit_program_execute(guard, env, &result, &ticks, &timed_out)
	  == JIT_RUN_FALLBACK, "type guard did not request fallback");

    jit_program_free(program);
    jit_program_free(guard);
    return failures != 0;
}
