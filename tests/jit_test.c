#include "jit_internal.h"

#include "my-math.h"
#include "my-stdio.h"
#include "my-string.h"

#include "integer_arithmetic.h"
#include "storage.h"
#include "utils.h"

#include <limits.h>

static int failures;

static void check(int, const char *);

struct machine_dump {
    int lines;
    int valid_first_line;
};

static void
check_machine_line(const char *line, void *data)
{
    struct machine_dump *dump = data;

    if (dump->lines++ == 0)
	dump->valid_first_line = !strncmp(line, "0000: ", 6);
}

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

static void
add_entry_deopt_map(JITProgram *program)
{
    program->num_deopt_maps = 1;
    program->deopt_maps = allocate(sizeof(JITDeoptMap));
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
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    one->value = 1;
    one->literal = 1;
    two->value = 2;
    two->literal = 2;
    tick->source_lineno = 7;
    tick->bytecode_pc = 11;
    add->source_lineno = 7;
    add->bytecode_pc = 11;
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
binary_program(Num lhs, Num rhs, HIROp op)
{
    JITProgram *program = arithmetic_program();
    JITInstruction *one = program->blocks->first;
    JITInstruction *two = one->next;
    JITInstruction *binary = two->next->next;

    one->literal = lhs;
    two->literal = rhs;
    binary->op = op;
    program->may_error = op == HIR_OP_DIV || op == HIR_OP_MOD
	|| op == HIR_OP_EXP || op == HIR_OP_SHL || op == HIR_OP_SHR
	|| op == HIR_OP_LSHR;
    return program;
}

static JITProgram *
unary_program(Num operand, HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *c = instruction(HIR_TAC_CONST);
    JITInstruction *unary = instruction(HIR_TAC_UNARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 3;
    program->num_vars = 0;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    c->value = 1;
    c->literal = operand;

    unary->value = 2;
    unary->src1 = 1;
    unary->op = op;

    ret->src1 = 2;

    c->next = unary;
    unary->next = ret;

    block->first = c;
    block->last = ret;
    return program;
}

static int
arithmetic_operation(HIROp op, IntegerArithmeticOperation *operation)
{
    switch (op) {
    case HIR_OP_ADD:
	*operation = INTEGER_ADD;
	return 1;
    case HIR_OP_SUB:
	*operation = INTEGER_SUBTRACT;
	return 1;
    case HIR_OP_MUL:
	*operation = INTEGER_MULTIPLY;
	return 1;
    case HIR_OP_DIV:
	*operation = INTEGER_DIVIDE;
	return 1;
    case HIR_OP_MOD:
	*operation = INTEGER_MODULUS;
	return 1;
    case HIR_OP_EXP:
	*operation = INTEGER_POWER;
	return 1;
    case HIR_OP_SHL:
	*operation = INTEGER_SHIFT_LEFT;
	return 1;
    case HIR_OP_SHR:
	*operation = INTEGER_SHIFT_RIGHT;
	return 1;
    case HIR_OP_LSHR:
	*operation = INTEGER_LOGICAL_SHIFT_RIGHT;
	return 1;
    default:
	return 0;
    }
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
    add_entry_deopt_map(program);
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
local_arithmetic_program(Num constant_val, HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *binary = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 1;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    constant->value = 2;
    constant->literal = constant_val;
    tick->source_lineno = 7;
    tick->bytecode_pc = 11;
    binary->source_lineno = 7;
    binary->bytecode_pc = 11;
    binary->value = 3;
    binary->src1 = 1;
    binary->src2 = 2;
    binary->op = op;
    ret->src1 = 3;
    load->next = constant;
    constant->next = tick;
    tick->next = binary;
    binary->next = ret;
    block->first = load;
    block->last = ret;
    program->may_error = op == HIR_OP_DIV || op == HIR_OP_MOD
	|| op == HIR_OP_EXP || op == HIR_OP_SHL || op == HIR_OP_SHR
	|| op == HIR_OP_LSHR;
    return program;
}

static JITProgram *
two_local_program(HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load0 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *binary = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load0->value = 1;
    load0->local_id = 0;
    load1->value = 2;
    load1->local_id = 1;
    tick->source_lineno = 7;
    tick->bytecode_pc = 11;
    binary->source_lineno = 7;
    binary->bytecode_pc = 11;
    binary->value = 3;
    binary->src1 = 1;
    binary->src2 = 2;
    binary->op = op;
    ret->src1 = 3;
    load0->next = load1;
    load1->next = tick;
    tick->next = binary;
    binary->next = ret;
    block->first = load0;
    block->last = ret;
    program->may_error = op == HIR_OP_DIV || op == HIR_OP_MOD
	|| op == HIR_OP_EXP || op == HIR_OP_SHL || op == HIR_OP_SHR
	|| op == HIR_OP_LSHR || op == HIR_OP_INDEX;
    return program;
}

static JITProgram *
index_program(Num index_val)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *index = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->may_error = 1;
    program->num_values = 4;
    program->num_vars = 1;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->literal_type = TYPE_LIST;
    constant->value = 2;
    constant->literal = index_val;
    tick->source_lineno = 7;
    tick->bytecode_pc = 11;
    index->source_lineno = 7;
    index->bytecode_pc = 11;
    index->value = 3;
    index->src1 = 1;
    index->src2 = 2;
    index->op = HIR_OP_INDEX;
    ret->src1 = 3;
    load->next = constant;
    constant->next = tick;
    tick->next = index;
    index->next = ret;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
scatter_destructure_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *c1 = instruction(HIR_TAC_CONST);
    JITInstruction *idx1 = instruction(HIR_TAC_BINARY);
    JITInstruction *c2 = instruction(HIR_TAC_CONST);
    JITInstruction *idx2 = instruction(HIR_TAC_BINARY);
    JITInstruction *add = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->may_error = 1;
    program->num_values = 7;
    program->num_vars = 1;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load->value = 1;
    load->local_id = 0;
    load->literal_type = TYPE_LIST;

    c1->value = 2;
    c1->literal = 1;

    idx1->value = 3;
    idx1->src1 = 1;
    idx1->src2 = 2;
    idx1->op = HIR_OP_INDEX;

    c2->value = 4;
    c2->literal = 2;

    idx2->value = 5;
    idx2->src1 = 1;
    idx2->src2 = 4;
    idx2->op = HIR_OP_INDEX;

    add->value = 6;
    add->src1 = 3;
    add->src2 = 5;
    add->op = HIR_OP_ADD;

    ret->src1 = 6;

    load->next = c1;
    c1->next = idx1;
    idx1->next = c2;
    c2->next = idx2;
    idx2->next = add;
    add->next = ret;

    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
call_boundary_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *c1 = instruction(HIR_TAC_CONST);
    JITInstruction *call = instruction(HIR_TAC_CALL);
    JITDeoptMap *map;

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 3;
    program->num_vars = 1;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 25;
    map->stack_depth = 1;
    map->ticks_charged = 0;
    map->num_locals = 1;
    map->local_values = allocate(sizeof(int) * 1);
    map->local_values[0] = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_values[0] = 1;
    program->blocks = program->last_block = block;
    block->id = 1;

    c1->value = 1;
    c1->literal = 99;

    call->value = 2;
    call->src1 = 1;
    call->deopt_map = 1;
    call->bytecode_pc = 25;

    c1->next = call;

    block->first = c1;
    block->last = call;
    return program;
}

static JITProgram *
get_prop_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *c1 = instruction(HIR_TAC_CONST);
    JITInstruction *c2 = instruction(HIR_TAC_CONST);
    JITInstruction *get = instruction(HIR_TAC_BINARY);
    JITDeoptMap *map;

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 1;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 30;
    map->stack_depth = 2;
    map->ticks_charged = 0;
    map->num_locals = 1;
    map->local_values = allocate(sizeof(int) * 1);
    map->local_values[0] = 1;
    map->stack_values = allocate(sizeof(int) * 2);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    program->blocks = program->last_block = block;
    block->id = 1;

    c1->value = 1;
    c1->literal = 0;

    c2->value = 2;
    c2->literal = 123;

    get->value = 3;
    get->src1 = 1;
    get->src2 = 2;
    get->op = HIR_OP_GET_PROP;
    get->deopt_map = 1;
    get->bytecode_pc = 30;

    c1->next = c2;
    c2->next = get;

    block->first = c1;
    block->last = get;
    return program;
}

static JITProgram *
deep_guard_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 3;
    program->num_vars = 2;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 12;
    map->stack_depth = 1;
    map->ticks_charged = 1;
    map->num_locals = 2;
    map->local_values = allocate(sizeof(int) * 2);
    map->local_values[0] = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_values[0] = 1;
    program->blocks = program->last_block = block;
    block->id = 1;
    constant->value = 1;
    constant->literal = 42;
    constant->next = tick;
    tick->next = load;
    load->value = 2;
    load->local_id = 1;
    load->deopt_map = 1;
    load->next = ret;
    ret->src1 = 2;
    block->first = constant;
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
    add_entry_deopt_map(program);
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

static JITProgram *
charge_tick_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 2;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    constant->value = 1;
    constant->literal = 7;
    constant->next = tick;
    tick->op = HIR_OP_CHARGE_TICK;
    tick->next = ret;
    ret->src1 = 1;
    block->first = constant;
    block->last = ret;
    return program;
}

static JITProgram *
call_verb_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_obj = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_verb = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_args = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *call_verb = instruction(HIR_TAC_CALL_VERB);
    JITDeoptMap *map;

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 5;
    program->num_vars = 3;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 30;
    map->stack_depth = 3;
    map->ticks_charged = 1;
    map->num_locals = 3;
    map->local_values = allocate(sizeof(int) * 3);
    map->local_types = allocate(sizeof(var_type) * 3);
    map->local_values[0] = 1;
    map->local_values[1] = 2;
    map->local_values[2] = 3;
    map->local_types[0] = TYPE_OBJ;
    map->local_types[1] = TYPE_STR;
    map->local_types[2] = TYPE_LIST;
    map->stack_values = allocate(sizeof(int) * 3);
    map->stack_types = allocate(sizeof(var_type) * 3);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    map->stack_types[0] = TYPE_OBJ;
    map->stack_types[1] = TYPE_STR;
    map->stack_types[2] = TYPE_LIST;
    load_obj->literal_type = TYPE_OBJ;
    load_verb->literal_type = TYPE_STR;
    load_args->literal_type = TYPE_LIST;

    program->blocks = program->last_block = block;
    block->id = 1;
    load_obj->value = 1;
    load_obj->local_id = 0;
    load_obj->next = load_verb;
    load_verb->value = 2;
    load_verb->local_id = 1;
    load_verb->next = load_args;
    load_args->value = 3;
    load_args->local_id = 2;
    load_args->next = tick;
    tick->bytecode_pc = 30;
    tick->next = call_verb;
    call_verb->value = 4;
    call_verb->src1 = 1;
    call_verb->src2 = 2;
    call_verb->deopt_map = 1;
    block->first = load_obj;
    block->last = call_verb;
    return program;
}

static JITProgram *
object_return_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_local = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 2;
    program->num_vars = 1;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load_local->value = 1;
    load_local->local_id = 0;
    load_local->literal_type = TYPE_OBJ;
    load_local->next = return_instr;
    return_instr->src1 = 1;
    return_instr->literal_type = TYPE_OBJ;
    block->first = load_local;
    block->last = return_instr;
    return program;
}

static JITProgram *
object_compare_program(HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_obj1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_obj2 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *cmp = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load_obj1->value = 1;
    load_obj1->local_id = 0;
    load_obj1->literal_type = TYPE_OBJ;
    load_obj1->next = load_obj2;
    load_obj2->value = 2;
    load_obj2->local_id = 1;
    load_obj2->literal_type = TYPE_OBJ;
    load_obj2->next = cmp;
    cmp->value = 3;
    cmp->src1 = 1;
    cmp->src2 = 2;
    cmp->op = op;
    cmp->next = return_instr;
    return_instr->src1 = 3;
    return_instr->literal_type = TYPE_INT;
    block->first = load_obj1;
    block->last = return_instr;
    return program;
}

static JITProgram *
float_return_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_local = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 2;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 2);
    program->value_types[0] = TYPE_ANY;
    program->value_types[1] = TYPE_FLOAT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load_local->value = 1;
    load_local->local_id = 0;
    load_local->literal_type = TYPE_FLOAT;
    load_local->next = return_instr;
    return_instr->src1 = 1;
    return_instr->literal_type = TYPE_FLOAT;
    block->first = load_local;
    block->last = return_instr;
    return program;
}

static JITProgram *
float_binary_program(HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_f1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_f2 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *bin = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_ANY;
    program->value_types[1] = TYPE_FLOAT;
    program->value_types[2] = TYPE_FLOAT;
    program->value_types[3] = TYPE_FLOAT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load_f1->value = 1;
    load_f1->local_id = 0;
    load_f1->literal_type = TYPE_FLOAT;
    load_f1->next = load_f2;
    load_f2->value = 2;
    load_f2->local_id = 1;
    load_f2->literal_type = TYPE_FLOAT;
    load_f2->next = bin;
    bin->value = 3;
    bin->src1 = 1;
    bin->src2 = 2;
    bin->op = op;
    bin->next = return_instr;
    return_instr->src1 = 3;
    return_instr->literal_type = TYPE_FLOAT;
    block->first = load_f1;
    block->last = return_instr;
    return program;
}

static JITProgram *
float_compare_program(HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_f1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_f2 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *cmp = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_ANY;
    program->value_types[1] = TYPE_FLOAT;
    program->value_types[2] = TYPE_FLOAT;
    program->value_types[3] = TYPE_INT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load_f1->value = 1;
    load_f1->local_id = 0;
    load_f1->literal_type = TYPE_FLOAT;
    load_f1->next = load_f2;
    load_f2->value = 2;
    load_f2->local_id = 1;
    load_f2->literal_type = TYPE_FLOAT;
    load_f2->next = cmp;
    cmp->value = 3;
    cmp->src1 = 1;
    cmp->src2 = 2;
    cmp->op = op;
    cmp->next = return_instr;
    return_instr->src1 = 3;
    return_instr->literal_type = TYPE_INT;
    block->first = load_f1;
    block->last = return_instr;
    return program;
}

static JITProgram *
float_unary_program(double val, HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *unary = instruction(HIR_TAC_UNARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 3;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_types[0] = TYPE_ANY;
    program->value_types[1] = TYPE_FLOAT;
    program->value_types[2] = (op == HIR_OP_NOT || op == HIR_OP_TYPEOF) ? TYPE_INT : TYPE_FLOAT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    constant->value = 1;
    constant->literal_type = TYPE_FLOAT;
    memcpy(&constant->literal, &val, sizeof(Num));
    constant->next = unary;
    unary->value = 2;
    unary->src1 = 1;
    unary->op = op;
    if (op == HIR_OP_TYPEOF)
	unary->literal = TYPE_FLOAT;
    unary->next = return_instr;
    return_instr->src1 = 2;
    return_instr->literal_type = (op == HIR_OP_NOT || op == HIR_OP_TYPEOF) ? TYPE_INT : TYPE_FLOAT;
    block->first = constant;
    block->last = return_instr;
    return program;
}

static JITProgram *
string_return_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_local = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 2;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 2);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load_local->value = 1;
    load_local->local_id = 0;
    load_local->literal_type = TYPE_STR;
    load_local->deopt_map = 0;
    load_local->next = return_instr;

    return_instr->src1 = 1;
    return_instr->literal_type = TYPE_STR;

    block->first = load_local;
    block->last = return_instr;
    return program;
}

static JITProgram *
string_const_program(const char *s)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 2;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 2);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    constant->value = 1;
    constant->literal_type = TYPE_STR;
    {
	char *dup_s = str_dup(s);
	constant->literal = (uintptr_t) dup_s;
    }
    constant->next = return_instr;

    return_instr->src1 = 1;
    return_instr->literal_type = TYPE_STR;

    block->first = constant;
    block->last = return_instr;
    return program;
}

static JITProgram *
string_compare_program(const char *lhs, const char *rhs, HIROp op)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *left = instruction(HIR_TAC_CONST);
    JITInstruction *right = instruction(HIR_TAC_CONST);
    JITInstruction *compare = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);
    char *left_string = str_dup(lhs);
    char *right_string = str_dup(rhs);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_STR;
    program->value_types[3] = TYPE_INT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    left->value = 1;
    left->literal = (uintptr_t) left_string;
    left->literal_type = TYPE_STR;
    left->next = right;
    right->value = 2;
    right->literal = (uintptr_t) right_string;
    right->literal_type = TYPE_STR;
    right->next = compare;
    compare->value = 3;
    compare->src1 = 1;
    compare->src2 = 2;
    compare->op = op;
    compare->deopt_map = 0;
    compare->next = return_instr;
    return_instr->src1 = 3;
    return_instr->literal_type = TYPE_INT;
    block->first = left;
    block->last = return_instr;
    return program;
}

static JITProgram *
string_branch_program(void)
{
    JITProgram *program = branch_program();
    JITInstruction *load = program->blocks->first;

    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_INT;
    program->value_types[4] = TYPE_INT;
    load->literal_type = TYPE_STR;
    return program;
}

static JITProgram *
string_not_program(const char *s)
{
    JITProgram *program = string_const_program(s);
    JITInstruction *constant = program->blocks->first;
    JITInstruction *return_instr = constant->next;
    JITInstruction *not_instr = instruction(HIR_TAC_UNARY);

    program->num_values = 3;
    myfree(program->value_types, M_PROGRAM);
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_INT;
    constant->next = not_instr;
    not_instr->value = 2;
    not_instr->src1 = 1;
    not_instr->op = HIR_OP_NOT;
    not_instr->deopt_map = 0;
    not_instr->next = return_instr;
    return_instr->src1 = 2;
    return_instr->literal_type = TYPE_INT;
    return program;
}
static JITProgram *
catch_stack_marker_deopt_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_codes = instruction(HIR_TAC_CONST);
    JITInstruction *const_pc = instruction(HIR_TAC_CONST);
    JITInstruction *const_catch = instruction(HIR_TAC_CONST);
    JITInstruction *deopt_op = instruction(HIR_TAC_UNARY);
    JITDeoptMap *map;

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 5;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_INT;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_CATCH;
    program->value_types[4] = TYPE_INT;

    map = &program->deopt_maps[1];
    map->bytecode_pc = 25;
    map->error_pc = 25;
    map->stack_depth = 3;
    map->ticks_charged = 1;
    map->num_locals = 0;
    map->stack_values = allocate(sizeof(int) * 3);
    map->stack_types = allocate(sizeof(var_type) * 3);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    map->stack_types[0] = TYPE_INT;
    map->stack_types[1] = TYPE_INT;
    map->stack_types[2] = TYPE_CATCH;

    program->blocks = program->last_block = block;
    block->id = 1;

    const_codes->value = 1;
    const_codes->literal = 0;
    const_codes->literal_type = TYPE_INT;
    const_codes->next = const_pc;

    const_pc->value = 2;
    const_pc->literal = 77;
    const_pc->literal_type = TYPE_INT;
    const_pc->next = const_catch;

    const_catch->value = 3;
    const_catch->literal = 1;
    const_catch->literal_type = TYPE_CATCH;
    const_catch->next = deopt_op;

    deopt_op->value = 4;
    deopt_op->src1 = 1;
    deopt_op->op = HIR_OP_MAKE_SINGLETON_LIST;
    deopt_op->deopt_map = 1;
    deopt_op->bytecode_pc = 25;

    block->first = const_codes;
    block->last = deopt_op;
    return program;
}

static JITProgram *
finally_stack_marker_deopt_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_finally = instruction(HIR_TAC_CONST);
    JITInstruction *deopt_op = instruction(HIR_TAC_UNARY);
    JITDeoptMap *map;

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 3;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_FINALLY;
    program->value_types[2] = TYPE_INT;

    map = &program->deopt_maps[1];
    map->bytecode_pc = 40;
    map->error_pc = 40;
    map->stack_depth = 1;
    map->ticks_charged = 1;
    map->num_locals = 0;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 1;
    map->stack_types[0] = TYPE_FINALLY;

    program->blocks = program->last_block = block;
    block->id = 1;

    const_finally->value = 1;
    const_finally->literal = 88;
    const_finally->literal_type = TYPE_FINALLY;
    const_finally->next = deopt_op;

    deopt_op->value = 2;
    deopt_op->src1 = 1;
    deopt_op->op = HIR_OP_MAKE_SINGLETON_LIST;
    deopt_op->deopt_map = 1;
    deopt_op->bytecode_pc = 40;

    block->first = const_finally;
    block->last = deopt_op;
    return program;
}

static JITProgram *
list_index_typed_program(var_type elem_type)
{
    JITProgram *program = allocate(sizeof(JITProgram));
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_idx = instruction(HIR_TAC_CONST);
    JITInstruction *index_instr = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

    program->state = JIT_STATE_PENDING;
    program->reason = "none";
    program->eligible = 1;
    program->num_values = 4;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = elem_type;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load_list->value = 1;
    load_list->local_id = 0;
    load_list->literal_type = TYPE_LIST;
    load_list->deopt_map = 0;
    load_list->next = const_idx;

    const_idx->value = 2;
    const_idx->literal = 1;
    const_idx->literal_type = TYPE_INT;
    const_idx->next = index_instr;

    index_instr->value = 3;
    index_instr->src1 = 1;
    index_instr->src2 = 2;
    index_instr->op = HIR_OP_INDEX;
    index_instr->deopt_map = 0;
    index_instr->next = return_instr;

    return_instr->src1 = 3;
    return_instr->literal_type = elem_type;

    block->first = load_list;
    block->last = return_instr;
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
		--*ticks;
		if (instr->op != HIR_OP_CHARGE_TICK && *ticks <= 0) {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_ABORT_TICKS;
		}
		if (instr->op != HIR_OP_CHARGE_TICK && *timed_out) {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_ABORT_SECONDS;
		}
		break;
	    case HIR_TAC_CONST:
		if (instr->literal_type == TYPE_FLOAT)
		    memcpy(&values[instr->value], &instr->literal, sizeof(Num));
		else
		    values[instr->value] = instr->literal;
		break;
	    case HIR_TAC_LOAD_LOCAL:
		if (env[instr->local_id].type != instr->literal_type) {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_FALLBACK;
		}
		if (instr->literal_type == TYPE_INT)
		    values[instr->value] = env[instr->local_id].v.num;
		else if (instr->literal_type == TYPE_OBJ)
		    values[instr->value] = env[instr->local_id].v.obj;
		else if (instr->literal_type == TYPE_FLOAT) {
		    FlNum f = fl_unbox(env[instr->local_id].v.fnum);
		    memcpy(&values[instr->value], &f, sizeof(Num));
		}
		else if (instr->literal_type == TYPE_LIST)
		    values[instr->value] = (Num) (intptr_t) env[instr->local_id].v.list;
		else if (instr->literal_type == TYPE_STR)
		    values[instr->value] = (Num) (intptr_t) env[instr->local_id].v.str;
		else {
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_FALLBACK;
		}
		break;
	    case HIR_TAC_UNARY:
		if (program->value_types && program->value_types[instr->src1] == TYPE_FLOAT) {
		    FlNum f;
		    memcpy(&f, &values[instr->src1], sizeof(FlNum));
		    if (instr->op == HIR_OP_NEGATE) {
			f = -f;
			memcpy(&values[instr->value], &f, sizeof(FlNum));
		    } else if (instr->op == HIR_OP_ABS) {
			if (f < 0.0) f = -f;
			memcpy(&values[instr->value], &f, sizeof(FlNum));
		    } else if (instr->op == HIR_OP_NOT) {
			values[instr->value] = (f == 0.0);
		    } else if (instr->op == HIR_OP_TYPEOF) {
			values[instr->value] = instr->literal;
		    }
		}
		break;
	    case HIR_TAC_BINARY:
		{
		    IntegerArithmeticOperation operation;

		    if (program->value_types && program->value_types[instr->src1] == TYPE_FLOAT) {
			FlNum a, b, res;
			memcpy(&a, &values[instr->src1], sizeof(FlNum));
			memcpy(&b, &values[instr->src2], sizeof(FlNum));
			if (instr->op == HIR_OP_ADD) {
			    res = a + b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_SUB) {
			    res = a - b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_MUL) {
			    res = a * b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_DIV) {
			    if (b == 0.0) {
				*error = E_DIV;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    res = a / b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_EQ)
			    values[instr->value] = (a == b);
			else if (instr->op == HIR_OP_NE)
			    values[instr->value] = (a != b);
			else if (instr->op == HIR_OP_LT)
			    values[instr->value] = (a < b);
			else if (instr->op == HIR_OP_LE)
			    values[instr->value] = (a <= b);
			else if (instr->op == HIR_OP_GT)
			    values[instr->value] = (a > b);
			else if (instr->op == HIR_OP_GE)
			    values[instr->value] = (a >= b);
			break;
		    }
		    if (instr->op == HIR_OP_INDEX) {
			Var *list_ptr = (Var *) (intptr_t) values[instr->src1];
			Num index = values[instr->src2];
			var_type expected_type = program->value_types
			    ? program->value_types[instr->value] : TYPE_INT;

			if (!list_ptr) {
			    myfree(values, M_PROGRAM);
			    return JIT_RUN_FALLBACK;
			}
			if (index < 1 || index > list_ptr[0].v.num) {
			    *error = E_RANGE;
			    myfree(values, M_PROGRAM);
			    return JIT_RUN_ERROR;
			}
			if (list_ptr[index].type != expected_type) {
			    myfree(values, M_PROGRAM);
			    return JIT_RUN_FALLBACK;
			}
			if (expected_type == TYPE_FLOAT) {
			    FlNum f = fl_unbox(list_ptr[index].v.fnum);
			    memcpy(&values[instr->value], &f, sizeof(Num));
			} else if (expected_type == TYPE_OBJ)
			    values[instr->value] = list_ptr[index].v.obj;
			else if (expected_type == TYPE_STR)
			    values[instr->value] = (Num) (intptr_t) list_ptr[index].v.str;
			else if (expected_type == TYPE_LIST)
			    values[instr->value] = (Num) (intptr_t) list_ptr[index].v.list;
			else
			    values[instr->value] = list_ptr[index].v.num;
		    } else if (arithmetic_operation(instr->op, &operation)) {
			IntegerArithmeticResult arithmetic = integer_arithmetic(
			    operation, values[instr->src1], values[instr->src2]);

			if (!arithmetic.succeeded) {
			    *error = arithmetic.error;
			    myfree(values, M_PROGRAM);
			    return JIT_RUN_ERROR;
			}
			values[instr->value] = arithmetic.value;
		    } else if (instr->op == HIR_OP_BITOR)
			values[instr->value] = values[instr->src1]
			    | values[instr->src2];
		    else if (instr->op == HIR_OP_BITXOR)
			values[instr->value] = values[instr->src1]
			    ^ values[instr->src2];
		    else if (instr->op == HIR_OP_BITAND)
			values[instr->value] = values[instr->src1]
			    & values[instr->src2];
		    else if (instr->op == HIR_OP_EQ)
			values[instr->value] = values[instr->src1]
			    == values[instr->src2];
		    else if (instr->op == HIR_OP_NE)
			values[instr->value] = values[instr->src1]
			    != values[instr->src2];
		    else if (instr->op == HIR_OP_LT)
			values[instr->value] = values[instr->src1]
			    < values[instr->src2];
		    else if (instr->op == HIR_OP_LE)
			values[instr->value] = values[instr->src1]
			    <= values[instr->src2];
		    else if (instr->op == HIR_OP_GT)
			values[instr->value] = values[instr->src1]
			    > values[instr->src2];
		    else if (instr->op == HIR_OP_GE)
			values[instr->value] = values[instr->src1]
			    >= values[instr->src2];
		    else {
			myfree(values, M_PROGRAM);
			return JIT_RUN_FALLBACK;
		    }
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
		result->type = instr->literal_type;
		if (instr->literal_type == TYPE_OBJ)
		    result->v.obj = values[instr->src1];
		else if (instr->literal_type == TYPE_FLOAT) {
		    FlNum f;
		    memcpy(&f, &values[instr->src1], sizeof(FlNum));
		    result->v.fnum = box_fl(f);
		}
		else if (instr->literal_type == TYPE_STR)
		    result->v.str = (const char *) (intptr_t) values[instr->src1];
		else if (instr->literal_type == TYPE_LIST)
		    result->v.list = (Var *) (intptr_t) values[instr->src1];
		else
		    result->v.num = values[instr->src1];
		*result = var_ref(*result);
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
					&native_error, 0, 0, 0);
    reference_status = reference_execute(program, env, &reference_result,
					 &reference_ticks, &timed_out,
					 &reference_error);
    check(native_status == reference_status && native_ticks == reference_ticks
	  && (native_status != JIT_RUN_ERROR
	      || native_error == reference_error)
	  && (native_status != JIT_RUN_RETURNED
	      || (native_result.type == reference_result.type
		  && (native_result.type == TYPE_FLOAT
		      ? fl_unbox(native_result.v.fnum) == fl_unbox(reference_result.v.fnum)
		      : (native_result.type == TYPE_STR
			 ? !strcmp(native_result.v.str, reference_result.v.str)
			 : (native_result.type == TYPE_OBJ
			    ? native_result.v.obj == reference_result.v.obj
			    : (native_result.type == TYPE_LIST
			       ? native_result.v.list == reference_result.v.list
			       : native_result.v.num == reference_result.v.num)))))), message);
    if (native_status == JIT_RUN_RETURNED)
	free_var(native_result);
    if (reference_status == JIT_RUN_RETURNED)
	free_var(reference_result);
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
    JITProgram *deep_guard = deep_guard_program();
    JITProgram *branch = branch_program();
    JITProgram *charge_tick = charge_tick_program();
    JITProgram *divide = binary_program(20, 4, HIR_OP_DIV);
    JITProgram *divide_zero = binary_program(20, 0, HIR_OP_DIV);
    JITProgram *divide_overflow = binary_program(NUM_MIN, -1, HIR_OP_DIV);
    JITProgram *modulus_overflow = binary_program(NUM_MIN, -1, HIR_OP_MOD);
    JITProgram *power = binary_program(3, 13, HIR_OP_EXP);
    JITProgram *power_wrap = binary_program(2, 63, HIR_OP_EXP);
    JITProgram *power_negative = binary_program(-1, -3, HIR_OP_EXP);
    JITProgram *power_error = binary_program(0, -1, HIR_OP_EXP);
    JITProgram *local_arith = local_arithmetic_program(5, HIR_OP_ADD);
    JITProgram *two_locals = two_local_program(HIR_OP_MUL);
    JITProgram *list_index1 = index_program(1);
    JITProgram *list_index2 = index_program(2);
    JITProgram *list_index_low = index_program(0);
    JITProgram *list_index_high = index_program(3);
    JITProgram *shift_left = binary_program(NUM_MIN, 1, HIR_OP_SHL);
    JITProgram *shift_right = binary_program(NUM_MIN, 63, HIR_OP_SHR);
    JITProgram *logical_shift = binary_program(NUM_MIN, 63, HIR_OP_LSHR);
    JITProgram *shift_error = binary_program(1, sizeof(Num) * CHAR_BIT,
					     HIR_OP_SHL);
    JITProgram *negative_shift = binary_program(1, -1, HIR_OP_SHL);
    JITProgram *bit_and = binary_program(0x55, 0x0f, HIR_OP_BITAND);
    JITProgram *bit_xor = binary_program(0x55, 0x0f, HIR_OP_BITXOR);
    JITProgram *bit_or = binary_program(0x55, 0x0f, HIR_OP_BITOR);
    JITProgram *scatter = scatter_destructure_program();
    Var env[1];
    Var deep_env[3];
    Var deopt_stack[4];
    Var *call_args = mymalloc(sizeof(Var) * 1, M_LIST);
    Var *list_elems = mymalloc(sizeof(Var) * 3, M_LIST);
    Var result;
    int ticks = 10;
    int timed_out = 0;
    enum error error = E_NONE;
    int lines = 0;
    struct machine_dump machine_dump = {0, 0};
    JITDeoptState deopt;
    JITSourceLocation source_location;

    check(jit_program_dump_mir(program, count_line, &lines),
	  "MIR dump failed");
    check(lines > 0, "MIR dump was empty");
    check(jit_program_deopt_map_count(program) == 1,
	  "JIT program has the wrong deopt map count");
    check(jit_program_state(program) == JIT_STATE_PENDING,
	  "MIR dump changed JIT state");
    check(jit_program_dump_machine(program, check_machine_line, &machine_dump),
	  "machine-code dump failed");
    check(machine_dump.lines > 0, "machine-code dump was empty");
    check(machine_dump.valid_first_line,
	  "machine-code dump did not contain hex bytes");
    check(jit_program_state(program) == JIT_STATE_COMPILED,
	  "machine-code dump did not compile lazily");
    check(jit_program_execute(program, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0) == JIT_RUN_RETURNED,
	  "native execution failed");
    check(result.type == TYPE_INT && result.v.num == 3,
	  "native execution returned the wrong value");
    check(ticks == 9, "native execution consumed the wrong tick count");
    check(jit_program_state(program) == JIT_STATE_COMPILED,
	  "native execution did not compile lazily");
    ticks = 1;
    check(jit_program_execute(program, env, &result, &ticks, &timed_out,
			      &error, &source_location, 0, 0)
	  == JIT_RUN_ABORT_TICKS, "tick exhaustion did not abort");
    check(ticks == 0, "tick exhaustion left the wrong tick count");
    check(source_location.bytecode_pc == 11
	  && source_location.error_pc == 11
	  && source_location.source_lineno == 7,
	  "tick exhaustion returned the wrong source location");
    ticks = 10;
    timed_out = 1;
    check(jit_program_execute(program, env, &result, &ticks, &timed_out,
			      &error, &source_location, 0, 0)
	  == JIT_RUN_ABORT_SECONDS, "seconds exhaustion did not abort");
    check(ticks == 9, "seconds exhaustion consumed the wrong tick count");
    check(source_location.bytecode_pc == 11
	  && source_location.source_lineno == 7,
	  "seconds exhaustion returned the wrong source location");
    timed_out = 0;
    check_differential(divide, env, 10, 0,
		       "division differed from reference execution");
    check_differential(divide_zero, env, 10, 0,
		       "division error differed from reference execution");
    check_differential(divide_overflow, env, 10, 0,
		       "division overflow differed from reference execution");
    check_differential(modulus_overflow, env, 10, 0,
		       "modulus overflow differed from reference execution");
    check_differential(power, env, 10, 0,
		       "power differed from reference execution");
    check_differential(power_wrap, env, 10, 0,
		       "wrapping power differed from reference execution");
    check_differential(power_negative, env, 10, 0,
		       "negative power differed from reference execution");
    check_differential(power_error, env, 10, 0,
		       "power error differed from reference execution");
    ticks = 10;
    error = E_NONE;
    check(jit_program_execute(power_error, env, &result, &ticks, &timed_out,
			      &error, &source_location, 0, 0)
	  == JIT_RUN_ERROR && error == E_DIV,
	  "power error did not return its native error");
    check(source_location.bytecode_pc == 11
	  && source_location.error_pc == 11
	  && source_location.source_lineno == 7,
	  "power error returned the wrong source location");
    check_differential(shift_left, env, 10, 0,
		       "left shift differed from reference execution");
    check_differential(shift_right, env, 10, 0,
		       "right shift differed from reference execution");
    check_differential(logical_shift, env, 10, 0,
		       "logical shift differed from reference execution");
    check_differential(shift_error, env, 10, 0,
		       "shift error differed from reference execution");
    check_differential(negative_shift, env, 10, 0,
		       "negative shift differed from reference execution");
    check_differential(bit_and, env, 10, 0,
		       "bitwise and differed from reference execution");
    check_differential(bit_xor, env, 10, 0,
		       "bitwise xor differed from reference execution");
    check_differential(bit_or, env, 10, 0,
		       "bitwise or differed from reference execution");

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
    check_differential(charge_tick, env, 1, 1,
		       "charge-only tick differed from reference execution");

    env[0].type = TYPE_INT;
    env[0].v.num = 42;
    ticks = 10;
    check(jit_program_execute(guard, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "entry guard int execution failed");
    check(result.type == TYPE_INT && result.v.num == 42,
	  "entry guard returned the wrong value");
    check_differential(guard, env, 10, 0,
		       "entry guard differed from reference execution");

    env[0].type = TYPE_INT;
    env[0].v.num = 10;
    ticks = 10;
    check(jit_program_execute(local_arith, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "local arithmetic execution failed");
    check(result.type == TYPE_INT && result.v.num == 15,
	  "local arithmetic returned the wrong value");
    check_differential(local_arith, env, 10, 0,
		       "local arithmetic differed from reference execution");

    env[0].type = TYPE_STR;
    env[0].v.str = "not an integer";
    ticks = 10;
    check(jit_program_execute(local_arith, env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "local arithmetic guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "local arithmetic guard fallback had wrong state");
    check_differential(local_arith, env, 10, 0,
		       "local arithmetic fallback differed from reference execution");

    deep_env[0].type = TYPE_INT;
    deep_env[0].v.num = 6;
    deep_env[1].type = TYPE_INT;
    deep_env[1].v.num = 7;
    ticks = 10;
    check(jit_program_execute(two_locals, deep_env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "two locals execution failed");
    check(result.type == TYPE_INT && result.v.num == 42,
	  "two locals returned the wrong value");
    check_differential(two_locals, deep_env, 10, 0,
		       "two locals differed from reference execution");

    deep_env[0].type = TYPE_STR;
    deep_env[0].v.str = "not an integer";
    ticks = 10;
    check(jit_program_execute(two_locals, deep_env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "two locals first guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "two locals first guard fallback had wrong state");
    check_differential(two_locals, deep_env, 10, 0,
		       "two locals first guard fallback differed from reference");

    deep_env[0].type = TYPE_INT;
    deep_env[0].v.num = 6;
    deep_env[1].type = TYPE_STR;
    deep_env[1].v.str = "not an integer";
    ticks = 10;
    check(jit_program_execute(two_locals, deep_env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "two locals second guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "two locals second guard fallback had wrong state");
    check_differential(two_locals, deep_env, 10, 0,
		       "two locals second guard fallback differed from reference");

    env[0].type = TYPE_STR;
    env[0].v.str = "not an integer";
    ticks = 10;
    check(jit_program_execute(guard, env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "type guard did not request fallback");
    check(ticks == 10, "entry guard fallback consumed ticks");
    check(deopt.bytecode_pc == 0 && deopt.error_pc == 0
	  && deopt.stack_depth == 0, "entry guard returned the wrong deopt map");
    check_differential(branch, env, 10, 0,
		       "guard fallback differed from reference execution");

    deep_env[0].type = TYPE_INT;
    deep_env[0].v.num = 7;
    deep_env[1].type = TYPE_STR;
    deep_env[1].v.str = "not an integer";
    ticks = 10;
    check(jit_program_execute(deep_guard, deep_env, &result, &ticks,
			      &timed_out, &error, 0, &deopt, deopt_stack)
	  == JIT_RUN_FALLBACK, "deep guard did not request fallback");
    check(ticks == 9 && deopt.ticks_charged == 1,
	  "deep guard returned the wrong tick credit");
    check(deopt.bytecode_pc == 12 && deopt.error_pc == 12
	  && deopt.stack_depth == 1, "deep guard returned the wrong frame state");
    check(deep_env[0].type == TYPE_INT && deep_env[0].v.num == 42,
	  "deep guard did not materialize an updated local");
    check(deopt_stack[0].type == TYPE_INT && deopt_stack[0].v.num == 42,
	  "deep guard did not materialize the operand stack");

    deep_env[0].type = TYPE_INT;
    deep_env[0].v.num = 7;
    deep_env[1].type = TYPE_INT;
    deep_env[1].v.num = 8;
    ticks = 10;
    check(jit_program_execute(deep_guard, deep_env, &result, &ticks,
			      &timed_out, &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "deep guard success execution failed");
    check(result.type == TYPE_INT && result.v.num == 8,
	  "deep guard success returned the wrong value");
    check_differential(deep_guard, deep_env, 10, 0,
		       "deep guard success differed from reference execution");

    /* List indexing tests */
    list_elems[0].type = TYPE_INT;
    list_elems[0].v.num = 2;
    list_elems[1].type = TYPE_INT;
    list_elems[1].v.num = 42;
    list_elems[2].type = TYPE_INT;
    list_elems[2].v.num = 99;
    env[0].type = TYPE_LIST;
    env[0].v.list = list_elems;

    ticks = 10;
    check(jit_program_execute(list_index1, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "list index 1 execution failed");
    check(result.type == TYPE_INT && result.v.num == 42,
	  "list index 1 returned the wrong value");
    check_differential(list_index1, env, 10, 0,
		       "list index 1 differed from reference execution");

    ticks = 10;
    check(jit_program_execute(list_index2, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "list index 2 execution failed");
    check(result.type == TYPE_INT && result.v.num == 99,
	  "list index 2 returned the wrong value");
    check_differential(list_index2, env, 10, 0,
		       "list index 2 differed from reference execution");

    ticks = 10;
    check(jit_program_execute(list_index_low, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_ERROR, "list index 0 did not error");
    check(error == E_RANGE, "list index 0 gave wrong error code");
    check_differential(list_index_low, env, 10, 0,
		       "list index 0 differed from reference execution");

    ticks = 10;
    check(jit_program_execute(list_index_high, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_ERROR, "list index 3 did not error");
    check(error == E_RANGE, "list index 3 gave wrong error code");
    check_differential(list_index_high, env, 10, 0,
		       "list index 3 differed from reference execution");

    env[0].type = TYPE_INT;
    env[0].v.num = 1;
    ticks = 10;
    check(jit_program_execute(list_index1, env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "list input guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "list input guard fallback had wrong state");
    check_differential(list_index1, env, 10, 0,
		       "list input guard differed from reference execution");
    env[0].type = TYPE_LIST;
    env[0].v.list = list_elems;

    /* Non-integer element in list falls back to interpreter */
    list_elems[1].type = TYPE_STR;
    list_elems[1].v.str = str_dup("hello");
    ticks = 10;
    check(jit_program_execute(list_index1, env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "list non-int element did not fallback");
    check_differential(list_index1, env, 10, 0,
		       "list non-int element fallback differed from reference");
    free_var(env[0]);

    /* Scatter destructuring execution test */
    Var *scatter_elems = mymalloc(sizeof(Var) * 3, M_LIST);
    scatter_elems[0].type = TYPE_INT;
    scatter_elems[0].v.num = 2;
    scatter_elems[1].type = TYPE_INT;
    scatter_elems[1].v.num = 10;
    scatter_elems[2].type = TYPE_INT;
    scatter_elems[2].v.num = 32;
    env[0].type = TYPE_LIST;
    env[0].v.list = scatter_elems;
    ticks = 10;
    check(jit_program_execute(scatter, env, &result, &ticks, &timed_out,
			      &error, 0, 0, 0)
	  == JIT_RUN_RETURNED, "scatter destructure execution failed");
    check(result.type == TYPE_INT && result.v.num == 42,
	  "scatter destructure returned the wrong value");
    check_differential(scatter, env, 10, 0,
		       "scatter destructure differed from reference execution");
    free_var(env[0]);

    /* Call boundary deopt test */
    {
	JITProgram *call_prog = call_boundary_program();
	deopt_stack[0].type = TYPE_INT;
	deopt_stack[0].v.num = 0;
	ticks = 10;
	check(jit_program_execute(call_prog, env, &result, &ticks, &timed_out,
				  &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_FALLBACK, "call boundary did not return fallback");
	check(deopt.bytecode_pc == 25, "call boundary wrong bytecode_pc");
	check(deopt.stack_depth == 1, "call boundary wrong stack depth");
	check(deopt_stack[0].v.num == 99, "call boundary wrong stack value");
	jit_program_free(call_prog);
    }

    /* Property read deopt test */
    {
	JITProgram *get_prog = get_prop_program();
	deopt_stack[0].type = TYPE_INT;
	deopt_stack[0].v.num = 0;
	deopt_stack[1].type = TYPE_INT;
	deopt_stack[1].v.num = 0;
	ticks = 10;
	check(jit_program_execute(get_prog, env, &result, &ticks, &timed_out,
				  &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_FALLBACK, "get_prop did not return fallback");
	check(deopt.bytecode_pc == 30, "get_prop wrong bytecode_pc");
	check(deopt.stack_depth == 2, "get_prop wrong stack depth");
	check(deopt_stack[0].v.num == 0, "get_prop wrong obj stack value");
	check(deopt_stack[1].v.num == 123, "get_prop wrong prop stack value");
	jit_program_free(get_prog);
    }

    /* Verb call deopt boundary tests */
    {
	JITProgram *call_prog = call_verb_program();
	deep_env[0].type = TYPE_OBJ;
	deep_env[0].v.obj = 0;
	deep_env[1].type = TYPE_STR;
	deep_env[1].v.str = str_dup("test");
	call_args[0].type = TYPE_INT;
	call_args[0].v.num = 0;
	deep_env[2].type = TYPE_LIST;
	deep_env[2].v.list = call_args;
	ticks = 10;
	check(jit_program_execute(call_prog, deep_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_FALLBACK, "call_verb did not return fallback");
	check(ticks == 9 && deopt.ticks_charged == 1,
	      "call_verb reported the wrong charged tick count");
	check(deopt.bytecode_pc == 30, "call_verb wrong bytecode_pc");
	check(deopt.stack_depth == 3, "call_verb wrong stack depth");
	check(deopt_stack[0].type == TYPE_OBJ && deopt_stack[0].v.obj == 0,
	      "call_verb wrong object stack value");
	check(deopt_stack[1].type == TYPE_STR
	      && !strcmp(deopt_stack[1].v.str, "test"),
	      "call_verb wrong verb stack value");
	check(deopt_stack[2].type == TYPE_LIST
	      && deopt_stack[2].v.list[0].v.num == 0,
	      "call_verb wrong argument stack value");
	free_var(deopt_stack[1]);
	free_var(deopt_stack[2]);
	free_var(deep_env[1]);
	free_var(deep_env[2]);
	jit_program_free(call_prog);
    }

    /* Pure inlined built-ins execution tests */
    {
	JITProgram *abs_p = unary_program(-42, HIR_OP_ABS);
	ticks = 10;
	check(jit_program_execute(abs_p, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "abs execution failed");
	check(result.type == TYPE_INT && result.v.num == 42,
	      "abs returned wrong value");
	jit_program_free(abs_p);

	JITProgram *min_p = binary_program(10, 20, HIR_OP_MIN);
	ticks = 10;
	check(jit_program_execute(min_p, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "min execution failed");
	check(result.type == TYPE_INT && result.v.num == 10,
	      "min returned wrong value");
	jit_program_free(min_p);

	JITProgram *max_p = binary_program(10, 20, HIR_OP_MAX);
	ticks = 10;
	check(jit_program_execute(max_p, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "max execution failed");
	check(result.type == TYPE_INT && result.v.num == 20,
	      "max returned wrong value");
	jit_program_free(max_p);

	JITProgram *toint_p = unary_program(123, HIR_OP_TOINT);
	ticks = 10;
	check(jit_program_execute(toint_p, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "toint execution failed");
	check(result.type == TYPE_INT && result.v.num == 123,
	      "toint returned wrong value");
	jit_program_free(toint_p);

	JITProgram *typeof_p = unary_program(123, HIR_OP_TYPEOF);
	ticks = 10;
	check(jit_program_execute(typeof_p, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "typeof execution failed");
	check(result.type == TYPE_INT && result.v.num == TYPE_INT,
	      "typeof returned wrong value");
	jit_program_free(typeof_p);
    }

    /* Scalar object tests */
    {
	JITProgram *obj_p = object_return_program();
	Var obj_env[1];
	obj_env[0].type = TYPE_OBJ;
	obj_env[0].v.obj = 1234;
	ticks = 10;
	check(jit_program_execute(obj_p, obj_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "object return execution failed");
	check(result.type == TYPE_OBJ && result.v.obj == 1234,
	      "object return returned wrong value");
	check_differential(obj_p, obj_env, 10, 0, "object return differential");
	{
	    JITProgram *typeof_obj = unary_program(1234, HIR_OP_TYPEOF);
	    JITInstruction *constant = typeof_obj->blocks->first;
	    JITInstruction *unary = constant->next;

	    constant->literal_type = TYPE_OBJ;
	    unary->literal = TYPE_OBJ;
	    ticks = 10;
	    check(jit_program_execute(typeof_obj, obj_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED, "object typeof execution failed");
	    check(result.type == TYPE_INT && result.v.num == TYPE_OBJ,
		  "object typeof returned wrong value");
	    jit_program_free(typeof_obj);
	}

	/* Mismatched type guard fallback for object */
	obj_env[0].type = TYPE_INT;
	obj_env[0].v.num = 1234;
	ticks = 10;
	check(jit_program_execute(obj_p, obj_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "object guard mismatch failed to fallback");
	jit_program_free(obj_p);

	JITProgram *cmp_eq = object_compare_program(HIR_OP_EQ);
	Var cmp_env[2];
	cmp_env[0].type = TYPE_OBJ;
	cmp_env[0].v.obj = 42;
	cmp_env[1].type = TYPE_OBJ;
	cmp_env[1].v.obj = 42;
	ticks = 10;
	check(jit_program_execute(cmp_eq, cmp_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "object compare eq execution failed");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "object compare eq returned wrong value");
	check_differential(cmp_eq, cmp_env, 10, 0, "object compare eq differential");

	cmp_env[1].v.obj = 99;
	ticks = 10;
	check(jit_program_execute(cmp_eq, cmp_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "object compare ne execution failed");
	check(result.type == TYPE_INT && result.v.num == 0,
	      "object compare ne returned wrong value");
	check_differential(cmp_eq, cmp_env, 10, 0, "object compare ne differential");
	jit_program_free(cmp_eq);
    }

    /* Scalar float tests */
    {
	JITProgram *fl_p = float_return_program();
	Var fl_env[1];
	fl_env[0].type = TYPE_FLOAT;
	fl_env[0].v.fnum = box_fl(3.14159);
	ticks = 10;
	check(jit_program_execute(fl_p, fl_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float return execution failed");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 3.14159,
	      "float return returned wrong value");
	check_differential(fl_p, fl_env, 10, 0, "float return differential");

	/* Mismatched type guard fallback for float */
	fl_env[0].type = TYPE_INT;
	fl_env[0].v.num = 1234;
	ticks = 10;
	check(jit_program_execute(fl_p, fl_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "float guard mismatch failed to fallback");
	jit_program_free(fl_p);

	/* Float binary arithmetic */
	JITProgram *fl_add = float_binary_program(HIR_OP_ADD);
	Var bin_env[2];
	bin_env[0].type = TYPE_FLOAT;
	bin_env[0].v.fnum = box_fl(1.5);
	bin_env[1].type = TYPE_FLOAT;
	bin_env[1].v.fnum = box_fl(2.5);
	ticks = 10;
	check(jit_program_execute(fl_add, bin_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float add execution failed");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 4.0,
	      "float add returned wrong value");
	check_differential(fl_add, bin_env, 10, 0, "float add differential");
	jit_program_free(fl_add);

	/* Non-finite float results raise E_FLOAT. */
	JITProgram *fl_overflow = float_binary_program(HIR_OP_MUL);
	bin_env[0].v.fnum = box_fl(1.0e308);
	bin_env[1].v.fnum = box_fl(1.0e308);
	ticks = 10;
	check(jit_program_execute(fl_overflow, bin_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_ERROR, "float overflow did not error");
	check(error == E_FLOAT, "float overflow wrong error code");
	check_differential(fl_overflow, bin_env, 10, 0,
			   "float overflow differential");
	jit_program_free(fl_overflow);

	/* Float division and division by zero */
	JITProgram *fl_div = float_binary_program(HIR_OP_DIV);
	bin_env[0].v.fnum = box_fl(10.0);
	bin_env[1].v.fnum = box_fl(2.0);
	ticks = 10;
	check(jit_program_execute(fl_div, bin_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float div execution failed");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 5.0,
	      "float div returned wrong value");
	check_differential(fl_div, bin_env, 10, 0, "float div differential");

	bin_env[1].v.fnum = box_fl(0.0);
	ticks = 10;
	check(jit_program_execute(fl_div, bin_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_ERROR, "float div zero did not error");
	check(error == E_DIV, "float div zero wrong error code");
	check_differential(fl_div, bin_env, 10, 0, "float div zero differential");
	jit_program_free(fl_div);

	/* Float comparison */
	JITProgram *fl_cmp = float_compare_program(HIR_OP_LT);
	bin_env[0].v.fnum = box_fl(1.23);
	bin_env[1].v.fnum = box_fl(4.56);
	ticks = 10;
	check(jit_program_execute(fl_cmp, bin_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float cmp lt execution failed");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "float cmp lt returned wrong value");
	check_differential(fl_cmp, bin_env, 10, 0, "float cmp lt differential");
	jit_program_free(fl_cmp);

	/* Float unary */
	JITProgram *fl_neg = float_unary_program(3.5, HIR_OP_NEGATE);
	ticks = 10;
	check(jit_program_execute(fl_neg, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float negate execution failed");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == -3.5,
	      "float negate returned wrong value");
	check_differential(fl_neg, 0, 10, 0, "float negate differential");
	jit_program_free(fl_neg);

	JITProgram *fl_abs = float_unary_program(-7.25, HIR_OP_ABS);
	ticks = 10;
	check(jit_program_execute(fl_abs, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float abs execution failed");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 7.25,
	      "float abs returned wrong value");
	check_differential(fl_abs, 0, 10, 0, "float abs differential");
	jit_program_free(fl_abs);

	JITProgram *fl_not = float_unary_program(0.0, HIR_OP_NOT);
	ticks = 10;
	check(jit_program_execute(fl_not, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float not execution failed");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "float not returned wrong value");
	check_differential(fl_not, 0, 10, 0, "float not differential");
	jit_program_free(fl_not);

	JITProgram *fl_typeof = float_unary_program(12.34, HIR_OP_TYPEOF);
	ticks = 10;
	check(jit_program_execute(fl_typeof, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "float typeof execution failed");
	check(result.type == TYPE_INT && result.v.num == TYPE_FLOAT,
	      "float typeof returned wrong value");
	check_differential(fl_typeof, 0, 10, 0, "float typeof differential");
	jit_program_free(fl_typeof);
    }

    /* Scalar string tests */
    {
	JITProgram *str_p = string_return_program();
	Var str_env[1];
	str_env[0].type = TYPE_STR;
	str_env[0].v.str = str_dup("hello world");
	ticks = 10;
	check(jit_program_execute(str_p, str_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string return execution failed");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "hello world"),
	      "string return returned wrong value");
	check(var_refcount(result) >= 2, "string return refcount not incremented");
	free_var(result);
	free_var(str_env[0]);

	/* Mismatched type guard fallback for string */
	str_env[0].type = TYPE_INT;
	str_env[0].v.num = 1234;
	ticks = 10;
	check(jit_program_execute(str_p, str_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "string guard mismatch failed to fallback");
	jit_program_free(str_p);

	/* String constant program */
	JITProgram *str_const = string_const_program("constant string");
	ticks = 10;
	check(jit_program_execute(str_const, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string const execution failed");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "constant string"),
	      "string const returned wrong value");
	free_var(result);
	check_differential(str_const, 0, 10, 0, "string const differential");
	jit_program_free(str_const);

	/* String truth and comparison semantics require content inspection. */
	JITProgram *str_not = string_not_program("");
	ticks = 10;
	check(jit_program_execute(str_not, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "empty string not did not fallback");
	jit_program_free(str_not);

	JITProgram *str_eq = string_compare_program("same", "SAME", HIR_OP_EQ);
	ticks = 10;
	check(jit_program_execute(str_eq, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "string equality did not fallback");
	jit_program_free(str_eq);

	JITProgram *str_branch = string_branch_program();
	Var branch_env[1];
	branch_env[0].type = TYPE_STR;
	branch_env[0].v.str = str_dup("");
	ticks = 10;
	check(jit_program_execute(str_branch, branch_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "empty string branch did not fallback");
	free_var(branch_env[0]);
	jit_program_free(str_branch);
    }

    /* Non-integer list indexing tests */
    {
	Var list_env[1];
	Var *elements = mymalloc(sizeof(Var) * 2, M_LIST);

	/* 1. Object element */
	JITProgram *idx_obj = list_index_typed_program(TYPE_OBJ);
	elements[0].type = TYPE_INT;
	elements[0].v.num = 1;
	elements[1].type = TYPE_OBJ;
	elements[1].v.obj = 4321;
	list_env[0].type = TYPE_LIST;
	list_env[0].v.list = elements;
	ticks = 10;
	check(jit_program_execute(idx_obj, list_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "list index obj execution failed");
	check(result.type == TYPE_OBJ && result.v.obj == 4321,
	      "list index obj returned wrong value");
	free_var(result);
	check_differential(idx_obj, list_env, 10, 0, "list index obj differential");
	jit_program_free(idx_obj);

	/* 2. Float element */
	JITProgram *idx_fl = list_index_typed_program(TYPE_FLOAT);
	elements[1].type = TYPE_FLOAT;
	elements[1].v.fnum = box_fl(2.71828);
	ticks = 10;
	check(jit_program_execute(idx_fl, list_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "list index float execution failed");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 2.71828,
	      "list index float returned wrong value");
	free_var(result);
	check_differential(idx_fl, list_env, 10, 0, "list index float differential");
	jit_program_free(idx_fl);

	/* 3. String element */
	JITProgram *idx_str = list_index_typed_program(TYPE_STR);
	elements[1].type = TYPE_STR;
	elements[1].v.str = str_dup("list string element");
	ticks = 10;
	check(jit_program_execute(idx_str, list_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "list index str execution failed");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "list string element"),
	      "list index str returned wrong value");
	check(var_refcount(result) >= 2, "list index str refcount not incremented");
	free_var(result);
	check_differential(idx_str, list_env, 10, 0, "list index str differential");

	free_var(elements[1]);

	/* 4. Element type mismatch on index (expected string, found int) -> fallback */
	elements[1].type = TYPE_INT;
	elements[1].v.num = 999;
	ticks = 10;
	check(jit_program_execute(idx_str, list_env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK, "list index elem type mismatch did not fallback");
	jit_program_free(idx_str);
	myfree(elements, M_LIST);
    }

    /* Exception and finally stack marker deoptimization tests */
    {
	JITProgram *catch_deopt = catch_stack_marker_deopt_program();
	JITDeoptState deopt_state;
	Var deopt_stack[10];
	memset(deopt_stack, 0, sizeof(deopt_stack));
	ticks = 10;
	check(jit_program_execute(catch_deopt, 0, &result, &ticks, &timed_out,
				  &error, 0, &deopt_state, deopt_stack)
	      == JIT_RUN_FALLBACK, "catch marker deopt failed");
	check(deopt_state.stack_depth == 3, "catch marker deopt depth wrong");
	check(deopt_stack[0].type == TYPE_INT && deopt_stack[0].v.num == 0,
	      "catch marker codes wrong");
	check(deopt_stack[1].type == TYPE_INT && deopt_stack[1].v.num == 77,
	      "catch marker handler pc wrong");
	check(deopt_stack[2].type == TYPE_CATCH && deopt_stack[2].v.num == 1,
	      "catch marker type/arm wrong");
	free_var(deopt_stack[0]);
	free_var(deopt_stack[1]);
	free_var(deopt_stack[2]);
	jit_program_free(catch_deopt);

	JITProgram *fin_deopt = finally_stack_marker_deopt_program();
	memset(deopt_stack, 0, sizeof(deopt_stack));
	ticks = 10;
	check(jit_program_execute(fin_deopt, 0, &result, &ticks, &timed_out,
				  &error, 0, &deopt_state, deopt_stack)
	      == JIT_RUN_FALLBACK, "finally marker deopt failed");
	check(deopt_state.stack_depth == 1, "finally marker deopt depth wrong");
	check(deopt_stack[0].type == TYPE_FINALLY && deopt_stack[0].v.num == 88,
	      "finally marker type/handler wrong");
	free_var(deopt_stack[0]);
	jit_program_free(fin_deopt);
    }

    jit_program_free(program);
    jit_program_free(guard);
    jit_program_free(scatter);
    jit_program_free(local_arith);
    jit_program_free(two_locals);
    jit_program_free(list_index1);
    jit_program_free(list_index2);
    jit_program_free(list_index_low);
    jit_program_free(list_index_high);
    jit_program_free(deep_guard);
    jit_program_free(branch);
    jit_program_free(charge_tick);
    jit_program_free(divide);
    jit_program_free(divide_zero);
    jit_program_free(divide_overflow);
    jit_program_free(modulus_overflow);
    jit_program_free(power);
    jit_program_free(power_wrap);
    jit_program_free(power_negative);
    jit_program_free(power_error);
    jit_program_free(shift_left);
    jit_program_free(shift_right);
    jit_program_free(logical_shift);
    jit_program_free(shift_error);
    jit_program_free(negative_shift);
    jit_program_free(bit_and);
    jit_program_free(bit_xor);
    jit_program_free(bit_or);
    return failures != 0;
}
