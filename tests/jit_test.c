#include "jit_internal.h"

#include "my-math.h"
#include "my-stdio.h"
#include "my-string.h"

#include "integer_arithmetic.h"
#include "list.h"
#include "storage.h"
#include "utf.h"
#include "utils.h"

#include <limits.h>

#define jit_program_execute(p, e, r, t, to, err, loc, d, ds) \
    jit_program_execute(p, e, r, t, to, err, loc, d, ds, 2, -1)

static int failures;

static void check(int, const char *);
extern void hir_test_set_length_protected(int);

struct machine_dump {
    int lines;
    int valid_first_line;
};

struct mir_dump {
    int lines;
    int found_source_marker;
};

static void
check_mir_line(const char *line, void *data)
{
    struct mir_dump *dump = data;

    dump->lines++;
    if (strstr(line, "pc_11_line_7_"))
	dump->found_source_marker = 1;
}

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
    result->func = FUNC_NOT_FOUND;
    return result;
}

static void
add_entry_deopt_map(JITProgram *program)
{
    program->num_deopt_maps = 1;
    program->deopt_maps = allocate(sizeof(JITDeoptMap));
    program->deopt_maps[0].builtin_args = -1;
    program->deopt_maps[0].operation = -1;
    program->deopt_maps[0].reason = JIT_DEOPT_TYPE_GUARD;
}

static JITProgram *
new_jit_program(void)
{
    JITProgram *program = allocate(sizeof(JITProgram));

    program->state = JIT_STATE_PENDING;
    program->reason = str_dup("none");
    program->diagnostic = str_dup("none");
    program->eligible = 1;
    return program;
}

static JITProgram *
arithmetic_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *one = instruction(HIR_TAC_CONST);
    JITInstruction *two = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *add = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *c = instruction(HIR_TAC_CONST);
    JITInstruction *unary = instruction(HIR_TAC_UNARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *binary = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load0 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *binary = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *index = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *c1 = instruction(HIR_TAC_CONST);
    JITInstruction *idx1 = instruction(HIR_TAC_BINARY);
    JITInstruction *c2 = instruction(HIR_TAC_CONST);
    JITInstruction *idx2 = instruction(HIR_TAC_BINARY);
    JITInstruction *add = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *c1 = instruction(HIR_TAC_CONST);
    JITInstruction *call = instruction(HIR_TAC_CALL);
    JITDeoptMap *map;

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
    map->builtin_func = 17;
    map->reason = JIT_DEOPT_BUILTIN_CALL;
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
builtin_call_program(unsigned func)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_args = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *call = instruction(HIR_TAC_CALL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 3;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_is_tagged = allocate(3);
    program->value_types[1] = TYPE_LIST;
    program->value_is_tagged[2] = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->resume_key.code_unit = 0;
    map->resume_key.site = 2;
    map->reason = JIT_DEOPT_BUILTIN_CALL;
    map->builtin_func = func;
    map->native_resume_valid = 1;
    map->num_resume_values = 1;
    map->resume_values = allocate(sizeof(JITResumeValue));
    map->resume_values[0].value = 2;
    map->resume_values[0].source = JIT_RESUME_RESULT;
    map->bytecode_pc = map->error_pc = 25;
    map->stack_depth = 1;
    map->num_locals = 1;
    map->local_values = allocate(sizeof(int));
    map->local_types = allocate(sizeof(var_type));
    map->local_values[0] = 1;
    map->local_types[0] = TYPE_LIST;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 1;
    map->stack_types[0] = TYPE_LIST;

    program->blocks = program->last_block = block;
    block->id = 1;
    load_args->value = 1;
    load_args->local_id = 0;
    load_args->literal_type = TYPE_LIST;
    load_args->next = call;
    call->value = 2;
    call->src1 = 1;
    call->deopt_map = 1;
    call->resume_key = map->resume_key;
    call->bytecode_pc = 25;
    call->next = return_instr;
    return_instr->src1 = 2;
    return_instr->literal_type = TYPE_ANY;
    block->first = load_args;
    block->last = return_instr;
    return program;
}

static JITProgram *
get_prop_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *c1 = instruction(HIR_TAC_CONST);
    JITInstruction *c2 = instruction(HIR_TAC_CONST);
    JITInstruction *get = instruction(HIR_TAC_BINARY);
    JITDeoptMap *map;

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

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
list_constant_program(int size)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *list_const = instruction(HIR_TAC_CONST);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    Var list = new_list(size);
    int i;

    for (i = 1; i <= size; i++) {
	list.v.list[i].type = TYPE_INT;
	list.v.list[i].v.num = i * 10;
    }

    program->num_values = 2;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 2);
    program->value_types[1] = TYPE_LIST;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    list_const->value = 1;
    list_const->literal_type = TYPE_LIST;
    list_const->literal = (uintptr_t) list.v.list;
    ret->src1 = 1;
    ret->literal_type = TYPE_LIST;
    list_const->next = ret;
    block->first = list_const;
    block->last = ret;
    return program;
}

static JITProgram *
in_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_lhs = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_rhs = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *in_tac = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[1] = TYPE_INT;
    program->value_types[2] = TYPE_LIST;
    program->value_types[3] = TYPE_INT;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 12;
    map->stack_depth = 2;
    map->ticks_charged = 1;
    map->num_locals = 2;
    map->local_values = allocate(sizeof(int) * 2);
    map->local_values[0] = 1;
    map->local_values[1] = 2;
    map->local_types = allocate(sizeof(var_type) * 2);
    map->local_types[0] = TYPE_INT;
    map->local_types[1] = TYPE_LIST;
    map->stack_values = allocate(sizeof(int) * 2);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_types = allocate(sizeof(var_type) * 2);
    map->stack_types[0] = TYPE_INT;
    map->stack_types[1] = TYPE_LIST;

    program->blocks = program->last_block = block;
    block->id = 1;
    load_lhs->value = 1;
    load_lhs->local_id = 0;
    load_lhs->literal_type = TYPE_INT;
    load_lhs->deopt_map = 0;
    load_rhs->value = 2;
    load_rhs->local_id = 1;
    load_rhs->literal_type = TYPE_LIST;
    load_rhs->deopt_map = 0;
    tick->source_lineno = 7;
    tick->bytecode_pc = 12;
    in_tac->source_lineno = 7;
    in_tac->bytecode_pc = 12;
    in_tac->value = 3;
    in_tac->src1 = 1;
    in_tac->src2 = 2;
    in_tac->op = HIR_OP_IN;
    in_tac->deopt_map = 1;
    ret->src1 = 3;

    load_lhs->next = load_rhs;
    load_rhs->next = tick;
    tick->next = in_tac;
    in_tac->next = ret;
    block->first = load_lhs;
    block->last = ret;
    return program;
}

static JITProgram *
branch_program(void)
{
    JITProgram *program = new_jit_program();
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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_obj = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_verb = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_args = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *tick = instruction(HIR_TAC_TICK);
    JITInstruction *call_verb = instruction(HIR_TAC_CALL_VERB);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 3;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_is_tagged = allocate(5);
    program->value_types[1] = TYPE_OBJ;
    program->value_types[2] = TYPE_STR;
    program->value_types[3] = TYPE_LIST;
    program->value_is_tagged[4] = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(JITDeoptMap));
    program->num_deopt_maps = 2;
    map->resume_key.code_unit = 0;
    map->resume_key.site = 1;
    map->reason = JIT_DEOPT_VERB_CALL;
    map->native_resume_valid = 1;
    map->num_resume_values = 1;
    map->resume_values = allocate(sizeof(JITResumeValue));
    map->resume_values[0].value = 4;
    map->resume_values[0].source = JIT_RESUME_RESULT;
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
    call_verb->resume_key = map->resume_key;
    call_verb->next = return_instr;
    return_instr->src1 = 4;
    return_instr->literal_type = TYPE_ANY;
    block->first = load_obj;
    block->last = return_instr;
    return program;
}

static JITProgram *
object_return_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_local = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_obj1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_obj2 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *cmp = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_local = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_f1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_f2 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *bin = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_f1 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_f2 = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *cmp = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *unary = instruction(HIR_TAC_UNARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_local = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *left = instruction(HIR_TAC_CONST);
    JITInstruction *right = instruction(HIR_TAC_CONST);
    JITInstruction *compare = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);
    char *left_string = str_dup(lhs);
    char *right_string = str_dup(rhs);

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
string_concat_program(const char *left_string, const char *right_string)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *left = instruction(HIR_TAC_CONST);
    JITInstruction *right = instruction(HIR_TAC_CONST);
    JITInstruction *concat = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);
    char *ls = str_dup(left_string);
    char *rs = str_dup(right_string);

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_STR;
    program->value_types[3] = TYPE_STR;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    left->value = 1;
    left->literal = (uintptr_t) ls;
    left->literal_type = TYPE_STR;
    left->next = right;
    right->value = 2;
    right->literal = (uintptr_t) rs;
    right->literal_type = TYPE_STR;
    right->next = concat;
    concat->value = 3;
    concat->src1 = 1;
    concat->src2 = 2;
    concat->op = HIR_OP_ADD;
    concat->deopt_map = 0;
    concat->next = return_instr;
    return_instr->src1 = 3;
    return_instr->literal_type = TYPE_STR;
    block->first = left;
    block->last = return_instr;
    return program;
}

static JITProgram *
string_index_program(const char *s, int idx)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *str_const = instruction(HIR_TAC_CONST);
    JITInstruction *idx_const = instruction(HIR_TAC_CONST);
    JITInstruction *index_op = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);
    char *str = str_dup(s);

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_STR;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    str_const->value = 1;
    str_const->literal = (uintptr_t) str;
    str_const->literal_type = TYPE_STR;
    str_const->next = idx_const;
    idx_const->value = 2;
    idx_const->literal = idx;
    idx_const->literal_type = TYPE_INT;
    idx_const->next = index_op;
    index_op->value = 3;
    index_op->src1 = 1;
    index_op->src2 = 2;
    index_op->op = HIR_OP_INDEX;
    index_op->deopt_map = 0;
    index_op->next = return_instr;
    return_instr->src1 = 3;
    return_instr->literal_type = TYPE_STR;
    block->first = str_const;
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
string_length_program(const char *s)
{
    JITProgram *program = string_const_program(s);
    JITInstruction *constant = program->blocks->first;
    JITInstruction *return_instr = constant->next;
    JITInstruction *length_instr = instruction(HIR_TAC_UNARY);
    JITDeoptMap *map;

    program->num_values = 3;
    program->num_deopt_maps = 2;
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    memset(&program->deopt_maps[1], 0, sizeof(JITDeoptMap));
    map = &program->deopt_maps[1];
    map->reason = JIT_DEOPT_ARITHMETIC_TYPE;
    map->builtin_func = 6;
    map->builtin_args = 1;
    map->stack_depth = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 1;
    map->stack_types[0] = TYPE_STR;
    myfree(program->value_types, M_PROGRAM);
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_INT;
    constant->next = length_instr;
    length_instr->value = 2;
    length_instr->src1 = 1;
    length_instr->func = 6;
    length_instr->op = HIR_OP_LENGTH;
    length_instr->deopt_map = 1;
    length_instr->next = return_instr;
    return_instr->src1 = 2;
    return_instr->literal_type = TYPE_INT;
    return program;
}

static JITProgram *
catch_stack_marker_deopt_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_codes = instruction(HIR_TAC_CONST);
    JITInstruction *const_pc = instruction(HIR_TAC_CONST);
    JITInstruction *const_catch = instruction(HIR_TAC_CONST);
    JITInstruction *deopt_op = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_INT;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_CATCH;

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

    deopt_op->deopt_map = 1;
    deopt_op->bytecode_pc = 25;

    block->first = const_codes;
    block->last = deopt_op;
    return program;
}

static JITProgram *
exception_boundary_deopt_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *deopt = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 1;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    map = &program->deopt_maps[1];
    map->bytecode_pc = 19;
    map->error_pc = 19;
    program->blocks = program->last_block = block;
    block->id = 1;
    block->first = block->last = deopt;
    deopt->deopt_map = 1;
    deopt->bytecode_pc = 19;
    return program;
}

static JITProgram *
fork_boundary_deopt_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_time = instruction(HIR_TAC_CONST);
    JITInstruction *deopt = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 2;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 2);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_INT;

    map = &program->deopt_maps[1];
    map->bytecode_pc = 33;
    map->error_pc = 33;
    map->stack_depth = 1;
    map->ticks_charged = 0;
    map->num_locals = 0;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 1;
    map->stack_types[0] = TYPE_INT;

    program->blocks = program->last_block = block;
    block->id = 1;

    const_time->value = 1;
    const_time->literal = 5;
    const_time->literal_type = TYPE_INT;
    const_time->next = deopt;

    deopt->deopt_map = 1;
    deopt->bytecode_pc = 33;

    block->first = const_time;
    block->last = deopt;
    return program;
}

static JITProgram *
finally_stack_marker_deopt_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_finally = instruction(HIR_TAC_CONST);
    JITInstruction *deopt_op = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 2;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 2);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_FINALLY;

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

    deopt_op->deopt_map = 1;
    deopt_op->bytecode_pc = 40;

    block->first = const_finally;
    block->last = deopt_op;
    return program;
}

static JITProgram *
nested_try_except_finally_deopt_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_finally = instruction(HIR_TAC_CONST);
    JITInstruction *const_codes = instruction(HIR_TAC_CONST);
    JITInstruction *const_pc = instruction(HIR_TAC_CONST);
    JITInstruction *const_catch = instruction(HIR_TAC_CONST);
    JITInstruction *deopt_op = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_FINALLY;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_INT;
    program->value_types[4] = TYPE_CATCH;

    map = &program->deopt_maps[1];
    map->bytecode_pc = 60;
    map->error_pc = 60;
    map->stack_depth = 4;
    map->ticks_charged = 1;
    map->num_locals = 0;
    map->stack_values = allocate(sizeof(int) * 4);
    map->stack_types = allocate(sizeof(var_type) * 4);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    map->stack_values[3] = 4;
    map->stack_types[0] = TYPE_FINALLY;
    map->stack_types[1] = TYPE_INT;
    map->stack_types[2] = TYPE_INT;
    map->stack_types[3] = TYPE_CATCH;

    program->blocks = program->last_block = block;
    block->id = 1;

    const_finally->value = 1;
    const_finally->literal = 99;
    const_finally->literal_type = TYPE_FINALLY;
    const_finally->next = const_codes;

    const_codes->value = 2;
    const_codes->literal = 0;
    const_codes->literal_type = TYPE_INT;
    const_codes->next = const_pc;

    const_pc->value = 3;
    const_pc->literal = 55;
    const_pc->literal_type = TYPE_INT;
    const_pc->next = const_catch;

    const_catch->value = 4;
    const_catch->literal = 1;
    const_catch->literal_type = TYPE_CATCH;
    const_catch->next = deopt_op;

    deopt_op->deopt_map = 1;
    deopt_op->bytecode_pc = 60;

    block->first = const_finally;
    block->last = deopt_op;
    return program;
}

static JITProgram *
range_ref_test_program(var_type base_type)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_base = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_from = instruction(HIR_TAC_CONST);
    JITInstruction *const_to = instruction(HIR_TAC_CONST);
    JITInstruction *range_op = instruction(HIR_TAC_RANGE_REF);
    JITInstruction *ret_op = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_types[0] = TYPE_NONE;
    program->value_types[1] = base_type;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_INT;
    program->value_types[4] = base_type;

    map = &program->deopt_maps[1];
    map->bytecode_pc = 10;
    map->error_pc = 10;
    map->stack_depth = 3;
    map->ticks_charged = 1;
    map->num_locals = 1;
    map->local_values = allocate(sizeof(int));
    map->local_types = allocate(sizeof(var_type));
    map->local_values[0] = 1;
    map->local_types[0] = base_type;
    map->stack_values = allocate(sizeof(int) * 3);
    map->stack_types = allocate(sizeof(var_type) * 3);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    map->stack_types[0] = base_type;
    map->stack_types[1] = TYPE_INT;
    map->stack_types[2] = TYPE_INT;

    program->blocks = program->last_block = block;
    block->id = 1;

    load_base->value = 1;
    load_base->local_id = 0;
    load_base->literal_type = base_type;
    load_base->next = const_from;

    const_from->value = 2;
    const_from->literal = 2;
    const_from->literal_type = TYPE_INT;
    const_from->next = const_to;

    const_to->value = 3;
    const_to->literal = 4;
    const_to->literal_type = TYPE_INT;
    const_to->next = range_op;

    range_op->value = 4;
    range_op->src1 = 1;
    range_op->src2 = 2;
    range_op->deopt_map = 1;
    range_op->bytecode_pc = 10;
    range_op->next = ret_op;

    ret_op->src1 = 4;
    ret_op->literal_type = base_type;

    block->first = load_base;
    block->last = ret_op;
    return program;
}

static JITProgram *
list_index_typed_program(var_type elem_type)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_idx = instruction(HIR_TAC_CONST);
    JITInstruction *index_instr = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = instruction(HIR_TAC_RETURN);

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

static JITProgram *
list_index_tagged_deopt_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_idx = instruction(HIR_TAC_CONST);
    JITInstruction *index_instr = instruction(HIR_TAC_BINARY);
    JITInstruction *copy_instr = instruction(HIR_TAC_PARALLEL_COPY);
    JITInstruction *deopt_instr = instruction(HIR_TAC_DEOPT);
    JITCopy *copy = allocate(sizeof(JITCopy));
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_is_tagged = allocate(5);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_is_tagged[3] = 1;
    program->value_is_tagged[4] = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->bytecode_pc = 12;
    map->source_lineno = 4;
    map->stack_depth = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 4;
    map->stack_types[0] = TYPE_ANY;
    program->blocks = program->last_block = block;
    block->id = 1;

    load_list->value = 1;
    load_list->local_id = 0;
    load_list->literal_type = TYPE_LIST;
    load_list->next = const_idx;
    const_idx->value = 2;
    const_idx->literal = 1;
    const_idx->literal_type = TYPE_INT;
    const_idx->next = index_instr;
    index_instr->value = 3;
    index_instr->src1 = 1;
    index_instr->src2 = 2;
    index_instr->op = HIR_OP_INDEX;
    index_instr->next = copy_instr;
    copy->src = 3;
    copy->dst = 4;
    copy_instr->copies = copy;
    copy_instr->next = deopt_instr;
    deopt_instr->deopt_map = 1;
    block->first = load_list;
    block->last = deopt_instr;
    return program;
}

static JITProgram *
list_index_tagged_return_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_idx = instruction(HIR_TAC_CONST);
    JITInstruction *index_instr = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 4;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_is_tagged = allocate(4);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_is_tagged[3] = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load_list->value = 1;
    load_list->local_id = 0;
    load_list->literal_type = TYPE_LIST;
    load_list->next = const_idx;
    const_idx->value = 2;
    const_idx->literal = 1;
    const_idx->literal_type = TYPE_INT;
    const_idx->next = index_instr;
    index_instr->value = 3;
    index_instr->src1 = 1;
    index_instr->src2 = 2;
    index_instr->op = HIR_OP_INDEX;
    index_instr->next = ret;
    ret->src1 = 3;
    ret->literal_type = TYPE_INT;
    block->first = load_list;
    block->last = ret;
    return program;
}

static JITProgram *
list_index_tagged_base_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_outer = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_one = instruction(HIR_TAC_CONST);
    JITInstruction *load_base = instruction(HIR_TAC_BINARY);
    JITInstruction *const_two = instruction(HIR_TAC_CONST);
    JITInstruction *load_index = instruction(HIR_TAC_BINARY);
    JITInstruction *load_value = instruction(HIR_TAC_BINARY);
    JITInstruction *deopt = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 7;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 7);
    program->value_is_tagged = allocate(7);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_types[4] = TYPE_INT;
    program->value_is_tagged[3] = 1;
    program->value_is_tagged[5] = 1;
    program->value_is_tagged[6] = 1;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->stack_depth = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 6;
    map->stack_types[0] = TYPE_ANY;
    program->blocks = program->last_block = block;
    block->id = 1;

    load_outer->value = 1;
    load_outer->local_id = 0;
    load_outer->literal_type = TYPE_LIST;
    load_outer->next = const_one;
    const_one->value = 2;
    const_one->literal = 1;
    const_one->literal_type = TYPE_INT;
    const_one->next = load_base;
    load_base->value = 3;
    load_base->src1 = 1;
    load_base->src2 = 2;
    load_base->op = HIR_OP_INDEX;
    load_base->next = const_two;
    const_two->value = 4;
    const_two->literal = 2;
    const_two->literal_type = TYPE_INT;
    const_two->next = load_index;
    load_index->value = 5;
    load_index->src1 = 1;
    load_index->src2 = 4;
    load_index->op = HIR_OP_INDEX;
    load_index->next = load_value;
    load_value->value = 6;
    load_value->src1 = 3;
    load_value->src2 = 5;
    load_value->op = HIR_OP_INDEX;
    load_value->next = deopt;
    deopt->deopt_map = 1;
    block->first = load_outer;
    block->last = deopt;
    return program;
}

static JITProgram *
list_index_tagged_consumer_program(HIROp op)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_idx = instruction(HIR_TAC_CONST);
    JITInstruction *index_instr = instruction(HIR_TAC_BINARY);
    JITInstruction *rhs_instr = instruction(op == HIR_OP_IN
					    ? HIR_TAC_LOAD_LOCAL : HIR_TAC_CONST);
    JITInstruction *consumer = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 6;
    program->num_vars = op == HIR_OP_IN ? 2 : 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 6);
    program->value_is_tagged = allocate(6);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_is_tagged[3] = 1;
    program->value_types[4] = op == HIR_OP_IN ? TYPE_LIST : TYPE_STR;
    program->value_types[5] = TYPE_INT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load_list->value = 1;
    load_list->local_id = 0;
    load_list->literal_type = TYPE_LIST;
    load_list->next = const_idx;
    const_idx->value = 2;
    const_idx->literal = 1;
    const_idx->literal_type = TYPE_INT;
    const_idx->next = index_instr;
    index_instr->value = 3;
    index_instr->src1 = 1;
    index_instr->src2 = 2;
    index_instr->op = HIR_OP_INDEX;
    index_instr->next = rhs_instr;
    rhs_instr->value = 4;
    if (op == HIR_OP_IN) {
	rhs_instr->local_id = 1;
	rhs_instr->literal_type = TYPE_LIST;
    } else {
	const char *literal = str_dup("tagged element");
	rhs_instr->literal = (Num) (intptr_t) literal;
	rhs_instr->literal_type = TYPE_STR;
    }
    rhs_instr->next = consumer;
    consumer->value = 5;
    consumer->src1 = 3;
    consumer->src2 = 4;
    consumer->op = op;
    consumer->next = ret;
    ret->src1 = 5;
    ret->literal_type = TYPE_INT;
    block->first = load_list;
    block->last = ret;
    return program;
}

static JITProgram *
tagged_unary_program(HIROp op)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *unary = instruction(HIR_TAC_UNARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 3;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_is_tagged = allocate(3);
    program->value_is_tagged[1] = 1;
    program->value_types[2] = TYPE_INT;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load->value = 1;
    load->local_id = 0;
    load->literal_type = TYPE_ANY;
    load->next = unary;
    unary->value = 2;
    unary->src1 = 1;
    unary->op = op;
    unary->next = ret;
    ret->src1 = 2;
    ret->literal_type = TYPE_INT;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
tagged_binary_program(HIROp op)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_lhs = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *load_rhs = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *binary = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 4);
    program->value_is_tagged = allocate(4);
    program->value_is_tagged[1] = 1;
    program->value_is_tagged[2] = 1;
    program->value_is_tagged[3] = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load_lhs->value = 1;
    load_lhs->local_id = 0;
    load_lhs->literal_type = TYPE_ANY;
    load_lhs->next = load_rhs;
    load_rhs->value = 2;
    load_rhs->local_id = 1;
    load_rhs->literal_type = TYPE_ANY;
    load_rhs->next = binary;
    binary->value = 3;
    binary->src1 = 1;
    binary->src2 = 2;
    binary->op = op;
    binary->next = ret;
    ret->src1 = 3;
    ret->literal_type = TYPE_INT;
    block->first = load_lhs;
    block->last = ret;
    return program;
}

static JITProgram *
tagged_string_pipeline_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_one = instruction(HIR_TAC_CONST);
    JITInstruction *load_subject = instruction(HIR_TAC_BINARY);
    JITInstruction *const_two = instruction(HIR_TAC_CONST);
    JITInstruction *load_delim = instruction(HIR_TAC_BINARY);
    JITInstruction *concat = instruction(HIR_TAC_BINARY);
    JITInstruction *index = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 8;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 8);
    program->value_is_tagged = allocate(8);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_types[4] = TYPE_INT;
    program->value_types[7] = TYPE_INT;
    program->value_is_tagged[3] = 1;
    program->value_is_tagged[5] = 1;
    program->value_is_tagged[6] = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;

    load_list->value = 1;
    load_list->local_id = 0;
    load_list->literal_type = TYPE_LIST;
    load_list->next = const_one;
    const_one->value = 2;
    const_one->literal = 1;
    const_one->literal_type = TYPE_INT;
    const_one->next = load_subject;
    load_subject->value = 3;
    load_subject->src1 = 1;
    load_subject->src2 = 2;
    load_subject->op = HIR_OP_INDEX;
    load_subject->next = const_two;
    const_two->value = 4;
    const_two->literal = 2;
    const_two->literal_type = TYPE_INT;
    const_two->next = load_delim;
    load_delim->value = 5;
    load_delim->src1 = 1;
    load_delim->src2 = 4;
    load_delim->op = HIR_OP_INDEX;
    load_delim->next = concat;
    concat->value = 6;
    concat->src1 = 3;
    concat->src2 = 5;
    concat->op = HIR_OP_ADD;
    concat->next = index;
    index->value = 7;
    index->src1 = 6;
    index->src2 = 5;
    index->op = HIR_OP_INDEX_BF;
    index->next = ret;
    ret->src1 = 7;
    ret->literal_type = TYPE_INT;
    block->first = load_list;
    block->last = ret;
    return program;
}

static JITProgram *
verb_call_boundary_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *call_verb = instruction(HIR_TAC_CALL_VERB);
    JITDeoptMap *map;

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    map = &program->deopt_maps[1];
    map->bytecode_pc = 55;
    map->error_pc = 55;
    program->blocks = program->last_block = block;
    block->id = 1;
    block->first = block->last = call_verb;
    call_verb->deopt_map = 1;
    call_verb->bytecode_pc = 55;
    return program;
}

static JITProgram *
prop_boundary_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *put_prop = instruction(HIR_TAC_PUT_PROP);
    JITDeoptMap *map;

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    map = &program->deopt_maps[1];
    map->bytecode_pc = 60;
    map->error_pc = 60;
    program->blocks = program->last_block = block;
    block->id = 1;
    block->first = block->last = put_prop;
    put_prop->deopt_map = 1;
    put_prop->bytecode_pc = 60;
    return program;
}

static JITProgram *
range_boundary_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *range_ref = instruction(HIR_TAC_RANGE_REF);
    JITDeoptMap *map;

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    map = &program->deopt_maps[1];
    map->bytecode_pc = 65;
    map->error_pc = 65;
    program->blocks = program->last_block = block;
    block->id = 1;
    block->first = block->last = range_ref;
    range_ref->deopt_map = 1;
    range_ref->bytecode_pc = 65;
    return program;
}

static JITProgram *
range_set_boundary_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *range_set = instruction(HIR_TAC_RANGE_SET);
    JITDeoptMap *map;

    program->num_values = 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    map = &program->deopt_maps[1];
    map->bytecode_pc = 70;
    map->error_pc = 70;
    program->blocks = program->last_block = block;
    block->id = 1;
    block->first = block->last = range_set;
    range_set->deopt_map = 1;
    range_set->bytecode_pc = 70;
    return program;
}

static JITProgram *
nested_loop_branch_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *b1 = allocate(sizeof(JITBlock));
    JITBlock *b2 = allocate(sizeof(JITBlock));
    JITBlock *b3 = allocate(sizeof(JITBlock));
    JITBlock *b4 = allocate(sizeof(JITBlock));
    JITBlock *b5 = allocate(sizeof(JITBlock));
    JITBlock *b6 = allocate(sizeof(JITBlock));
    JITBlock *b7 = allocate(sizeof(JITBlock));

    program->num_values = 20;
    program->num_vars = 0;
    program->num_blocks = 7;
    add_entry_deopt_map(program);

    program->blocks = b1;
    program->last_block = b7;

    b1->id = 1; b1->next = b2;
    b2->id = 2; b2->next = b3;
    b3->id = 3; b3->next = b4;
    b4->id = 4; b4->next = b5;
    b5->id = 5; b5->next = b6;
    b6->id = 6; b6->next = b7;
    b7->id = 7; b7->next = 0;

    /* B1 (Entry) */
    JITInstruction *c_acc0 = instruction(HIR_TAC_CONST);
    c_acc0->value = 1; c_acc0->literal = 0; c_acc0->literal_type = TYPE_INT;

    JITInstruction *c_i1 = instruction(HIR_TAC_CONST);
    c_i1->value = 2; c_i1->literal = 1; c_i1->literal_type = TYPE_INT;

    JITInstruction *cp_entry = instruction(HIR_TAC_PARALLEL_COPY);
    JITCopy *cp_e1 = allocate(sizeof(JITCopy));
    JITCopy *cp_e2 = allocate(sizeof(JITCopy));
    cp_e1->dst = 5; cp_e1->src = 1; cp_e1->next = cp_e2;
    cp_e2->dst = 6; cp_e2->src = 2; cp_e2->next = 0;
    cp_entry->copies = cp_e1;

    JITInstruction *jmp_entry = instruction(HIR_TAC_JUMP);
    c_acc0->next = c_i1; c_i1->next = cp_entry; cp_entry->next = jmp_entry;
    b1->first = c_acc0; b1->last = jmp_entry;
    b1->num_successors = 1;
    b1->successors[0] = 2;

    /* B2 (Header) */
    JITInstruction *t_hdr = instruction(HIR_TAC_TICK);
    JITInstruction *c_limit = instruction(HIR_TAC_CONST);
    c_limit->value = 7; c_limit->literal = 10; c_limit->literal_type = TYPE_INT;

    JITInstruction *cmp_le = instruction(HIR_TAC_BINARY);
    cmp_le->value = 8; cmp_le->src1 = 6; cmp_le->src2 = 7; cmp_le->op = HIR_OP_LE;

    JITInstruction *br_hdr = instruction(HIR_TAC_BRANCH_FALSE);
    br_hdr->src1 = 8;

    t_hdr->next = c_limit; c_limit->next = cmp_le; cmp_le->next = br_hdr;
    b2->first = t_hdr; b2->last = br_hdr;
    b2->num_successors = 2;
    b2->successors[0] = 7;
    b2->successors[1] = 3;

    /* B3 (Body) */
    JITInstruction *c_mask = instruction(HIR_TAC_CONST);
    c_mask->value = 9; c_mask->literal = 1; c_mask->literal_type = TYPE_INT;

    JITInstruction *and_instr = instruction(HIR_TAC_BINARY);
    and_instr->value = 10; and_instr->src1 = 6; and_instr->src2 = 9; and_instr->op = HIR_OP_BITAND;

    JITInstruction *br_body = instruction(HIR_TAC_BRANCH_FALSE);
    br_body->src1 = 10;

    c_mask->next = and_instr; and_instr->next = br_body;
    b3->first = c_mask; b3->last = br_body;
    b3->num_successors = 2;
    b3->successors[0] = 4;
    b3->successors[1] = 5;

    /* B4 (Even) */
    JITInstruction *add_even = instruction(HIR_TAC_BINARY);
    add_even->value = 11; add_even->src1 = 5; add_even->src2 = 6; add_even->op = HIR_OP_ADD;

    JITInstruction *cp_even = instruction(HIR_TAC_PARALLEL_COPY);
    JITCopy *cp_ev = allocate(sizeof(JITCopy));
    cp_ev->dst = 13; cp_ev->src = 11; cp_ev->next = 0;
    cp_even->copies = cp_ev;

    JITInstruction *jmp_even = instruction(HIR_TAC_JUMP);
    add_even->next = cp_even; cp_even->next = jmp_even;
    b4->first = add_even; b4->last = jmp_even;
    b4->num_successors = 1;
    b4->successors[0] = 6;

    /* B5 (Odd) */
    JITInstruction *sub_odd = instruction(HIR_TAC_BINARY);
    sub_odd->value = 12; sub_odd->src1 = 5; sub_odd->src2 = 6; sub_odd->op = HIR_OP_SUB;

    JITInstruction *cp_odd = instruction(HIR_TAC_PARALLEL_COPY);
    JITCopy *cp_od = allocate(sizeof(JITCopy));
    cp_od->dst = 13; cp_od->src = 12; cp_od->next = 0;
    cp_odd->copies = cp_od;

    JITInstruction *jmp_odd = instruction(HIR_TAC_JUMP);
    sub_odd->next = cp_odd; cp_odd->next = jmp_odd;
    b5->first = sub_odd; b5->last = jmp_odd;
    b5->num_successors = 1;
    b5->successors[0] = 6;

    /* B6 (Latch) */
    JITInstruction *c_inc = instruction(HIR_TAC_CONST);
    c_inc->value = 14; c_inc->literal = 1; c_inc->literal_type = TYPE_INT;

    JITInstruction *add_inc = instruction(HIR_TAC_BINARY);
    add_inc->value = 15; add_inc->src1 = 6; add_inc->src2 = 14; add_inc->op = HIR_OP_ADD;

    JITInstruction *cp_latch = instruction(HIR_TAC_PARALLEL_COPY);
    JITCopy *cp_l1 = allocate(sizeof(JITCopy));
    JITCopy *cp_l2 = allocate(sizeof(JITCopy));
    cp_l1->dst = 5; cp_l1->src = 13; cp_l1->next = cp_l2;
    cp_l2->dst = 6; cp_l2->src = 15; cp_l2->next = 0;
    cp_latch->copies = cp_l1;

    JITInstruction *jmp_latch = instruction(HIR_TAC_JUMP);
    c_inc->next = add_inc; add_inc->next = cp_latch; cp_latch->next = jmp_latch;
    b6->first = c_inc; b6->last = jmp_latch;
    b6->num_successors = 1;
    b6->successors[0] = 2;

    /* B7 (Exit) */
    JITInstruction *ret_exit = instruction(HIR_TAC_RETURN);
    ret_exit->src1 = 5;
    b7->first = b7->last = ret_exit;

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

static Var
materialize_deopt_value(var_type type, Num raw)
{
    Var value;

    value.type = type;
    if (type == TYPE_STR)
	value.v.str = (const char *) (intptr_t) raw;
    else if (type == TYPE_LIST)
	value.v.list = (Var *) (intptr_t) raw;
    else if (type == TYPE_OBJ)
	value.v.obj = raw;
    else if (type == TYPE_ERR)
	value.v.err = raw;
    else if (type == TYPE_FLOAT) {
	FlNum f;
	memcpy(&f, &raw, sizeof(FlNum));
	value.v.fnum = box_fl(f);
	return value;
    }
    else
	value.v.num = raw;
    return var_ref(value);
}

static JITRunResult
reference_execute(JITProgram *program, Var *env, Var *result, int *ticks,
		  int *timed_out, enum error *error,
		  JITSourceLocation *source_location,
		  JITDeoptState *deopt, Var *deopt_stack)
{
    Num *values = allocate(sizeof(Num) * (program->num_values + 1));
    JITBlock *block = program->blocks;
    JITSourceLocation ignored_loc;
    int deopt_map_index = -1;
    JITRunResult fallback_result = JIT_RUN_FALLBACK;

    if (!source_location)
	source_location = &ignored_loc;
    source_location->bytecode_pc = 0;
    source_location->error_pc = 0;
    source_location->source_lineno = 0;

    if (deopt) {
	memset(deopt, 0, sizeof(*deopt));
	deopt->builtin_func = -1;
	deopt->operation = -1;
	if (program && program->num_deopt_maps > 0) {
	    deopt->bytecode_pc = program->deopt_maps[0].bytecode_pc;
	    deopt->error_pc = program->deopt_maps[0].error_pc;
	    deopt->stack_depth = program->deopt_maps[0].stack_depth;
	    deopt->ticks_charged = program->deopt_maps[0].ticks_charged;
	    deopt->builtin_func = program->deopt_maps[0].builtin_func;
	    deopt->operation = program->deopt_maps[0].operation;
	}
    }

    while (block) {
	JITInstruction *instr;
	JITBlock *next = block->next;

	for (instr = block->first; instr; instr = instr->next) {
	    switch (instr->kind) {
	    case HIR_TAC_TICK:
		--*ticks;
		if (instr->op != HIR_OP_CHARGE_TICK && *ticks <= 0) {
		    source_location->bytecode_pc = instr->bytecode_pc;
		    source_location->error_pc = instr->bytecode_pc;
		    source_location->source_lineno = instr->source_lineno;
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_ABORT_TICKS;
		}
		if (instr->op != HIR_OP_CHARGE_TICK && *timed_out) {
		    source_location->bytecode_pc = instr->bytecode_pc;
		    source_location->error_pc = instr->bytecode_pc;
		    source_location->source_lineno = instr->source_lineno;
		    myfree(values, M_PROGRAM);
		    return JIT_RUN_ABORT_SECONDS;
		}
		break;
	    case HIR_TAC_DEOPT:
	    case HIR_TAC_CALL:
	    case HIR_TAC_PUT_PROP:
	    case HIR_TAC_RANGE_REF:
	    case HIR_TAC_RANGE_SET:
		deopt_map_index = instr->deopt_map;
		goto do_fallback;
	    case HIR_TAC_CALL_VERB:
		deopt_map_index = instr->deopt_map;
		fallback_result = JIT_RUN_CALL_VERB;
		goto do_fallback;
	    case HIR_TAC_CONST:
		if (instr->literal_type == TYPE_FLOAT)
		    memcpy(&values[instr->value], &instr->literal, sizeof(Num));
		else
		    values[instr->value] = instr->literal;
		break;
	    case HIR_TAC_LOAD_LOCAL:
		if (env[instr->local_id].type != instr->literal_type) {
		    deopt_map_index = instr->deopt_map;
		    goto do_fallback;
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
		    deopt_map_index = instr->deopt_map;
		    goto do_fallback;
		}
		break;
	    case HIR_TAC_UNARY:
		if (program->value_types && (program->value_types[instr->src1] == TYPE_STR
					     || program->value_types[instr->src1] == TYPE_LIST)) {
		    if (instr->op == HIR_OP_NOT) {
			deopt_map_index = instr->deopt_map;
			goto do_fallback;
		    }
		}
		if (instr->op == HIR_OP_LENGTH && program->value_types
		    && program->value_types[instr->src1] == TYPE_STR)
		    values[instr->value] = memo_strlen_utf((const char *)
			(intptr_t) values[instr->src1]);
		else if (program->value_types
			 && program->value_types[instr->src1] == TYPE_FLOAT) {
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

		    if (program->value_types
			&& (program->value_types[instr->src1] == TYPE_STR
			    || program->value_types[instr->src1] == TYPE_LIST)
			&& (instr->op == HIR_OP_EQ || instr->op == HIR_OP_NE
			    || instr->op == HIR_OP_LT || instr->op == HIR_OP_LE
			    || instr->op == HIR_OP_GT || instr->op == HIR_OP_GE)) {
			deopt_map_index = instr->deopt_map;
			goto do_fallback;
		    }
		    if (program->value_types && program->value_types[instr->src1] == TYPE_FLOAT) {
			FlNum a, b, res;
			memcpy(&a, &values[instr->src1], sizeof(FlNum));
			memcpy(&b, &values[instr->src2], sizeof(FlNum));
			if (instr->op == HIR_OP_ADD) {
			    res = a + b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				source_location->bytecode_pc = instr->bytecode_pc;
				source_location->error_pc = instr->bytecode_pc;
				source_location->source_lineno = instr->source_lineno;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_SUB) {
			    res = a - b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				source_location->bytecode_pc = instr->bytecode_pc;
				source_location->error_pc = instr->bytecode_pc;
				source_location->source_lineno = instr->source_lineno;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_MUL) {
			    res = a * b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				source_location->bytecode_pc = instr->bytecode_pc;
				source_location->error_pc = instr->bytecode_pc;
				source_location->source_lineno = instr->source_lineno;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    memcpy(&values[instr->value], &res, sizeof(FlNum));
			} else if (instr->op == HIR_OP_DIV) {
			    if (b == 0.0) {
				*error = E_DIV;
				source_location->bytecode_pc = instr->bytecode_pc;
				source_location->error_pc = instr->bytecode_pc;
				source_location->source_lineno = instr->source_lineno;
				myfree(values, M_PROGRAM);
				return JIT_RUN_ERROR;
			    }
			    res = a / b;
			    if (!IS_REAL(res)) {
				*error = E_FLOAT;
				source_location->bytecode_pc = instr->bytecode_pc;
				source_location->error_pc = instr->bytecode_pc;
				source_location->source_lineno = instr->source_lineno;
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
			    deopt_map_index = instr->deopt_map;
			    goto do_fallback;
			}
			if (index < 1 || index > list_ptr[0].v.num) {
			    *error = E_RANGE;
			    source_location->bytecode_pc = instr->bytecode_pc;
			    source_location->error_pc = instr->bytecode_pc;
			    source_location->source_lineno = instr->source_lineno;
			    myfree(values, M_PROGRAM);
			    return JIT_RUN_ERROR;
			}
			if (list_ptr[index].type != expected_type) {
			    deopt_map_index = instr->deopt_map;
			    goto do_fallback;
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
			    source_location->bytecode_pc = instr->bytecode_pc;
			    source_location->error_pc = instr->bytecode_pc;
			    source_location->source_lineno = instr->source_lineno;
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
			deopt_map_index = instr->deopt_map;
			goto do_fallback;
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
		if (program->value_types && (program->value_types[instr->src1] == TYPE_STR
					     || program->value_types[instr->src1] == TYPE_LIST)) {
		    deopt_map_index = instr->deopt_map;
		    goto do_fallback;
		}
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

do_fallback:
    if (deopt_map_index >= 0 && deopt_map_index < program->num_deopt_maps) {
	JITDeoptMap *map = &program->deopt_maps[deopt_map_index];
	int i;
	for (i = 0; env && i < map->num_locals; i++) {
	    if (map->local_values[i] > 0) {
		var_type type = map->local_types ? map->local_types[i] : TYPE_INT;
		Var val = materialize_deopt_value(type, values[map->local_values[i]]);
		free_var(env[i]);
		env[i] = val;
	    }
	}
	for (i = 0; deopt_stack && i < (int) map->stack_depth; i++) {
	    var_type type = map->stack_types ? map->stack_types[i] : TYPE_INT;
	    deopt_stack[i] = materialize_deopt_value(type, values[map->stack_values[i]]);
	}
	if (deopt) {
	    deopt->bytecode_pc = map->bytecode_pc;
	    deopt->error_pc = map->error_pc;
	    deopt->stack_depth = map->stack_depth;
	    deopt->ticks_charged = map->ticks_charged;
	    deopt->builtin_func = map->builtin_func;
	    deopt->operation = map->operation;
	}
    }
    myfree(values, M_PROGRAM);
    return fallback_result;
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
    JITSourceLocation native_loc, ref_loc;
    JITDeoptState native_deopt, ref_deopt;
    Var *native_deopt_stack;
    Var *ref_deopt_stack;
    Var *native_env_copy = 0;
    Var *ref_env_copy = 0;
    unsigned stack_capacity = 1;
    int num_vars = program->num_vars;
    int i;
    JITRunResult native_status;
    JITRunResult reference_status;

    memset(&native_loc, 0, sizeof(native_loc));
    memset(&ref_loc, 0, sizeof(ref_loc));
    memset(&native_deopt, 0, sizeof(native_deopt));
    memset(&ref_deopt, 0, sizeof(ref_deopt));
    for (i = 0; i < program->num_deopt_maps; i++)
	if (program->deopt_maps[i].stack_depth > stack_capacity)
	    stack_capacity = program->deopt_maps[i].stack_depth;
    native_deopt_stack = allocate(sizeof(Var) * stack_capacity);
    ref_deopt_stack = allocate(sizeof(Var) * stack_capacity);

    if (num_vars > 0 && env) {
	native_env_copy = allocate(sizeof(Var) * num_vars);
	ref_env_copy = allocate(sizeof(Var) * num_vars);
	for (i = 0; i < num_vars; i++) {
	    native_env_copy[i] = var_ref(env[i]);
	    ref_env_copy[i] = var_ref(env[i]);
	}
    }

    native_status = jit_program_execute(program, native_env_copy ? native_env_copy : env,
					&native_result, &native_ticks, &timed_out,
					&native_error, &native_loc, &native_deopt,
					native_deopt_stack);
    reference_status = reference_execute(program, ref_env_copy ? ref_env_copy : env,
					 &reference_result, &reference_ticks, &timed_out,
					 &reference_error, &ref_loc, &ref_deopt,
					 ref_deopt_stack);

    check(native_status == reference_status, message);
    check(native_ticks == reference_ticks, message);
    if (native_status == JIT_RUN_ERROR) {
	check(native_error == reference_error, message);
	check(native_loc.bytecode_pc == ref_loc.bytecode_pc, message);
	check(native_loc.error_pc == ref_loc.error_pc, message);
	check(native_loc.source_lineno == ref_loc.source_lineno, message);
    } else if (native_status == JIT_RUN_ABORT_TICKS || native_status == JIT_RUN_ABORT_SECONDS) {
	check(native_loc.bytecode_pc == ref_loc.bytecode_pc, message);
	check(native_loc.error_pc == ref_loc.error_pc, message);
	check(native_loc.source_lineno == ref_loc.source_lineno, message);
    } else if (native_status == JIT_RUN_FALLBACK) {
	check(native_deopt.bytecode_pc == ref_deopt.bytecode_pc, message);
	check(native_deopt.error_pc == ref_deopt.error_pc, message);
	check(native_deopt.stack_depth == ref_deopt.stack_depth, message);
	check(native_deopt.ticks_charged == ref_deopt.ticks_charged, message);
	check(native_deopt.builtin_func == ref_deopt.builtin_func, message);
	for (i = 0; i < (int) native_deopt.stack_depth; i++) {
	    check(native_deopt_stack[i].type == ref_deopt_stack[i].type, message);
	    if (native_deopt_stack[i].type == TYPE_INT)
		check(native_deopt_stack[i].v.num == ref_deopt_stack[i].v.num, message);
	    else if (native_deopt_stack[i].type == TYPE_OBJ)
		check(native_deopt_stack[i].v.obj == ref_deopt_stack[i].v.obj, message);
	    else if (native_deopt_stack[i].type == TYPE_STR)
		check(!strcmp(native_deopt_stack[i].v.str, ref_deopt_stack[i].v.str), message);
	    else if (native_deopt_stack[i].type == TYPE_FLOAT)
		check(fl_unbox(native_deopt_stack[i].v.fnum) == fl_unbox(ref_deopt_stack[i].v.fnum), message);
	}
	if (native_env_copy && ref_env_copy) {
	    for (i = 0; i < num_vars; i++) {
		check(native_env_copy[i].type == ref_env_copy[i].type, message);
		if (native_env_copy[i].type == TYPE_INT)
		    check(native_env_copy[i].v.num == ref_env_copy[i].v.num, message);
		else if (native_env_copy[i].type == TYPE_OBJ)
		    check(native_env_copy[i].v.obj == ref_env_copy[i].v.obj, message);
	    }
	}
    } else if (native_status == JIT_RUN_RETURNED) {
	check(native_result.type == reference_result.type, message);
	if (native_result.type == TYPE_FLOAT)
	    check(fl_unbox(native_result.v.fnum) == fl_unbox(reference_result.v.fnum), message);
	else if (native_result.type == TYPE_STR)
	    check(!strcmp(native_result.v.str, reference_result.v.str), message);
	else if (native_result.type == TYPE_OBJ)
	    check(native_result.v.obj == reference_result.v.obj, message);
	else if (native_result.type == TYPE_LIST)
	    check(native_result.v.list == reference_result.v.list, message);
	else
	    check(native_result.v.num == reference_result.v.num, message);
    }

    if (native_status == JIT_RUN_RETURNED)
	free_var(native_result);
    if (reference_status == JIT_RUN_RETURNED)
	free_var(reference_result);
    for (i = 0; i < (int) stack_capacity; i++) {
	free_var(native_deopt_stack[i]);
	free_var(ref_deopt_stack[i]);
    }
    myfree(native_deopt_stack, M_PROGRAM);
    myfree(ref_deopt_stack, M_PROGRAM);
    if (native_env_copy) {
	for (i = 0; i < num_vars; i++) {
	    free_var(native_env_copy[i]);
	    free_var(ref_env_copy[i]);
	}
	myfree(native_env_copy, M_PROGRAM);
	myfree(ref_env_copy, M_PROGRAM);
    }
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
    struct mir_dump mir_dump = {0, 0};
    struct machine_dump machine_dump = {0, 0};
    JITDeoptState deopt;
    JITSourceLocation source_location;

    check(jit_program_dump_mir(program, check_mir_line, &mir_dump),
	  "MIR dump failed");
    check(mir_dump.lines > 0, "MIR dump was empty");
    check(mir_dump.found_source_marker,
	  "MIR dump did not contain PC and line information");
    mir_dump.lines = 0;
    check(jit_program_dump_hir(program, check_mir_line, &mir_dump),
	  "HIR dump failed");
    check(mir_dump.lines > 0, "HIR dump was empty");
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
    env[0].v.str = str_dup("not an integer");
    ticks = 10;
    check(jit_program_execute(local_arith, env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "local arithmetic guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "local arithmetic guard fallback had wrong state");
    check_differential(local_arith, env, 10, 0,
		       "local arithmetic fallback differed from reference execution");
    free_var(env[0]);

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
    deep_env[0].v.str = str_dup("not an integer");
    ticks = 10;
    check(jit_program_execute(two_locals, deep_env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "two locals first guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "two locals first guard fallback had wrong state");
    check_differential(two_locals, deep_env, 10, 0,
		       "two locals first guard fallback differed from reference");
    free_var(deep_env[0]);

    deep_env[0].type = TYPE_INT;
    deep_env[0].v.num = 6;
    deep_env[1].type = TYPE_STR;
    deep_env[1].v.str = str_dup("not an integer");
    ticks = 10;
    check(jit_program_execute(two_locals, deep_env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "two locals second guard did not fallback");
    check(ticks == 10 && deopt.bytecode_pc == 0,
	  "two locals second guard fallback had wrong state");
    check_differential(two_locals, deep_env, 10, 0,
		       "two locals second guard fallback differed from reference");
    free_var(deep_env[1]);

    env[0].type = TYPE_STR;
    env[0].v.str = str_dup("not an integer");
    ticks = 10;
    check(jit_program_execute(guard, env, &result, &ticks, &timed_out,
			      &error, 0, &deopt, 0)
	  == JIT_RUN_FALLBACK, "type guard did not request fallback");
    check(ticks == 10, "entry guard fallback consumed ticks");
    check(deopt.bytecode_pc == 0 && deopt.error_pc == 0
	  && deopt.stack_depth == 0, "entry guard returned the wrong deopt map");
    check(deopt.reason == JIT_DEOPT_TYPE_GUARD,
	  "entry guard returned the wrong deopt reason");
    check_differential(guard, env, 10, 0,
		       "guard fallback differed from reference execution");
    free_var(env[0]);

    deep_env[0].type = TYPE_INT;
    deep_env[0].v.num = 7;
    deep_env[1].type = TYPE_STR;
    deep_env[1].v.str = str_dup("not an integer");
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
    check_differential(deep_guard, deep_env, 10, 0,
		       "deep guard fallback differed from reference execution");
    free_var(deep_env[1]);

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
    free_var(list_elems[1]);
    list_elems[1].type = TYPE_INT;
    list_elems[1].v.num = 42;
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
    env[0].type = TYPE_INT;
    env[0].v.num = 0;

    /* Generic built-in VM call boundary test */
    {
	JITProgram *call_prog = call_boundary_program();
	deopt_stack[0].type = TYPE_INT;
	deopt_stack[0].v.num = 0;
	ticks = 10;
	check(jit_program_execute(call_prog, env, &result, &ticks, &timed_out,
				  &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_CALL_VERB, "call boundary did not request a VM call");
	check(deopt.bytecode_pc == 25, "call boundary wrong bytecode_pc");
	check(deopt.stack_depth == 1, "call boundary wrong stack depth");
	check(deopt_stack[0].v.num == 99, "call boundary wrong stack value");
	jit_program_free(call_prog);
    }

    /* pass() VM call and native continuation tests */
    {
	JITProgram *pass_prog = builtin_call_program(9);
	ResumeKey pass_key = { 0, 2 };
	Var pass_env[1];
	Var *pass_args = new_list(0).v.list;

	pass_env[0].type = TYPE_LIST;
	pass_env[0].v.list = pass_args;
	ticks = 10;
	check(jit_program_resume_map(pass_prog, pass_key) == 1,
	      "pass continuation key did not resolve");
	check(jit_program_execute(pass_prog, pass_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_CALL_VERB, "pass did not request a VM call");
	check(ticks == 10 && deopt.ticks_charged == 0,
	      "pass reported the wrong charged tick count");
	check(deopt.stack_depth == 1 && deopt_stack[0].type == TYPE_LIST,
	      "pass did not materialize its argument list");
	free_var(deopt_stack[0]);
	deopt_stack[0].type = TYPE_STR;
	deopt_stack[0].v.str = str_dup("passed");
	check((jit_program_execute)(pass_prog, pass_env, &result, &ticks,
				    &timed_out, &error, 0, &deopt,
				    deopt_stack, 2, 1) == JIT_RUN_RETURNED,
	      "pass continuation did not return");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "passed"),
	      "pass continuation returned the wrong value");
	free_var(result);
	free_var(deopt_stack[0]);
	free_var(pass_env[0]);
	jit_program_free(pass_prog);

	pass_prog = builtin_call_program(9);
	pass_prog->deopt_maps[1].native_resume_valid = 0;
	pass_args = new_list(0).v.list;
	pass_env[0].type = TYPE_LIST;
	pass_env[0].v.list = pass_args;
	check(jit_program_resume_map(pass_prog, pass_key) == -1,
	      "unsafe pass continuation key resolved");
	check(jit_program_execute(pass_prog, pass_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_CALL_VERB,
	      "pass without a native continuation did not request a VM call");
	free_var(deopt_stack[0]);
	free_var(pass_env[0]);
	jit_program_free(pass_prog);

	/* The same continuation machinery applies to ordinary built-ins. */
	pass_prog = builtin_call_program(17);
	pass_args = new_list(0).v.list;
	pass_env[0].type = TYPE_LIST;
	pass_env[0].v.list = pass_args;
	check(jit_program_resume_map(pass_prog, pass_key) == 1,
	      "generic built-in continuation key did not resolve");
	check(jit_program_execute(pass_prog, pass_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_CALL_VERB,
	      "generic built-in did not request a VM call");
	free_var(deopt_stack[0]);
	deopt_stack[0].type = TYPE_INT;
	deopt_stack[0].v.num = 41;
	check((jit_program_execute)(pass_prog, pass_env, &result, &ticks,
				    &timed_out, &error, 0, &deopt,
				    deopt_stack, 2, 1) == JIT_RUN_RETURNED,
	      "generic built-in continuation did not return");
	check(result.type == TYPE_INT && result.v.num == 41,
	      "generic built-in continuation returned the wrong value");
	free_var(deopt_stack[0]);
	free_var(pass_env[0]);
	jit_program_free(pass_prog);
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
	ResumeKey call_key = { 0, 1 };
	ResumeKey wrong_key = { 0, 2 };
	check(jit_program_resume_map(call_prog, call_key) == 1,
	      "verb call resume key did not resolve");
	check(jit_program_resume_map(call_prog, wrong_key) == -1,
	      "unknown verb call resume key resolved");
	{
	    JITProgram *non_tail = call_verb_program();
	    JITInstruction *call = non_tail->blocks->first;
	    JITInstruction *extra = instruction(HIR_TAC_CONST);

	    while (call->kind != HIR_TAC_CALL_VERB)
		call = call->next;
	    extra->value = 1;
	    extra->literal_type = TYPE_OBJ;
	    extra->next = call->next;
	    call->next = extra;
	    non_tail->deopt_maps[1].native_resume_valid = 0;
	    check(jit_program_resume_map(non_tail, call_key) == -1,
		  "non-tail verb call exposed an unsafe continuation");
	    jit_program_free(non_tail);
	}
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
	      == JIT_RUN_CALL_VERB, "call_verb did not request a VM call");
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
	deopt_stack[0].type = TYPE_STR;
	deopt_stack[0].v.str = str_dup("returned");
	check((jit_program_execute)(call_prog, deep_env, &result, &ticks,
				    &timed_out, &error, 0, &deopt,
				    deopt_stack, 2, 1) == JIT_RUN_RETURNED,
	      "call_verb continuation did not return");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "returned"),
	      "call_verb continuation returned the wrong value");
	free_var(result);
	free_var(deopt_stack[0]);
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

	JITProgram *ticks_left_p = unary_program(0, HIR_OP_TICKS_LEFT);
	ticks = 37;
	check(jit_program_execute(ticks_left_p, env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "ticks_left execution failed");
	check(result.type == TYPE_INT && result.v.num == 37,
	      "ticks_left returned wrong value");
	jit_program_free(ticks_left_p);

	JITProgram *seconds_left_p = unary_program(0, HIR_OP_SECONDS_LEFT);
	ticks = 10;
	check(jit_program_execute(seconds_left_p, env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "seconds_left execution failed");
	check(result.type == TYPE_INT && result.v.num == 5,
	      "seconds_left returned wrong value");
	jit_program_free(seconds_left_p);

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

	/* String truth and comparison semantics. */
	JITProgram *str_not = string_not_program("");
	ticks = 10;
	check(jit_program_execute(str_not, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "empty string not returned");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "empty string not evaluated to 1");
	jit_program_free(str_not);

	JITProgram *str_eq = string_compare_program("same", "SAME", HIR_OP_EQ);
	ticks = 10;
	check(jit_program_execute(str_eq, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string equality execution returned");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "string equality case-insensitive match");
	jit_program_free(str_eq);

	JITProgram *str_branch = string_branch_program();
	Var branch_env[1];
	branch_env[0].type = TYPE_STR;
	branch_env[0].v.str = str_dup("");
	ticks = 10;
	check(jit_program_execute(str_branch, branch_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "empty string branch executed natively");
	check(result.type == TYPE_INT && result.v.num == 20,
	      "empty string branch selected false arm");
	free_var(branch_env[0]);
	jit_program_free(str_branch);

	JITProgram *str_length = string_length_program("h\xc3\xa9llo");
	ticks = 10;
	check(jit_program_execute(str_length, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string length execution failed");
	check(result.type == TYPE_INT
	      && result.v.num == (Num) memo_strlen_utf("h\xc3\xa9llo"),
	      "string length returned wrong configured character length");
	check_differential(str_length, 0, 10, 0, "string length differential");

	/* Protection changes regenerate code and bridge the builtin through the VM. */
	hir_test_set_length_protected(1);
	{
	    JITDeoptState protected_deopt;
	    Var protected_stack[1];

	    ticks = 10;
	    check(jit_program_execute(str_length, 0, &result, &ticks,
				      &timed_out, &error, 0, &protected_deopt,
				      protected_stack)
		  == JIT_RUN_CALL_VERB, "protected length did not enter VM");
	    check(protected_deopt.stack_depth == 1
		  && protected_stack[0].type == TYPE_LIST
		  && protected_stack[0].v.list[0].v.num == 1
		  && protected_stack[0].v.list[1].type == TYPE_STR,
		  "protected length did not materialize its arguments");
	    free_var(protected_stack[0]);
	}
	hir_test_set_length_protected(0);
	ticks = 10;
	check(jit_program_execute(str_length, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "unprotected length did not return to native");
	check(result.type == TYPE_INT
	      && result.v.num == (Num) memo_strlen_utf("h\xc3\xa9llo"),
	      "recompiled length returned the wrong value");
	jit_program_free(str_length);

	JITProgram *str_cat = string_concat_program("Hello, ", "world!");
	ticks = 10;
	check(jit_program_execute(str_cat, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string concat execution returned");
	check(result.type == TYPE_STR && strcmp(result.v.str, "Hello, world!") == 0,
	      "string concat returned expected string");
	free_var(result);
	jit_program_free(str_cat);

	JITProgram *str_idx = string_index_program("LambdaMOO", 7);
	ticks = 10;
	check(jit_program_execute(str_idx, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string index execution returned");
	check(result.type == TYPE_STR && strcmp(result.v.str, "M") == 0,
	      "string index returned expected character");
	free_var(result);
	jit_program_free(str_idx);

	JITProgram *str_lt = string_compare_program("abc", "def", HIR_OP_LT);
	ticks = 10;
	check(jit_program_execute(str_lt, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "string less-than execution returned");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "string less-than match");
	jit_program_free(str_lt);

	JITProgram *str_find = string_compare_program("h\xc3\xa9llo MOO", "moo",
						     HIR_OP_INDEX_BF);
	ticks = 10;
	check(jit_program_execute(str_find, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "index built-in execution returned");
	check(result.type == TYPE_INT && result.v.num == 7,
	      "index built-in returned Unicode character position");
	jit_program_free(str_find);

	JITProgram *str_rfind = string_compare_program("MOO and moo", "moo",
						      HIR_OP_RINDEX_BF);
	ticks = 10;
	check(jit_program_execute(str_rfind, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "rindex built-in execution returned");
	check(result.type == TYPE_INT && result.v.num == 9,
	      "rindex built-in returned last case-insensitive match");
	jit_program_free(str_rfind);

	JITProgram *str_missing = string_compare_program("LambdaMOO", "xyz",
							HIR_OP_INDEX_BF);
	ticks = 10;
	check(jit_program_execute(str_missing, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "missing index built-in execution returned");
	check(result.type == TYPE_INT && result.v.num == 0,
	      "missing index built-in returned zero");
	jit_program_free(str_missing);
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

    /* Dynamically tagged list elements survive SSA copies and deoptimization. */
    {
	JITProgram *tagged = list_index_tagged_deopt_program();
	Var tagged_env[1];
	Var tagged_stack[1];

	tagged_env[0] = new_list(1);
	tagged_env[0].v.list[1].type = TYPE_STR;
	tagged_env[0].v.list[1].v.str = str_dup("tagged element");
	memset(tagged_stack, 0, sizeof(tagged_stack));
	ticks = 10;
	check(jit_program_execute(tagged, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt,
				  tagged_stack) == JIT_RUN_FALLBACK,
	      "tagged list index did not reach deopt boundary");
	check(tagged_stack[0].type == TYPE_STR
	      && !strcmp(tagged_stack[0].v.str, "tagged element"),
	      "tagged list index reconstructed the wrong value");
	free_var(tagged_stack[0]);
	free_var(tagged_env[0]);
	jit_program_free(tagged);
    }

    /* A native return must use a tagged value's runtime type. */
    {
	JITProgram *tagged = list_index_tagged_return_program();
	Var env[1];

	env[0] = new_list(1);
	env[0].v.list[1].type = TYPE_STR;
	env[0].v.list[1].v.str = str_dup("tagged return");
	ticks = 10;
	check(jit_program_execute(tagged, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0) == JIT_RUN_RETURNED,
	      "tagged return executed natively");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "tagged return"),
	      "tagged return preserved its runtime type");
	free_var(result);
	free_var(env[0]);
	jit_program_free(tagged);
    }

    /* Tagged list bases and indexes are guarded before native indexing. */
    {
	JITProgram *tagged = list_index_tagged_base_program();
	Var tagged_env[1];
	Var tagged_stack[1];
	Var inner = new_list(1);

	inner.v.list[1].type = TYPE_STR;
	inner.v.list[1].v.str = str_dup("nested tagged element");
	tagged_env[0] = new_list(2);
	tagged_env[0].v.list[1] = inner;
	tagged_env[0].v.list[2].type = TYPE_INT;
	tagged_env[0].v.list[2].v.num = 1;
	memset(tagged_stack, 0, sizeof(tagged_stack));
	ticks = 10;
	check(jit_program_execute(tagged, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt,
				  tagged_stack) == JIT_RUN_FALLBACK,
	      "tagged base indexing did not reach deopt boundary");
	check(tagged_stack[0].type == TYPE_STR
	      && !strcmp(tagged_stack[0].v.str, "nested tagged element"),
	      "tagged base indexing reconstructed the wrong value");
	free_var(tagged_stack[0]);
	tagged_env[0].v.list[2].type = TYPE_STR;
	tagged_env[0].v.list[2].v.str = str_dup("not an index");
	ticks = 10;
	check(jit_program_execute(tagged, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, 0)
	      == JIT_RUN_FALLBACK,
	      "tagged non-integer index did not fallback");
	free_var(tagged_env[0].v.list[2]);
	tagged_env[0].v.list[2].type = TYPE_INT;
	tagged_env[0].v.list[2].v.num = 1;
	free_var(tagged_env[0].v.list[1]);
	tagged_env[0].v.list[1].type = TYPE_INT;
	tagged_env[0].v.list[1].v.num = 7;
	ticks = 10;
	check(jit_program_execute(tagged, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, 0)
	      == JIT_RUN_FALLBACK,
	      "tagged non-list base did not fallback");
	free_var(tagged_env[0]);
	jit_program_free(tagged);
    }

    /* Equality and membership consume dynamically tagged values natively. */
    {
	JITProgram *tagged_eq = list_index_tagged_consumer_program(HIR_OP_EQ);
	JITProgram *tagged_in = list_index_tagged_consumer_program(HIR_OP_IN);
	Var tagged_env[2];

	tagged_env[0] = new_list(1);
	tagged_env[0].v.list[1].type = TYPE_STR;
	tagged_env[0].v.list[1].v.str = str_dup("tagged element");
	tagged_env[1] = new_list(1);
	tagged_env[1].v.list[1].type = TYPE_STR;
	tagged_env[1].v.list[1].v.str = str_dup("tagged element");
	ticks = 10;
	check(jit_program_execute(tagged_eq, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED && result.type == TYPE_INT
	      && result.v.num == 1,
	      "tagged equality returned the wrong value");
	ticks = 10;
	check(jit_program_execute(tagged_in, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED && result.type == TYPE_INT
	      && result.v.num == 1,
	      "tagged membership returned the wrong value");
	free_var(tagged_env[0]);
	free_var(tagged_env[1]);
	jit_program_free(tagged_eq);
	jit_program_free(tagged_in);
    }

    /* Type inspection reads a dynamic value's runtime tag without deoptimizing. */
    {
	JITProgram *tagged_typeof = tagged_unary_program(HIR_OP_TYPEOF);
	Var tagged_env[1];

	tagged_env[0].type = TYPE_STR;
	tagged_env[0].v.str = str_dup("dynamic type");
	ticks = 10;
	check(jit_program_execute(tagged_typeof, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "tagged typeof executed natively");
	check(result.type == TYPE_INT && result.v.num == TYPE_STR,
	      "tagged typeof returned the runtime type");
	free_var(tagged_env[0]);
	jit_program_free(tagged_typeof);
    }

    /* Tagged exponentiation accepts integers and guards other runtime types. */
    {
	JITProgram *tagged_exp = tagged_binary_program(HIR_OP_EXP);
	Var tagged_env[2];

	tagged_env[0].type = TYPE_INT;
	tagged_env[0].v.num = 3;
	tagged_env[1].type = TYPE_INT;
	tagged_env[1].v.num = 4;
	ticks = 10;
	check(jit_program_execute(tagged_exp, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "tagged exponentiation executed natively");
	check(result.type == TYPE_INT && result.v.num == 81,
	      "tagged exponentiation returned the wrong value");

	tagged_env[1].type = TYPE_STR;
	tagged_env[1].v.str = str_dup("not an exponent");
	ticks = 10;
	check(jit_program_execute(tagged_exp, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK,
	      "tagged non-integer exponent did not deoptimize");
	free_var(tagged_env[1]);
	jit_program_free(tagged_exp);
    }

    /* Tagged strings retain their type through concatenation and index(). */
    {
	JITProgram *pipeline = tagged_string_pipeline_program();
	Var env[1];

	env[0] = new_list(2);
	env[0].v.list[1].type = TYPE_STR;
	env[0].v.list[1].v.str = str_dup("hello world");
	env[0].v.list[2].type = TYPE_STR;
	env[0].v.list[2].v.str = str_dup(" ");
	ticks = 10;
	check(jit_program_execute(pipeline, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0) == JIT_RUN_RETURNED,
	      "tagged string pipeline executed natively");
	check(result.type == TYPE_INT && result.v.num == 6,
	      "tagged string pipeline returned the delimiter position");
	free_var(env[0]);
	jit_program_free(pipeline);
    }

    /* Sublist from runtime helper tests */
    {
	Var base = new_list(3);
	base.v.list[1].type = TYPE_INT;
	base.v.list[1].v.num = 10;
	base.v.list[2].type = TYPE_INT;
	base.v.list[2].v.num = 20;
	base.v.list[3].type = TYPE_INT;
	base.v.list[3].v.num = 30;

	Var *sub2 = jit_rt_sublist_from(base.v.list, 2);
	check(sub2 != 0 && sub2[0].v.num == 2 && sub2[1].v.num == 20 && sub2[2].v.num == 30,
	      "jit_rt_sublist_from start 2 failed");
	Var v_sub2;
	v_sub2.type = TYPE_LIST;
	v_sub2.v.list = sub2;
	free_var(v_sub2);

	Var *sub4 = jit_rt_sublist_from(base.v.list, 4);
	check(sub4 != 0 && sub4[0].v.num == 0,
	      "jit_rt_sublist_from start 4 failed");
	Var v_sub4;
	v_sub4.type = TYPE_LIST;
	v_sub4.v.list = sub4;
	free_var(v_sub4);

	free_var(base);
    }

    /* Exception and finally stack marker deoptimization tests */
    {
	JITProgram *boundary = exception_boundary_deopt_program();
	JITDeoptState boundary_state;
	ticks = 10;
	check(jit_program_execute(boundary, 0, &result, &ticks, &timed_out,
				  &error, 0, &boundary_state, 0)
	      == JIT_RUN_FALLBACK, "exception boundary did not deopt");
	check(boundary_state.bytecode_pc == 19,
	      "exception boundary resumed at wrong pc");
	check(boundary_state.stack_depth == 0,
	      "exception boundary preserved setup stack");
	check(boundary_state.ticks_charged == 0,
	      "exception boundary charged a tick");
	jit_program_free(boundary);

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

	/* Nested try-except inside try-finally deoptimization test */
	JITProgram *nested_deopt = nested_try_except_finally_deopt_program();
	memset(deopt_stack, 0, sizeof(deopt_stack));
	ticks = 10;
	check(jit_program_execute(nested_deopt, 0, &result, &ticks, &timed_out,
				  &error, 0, &deopt_state, deopt_stack)
	      == JIT_RUN_FALLBACK, "nested catch/finally marker deopt failed");
	check(deopt_state.stack_depth == 4, "nested marker deopt depth wrong");
	check(deopt_stack[0].type == TYPE_FINALLY && deopt_stack[0].v.num == 99,
	      "nested finally marker wrong");
	check(deopt_stack[1].type == TYPE_INT && deopt_stack[1].v.num == 0,
	      "nested catch marker codes wrong");
	check(deopt_stack[2].type == TYPE_INT && deopt_stack[2].v.num == 55,
	      "nested catch marker handler pc wrong");
	check(deopt_stack[3].type == TYPE_CATCH && deopt_stack[3].v.num == 1,
	      "nested catch marker type/arm wrong");
	free_var(deopt_stack[0]);
	free_var(deopt_stack[1]);
	free_var(deopt_stack[2]);
	free_var(deopt_stack[3]);
	jit_program_free(nested_deopt);

	/* Fork boundary deoptimization tests */
	JITProgram *fork_deopt = fork_boundary_deopt_program();
	memset(deopt_stack, 0, sizeof(deopt_stack));
	ticks = 10;
	check(jit_program_execute(fork_deopt, 0, &result, &ticks, &timed_out,
				  &error, 0, &deopt_state, deopt_stack)
	      == JIT_RUN_FALLBACK, "fork boundary deopt failed");
	check(deopt_state.bytecode_pc == 33,
	      "fork boundary resumed at wrong pc");
	check(deopt_state.stack_depth == 1,
	      "fork boundary stack depth wrong");
	check(deopt_stack[0].type == TYPE_INT && deopt_stack[0].v.num == 5,
	      "fork boundary time value on stack wrong");
	free_var(deopt_stack[0]);
	jit_program_free(fork_deopt);

	/* Native string and list range reference tests */
	{
	    Var str_input;
	    str_input.type = TYPE_STR;
	    str_input.v.str = str_dup("abcdef");
	    JITProgram *str_range_p = range_ref_test_program(TYPE_STR);
	    ticks = 10;
	    check(jit_program_execute(str_range_p, &str_input, &result, &ticks,
				      &timed_out, &error, 0, &deopt_state, 0)
		  == JIT_RUN_RETURNED, "string range ref did not return");
	    check(result.type == TYPE_STR && !strcmp(result.v.str, "bcd"),
		  "string range ref returned wrong substring");
	    free_var(result);
	    free_var(str_input);
	    jit_program_free(str_range_p);

	    Var list_input = new_list(5);
	    list_input.v.list[1] = (Var){ .type = TYPE_INT, .v.num = 10 };
	    list_input.v.list[2] = (Var){ .type = TYPE_INT, .v.num = 20 };
	    list_input.v.list[3] = (Var){ .type = TYPE_INT, .v.num = 30 };
	    list_input.v.list[4] = (Var){ .type = TYPE_INT, .v.num = 40 };
	    list_input.v.list[5] = (Var){ .type = TYPE_INT, .v.num = 50 };
	    JITProgram *list_range_p = range_ref_test_program(TYPE_LIST);
	    ticks = 10;
	    check(jit_program_execute(list_range_p, &list_input, &result, &ticks,
				      &timed_out, &error, 0, &deopt_state, 0)
		  == JIT_RUN_RETURNED, "list range ref did not return");
	    check(result.type == TYPE_LIST && result.v.list[0].v.num == 3
		  && result.v.list[1].v.num == 20
		  && result.v.list[2].v.num == 30
		  && result.v.list[3].v.num == 40,
		  "list range ref returned wrong sublist");
	    free_var(result);
	    free_var(list_input);
	    jit_program_free(list_range_p);
	}
    }

    /* Nested control flow (loop + conditional) differential test */
    {
	JITProgram *loop_p = nested_loop_branch_program();
	ticks = 50;
	check(jit_program_execute(loop_p, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "nested loop execution failed");
	check(result.type == TYPE_INT && result.v.num == 5,
	      "nested loop returned wrong value");
	check(ticks == 39, "nested loop consumed wrong tick count");
	free_var(result);
	check_differential(loop_p, 0, 50, 0, "nested loop differential");
	jit_program_free(loop_p);
    }

    /* Boundary deoptimization differential tests */
    {
	JITProgram *vcall_p = verb_call_boundary_program();
	check_differential(vcall_p, 0, 10, 0, "verb call boundary differential");
	jit_program_free(vcall_p);

	JITProgram *prop_p = prop_boundary_program();
	check_differential(prop_p, 0, 10, 0, "prop boundary differential");
	jit_program_free(prop_p);

	JITProgram *range_p = range_boundary_program();
	check_differential(range_p, 0, 10, 0, "range ref boundary differential");
	jit_program_free(range_p);

	JITProgram *range_set_p = range_set_boundary_program();
	check_differential(range_set_p, 0, 10, 0, "range set boundary differential");
	jit_program_free(range_set_p);
    }

    /* Repeated-execution smoke test: 1,000 native JIT loop executions */
    {
	JITProgram *bench_p = nested_loop_branch_program();
	int iter;
	for (iter = 0; iter < 1000; iter++) {
	    ticks = 50;
	    timed_out = 0;
	    error = E_NONE;
	    JITRunResult res = jit_program_execute(bench_p, 0, &result, &ticks,
						   &timed_out, &error, 0, 0, 0);
	    if (res != JIT_RUN_RETURNED || result.v.num != 5) {
		check(0, "repeated execution iteration failed");
		break;
	    }
	    free_var(result);
	}
	check(jit_program_state(bench_p) == JIT_STATE_COMPILED,
	      "repeated execution lost JIT compiled state");
	jit_program_free(bench_p);
    }

    {
	int size;

	for (size = 0; size <= 2; size += 2) {
	    JITProgram *list_const_p = list_constant_program(size);
	    int iter;

	    check(jit_program_compile(list_const_p) == 1,
		  "list constant JIT compile failed");
	    for (iter = 0; iter < 50; iter++) {
		ticks = 50;
		timed_out = 0;
		error = E_NONE;
		JITRunResult res = jit_program_execute(list_const_p, 0, &result,
						       &ticks, &timed_out, &error,
						       0, 0, 0);
		check(res == JIT_RUN_RETURNED, "list constant return result");
		check(result.type == TYPE_LIST, "list constant result type");
		check(result.v.list[0].v.num == size, "list constant length");
		if (size)
		    check(result.v.list[1].v.num == 10
			  && result.v.list[2].v.num == 20,
			  "list constant elements");
		free_var(result);
	    }
	    jit_program_free(list_const_p);
	}
    }

    {
	JITProgram *in_p = in_program();
	Var env[2];
	Var stack[4];
	JITDeoptState deopt_state;

	env[0].type = TYPE_INT;
	env[0].v.num = 42;
	env[1] = new_list(2);
	env[1].v.list[1].type = TYPE_INT;
	env[1].v.list[1].v.num = 10;
	env[1].v.list[2].type = TYPE_INT;
	env[1].v.list[2].v.num = 42;

	check(jit_program_compile(in_p) == 1, "in JIT compile failed");
	check(jit_program_may_error(in_p) == 0,
	      "deoptimized in operation should not mark program may-error");
	ticks = 50;
	timed_out = 0;
	error = E_NONE;
	memset(&deopt_state, 0, sizeof(deopt_state));
	JITRunResult res = jit_program_execute(in_p, env, &result,
					       &ticks, &timed_out, &error,
					       0, &deopt_state, stack);
	check(res == JIT_RUN_RETURNED, "in native execution result");
	check(result.type == TYPE_INT && result.v.num == 2,
	      "in native execution index value");
	free_var(env[1]);
	jit_program_free(in_p);
    }

    {
	/* Regression test: empty JIT program compilation and fallback */
	JITProgram *empty_prog = new_jit_program();
	check(jit_program_compile(empty_prog) == 1, "empty JIT program compile succeeds");
	ticks = 50;
	timed_out = 0;
	error = E_NONE;
	JITRunResult res = jit_program_execute(empty_prog, 0, &result,
					       &ticks, &timed_out, &error,
					       0, 0, 0);
	check(res == JIT_RUN_FALLBACK, "empty JIT program execute falls back");
	jit_program_free(empty_prog);
    }

    {
	/* Regression test: deoptimization of indexed string operation must not corrupt local type to TYPE_LIST */
	JITProgram *deopt_prog = new_jit_program();
	JITBlock *block = allocate(sizeof(JITBlock));
	JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
	JITInstruction *deopt_inst = instruction(HIR_TAC_DEOPT);
	JITDeoptMap *map;
	Var env[1];
	Var stack[4];
	JITDeoptState deopt_state;

	deopt_prog->num_values = 2;
	deopt_prog->num_vars = 1;
	deopt_prog->num_blocks = 1;
	deopt_prog->value_types = allocate(sizeof(var_type) * 2);
	deopt_prog->value_types[1] = TYPE_STR;
	add_entry_deopt_map(deopt_prog);
	deopt_prog->deopt_maps = myrealloc(deopt_prog->deopt_maps,
					   sizeof(JITDeoptMap) * 2, M_PROGRAM);
	map = &deopt_prog->deopt_maps[1];
	memset(map, 0, sizeof(JITDeoptMap));
	deopt_prog->num_deopt_maps = 2;
	map->bytecode_pc = map->error_pc = 20;
	map->stack_depth = 0;
	map->ticks_charged = 1;
	map->num_locals = 1;
	map->local_values = allocate(sizeof(int) * 1);
	map->local_values[0] = 1;
	map->local_types = allocate(sizeof(var_type) * 1);
	map->local_types[0] = TYPE_STR;
	map->operation = HIR_OP_INDEX;
	map->reason = JIT_DEOPT_UNSUPPORTED_OP;

	deopt_prog->blocks = deopt_prog->last_block = block;
	block->id = 1;
	load->value = 1;
	load->local_id = 0;
	load->literal_type = TYPE_STR;
	load->deopt_map = 0;
	deopt_inst->kind = HIR_TAC_DEOPT;
	deopt_inst->deopt_map = 1;

	load->next = deopt_inst;
	block->first = load;
	block->last = deopt_inst;

	env[0].type = TYPE_STR;
	env[0].v.str = str_dup("root class");

	check(jit_program_compile(deopt_prog) == 1, "indexed string deopt program compile");
	ticks = 50;
	timed_out = 0;
	error = E_NONE;
	memset(&deopt_state, 0, sizeof(deopt_state));
	JITRunResult res = jit_program_execute(deopt_prog, env, &result,
					       &ticks, &timed_out, &error,
					       0, &deopt_state, stack);
	check(res == JIT_RUN_FALLBACK, "indexed string deopt returns fallback");
	check(deopt_state.operation == HIR_OP_INDEX,
	      "indexed string deopt preserves operation identity");
	check(env[0].type == TYPE_STR, "deoptimized string local retains TYPE_STR");
	check(strcmp(env[0].v.str, "root class") == 0, "deoptimized string local retains value");
	free_var(env[0]);
	jit_program_free(deopt_prog);
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

    /* JIT complex value and property runtime helper unit tests */
    {
	/* 1. is_true helper tests */
	check(jit_rt_is_true(1, TYPE_INT) == 1, "jit_rt_is_true int 1");
	check(jit_rt_is_true(0, TYPE_INT) == 0, "jit_rt_is_true int 0");
	double d_pos = 1.5;
	double d_zero = 0.0;
	int64_t raw_fpos = 0, raw_fzero = 0;
	memcpy(&raw_fpos, &d_pos, sizeof(d_pos));
	memcpy(&raw_fzero, &d_zero, sizeof(d_zero));
	check(jit_rt_is_true(raw_fpos, TYPE_FLOAT) == 1, "jit_rt_is_true float 1.5");
	check(jit_rt_is_true(raw_fzero, TYPE_FLOAT) == 0, "jit_rt_is_true float 0.0");
	check(jit_rt_is_true((intptr_t)"hello", TYPE_STR) == 1, "jit_rt_is_true str non-empty");
	check(jit_rt_is_true((intptr_t)"", TYPE_STR) == 0, "jit_rt_is_true str empty");
	Var l_empty = new_list(0);
	Var l_elem = new_list(1);
	l_elem.v.list[1].type = TYPE_INT;
	l_elem.v.list[1].v.num = 1;
	check(jit_rt_is_true((intptr_t)l_empty.v.list, TYPE_LIST) == 0, "jit_rt_is_true list empty");
	check(jit_rt_is_true((intptr_t)l_elem.v.list, TYPE_LIST) == 1, "jit_rt_is_true list non-empty");
	free_var(l_empty);
	free_var(l_elem);

	/* 2. equality helper tests */
	check(jit_rt_equality((intptr_t)"Foo", TYPE_STR, (intptr_t)"foo", TYPE_STR, 0) == 1,
	      "jit_rt_equality str case-insensitive");
	check(jit_rt_equality((intptr_t)"Foo", TYPE_STR, (intptr_t)"foo", TYPE_STR, 1) == 0,
	      "jit_rt_equality str case-sensitive");
	check(jit_rt_equality((intptr_t)"bar", TYPE_STR, (intptr_t)"bar", TYPE_STR, 1) == 1,
	      "jit_rt_equality str equal");
	check(jit_rt_equality(10, TYPE_INT, 10, TYPE_INT, 0) == 1, "jit_rt_equality int equal");
	check(jit_rt_equality(10, TYPE_INT, 20, TYPE_INT, 0) == 0, "jit_rt_equality int unequal");

	/* 3. string comparison tests */
	check(jit_rt_str_cmp("abc", "abc", 1) == 0, "jit_rt_str_cmp equal");
	check(jit_rt_str_cmp("abc", "ABC", 0) == 0, "jit_rt_str_cmp case-insensitive equal");
	check(jit_rt_str_cmp("abc", "def", 1) < 0, "jit_rt_str_cmp lt");
	check(jit_rt_str_cmp("xyz", "abc", 1) > 0, "jit_rt_str_cmp gt");

	/* 4. string concat and index tests */
	int32_t rt_err = E_NONE;
	const char *concat_res = jit_rt_str_concat("Hello, ", "World!", &rt_err);
	check(rt_err == E_NONE && concat_res && strcmp(concat_res, "Hello, World!") == 0,
	      "jit_rt_str_concat success");
	if (concat_res)
	    free_str(concat_res);

	const char *char_res = jit_rt_str_ref("LambdaMOO", 7, &rt_err);
	check(rt_err == E_NONE && char_res && strcmp(char_res, "M") == 0,
	      "jit_rt_str_ref index 7");
	if (char_res)
	    free_str(char_res);

	char_res = jit_rt_str_ref("LambdaMOO", 0, &rt_err);
	check(rt_err == E_RANGE && char_res == 0, "jit_rt_str_ref index 0 range error");

	char_res = jit_rt_str_ref("LambdaMOO", 100, &rt_err);
	check(rt_err == E_RANGE && char_res == 0, "jit_rt_str_ref index 100 range error");

	/* 5. list concat and append tests */
	Var l1 = new_list(1);
	l1.v.list[1].type = TYPE_INT;
	l1.v.list[1].v.num = 111;
	Var l2 = new_list(1);
	l2.v.list[1].type = TYPE_INT;
	l2.v.list[1].v.num = 222;

	Var *lconcat = jit_rt_list_concat(l1.v.list, l2.v.list, &rt_err);
	check(rt_err == E_NONE && lconcat && lconcat[0].v.num == 2, "jit_rt_list_concat len");
	check(lconcat[1].v.num == 111 && lconcat[2].v.num == 222, "jit_rt_list_concat elements");
	Var lconcat_var;
	lconcat_var.type = TYPE_LIST;
	lconcat_var.v.list = lconcat;
	free_var(lconcat_var);

	Var *lapp = jit_rt_list_append(l1.v.list, 333, TYPE_INT);
	check(lapp && lapp[0].v.num == 2 && lapp[2].v.num == 333, "jit_rt_list_append int");
	Var lapp_var;
	lapp_var.type = TYPE_LIST;
	lapp_var.v.list = lapp;
	free_var(lapp_var);

	/* 6. list_in test */
	check(jit_rt_list_in(111, TYPE_INT, l1.v.list) == 1, "jit_rt_list_in found");
	check(jit_rt_list_in(999, TYPE_INT, l1.v.list) == 0, "jit_rt_list_in not found");

	free_var(l1);
	free_var(l2);

	/* 7. get_prop test */
	int64_t prop_raw = 0;
	int32_t prop_type = 0;
	int ok = jit_rt_get_prop(0, "name", 2, &prop_raw, &prop_type, &rt_err);
	check(ok == 1 && rt_err == E_NONE && prop_type == TYPE_INT && prop_raw == 123,
	      "jit_rt_get_prop valid property read");

	ok = jit_rt_get_prop(-1, "name", 2, &prop_raw, &prop_type, &rt_err);
	check(ok == 0 && rt_err == E_INVIND, "jit_rt_get_prop invalid object");

	/* 8. valid/parent tests */
	check(jit_rt_valid(0) == 1, "jit_rt_valid object #0");
	check(jit_rt_valid(-1) == 0, "jit_rt_valid object #-1");

	int64_t parent_res = jit_rt_parent(1, &rt_err);
	check(parent_res == 0 && rt_err == E_NONE, "jit_rt_parent object #1");
	parent_res = jit_rt_parent(-1, &rt_err);
	check(rt_err == E_INVARG, "jit_rt_parent invalid object");

	/* 9. index/rindex tests */
	check(jit_rt_index("hello world", "world") == 7, "jit_rt_index found");
	check(jit_rt_index("hello world", "xyz") == 0, "jit_rt_index not found");
	check(jit_rt_rindex("foo bar foo", "foo") == 9, "jit_rt_rindex found");

	/* 10. seconds_left / time tests */
	check(jit_rt_seconds_left() == 5, "jit_rt_seconds_left stub");
	check(jit_rt_time() > 0, "jit_rt_time positive");
    }

    /* Deoptimization profiling tests */
    {
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_NONE), "none") == 0,
	      "deopt reason name none");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_BUILTIN_CALL), "builtin_call") == 0,
	      "deopt reason name builtin_call");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_VERB_CALL), "verb_call") == 0,
	      "deopt reason name verb_call");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_PROPERTY_READ), "property_read") == 0,
	      "deopt reason name property_read");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_PROPERTY_WRITE), "property_write") == 0,
	      "deopt reason name property_write");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_RANGE_OP), "range_operation") == 0,
	      "deopt reason name range_operation");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_TYPE_GUARD), "type_guard_failure") == 0,
	      "deopt reason name type_guard_failure");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_BRANCH_TYPE), "branch_type_mismatch") == 0,
	      "deopt reason name branch_type_mismatch");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_CONTROL_FLOW), "control_flow") == 0,
	      "deopt reason name control_flow");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_ARITHMETIC_TYPE), "arithmetic_type") == 0,
	      "deopt reason name arithmetic_type");
	check(strcmp(jit_deopt_reason_name(JIT_DEOPT_UNSUPPORTED_OP), "unsupported_operation") == 0,
	      "deopt reason name unsupported_operation");

	jit_profile_reset();
	jit_profile_record_entry();
	jit_profile_record_entry();
	jit_profile_record_completed();
	jit_profile_record_vm_call();

	JITDeoptState deopt_sample;
	memset(&deopt_sample, 0, sizeof(deopt_sample));
	deopt_sample.bytecode_pc = 42;
	deopt_sample.source_lineno = 10;
	deopt_sample.reason = JIT_DEOPT_BUILTIN_CALL;
	jit_profile_record_deopt(0, "do_command", &deopt_sample);

	deopt_sample.bytecode_pc = 18;
	deopt_sample.source_lineno = 5;
	deopt_sample.operation = HIR_OP_GET_PROP;
	deopt_sample.reason = JIT_DEOPT_PROPERTY_READ;
	jit_profile_record_deopt(1, "eval", &deopt_sample);

	deopt_sample.bytecode_pc = 20;
	deopt_sample.source_lineno = 6;
	deopt_sample.operation = HIR_OP_SCATTER;
	deopt_sample.reason = JIT_DEOPT_UNSUPPORTED_OP;
	jit_profile_record_deopt(69, "parse_parties", &deopt_sample);

	/* Trigger report generation */
	jit_profile_report();

	/* Trigger periodic check */
	jit_profile_maybe_report(100);
	jit_profile_maybe_report(2000);

	jit_profile_reset();
    }

    return failures != 0;
}
