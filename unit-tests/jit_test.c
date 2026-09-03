#include "jit_internal.h"

#include "my-math.h"
#include "my-stdio.h"
#include "my-string.h"

#include "db.h"
#include "execute.h"
#include "integer_arithmetic.h"
#include "list.h"
#include "server.h"
#include "storage.h"
#include "utf.h"
#include "utils.h"

#include <limits.h>

#define jit_program_execute(p, e, r, t, to, err, loc, d, ds) \
    jit_program_execute(p, e, r, t, to, err, loc, d, ds, 2, -1, 0, 0)

static int failures;

static void check(int, const char *);
extern void hir_test_set_length_protected(int);
extern void hir_test_set_builtin_property(enum bi_prop);
extern void hir_test_set_builtin_property_protected(enum bi_prop, int);
extern void hir_test_set_property(Var);
extern void hir_test_set_property_allowed(int);
extern void hir_test_set_resume_point(const ResumePoint *);
extern void hir_test_reset_property(void);
extern void jit_test_set_compiled_program(JITProgram *);
#ifdef WAIF_CORE
extern Var hir_test_new_waif(void);
#endif

struct machine_dump {
    int lines;
    int valid_first_line;
};

struct mir_dump {
    int lines;
    int found_source_marker;
    int timeout_checks;
    int source_location_stores;
    int source_location_field_stores;
};

struct promotion_dump {
    JITNativeFrame *frames[4];
    int maps[4];
    unsigned count;
};

static void
record_promotion(JITNativeFrame *frame, JITCallerResume *resume, void *data)
{
    struct promotion_dump *dump = data;

    dump->frames[dump->count] = frame;
    dump->maps[dump->count] = resume ? resume->map_id : frame->current_map;
    dump->count++;
}

static void
check_mir_line(const char *line, void *data)
{
    struct mir_dump *dump = data;

    dump->lines++;
    if (strstr(line, "pc_11_line_7_"))
	dump->found_source_marker = 1;
    if (strstr(line, "i32:(timed_out)"))
	dump->timeout_checks++;
    if (strstr(line, "i32:(source_location)"))
	dump->source_location_stores++;
    if (strstr(line, "4(source_location)")
	|| strstr(line, "8(source_location)"))
	dump->source_location_field_stores++;
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

static void
allocate_map_locals(JITDeoptMap *map, int count)
{
    int i;

    map->num_local_values = count;
    map->local_values = allocate(sizeof(JITLocalValue) * count);
    for (i = 0; i < count; i++)
	map->local_values[i].slot = i;
}

static void
set_program_value_type(JITProgram *program, int value, var_type type)
{
    if (!program->value_types)
	program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_types[value] = type;
}

static void
set_program_owned_value(JITProgram *program, int value)
{
    int i;

    if (!program->value_ownership)
	program->value_ownership = allocate(program->num_values);
    if (!program->value_owner_root) {
	program->value_owner_root = allocate(sizeof(int) * program->num_values);
	for (i = 0; i < program->num_values; i++)
	    program->value_owner_root[i] = JIT_OWNER_ROOT_NONE;
    }
    program->value_ownership[value] = JIT_OWNERSHIP_OWNED;
    program->value_owner_root[value] = value;
}

static void
set_program_owned_home(JITProgram *program, int value, int slot)
{
    int i;

    set_program_owned_value(program, value);
    if (!program->value_owned_slots) {
	program->value_owned_slots = allocate(sizeof(int) * program->num_values);
	for (i = 0; i < program->num_values; i++)
	    program->value_owned_slots[i] = -1;
    }
    program->value_owned_slots[value] = slot;
    if (program->num_owned_slots <= slot)
	program->num_owned_slots = slot + 1;
}

static void
use_compact_tag_slots(JITProgram *program)
{
    int value;

    program->value_tag_slots = allocate(sizeof(int) * program->num_values);
    for (value = 0; value < program->num_values; value++) {
	program->value_tag_slots[value] = -1;
	if (program->value_is_tagged[value])
	    program->value_tag_slots[value] = program->num_tag_slots++;
    }
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
two_tick_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *one = instruction(HIR_TAC_CONST);
    JITInstruction *first_tick = instruction(HIR_TAC_TICK);
    JITInstruction *two = instruction(HIR_TAC_CONST);
    JITInstruction *second_tick = instruction(HIR_TAC_TICK);
    JITInstruction *add = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 4;
    program->num_blocks = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    one->value = 1;
    one->literal = 1;
    first_tick->source_lineno = 7;
    first_tick->bytecode_pc = 11;
    two->value = 2;
    two->literal = 2;
    second_tick->source_lineno = 8;
    second_tick->bytecode_pc = 12;
    add->source_lineno = 8;
    add->bytecode_pc = 12;
    add->value = 3;
    add->src1 = 1;
    add->src2 = 2;
    add->op = HIR_OP_ADD;
    ret->src1 = 3;
    one->next = first_tick;
    first_tick->next = two;
    two->next = second_tick;
    second_tick->next = add;
    add->next = ret;
    block->first = one;
    block->last = ret;
    return program;
}

static JITProgram *
duplicate_tick_exit_program(void)
{
    JITProgram *program = two_tick_program();
    JITInstruction *first_tick = program->blocks->first->next;
    JITInstruction *second_tick = first_tick->next->next;

    second_tick->source_lineno = first_tick->source_lineno;
    second_tick->bytecode_pc = first_tick->bytecode_pc;
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
    program->deopt_maps[0].guard_value[0] = 1;
    program->deopt_maps[0].guard_local[0] = 0;
    program->deopt_maps[0].guard_local[1] = -1;
    program->deopt_maps[0].guard_expected[0] = JIT_TYPE_MASK(TYPE_INT);
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
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
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
    map->native_resume = allocate(sizeof(JITNativeResume));
    map->native_resume->valid = 1;
    map->native_resume->rehydratable = 1;
    map->native_resume->num_values = 1;
    map->native_resume->values = allocate(sizeof(JITResumeValue));
    map->native_resume->values[0].value = 2;
    map->native_resume->values[0].source = JIT_RESUME_RESULT;
    map->bytecode_pc = map->error_pc = 25;
    map->stack_depth = 1;
    map->num_locals = 1;
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
    set_program_value_type(program, 1, TYPE_LIST);
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
    use_compact_tag_slots(program);
    return program;
}

static JITProgram *
owned_builtin_call_program(unsigned func)
{
    JITProgram *program = builtin_call_program(func);
    JITInstruction *load = program->blocks->first;
    JITInstruction *call = load->next;
    JITInstruction *ret = call->next;
    JITInstruction *singleton = instruction(HIR_TAC_UNARY);
    JITDeoptMap *map = &program->deopt_maps[1];

    program->num_values = 4;
    program->value_types = myrealloc(program->value_types,
				     sizeof(var_type) * program->num_values,
				     M_PROGRAM);
    program->value_is_tagged = myrealloc(program->value_is_tagged,
					 program->num_values, M_PROGRAM);
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_LIST;
    program->value_types[3] = TYPE_ANY;
    program->value_is_tagged[1] = 0;
    program->value_is_tagged[2] = 0;
    program->value_is_tagged[3] = 1;
    set_program_owned_home(program, 2, 0);

    singleton->value = 2;
    singleton->src1 = 1;
    singleton->op = HIR_OP_MAKE_SINGLETON_LIST;
    singleton->next = call;
    load->literal_type = TYPE_STR;
    load->next = singleton;
    call->value = 3;
    call->src1 = 2;
    ret->src1 = 3;
    map->native_resume->values[0].value = 3;
    map->stack_values[0] = 2;
    map->stack_types[0] = TYPE_LIST;
    map->stack_owner_slots = allocate(sizeof(int));
    map->stack_owner_slots[0] = 0;
    map->local_values[0].value = 2;
    map->local_owner_slots = allocate(sizeof(int));
    map->local_owner_slots[0] = 0;
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
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
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
    allocate_map_locals(map, 2);
    map->local_values[0].value = 1;
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
    allocate_map_locals(map, 2);
    map->local_values[0].value = 1;
    map->local_values[1].value = 2;
    set_program_value_type(program, 2, TYPE_LIST);
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
    map->native_resume = allocate(sizeof(JITNativeResume));
    map->native_resume->valid = 1;
    map->native_resume->rehydratable = 1;
    map->native_resume->num_values = 4;
    map->native_resume->values = allocate(sizeof(JITResumeValue) * 4);
    map->native_resume->values[0].value = 1;
    map->native_resume->values[0].source = JIT_RESUME_OPERAND;
    map->native_resume->values[0].index = -1;
    map->native_resume->values[1].value = 2;
    map->native_resume->values[1].source = JIT_RESUME_OPERAND;
    map->native_resume->values[1].index = -1;
    map->native_resume->values[2].value = 3;
    map->native_resume->values[2].source = JIT_RESUME_OPERAND;
    map->native_resume->values[2].index = -1;
    map->native_resume->values[3].value = 4;
    map->native_resume->values[3].source = JIT_RESUME_RESULT;
    map->bytecode_pc = map->error_pc = 30;
    map->stack_depth = 3;
    map->ticks_charged = 1;
    map->num_locals = 3;
    allocate_map_locals(map, 3);
    map->local_values[0].value = 1;
    map->local_values[1].value = 2;
    map->local_values[2].value = 3;
    set_program_value_type(program, 1, TYPE_OBJ);
    set_program_value_type(program, 2, TYPE_STR);
    set_program_value_type(program, 3, TYPE_LIST);
    map->stack_values = allocate(sizeof(int) * 3);
    map->stack_types = allocate(sizeof(var_type) * 3);
    map->stack_slots = allocate(sizeof(ResumeStackSlot) * 3);
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
call_verb_preserved_float_program(void)
{
    JITProgram *program = call_verb_program();
    JITDeoptMap *map = &program->deopt_maps[1];
    JITInstruction *load_args = program->blocks->first->next->next;
    JITInstruction *load_float = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *return_instr = program->blocks->last;

    program->num_values = 6;
    program->num_vars = 4;
    program->value_types = myrealloc(program->value_types,
				     sizeof(var_type) * 6, M_PROGRAM);
    program->value_is_tagged = myrealloc(program->value_is_tagged, 6,
					 M_PROGRAM);
    program->value_types[5] = TYPE_FLOAT;
    program->value_is_tagged[5] = 0;
    map->num_locals = 4;
    map->num_local_values = 4;
    map->local_values = myrealloc(map->local_values,
				  sizeof(JITLocalValue) * 4, M_PROGRAM);
    map->local_values[3].slot = 3;
    map->local_values[3].value = 5;
    map->native_resume->values[3].value = 5;
    map->native_resume->values[3].source = JIT_RESUME_LOCAL;
    map->native_resume->values[3].index = 3;
    load_float->value = 5;
    load_float->local_id = 3;
    load_float->literal_type = TYPE_FLOAT;
    load_float->next = load_args->next;
    load_args->next = load_float;
    return_instr->src1 = 5;
    return_instr->literal_type = TYPE_FLOAT;
    return program;
}

static JITProgram *
call_verb_preserved_property_program(void)
{
    JITProgram *program = call_verb_program();
    JITDeoptMap *call_map = &program->deopt_maps[1];
    JITDeoptMap *property_map;
    JITInstruction *load_args = program->blocks->first->next->next;
    JITInstruction *load_property = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *get_property = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = program->blocks->last;

    program->num_values = 7;
    program->num_vars = 5;
    program->value_types = myrealloc(program->value_types,
				     sizeof(var_type) * 7, M_PROGRAM);
    program->value_is_tagged = myrealloc(program->value_is_tagged, 7,
					 M_PROGRAM);
    program->value_types[5] = TYPE_STR;
    program->value_types[6] = TYPE_ANY;
    program->value_is_tagged[5] = 0;
    program->value_is_tagged[6] = 1;
    set_program_owned_home(program, 6, 0);
    program->value_ownership[6] = JIT_OWNERSHIP_OWNED_PROPERTY;

    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 3, M_PROGRAM);
    call_map = &program->deopt_maps[1];
    property_map = &program->deopt_maps[2];
    memset(property_map, 0, sizeof(*property_map));
    program->num_deopt_maps = 3;
    property_map->reason = JIT_DEOPT_PROPERTY_READ;
    property_map->operation = HIR_OP_GET_PROP;
    property_map->bytecode_pc = property_map->error_pc = 29;
    property_map->num_locals = 5;
    allocate_map_locals(property_map, 5);
    property_map->local_values[0].value = 1;
    property_map->local_values[1].value = 2;
    property_map->local_values[2].value = 3;
    property_map->local_values[3].value = 5;
    property_map->stack_depth = 2;
    property_map->stack_values = allocate(sizeof(int) * 2);
    property_map->stack_types = allocate(sizeof(var_type) * 2);
    property_map->stack_values[0] = 1;
    property_map->stack_values[1] = 5;
    property_map->stack_types[0] = TYPE_OBJ;
    property_map->stack_types[1] = TYPE_STR;

    call_map->num_locals = 5;
    call_map->num_local_values = 5;
    call_map->local_values = myrealloc(call_map->local_values,
				       sizeof(JITLocalValue) * 5, M_PROGRAM);
    call_map->local_values[3].slot = 3;
    call_map->local_values[3].value = 5;
    call_map->local_values[4].slot = 4;
    call_map->local_values[4].value = 6;
    call_map->native_resume->num_values = 5;
    call_map->native_resume->values = myrealloc(
	call_map->native_resume->values, sizeof(JITResumeValue) * 5, M_PROGRAM);
    call_map->native_resume->values[4].value = 6;
    call_map->native_resume->values[4].source = JIT_RESUME_OWNER;
    call_map->native_resume->values[4].index = 0;

    load_property->value = 5;
    load_property->local_id = 3;
    load_property->literal_type = TYPE_STR;
    load_property->next = get_property;
    get_property->value = 6;
    get_property->src1 = 1;
    get_property->src2 = 5;
    get_property->op = HIR_OP_GET_PROP;
    get_property->deopt_map = 2;
    get_property->bytecode_pc = 29;
    get_property->next = load_args->next;
    load_args->next = load_property;
    return_instr->src1 = 6;
    return_instr->literal_type = TYPE_ANY;
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
    set_program_owned_home(program, 3, 0);
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
    set_program_owned_home(program, 3, 0);
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
duplicate_owned_string_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *left = instruction(HIR_TAC_CONST);
    JITInstruction *right = instruction(HIR_TAC_CONST);
    JITInstruction *concat = instruction(HIR_TAC_BINARY);
    JITInstruction *duplicate = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    char *ls = str_dup("a");
    char *rs = str_dup("b");

    program->num_values = 5;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_STR;
    program->value_types[3] = TYPE_STR;
    program->value_types[4] = TYPE_STR;
    set_program_owned_home(program, 3, 0);
    set_program_owned_home(program, 4, 0);
    program->value_owner_root[4] = 3;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    left->value = 1;
    left->literal_type = TYPE_STR;
    left->literal = (uintptr_t) ls;
    left->next = right;
    right->value = 2;
    right->literal_type = TYPE_STR;
    right->literal = (uintptr_t) rs;
    right->next = concat;
    concat->value = 3;
    concat->src1 = 1;
    concat->src2 = 2;
    concat->op = HIR_OP_ADD;
    concat->next = duplicate;
    duplicate->value = 4;
    duplicate->src1 = 3;
    duplicate->src2 = 3;
    duplicate->op = HIR_OP_ADD;
    duplicate->next = ret;
    ret->src1 = 4;
    ret->literal_type = TYPE_STR;
    block->first = left;
    block->last = ret;
    jit_analyze_owned_last_uses(program);
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
    set_program_owned_value(program, 3);
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
native_catch_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *body = allocate(sizeof(JITBlock));
    JITBlock *handler = allocate(sizeof(JITBlock));
    JITInstruction *lhs = instruction(HIR_TAC_CONST);
    JITInstruction *rhs = instruction(HIR_TAC_CONST);
    JITInstruction *divide = instruction(HIR_TAC_BINARY);
    JITInstruction *load_error = instruction(HIR_TAC_LOAD_ERROR);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_blocks = 2;
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_types[1] = TYPE_INT;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_INT;
    program->value_types[4] = TYPE_ERR;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 25;
    map->native_error_block = 2;

    program->blocks = body;
    program->last_block = handler;
    body->id = 1;
    body->num_successors = 2;
    body->successors[0] = 2;
    body->successors[1] = 2;
    body->next = handler;
    handler->id = 2;

    lhs->value = 1;
    lhs->literal = 1;
    lhs->literal_type = TYPE_INT;
    lhs->next = rhs;
    rhs->value = 2;
    rhs->literal = 0;
    rhs->literal_type = TYPE_INT;
    rhs->next = divide;
    divide->value = 3;
    divide->src1 = 1;
    divide->src2 = 2;
    divide->op = HIR_OP_DIV;
    divide->deopt_map = 1;
    divide->error_block = 2;
    divide->bytecode_pc = 25;
    body->first = lhs;
    body->last = divide;

    load_error->value = 4;
    load_error->next = ret;
    ret->src1 = 4;
    ret->literal_type = TYPE_ERR;
    handler->first = load_error;
    handler->last = ret;
    return program;
}

static JITProgram *
catch_stack_marker_program(int native_error)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *const_codes = instruction(HIR_TAC_CONST);
    JITInstruction *const_pc = instruction(HIR_TAC_CONST);
    JITInstruction *const_catch = instruction(HIR_TAC_CONST);
    JITInstruction *deopt_op = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = native_error ? 7 : 4;
    program->num_vars = 0;
    program->num_blocks = 1;
    program->num_deopt_maps = 2;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_types[0] = TYPE_INT;
    program->value_types[1] = TYPE_INT;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_CATCH;
    if (native_error) {
	program->value_types[4] = TYPE_INT;
	program->value_types[5] = TYPE_INT;
	program->value_types[6] = TYPE_INT;
    }

    map = &program->deopt_maps[1];
    map->bytecode_pc = 25;
    map->error_pc = 25;
    map->stack_depth = 3;
    map->ticks_charged = 1;
    map->num_locals = 0;
    map->stack_values = allocate(sizeof(int) * 3);
    map->stack_types = allocate(sizeof(var_type) * 3);
    map->stack_slots = allocate(sizeof(ResumeStackSlot) * 3);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    map->stack_types[0] = TYPE_INT;
    map->stack_types[1] = TYPE_INT;
    map->stack_types[2] = TYPE_CATCH;
    map->stack_slots[0].kind = RSS_VALUE;
    map->stack_slots[1].kind = RSS_HANDLER_PC;
    map->stack_slots[1].data = 77;
    map->stack_slots[2].kind = RSS_CATCH;
    map->stack_slots[2].data = 1;

    program->blocks = program->last_block = block;
    block->id = 1;

    const_codes->value = 1;
    const_codes->literal = 0;
    const_codes->literal_type = TYPE_INT;
    const_codes->next = const_pc;

    const_pc->value = 2;
    const_pc->literal = 999;
    const_pc->literal_type = TYPE_INT;
    const_pc->next = const_catch;

    const_catch->value = 3;
    const_catch->literal = 1;
    const_catch->literal_type = TYPE_CATCH;
    if (native_error) {
	JITInstruction *const_lhs = instruction(HIR_TAC_CONST);
	JITInstruction *const_rhs = instruction(HIR_TAC_CONST);

	const_catch->next = const_lhs;
	const_lhs->value = 4;
	const_lhs->literal = 1;
	const_lhs->literal_type = TYPE_INT;
	const_lhs->next = const_rhs;
	const_rhs->value = 5;
	const_rhs->literal = 0;
	const_rhs->literal_type = TYPE_INT;
	const_rhs->next = deopt_op;
	deopt_op->kind = HIR_TAC_BINARY;
	deopt_op->value = 6;
	deopt_op->src1 = 4;
	deopt_op->src2 = 5;
	deopt_op->op = HIR_OP_DIV;
	deopt_op->deopt_map = 1;
	deopt_op->bytecode_pc = 25;
	deopt_op->source_lineno = 9;
	block->last = deopt_op;
    } else {
	const_catch->next = deopt_op;
	deopt_op->deopt_map = 1;
	deopt_op->bytecode_pc = 25;
	block->last = deopt_op;
    }

    block->first = const_codes;
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
    map->stack_slots = allocate(sizeof(ResumeStackSlot));
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
    map->stack_slots = allocate(sizeof(ResumeStackSlot));
    map->stack_values[0] = 1;
    map->stack_types[0] = TYPE_FINALLY;
    map->stack_slots[0].kind = RSS_FINALLY;
    map->stack_slots[0].data = 88;

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
    map->stack_slots = allocate(sizeof(ResumeStackSlot) * 4);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    map->stack_values[3] = 4;
    map->stack_types[0] = TYPE_FINALLY;
    map->stack_types[1] = TYPE_INT;
    map->stack_types[2] = TYPE_INT;
    map->stack_types[3] = TYPE_CATCH;
    map->stack_slots[0].kind = RSS_FINALLY;
    map->stack_slots[0].data = 99;
    map->stack_slots[1].kind = RSS_VALUE;
    map->stack_slots[2].kind = RSS_HANDLER_PC;
    map->stack_slots[2].data = 55;
    map->stack_slots[3].kind = RSS_CATCH;
    map->stack_slots[3].data = 1;

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
    set_program_owned_value(program, 4);

    map = &program->deopt_maps[1];
    map->bytecode_pc = 10;
    map->error_pc = 10;
    map->stack_depth = 3;
    map->ticks_charged = 1;
    map->num_locals = 1;
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
    set_program_value_type(program, 1, base_type);
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
tagged_parent_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load_list = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *const_idx = instruction(HIR_TAC_CONST);
    JITInstruction *index_instr = instruction(HIR_TAC_BINARY);
    JITInstruction *parent_instr = instruction(HIR_TAC_UNARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 5);
    program->value_is_tagged = allocate(5);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_is_tagged[3] = 1;
    program->value_types[4] = TYPE_OBJ;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->bytecode_pc = map->error_pc = 31;
    map->source_lineno = 5;
    map->operation = HIR_OP_PARENT;
    map->reason = JIT_DEOPT_ARITHMETIC_TYPE;
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
    index_instr->next = parent_instr;
    parent_instr->value = 4;
    parent_instr->src1 = 3;
    parent_instr->op = HIR_OP_PARENT;
    parent_instr->deopt_map = 1;
    parent_instr->next = ret;
    ret->src1 = 4;
    ret->literal_type = TYPE_OBJ;
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
list_index_tagged_consumer_program(HIROp op, var_type rhs_type)
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
    program->value_types[4] = op == HIR_OP_IN ? TYPE_LIST : rhs_type;
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
    } else if (rhs_type == TYPE_FLOAT) {
	FlNum literal = 1.5;

	memcpy(&rhs_instr->literal, &literal, sizeof(literal));
	rhs_instr->literal_type = TYPE_FLOAT;
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
tagged_unary_result_program(HIROp op, var_type result_type)
{
    JITProgram *program = tagged_unary_program(op);
    JITInstruction *unary = program->blocks->first->next;
    JITInstruction *ret = unary->next;

    program->value_types[2] = result_type;
    set_program_owned_value(program, 2);
    ret->literal_type = result_type;
    return program;
}

static Var
tagged_test_value(var_type type)
{
    Var value;

    value.type = type;
    switch (type) {
    case TYPE_INT:
	value.v.num = 17;
	break;
    case TYPE_OBJ:
	value.v.obj = 17;
	break;
    case TYPE_STR:
	value.v.str = str_dup("tagged value");
	break;
    case TYPE_ERR:
	value.v.err = E_INVARG;
	break;
    case TYPE_LIST:
	value = new_list(1);
	value.v.list[1].type = TYPE_INT;
	value.v.list[1].v.num = 17;
	break;
    case TYPE_FLOAT:
	value.v.fnum = box_fl(17.5);
	break;
#ifdef WAIF_CORE
    case TYPE_WAIF:
	value = hir_test_new_waif();
	break;
#endif
    default:
	panic("unsupported tagged test value type");
    }
    return value;
}

static JITProgram *
float_singleton_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *constant = instruction(HIR_TAC_CONST);
    JITInstruction *singleton = instruction(HIR_TAC_UNARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    FlNum literal = 1.5;

    program->num_values = 3;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * 3);
    program->value_is_tagged = allocate(3);
    program->value_types[1] = TYPE_FLOAT;
    program->value_types[2] = TYPE_LIST;
    set_program_owned_value(program, 2);
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    constant->value = 1;
    memcpy(&constant->literal, &literal, sizeof(literal));
    constant->literal_type = TYPE_FLOAT;
    constant->next = singleton;
    singleton->value = 2;
    singleton->src1 = 1;
    singleton->op = HIR_OP_MAKE_SINGLETON_LIST;
    singleton->next = ret;
    ret->src1 = 2;
    ret->literal_type = TYPE_LIST;
    block->first = constant;
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
    if (op == HIR_OP_ADD)
	set_program_owned_value(program, 3);
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
tagged_binary_result_program(HIROp op, var_type result_type)
{
    JITProgram *program = tagged_binary_program(op);
    JITInstruction *binary = program->blocks->first->next->next;
    JITInstruction *ret = binary->next;

    program->value_types[3] = result_type;
    if (op == HIR_OP_LIST_ADD_TAIL)
	set_program_owned_home(program, 3, 0);
    ret->literal_type = result_type;
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
    set_program_owned_value(program, 6);
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
    jit_analyze_owned_last_uses(program);
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
	    int value = jit_deopt_map_local_value(program, map, i);

	    if (value > 0) {
		var_type type = jit_deopt_map_local_type(program, map, i);
		Var val = materialize_deopt_value(type, values[value]);
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

static JITProgram *
owned_last_use_program(int loop, int use_old_after)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *copy = instruction(HIR_TAC_PARALLEL_COPY);
    JITInstruction *candidate = instruction(HIR_TAC_BINARY);
    JITInstruction *after = use_old_after
	? instruction(HIR_TAC_UNARY) : 0;
    JITInstruction *terminal = instruction(loop ? HIR_TAC_JUMP
					       : HIR_TAC_RETURN);
    JITCopy *pair = allocate(sizeof(JITCopy));

    program->num_values = 4;
    program->num_blocks = 1;
    program->blocks = program->last_block = block;
    program->value_ownership = allocate(program->num_values);
    program->value_ownership[1] = JIT_OWNERSHIP_OWNED;
    block->id = 1;
    block->num_successors = loop ? 1 : 0;
    block->successors[0] = 1;
    pair->dst = 3;
    pair->src = 1;
    copy->copies = pair;
    copy->next = candidate;
    candidate->value = loop ? 1 : 2;
    candidate->src1 = 3;
    candidate->op = HIR_OP_ADD;
    if (after) {
	candidate->next = after;
	after->value = 2;
	after->src1 = 3;
	after->op = HIR_OP_NOT;
	after->next = terminal;
    } else
	candidate->next = terminal;
    if (loop) {
	JITInstruction *backedge = instruction(HIR_TAC_PARALLEL_COPY);
	JITCopy *backedge_pair = allocate(sizeof(JITCopy));

	backedge_pair->dst = 3;
	backedge_pair->src = 1;
	backedge->copies = backedge_pair;
	if (after)
	    after->next = backedge;
	else
	    candidate->next = backedge;
	backedge->next = terminal;
    } else {
	terminal->src1 = use_old_after ? 3 : 2;
	terminal->literal_type = TYPE_INT;
    }
    block->first = copy;
    block->last = terminal;
    return program;
}

static JITInstruction *
owned_last_use_candidate(JITProgram *program)
{
    return program->blocks->first->next;
}

static JITProgram *
owned_last_use_branch_program(int old_value_on_successor)
{
    JITProgram *program = new_jit_program();
    JITBlock *entry = allocate(sizeof(JITBlock));
    JITBlock *left = allocate(sizeof(JITBlock));
    JITBlock *right = allocate(sizeof(JITBlock));
    JITInstruction *copy = instruction(HIR_TAC_PARALLEL_COPY);
    JITInstruction *candidate = instruction(HIR_TAC_BINARY);
    JITInstruction *branch = instruction(HIR_TAC_BRANCH_FALSE);
    JITInstruction *left_return = instruction(HIR_TAC_RETURN);
    JITInstruction *right_return = instruction(HIR_TAC_RETURN);
    JITCopy *pair = allocate(sizeof(JITCopy));

    program->num_values = 5;
    program->num_blocks = 3;
    program->blocks = entry;
    program->last_block = right;
    program->value_ownership = allocate(program->num_values);
    program->value_ownership[1] = JIT_OWNERSHIP_OWNED;
    entry->id = 1;
    entry->num_successors = 2;
    entry->successors[0] = 2;
    entry->successors[1] = 3;
    entry->next = left;
    left->id = 2;
    left->next = right;
    right->id = 3;
    pair->dst = 3;
    pair->src = 1;
    copy->copies = pair;
    copy->next = candidate;
    candidate->value = 2;
    candidate->src1 = 3;
    candidate->op = HIR_OP_ADD;
    candidate->next = branch;
    branch->src1 = 4;
    entry->first = copy;
    entry->last = branch;
    left_return->src1 = old_value_on_successor ? 3 : 2;
    left_return->literal_type = TYPE_INT;
    left->first = left->last = left_return;
    right_return->src1 = 2;
    right_return->literal_type = TYPE_INT;
    right->first = right->last = right_return;
    return program;
}

static JITProgram *
owned_last_use_third_operand_program(int use_after)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *concat = instruction(HIR_TAC_BINARY);
    JITInstruction *set = instruction(HIR_TAC_INDEX_SET);
    JITInstruction *after = use_after ? instruction(HIR_TAC_UNARY) : 0;
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 8;
    program->num_blocks = 1;
    program->blocks = program->last_block = block;
    program->value_ownership = allocate(program->num_values);
    program->value_ownership[3] = JIT_OWNERSHIP_OWNED;
    block->id = 1;
    concat->value = 3;
    concat->src1 = 1;
    concat->src2 = 2;
    concat->op = HIR_OP_ADD;
    concat->next = set;
    set->value = 6;
    set->src1 = 4;
    set->src2 = 5;
    set->src3 = 3;
    set->next = after ? after : ret;
    if (after) {
	after->value = 7;
	after->src1 = 3;
	after->op = HIR_OP_LENGTH;
	after->next = ret;
    }
    ret->src1 = 6;
    block->first = concat;
    block->last = ret;
    return program;
}

static JITProgram *
tagged_guard_instruction_program(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *guard = instruction(HIR_TAC_GUARD_TYPE);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 2;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_is_tagged[1] = 1;
    use_compact_tag_slots(program);
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    map->reason = JIT_DEOPT_TYPE_GUARD;
    map->bytecode_pc = map->error_pc = 80;
    program->num_deopt_maps = 2;
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->next = guard;
    guard->src1 = 1;
    guard->guarded_operands = JIT_LAST_USE_SRC1;
    guard->guarded_type_masks[0] = JIT_TYPE_MASK(TYPE_INT)
	| JIT_TYPE_MASK(TYPE_FLOAT);
    guard->deopt_map = 1;
    guard->next = ret;
    ret->src1 = 1;
    ret->literal_type = TYPE_ANY;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
index_set_program(int direct_int_list)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *index = instruction(HIR_TAC_CONST);
    JITInstruction *value = instruction(HIR_TAC_CONST);
    JITInstruction *set = instruction(HIR_TAC_INDEX_SET);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = TYPE_LIST;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_INT;
    program->value_types[4] = TYPE_LIST;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    map->reason = JIT_DEOPT_RANGE_OP;
    map->bytecode_pc = map->error_pc = 81;
    program->num_deopt_maps = 2;
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->next = index;
    index->value = 2;
    index->literal = 1;
    index->next = value;
    value->value = 3;
    value->literal = 42;
    value->next = set;
    set->value = 4;
    set->src1 = 1;
    set->src2 = 2;
    set->src3 = 3;
    set->local_id = 0;
    set->deopt_map = 1;
    set->direct_int_list_index_set = direct_int_list;
    set->next = ret;
    ret->src1 = 4;
    ret->literal_type = TYPE_LIST;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
put_prop_lowering_program(int tagged_object, var_type rhs_type,
			  int tagged_result)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *object = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *property = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *rhs = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *put = instruction(HIR_TAC_PUT_PROP);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITDeoptMap *map;

    program->num_values = 5;
    program->num_vars = 3;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = tagged_object ? TYPE_ANY : TYPE_OBJ;
    program->value_types[2] = TYPE_STR;
    program->value_types[3] = rhs_type;
    program->value_types[4] = tagged_result ? TYPE_ANY : rhs_type;
    program->value_is_tagged[1] = tagged_object;
    program->value_is_tagged[4] = tagged_result;
    use_compact_tag_slots(program);
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    map->reason = JIT_DEOPT_PROPERTY_WRITE;
    map->bytecode_pc = map->error_pc = 82;
    map->stack_depth = 3;
    map->stack_values = allocate(sizeof(int) * map->stack_depth);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_values[2] = 3;
    program->num_deopt_maps = 2;
    program->blocks = program->last_block = block;
    block->id = 1;
    object->value = 1;
    object->local_id = 0;
    object->next = property;
    property->value = 2;
    property->local_id = 1;
    property->next = rhs;
    rhs->value = 3;
    rhs->local_id = 2;
    rhs->next = put;
    put->value = 4;
    put->src1 = 1;
    put->src2 = 2;
    put->deopt_map = 1;
    put->next = ret;
    ret->src1 = 4;
    ret->literal_type = tagged_result ? TYPE_ANY : rhs_type;
    block->first = object;
    block->last = ret;
    return program;
}

static JITProgram *
tagged_range_ref_program(void)
{
    JITProgram *program = range_ref_test_program(TYPE_ANY);

    program->value_is_tagged = allocate(program->num_values);
    program->value_is_tagged[1] = 1;
    program->value_is_tagged[2] = 1;
    program->value_is_tagged[3] = 1;
    program->value_is_tagged[4] = 1;
    use_compact_tag_slots(program);
    return program;
}

static JITProgram *
typed_binary_lowering_program(HIROp op, var_type left_type,
			      var_type right_type, var_type result_type,
			      int tagged_left, int tagged_right,
			      int tagged_result)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *left = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *right = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *binary = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 4;
    program->num_vars = 2;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = tagged_left ? TYPE_ANY : left_type;
    program->value_types[2] = tagged_right ? TYPE_ANY : right_type;
    program->value_types[3] = tagged_result ? TYPE_ANY : result_type;
    program->value_is_tagged[1] = tagged_left;
    program->value_is_tagged[2] = tagged_right;
    program->value_is_tagged[3] = tagged_result;
    use_compact_tag_slots(program);
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    left->value = 1;
    left->local_id = 0;
    left->next = right;
    right->value = 2;
    right->local_id = 1;
    right->next = binary;
    binary->value = 3;
    binary->src1 = 1;
    binary->src2 = 2;
    binary->op = op;
    binary->deopt_map = 0;
    binary->next = ret;
    ret->src1 = 3;
    ret->literal_type = tagged_result ? TYPE_ANY : result_type;
    block->first = left;
    block->last = ret;
    return program;
}

static JITProgram *
typed_unary_lowering_program(HIROp op, var_type operand_type,
			     var_type result_type, int tagged_operand,
			     int tagged_result, JITTypeMask guarded_types)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *unary = instruction(HIR_TAC_UNARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);

    program->num_values = 3;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = tagged_operand ? TYPE_ANY : operand_type;
    program->value_types[2] = tagged_result ? TYPE_ANY : result_type;
    program->value_is_tagged[1] = tagged_operand;
    program->value_is_tagged[2] = tagged_result;
    use_compact_tag_slots(program);
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->next = unary;
    unary->value = 2;
    unary->src1 = 1;
    unary->op = op;
    unary->deopt_map = 0;
    unary->guarded_operands = guarded_types ? JIT_LAST_USE_SRC1 : 0;
    unary->guarded_type_masks[0] = guarded_types;
    unary->next = ret;
    ret->src1 = 2;
    ret->literal_type = tagged_result ? TYPE_ANY : result_type;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
owned_property_result_program(void)
{
    JITProgram *program = typed_binary_lowering_program(HIR_OP_GET_PROP,
	TYPE_OBJ, TYPE_STR, TYPE_ANY, 0, 0, 1);
    JITInstruction *get = program->blocks->first->next->next;
    JITDeoptMap *map;

    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->reason = JIT_DEOPT_PROPERTY_READ;
    map->operation = HIR_OP_GET_PROP;
    map->bytecode_pc = map->error_pc = 72;
    map->num_locals = 2;
    allocate_map_locals(map, 2);
    map->local_values[0].value = 1;
    map->local_values[1].value = 2;
    map->stack_depth = 2;
    map->stack_values = allocate(sizeof(int) * 2);
    map->stack_types = allocate(sizeof(var_type) * 2);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_types[0] = TYPE_OBJ;
    map->stack_types[1] = TYPE_STR;
    program->blocks->first->literal_type = TYPE_OBJ;
    program->blocks->first->next->literal_type = TYPE_STR;
    get->deopt_map = 1;
    get->bytecode_pc = 72;
    set_program_owned_home(program, 3, 0);
    program->value_ownership[3] = JIT_OWNERSHIP_OWNED_PROPERTY;
    return program;
}

static JITProgram *
repeated_owned_property_program(void)
{
    JITProgram *program = owned_property_result_program();
    JITInstruction *first_get = program->blocks->first->next->next;
    JITInstruction *second_get = instruction(HIR_TAC_BINARY);
    JITInstruction *return_instr = program->blocks->last;

    program->num_values = 5;
    program->value_types = myrealloc(program->value_types,
				     sizeof(var_type) * 5, M_PROGRAM);
    program->value_is_tagged = myrealloc(program->value_is_tagged, 5,
					 M_PROGRAM);
    program->value_ownership = myrealloc(program->value_ownership,
					 5, M_PROGRAM);
    program->value_owner_root = myrealloc(program->value_owner_root,
					  sizeof(int) * 5, M_PROGRAM);
    program->value_owned_slots = myrealloc(program->value_owned_slots,
					   sizeof(int) * 5, M_PROGRAM);
    program->value_types[4] = TYPE_ANY;
    program->value_is_tagged[4] = 1;
    program->value_ownership[4] = JIT_OWNERSHIP_OWNED_PROPERTY;
    program->value_owner_root[4] = 4;
    program->value_owned_slots[4] = 0;

    second_get->value = 4;
    second_get->src1 = first_get->src1;
    second_get->src2 = first_get->src2;
    second_get->op = HIR_OP_GET_PROP;
    second_get->deopt_map = first_get->deopt_map;
    second_get->bytecode_pc = first_get->bytecode_pc;
    second_get->next = return_instr;
    first_get->next = second_get;
    return_instr->src1 = 4;
    return program;
}

static JITProgram *
fixed_list_chain_program(int interrupted_capacity)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *first = instruction(HIR_TAC_CONST);
    JITInstruction *head = instruction(HIR_TAC_UNARY);
    JITInstruction *second = instruction(HIR_TAC_CONST);
    JITInstruction *tail1 = instruction(HIR_TAC_BINARY);
    JITInstruction *third = instruction(HIR_TAC_CONST);
    JITInstruction *tail2 = instruction(HIR_TAC_BINARY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    int i;

    program->num_values = 7;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_ownership = allocate(program->num_values);
    program->value_owned_slots = allocate(sizeof(int) * program->num_values);
    program->value_use_counts = allocate(sizeof(unsigned) * program->num_values);
    program->value_escape_flags = allocate(program->num_values);
    for (i = 1; i < program->num_values; i++) {
	program->value_types[i] = (i == 2 || i == 4 || i == 6)
	    ? TYPE_LIST : TYPE_INT;
	program->value_owned_slots[i] = -1;
    }
    program->value_ownership[2] = JIT_OWNERSHIP_OWNED;
    program->value_ownership[4] = JIT_OWNERSHIP_OWNED;
    program->value_ownership[6] = JIT_OWNERSHIP_OWNED;
    program->value_owned_slots[2] = 0;
    program->value_owned_slots[4] = 0;
    program->value_owned_slots[6] = 0;
    program->value_use_counts[1] = 1;
    program->value_use_counts[2] = 1;
    program->value_use_counts[3] = 1;
    program->value_use_counts[4] = 1;
    program->value_use_counts[5] = 1;
    program->value_use_counts[6] = 1;
    program->num_owned_slots = 1;
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    first->value = 1;
    first->literal = 10;
    first->next = head;
    head->value = 2;
    head->src1 = 1;
    head->op = HIR_OP_MAKE_SINGLETON_LIST;
    head->next = second;
    second->value = 3;
    second->literal = 20;
    second->next = tail1;
    tail1->value = 4;
    tail1->src1 = 2;
    tail1->src2 = 3;
    tail1->op = HIR_OP_LIST_ADD_TAIL;
    tail1->owned_last_use = JIT_LAST_USE_SRC1;
    tail1->exit_mask = interrupted_capacity ? JIT_EXIT_ERROR : JIT_EXIT_NONE;
    tail1->next = third;
    third->value = 5;
    third->literal = 30;
    third->next = tail2;
    tail2->value = 6;
    tail2->src1 = 4;
    tail2->src2 = 5;
    tail2->op = HIR_OP_LIST_ADD_TAIL;
    tail2->owned_last_use = JIT_LAST_USE_SRC1;
    tail2->next = ret;
    ret->src1 = 6;
    ret->literal_type = TYPE_LIST;
    block->first = first;
    block->last = ret;
    return program;
}

static JITProgram *
typed_branch_program(var_type type, int tagged)
{
    JITProgram *program = branch_program();

    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = tagged ? TYPE_ANY : type;
    program->value_types[2] = TYPE_INT;
    program->value_types[3] = TYPE_INT;
    program->value_types[4] = TYPE_INT;
    program->value_is_tagged[1] = tagged;
    use_compact_tag_slots(program);
    return program;
}

static JITProgram *
parallel_copy_lowering_program(var_type source_type, var_type destination_type,
			       int tagged_source, int tagged_destination)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *parallel = instruction(HIR_TAC_PARALLEL_COPY);
    JITInstruction *ret = instruction(HIR_TAC_RETURN);
    JITCopy *copy = allocate(sizeof(JITCopy));

    program->num_values = 3;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = tagged_source ? TYPE_ANY : source_type;
    program->value_types[2] = tagged_destination
	? TYPE_ANY : destination_type;
    program->value_is_tagged[1] = tagged_source;
    program->value_is_tagged[2] = tagged_destination;
    use_compact_tag_slots(program);
    add_entry_deopt_map(program);
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->next = parallel;
    copy->dst = 2;
    copy->src = 1;
    parallel->copies = copy;
    parallel->next = ret;
    ret->src1 = 2;
    ret->literal_type = tagged_destination ? TYPE_ANY : destination_type;
    block->first = load;
    block->last = ret;
    return program;
}

static JITProgram *
typed_deopt_program(var_type type, int tagged)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *load = instruction(HIR_TAC_LOAD_LOCAL);
    JITInstruction *deopt = instruction(HIR_TAC_DEOPT);
    JITDeoptMap *map;

    program->num_values = 2;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = tagged ? TYPE_ANY : type;
    program->value_is_tagged[1] = tagged;
    use_compact_tag_slots(program);
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->reason = JIT_DEOPT_UNSUPPORTED_OP;
    map->operation = HIR_OP_FORK;
    map->bytecode_pc = map->error_pc = 71;
    map->stack_depth = 1;
    map->num_locals = 1;
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_types = allocate(sizeof(var_type));
    map->stack_values[0] = 1;
    map->stack_types[0] = tagged ? TYPE_ANY : type;
    map->guard_value[0] = 1;
    map->guard_local[0] = -1;
    map->guard_local[1] = -1;
    map->guard_expected[0] = JIT_TYPE_MASK(type);
    program->blocks = program->last_block = block;
    block->id = 1;
    load->value = 1;
    load->local_id = 0;
    load->literal_type = tagged ? TYPE_ANY : type;
    load->next = deopt;
    deopt->deopt_map = 1;
    deopt->op = HIR_OP_FORK;
    deopt->bytecode_pc = 71;
    block->first = load;
    block->last = deopt;
    return program;
}

static void
test_program_metadata_api(void)
{
    JITProgram *program = arithmetic_program();
    JITProgram *nonleaf = call_verb_program();
    JITProgram *unsupported;

    check(jit_program_state(0) == JIT_STATE_UNSUPPORTED,
	  "null JIT program state is wrong");
    check(!jit_program_compile(0), "null JIT program compiled");
    check(!strcmp(jit_program_state_name(program), "pending"),
	  "pending JIT program state name is wrong");
    program->state = JIT_STATE_COMPILED;
    check(!strcmp(jit_program_state_name(program), "compiled"),
	  "compiled JIT program state name is wrong");
    program->state = JIT_STATE_FAILED;
    check(!strcmp(jit_program_state_name(program), "failed"),
	  "failed JIT program state name is wrong");
    program->state = JIT_STATE_PENDING;

    check(jit_program_is_eligible(program) && !jit_program_is_eligible(0),
	  "JIT eligibility accessor is wrong");
    check(!jit_program_may_error(program) && !jit_program_may_error(0),
	  "JIT error accessor is wrong");
    check(jit_program_is_direct_leaf(program)
	  && jit_program_is_direct_leaf(program),
	  "leaf classification or its cache is wrong");
    check(!jit_program_is_direct_leaf(nonleaf),
	  "verb-calling program was classified as a leaf");
    check(jit_program_anchor_count(program) == program->num_resume_anchors
	  && jit_program_anchor_count(0) == 0,
	  "resume anchor accessor is wrong");
    check(jit_program_deopt_map_count(program) == program->num_deopt_maps
	  && jit_program_deopt_map_count(0) == 0,
	  "deopt map accessor is wrong");
    check(jit_program_warmup_generation(0) == 0,
	  "null warmup generation is wrong");
    check(jit_program_bytes(program) > 0 && jit_program_bytes(0) == 0,
	  "JIT program byte accounting accessor is wrong");
    check(!jit_program_has_location(program),
	  "fresh JIT program unexpectedly has a diagnostic location");
    jit_program_note_location(program, -1, 1);
    jit_program_note_location(program, 7, 0);
    check(!jit_program_has_location(program),
	  "invalid diagnostic location was accepted");
    jit_program_note_location(program, 7, 3);
    check(jit_program_has_location(program),
	  "valid diagnostic location was rejected");

    unsupported = jit_program_unsupported_with_diagnostic("reason", "detail");
    check(!jit_program_compile(unsupported),
	  "unsupported JIT program compiled");
    check(!strcmp(jit_program_state_name(unsupported), "unsupported")
	  && !strcmp(jit_program_reason(unsupported), "reason")
	  && !strcmp(jit_program_diagnostic(unsupported), "detail"),
	  "unsupported JIT program metadata is wrong");
    check(!strcmp(jit_program_reason(0), "unsupported-program")
	  && !strcmp(jit_program_diagnostic(0), "none"),
	  "null JIT program metadata is wrong");
    jit_program_free(unsupported);
    unsupported = jit_program_unsupported(0);
    check(!strcmp(jit_program_reason(unsupported), "unsupported-program")
	  && !strcmp(jit_program_diagnostic(unsupported), "none"),
	  "default unsupported JIT metadata is wrong");

    program->state = JIT_STATE_FAILED;
    check(!jit_program_compile(program), "failed JIT program compiled");
    program->state = JIT_STATE_PENDING;

    jit_program_free(unsupported);
    jit_program_free(nonleaf);
    jit_program_free(program);
}

static void
test_released_ir_restoration(void)
{
    Program bytecode;
    JITProgram *program = arithmetic_program();
    JITProgram *rebuilt;

    memset(&bytecode, 0, sizeof(bytecode));
    bytecode.ref_count = 1;
    program->bytecode_program = &bytecode;
    check(jit_program_compile(program),
	  "bytecode-backed JIT program did not compile");
    check(!program->blocks,
	  "compiled bytecode-backed program retained its lowering IR");

    rebuilt = arithmetic_program();
    jit_test_set_compiled_program(rebuilt);
    check(jit_program_is_direct_leaf(program),
	  "restored arithmetic IR was not classified as a leaf");
    check(!program->blocks,
	  "temporary restored IR was not released after inspection");

    program->direct_leaf = 0;
    rebuilt = call_verb_program();
    jit_test_set_compiled_program(rebuilt);
    check(!jit_program_is_direct_leaf(program),
	  "IR restoration accepted mismatched reconstruction metadata");
    check(!program->blocks,
	  "failed IR restoration published mismatched blocks");

    program->direct_leaf = 0;
    check(!jit_program_is_direct_leaf(program),
	  "IR restoration accepted a missing reconstruction");
    jit_program_free(program);
    check(bytecode.ref_count == 1,
	  "JIT program changed its borrowed bytecode reference");
}

static void
test_guard_and_index_set_lowering(void)
{
    JITProgram *guard = tagged_guard_instruction_program();
    JITProgram *direct_set = index_set_program(1);
    JITProgram *cow_set = index_set_program(0);
    JITProgram *float_property = put_prop_lowering_program(0, TYPE_FLOAT, 0);
    JITProgram *tagged_property = put_prop_lowering_program(1, TYPE_INT, 1);
    JITProgram *tagged_range = tagged_range_ref_program();
    JITProgram *fixed_chain = fixed_list_chain_program(0);
    JITProgram *checked_chain = fixed_list_chain_program(1);

    check(jit_program_compile(guard),
	  "tagged guard instruction did not compile");
    check(jit_program_compile(direct_set),
	  "direct integer-list index set did not compile");
    check(jit_program_compile(cow_set),
	  "copy-on-write list index set did not compile");
    check(jit_program_compile(float_property),
	  "floating-point property write did not compile");
    check(jit_program_compile(tagged_property),
	  "tagged property write did not compile");
    check(jit_program_compile(tagged_range),
	  "tagged range reference did not compile");
    check(jit_program_compile(fixed_chain),
	  "fixed-capacity list construction did not compile");
    check(jit_program_compile(checked_chain),
	  "capacity-checked list construction did not compile");

    jit_program_free(checked_chain);
    jit_program_free(fixed_chain);
    jit_program_free(tagged_range);
    jit_program_free(tagged_property);
    jit_program_free(float_property);
    jit_program_free(cow_set);
    jit_program_free(direct_set);
    jit_program_free(guard);
}

static void
test_numeric_and_comparison_lowering_matrix(void)
{
    static const HIROp integer_ops[] = {
	HIR_OP_ADD, HIR_OP_SUB, HIR_OP_MUL, HIR_OP_DIV, HIR_OP_MOD,
	HIR_OP_EXP, HIR_OP_EQ, HIR_OP_NE, HIR_OP_LT, HIR_OP_LE,
	HIR_OP_GT, HIR_OP_GE, HIR_OP_BITOR, HIR_OP_BITXOR,
	HIR_OP_BITAND, HIR_OP_SHL, HIR_OP_SHR, HIR_OP_LSHR,
	HIR_OP_MIN, HIR_OP_MAX, HIR_OP_ROTL32
    };
    static const HIROp float_arithmetic_ops[] = {
	HIR_OP_ADD, HIR_OP_SUB, HIR_OP_MUL, HIR_OP_DIV
    };
    static const HIROp comparison_ops[] = {
	HIR_OP_EQ, HIR_OP_NE, HIR_OP_LT, HIR_OP_LE, HIR_OP_GT, HIR_OP_GE
    };
    static const HIROp unary_ops[] = {
	HIR_OP_NEGATE, HIR_OP_NOT, HIR_OP_COMPLEMENT, HIR_OP_ABS,
	HIR_OP_TOINT, HIR_OP_TYPEOF, HIR_OP_TICKS_LEFT,
	HIR_OP_SECONDS_LEFT, HIR_OP_TIME
    };
    unsigned i;

    for (i = 0; i < sizeof(integer_ops) / sizeof(integer_ops[0]); i++) {
	JITProgram *program = binary_program(17, 3, integer_ops[i]);

	check(jit_program_compile(program),
	      "integer operation lowering matrix compile failed");
	jit_program_free(program);
    }
    for (i = 0; i < sizeof(float_arithmetic_ops)
	 / sizeof(float_arithmetic_ops[0]); i++) {
	JITProgram *program = float_binary_program(float_arithmetic_ops[i]);

	check(jit_program_compile(program),
	      "float arithmetic lowering matrix compile failed");
	jit_program_free(program);
    }
    for (i = 0; i < sizeof(comparison_ops) / sizeof(comparison_ops[0]); i++) {
	JITProgram *float_program = float_compare_program(comparison_ops[i]);
	JITProgram *string_program = string_compare_program("alpha", "beta",
							 comparison_ops[i]);
	JITProgram *tagged_program = tagged_binary_program(comparison_ops[i]);

	check(jit_program_compile(float_program),
	      "float comparison lowering matrix compile failed");
	check(jit_program_compile(string_program),
	      "string comparison lowering matrix compile failed");
	check(jit_program_compile(tagged_program),
	      "tagged comparison lowering matrix compile failed");
	jit_program_free(tagged_program);
	jit_program_free(string_program);
	jit_program_free(float_program);
    }
    for (i = 0; i < sizeof(unary_ops) / sizeof(unary_ops[0]); i++) {
	JITProgram *program = unary_program(17, unary_ops[i]);

	check(jit_program_compile(program),
	      "integer unary lowering matrix compile failed");
	jit_program_free(program);
    }
    {
	JITProgram *programs[] = {
	    typed_binary_lowering_program(HIR_OP_GET_PROP, TYPE_OBJ,
		TYPE_STR, TYPE_ANY, 0, 0, 1),
	    typed_binary_lowering_program(HIR_OP_GET_PROP, TYPE_OBJ,
		TYPE_STR, TYPE_ANY, 1, 0, 1),
	    typed_binary_lowering_program(HIR_OP_SUBLIST_FROM, TYPE_LIST,
		TYPE_INT, TYPE_LIST, 0, 0, 0),
	    typed_binary_lowering_program(HIR_OP_SUBLIST_FROM, TYPE_LIST,
		TYPE_INT, TYPE_LIST, 1, 1, 1),
	    typed_binary_lowering_program(HIR_OP_LIST_APPEND, TYPE_LIST,
		TYPE_LIST, TYPE_LIST, 0, 0, 0),
	    typed_binary_lowering_program(HIR_OP_LIST_APPEND, TYPE_LIST,
		TYPE_LIST, TYPE_LIST, 1, 1, 1),
	    typed_binary_lowering_program(HIR_OP_ADD, TYPE_STR,
		TYPE_STR, TYPE_STR, 0, 0, 0),
	    typed_binary_lowering_program(HIR_OP_ADD, TYPE_LIST,
		TYPE_LIST, TYPE_LIST, 0, 0, 0),
	    typed_binary_lowering_program(HIR_OP_EQ, TYPE_LIST,
		TYPE_LIST, TYPE_INT, 0, 0, 0),
	    typed_binary_lowering_program(HIR_OP_NE, TYPE_LIST,
		TYPE_LIST, TYPE_INT, 0, 0, 0),
	    typed_binary_lowering_program(HIR_OP_ADD, TYPE_FLOAT,
		TYPE_INT, TYPE_FLOAT, 0, 0, 0),
	    object_compare_program(HIR_OP_NE)
	};

	for (i = 0; i < sizeof(programs) / sizeof(programs[0]); i++) {
	    check(jit_program_compile(programs[i]),
		  "specialized binary lowering matrix compile failed");
	    jit_program_free(programs[i]);
	}
    }
    {
	JITProgram *owned_string = typed_binary_lowering_program(HIR_OP_ADD,
	    TYPE_STR, TYPE_STR, TYPE_STR, 0, 0, 0);
	JITProgram *proven_shift = binary_program(17, 3, HIR_OP_SHL);
	JITInstruction *concat = owned_string->blocks->first->next->next;
	JITInstruction *shift = proven_shift->blocks->first->next->next->next;
	int j;

	owned_string->value_ownership = allocate(owned_string->num_values);
	owned_string->value_owned_slots = allocate(sizeof(int)
	    * owned_string->num_values);
	for (j = 0; j < owned_string->num_values; j++)
	    owned_string->value_owned_slots[j] = -1;
	owned_string->value_ownership[concat->value] = JIT_OWNERSHIP_OWNED;
	owned_string->value_owned_slots[concat->value] = 0;
	owned_string->num_owned_slots = 1;
	shift->shift_count_proven_valid = 1;
	check(jit_program_compile(owned_string),
	      "owned string concatenation did not compile");
	check(jit_program_compile(proven_shift),
	      "proven shift count did not compile");
	jit_program_free(proven_shift);
	jit_program_free(owned_string);
    }
    {
	JITProgram *none_load = typed_unary_lowering_program(HIR_OP_TYPEOF,
	    TYPE_NONE, TYPE_INT, 0, 0, 0);
	JITProgram *programs[] = {
	    typed_unary_lowering_program(HIR_OP_CHECK_LIST_FOR_SPLICE,
		TYPE_LIST, TYPE_LIST, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_CHECK_LIST_FOR_SPLICE,
		TYPE_LIST, TYPE_LIST, 1, 1, 0),
	    typed_unary_lowering_program(HIR_OP_CHECK_LIST_FOR_SPLICE,
		TYPE_INT, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_LENGTH,
		TYPE_STR, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_LENGTH,
		TYPE_LIST, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_LENGTH,
		TYPE_ANY, TYPE_INT, 1, 1, 0),
	    typed_unary_lowering_program(HIR_OP_LENGTH,
		TYPE_ANY, TYPE_INT, 1, 1, JIT_TYPE_MASK(TYPE_STR)),
	    typed_unary_lowering_program(HIR_OP_LENGTH,
		TYPE_ANY, TYPE_INT, 1, 1, JIT_TYPE_MASK(TYPE_LIST)),
	    typed_unary_lowering_program(HIR_OP_LENGTH,
		TYPE_ANY, TYPE_INT, 1, 1,
		JIT_TYPE_MASK(TYPE_STR) | JIT_TYPE_MASK(TYPE_LIST)),
	    typed_unary_lowering_program(HIR_OP_VALID,
		TYPE_OBJ, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_VALID,
		TYPE_ANY, TYPE_INT, 1, 0, 0),
	    typed_unary_lowering_program(HIR_OP_VALID,
		TYPE_INT, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_PARENT,
		TYPE_OBJ, TYPE_OBJ, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_PARENT,
		TYPE_ANY, TYPE_ANY, 1, 1, 0),
	    typed_unary_lowering_program(HIR_OP_PARENT,
		TYPE_INT, TYPE_OBJ, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_TOINT,
		TYPE_FLOAT, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_TOINT,
		TYPE_INT, TYPE_FLOAT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_TYPEOF,
		TYPE_ANY, TYPE_INT, 1, 0, 0),
	    typed_unary_lowering_program(HIR_OP_ABS,
		TYPE_FLOAT, TYPE_FLOAT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_ABS,
		TYPE_FLOAT, TYPE_INT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_ABS,
		TYPE_INT, TYPE_FLOAT, 0, 0, 0),
	    typed_unary_lowering_program(HIR_OP_ABS,
		TYPE_ANY, TYPE_ANY, 1, 1, 0),
	    typed_unary_lowering_program(HIR_OP_ABS,
		TYPE_ANY, TYPE_ANY, 1, 1, JIT_TYPE_MASK(TYPE_INT)),
	    typed_unary_lowering_program(HIR_OP_CHECK_LIST_FOR_SPLICE,
		TYPE_LIST, TYPE_ANY, 0, 1, 0),
	    typed_unary_lowering_program(HIR_OP_MAKE_SINGLETON_LIST,
		TYPE_ANY, TYPE_ANY, 1, 1, 0)
	};

	none_load->blocks->first->literal_type = TYPE_NONE;
	check(jit_program_compile(none_load),
	      "none local load lowering compile failed");
	jit_program_free(none_load);
	for (i = 0; i < sizeof(programs) / sizeof(programs[0]); i++) {
	    check(jit_program_compile(programs[i]),
		  "specialized unary lowering matrix compile failed");
	    jit_program_free(programs[i]);
	}
    }
}

static void
test_tick_return_and_dump_lowering(void)
{
    JITProgram *batched = arithmetic_program();
    JITProgram *elided = arithmetic_program();
    JITProgram *return_zero = arithmetic_program();
    JITProgram *call = call_verb_program();
    JITProgram *copies = branch_program();
    JITProgram *string_branch = typed_branch_program(TYPE_STR, 0);
    JITProgram *list_branch = typed_branch_program(TYPE_LIST, 0);
    JITProgram *float_branch = typed_branch_program(TYPE_FLOAT, 0);
    JITProgram *tagged_branch = typed_branch_program(TYPE_ANY, 1);
    JITProgram *float_copy = parallel_copy_lowering_program(TYPE_FLOAT,
	TYPE_FLOAT, 0, 0);
    JITProgram *int_to_float = parallel_copy_lowering_program(TYPE_INT,
	TYPE_FLOAT, 0, 0);
    JITProgram *float_to_int = parallel_copy_lowering_program(TYPE_FLOAT,
	TYPE_INT, 0, 0);
    JITProgram *tagged_copy = parallel_copy_lowering_program(TYPE_ANY,
	TYPE_ANY, 1, 1);
    JITInstruction *batched_tick = batched->blocks->first->next->next;
    JITInstruction *elided_tick = elided->blocks->first->next->next;
    JITInstruction *ret = return_zero->blocks->last;
    struct mir_dump dump = { 0 };

    batched_tick->tick_batch_count = 3;
    elided_tick->tick_batch_count = (unsigned char) -1;
    ret->kind = HIR_TAC_RETURN0;
    ret->src1 = 0;
    check(jit_program_compile(batched), "batched tick did not compile");
    check(jit_program_compile(elided), "elided tick did not compile");
    check(jit_program_compile(return_zero), "zero return did not compile");
    check(jit_program_compile(string_branch), "string branch did not compile");
    check(jit_program_compile(list_branch), "list branch did not compile");
    check(jit_program_compile(float_branch), "float branch did not compile");
    check(jit_program_compile(tagged_branch), "tagged branch did not compile");
    check(jit_program_compile(float_copy), "float copy did not compile");
    check(jit_program_compile(int_to_float), "int-to-float copy did not compile");
    check(jit_program_compile(float_to_int), "float-to-int copy did not compile");
    check(jit_program_compile(tagged_copy), "tagged copy did not compile");
    check(jit_program_dump_hir(call, check_mir_line, &dump),
	  "verb-call HIR dump failed");
    check(jit_program_dump_hir(copies, check_mir_line, &dump),
	  "parallel-copy HIR dump failed");
    check(dump.lines > 0, "expanded HIR dumps produced no lines");

    jit_program_free(tagged_copy);
    jit_program_free(float_to_int);
    jit_program_free(int_to_float);
    jit_program_free(float_copy);
    jit_program_free(tagged_branch);
    jit_program_free(float_branch);
    jit_program_free(list_branch);
    jit_program_free(string_branch);
    jit_program_free(copies);
    jit_program_free(call);
    jit_program_free(return_zero);
    jit_program_free(elided);
    jit_program_free(batched);
}

static void
test_runtime_helper_edge_cases(void)
{
    Var homes[1];
    Var result;
    Var *list;
    const char *raw_string;
    int32_t error;
    const char *name;

    homes[0].type = TYPE_STR;
    homes[0].v.str = str_dup("owned discard");
    jit_rt_discard_owned(homes, 0, 0, TYPE_NONE);
    check(homes[0].type == TYPE_NONE,
	  "owned discard did not clear its owner home");
    raw_string = str_dup("raw discard");
    jit_rt_discard_owned(0, -1, (intptr_t) raw_string, TYPE_STR);

    list = jit_rt_sublist_from(0, 1);
    result.type = TYPE_LIST;
    result.v.list = list;
    check(list[0].v.num == 0, "null sublist base was not empty");
    free_var(result);
    result = new_list(1);
    result.v.list[1].type = TYPE_INT;
    result.v.list[1].v.num = 7;
    list = jit_rt_sublist_from(result.v.list, 0);
    check(list[0].v.num == 0, "out-of-range sublist was not empty");
    {
	Var empty = { .type = TYPE_LIST, .v.list = list };

	free_var(empty);
    }
    check(!jit_rt_list_index_set(0, 0, result.v.list, 1, 8, TYPE_INT,
				 &error) && error == E_TYPE,
	  "index set accepted a null environment");
    check(!jit_rt_list_index_set(&result, 0, 0, 1, 8, TYPE_INT, &error)
	  && error == E_TYPE,
	  "index set accepted a null list");
    free_var(result);

    check(!jit_rt_get_prop(0, "", 2, 0, 0, &error)
	  && error == E_PROPNF,
	  "property read did not report a missing property");
    check(!jit_rt_put_prop(0, "", 2, 1, TYPE_INT, &error)
	  && error == E_PROPNF,
	  "property write did not report a missing property");
    hir_test_set_builtin_property(BP_NAME);
    check(!jit_rt_put_prop(0, "name", 2, 1, TYPE_INT, &error)
	  && error == E_TYPE,
	  "built-in name accepted a non-string value");
    name = str_dup("renamed");
    check(!jit_rt_put_prop(0, "name", 1, (intptr_t) name, TYPE_STR,
			   &error) && error == E_PERM,
	  "built-in name ignored ownership permission");
    check(jit_rt_put_prop(0, "name", 2, (intptr_t) name, TYPE_STR,
			  &error) == 1 && error == E_NONE,
	  "wizard could not set built-in name");
    free_str(name);
    hir_test_set_builtin_property(BP_OWNER);
    check(!jit_rt_put_prop(0, "owner", 2, 1, TYPE_INT, &error)
	  && error == E_TYPE,
	  "built-in owner accepted a non-object value");
    check(!jit_rt_put_prop(0, "owner", 1, 2, TYPE_OBJ, &error)
	  && error == E_PERM,
	  "non-wizard changed built-in owner");
    check(jit_rt_put_prop(0, "owner", 2, 2, TYPE_OBJ, &error) == 1,
	  "wizard could not set built-in owner");
    hir_test_set_builtin_property(BP_PROGRAMMER);
    check(!jit_rt_put_prop(0, "programmer", 1, 1, TYPE_INT, &error)
	  && error == E_PERM,
	  "non-wizard changed programmer flag");
    check(jit_rt_put_prop(0, "programmer", 2, 1, TYPE_INT, &error) == 1,
	  "wizard could not set programmer flag");
    hir_test_set_builtin_property(BP_WIZARD);
    check(!jit_rt_put_prop(0, "wizard", 1, 1, TYPE_INT, &error)
	  && error == E_PERM,
	  "non-wizard changed wizard flag");
    check(jit_rt_put_prop(2, "wizard", 2, 0, TYPE_INT, &error) == -1,
	  "unchanged wizard flag did not use canonical fallback");
    check(jit_rt_put_prop(2, "wizard", 2, 1, TYPE_INT, &error) == 1,
	  "wizard could not preserve wizard flag");
    hir_test_set_builtin_property(BP_R);
    check(!jit_rt_put_prop(0, "r", 1, 1, TYPE_INT, &error)
	  && error == E_PERM,
	  "non-owner changed a permission flag");
    check(jit_rt_put_prop(0, "r", 2, 1, TYPE_INT, &error) == 1,
	  "wizard could not set a permission flag");
    hir_test_set_builtin_property(BP_LOCATION);
    check(!jit_rt_put_prop(0, "location", 2, 1, TYPE_OBJ, &error)
	  && error == E_PERM,
	  "built-in location write was not rejected");
    hir_test_set_builtin_property((enum bi_prop) 99);
    check(jit_rt_put_prop(0, "unknown", 2, 1, TYPE_INT, &error) == -1,
	  "unknown built-in property did not use canonical fallback");
    hir_test_set_builtin_property(BP_NONE);
    hir_test_reset_property();
}

static void
test_perf_map_and_manual_rotation(void)
{
    JITProgram *program = arithmetic_program();
    JITPoolPolicyStats policy;
    char path[128];

    jit_program_note_location(program, 42, 7);
    check(jit_program_compile(program),
	  "perf-map test program did not compile");
    check(jit_perf_map_start() && jit_perf_map_active(),
	  "perf map did not start");
    check(jit_perf_map_start(), "starting an active perf map failed");
    snprintf(path, sizeof(path), "%s", jit_perf_map_path());
    check(path[0] != '\0', "active perf map has no path");
    jit_perf_map_stop();
    check(!jit_perf_map_active(), "perf map did not stop");
    jit_perf_map_stop();
    if (path[0])
	remove(path);

    jit_pool_request_rotation();
    jit_pool_policy_stats(&policy);
    check(policy.rotation_pending,
	  "manual pool rotation request was not recorded");
    jit_pool_maintain();
    jit_pool_policy_stats(&policy);
    check(!policy.rotation_pending,
	  "manual pool rotation request was not completed");
    jit_program_free(program);
}

static void
test_full_metadata_accounting_and_free(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *instr = instruction(HIR_TAC_PARALLEL_COPY);
    JITCopy *copy = allocate(sizeof(JITCopy));
    JITDeoptMap *map;
    JITProgramStats stats;

    program->num_values = 4;
    program->num_vars = 1;
    program->num_blocks = 1;
    program->num_resume_anchors = 1;
    program->num_reconstruction_states = 1;
    program->reconstruction_states = allocate(sizeof(JITReconstructionState));
    program->reconstruction_states[0].representative_map = 0;
    program->num_status_locations = 1;
    program->status_locations = allocate(sizeof(JITSourceLocation));
    program->value_types = allocate(sizeof(int16_t) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_constant_bits = allocate((program->num_values + 7) / 8);
    program->num_constant_values = 1;
    program->constant_value_ids = allocate(sizeof(uint16_t));
    program->value_constants = allocate(sizeof(Num));
    program->value_tag_slots = allocate(sizeof(uint16_t) * program->num_values);
    program->value_ownership = allocate(program->num_values);
    program->value_owner_root = allocate(sizeof(int) * program->num_values);
    program->value_use_counts = allocate(sizeof(unsigned) * program->num_values);
    program->value_escape_flags = allocate(program->num_values);
    program->value_owned_slots = allocate(sizeof(int) * program->num_values);
    program->value_is_int_list = allocate(program->num_values);
    program->num_borrowed_locals = 1;
    program->borrowed_local_slots = allocate(sizeof(int));
    program->usage = allocate(sizeof(JITProgramUsage));
    add_entry_deopt_map(program);
    map = &program->deopt_maps[0];
    map->num_locals = 1;
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
    map->num_tagged_values = 1;
    map->tagged_values = allocate(sizeof(int));
    map->tagged_values[0] = 1;
    map->stack_depth = 1;
    map->stack_values = allocate(sizeof(int));
    map->stack_values[0] = 1;
    map->stack_types = allocate(sizeof(var_type));
    map->stack_types[0] = TYPE_INT;
    map->stack_slots = allocate(sizeof(ResumeStackSlot));
    map->stack_slots[0].kind = RSS_VALUE;
    map->local_owner_slots = allocate(sizeof(int));
    map->stack_owner_slots = allocate(sizeof(int));
    map->stack_boundary_ownership = allocate(1);
    map->native_resume = allocate(sizeof(JITNativeResume));
    map->native_resume->num_values = 1;
    map->native_resume->values = allocate(sizeof(JITResumeValue));
    map->native_resume->num_literals = 1;
    map->native_resume->literals = allocate(sizeof(JITResumeLiteral));
    block->id = 1;
    block->first = block->last = instr;
    copy->dst = 2;
    copy->src = 1;
    instr->copies = copy;
    program->blocks = program->last_block = block;
    program->retained_constants = instruction(HIR_TAC_CONST);

    jit_program_stats(program, &stats);
    check(stats.metadata_bytes > sizeof(*program)
	  && jit_program_bytes(program) == (int) stats.accounted_bytes,
	  "complete JIT metadata was not included in server accounting");
    jit_program_free(program);
    jit_program_free(0);
}

static void
test_suspend_zero_detection(void)
{
    JITProgram *list_program = builtin_call_program(11);
    Var env[1];
    Var result;
    Var deopt_stack[1];
    JITDeoptState deopt;
    JITContinuationFrame *continuation = 0;
    int ticks = 10;
    int timed_out = 0;
    enum error error = E_NONE;

    list_program->deopt_maps[1].builtin_args = -1;
    list_program->usage = allocate(sizeof(JITProgramUsage));
    env[0] = new_list(1);
    env[0].v.list[1].type = TYPE_INT;
    env[0].v.list[1].v.num = 0;
    check((jit_program_execute)(list_program, env, &result, &ticks,
			      &timed_out, &error, 0, &deopt, deopt_stack,
			      0, -1, 0, &continuation)
	  == JIT_RUN_CALL_VERB && deopt.boundary == JIT_BOUNDARY_SUSPEND_ZERO,
	  "suspend({0}) was not recognized as a fast suspension");
    check(continuation != 0, "suspend({0}) did not capture a continuation");
    check(list_program->usage->continuation_captures == 1
	  && list_program->usage->continuation_fast_suspends == 1,
	  "suspend({0}) did not update fast-suspension statistics");
    jit_continuation_free(continuation);
    continuation = 0;
    free_var(env[0]);
    jit_program_free(list_program);

    list_program = owned_builtin_call_program(11);
    list_program->deopt_maps[1].builtin_args = -1;
    list_program->deopt_maps[1].local_values[0].value = 1;
    list_program->deopt_maps[1].local_owner_slots[0] = -1;
    list_program->value_types[1] = TYPE_INT;
    list_program->blocks->first->literal_type = TYPE_INT;
    jit_analyze_owned_last_uses(list_program);
    env[0].type = TYPE_INT;
    env[0].v.num = 0;
    check((jit_program_execute)(list_program, env, &result, &ticks,
			      &timed_out, &error, 0, &deopt, deopt_stack,
			      0, -1, 0, &continuation)
	  == JIT_RUN_CALL_VERB && deopt.boundary == JIT_BOUNDARY_SUSPEND_ZERO,
	  "owned suspend({0}) was not recognized as a fast suspension");
    check(continuation != 0
	  && list_program->deopt_maps[1].stack_boundary_ownership[0]
	     == JIT_BOUNDARY_VALUE_MOVED_OWNER,
	  "fast suspension did not consume its owned argument list");
    jit_continuation_free(continuation);
    jit_program_free(list_program);
}

static void
test_suspend_zero_validation_matrix(void)
{
    JITProgram *program = builtin_call_program(11);
    JITDeoptMap *map = &program->deopt_maps[1];
    Num raw[3] = {0, 0, 0};
    Var args = new_list(1);
    Var home;
    unsigned char home_state = JIT_HOME_OWNED;

    args.v.list[1].type = TYPE_INT;
    args.v.list[1].v.num = 0;
    map->builtin_args = 1;
    map->stack_types[0] = TYPE_INT;
    check(jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "direct suspend(0) was not recognized");
    raw[1] = 1;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "direct suspend(1) was recognized as suspend(0)");
    raw[1] = 0;
    map->stack_types[0] = TYPE_STR;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "string suspend argument was recognized as zero");
    map->stack_types[0] = TYPE_INT;

    map->builtin_args = -1;
    map->stack_types[0] = TYPE_LIST;
    raw[1] = (Num) (intptr_t) args.v.list;
    check(jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "direct suspend({0}) was not recognized");
    raw[1] = 0;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "null argument list was recognized as suspend({0})");
    raw[1] = (Num) (intptr_t) args.v.list;
    args.v.list[0].v.num = 2;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "two-element list was recognized as suspend({0})");
    args.v.list[0].v.num = 1;
    args.v.list[1].type = TYPE_STR;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "string list element was recognized as suspend({0})");
    args.v.list[1].type = TYPE_INT;
    args.v.list[1].v.num = 1;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "nonzero list element was recognized as suspend({0})");
    args.v.list[1].v.num = 0;

    map->stack_owner_slots = allocate(sizeof(int));
    map->stack_owner_slots[0] = 0;
    program->num_owned_slots = 1;
    home.type = TYPE_INT;
    home.v.num = 0;
    map->builtin_args = 1;
    check(jit_test_deopt_map_is_suspend_zero(program, map, raw, &home,
	&home_state), "owner-backed suspend(0) was not recognized");
    home.v.num = 1;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, &home,
	&home_state), "owner-backed suspend(1) was recognized as zero");
    home = args;
    map->builtin_args = -1;
    check(jit_test_deopt_map_is_suspend_zero(program, map, raw, &home,
	&home_state), "owner-backed suspend({0}) was not recognized");
    map->builtin_args = 0;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, &home,
	&home_state), "zero-arity suspend was recognized as suspend(0)");

    map->stack_owner_slots[0] = -1;
    map->reason = JIT_DEOPT_TYPE_GUARD;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "non-builtin boundary was recognized as suspend(0)");
    map->reason = JIT_DEOPT_BUILTIN_CALL;
    map->builtin_func = 10;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "time() boundary was recognized as suspend(0)");
    map->builtin_func = 11;
    map->stack_depth = 0;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "empty stack was recognized as suspend(0)");
    map->stack_depth = 1;
    map->stack_slots = allocate(sizeof(ResumeStackSlot));
    map->stack_slots[0].kind = RSS_CATCH;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "catch marker was recognized as a suspend argument");
    map->stack_slots[0].kind = RSS_VALUE;
    map->stack_values[0] = 0;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "zero value id was recognized as a suspend argument");
    map->stack_values[0] = program->num_values;
    check(!jit_test_deopt_map_is_suspend_zero(program, map, raw, 0, 0),
	  "excessive value id was recognized as a suspend argument");

    free_var(args);
    jit_program_free(program);
}

static void
test_native_resume_constant_lowering(void)
{
    static const var_type types[] = {TYPE_INT, TYPE_FLOAT, TYPE_STR};
    unsigned i;

    for (i = 0; i < sizeof(types) / sizeof(types[0]); i++) {
	JITProgram *program = builtin_call_program(11);
	JITDeoptMap *map = &program->deopt_maps[1];
	JITNativeResume *resume = map->native_resume;
	Var literal;

	resume->values[0].source = JIT_RESUME_CONSTANT;
	resume->values[0].index = 0;
	resume->num_literals = 1;
	resume->literals = allocate(sizeof(JITResumeLiteral));
	literal.type = types[i];
	if (types[i] == TYPE_FLOAT) {
	    FlNum value = 1.5;

	    memcpy(&resume->literals[0].literal, &value, sizeof(value));
	    program->value_types[2] = TYPE_FLOAT;
	    program->value_is_tagged[2] = 0;
	} else if (types[i] == TYPE_STR) {
	    literal.v.str = str_dup("constant resume");
	    resume->literals[0].literal = (Num) (intptr_t) literal.v.str;
	    program->value_types[2] = TYPE_ANY;
	    program->value_is_tagged[2] = 1;
	} else {
	    literal.v.num = 42;
	    resume->literals[0].literal = literal.v.num;
	    program->value_types[2] = TYPE_INT;
	    program->value_is_tagged[2] = 0;
	}
	resume->literals[0].literal_type = types[i];
	check(jit_program_compile(program),
	      "native constant resume value did not compile");
	jit_program_free(program);
	if (types[i] == TYPE_STR)
	    free_var(literal);
    }
}

static void
test_native_frame_verifier_rejections(void)
{
    JITProgram *program = builtin_call_program(17);
    JITExecutionContext context;
    JITNativeFrame root;
    JITNativeFrame other;
    Var env[1];
    Var home;
    unsigned capacity = 0;
    unsigned char home_state = JIT_HOME_EMPTY;
    int ticks = 10;
    int timed_out = 0;
    enum error error = E_NONE;

    memset(&other, 0, sizeof(other));
    env[0] = new_list(0);
    jit_execution_context_init(&context, &root, program, env, 0, 1, 4,
	&ticks, &timed_out, &error, -1);
    check(jit_native_frame_verify(&context, &root),
	  "verifier rejection fixture is not initially valid");
    check(!jit_native_frame_verify(0, &root)
	  && !jit_native_frame_verify(&context, 0),
	  "native verifier accepted a missing context or frame");

    root.context = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted the wrong context");
    root.context = &context;
    context.root_frame = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a missing root");
    context.root_frame = &root;
    context.current_frame = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a missing current frame");
    context.current_frame = &root;
    root.program = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a missing program");
    root.program = program;

    context.canonical_depth = 5;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted excessive canonical depth");
    context.canonical_depth = 1;
    context.native_depth = 5;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted excessive native depth");
    context.native_depth = 0;
    context.canonical_depth = 4;
    context.native_depth = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted excessive combined depth");
    context.canonical_depth = 1;
    context.native_depth = 0;

    root.kind = JIT_FRAME_COMPACT;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a compact root");
    root.kind = JIT_FRAME_ROOT_OVERLAY;
    root.caller = &other;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a root caller");
    root.caller = 0;
    root.canonical_index++;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted the wrong root activation");
    root.canonical_index--;
    root.callee = &other;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a mismatched callee");
    root.callee = 0;
    root.state = JIT_FRAME_SUSPENDED;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a suspended current frame");
    root.state = JIT_FRAME_RUNNING;

    root.canonical_index = context.activation_limit;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an out-of-range activation");
    root.canonical_index = context.root_activation_index;
    root.entry_map = -2;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an invalid entry map");
    root.entry_map = -1;
    root.current_map = -2;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an invalid current map");
    root.current_map = -1;
    root.entry_map = program->num_deopt_maps;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an out-of-range entry map");
    root.entry_map = -1;
    root.current_map = program->num_deopt_maps;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an out-of-range current map");
    root.current_map = -1;

    root.owns_boundary_stack = 1;
    root.boundary_depth = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a missing boundary stack");
    root.boundary_depth = 0;
    root.boundary_map = -1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a negative boundary map");
    root.boundary_map = program->num_deopt_maps;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an out-of-range boundary map");
    root.boundary_map = 1;
    root.current_map = -1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted mismatched boundary maps");
    root.owns_boundary_stack = 0;
    root.boundary_map = 0;
    root.boundary_stack = &home;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an unowned boundary stack");
    root.boundary_stack = 0;
    root.boundary_depth = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted unowned boundary depth");
    root.boundary_depth = 0;
    root.boundary_map = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an unowned boundary map");
    root.boundary_map = 0;

    root.owns_runtime = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted missing owned runtime");
    root.runtime_storage = &home;
    root.runtime_bytes = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted unaccounted owned runtime");
    root.runtime_storage = 0;
    root.runtime_bytes = 0;
    root.owns_runtime = 0;
    root.num_homes = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted missing home arrays");
    root.homes = &home;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted missing home state and capacity arrays");
    root.home_states = &home_state;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a missing home capacity array");
    root.home_capacities = &capacity;
    home.type = TYPE_INT;
    home.v.num = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a value in an empty home");
    home.type = TYPE_NONE;
    home_state = JIT_HOME_OWNED;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an empty owned home");
    home_state = 99;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted an unknown home state");
    root.num_homes = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted home arrays without homes");
    root.homes = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted state and capacity arrays without homes");
    root.home_states = 0;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted a capacity array without homes");
    root.home_capacities = 0;

    root.owns_boundary_stack = 1;
    root.boundary_stack = &home;
    root.boundary_depth = 1;
    root.boundary_map = 1;
    root.current_map = 1;
    check(!jit_native_frame_verify(&context, &root),
	  "native verifier accepted unaccounted boundary storage");
    root.owns_boundary_stack = 0;
    root.boundary_stack = 0;
    root.boundary_depth = 0;
    root.boundary_map = 0;
    root.current_map = -1;

    {
	JITNativeFrame child;
	JITCallerResume resume;
	Var returned;

	home.type = TYPE_NONE;
	home.v.num = 0;
	home_state = JIT_HOME_EMPTY;
	root.homes = &home;
	root.num_homes = 1;
	root.home_states = &home_state;
	root.home_capacities = &capacity;
	memset(&resume, 0, sizeof(resume));
	resume.caller = &root;
	resume.map_id = 1;
	resume.result_home = 0;
	resume.state = JIT_RESUME_PREPARING;
	check(jit_execution_context_push_compact(&context, &child, program, env,
	    &resume, -1) && jit_native_frame_verify(&context, &root)
	    && jit_native_frame_verify(&context, &child),
	    "compact verifier rejection fixture is not initially valid");

	child.owns_invocation = 1;
	child.bytecode_program = (Program *) &context;
	child.verb = "test";
	child.verbname = "test";
	check(jit_native_frame_verify(&context, &child),
	      "owned invocation verifier fixture is not initially valid");
	child.bytecode_program = 0;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted a missing invocation program");
	child.bytecode_program = (Program *) &context;
	child.env = 0;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted a missing invocation environment");
	child.env = env;
	child.verb = 0;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted a missing invocation verb");
	child.verb = "test";
	child.verbname = 0;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted a missing invocation verb name");
	child.verbname = "test";
	child.owns_invocation = 0;
	child.bytecode_program = 0;
	child.verb = 0;
	child.verbname = 0;

	resume.caller = &other;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted the wrong incoming caller");
	resume.caller = &root;
	resume.state = JIT_RESUME_PREPARING;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted an undispatched incoming resume");
	resume.state = JIT_RESUME_DISPATCHED;
	resume.map_id = 0;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted a zero incoming map");
	resume.map_id = program->num_deopt_maps;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted an out-of-range incoming map");
	resume.map_id = 1;
	resume.result_home = 1;
	check(!jit_native_frame_verify(&context, &child),
	      "native verifier accepted an out-of-range incoming result home");
	resume.result_home = 0;

	resume.caller = &other;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted the wrong outgoing caller");
	resume.caller = &root;
	resume.state = JIT_RESUME_PREPARING;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted an undispatched outgoing resume");
	resume.state = JIT_RESUME_DISPATCHED;
	root.callee = 0;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted a missing outgoing callee");
	root.callee = &child;
	child.incoming = 0;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted mismatched outgoing linkage");
	child.incoming = &resume;
	resume.map_id = 0;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted a zero outgoing map");
	resume.map_id = program->num_deopt_maps;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted an out-of-range outgoing map");
	resume.map_id = 1;
	resume.result_home = 1;
	check(!jit_native_frame_verify(&context, &root),
	      "native verifier accepted an out-of-range outgoing result home");
	resume.result_home = 0;

	returned.type = TYPE_INT;
	returned.v.num = 9;
	check(jit_execution_context_return_compact(&context, &child, &returned),
	      "compact verifier rejection child did not return");
	check(jit_native_frame_home_take(&root, 0, &returned),
	      "compact verifier rejection result was not transferred");
	free_var(returned);
	root.homes = 0;
	root.num_homes = 0;
	root.home_states = 0;
	root.home_capacities = 0;
    }

    check(jit_execution_context_finish(&context, &root),
	  "verifier rejection context did not finish");
    free_var(env[0]);
    jit_program_free(program);
}

static void
test_owned_call_boundary_lowering(void)
{
    JITProgram *builtin = builtin_call_program(17);
    JITProgram *verb = call_verb_program();
    JITDeoptMap *builtin_map = &builtin->deopt_maps[1];
    JITDeoptMap *verb_map = &verb->deopt_maps[1];

    builtin->value_ownership = allocate(builtin->num_values);
    builtin->value_owned_slots = allocate(sizeof(int) * builtin->num_values);
    memset(builtin->value_owned_slots, -1,
	   sizeof(int) * builtin->num_values);
    builtin->value_ownership[1] = JIT_OWNERSHIP_OWNED;
    builtin->value_owned_slots[1] = 0;
    builtin->num_owned_slots = 1;
    builtin_map->num_locals = 0;
    builtin_map->stack_owner_slots = allocate(sizeof(int));
    builtin_map->stack_owner_slots[0] = 0;
    jit_analyze_owned_last_uses(builtin);
    check(builtin_map->stack_boundary_ownership
	  && builtin_map->stack_boundary_ownership[0]
	     == JIT_BOUNDARY_VALUE_MOVED_OWNER,
	  "owned built-in argument was not moved from its owner home");
    check(jit_program_compile(builtin),
	  "owned built-in boundary did not compile");

    verb->value_ownership = allocate(verb->num_values);
    verb->value_owned_slots = allocate(sizeof(int) * verb->num_values);
    memset(verb->value_owned_slots, -1, sizeof(int) * verb->num_values);
    verb->value_ownership[3] = JIT_OWNERSHIP_OWNED;
    verb->value_owned_slots[3] = 0;
    verb->num_owned_slots = 1;
    verb_map->num_locals = 2;
    verb_map->stack_owner_slots = allocate(sizeof(int) * 3);
    verb_map->stack_owner_slots[0] = -1;
    verb_map->stack_owner_slots[1] = -1;
    verb_map->stack_owner_slots[2] = 0;
    jit_analyze_owned_last_uses(verb);
    check(verb_map->stack_boundary_ownership
	  && verb_map->stack_boundary_ownership[2]
	     == JIT_BOUNDARY_VALUE_RELEASE_AFTER_RESUME,
	  "owned verb argument list was not deferred until resume");
    check(jit_program_compile(verb),
	  "owned verb-call boundary did not compile");

    jit_program_free(verb);
    jit_program_free(builtin);
}

static void
test_boundary_value_ownership_transfer(void)
{
    static const JITBoundaryValueOwnership owner_modes[] = {
	JIT_BOUNDARY_VALUE_RETAINED,
	JIT_BOUNDARY_VALUE_RELEASE_AFTER_RESUME,
	JIT_BOUNDARY_VALUE_MOVED_OWNER
    };
    JITProgram *program = new_jit_program();
    unsigned i;

    program->num_owned_slots = 1;
    program->num_values = 2;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_types[1] = TYPE_STR;
    for (i = 0; i < sizeof(owner_modes) / sizeof(owner_modes[0]); i++) {
	Var homes[1];
	unsigned char states[1] = {JIT_HOME_OWNED};
	Var taken;

	homes[0].type = TYPE_STR;
	homes[0].v.str = str_dup("owner boundary");
	taken = jit_test_take_boundary_stack_value(program, owner_modes[i], 0,
	    TYPE_STR, 1, 0, homes, states);
	check(taken.type == TYPE_STR
	      && !strcmp(taken.v.str, "owner boundary"),
	      "owner-backed boundary produced the wrong value");
	if (owner_modes[i] == JIT_BOUNDARY_VALUE_MOVED_OWNER) {
	    check(homes[0].type == TYPE_NONE && states[0] == JIT_HOME_EMPTY,
		  "moved owner boundary did not empty its home");
	} else {
	    check(homes[0].type == TYPE_STR && states[0] == JIT_HOME_OWNED
		  && homes[0].v.str == taken.v.str,
		  "borrowed owner boundary changed its home");
	    free_var(homes[0]);
	}
	free_var(taken);
    }
#ifdef WAIF_CORE
    for (i = 0; i < sizeof(owner_modes) / sizeof(owner_modes[0]); i++) {
	Var homes[1];
	unsigned char states[1] = {JIT_HOME_OWNED};
	Var taken;

	homes[0] = hir_test_new_waif();
	taken = jit_test_take_boundary_stack_value(program, owner_modes[i], 0,
	    TYPE_WAIF, 1, 0, homes, states);
	check(taken.type == TYPE_WAIF,
	      "owner-backed waif boundary produced the wrong type");
	if (owner_modes[i] == JIT_BOUNDARY_VALUE_MOVED_OWNER) {
	    check(homes[0].type == TYPE_NONE && states[0] == JIT_HOME_EMPTY
		  && var_refcount(taken) == 1,
		  "moved waif boundary did not transfer its owner reference");
	} else {
	    check(homes[0].type == TYPE_WAIF && states[0] == JIT_HOME_OWNED
		  && homes[0].v.waif == taken.v.waif
		  && var_refcount(taken) == 2,
		  "borrowed waif boundary did not retain its owner reference");
	    free_var(homes[0]);
	}
	free_var(taken);
    }
    {
	Num raw[2] = {0, 0};
	Var original = hir_test_new_waif();
	Var taken;

	raw[1] = (Num) (intptr_t) original.v.waif;
	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_RETAINED, -1, TYPE_WAIF, 1, raw, 0, 0);
	check(taken.type == TYPE_WAIF && taken.v.waif == original.v.waif
	      && var_refcount(taken) == 2,
	      "retained raw waif boundary did not retain its source");
	free_var(taken);
	free_var(original);

	original = hir_test_new_waif();
	raw[1] = (Num) (intptr_t) original.v.waif;
	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_MOVED_RAW, -1, TYPE_WAIF, 1, raw, 0, 0);
	check(taken.type == TYPE_WAIF && taken.v.waif == original.v.waif
	      && raw[1] == 0 && var_refcount(taken) == 1,
	      "moved raw waif boundary did not consume its source");
	original.type = TYPE_NONE;
	free_var(taken);
    }
#endif
    {
	Num raw[2] = {0, 0};
	Var original;
	Var taken;

	original.type = TYPE_STR;
	original.v.str = str_dup("retained raw boundary");
	raw[1] = (Num) (intptr_t) original.v.str;
	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_RETAINED, -1, TYPE_STR, 1, raw, 0, 0);
	check(taken.type == TYPE_STR && taken.v.str == original.v.str
	      && raw[1] != 0,
	      "retained raw boundary did not retain its source");
	free_var(taken);
	free_var(original);
    }
    {
	Num raw[2] = {0, 0};
	const char *string = str_dup("moved raw boundary");
	Var taken;

	raw[1] = (Num) (intptr_t) string;
	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_MOVED_RAW, -1, TYPE_STR, 1, raw, 0, 0);
	check(taken.type == TYPE_STR
	      && !strcmp(taken.v.str, "moved raw boundary") && raw[1] == 0,
	      "moved raw boundary did not consume its source");
	free_var(taken);
    }
    {
	Num raw[2] = {0, 0};
	Var taken;

	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_RETAINED, -1, TYPE_NONE, 1, raw, 0, 0);
	check(taken.type == TYPE_NONE,
	      "none boundary value was not preserved");
	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_RETAINED, -1, TYPE_STR, 1, raw, 0, 0);
	check(taken.type == TYPE_NONE,
	      "null string boundary value was materialized");
	program->value_types[1] = TYPE_LIST;
	taken = jit_test_take_boundary_stack_value(program,
	    JIT_BOUNDARY_VALUE_RETAINED, -1, TYPE_LIST, 1, raw, 0, 0);
	check(taken.type == TYPE_NONE,
	      "null list boundary value was materialized");
    }
    jit_program_free(program);
}

static void
test_guard_actual_type_sources(void)
{
    JITProgram *program = new_jit_program();
    JITDeoptMap map;
    JITLocalValue local_value;
    Var env[1];
    Var homes[1];
    unsigned char states[1] = {JIT_HOME_OWNED};
    int local_owners[1] = {0};
    int stack_values[1] = {1};
    int stack_owners[1] = {0};
    Num raw[4] = {0, 0, 0, 0};

    memset(&map, 0, sizeof(map));
    program->num_vars = 1;
    program->num_values = 3;
    program->num_owned_slots = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = TYPE_ERR;
    map.guard_expected[0] = JIT_TYPE_MASK(TYPE_INT);
    map.guard_value[0] = 1;
    map.guard_local[0] = 0;
    env[0].type = TYPE_OBJ;
    env[0].v.obj = 17;
    check(jit_test_guard_actual_type(program, &map, env, raw, homes,
	states, 0) == TYPE_OBJ,
	  "guard did not use its environment-local runtime type");

    map.guard_local[0] = -1;
    map.num_locals = 1;
    map.num_local_values = 1;
    local_value.slot = 0;
    local_value.value = 1;
    map.local_values = &local_value;
    map.local_owner_slots = local_owners;
    homes[0].type = TYPE_STR;
    homes[0].v.str = str_dup("guard owner");
    check(jit_test_guard_actual_type(program, &map, env, raw, homes,
	states, 0) == TYPE_STR,
	  "guard did not use its local owner-home runtime type");
    free_var(homes[0]);

    local_owners[0] = -1;
    map.stack_depth = 1;
    map.stack_values = stack_values;
    map.stack_owner_slots = stack_owners;
    homes[0] = new_list(0);
    check(jit_test_guard_actual_type(program, &map, env, raw, homes,
	states, 0) == TYPE_LIST,
	  "guard did not use its stack owner-home runtime type");
    free_var(homes[0]);

    stack_owners[0] = -1;
    program->value_is_tagged[1] = 1;
    use_compact_tag_slots(program);
    raw[program->num_values] = TYPE_FLOAT;
    check(jit_test_guard_actual_type(program, &map, env, raw, homes,
	states, 0) == TYPE_FLOAT,
	  "guard did not use its tagged runtime type");

    program->value_is_tagged[1] = 0;
    check(jit_test_guard_actual_type(program, &map, env, raw, homes,
	states, 0) == TYPE_ERR,
	  "guard did not use its statically known type");
    map.guard_expected[0] = 0;
    check(jit_test_guard_actual_type(program, &map, env, raw, homes,
	states, 0) == TYPE_NONE,
	  "absent guard reported an actual type");

    jit_program_free(program);
}

static void
test_typed_deopt_materialization(void)
{
    const var_type types[] = { TYPE_ERR, TYPE_OBJ, TYPE_FLOAT, TYPE_STR };
    Var inputs[4];
    int i;

    inputs[0].type = TYPE_ERR;
    inputs[0].v.err = E_INVARG;
    inputs[1].type = TYPE_OBJ;
    inputs[1].v.obj = 42;
    inputs[2].type = TYPE_FLOAT;
    inputs[2].v.fnum = box_fl(2.5);
    inputs[3].type = TYPE_STR;
    inputs[3].v.str = str_dup("tagged deopt");
    for (i = 0; i < 4; i++) {
	JITProgram *program = typed_deopt_program(types[i], i == 3);
	JITDeoptState deopt;
	Var stack[1];
	Var result;
	int ticks = 10;
	int timed_out = 0;
	enum error error = E_NONE;

	check(jit_program_execute(program, &inputs[i], &result, &ticks,
				  &timed_out, &error, 0, &deopt, stack)
	      == JIT_RUN_FALLBACK,
	      "typed deopt program did not request fallback");
	check(stack[0].type == types[i] && deopt.guard_actual[0] == types[i],
	      "typed deopt reconstructed the wrong value or guard type");
	check(inputs[i].type == types[i],
	      "typed deopt reconstructed the wrong local type");
	if (types[i] == TYPE_ERR)
	    check(stack[0].v.err == E_INVARG,
		  "typed error deopt reconstructed the wrong error");
	else if (types[i] == TYPE_OBJ)
	    check(stack[0].v.obj == 42,
		  "typed object deopt reconstructed the wrong object");
	else if (types[i] == TYPE_FLOAT)
	    check(fl_unbox(stack[0].v.fnum) == 2.5,
		  "typed float deopt reconstructed the wrong float");
	else
	    check(!strcmp(stack[0].v.str, "tagged deopt"),
		  "tagged string deopt reconstructed the wrong string");
	free_var(stack[0]);
	jit_program_free(program);
    }
    for (i = 0; i < 4; i++)
	free_var(inputs[i]);
}

static void
test_mir_allocator(void)
{
    check(jit_test_mir_allocator(), "MIR allocator lifecycle test failed");
}

static void
test_null_jit_api_contracts(void)
{
    JITNativeFrame frame;
    JITExecutionContext context;
    JITContinuationFrame continuation;
    JITProgramStats stats;
    activation owner;
    PreparedVerbCall prepared;
    Var value;

    memset(&frame, 0, sizeof(frame));
    memset(&context, 0, sizeof(context));
    memset(&continuation, 0, sizeof(continuation));
    memset(&owner, 0, sizeof(owner));
    memset(&prepared, 0, sizeof(prepared));
    value.type = TYPE_INT;
    value.v.num = 1;

    check(!jit_native_chain_promotion_count(0)
	  && !jit_native_chain_promotion_frame(0, 0)
	  && !jit_native_chain_commit_promotion(0, record_promotion, 0),
	  "null native promotion accessors did not reject input");
    jit_native_chain_discard_promotion(0);
    check(!jit_execution_context_finish(0, &frame)
	  && !jit_execution_context_finish(&context, 0),
	  "null execution context finish did not reject input");
    check(!jit_native_frame_bind_activation(0, &owner)
	  && !jit_native_frame_bind_activation(&frame, 0),
	  "null activation binding did not reject input");
    check(!jit_native_frame_copy_invocation(0, &owner)
	  && !jit_native_frame_copy_invocation(&frame, 0),
	  "null invocation copy did not reject input");
    check(!jit_native_frame_take_prepared_invocation(0, &prepared)
	  && !jit_native_frame_take_prepared_invocation(&frame, 0),
	  "null prepared invocation did not reject input");
    jit_native_frame_release_invocation(0);
    jit_native_frame_release_invocation(&frame);
    jit_native_frame_mark_runtime_owned(0);
    check(!jit_native_frame_adopt_continuation_runtime(0, &continuation)
	  && !jit_native_frame_adopt_continuation_runtime(&frame, 0),
	  "null continuation runtime adoption did not reject input");
    check(!jit_native_frame_return_continuation_runtime(0, &continuation)
	  && !jit_native_frame_return_continuation_runtime(&frame, 0),
	  "null continuation runtime return did not reject input");
    check(!jit_native_frame_continuation_matches(0, 1)
	  && !jit_native_frame_continuation_matches(&frame, 1),
	  "null continuation matching did not reject input");
    jit_native_frame_release_runtime(0);
    jit_native_frame_release_runtime(&frame);
    check(!jit_native_frame_capture_boundary(0, &value, 1, 1),
	  "null boundary capture did not reject input");
    jit_native_frame_release_boundary(0);
    jit_native_frame_release_boundary(&frame);
    check(!jit_native_frame_home_move(0, 0, &value)
	  && !jit_native_frame_home_move(&frame, 0, 0)
	  && !jit_native_frame_home_take(0, 0, &value)
	  && !jit_native_frame_home_take(&frame, 0, 0),
	  "null owner-home operations did not reject input");
    check(!jit_native_frame_prepare_activation(0, &owner, 1, 0)
	  && !jit_native_frame_prepare_activation(&frame, 0, 1, 0),
	  "null activation preparation did not reject input");

    jit_program_stats(0, &stats);
    check(stats.accounted_bytes == 0,
	  "null program statistics were not empty");
    jit_continuation_attach(0, &owner);
    jit_continuation_attach(&continuation, 0);
    jit_continuation_relocate(0, &owner);
    jit_continuation_relocate(&continuation, 0);
    jit_continuation_mark_dispatched(0);
    check(!jit_continuation_is_dispatched(0),
	  "null continuation was reported dispatched");
    jit_continuation_set_result(0, value);
    check(jit_continuation_materialize(0)
	  && jit_continuation_materialize_boundary(0, &value, 1)
	  && jit_continuation_materialize(&owner)
	  && jit_continuation_materialize_boundary(&owner, &value, 1),
	  "empty continuation materialization was not a no-op");
    jit_continuation_free(0);
}

static void
test_entry_activation_validation(void)
{
    JITProgram *program = builtin_call_program(11);
    JITNativeFrame frame;
    JITContinuationFrame continuation;
    activation owner;
    Program bytecode;
    Var env[1];
    Var stack[6];
    Var value;

    memset(&frame, 0, sizeof(frame));
    memset(&continuation, 0, sizeof(continuation));
    memset(&owner, 0, sizeof(owner));
    memset(&bytecode, 0, sizeof(bytecode));
    frame.program = program;
    owner.prog = &bytecode;
    owner.rt_env = env;
    owner.base_rt_stack = owner.top_rt_stack = &stack[2];
    owner.rt_stack_size = 2;
    bytecode.num_var_names = 1;

    check(jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "valid entry activation was rejected");
    check(owner.pc == program->deopt_maps[0].bytecode_pc
	  && owner.error_pc == program->deopt_maps[0].error_pc,
	  "entry activation did not restore its PCs");
    owner.jit_continuation = &continuation;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation with an existing continuation was accepted");
    owner.jit_continuation = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, -1, 0)
	  && !jit_native_frame_prepare_activation(&frame, &owner,
	      program->num_deopt_maps, 0),
	  "invalid activation map was accepted");
    frame.program = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation without a program was accepted");
    frame.program = program;

    program->deopt_maps[0].num_locals = 1;
    owner.prog = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation locals without bytecode were accepted");
    owner.prog = &bytecode;
    owner.rt_env = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation locals without an environment were accepted");
    owner.rt_env = env;
    bytecode.num_var_names = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation with too few variables was accepted");
    bytecode.num_var_names = 1;
    program->deopt_maps[0].num_locals = 0;

    owner.rt_stack_size = -1;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation with negative stack size was accepted");
    owner.rt_stack_size = 2;
    owner.base_rt_stack = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation without a stack base was accepted");
    owner.base_rt_stack = &stack[2];
    owner.top_rt_stack = 0;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation without a stack top was accepted");
    owner.top_rt_stack = &stack[1];
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation with stack underflow was accepted");
    owner.top_rt_stack = &stack[5];
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "activation with stack overflow was accepted");
    owner.top_rt_stack = &stack[2];

    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 1),
	  "dispatched entry activation was accepted");
    frame.owns_boundary_stack = 1;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "entry activation with boundary storage was accepted");
    frame.owns_boundary_stack = 0;
    frame.runtime_borrower = &continuation;
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "entry activation with a runtime borrower was accepted");
    frame.runtime_borrower = 0;
    owner.top_rt_stack = &stack[3];
    check(!jit_native_frame_prepare_activation(&frame, &owner, 0, 0),
	  "entry activation with a nonempty stack was accepted");

    owner.top_rt_stack = owner.base_rt_stack;
    value.type = TYPE_STR;
    value.v.str = str_dup("native boundary");
    check(jit_native_frame_capture_boundary(&frame, &value, 1, 1),
	  "native boundary operands were not captured");
    check(jit_native_frame_prepare_activation(&frame, &owner, 1, 0),
	  "owned native boundary was not prepared for interpretation");
    check(owner.top_rt_stack == owner.base_rt_stack + 1
	  && owner.base_rt_stack[0].type == TYPE_STR
	  && !strcmp(owner.base_rt_stack[0].v.str, "native boundary")
	  && owner.pc == 25 && owner.error_pc == 25,
	  "owned native boundary restored the wrong activation");
    free_var(*--owner.top_rt_stack);
    jit_native_frame_release_boundary(&frame);

    jit_program_free(program);
}

static void
test_owned_value_predicates(void)
{
    JITProgram *program = new_jit_program();
    JITBlock *block = allocate(sizeof(JITBlock));
    JITInstruction *definition = instruction(HIR_TAC_BINARY);
    JITInstruction tail;
    unsigned char *ownership;
    unsigned char *tagged;
    unsigned int *uses;
    unsigned char *escapes;
    int *owned_slots;
    int16_t *types;

    memset(&tail, 0, sizeof(tail));
    program->num_values = 4;
    program->num_blocks = 1;
    program->blocks = program->last_block = block;
    block->first = block->last = definition;
    definition->value = 2;
    definition->src1 = 1;
    definition->op = HIR_OP_ADD;
    ownership = program->value_ownership = allocate(4);
    tagged = program->value_is_tagged = allocate(4);
    uses = program->value_use_counts = allocate(sizeof(unsigned int) * 4);
    escapes = program->value_escape_flags = allocate(4);
    owned_slots = program->value_owned_slots = allocate(sizeof(int) * 4);
    types = program->value_types = allocate(sizeof(int16_t) * 4);
    ownership[2] = ownership[3] = JIT_OWNERSHIP_OWNED;
    owned_slots[2] = owned_slots[3] = 0;
    uses[2] = 1;
    types[1] = types[2] = TYPE_STR;

    check(jit_test_value_is_owned_string_result(program, 2),
	  "owned untagged string result was not recognized");
    types[2] = TYPE_INT;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "owned untagged integer was recognized as a string");
    types[2] = TYPE_STR;
    ownership[2] = JIT_OWNERSHIP_BORROWED_LOCAL;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "borrowed string was recognized as owned");
    ownership[2] = JIT_OWNERSHIP_OWNED;
    check(!jit_test_value_is_owned_string_result(program, 0)
	  && !jit_test_value_is_owned_string_result(program, 4),
	  "out-of-range string result was recognized");
    program->value_ownership = 0;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "string result without ownership metadata was recognized");
    program->value_ownership = ownership;
    program->value_types = 0;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "string result without type metadata was recognized");
    program->value_types = types;
    program->value_is_tagged = 0;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "string result without tag metadata was recognized");
    program->value_is_tagged = tagged;

    tagged[2] = 1;
    check(jit_test_value_is_owned_string_result(program, 2),
	  "owned tagged string addition was not recognized");
    definition->op = HIR_OP_INDEX;
    check(jit_test_value_is_owned_string_result(program, 2),
	  "owned tagged string index was not recognized");
    types[1] = TYPE_LIST;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "owned tagged list index was recognized as a string");
    types[1] = TYPE_STR;
    definition->kind = HIR_TAC_RANGE_REF;
    check(jit_test_value_is_owned_string_result(program, 2),
	  "owned tagged string range was not recognized");
    types[1] = TYPE_LIST;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "owned tagged list range was recognized as a string");
    definition->kind = HIR_TAC_CONST;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "owned tagged constant was recognized as a string result");
    block->first = block->last = 0;
    check(!jit_test_value_is_owned_string_result(program, 2),
	  "undefined tagged value was recognized as a string result");
    block->first = block->last = definition;

    definition->kind = HIR_TAC_UNARY;
    definition->op = HIR_OP_MAKE_SINGLETON_LIST;
    uses[2] = 0;
    escapes[2] = JIT_ESCAPE_NONE;
    check(jit_test_value_is_dead_owned_list(program, definition),
	  "dead owned singleton list was not recognized");
    definition->kind = HIR_TAC_BINARY;
    definition->op = HIR_OP_LIST_ADD_TAIL;
    check(jit_test_value_is_dead_owned_list(program, definition),
	  "dead owned list tail was not recognized");
    definition->op = HIR_OP_ADD;
    check(!jit_test_value_is_dead_owned_list(program, definition),
	  "non-list operation was recognized as a dead list");
    definition->op = HIR_OP_LIST_ADD_TAIL;
    uses[2] = 1;
    check(!jit_test_value_is_dead_owned_list(program, definition),
	  "used owned list was recognized as dead");
    uses[2] = 0;
    escapes[2] = JIT_ESCAPE_RETURN;
    check(!jit_test_value_is_dead_owned_list(program, definition),
	  "escaping owned list was recognized as dead");
    escapes[2] = JIT_ESCAPE_NONE;
    ownership[2] = JIT_OWNERSHIP_BORROWED_LOCAL;
    check(!jit_test_value_is_dead_owned_list(program, definition),
	  "borrowed list was recognized as dead and owned");
    ownership[2] = JIT_OWNERSHIP_OWNED;
    definition->value = 0;
    check(!jit_test_value_is_dead_owned_list(program, definition),
	  "out-of-range list value was recognized as dead");
    definition->value = 2;

    tail.kind = HIR_TAC_BINARY;
    tail.op = HIR_OP_LIST_ADD_TAIL;
    tail.src1 = 2;
    tail.value = 3;
    uses[2] = 1;
    check(jit_test_list_tail_consumes_home(program, &tail),
	  "eligible list tail did not consume its owner home");
    owned_slots[3] = 1;
    check(!jit_test_list_tail_consumes_home(program, &tail),
	  "list tail consumed a different owner home");
    owned_slots[3] = 0;
    owned_slots[2] = -1;
    check(!jit_test_list_tail_consumes_home(program, &tail),
	  "list tail consumed a missing owner home");
    owned_slots[2] = 0;
    escapes[2] = JIT_ESCAPE_CALL;
    check(!jit_test_list_tail_consumes_home(program, &tail),
	  "escaping list tail consumed its owner home");
    escapes[2] = JIT_ESCAPE_NONE;
    uses[2] = 2;
    check(!jit_test_list_tail_consumes_home(program, &tail),
	  "multiply used list tail consumed its owner home");
    uses[2] = 1;
    tail.op = HIR_OP_ADD;
    check(!jit_test_list_tail_consumes_home(program, &tail),
	  "non-list tail consumed an owner home");

    jit_program_free(program);
}

static void
test_resume_capture_classification(void)
{
    static const var_type owned_types[] = {TYPE_STR, TYPE_LIST};
    static const var_type scalar_types[] = {
	TYPE_INT, TYPE_OBJ, TYPE_ERR, TYPE_FLOAT
    };
    unsigned i;
    int source;

    for (i = 0; i < sizeof(owned_types) / sizeof(owned_types[0]); i++) {
	for (source = JIT_RESUME_LOCAL; source <= JIT_RESUME_OPERAND; source++) {
	    int expected = source == JIT_RESUME_LOCAL
		|| source == JIT_RESUME_STACK
		|| source == JIT_RESUME_CAPTURED;

	    check(jit_test_resume_value_needs_capture(
		(JITResumeSource) source, owned_types[i]) == expected,
		  "owned resume source has the wrong capture classification");
	}
    }
    for (i = 0; i < sizeof(scalar_types) / sizeof(scalar_types[0]); i++)
	for (source = JIT_RESUME_LOCAL; source <= JIT_RESUME_OPERAND; source++)
	    check(!jit_test_resume_value_needs_capture(
		(JITResumeSource) source, scalar_types[i]),
		  "scalar resume value unexpectedly requires capture");
}

static void
test_continuation_capture_validation(void)
{
    JITProgram *program = new_jit_program();
    JITNativeResume *resume = allocate(sizeof(JITNativeResume));
    JITResumeValue *values = allocate(sizeof(JITResumeValue) * 8);
    JITContinuationFrame *frame;
    JITNativeFrame runtime_owner;
    activation stats_owner;
    Num raw[8];
    Var strings[3];
    Var list;
    Var homes[1];
    unsigned char states[1] = {JIT_HOME_OWNED};
    unsigned capacities[1] = {0};
    int i;

    memset(&runtime_owner, 0, sizeof(runtime_owner));
    memset(&stats_owner, 0, sizeof(stats_owner));
    memset(raw, 0, sizeof(raw));
    program->num_values = 8;
    program->num_deopt_maps = 2;
    program->num_owned_slots = 1;
    program->deopt_maps = allocate(sizeof(JITDeoptMap) * 2);
    program->value_types = allocate(sizeof(int16_t) * 8);
    program->value_is_tagged = allocate(8);
    program->deopt_maps[1].native_resume = resume;
    resume->valid = 1;
    resume->capture_classified = 1;
    resume->num_values = 8;
    resume->num_capture_values = 7;
    resume->num_owner_values = 1;
    resume->values = values;
    for (i = 0; i < 8; i++) {
	values[i].value = i ? i : 1;
	values[i].index = 0;
	values[i].source = JIT_RESUME_CONSTANT;
	program->value_types[i] = TYPE_INT;
    }

    strings[0].type = strings[1].type = strings[2].type = TYPE_STR;
    strings[0].v.str = str_dup("captured local");
    strings[1].v.str = str_dup("borrowed local");
    strings[2].v.str = str_dup("owner home");
    list = new_list(1);
    list.v.list[1].type = TYPE_INT;
    list.v.list[1].v.num = 42;
    homes[0] = strings[2];
    raw[1] = (Num) (intptr_t) strings[0].v.str;
    raw[2] = (Num) (intptr_t) list.v.list;
    raw[3] = (Num) (intptr_t) strings[1].v.str;
    program->value_types[1] = TYPE_STR;
    program->value_types[2] = TYPE_LIST;
    program->value_types[3] = TYPE_STR;
    values[0].value = 1;
    values[0].source = JIT_RESUME_LOCAL;
    values[1].value = 2;
    values[1].source = JIT_RESUME_STACK;
    values[2].value = 3;
    values[2].source = JIT_RESUME_BORROWED_LOCAL;
    values[3].source = JIT_RESUME_OWNER;
    values[4].source = JIT_RESUME_RESULT;
    values[5].source = JIT_RESUME_CONSTANT;
    values[6].source = JIT_RESUME_OPERAND;
    values[7].source = JIT_RESUME_OWNER;

    check(!jit_test_continuation_capture(0, 1, raw, 0, 0, homes, states,
	capacities, 0, 0)
	  && !jit_test_continuation_capture(program, 0, raw, 0, 0, homes,
	      states, capacities, 0, 0)
	  && !jit_test_continuation_capture(program, 2, raw, 0, 0, homes,
	      states, capacities, 0, 0),
	  "continuation capture accepted an invalid program or map");
    resume->valid = 0;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted an invalid resume");
    resume->valid = 1;
    values[3].index = -1;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted a negative owner");
    values[3].index = 1;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted an excessive owner");
    values[3].index = 0;
    states[0] = JIT_HOME_EMPTY;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted an empty owner");
    states[0] = JIT_HOME_OWNED;
    homes[0].type = TYPE_NONE;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted an owner without a value");
    homes[0] = strings[2];
    program->value_types[1] = (var_type) 127;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted an invalid value type");
    program->value_types[1] = TYPE_STR;
    values[7].index = -1;
    check(!jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0),
	  "continuation capture accepted an invalid owner tail");
    values[7].index = 0;

    frame = jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	states, capacities, 0, 0);
    check(frame && frame->map_id == 1 && frame->num_retained == 2
	  && frame->retained_values[0].type == TYPE_STR
	  && frame->retained_values[1].type == TYPE_LIST,
	  "continuation capture did not retain complex values");
    if (frame) {
	JITProgramStats program_stats;
	JITPoolStats pool_stats;
	size_t minimum_bytes = sizeof(*frame)
	    + sizeof(Var) * (frame->retained_capacity
		+ frame->spare_retained_capacity);

	jit_continuation_attach(frame, &stats_owner);
	jit_program_stats(program, &program_stats);
	jit_pool_stats(&pool_stats);
	check(program_stats.active_continuations == 1
	      && program_stats.continuation_bytes >= minimum_bytes,
	      "program statistics omitted its live continuation");
	check(pool_stats.active_continuations >= 1
	      && pool_stats.continuation_bytes >= minimum_bytes,
	      "pool statistics omitted a live continuation");
	frame->result.type = TYPE_STR;
	frame->result.v.str = str_dup("discarded result");
	frame->has_result = 1;
	frame->dispatched = 1;
	check(jit_test_continuation_capture(program, 1, raw, 0, 0, homes,
	    states, capacities, 0, frame) == frame
	      && !frame->has_result && !frame->dispatched
	      && frame->num_retained == 2,
	      "continuation recapture did not replace retained state");

	runtime_owner.owns_runtime = 1;
	runtime_owner.runtime_borrower = frame;
	runtime_owner.runtime_storage = raw;
	frame->runtime_owner = &runtime_owner;
	frame->runtime_storage = raw;
	frame->owned_values = homes;
	frame->home_states = states;
	frame->runtime_bytes = sizeof(raw);
	check(jit_test_continuation_capture(program, 1, raw, raw, 0, homes,
	    states, capacities, sizeof(raw), frame) == frame,
	      "continuation capture rejected consistent borrowed runtime");
	frame->owns_runtime = 1;
	check(!jit_test_continuation_capture(program, 1, raw, raw, 0, homes,
	    states, capacities, sizeof(raw), frame),
	      "continuation capture accepted multiply owned runtime");
	frame->owns_runtime = 0;
	runtime_owner.runtime_borrower = 0;
	check(!jit_test_continuation_capture(program, 1, raw, raw, 0, homes,
	    states, capacities, sizeof(raw), frame),
	      "continuation capture accepted the wrong runtime borrower");
	runtime_owner.runtime_borrower = frame;
	frame->runtime_owner = 0;
	frame->runtime_storage = 0;
	frame->owned_values = 0;
	frame->home_states = 0;
	frame->runtime_bytes = 0;
	jit_continuation_free(frame);
	check(!stats_owner.jit_continuation,
	      "released continuation remained attached to its activation");
	jit_program_stats(program, &program_stats);
	check(program_stats.active_continuations == 0
	      && program_stats.continuation_bytes == 0,
	      "released continuation remained in program statistics");
    }
    free_var(strings[0]);
    free_var(strings[1]);
    free_var(strings[2]);
    free_var(list);
    jit_program_free(program);
}

static JITProgram *
single_local_continuation_program(JITResumeSource source, var_type type)
{
    JITProgram *program = new_jit_program();
    JITDeoptMap *map;

    program->num_values = 2;
    program->num_vars = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->value_types[1] = type;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->reason = JIT_DEOPT_TYPE_GUARD;
    map->bytecode_pc = 71;
    map->error_pc = 72;
    map->num_locals = 1;
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
    map->native_resume = allocate(sizeof(JITNativeResume));
    map->native_resume->valid = 1;
    map->native_resume->rehydratable = 1;
    map->native_resume->num_values = 1;
    map->native_resume->values = allocate(sizeof(JITResumeValue));
    map->native_resume->values[0].value = 1;
    map->native_resume->values[0].source = source;
    return program;
}

static void
test_undispatched_continuation_materialization(void)
{
    Program bytecode;

    memset(&bytecode, 0, sizeof(bytecode));
    {
	JITProgram *program = single_local_continuation_program(
	    JIT_RESUME_CONSTANT, TYPE_INT);
	JITNativeResume *resume = program->deopt_maps[1].native_resume;
	JITContinuationFrame *continuation;
	activation owner;
	Var env[1];
	Var stack[1];
	Num raw[2] = {0, 0};

	resume->num_literals = 1;
	resume->literals = allocate(sizeof(JITResumeLiteral));
	resume->literals[0].literal_type = TYPE_INT;
	resume->literals[0].literal = 123;
	memset(&owner, 0, sizeof(owner));
	env[0].type = TYPE_INT;
	env[0].v.num = 9;
	owner.prog = &bytecode;
	owner.rt_env = env;
	owner.base_rt_stack = owner.top_rt_stack = stack;
	owner.rt_stack_size = 1;
	owner.temp.type = TYPE_NONE;
	continuation = jit_test_continuation_capture(program, 1, raw, 0, 0,
	    0, 0, 0, 0, 0);
	check(continuation != 0,
	      "constant-local continuation was not captured");
	if (continuation) {
	    jit_continuation_attach(continuation, &owner);
	    check(jit_continuation_materialize(&owner),
		  "constant-local continuation did not materialize");
	}
	check(!owner.jit_continuation && env[0].type == TYPE_INT
	      && env[0].v.num == 123 && owner.pc == 71
	      && owner.error_pc == 72,
	      "constant-local continuation restored the wrong state");
	if (owner.jit_continuation)
	    jit_continuation_free(owner.jit_continuation);
	jit_program_free(program);
    }
    {
	JITProgram *program = single_local_continuation_program(
	    JIT_RESUME_LOCAL, TYPE_ANY);
	JITContinuationFrame *continuation;
	activation owner;
	Var env[1];
	Var stack[1];
	Var original;
	Num raw[3] = {0, 0, 0};

	program->value_is_tagged[1] = 1;
	use_compact_tag_slots(program);
	original.type = TYPE_STR;
	original.v.str = str_dup("tagged continuation local");
	raw[1] = (Num) (intptr_t) original.v.str;
	raw[2] = TYPE_STR;
	memset(&owner, 0, sizeof(owner));
	env[0].type = TYPE_INT;
	env[0].v.num = 9;
	owner.prog = &bytecode;
	owner.rt_env = env;
	owner.base_rt_stack = owner.top_rt_stack = stack;
	owner.rt_stack_size = 1;
	owner.temp.type = TYPE_NONE;
	continuation = jit_test_continuation_capture(program, 1, raw, 0, 0,
	    0, 0, 0, 0, 0);
	check(continuation && var_refcount(original) == 2,
	      "tagged-local continuation did not retain its value");
	if (continuation) {
	    jit_continuation_attach(continuation, &owner);
	    check(jit_continuation_materialize(&owner),
		  "tagged-local continuation did not materialize");
	}
	check(!owner.jit_continuation && env[0].type == TYPE_STR
	      && env[0].v.str == original.v.str
	      && var_refcount(original) == 2,
	      "tagged-local continuation restored the wrong ownership");
	if (owner.jit_continuation)
	    jit_continuation_free(owner.jit_continuation);
	free_var(env[0]);
	free_var(original);
	jit_program_free(program);
    }
}

static void
test_control_stack_continuation_materialization(void)
{
    JITProgram *program = new_jit_program();
    JITDeoptMap *map;
    JITContinuationFrame *continuation;
    activation owner;
    Var stack[3];
    Num raw[1] = {0};

    program->num_values = 1;
    program->value_types = allocate(sizeof(var_type));
    program->value_is_tagged = allocate(1);
    program->usage = allocate(sizeof(JITProgramUsage));
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->reason = JIT_DEOPT_TYPE_GUARD;
    map->bytecode_pc = 76;
    map->error_pc = 77;
    map->stack_depth = 3;
    map->stack_values = allocate(sizeof(int) * 3);
    map->stack_slots = allocate(sizeof(ResumeStackSlot) * 3);
    map->stack_slots[0].kind = RSS_CATCH;
    map->stack_slots[0].data = 101;
    map->stack_slots[1].kind = RSS_FINALLY;
    map->stack_slots[1].data = 202;
    map->stack_slots[2].kind = RSS_HANDLER_PC;
    map->stack_slots[2].data = 303;
    map->native_resume = allocate(sizeof(JITNativeResume));
    map->native_resume->valid = 1;
    map->native_resume->rehydratable = 1;

    continuation = jit_test_continuation_capture(program, 1, raw, 0, 0,
	0, 0, 0, 0, 0);
    memset(&owner, 0, sizeof(owner));
    stack[0].type = TYPE_STR;
    stack[0].v.str = str_dup("discarded stack value");
    owner.base_rt_stack = stack;
    owner.top_rt_stack = stack + 1;
    owner.rt_stack_size = 3;
    owner.temp.type = TYPE_STR;
    owner.temp.v.str = str_dup("discarded temporary");
    check(continuation != 0,
	  "control-stack continuation was not captured");
    if (continuation) {
	jit_continuation_attach(continuation, &owner);
	check(jit_continuation_materialize(&owner),
	      "control-stack continuation did not materialize");
    }
    check(!owner.jit_continuation
	  && owner.top_rt_stack == owner.base_rt_stack + 3
	  && stack[0].type == TYPE_CATCH && stack[0].v.num == 101
	  && stack[1].type == TYPE_FINALLY && stack[1].v.num == 202
	  && stack[2].type == TYPE_INT && stack[2].v.num == 303
	  && owner.temp.type == TYPE_NONE
	  && owner.pc == 76 && owner.error_pc == 77
	  && program->usage->continuation_captures == 1
	  && program->usage->continuation_materializations == 1,
	  "control-stack continuation restored the wrong activation");
    while (owner.top_rt_stack > owner.base_rt_stack)
	free_var(*--owner.top_rt_stack);
    free_var(owner.temp);
    if (owner.jit_continuation)
	jit_continuation_free(owner.jit_continuation);
    jit_program_free(program);
}

static void
test_all_continuations_materialize(void)
{
    JITProgram *programs[3];
    JITContinuationFrame *continuation;
    activation owners[3];
    Program bytecode;
    Var env[3];
    Var stacks[3];
    Num raw[2] = {0, 0};
    int i;

    memset(&bytecode, 0, sizeof(bytecode));
    for (i = 0; i < 3; i++) {
	JITNativeResume *resume;

	programs[i] = single_local_continuation_program(
	    JIT_RESUME_CONSTANT, TYPE_INT);
	resume = programs[i]->deopt_maps[1].native_resume;
	resume->num_literals = 1;
	resume->literals = allocate(sizeof(JITResumeLiteral));
	resume->literals[0].literal_type = TYPE_INT;
	resume->literals[0].literal = 300 + i;
	memset(&owners[i], 0, sizeof(owners[i]));
	env[i].type = TYPE_INT;
	env[i].v.num = i;
	owners[i].prog = &bytecode;
	owners[i].rt_env = &env[i];
	owners[i].base_rt_stack = owners[i].top_rt_stack = &stacks[i];
	owners[i].rt_stack_size = 1;
	owners[i].temp.type = TYPE_NONE;
	continuation = jit_test_continuation_capture(programs[i], 1, raw,
	    0, 0, 0, 0, 0, 0, 0);
	check(continuation != 0,
	      "global-boundary continuation was not captured");
	if (continuation)
	    jit_continuation_attach(continuation, &owners[i]);
    }

    jit_continuation_free(owners[1].jit_continuation);
    check(!owners[1].jit_continuation && env[1].v.num == 1,
	  "middle continuation did not unlink independently");
    jit_continuation_materialize_all();
    check(!owners[0].jit_continuation && !owners[1].jit_continuation
	  && !owners[2].jit_continuation
	  && env[0].type == TYPE_INT && env[0].v.num == 300
	  && env[1].type == TYPE_INT && env[1].v.num == 1
	  && env[2].type == TYPE_INT && env[2].v.num == 302,
	  "global boundary did not materialize every continuation");
    for (i = 0; i < 3; i++)
	jit_program_free(programs[i]);
}

static void
test_specialized_builtin_boundary_materialization(void)
{
    JITProgram *program = new_jit_program();
    JITDeoptMap *map;
    JITContinuationFrame *continuation;
    JITNativeResume *resume;
    activation owner;
    Program bytecode;
    Var owner_env[1];
    Var owner_stack[2];
    Var wrong;
    Var boundary;
    Num raw[3] = {0, 0, 0};

    program->num_values = 3;
    program->num_vars = 1;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    program->usage = allocate(sizeof(JITProgramUsage));
    program->value_types[1] = TYPE_INT;
    program->value_types[2] = TYPE_INT;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->reason = JIT_DEOPT_ARITHMETIC_TYPE;
    map->builtin_func = 6;
    map->builtin_args = 2;
    map->bytecode_pc = 81;
    map->error_pc = 82;
    map->num_locals = 1;
    allocate_map_locals(map, 1);
    map->local_values[0].value = 1;
    map->stack_depth = 2;
    map->stack_values = allocate(sizeof(int) * 2);
    map->stack_types = allocate(sizeof(var_type) * 2);
    map->stack_values[0] = 1;
    map->stack_values[1] = 2;
    map->stack_types[0] = TYPE_INT;
    map->stack_types[1] = TYPE_INT;
    map->native_resume = resume = allocate(sizeof(JITNativeResume));
    resume->valid = 1;
    resume->rehydratable = 1;
    resume->num_values = 2;
    resume->values = allocate(sizeof(JITResumeValue) * 2);
    resume->values[0].value = 1;
    resume->values[0].source = JIT_RESUME_OPERAND;
    resume->values[1].value = 2;
    resume->values[1].source = JIT_RESUME_OPERAND;

    continuation = jit_test_continuation_capture(program, 1, raw, 0, 0,
	0, 0, 0, 0, 0);
    memset(&owner, 0, sizeof(owner));
    memset(&bytecode, 0, sizeof(bytecode));
    bytecode.num_var_names = 1;
    owner_env[0].type = TYPE_INT;
    owner_env[0].v.num = 99;
    owner.prog = &bytecode;
    owner.rt_env = owner_env;
    owner.base_rt_stack = owner.top_rt_stack = owner_stack;
    owner.rt_stack_size = 2;
    owner.temp.type = TYPE_NONE;
    check(continuation != 0,
	  "specialized built-in continuation was not captured");
    if (continuation)
	jit_continuation_attach(continuation, &owner);

    wrong.type = TYPE_INT;
    wrong.v.num = 10;
    check(!jit_continuation_materialize_boundary(&owner, &wrong, 1)
	  && owner.jit_continuation == continuation
	  && owner.top_rt_stack == owner.base_rt_stack
	  && program->usage->continuation_materializations == 0,
	  "specialized boundary accepted a non-list argument package");
    boundary = new_list(1);
    boundary.v.list[1].type = TYPE_INT;
    boundary.v.list[1].v.num = 10;
    check(!jit_continuation_materialize_boundary(&owner, &boundary, 1)
	  && owner.jit_continuation == continuation
	  && owner.top_rt_stack == owner.base_rt_stack
	  && program->usage->continuation_materializations == 0,
	  "specialized boundary accepted the wrong argument count");
    free_var(boundary);

    boundary = new_list(2);
    boundary.v.list[1].type = TYPE_INT;
    boundary.v.list[1].v.num = 10;
    boundary.v.list[2].type = TYPE_STR;
    boundary.v.list[2].v.str = str_dup("twenty");
    check(jit_continuation_materialize_boundary(&owner, &boundary, 1),
	  "specialized built-in boundary did not materialize");
    check(!owner.jit_continuation
	  && owner.top_rt_stack == owner.base_rt_stack + 2
	  && owner_stack[0].type == TYPE_INT && owner_stack[0].v.num == 10
	  && owner_stack[1].type == TYPE_STR
	  && !strcmp(owner_stack[1].v.str, "twenty")
	  && owner_env[0].type == TYPE_INT && owner_env[0].v.num == 10
	  && owner.pc == 81 && owner.error_pc == 82
	  && program->usage->continuation_captures == 1
	  && program->usage->continuation_materializations == 1,
	  "specialized built-in boundary unpacked the wrong activation");
    free_var(boundary);
    while (owner.top_rt_stack > owner.base_rt_stack)
	free_var(*--owner.top_rt_stack);
    if (owner.jit_continuation)
	jit_continuation_free(owner.jit_continuation);
    jit_program_free(program);
}

static void
test_verb_boundary_outer_state_materialization(void)
{
    JITProgram *program = new_jit_program();
    JITDeoptMap *map;
    JITContinuationFrame *continuation;
    JITNativeResume *resume;
    activation owner;
    Program bytecode;
    Var env[2];
    Var owner_stack[7];
    Var boundary[3];
    Num raw[5] = {0, 0, 0, 0, 0};
    int i;

    program->num_values = 5;
    program->value_types = allocate(sizeof(var_type) * program->num_values);
    program->value_is_tagged = allocate(program->num_values);
    for (i = 1; i < program->num_values; i++)
	program->value_types[i] = TYPE_INT;
    add_entry_deopt_map(program);
    program->deopt_maps = myrealloc(program->deopt_maps,
				    sizeof(JITDeoptMap) * 2, M_PROGRAM);
    map = &program->deopt_maps[1];
    memset(map, 0, sizeof(*map));
    program->num_deopt_maps = 2;
    map->reason = JIT_DEOPT_VERB_CALL;
    map->bytecode_pc = 91;
    map->error_pc = 92;
    map->num_locals = 2;
    allocate_map_locals(map, 2);
    map->local_values[0].value = 1;
    map->local_values[1].value = 0;
    map->stack_depth = 7;
    map->stack_values = allocate(sizeof(int) * map->stack_depth);
    map->stack_types = allocate(sizeof(var_type) * map->stack_depth);
    map->stack_slots = allocate(sizeof(ResumeStackSlot) * map->stack_depth);
    map->stack_slots[0].kind = RSS_CATCH;
    map->stack_slots[0].data = 123;
    map->stack_slots[1].kind = RSS_FINALLY;
    map->stack_slots[1].data = 456;
    map->stack_slots[2].kind = RSS_HANDLER_PC;
    map->stack_slots[2].data = 789;
    map->stack_values[3] = 4;
    map->stack_types[3] = TYPE_INT;
    map->stack_slots[3].kind = RSS_VALUE;
    for (i = 4; i < (int) map->stack_depth; i++) {
	map->stack_values[i] = i - 3;
	map->stack_types[i] = TYPE_INT;
	map->stack_slots[i].kind = RSS_VALUE;
    }
    map->native_resume = resume = allocate(sizeof(*resume));
    resume->valid = 1;
    resume->rehydratable = 1;
    resume->num_values = 2;
    resume->values = allocate(sizeof(*resume->values) * 2);
    resume->values[0].value = 1;
    resume->values[0].source = JIT_RESUME_OPERAND;
    resume->values[1].value = 4;
    resume->values[1].source = JIT_RESUME_CONSTANT;
    resume->values[1].index = 0;
    resume->num_literals = 1;
    resume->literals = allocate(sizeof(*resume->literals));
    resume->literals[0].literal_type = TYPE_INT;
    resume->literals[0].literal = 77;

    continuation = jit_test_continuation_capture(program, 1, raw, 0, 0,
	0, 0, 0, 0, 0);
    memset(&owner, 0, sizeof(owner));
    memset(&bytecode, 0, sizeof(bytecode));
    bytecode.num_var_names = 2;
    env[0].type = TYPE_STR;
    env[0].v.str = str_dup("replaced local");
    env[1].type = TYPE_INT;
    env[1].v.num = 888;
    owner.prog = &bytecode;
    owner.rt_env = env;
    owner.base_rt_stack = owner.top_rt_stack = owner_stack;
    owner.rt_stack_size = 7;
    owner.temp.type = TYPE_NONE;
    check(continuation != 0,
	  "verb boundary continuation was not captured");
    if (continuation)
	jit_continuation_attach(continuation, &owner);

    for (i = 0; i < 3; i++) {
	boundary[i].type = TYPE_INT;
	boundary[i].v.num = 10 + i;
    }
    check(jit_continuation_materialize_boundary(&owner, boundary, 3),
	  "verb boundary with outer state did not materialize");
    check(!owner.jit_continuation
	  && owner.top_rt_stack == owner.base_rt_stack + 7
	  && owner_stack[0].type == TYPE_CATCH
	  && owner_stack[0].v.num == 123
	  && owner_stack[1].type == TYPE_FINALLY
	  && owner_stack[1].v.num == 456
	  && owner_stack[2].type == TYPE_INT && owner_stack[2].v.num == 789
	  && owner_stack[3].type == TYPE_INT && owner_stack[3].v.num == 77
	  && owner_stack[4].type == TYPE_INT && owner_stack[4].v.num == 10
	  && owner_stack[5].type == TYPE_INT && owner_stack[5].v.num == 11
	  && owner_stack[6].type == TYPE_INT && owner_stack[6].v.num == 12
	  && env[0].type == TYPE_INT && env[0].v.num == 10
	  && env[1].type == TYPE_INT && env[1].v.num == 888
	  && owner.pc == 91 && owner.error_pc == 92,
	  "verb boundary restored the wrong outer state or operands");
    while (owner.top_rt_stack > owner.base_rt_stack)
	free_var(*--owner.top_rt_stack);
    free_var(env[0]);
    free_var(env[1]);
    if (owner.jit_continuation)
	jit_continuation_free(owner.jit_continuation);
    jit_program_free(program);
}

static void
test_dispatched_continuation_materialization(void)
{
    JITProgram *program = call_verb_program();
    JITContinuationFrame *continuation = 0;
    JITDeoptState deopt;
    ResumePoint point;
    Program bytecode;
    activation owner;
    Var env[3];
    Var owner_env[3];
    Var owner_stack[4];
    Var deopt_stack[3];
    Var result;
    Var returned;
    int ticks = 10;
    int timed_out = 0;
    enum error error = E_NONE;
    int i;

    memset(&point, 0, sizeof(point));
    memset(&bytecode, 0, sizeof(bytecode));
    memset(&owner, 0, sizeof(owner));
    memset(deopt_stack, 0, sizeof(deopt_stack));
    env[0].type = TYPE_OBJ;
    env[0].v.obj = 0;
    env[1].type = TYPE_STR;
    env[1].v.str = str_dup("materialize");
    env[2] = new_list(0);
    for (i = 0; i < 3; i++) {
	owner_env[i].type = TYPE_INT;
	owner_env[i].v.num = 40 + i;
    }
    owner.prog = &bytecode;
    owner.rt_env = owner_env;
    owner.base_rt_stack = owner.top_rt_stack = owner_stack;
    owner.rt_stack_size = 4;
    owner.temp.type = TYPE_INT;
    owner.temp.v.num = 99;

    check((jit_program_execute)(program, env, &result, &ticks,
	&timed_out, &error, 0, &deopt, deopt_stack, 2, -1, 0,
	&continuation) == JIT_RUN_CALL_VERB && continuation,
	"verb call did not capture a materializable continuation");
    if (continuation) {
	Var replaced;

	/* The post-call map stores the returned expression in local zero. */
	program->deopt_maps[1].local_values[0].value = 4;
	point.key = program->deopt_maps[1].resume_key;
	point.pc = 77;
	point.error_pc = 78;
	point.kind = RP_CALL;
	hir_test_set_resume_point(&point);
	jit_continuation_attach(continuation, &owner);
	jit_continuation_mark_dispatched(continuation);
	replaced.type = TYPE_STR;
	replaced.v.str = str_dup("superseded callee result");
	jit_continuation_set_result(continuation, var_ref(replaced));
	returned.type = TYPE_STR;
	returned.v.str = str_dup("callee result");
	jit_continuation_set_result(continuation, returned);
	check(var_refcount(replaced) == 1,
	      "replaced continuation result retained a reference");
	free_var(replaced);
	check(jit_continuation_materialize(&owner),
	      "dispatched continuation did not materialize");
	check(!owner.jit_continuation
	      && owner.top_rt_stack == owner.base_rt_stack + 1
	      && owner_stack[0].type == TYPE_STR
	      && !strcmp(owner_stack[0].v.str, "callee result")
	      && owner_env[0].type == TYPE_STR
	      && owner_env[0].v.str == owner_stack[0].v.str,
	      "materialized continuation lost its callee result");
	check(owner.pc == point.pc && owner.error_pc == point.error_pc
	      && owner.resume_key.code_unit == point.key.code_unit
	      && owner.resume_key.site == point.key.site,
	      "materialized continuation restored the wrong resume point");
	check(owner_env[1].v.num == 41 && owner_env[2].v.num == 42,
	      "operand-backed locals were overwritten during materialization");
    }
    hir_test_set_resume_point(0);
    if (owner.jit_continuation)
	jit_continuation_free(owner.jit_continuation);
    while (owner.top_rt_stack > owner.base_rt_stack)
	free_var(*--owner.top_rt_stack);
    for (i = 0; i < 3; i++) {
	free_var(env[i]);
	free_var(owner_env[i]);
	free_var(deopt_stack[i]);
    }
    free_var(owner.temp);
    jit_program_free(program);
}

int
main(void)
{
    JITProgram *program = arithmetic_program();
    JITProgram *two_ticks = two_tick_program();
    JITProgram *duplicate_tick_exits = duplicate_tick_exit_program();
    JITProgram *guard = guard_program();
    JITProgram *deep_guard = deep_guard_program();
    JITProgram *branch = branch_program();
    JITProgram *charge_tick = charge_tick_program();
    JITProgram *divide = binary_program(20, 4, HIR_OP_DIV);
    JITProgram *divide_zero = binary_program(20, 0, HIR_OP_DIV);
    JITProgram *divide_overflow = binary_program(NUM_MIN, -1, HIR_OP_DIV);
    JITProgram *modulus_overflow = binary_program(NUM_MIN, -1, HIR_OP_MOD);
    JITProgram *modulus_power_two = binary_program(13, 8, HIR_OP_MOD);
    JITProgram *negative_modulus_power_two = binary_program(-13, 8,
	HIR_OP_MOD);
    JITProgram *minimum_modulus_power_two = binary_program(NUM_MIN, 8,
	HIR_OP_MOD);
    JITProgram *modulus_one = binary_program(-13, 1, HIR_OP_MOD);
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
    struct mir_dump mir_dump = { 0 };
    struct machine_dump machine_dump = {0, 0};
    JITDeoptState deopt;
    JITSourceLocation source_location;

    test_program_metadata_api();
    test_released_ir_restoration();
    test_guard_and_index_set_lowering();
    test_numeric_and_comparison_lowering_matrix();
    test_tick_return_and_dump_lowering();
    test_runtime_helper_edge_cases();
    test_perf_map_and_manual_rotation();
    test_full_metadata_accounting_and_free();
    test_suspend_zero_detection();
    test_suspend_zero_validation_matrix();
    test_native_resume_constant_lowering();
    test_native_frame_verifier_rejections();
    test_owned_call_boundary_lowering();
    test_boundary_value_ownership_transfer();
    test_guard_actual_type_sources();
    test_typed_deopt_materialization();
    test_mir_allocator();
    test_null_jit_api_contracts();
    test_entry_activation_validation();
    test_owned_value_predicates();
    test_resume_capture_classification();
    test_continuation_capture_validation();
    test_undispatched_continuation_materialization();
    test_control_stack_continuation_materialization();
    test_all_continuations_materialize();
    test_specialized_builtin_boundary_materialization();
    test_verb_boundary_outer_state_materialization();
    test_dispatched_continuation_materialization();

    {
	JITProgram *dead = owned_last_use_program(0, 0);
	JITProgram *live = owned_last_use_program(0, 1);
	JITProgram *loop_dead = owned_last_use_program(1, 0);
	JITProgram *loop_live = owned_last_use_program(1, 1);
	JITProgram *branch_dead = owned_last_use_branch_program(0);
	JITProgram *branch_live = owned_last_use_branch_program(1);
	JITProgram *third_dead = owned_last_use_third_operand_program(0);
	JITProgram *third_live = owned_last_use_third_operand_program(1);

	jit_analyze_owned_last_uses(dead);
	jit_analyze_owned_last_uses(live);
	jit_analyze_owned_last_uses(loop_dead);
	jit_analyze_owned_last_uses(loop_live);
	jit_analyze_owned_last_uses(branch_dead);
	jit_analyze_owned_last_uses(branch_live);
	jit_analyze_owned_last_uses(third_dead);
	jit_analyze_owned_last_uses(third_live);
	check(owned_last_use_candidate(dead)->owned_last_use
	      & JIT_LAST_USE_SRC1,
	      "owned last-use analysis missed a dead alias");
	check(!(owned_last_use_candidate(live)->owned_last_use
		& JIT_LAST_USE_SRC1),
	      "owned last-use analysis discarded a live alias");
	check(owned_last_use_candidate(loop_dead)->owned_last_use
	      & JIT_LAST_USE_SRC1,
	      "owned last-use analysis missed a loop-carried replacement");
	check(!(owned_last_use_candidate(loop_live)->owned_last_use
		& JIT_LAST_USE_SRC1),
	      "owned last-use analysis ignored a live loop alias");
	check(owned_last_use_candidate(branch_dead)->owned_last_use
	      & JIT_LAST_USE_SRC1,
	      "owned last-use analysis missed dead CFG successors");
	check(!(owned_last_use_candidate(branch_live)->owned_last_use
		& JIT_LAST_USE_SRC1),
	      "owned last-use analysis ignored a live CFG successor");
	check(third_dead->blocks->first->next->owned_last_use
	      & JIT_LAST_USE_SRC3,
	      "owned last-use analysis missed a dead third operand");
	check(!(third_live->blocks->first->next->owned_last_use
		& JIT_LAST_USE_SRC3),
	      "owned last-use analysis discarded a live third operand");
	jit_program_free(third_live);
	jit_program_free(third_dead);
	jit_program_free(branch_live);
	jit_program_free(branch_dead);
	jit_program_free(loop_live);
	jit_program_free(loop_dead);
	jit_program_free(live);
	jit_program_free(dead);
    }

    {
	JITNativeFrame compact;
	JITNativeFrame overlay;
	Program bytecode;
	activation invocation;
	Var invocation_env[1];
#ifdef WAIF_CORE
	int receiver_refs;
#endif

	memset(&compact, 0, sizeof(compact));
	memset(&overlay, 0, sizeof(overlay));
	memset(&bytecode, 0, sizeof(bytecode));
	memset(&invocation, 0, sizeof(invocation));
	compact.kind = JIT_FRAME_COMPACT;
	bytecode.ref_count = 1;
	bytecode.num_var_names = 1;
	invocation_env[0].type = TYPE_STR;
	invocation_env[0].v.str = str_dup("invocation environment");
	invocation.prog = &bytecode;
	invocation.rt_env = invocation_env;
#ifdef WAIF_CORE
	invocation.THIS = hir_test_new_waif();
	receiver_refs = var_refcount(invocation.THIS);
#endif
	invocation.this = 17;
	invocation.player = 18;
	invocation.progr = 19;
	invocation.vloc = 20;
	invocation.verb = str_dup("called");
	invocation.verbname = str_dup("called alias");
	invocation.debug = 1;
	check(!jit_native_frame_bind_activation(0, &invocation)
	      && !jit_native_frame_bind_activation(&overlay, 0),
	      "activation binding accepted a null argument");
	check(jit_native_frame_bind_activation(&overlay, &invocation)
	      && overlay.bytecode_program == &bytecode
	      && overlay.env == invocation_env && overlay.this == 17
	      && overlay.player == 18 && overlay.progr == 19
	      && overlay.vloc == 20 && overlay.verb == invocation.verb
	      && overlay.verbname == invocation.verbname && overlay.debug == 1,
	      "activation binding did not publish borrowed invocation state");
	check(jit_native_frame_copy_invocation(&compact, &invocation),
	      "compact frame invocation copy failed");
	check(compact.owns_invocation && compact.bytecode_program == &bytecode
	      && compact.env != invocation_env
	      && compact.env[0].type == TYPE_STR
	      && !strcmp(compact.env[0].v.str, "invocation environment")
	      && compact.this == 17 && compact.player == 18
	      && compact.progr == 19 && compact.vloc == 20
	      && compact.debug == 1 && bytecode.ref_count == 2,
	      "compact frame invocation metadata is incomplete");
#ifdef WAIF_CORE
	check(compact.receiver.type == TYPE_WAIF
	      && compact.receiver.v.waif == invocation.THIS.v.waif
	      && var_refcount(invocation.THIS) == receiver_refs + 1,
	      "compact frame did not retain its waif receiver");
#endif
	jit_native_frame_release_invocation(&compact);
	check(!compact.owns_invocation && !compact.bytecode_program
	      && !compact.env && bytecode.ref_count == 1,
	      "compact frame invocation release was incomplete");
#ifdef WAIF_CORE
	check(var_refcount(invocation.THIS) == receiver_refs,
	      "compact frame leaked its waif receiver");
#endif
	{
	    PreparedVerbCall prepared;
	    Var *prepared_env = mymalloc(sizeof(Var), M_RT_ENV);

	    memset(&compact, 0, sizeof(compact));
	    memset(&prepared, 0, sizeof(prepared));
	    prepared.program = program_ref(&bytecode);
	    prepared.env = prepared_env;
	    prepared_env[0].type = TYPE_STR;
	    prepared_env[0].v.str = str_dup("prepared environment");
#ifdef WAIF_CORE
	    prepared.receiver.type = TYPE_OBJ;
	    prepared.receiver.v.obj = 27;
#endif
	    prepared.this = 27;
	    prepared.player = 28;
	    prepared.progr = 29;
	    prepared.vloc = 30;
	    prepared.verb = str_dup("prepared");
	    prepared.verbname = str_dup("prepared alias");
	    prepared.debug = 1;
	    compact.kind = JIT_FRAME_COMPACT;
	    compact.env = invocation_env;
	    check(!jit_native_frame_take_prepared_invocation(&compact,
		&prepared) && prepared.program == &bytecode
		&& prepared.env == prepared_env && !compact.owns_invocation,
		"failed prepared invocation transfer consumed ownership");
	    compact.env = prepared_env;
	    check(jit_native_frame_take_prepared_invocation(&compact, &prepared),
		"prepared invocation ownership transfer failed");
	    check(compact.owns_invocation
		&& compact.bytecode_program == &bytecode
		&& compact.env == prepared_env && compact.this == 27
		&& compact.player == 28 && compact.progr == 29
		&& compact.vloc == 30 && compact.debug == 1
		&& !prepared.program && !prepared.env && !prepared.verb
		&& !prepared.verbname && bytecode.ref_count == 2,
		"prepared invocation ownership transfer was incomplete");
	    jit_native_frame_release_invocation(&compact);
	    check(bytecode.ref_count == 1,
		"prepared invocation release leaked its program reference");
	}
	free_var(invocation_env[0]);
#ifdef WAIF_CORE
	free_var(invocation.THIS);
#endif
	free_str(invocation.verb);
	free_str(invocation.verbname);
    }

    {
	JITExecutionContext context;
	JITNativeFrame root;
	JITNativeFrame child;
	Var homes[5];
	unsigned home_capacities[5] = { 0 };
	unsigned char home_states[5];
	Var value;
	Var taken;
	const char *shared;
	int i;

	for (i = 0; i < 5; i++) {
	    homes[i].type = TYPE_NONE;
	    homes[i].v.num = 0;
	    home_states[i] = JIT_HOME_EMPTY;
	}
	jit_execution_context_init(&context, &root, program, env, 2, 3, 10,
	    &ticks, &timed_out, &error, -1);
	check(jit_native_frame_verify(&context, &root),
	      "native root frame verification failed");
	jit_native_frame_bind_runtime(&root, homes, sizeof(homes), homes, 5,
	    home_states, home_capacities);
	check(jit_native_frame_verify(&context, &root),
	      "native frame runtime binding verification failed");

	value.type = TYPE_INT;
	value.v.num = 17;
	check(jit_native_frame_home_move(&root, 0, &value),
	      "native integer home move failed");
	check(value.type == TYPE_NONE
	      && jit_native_frame_home_take(&root, 0, &taken)
	      && taken.type == TYPE_INT && taken.v.num == 17,
	      "native integer home take failed");
	free_var(taken);

	value.type = TYPE_STR;
	value.v.str = str_dup("native frame home");
	check(jit_native_frame_home_move(&root, 1, &value)
	      && jit_native_frame_verify(&context, &root),
	      "native string home move failed");
	check(jit_native_frame_home_take(&root, 1, &taken),
	      "native string home take failed");
	free_var(taken);

	value = new_list(0);
	check(jit_native_frame_home_move(&root, 2, &value)
	      && jit_native_frame_verify(&context, &root)
	      && jit_native_frame_home_take(&root, 2, &taken),
	      "native list home transfer failed");
	free_var(taken);

	value.type = TYPE_FLOAT;
	value.v.fnum = box_fl(1.5);
	check(jit_native_frame_home_move(&root, 4, &value)
	      && jit_native_frame_verify(&context, &root)
	      && jit_native_frame_home_take(&root, 4, &taken),
	      "native float home transfer failed");
	free_var(taken);
#ifdef WAIF_CORE
	value = hir_test_new_waif();
	check(jit_native_frame_home_move(&root, 3, &value)
	      && jit_native_frame_verify(&context, &root)
	      && jit_native_frame_home_take(&root, 3, &taken),
	      "native waif home transfer failed");
	free_var(taken);
#endif
	check(jit_native_frame_verify(&context, &root),
	      "consumed native homes failed verification");

	value.type = TYPE_INT;
	value.v.num = 1;
	check(!jit_native_frame_home_move(&root, 0, &value),
	      "native frame reused a consumed home");
	free_var(value);
	home_states[0] = JIT_HOME_OWNED;
	check(!jit_native_frame_verify(&context, &root),
	      "native frame accepted an uninitialized owned home");
	home_states[0] = JIT_HOME_CONSUMED;

	shared = str_dup("duplicate native owner");
	homes[0].type = homes[1].type = TYPE_STR;
	homes[0].v.str = homes[1].v.str = shared;
	home_states[0] = home_states[1] = JIT_HOME_OWNED;
	check(!jit_native_frame_verify(&context, &root),
	      "native frame accepted duplicate ownership");
	homes[1].type = TYPE_NONE;
	homes[1].v.num = 0;
	home_states[1] = JIT_HOME_CONSUMED;
	free_var(homes[0]);
	homes[0].type = TYPE_NONE;
	homes[0].v.num = 0;
	home_states[0] = JIT_HOME_CONSUMED;

	jit_native_frame_unbind_runtime(&root);
	context.canonical_depth = context.activation_limit;
	context.native_depth = 1;
	check(!jit_native_frame_verify(&context, &root),
	      "native frame accepted excess activation depth");
	context.canonical_depth = 3;
	context.native_depth = 0;
	check(jit_execution_context_push_overlay(&context, &child, program, env,
	    3, -1), "native canonical overlay push failed");
	check(context.current_frame == &child && child.caller == &root
	      && root.state == JIT_FRAME_SUSPENDED
	      && child.state == JIT_FRAME_RUNNING,
	      "native canonical overlay linkage is wrong");
	check(jit_execution_context_pop_overlay(&context, &child),
	      "native canonical overlay pop failed");
	check(root.state == JIT_FRAME_RUNNING
	      && child.state == JIT_FRAME_DETACHED,
	      "native canonical overlay states were not restored");
	check(jit_execution_context_finish(&context, &root),
	      "native root frame did not detach cleanly");
    }

    {
	JITProgram *chain_program = call_boundary_program();
	JITExecutionContext context;
	JITNativeFrame root;
	JITNativeFrame middle;
	JITNativeFrame leaf;
	JITCallerResume root_resume;
	JITCallerResume middle_resume;
	Var root_home[1];
	Var middle_home[1];
	unsigned root_capacity[1] = { 0 };
	unsigned middle_capacity[1] = { 0 };
	unsigned char root_state[1];
	unsigned char middle_state[1];
	Var returned;
	Var transferred;

	root_home[0].type = middle_home[0].type = TYPE_NONE;
	root_home[0].v.num = middle_home[0].v.num = 0;
	root_state[0] = middle_state[0] = JIT_HOME_EMPTY;
	jit_execution_context_init(&context, &root, chain_program, env, 0, 1,
	    4, &ticks, &timed_out, &error, -1);
	jit_native_frame_bind_runtime(&root, root_home, sizeof(root_home),
	    root_home, 1, root_state, root_capacity);
	memset(&root_resume, 0, sizeof(root_resume));
	root_resume.caller = &root;
	root_resume.map_id = 1;
	root_resume.result_home = 0;
	root_resume.state = JIT_RESUME_PREPARING;
	check(jit_execution_context_push_compact(&context, &middle,
	    chain_program, deep_env, &root_resume, -1),
	      "first compact native dispatch failed");
	jit_native_frame_bind_runtime(&middle, middle_home,
	    sizeof(middle_home), middle_home, 1, middle_state, middle_capacity);

	memset(&middle_resume, 0, sizeof(middle_resume));
	middle_resume.caller = &middle;
	middle_resume.map_id = 1;
	middle_resume.result_home = 0;
	middle_resume.state = JIT_RESUME_PREPARING;
	check(jit_execution_context_push_compact(&context, &leaf,
	    chain_program, deopt_stack, &middle_resume, -1),
	      "second compact native dispatch failed");
	check(context.native_depth == 2 && context.current_frame == &leaf,
	      "compact native chain depth is wrong");

	returned = new_list(1);
	returned.v.list[1].type = TYPE_STR;
	returned.v.list[1].v.str = str_dup("compact chain result");
	check(jit_execution_context_return_compact(&context, &leaf, &returned),
	      "compact leaf return failed");
	check(returned.type == TYPE_NONE
	      && middle_resume.state == JIT_RESUME_RETURNED
	      && context.current_frame == &middle && context.native_depth == 1,
	      "compact leaf return transition is wrong");
	check(jit_native_frame_home_take(&middle, 0, &transferred),
	      "compact middle frame did not acquire its result");
	jit_native_frame_unbind_runtime(&middle);
	check(jit_execution_context_return_compact(&context, &middle,
	    &transferred), "compact middle return failed");
	check(transferred.type == TYPE_NONE
	      && root_resume.state == JIT_RESUME_RETURNED
	      && context.current_frame == &root && context.native_depth == 0,
	      "compact middle return transition is wrong");
	check(jit_native_frame_home_take(&root, 0, &transferred),
	      "compact root frame did not acquire the final result");
	check(transferred.type == TYPE_LIST
	      && transferred.v.list[1].type == TYPE_STR
	      && !strcmp(transferred.v.list[1].v.str, "compact chain result"),
	      "compact chain corrupted a complex result");
	free_var(transferred);
	jit_native_frame_unbind_runtime(&root);
	check(jit_execution_context_finish(&context, &root),
	      "compact chain root did not detach cleanly");
	jit_program_free(chain_program);
    }

    {
	JITProgram *chain_program = call_boundary_program();
	JITExecutionContext context;
	JITNativeFrame root;
	JITNativeFrame middle;
	JITNativeFrame leaf;
	JITCallerResume root_resume;
	JITCallerResume middle_resume;
	JITPromotionPlan *promotion;
	struct promotion_dump dump = {{0}, {0}, 0};
	Var root_homes[2];
	Var middle_home[1];
	unsigned root_capacities[2] = { 0 };
	unsigned middle_capacity[1] = { 0 };
	unsigned char root_states[2];
	unsigned char middle_state[1];
	Var retained;

	root_homes[0].type = root_homes[1].type = TYPE_NONE;
	root_homes[0].v.num = root_homes[1].v.num = 0;
	middle_home[0].type = TYPE_NONE;
	middle_home[0].v.num = 0;
	root_states[0] = root_states[1] = JIT_HOME_EMPTY;
	middle_state[0] = JIT_HOME_EMPTY;
	jit_execution_context_init(&context, &root, chain_program, env, 0, 1,
	    4, &ticks, &timed_out, &error, -1);
	jit_native_frame_bind_runtime(&root, root_homes, sizeof(root_homes),
	    root_homes, 2, root_states, root_capacities);
	retained.type = TYPE_STR;
	retained.v.str = str_dup("retained through promotion");
	check(jit_native_frame_home_move(&root, 1, &retained),
	      "promotion test could not retain its owned value");

	memset(&root_resume, 0, sizeof(root_resume));
	root_resume.caller = &root;
	root_resume.map_id = 1;
	root_resume.result_home = 0;
	root_resume.state = JIT_RESUME_PREPARING;
	check(jit_execution_context_push_compact(&context, &middle,
	    chain_program, deep_env, &root_resume, -1),
	      "promotion middle dispatch failed");
	jit_native_frame_bind_runtime(&middle, middle_home,
	    sizeof(middle_home), middle_home, 1, middle_state, middle_capacity);
	memset(&middle_resume, 0, sizeof(middle_resume));
	middle_resume.caller = &middle;
	middle_resume.map_id = 1;
	middle_resume.result_home = 0;
	middle_resume.state = JIT_RESUME_PREPARING;
	check(jit_execution_context_push_compact(&context, &leaf,
	    chain_program, deopt_stack, &middle_resume, 1),
	      "promotion leaf dispatch failed");

	leaf.current_map = 2;
	check(!jit_native_chain_prepare_promotion(&context)
	      && context.current_frame == &leaf && context.native_depth == 2
	      && root_resume.state == JIT_RESUME_DISPATCHED
	      && middle_resume.state == JIT_RESUME_DISPATCHED,
	      "failed promotion preparation mutated the native chain");
	leaf.current_map = 1;
	promotion = jit_native_chain_prepare_promotion(&context);
	check(promotion != 0, "native chain promotion preparation failed");
	check(jit_native_chain_promotion_count(promotion) == 3
	      && jit_native_chain_promotion_frame(promotion, 0) == &root
	      && jit_native_chain_promotion_frame(promotion, 1) == &middle
	      && jit_native_chain_promotion_frame(promotion, 2) == &leaf
	      && !jit_native_chain_promotion_frame(promotion, 3),
	      "native chain promotion snapshot access is wrong");
	check(jit_native_chain_commit_promotion(promotion, record_promotion,
	    &dump), "native chain promotion commit failed");
	check(dump.count == 3 && dump.frames[0] == &root
	      && dump.frames[1] == &middle && dump.frames[2] == &leaf
	      && dump.maps[0] == 1 && dump.maps[1] == 1
	      && dump.maps[2] == 1,
	      "native chain promotion order or maps are wrong");
	check(!context.root_frame && !context.current_frame
	      && context.native_depth == 0
	      && root.state == JIT_FRAME_PROMOTED
	      && middle.state == JIT_FRAME_PROMOTED
	      && leaf.state == JIT_FRAME_PROMOTED
	      && root_resume.state == JIT_RESUME_PROMOTED
	      && middle_resume.state == JIT_RESUME_PROMOTED,
	      "native chain promotion did not detach every frame");
	check(jit_native_frame_home_take(&root, 1, &retained)
	      && retained.type == TYPE_STR
	      && !strcmp(retained.v.str, "retained through promotion"),
	      "native chain promotion lost an owned value");
	free_var(retained);
	jit_native_frame_unbind_runtime(&middle);
	jit_native_frame_unbind_runtime(&root);
	jit_native_chain_discard_promotion(promotion);
	jit_program_free(chain_program);
    }

    {
	JITProgram *owner_program = call_boundary_program();
	JITDeoptMap *map = &owner_program->deopt_maps[1];
	JITNativeFrame native_frame;
	JITContinuationFrame *owned_continuation;
	JITNativeResume *resume;
	activation owner;
	Var owner_stack[2];
	Var owner_home[1];
	unsigned owner_capacity[1] = { 0 };
	unsigned char home_state[1];
	Num stale_values[6] = { 0, 0, 0, 0, 0, 0 };
	void *owned_storage;
	Var *borrowed_home;
	Var *owned_home;
	Var borrowed_original;
	unsigned *owned_capacity;
	unsigned char *owned_state;
	size_t owned_bytes;

	memset(&owner, 0, sizeof(owner));
	memset(&native_frame, 0, sizeof(native_frame));
	owner_program->value_types = allocate(sizeof(var_type) * 3);
	owner_program->value_is_tagged = allocate(3);
	owner_program->value_types[1] = TYPE_ANY;
	owner_program->value_is_tagged[1] = 1;
	owner_program->num_owned_slots = 1;
	resume = allocate(sizeof(*resume));
	resume->num_values = 1;
	resume->valid = 1;
	resume->values = allocate(sizeof(*resume->values));
	resume->values[0].value = 1;
	resume->values[0].source = JIT_RESUME_OWNER;
	resume->values[0].index = 0;
	map->native_resume = resume;
	map->num_locals = 0;
	map->num_local_values = 0;
	check(jit_program_compile(owner_program),
	      "owner-backed native resume did not compile");
	owner_home[0].type = TYPE_STR;
	owner_home[0].v.str = str_dup("authoritative owner tag");
	home_state[0] = JIT_HOME_OWNED;
	native_frame.program = owner_program;
	jit_native_frame_bind_runtime(&native_frame, stale_values,
	    sizeof(stale_values), owner_home, 1, home_state, owner_capacity);
	owner.base_rt_stack = owner.top_rt_stack = owner_stack;
	owner.rt_stack_size = 2;
	native_frame.runtime_bytes--;
	check(!jit_native_frame_prepare_activation(&native_frame, &owner, 1, 0)
	      && owner.top_rt_stack == owner.base_rt_stack,
	      "native frame accepted undersized runtime storage");
	native_frame.runtime_bytes++;
	owner.rt_stack_size = 0;
	check(!jit_native_frame_prepare_activation(&native_frame, &owner, 1, 0),
	      "native frame accepted an undersized activation stack");
	owner.rt_stack_size = 2;
	check(jit_native_frame_prepare_activation(&native_frame, &owner, 1, 0),
	      "owner-backed native frame did not prepare an activation");
	check(owner.top_rt_stack == owner.base_rt_stack + 1
	      && owner_stack[0].type == TYPE_STR
	      && !strcmp(owner_stack[0].v.str, "authoritative owner tag"),
	      "owner-backed native frame used stale payload or tag data");
	check(home_state[0] == JIT_HOME_OWNED
	      && owner_home[0].type == TYPE_STR,
	      "activation preparation consumed its native owner");
	free_var(*--owner.top_rt_stack);
	jit_native_frame_unbind_runtime(&native_frame);
	jit_native_frame_bind_runtime(&native_frame, stale_values,
	    sizeof(stale_values), owner_home, 1, home_state, owner_capacity);
	jit_native_frame_release_runtime(&native_frame);
	check(!native_frame.runtime_storage && !native_frame.owns_runtime
	      && owner_home[0].type == TYPE_STR
	      && !strcmp(owner_home[0].v.str, "authoritative owner tag"),
	      "borrowed native runtime release consumed caller storage");
	free_var(owner_home[0]);
	owner_program->num_borrowed_locals = 1;
	owner_program->borrowed_local_slots = allocate(sizeof(int));
	owner_program->borrowed_local_slots[0] = 0;
	owned_bytes = sizeof(stale_values) + 2 * sizeof(Var)
	    + sizeof(unsigned) + 1;
	owned_storage = mymalloc(owned_bytes, M_PROGRAM);
	memset(owned_storage, 0, owned_bytes);
	borrowed_home = (Var *) ((char *) owned_storage + sizeof(stale_values));
	owned_home = borrowed_home + 1;
	owned_capacity = (unsigned *) (owned_home + 1);
	owned_state = (unsigned char *) (owned_capacity + 1);
	borrowed_original.type = TYPE_STR;
	borrowed_original.v.str = str_dup("released borrowed local");
	borrowed_home[0] = var_ref(borrowed_original);
	owned_home[0].type = TYPE_STR;
	owned_home[0].v.str = str_dup("released native runtime");
	owned_state[0] = JIT_HOME_OWNED;
	owner_program->active_runtime_bytes = owned_bytes;
	jit_native_frame_bind_runtime(&native_frame, owned_storage, owned_bytes,
	    owned_home, 1, owned_state, owned_capacity);
	jit_native_frame_mark_runtime_owned(&native_frame);
	jit_native_frame_release_runtime(&native_frame);
	check(!native_frame.runtime_storage && !native_frame.owns_runtime
	      && owner_program->active_runtime_bytes == 0
	      && var_refcount(borrowed_original) == 1,
	      "owned native runtime release was incomplete");
	free_var(borrowed_original);

	owned_storage = mymalloc(owned_bytes, M_PROGRAM);
	memset(owned_storage, 0, owned_bytes);
	borrowed_home = (Var *) ((char *) owned_storage + sizeof(stale_values));
	owned_home = borrowed_home + 1;
	owned_capacity = (unsigned *) (owned_home + 1);
	owned_state = (unsigned char *) (owned_capacity + 1);
	borrowed_original.type = TYPE_STR;
	borrowed_original.v.str = str_dup("continuation borrowed local");
	borrowed_home[0] = var_ref(borrowed_original);
	owned_home[0].type = TYPE_STR;
	owned_home[0].v.str = str_dup("continuation owner home");
	owned_state[0] = JIT_HOME_OWNED;
	owner_program->active_runtime_bytes = owned_bytes;
	owned_continuation = jit_test_continuation_capture(owner_program, 1,
	    owned_storage, owned_storage, borrowed_home, owned_home, owned_state,
	    owned_capacity, owned_bytes, 0);
	check(owned_continuation && owned_continuation->owns_runtime,
	      "continuation did not adopt owned runtime storage");
	jit_continuation_free(owned_continuation);
	check(owner_program->active_runtime_bytes == 0
	      && var_refcount(borrowed_original) == 1,
	      "continuation runtime release was incomplete");
	free_var(borrowed_original);
	jit_program_free(owner_program);
    }

    {
	JITProgram *boundary_program = call_boundary_program();
	JITExecutionContext context;
	JITNativeFrame root;
	activation first = { 0 };
	activation second = { 0 };
	Var source[2];
	Var first_stack[2];
	Var second_stack[2];
	size_t runtime_before = boundary_program->active_runtime_bytes;

	source[0].type = TYPE_STR;
	source[0].v.str = str_dup("exact boundary stack");
	source[1] = new_list(1);
	source[1].v.list[1].type = TYPE_INT;
	source[1].v.list[1].v.num = 42;
	boundary_program->deopt_maps[1].num_locals = 0;
	jit_execution_context_init(&context, &root, boundary_program, env, 0, 1,
	    4, &ticks, &timed_out, &error, -1);
	check(jit_native_frame_capture_boundary(&root, source, 2, 1),
	      "native frame did not capture an exact boundary stack");
	check(source[0].type == TYPE_NONE && source[1].type == TYPE_NONE
	      && root.owns_boundary_stack && root.boundary_depth == 2
	      && root.boundary_map == 1
	      && boundary_program->active_runtime_bytes
		 == runtime_before + sizeof(source)
	      && jit_native_frame_verify(&context, &root),
	      "native boundary stack ownership is inconsistent");
	check(!jit_native_frame_capture_boundary(&root, source, 0, 1),
	      "native frame captured more than one boundary stack");
	first.base_rt_stack = first.top_rt_stack = first_stack;
	first.rt_stack_size = 2;
	second.base_rt_stack = second.top_rt_stack = second_stack;
	second.rt_stack_size = 2;
	check(jit_native_frame_prepare_activation(&root, &first, 1, 0)
	      && jit_native_frame_prepare_activation(&root, &second, 1, 0),
	      "native boundary stack was not retry-safe during preparation");
	jit_native_frame_release_boundary(&root);
	check(first.top_rt_stack == first.base_rt_stack + 2
	      && second.top_rt_stack == second.base_rt_stack + 2
	      && first_stack[0].type == TYPE_STR
	      && !strcmp(first_stack[0].v.str, "exact boundary stack")
	      && second_stack[1].type == TYPE_LIST
	      && second_stack[1].v.list[1].v.num == 42
	      && boundary_program->active_runtime_bytes == runtime_before,
	      "prepared boundary activation did not retain exact values");
	while (first.top_rt_stack > first.base_rt_stack)
	    free_var(*--first.top_rt_stack);
	while (second.top_rt_stack > second.base_rt_stack)
	    free_var(*--second.top_rt_stack);
	check(jit_execution_context_finish(&context, &root),
	      "boundary snapshot root frame did not detach cleanly");
	jit_program_free(boundary_program);
    }

    check(jit_program_dump_mir(program, check_mir_line, &mir_dump),
	  "MIR dump failed");
    check(mir_dump.lines > 0, "MIR dump was empty");
    check(mir_dump.found_source_marker,
	  "MIR dump did not contain PC and line information");
    {
	struct mir_dump tick_dump = { 0 };
	struct mir_dump exit_dump = { 0 };

	check(jit_program_dump_mir(two_ticks, check_mir_line, &tick_dump),
	      "two-tick MIR dump failed");
	check(tick_dump.timeout_checks == 1,
	      "basic block emitted redundant seconds-timeout checks");
	check(jit_program_dump_mir(duplicate_tick_exits, check_mir_line,
				   &exit_dump),
	      "duplicate-tick MIR dump failed");
	check(exit_dump.source_location_stores == 2,
	      "equivalent tick status exits were not shared");
	check(exit_dump.source_location_field_stores == 0,
	      "status exits wrote expanded source locations");
    }
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
    {
	JITProgramStats stats;

	jit_program_stats(program, &stats);
	check(stats.compile_attempts == 1 && stats.compile_successes == 1
	      && stats.compile_failures == 0,
	      "JIT compilation statistics are wrong");
	check(stats.metadata_bytes > sizeof(JITProgram)
	      && stats.runtime_bytes == 0
	      && stats.machine_code_bytes == program->machine_code_len
	      && stats.native_allocated_bytes >= stats.machine_code_bytes,
	      "JIT memory statistics are wrong");
	check(stats.accounted_bytes == stats.metadata_bytes + stats.runtime_bytes
	      + stats.native_allocated_bytes,
	      "JIT accounted byte total is wrong");
    }
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
    check_differential(modulus_power_two, env, 10, 0,
		       "power-of-two modulus differed from reference execution");
    check_differential(negative_modulus_power_two, env, 10, 0,
		       "negative power-of-two modulus differed from reference");
    check_differential(minimum_modulus_power_two, env, 10, 0,
		       "minimum power-of-two modulus differed from reference");
    check_differential(modulus_one, env, 10, 0,
		       "modulus by one differed from reference execution");
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
    check_differential(two_ticks, env, 10, 1,
		       "coalesced seconds abort differed from reference execution");
    check_differential(two_ticks, env, 2, 0,
		       "coalesced tick exhaustion differed from reference execution");
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
    check(deopt.guard_value[0] == 1 && deopt.guard_local[0] == 0,
	  "entry guard returned the wrong guarded value");
    check(deopt.guard_expected[0] == JIT_TYPE_MASK(TYPE_INT)
	  && deopt.guard_actual[0] == TYPE_STR,
	  "entry guard returned the wrong expected or actual type");
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

    /* Full boundary materialization moves an owned argument from its home. */
    {
	JITProgram *owned_call = owned_builtin_call_program(17);
	Var owned_env[1];

	owned_env[0].type = TYPE_STR;
	owned_env[0].v.str = str_dup("owned argument");
	ticks = 10;
	check(jit_program_execute(owned_call, owned_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_CALL_VERB,
	      "owned built-in argument did not reach its VM boundary");
	check(deopt.stack_depth == 1 && deopt_stack[0].type == TYPE_LIST
	      && deopt_stack[0].v.list[0].v.num == 1
	      && deopt_stack[0].v.list[1].type == TYPE_STR
	      && !strcmp(deopt_stack[0].v.list[1].v.str, "owned argument"),
	      "owned built-in argument was not materialized intact");
	check(owned_env[0].type == TYPE_LIST
	      && owned_env[0].v.list == deopt_stack[0].v.list
	      && var_refcount(owned_env[0]) == 2,
	      "owner-backed local was not reconstructed alongside the stack");
	free_var(deopt_stack[0]);
	free_var(owned_env[0]);
	jit_program_free(owned_call);
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
				    deopt_stack, 2, 1, 0, 0) == JIT_RUN_RETURNED,
	      "pass continuation did not return");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "passed"),
	      "pass continuation returned the wrong value");
	free_var(result);
	free_var(deopt_stack[0]);
	free_var(pass_env[0]);
	jit_program_free(pass_prog);

	pass_prog = builtin_call_program(9);
	pass_prog->deopt_maps[1].native_resume->valid = 0;
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
				    deopt_stack, 2, 1, 0, 0) == JIT_RUN_RETURNED,
	      "generic built-in continuation did not return");
	check(result.type == TYPE_INT && result.v.num == 41,
	      "generic built-in continuation returned the wrong value");
	free_var(deopt_stack[0]);
	free_var(pass_env[0]);
	jit_program_free(pass_prog);

	/* Native-only continuations need not promise bytecode rehydration. */
	pass_prog = builtin_call_program(17);
	pass_prog->deopt_maps[1].native_resume->rehydratable = 0;
	pass_args = new_list(0).v.list;
	pass_env[0].type = TYPE_LIST;
	pass_env[0].v.list = pass_args;
	{
	    JITContinuationFrame *continuation = 0;
	    Var returned;

	    check(jit_program_resume_map(pass_prog, pass_key) == -1,
		  "native-only built-in exposed a bytecode resume map");
	    check((jit_program_execute)(pass_prog, pass_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, 0,
					&continuation) == JIT_RUN_CALL_VERB,
		  "native-only built-in did not request a VM call");
	    check(continuation != 0,
		  "native-only built-in did not capture its continuation");
	    free_var(deopt_stack[0]);
	    returned.type = TYPE_INT;
	    returned.v.num = 42;
	    jit_continuation_set_result(continuation, returned);
	    check((jit_program_execute)(pass_prog, pass_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, continuation,
					0) == JIT_RUN_RETURNED,
		  "native-only built-in continuation did not return");
	    check(result.type == TYPE_INT && result.v.num == 42,
		  "native-only built-in continuation returned the wrong value");
	    jit_continuation_free(continuation);
	}
	free_var(pass_env[0]);
	jit_program_free(pass_prog);

	/* A statically typed float result is bitcast from the VM Var payload. */
	pass_prog = builtin_call_program(17);
	pass_prog->value_types[2] = TYPE_FLOAT;
	pass_prog->value_is_tagged[2] = 0;
	pass_prog->blocks->last->literal_type = TYPE_FLOAT;
	pass_args = new_list(0).v.list;
	pass_env[0].type = TYPE_LIST;
	pass_env[0].v.list = pass_args;
	ticks = 10;
	check(jit_program_execute(pass_prog, pass_env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_CALL_VERB,
	      "float built-in did not request a VM call");
	free_var(deopt_stack[0]);
	deopt_stack[0].type = TYPE_FLOAT;
	deopt_stack[0].v.fnum = box_fl(1.5);
	check((jit_program_execute)(pass_prog, pass_env, &result, &ticks,
				    &timed_out, &error, 0, &deopt,
				    deopt_stack, 2, 1, 0, 0) == JIT_RUN_RETURNED,
	      "float built-in continuation did not return");
	check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 1.5,
	      "float built-in continuation returned the wrong value");
	free_var(result);
	free_var(deopt_stack[0]);
	free_var(pass_env[0]);
	jit_program_free(pass_prog);
    }

    /* Specialized built-in fallback reconstructs the bytecode argument list. */
    {
	JITProgram *builtin_deopt = string_length_program("hello");
	JITInstruction *length_instr = builtin_deopt->blocks->first->next;

	length_instr->kind = HIR_TAC_DEOPT;
	ticks = 10;
	check(jit_program_execute(builtin_deopt, env, &result, &ticks,
				  &timed_out, &error, 0, &deopt, deopt_stack)
	      == JIT_RUN_FALLBACK,
	      "specialized built-in fallback did not deopt");
	check(deopt.stack_depth == 1 && deopt_stack[0].type == TYPE_LIST,
	      "specialized built-in fallback did not pack its arguments");
	check(deopt_stack[0].v.list[0].v.num == 1
	      && deopt_stack[0].v.list[1].type == TYPE_STR
	      && !strcmp(deopt_stack[0].v.list[1].v.str, "hello"),
	      "specialized built-in fallback packed the wrong argument");
	free_var(deopt_stack[0]);
	jit_program_free(builtin_deopt);
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
	    non_tail->deopt_maps[1].native_resume->valid = 0;
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
				    deopt_stack, 2, 1, 0, 0) == JIT_RUN_RETURNED,
	      "call_verb continuation did not return");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "returned"),
	      "call_verb continuation returned the wrong value");
	free_var(result);
	free_var(deopt_stack[0]);
	{
	    JITContinuationFrame *continuation = 0;
	    activation owner = { 0 };
	    Var owner_env[3];
	    Var owner_stack[4];
	    int i;

	    ticks = 10;
	    check((jit_program_execute)(call_prog, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, 0,
					&continuation) == JIT_RUN_CALL_VERB,
		  "failed-call boundary did not capture a continuation");
	    for (i = 0; i < 3; i++) {
		owner_env[i].type = TYPE_INT;
		owner_env[i].v.num = 99;
	    }
	    owner.rt_env = owner_env;
	    owner.base_rt_stack = owner_stack;
	    owner.top_rt_stack = owner_stack;
	    owner.rt_stack_size = 4;
	    owner.temp.type = TYPE_NONE;
	    jit_continuation_attach(continuation, &owner);
	    {
		activation relocated = { 0 };

		check(!jit_continuation_is_dispatched(continuation),
		      "fresh continuation was marked dispatched");
		jit_continuation_relocate(continuation, &relocated);
		check(!owner.jit_continuation
		      && relocated.jit_continuation == continuation,
		      "continuation relocation did not update both owners");
		jit_continuation_relocate(continuation, &owner);
	    }
	    check(jit_continuation_materialize_boundary(&owner, deopt_stack, 3),
		  "failed-call boundary continuation did not materialize");
	    check(!owner.jit_continuation
		  && owner.top_rt_stack == owner.base_rt_stack + 3,
		  "failed-call boundary produced the wrong stack depth");
	    check(owner_stack[0].type == TYPE_OBJ
		  && owner_stack[0].v.obj == 0
		  && owner_stack[1].type == TYPE_STR
		  && !strcmp(owner_stack[1].v.str, "test")
		  && owner_stack[2].type == TYPE_LIST
		  && owner_stack[2].v.list[0].v.num == 0,
		  "failed-call boundary reconstructed the wrong operands");
	    check(owner_env[0].type == TYPE_OBJ && owner_env[0].v.obj == 0
		  && owner_env[1].type == TYPE_STR
		  && !strcmp(owner_env[1].v.str, "test")
		  && owner_env[2].type == TYPE_LIST
		  && owner_env[2].v.list[0].v.num == 0,
		  "failed-call boundary did not restore operand-backed locals");
	    while (owner.top_rt_stack > owner.base_rt_stack)
		free_var(*--owner.top_rt_stack);
	    for (i = 0; i < 3; i++) {
		free_var(owner_env[i]);
		free_var(deopt_stack[i]);
	    }
	}
	{
	    JITContinuationFrame *continuation = 0;
	    activation owner = { 0 };
	    Var shadow_stack[3];
	    Var returned;

	    ticks = 10;
	    check((jit_program_execute)(call_prog, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, 0,
					&continuation) == JIT_RUN_CALL_VERB,
		  "compact call_verb did not request a VM call");
	    check(continuation && !deopt.materialized && deopt.stack_depth == 3,
		  "call_verb did not capture a compact continuation");
	    owner.base_rt_stack = shadow_stack;
	    owner.top_rt_stack = shadow_stack + 3;
	    jit_continuation_attach(continuation, &owner);
	    jit_continuation_mark_dispatched(continuation);
	    check(jit_continuation_is_dispatched(continuation),
		  "marked continuation did not report dispatched state");
	    check(owner.top_rt_stack == owner.base_rt_stack,
		  "dispatched continuation left compact operands live");
	    free_var(deopt_stack[1]);
	    free_var(deopt_stack[2]);
	    returned.type = TYPE_STR;
	    returned.v.str = str_dup("compact returned");
	    jit_continuation_set_result(continuation, returned);
	    check((jit_program_execute)(call_prog, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, continuation,
					0) == JIT_RUN_RETURNED,
		  "compact call_verb continuation did not return");
	    jit_continuation_free(continuation);
	    check(result.type == TYPE_STR
		  && !strcmp(result.v.str, "compact returned"),
		  "compact call_verb continuation returned the wrong value");
	    free_var(result);
	}
	{
	    JITProgram *float_caller = call_verb_preserved_float_program();
	    JITContinuationFrame *continuation = 0;
	    Var float_env[4];
	    Var returned;

	    float_env[0].type = TYPE_OBJ;
	    float_env[0].v.obj = 0;
	    float_env[1].type = TYPE_STR;
	    float_env[1].v.str = str_dup("test");
	    float_env[2] = new_list(0);
	    float_env[3].type = TYPE_FLOAT;
	    float_env[3].v.fnum = box_fl(12.5);
	    ticks = 10;
	    check((jit_program_execute)(float_caller, float_env, &result, &ticks,
					  &timed_out, &error, 0, &deopt,
					  deopt_stack, 2, -1, 0,
					  &continuation) == JIT_RUN_CALL_VERB,
		  "float-preserving caller did not request a VM call");
	    check(continuation != 0,
		  "float-preserving caller did not capture a continuation");
	    jit_continuation_mark_dispatched(continuation);
	    free_var(deopt_stack[1]);
	    free_var(deopt_stack[2]);
	    returned.type = TYPE_INT;
	    returned.v.num = 99;
	    jit_continuation_set_result(continuation, returned);
	    check((jit_program_execute)(float_caller, float_env, &result, &ticks,
					  &timed_out, &error, 0, &deopt,
					  deopt_stack, 2, -1, continuation,
					  0) == JIT_RUN_RETURNED,
		  "float-preserving continuation did not resume natively");
	    check(result.type == TYPE_FLOAT && fl_unbox(result.v.fnum) == 12.5,
		  "native continuation did not preserve its float local");
	    jit_continuation_free(continuation);
	    free_var(result);
	    free_var(float_env[1]);
	    free_var(float_env[2]);
	    free_var(float_env[3]);
	    jit_program_free(float_caller);
	}
	{
	    JITProgram *property_caller =
		call_verb_preserved_property_program();
	    JITContinuationFrame *continuation = 0;
	    Var property_env[5];
	    Var property;
	    Var returned;
	    int refs;

	    property_env[0].type = TYPE_OBJ;
	    property_env[0].v.obj = 0;
	    property_env[1].type = TYPE_STR;
	    property_env[1].v.str = str_dup("test");
	    property_env[2] = new_list(0);
	    property_env[3].type = TYPE_STR;
	    property_env[3].v.str = str_dup("value");
	    property_env[4].type = TYPE_NONE;
	    property = new_list(1);
	    property.v.list[1].type = TYPE_STR;
	    property.v.list[1].v.str = str_dup("preserved property");
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ticks = 10;
	    check((jit_program_execute)(property_caller, property_env, &result,
					  &ticks, &timed_out, &error, 0,
					  &deopt, deopt_stack, 2, -1, 0,
					  &continuation) == JIT_RUN_CALL_VERB,
		  "property-preserving caller did not request a VM call");
	    check(continuation && continuation->owns_runtime
		  && var_refcount(property) == refs + 1,
		  "property result was not retained by the continuation runtime");
	    jit_continuation_mark_dispatched(continuation);
	    free_var(deopt_stack[1]);
	    free_var(deopt_stack[2]);
	    returned.type = TYPE_INT;
	    returned.v.num = 99;
	    jit_continuation_set_result(continuation, returned);
	    check((jit_program_execute)(property_caller, property_env, &result,
					  &ticks, &timed_out, &error, 0,
					  &deopt, deopt_stack, 2, -1,
					  continuation, 0) == JIT_RUN_RETURNED,
		  "property-preserving continuation did not resume natively");
	    check(result.type == TYPE_LIST && result.v.list == property.v.list
		  && var_refcount(property) == refs + 1,
		  "native continuation corrupted its owned property result");
	    jit_continuation_free(continuation);
	    free_var(result);
	    hir_test_reset_property();
	    free_var(property);
	    free_var(property_env[1]);
	    free_var(property_env[2]);
	    free_var(property_env[3]);
	    jit_program_free(property_caller);
	}
	{
	    JITContinuationFrame *continuation = 0;
	    JITExecutionContext context;
	    JITNativeFrame root;
	    JITNativeFrame child;
	    JITCallerResume native_resume;
	    activation owner = { 0 };
	    activation promoted = { 0 };
	    Program bytecode = { 0 };
	    ResumePoint point = { 0 };
	    Var promoted_env[3];
	    Var promoted_stack[3];
	    Var returned;
	    size_t runtime_before = call_prog->active_runtime_bytes;
	    int i;

	    ticks = 10;
	    check((jit_program_execute)(call_prog, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, 0,
					&continuation) == JIT_RUN_CALL_VERB,
		"borrowed-runtime call did not capture a continuation");
	    check(continuation && continuation->owns_runtime
		&& !continuation->runtime_owner
		&& call_prog->active_runtime_bytes > runtime_before,
		"captured continuation did not own its runtime");
	    jit_execution_context_init(&context, &root, call_prog, deep_env,
		0, 1, 4, &ticks, &timed_out, &error, -1);
	    jit_continuation_attach(continuation, &owner);
	    check(jit_native_frame_adopt_continuation_runtime(&root,
		continuation), "native frame did not adopt continuation runtime");
	    check(root.owns_runtime && root.runtime_borrower == continuation
		&& !continuation->owns_runtime
		&& continuation->runtime_owner == &root
		&& !owner.jit_continuation && !continuation->owner
		&& jit_native_frame_verify(&context, &root),
		"adopted continuation runtime ownership is inconsistent");
	    check(jit_native_frame_continuation_matches(&root,
		continuation->map_id)
		&& !jit_native_frame_continuation_matches(&root,
		    continuation->map_id + 1),
		"native frame continuation map matching is wrong");
	    bytecode.num_var_names = 3;
	    for (i = 0; i < 3; i++)
		promoted_env[i] = var_ref(deep_env[i]);
	    promoted.prog = &bytecode;
	    promoted.rt_env = promoted_env;
	    promoted.base_rt_stack = promoted.top_rt_stack = promoted_stack;
	    promoted.rt_stack_size = 3;
	    promoted.temp.type = TYPE_NONE;
	    check(jit_native_frame_capture_boundary(&root, deopt_stack, 3, 1),
		"borrowed-runtime boundary operands were not captured");
	    check(jit_native_frame_prepare_activation(&root, &promoted, 1, 0),
		"borrowed-runtime boundary was not prepared for interpretation");
	    check(promoted.top_rt_stack == promoted.base_rt_stack + 3
		  && promoted_env[0].type == TYPE_OBJ
		  && promoted_env[1].type == TYPE_STR
		  && promoted_env[2].type == TYPE_LIST
		  && promoted_stack[0].type == TYPE_OBJ
		  && promoted_stack[1].type == TYPE_STR
		  && promoted_stack[2].type == TYPE_LIST
		  && promoted.pc == deopt.bytecode_pc
		  && promoted.error_pc == deopt.error_pc,
		"borrowed-runtime boundary restored the wrong activation");
	    for (i = 0; i < 3; i++)
		free_var(promoted_env[i]);
	    while (promoted.top_rt_stack > promoted.base_rt_stack)
		free_var(*--promoted.top_rt_stack);
	    jit_native_frame_release_boundary(&root);
	    for (i = 0; i < 3; i++)
		promoted_env[i] = var_ref(deep_env[i]);
	    point.key = call_prog->deopt_maps[1].resume_key;
	    point.pc = 79;
	    point.error_pc = 80;
	    point.kind = RP_CALL;
	    hir_test_set_resume_point(&point);
	    check(jit_native_frame_prepare_activation(&root, &promoted, 1, 1),
		"dispatched borrowed-runtime frame was not prepared");
	    check(!promoted.jit_continuation
		  && promoted.top_rt_stack == promoted.base_rt_stack
		  && promoted_env[0].type == TYPE_OBJ
		  && promoted_env[1].type == TYPE_STR
		  && promoted_env[2].type == TYPE_LIST
		  && promoted.pc == point.pc
		  && promoted.error_pc == point.error_pc,
		"dispatched borrowed-runtime frame restored the wrong activation");
	    hir_test_set_resume_point(0);
	    for (i = 0; i < 3; i++)
		free_var(promoted_env[i]);
	    check(!jit_native_frame_adopt_continuation_runtime(&root,
		continuation), "continuation runtime was adopted more than once");
	    memset(&native_resume, 0, sizeof(native_resume));
	    native_resume.caller = &root;
	    native_resume.continuation = continuation;
	    native_resume.map_id = continuation->map_id;
	    native_resume.bytecode_pc = deopt.bytecode_pc;
	    native_resume.error_pc = deopt.error_pc;
	    native_resume.result_home = UINT_MAX;
	    native_resume.state = JIT_RESUME_PREPARING;
	    check(jit_execution_context_push_compact(&context, &child,
		call_prog, deep_env, &native_resume, -1),
		"continuation-backed compact dispatch failed");
	    returned.type = TYPE_STR;
	    returned.v.str = str_dup("borrowed runtime returned");
	    check(jit_execution_context_return_compact(&context, &child,
		&returned), "continuation-backed compact return failed");
	    check(returned.type == TYPE_NONE
		&& native_resume.state == JIT_RESUME_RETURNED
		&& context.current_frame == &root,
		"compact return did not transfer its result to the continuation");
	    check(jit_program_execute_in_context(call_prog, &context, &root,
		deep_env, &result, &ticks, &timed_out, &error, 0, &deopt,
		deopt_stack, 2, -1, continuation, 0) == JIT_RUN_RETURNED,
		"borrowed continuation runtime did not resume");
	    check(root.runtime_storage && root.runtime_borrower == continuation
		&& continuation->runtime_owner == &root
		&& result.type == TYPE_STR
		&& !strcmp(result.v.str, "borrowed runtime returned"),
		"borrowed continuation resume corrupted runtime ownership");
	    free_var(result);
	    check(jit_native_frame_return_continuation_runtime(&root,
		continuation),
		"native frame did not return continuation runtime ownership");
	    check(!root.runtime_storage && !root.runtime_borrower
		&& continuation->owns_runtime && !continuation->runtime_owner,
		"returned continuation runtime ownership is inconsistent");
	    jit_continuation_attach(continuation, &owner);
	    jit_continuation_free(continuation);
	    check(!owner.jit_continuation
		&& call_prog->active_runtime_bytes == runtime_before,
		"returned continuation did not release runtime exactly once");
	    check(jit_execution_context_finish(&context, &root),
		"borrowed-runtime root frame did not detach cleanly");

	    continuation = 0;
	    ticks = 10;
	    check((jit_program_execute)(call_prog, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, 0,
					&continuation) == JIT_RUN_CALL_VERB,
		"cancellation test did not capture a continuation");
	    free_var(deopt_stack[1]);
	    free_var(deopt_stack[2]);
	    jit_execution_context_init(&context, &root, call_prog, deep_env,
		0, 1, 4, &ticks, &timed_out, &error, -1);
	    check(jit_native_frame_adopt_continuation_runtime(&root,
		continuation),
		"cancellation frame did not adopt continuation runtime");
	    jit_continuation_free(continuation);
	    check(!root.runtime_borrower && root.owns_runtime
		  && root.runtime_storage
		  && call_prog->active_runtime_bytes > runtime_before,
		"continuation cancellation corrupted frame-owned runtime");
	    jit_native_frame_release_runtime(&root);
	    check(!root.runtime_storage
		  && call_prog->active_runtime_bytes == runtime_before,
		"cancelled continuation runtime was not released exactly once");
	    check(jit_execution_context_finish(&context, &root),
		"cancellation frame did not detach cleanly");
	}
	{
	    JITProgram *sparse = call_verb_program();
	    JITDeoptMap *sparse_map = &sparse->deopt_maps[1];
	    JITContinuationFrame *continuation = 0;
	    activation owner = { 0 };
	    Var owner_env[3];
	    Var owner_stack[4];
	    int i;

	    sparse_map->num_local_values = 2;
	    sparse_map->local_values[1].slot = 2;
	    sparse_map->local_values[1].value = 3;
	    myfree(sparse_map->native_resume->values, M_PROGRAM);
	    sparse_map->native_resume->num_values = 4;
	    sparse_map->native_resume->values =
		allocate(sizeof(JITResumeValue) * 4);
	    sparse_map->native_resume->values[0].value = 1;
	    sparse_map->native_resume->values[0].source = JIT_RESUME_LOCAL;
	    sparse_map->native_resume->values[0].index = 0;
	    sparse_map->native_resume->values[1].value = 2;
	    sparse_map->native_resume->values[1].source = JIT_RESUME_STACK;
	    sparse_map->native_resume->values[1].index = 1;
	    sparse_map->native_resume->values[2].value = 3;
	    sparse_map->native_resume->values[2].source = JIT_RESUME_LOCAL;
	    sparse_map->native_resume->values[2].index = 2;
	    sparse_map->native_resume->values[3].value = 4;
	    sparse_map->native_resume->values[3].source = JIT_RESUME_RESULT;
	    owner_env[0].type = TYPE_OBJ;
	    owner_env[0].v.obj = 99;
	    owner_env[1].type = TYPE_STR;
	    owner_env[1].v.str = str_dup("resident local");
	    owner_env[2] = new_list(0);
	    owner.rt_env = owner_env;
	    owner.base_rt_stack = owner_stack;
	    owner.top_rt_stack = owner_stack;
	    ticks = 10;
	    check((jit_program_execute)(sparse, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, -1, 0,
					&continuation) == JIT_RUN_CALL_VERB,
		  "sparse continuation did not request a VM call");
	    check(continuation != 0, "sparse continuation was not captured");
	    if (continuation) {
		jit_continuation_attach(continuation, &owner);
		check(jit_continuation_materialize(&owner),
		      "sparse continuation did not materialize");
	    }
	    for (i = 0; i < 3; i++)
		free_var(deopt_stack[i]);
	    check(owner_env[1].type == TYPE_STR
		  && !strcmp(owner_env[1].v.str, "resident local"),
		  "sparse continuation replaced an environment local");
	    if (owner.jit_continuation)
		jit_continuation_free(owner.jit_continuation);
	    while (owner.top_rt_stack > owner.base_rt_stack)
		free_var(*--owner.top_rt_stack);
	    free_var(owner_env[0]);
	    free_var(owner_env[1]);
	    free_var(owner_env[2]);
	    jit_program_free(sparse);
	}
	{
	    JITProgram *fallthrough = call_verb_program();
	    JITInstruction *call = fallthrough->blocks->first;
	    JITInstruction *terminal = instruction(HIR_TAC_LABEL);
	    JITInstruction *replaced;

	    while (call->kind != HIR_TAC_CALL_VERB)
		call = call->next;
	    replaced = call->next;
	    call->next = terminal;
	    fallthrough->blocks->last = terminal;
	    myfree(replaced, M_PROGRAM);
	    deopt_stack[0].type = TYPE_INT;
	    deopt_stack[0].v.num = 17;
	    check((jit_program_execute)(fallthrough, deep_env, &result, &ticks,
					&timed_out, &error, 0, &deopt,
					deopt_stack, 2, 1, 0, 0) == JIT_RUN_RETURNED,
		  "fallthrough continuation did not return");
	    check(result.type == TYPE_INT && result.v.num == 0,
		  "fallthrough continuation did not return zero");
	    jit_program_free(fallthrough);
	}
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

	{
	    const char *static_value = str_dup("static type");
	    JITProgram *typeof_str = unary_program(
		(Num) (uintptr_t) static_value, HIR_OP_TYPEOF);
	    JITInstruction *constant = typeof_str->blocks->first;
	    JITInstruction *unary = constant->next;

	    constant->literal_type = TYPE_STR;
	    unary->literal = TYPE_STR;
	    ticks = 10;
	    check(jit_program_execute(typeof_str, env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED, "string typeof execution failed");
	    check(result.type == TYPE_INT && result.v.num == _TYPE_STR,
		  "string typeof returned internal runtime tag");
	    jit_program_free(typeof_str);
	}
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
	    JITContinuationFrame *continuation = 0;
	    JITDeoptMap *map = &str_length->deopt_maps[1];
	    Var returned;

	    map->resume_key.code_unit = 0;
	    map->resume_key.site = 1;
	    map->native_resume = allocate(sizeof(JITNativeResume));
	    map->native_resume->valid = 1;
	    map->native_resume->rehydratable = 1;
	    map->native_resume->num_values = 1;
	    map->native_resume->values = allocate(sizeof(JITResumeValue));
	    map->native_resume->values[0].value = 2;
	    map->native_resume->values[0].source = JIT_RESUME_RESULT;

	    ticks = 10;
	    check((jit_program_execute)(str_length, 0, &result, &ticks,
				       &timed_out, &error, 0, &protected_deopt,
				       protected_stack, 2, -1, 0,
				       &continuation)
		  == JIT_RUN_CALL_VERB, "protected length did not enter VM");
	    check(protected_deopt.reason == JIT_DEOPT_ARITHMETIC_TYPE
		  && protected_deopt.boundary == JIT_BOUNDARY_BUILTIN,
		  "protected length lost its boundary classification");
	    check(continuation != 0,
		  "protected length did not capture a native continuation");
	    check(protected_deopt.stack_depth == 1
		  && protected_stack[0].type == TYPE_LIST
		  && protected_stack[0].v.list[0].v.num == 1
		  && protected_stack[0].v.list[1].type == TYPE_STR,
		  "protected length did not materialize its arguments");
	    free_var(protected_stack[0]);
	    returned.type = TYPE_INT;
	    returned.v.num = 5;
	    jit_continuation_set_result(continuation, returned);
	    check((jit_program_execute)(str_length, 0, &result, &ticks,
				       &timed_out, &error, 0, &protected_deopt,
				       protected_stack, 2, -1,
				       continuation, 0) == JIT_RUN_RETURNED,
		  "protected length continuation did not return");
	    check(result.type == TYPE_INT && result.v.num == 5,
		  "protected length continuation returned the wrong value");
	    jit_continuation_free(continuation);
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

	JITProgram *duplicate_str = duplicate_owned_string_program();
	ticks = 10;
	check(jit_program_execute(duplicate_str, 0, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED,
	      "duplicate owned string operands did not execute natively");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "abab"),
	      "duplicate owned string operands returned the wrong value");
	free_var(result);
	jit_program_free(duplicate_str);

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

    /* A tagged object operand can execute parent() natively. */
    {
	JITProgram *tagged = tagged_parent_program();
	Var env[1];

	env[0] = new_list(1);
	env[0].v.list[1].type = TYPE_OBJ;
	env[0].v.list[1].v.obj = 1;
	ticks = 10;
	check(jit_program_execute(tagged, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0) == JIT_RUN_RETURNED,
	      "tagged parent object did not execute natively");
	check(result.type == TYPE_OBJ && result.v.obj == 0,
	      "tagged parent returned the wrong object");
	free_var(result);

	env[0].v.list[1].type = TYPE_INT;
	env[0].v.list[1].v.num = 1;
	ticks = 10;
	check(jit_program_execute(tagged, env, &result, &ticks, &timed_out,
				  &error, 0, &deopt, 0) == JIT_RUN_FALLBACK,
	      "tagged parent non-object did not fallback");
	check(deopt.bytecode_pc == 31 && deopt.operation == HIR_OP_PARENT,
	      "tagged parent fallback used the wrong deopt map");
	free_var(env[0]);
	jit_program_free(tagged);
    }

    /* A tagged object operand can execute valid() natively. */
    {
	JITProgram *tagged = tagged_unary_program(HIR_OP_VALID);
	Var env[1];

	env[0].type = TYPE_OBJ;
	env[0].v.obj = 1;
	ticks = 10;
	check(jit_program_execute(tagged, env, &result, &ticks, &timed_out,
				  &error, 0, 0, 0) == JIT_RUN_RETURNED,
	      "tagged valid object did not execute natively");
	check(result.type == TYPE_INT && result.v.num == 1,
	      "tagged valid returned the wrong result");
	free_var(result);

	env[0].type = TYPE_INT;
	env[0].v.num = 1;
	ticks = 10;
	check(jit_program_execute(tagged, env, &result, &ticks, &timed_out,
				  &error, 0, &deopt, 0) == JIT_RUN_FALLBACK,
	      "tagged valid non-object did not fallback");
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
	JITProgram *tagged_eq = list_index_tagged_consumer_program(HIR_OP_EQ,
							      TYPE_STR);
	JITProgram *tagged_float_eq = list_index_tagged_consumer_program(HIR_OP_EQ,
								    TYPE_FLOAT);
	JITProgram *tagged_in = list_index_tagged_consumer_program(HIR_OP_IN,
							      TYPE_LIST);
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
	free_var(tagged_env[0].v.list[1]);
	tagged_env[0].v.list[1].type = TYPE_FLOAT;
	tagged_env[0].v.list[1].v.fnum = box_fl(1.5);
	ticks = 10;
	check(jit_program_execute(tagged_float_eq, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED && result.type == TYPE_INT
	      && result.v.num == 1,
	      "tagged equality with a static float returned the wrong value");
	free_var(tagged_env[0]);
	free_var(tagged_env[1]);
	jit_program_free(tagged_eq);
	jit_program_free(tagged_float_eq);
	jit_program_free(tagged_in);
    }

    /* Float payloads cross raw-value helper ABIs without changing mode. */
    {
	JITProgram *singleton = float_singleton_program();

	ticks = 10;
	check(jit_program_execute(singleton, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0) == JIT_RUN_RETURNED,
	      "float singleton did not execute natively");
	check(result.type == TYPE_LIST && result.v.list[0].v.num == 1
	      && result.v.list[1].type == TYPE_FLOAT
	      && fl_unbox(result.v.list[1].v.fnum) == 1.5,
	      "float singleton returned the wrong value");
	free_var(result);
	jit_program_free(singleton);
    }

    /* Type-transparent consumers accept every core user-visible runtime type. */
    {
	const var_type types[] = {TYPE_STR, TYPE_LIST, TYPE_OBJ, TYPE_ERR};
	unsigned i;

	for (i = 0; i < sizeof(types) / sizeof(types[0]); i++) {
	    JITProgram *typed_not = typed_unary_lowering_program(HIR_OP_NOT,
		types[i], TYPE_INT, 0, 0, 0);
	    Var typed_env[1];
	    int expected;

	    typed_not->blocks->first->literal_type = types[i];
	    typed_env[0] = tagged_test_value(types[i]);
	    expected = !is_true(typed_env[0]);
	    ticks = 10;
	    check(jit_program_execute(typed_not, typed_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "statically typed truth test did not execute natively");
	    check(result.type == TYPE_INT && result.v.num == expected,
		  "statically typed truth test returned the wrong value");
	    free_var(typed_env[0]);
	    jit_program_free(typed_not);
	}
    }

#ifdef WAIF_CORE
    {
	JITProgram *complex_guard = tagged_guard_instruction_program();
	JITInstruction *guard = complex_guard->blocks->first->next;
	const var_type types[] = {TYPE_LIST, TYPE_WAIF};
	unsigned i;

	guard->guarded_type_masks[0] = JIT_TYPE_MASK(TYPE_LIST)
	    | JIT_TYPE_MASK(TYPE_WAIF);
	for (i = 0; i < sizeof(types) / sizeof(types[0]); i++) {
	    Var guarded_env[1];

	    guarded_env[0] = tagged_test_value(types[i]);
	    ticks = 10;
	    check(jit_program_execute(complex_guard, guarded_env, &result,
				      &ticks, &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED && result.type == types[i],
		  "complex tagged guard rejected an accepted runtime type");
	    free_var(result);
	    free_var(guarded_env[0]);
	}
	jit_program_free(complex_guard);
    }
#endif

    {
	JITProgram *tagged_typeof = tagged_unary_program(HIR_OP_TYPEOF);
	JITProgram *tagged_not = tagged_unary_program(HIR_OP_NOT);
	JITProgram *tagged_eq = tagged_binary_program(HIR_OP_EQ);
	JITProgram *tagged_in = tagged_binary_program(HIR_OP_IN);
	JITProgram *tagged_singleton = tagged_unary_result_program(
	    HIR_OP_MAKE_SINGLETON_LIST, TYPE_LIST);
	JITProgram *tagged_append = tagged_binary_result_program(
	    HIR_OP_LIST_ADD_TAIL, TYPE_LIST);
	const var_type types[] = {
	    TYPE_INT, TYPE_OBJ, TYPE_STR, TYPE_ERR, TYPE_LIST, TYPE_FLOAT,
#ifdef WAIF_CORE
	    TYPE_WAIF,
#endif
	};
	unsigned i;

	for (i = 0; i < sizeof(types) / sizeof(types[0]); i++) {
	    Var tagged_env[2];
	    int truth;

	    tagged_env[0] = tagged_test_value(types[i]);
	    truth = is_true(tagged_env[0]);
	    ticks = 10;
	    check(jit_program_execute(tagged_typeof, tagged_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "tagged typeof runtime type did not execute natively");
	    check(result.type == TYPE_INT
		  && result.v.num == (types[i] & TYPE_DB_MASK),
		  "tagged typeof returned the wrong runtime type");

	    ticks = 10;
	    check(jit_program_execute(tagged_not, tagged_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "tagged truth test runtime type did not execute natively");
	    check(result.type == TYPE_INT && result.v.num == !truth,
		  "tagged truth test returned the wrong value");

	    tagged_env[1] = var_ref(tagged_env[0]);
	    ticks = 10;
	    check(jit_program_execute(tagged_eq, tagged_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "tagged equality runtime type did not execute natively");
	    check(result.type == TYPE_INT && result.v.num == 1,
		  "tagged equality returned the wrong value");
	    free_var(tagged_env[1]);

	    tagged_env[1] = new_list(1);
	    tagged_env[1].v.list[1] = var_ref(tagged_env[0]);
	    ticks = 10;
	    check(jit_program_execute(tagged_in, tagged_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "tagged membership runtime type did not execute natively");
	    check(result.type == TYPE_INT && result.v.num == 1,
		  "tagged membership returned the wrong value");
	    free_var(tagged_env[1]);

	    ticks = 10;
	    check(jit_program_execute(tagged_singleton, tagged_env, &result,
				      &ticks, &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "tagged singleton runtime type did not execute natively");
	    check(result.type == TYPE_LIST && result.v.list[0].v.num == 1
		  && result.v.list[1].type == types[i]
		  && equality(result.v.list[1], tagged_env[0], 1),
		  "tagged singleton did not preserve its element");
	    free_var(result);

	    tagged_env[1] = tagged_env[0];
	    tagged_env[0] = new_list(0);
	    ticks = 10;
	    check(jit_program_execute(tagged_append, tagged_env, &result, &ticks,
				      &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "tagged list tail runtime type did not execute natively");
	    check(result.type == TYPE_LIST && result.v.list[0].v.num == 1
		  && result.v.list[1].type == types[i]
		  && equality(result.v.list[1], tagged_env[1], 1),
		  "tagged list tail did not preserve its element");
	    free_var(result);
	    free_var(tagged_env[0]);
	    free_var(tagged_env[1]);
	}
	jit_program_free(tagged_typeof);
	jit_program_free(tagged_not);
	jit_program_free(tagged_eq);
	jit_program_free(tagged_in);
	jit_program_free(tagged_singleton);
	jit_program_free(tagged_append);
    }

    /* Tagged absolute value accepts integers and guards other runtime types. */
    {
	JITProgram *tagged_abs = tagged_unary_program(HIR_OP_ABS);
	Var tagged_env[1];

	tagged_abs->value_is_tagged[2] = 1;
	tagged_env[0].type = TYPE_INT;
	tagged_env[0].v.num = -42;
	ticks = 10;
	check(jit_program_execute(tagged_abs, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "tagged abs executed natively");
	check(result.type == TYPE_INT && result.v.num == 42,
	      "tagged abs returned the wrong value");

	tagged_env[0].type = TYPE_STR;
	tagged_env[0].v.str = str_dup("not a number");
	ticks = 10;
	check(jit_program_execute(tagged_abs, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK,
	      "tagged non-integer abs did not deoptimize");
	free_var(tagged_env[0]);
	jit_program_free(tagged_abs);
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

    /* Overloaded addition dispatches only semantically valid type pairs. */
    {
	JITProgram *tagged_add = tagged_binary_program(HIR_OP_ADD);
	JITProgram *typed_left_add = tagged_binary_program(HIR_OP_ADD);
	JITProgram *typed_right_add = tagged_binary_program(HIR_OP_ADD);
	Var tagged_env[2];
	JITInstruction *typed_load;

	typed_load = typed_left_add->blocks->first;
	typed_left_add->value_is_tagged[1] = 0;
	typed_left_add->value_types[1] = TYPE_STR;
	typed_load->literal_type = TYPE_STR;
	typed_load = typed_right_add->blocks->first->next;
	typed_right_add->value_is_tagged[2] = 0;
	typed_right_add->value_types[2] = TYPE_STR;
	typed_load->literal_type = TYPE_STR;

	tagged_env[0].type = tagged_env[1].type = TYPE_INT;
	tagged_env[0].v.num = 20;
	tagged_env[1].v.num = 22;
	ticks = 10;
	check(jit_program_execute(tagged_add, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "tagged integer addition executed natively");
	check(result.type == TYPE_INT && result.v.num == 42,
	      "tagged integer addition returned the wrong value");

	tagged_env[0].type = tagged_env[1].type = TYPE_STR;
	tagged_env[0].v.str = str_dup("hello ");
	tagged_env[1].v.str = str_dup("world");
	ticks = 10;
	check(jit_program_execute(tagged_add, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED, "tagged string addition executed natively");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "hello world"),
	      "tagged string addition returned the wrong value");
	free_var(result);

	ticks = 10;
	check(jit_program_execute(typed_left_add, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED,
	      "typed-left string addition did not execute natively");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "hello world"),
	      "typed-left string addition returned the wrong value");
	free_var(result);
	free_var(tagged_env[0]);
	free_var(tagged_env[1]);

	tagged_env[0].type = TYPE_STR;
	tagged_env[0].v.str = str_dup("hello ");
	tagged_env[1].type = TYPE_STR;
	tagged_env[1].v.str = str_dup("world");
	ticks = 10;
	check(jit_program_execute(typed_right_add, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_RETURNED,
	      "typed-right string addition did not execute natively");
	check(result.type == TYPE_STR && !strcmp(result.v.str, "hello world"),
	      "typed-right string addition returned the wrong value");
	free_var(result);
	free_var(tagged_env[0]);
	free_var(tagged_env[1]);

	tagged_env[0].type = TYPE_STR;
	tagged_env[0].v.str = str_dup("hello ");
	tagged_env[1].type = TYPE_INT;
	tagged_env[1].v.num = 1;
	ticks = 10;
	check(jit_program_execute(tagged_add, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK,
	      "mixed tagged addition did not deoptimize");
	free_var(tagged_env[0]);

	tagged_env[0].type = tagged_env[1].type = TYPE_FLOAT;
	tagged_env[0].v.fnum = box_fl(1.5);
	tagged_env[1].v.fnum = box_fl(2.5);
	ticks = 10;
	check(jit_program_execute(tagged_add, tagged_env, &result, &ticks,
				  &timed_out, &error, 0, 0, 0)
	      == JIT_RUN_FALLBACK,
	      "tagged float addition bypassed its unimplemented dispatch");
	jit_program_free(tagged_add);
	jit_program_free(typed_left_add);
	jit_program_free(typed_right_add);
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

#ifdef WAIF_CORE
    /* Complex extension values retain the full pointer through resumes. */
    {
	Var waif;
	uintptr_t pointer = UINTPTR_MAX - 0x1234;

	waif.type = TYPE_WAIF;
	waif.v.waif = (Waif *) pointer;
	check((uintptr_t) jit_rt_var_raw(&waif) == pointer,
	      "jit_rt_var_raw truncated waif pointer");
    }
#endif

    /* Exception and finally stack marker deoptimization tests */
    {
	JITProgram *native_catch = native_catch_program();

	ticks = 10;
	check(jit_program_execute(native_catch, 0, &result, &ticks, &timed_out,
				  &error, 0, 0, 0) == JIT_RUN_RETURNED,
	      "native catch handler did not return");
	check(result.type == TYPE_ERR && result.v.err == E_DIV,
	      "native catch handler received the wrong error");
	free_var(result);
	jit_program_free(native_catch);

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

	JITProgram *catch_deopt = catch_stack_marker_program(0);
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

	JITProgram *catch_error = catch_stack_marker_program(1);
	memset(deopt_stack, 0, sizeof(deopt_stack));
	ticks = 10;
	error = E_NONE;
	check(jit_program_execute(catch_error, 0, &result, &ticks, &timed_out,
				  &error, 0, &deopt_state, deopt_stack)
	      == JIT_RUN_ERROR && error == E_DIV,
	      "native error with catch marker failed");
	check(deopt_state.stack_depth == 3,
	      "native error catch marker depth wrong");
	check(deopt_state.materialized,
	      "native error did not report materialized state");
	check(deopt_stack[0].type == TYPE_INT && deopt_stack[0].v.num == 0,
	      "native error catch codes wrong");
	check(deopt_stack[1].type == TYPE_INT && deopt_stack[1].v.num == 77,
	      "native error catch handler pc wrong");
	check(deopt_stack[2].type == TYPE_CATCH && deopt_stack[2].v.num == 1,
	      "native error catch marker wrong");
	free_var(deopt_stack[0]);
	free_var(deopt_stack[1]);
	free_var(deopt_stack[2]);
	jit_program_free(catch_error);

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
	allocate_map_locals(map, 1);
	map->local_values[0].value = 1;
	set_program_value_type(program, 1, TYPE_STR);
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
    jit_program_free(two_ticks);
    jit_program_free(duplicate_tick_exits);
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
    jit_program_free(modulus_power_two);
    jit_program_free(negative_modulus_power_two);
    jit_program_free(minimum_modulus_power_two);
    jit_program_free(modulus_one);
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
	check(jit_rt_str_cmp(0, "", 1) == 0
	      && jit_rt_str_cmp("", 0, 1) == 0,
	      "jit_rt_str_cmp treats null strings as empty");

	/* 4. string concat and index tests */
	int32_t rt_err = E_NONE;
	const char *concat_res = jit_rt_str_concat("Hello, ", "World!", &rt_err);
	check(rt_err == E_NONE && concat_res && strcmp(concat_res, "Hello, World!") == 0,
	      "jit_rt_str_concat success");
	if (concat_res)
	    free_str(concat_res);
	concat_res = jit_rt_str_concat(0, "suffix", &rt_err);
	check(rt_err == E_NONE && concat_res && !strcmp(concat_res, "suffix"),
	      "jit_rt_str_concat accepts a null left operand");
	free_str(concat_res);
	concat_res = jit_rt_str_concat("prefix", 0, &rt_err);
	check(rt_err == E_NONE && concat_res && !strcmp(concat_res, "prefix"),
	      "jit_rt_str_concat accepts a null right operand");
	free_str(concat_res);
	{
	    Num saved_limit = _server_int_option_cache[SVO_MAX_STRING_CONCAT];

	    _server_int_option_cache[SVO_MAX_STRING_CONCAT] = 3;
	    concat_res = jit_rt_str_concat("ab", "cd", &rt_err);
	    _server_int_option_cache[SVO_MAX_STRING_CONCAT] = saved_limit;
	    check(!concat_res && rt_err == E_QUOTA,
		  "jit_rt_str_concat did not enforce the configured limit");
	}
	{
	    Var homes[1];
	    const char *owned;
	    int64_t owned_raw = 0;

	    homes[0].type = TYPE_NONE;
	    check(jit_rt_str_concat_owned(homes, 0, "a", "b",
		JIT_LAST_USE_SRC1, &owned_raw, &rt_err)
		  && rt_err == E_NONE && homes[0].type == TYPE_STR
		  && homes[0].v.str == (const char *) (intptr_t) owned_raw
		  && !strcmp(homes[0].v.str, "ab"),
		  "owned string concat publishes an empty home");
	    owned = homes[0].v.str;
	    check(jit_rt_str_concat_owned(homes, 0, owned, "c",
		JIT_LAST_USE_SRC1, &owned_raw, &rt_err)
		  && rt_err == E_NONE && !strcmp(homes[0].v.str, "abc")
		  && var_refcount(homes[0]) == 1,
		  "owned string concat transfers a last-use operand");
	    owned = homes[0].v.str;
	    check(jit_rt_str_concat_owned(homes, 0, "prefix", owned,
		JIT_LAST_USE_SRC2, &owned_raw, &rt_err)
		  && rt_err == E_NONE
		  && !strcmp(homes[0].v.str, "prefixabc")
		  && var_refcount(homes[0]) == 1,
		  "owned string concat transfers a last-use right operand");
	    owned = homes[0].v.str;
	    check(!jit_rt_str_concat_owned(homes, 0, "x", "y",
		JIT_LAST_USE_SRC1, &owned_raw, &rt_err)
		  && rt_err == E_NONE && homes[0].v.str == owned,
		  "owned string concat rejects an owner mismatch");
	    {
		Num saved_limit =
		    _server_int_option_cache[SVO_MAX_STRING_CONCAT];

		owned_raw = 17;
		_server_int_option_cache[SVO_MAX_STRING_CONCAT] = 3;
		check(jit_rt_str_concat_owned(homes, 0, owned, "x",
		    JIT_LAST_USE_SRC1, &owned_raw, &rt_err)
		      && rt_err == E_QUOTA && owned_raw == 17
		      && homes[0].type == TYPE_STR
		      && homes[0].v.str == owned,
		      "owned string concat consumed its home on quota failure");
		_server_int_option_cache[SVO_MAX_STRING_CONCAT] = saved_limit;
	    }
	    free_var(homes[0]);
	}

	const char *char_res = jit_rt_str_ref("LambdaMOO", 7, &rt_err);
	check(rt_err == E_NONE && char_res && strcmp(char_res, "M") == 0,
	      "jit_rt_str_ref index 7");
	if (char_res)
	    free_str(char_res);

	char_res = jit_rt_str_ref("LambdaMOO", 0, &rt_err);
	check(rt_err == E_RANGE && char_res == 0, "jit_rt_str_ref index 0 range error");

	char_res = jit_rt_str_ref("LambdaMOO", 100, &rt_err);
	check(rt_err == E_RANGE && char_res == 0, "jit_rt_str_ref index 100 range error");
	char_res = jit_rt_str_ref(0, 1, &rt_err);
	check(rt_err == E_RANGE && char_res == 0,
	      "jit_rt_str_ref rejects a null string");
	char_res = jit_rt_str_range_ref(0, 1, 1, &rt_err);
	check(!char_res && rt_err == E_TYPE,
	      "jit_rt_str_range_ref null base type error");
	{
	    const char *range_base = str_dup("abc");

	    char_res = jit_rt_str_range_ref(range_base, 0, 1, &rt_err);
	    check(!char_res && rt_err == E_RANGE,
		  "jit_rt_str_range_ref invalid range error");
	    char_res = jit_rt_str_range_ref(range_base, 2, 2, &rt_err);
	    check(char_res && rt_err == E_NONE && !strcmp(char_res, "b"),
		  "jit_rt_str_range_ref valid substring");
	    free_str(char_res);
	    free_str(range_base);
	}

	/* 5. list concat and append tests */
	Var l1 = new_list(1);
	l1.v.list[1].type = TYPE_INT;
	l1.v.list[1].v.num = 111;
	Var l2 = new_list(1);
	int l1_refs;
	l2.v.list[1].type = TYPE_INT;
	l2.v.list[1].v.num = 222;

	Var *lconcat = jit_rt_list_concat(l1.v.list, l2.v.list, &rt_err);
	check(rt_err == E_NONE && lconcat && lconcat[0].v.num == 2, "jit_rt_list_concat len");
	check(lconcat[1].v.num == 111 && lconcat[2].v.num == 222, "jit_rt_list_concat elements");
	Var lconcat_var;
	lconcat_var.type = TYPE_LIST;
	lconcat_var.v.list = lconcat;
	free_var(lconcat_var);
	check(!jit_rt_list_concat(0, l2.v.list, &rt_err) && rt_err == E_TYPE,
	      "jit_rt_list_concat rejects a null left operand");
	check(!jit_rt_list_concat(l1.v.list, 0, &rt_err) && rt_err == E_TYPE,
	      "jit_rt_list_concat rejects a null right operand");
	check(!jit_rt_list_range_ref(0, 1, 1, &rt_err) && rt_err == E_TYPE,
	      "jit_rt_list_range_ref null base type error");
	check(!jit_rt_list_range_ref(l1.v.list, 0, 1, &rt_err)
	      && rt_err == E_RANGE,
	      "jit_rt_list_range_ref invalid range error");
	{
	    Var range;

	    range.type = TYPE_LIST;
	    range.v.list = jit_rt_list_range_ref(l1.v.list, 1, 1, &rt_err);
	    check(range.v.list && rt_err == E_NONE
		  && range.v.list[0].v.num == 1
		  && range.v.list[1].v.num == 111,
		  "jit_rt_list_range_ref valid sublist");
	    free_var(range);
	}

	l1_refs = var_refcount(l1);
	Var *lapp = jit_rt_list_append(l1.v.list, 333, TYPE_INT);
	check(lapp && lapp[0].v.num == 2 && lapp[2].v.num == 333, "jit_rt_list_append int");
	check(var_refcount(l1) == l1_refs && l1.v.list[0].v.num == 1
	      && l1.v.list[1].v.num == 111,
	      "jit_rt_list_append borrows its source");
	Var lapp_var;
	lapp_var.type = TYPE_LIST;
	lapp_var.v.list = lapp;
	free_var(lapp_var);
	{
	    Var homes[1];
	    unsigned capacities[1] = { 0 };
	    Var *owned_result;

	    homes[0] = new_list(1);
	    homes[0].v.list[1].type = TYPE_INT;
	    homes[0].v.list[1].v.num = 666;
	    owned_result = jit_rt_list_append_owned(homes, capacities, 0,
		homes[0].v.list, 777, TYPE_INT);
	    check(owned_result == homes[0].v.list
		  && homes[0].v.list[0].v.num == 2
		  && homes[0].v.list[2].v.num == 777,
		  "owner-backed list append updates its home");
	    check(var_refcount(homes[0]) == 1,
		  "owner-backed list append remains exclusive");
	    free_var(homes[0]);
	}
	{
	    Var homes[1];
	    unsigned capacities[1] = { 0 };
	    Var partial = new_list(1);
	    Var *owned_result;

	    partial.v.list[1].type = TYPE_INT;
	    partial.v.list[1].v.num = 111;
	    homes[0].type = TYPE_NONE;
	    homes[0].v.num = 0;
	    owned_result = jit_rt_list_append_owned(homes, capacities, 0,
		partial.v.list, 222, TYPE_INT);
	    check(homes[0].type == TYPE_LIST
		  && owned_result == homes[0].v.list
		  && owned_result[0].v.num == 2
		  && owned_result[2].v.num == 222,
		  "resumed owner-backed list append acquires its list");
	    free_var(partial);
	    free_var(homes[0]);
	}
	{
	    Var homes[1];
	    unsigned capacities[1] = { 3 };
	    Var *fixed_result;

	    homes[0].type = TYPE_LIST;
	    homes[0].v.list = jit_rt_make_fixed_list_head(111, TYPE_INT, 3);
	    fixed_result = jit_rt_fixed_list_append_owned(homes, capacities, 0,
		homes[0].v.list, 2, 222, TYPE_INT);
	    fixed_result = jit_rt_fixed_list_append_owned(homes, capacities, 0,
		fixed_result, 3, 333, TYPE_INT);
	    check(fixed_result == homes[0].v.list
		  && fixed_result[0].v.num == 3
		  && fixed_result[1].v.num == 111
		  && fixed_result[2].v.num == 222
		  && fixed_result[3].v.num == 333,
		  "fixed list construction fills one allocation");
	    check(var_refcount(homes[0]) == 1,
		  "fixed list construction remains exclusive");
	    free_var(homes[0]);
	}
	{
	    Var homes[1];
	    unsigned capacities[1] = { 0 };
	    Var *fixed_result;

	    homes[0] = new_list(1);
	    homes[0].v.list[1].type = TYPE_INT;
	    homes[0].v.list[1].v.num = 111;
	    fixed_result = jit_rt_fixed_list_append_owned(homes, capacities, 0,
		homes[0].v.list, 2, 222, TYPE_INT);
	    check(fixed_result == homes[0].v.list
		  && fixed_result[0].v.num == 2
		  && fixed_result[2].v.num == 222
		  && capacities[0] == 0,
		  "fixed list append grows an exhausted owner home");
	    free_var(homes[0]);
	}
	{
	    Var homes[1];
	    unsigned capacities[1] = { 0 };
	    Var partial = new_list(1);
	    Var *fixed_result;

	    partial.v.list[1].type = TYPE_INT;
	    partial.v.list[1].v.num = 111;
	    homes[0].type = TYPE_NONE;
	    homes[0].v.num = 0;
	    fixed_result = jit_rt_fixed_list_append_owned(homes, capacities, 0,
		partial.v.list, 2, 222, TYPE_INT);
	    check(fixed_result[0].v.num == 2
		  && fixed_result[1].v.num == 111
		  && fixed_result[2].v.num == 222,
		  "resumed fixed list construction grows a canonical list");
	    free_var(partial);
	    partial.v.list = fixed_result;
	    free_var(partial);
	}

	/* Indexed local updates preserve shared lists and acquire the RHS. */
	{
	    Var env[1];
	    Var shared;
	    Var *updated;
	    const char *replacement = str_dup("replacement");

	    env[0] = new_list(2);
	    env[0].v.list[1].type = TYPE_INT;
	    env[0].v.list[1].v.num = 10;
	    env[0].v.list[2].type = TYPE_INT;
	    env[0].v.list[2].v.num = 20;
	    shared = var_ref(env[0]);
	    updated = jit_rt_list_index_set(env, 0, env[0].v.list, 2,
		(int64_t) (intptr_t) replacement, TYPE_STR, &rt_err);
	    check(rt_err == E_NONE && updated == env[0].v.list,
		  "jit_rt_list_index_set updates local");
	    check(env[0].v.list != shared.v.list
		  && shared.v.list[2].type == TYPE_INT
		  && shared.v.list[2].v.num == 20,
		  "jit_rt_list_index_set preserves shared list");
	    check(env[0].v.list[2].type == TYPE_STR
		  && !strcmp(env[0].v.list[2].v.str, "replacement"),
		  "jit_rt_list_index_set stores complex value");
	    updated = jit_rt_list_index_set(env, 0, env[0].v.list, 0,
		42, TYPE_INT, &rt_err);
	    check(!updated && rt_err == E_RANGE
		  && env[0].v.list[2].type == TYPE_STR,
		  "jit_rt_list_index_set rejects range without mutation");
	    free_str(replacement);
	    free_var(shared);
	    free_var(env[0]);
	}

	/* 6. list_in test */
	check(jit_rt_list_in(111, TYPE_INT, l1.v.list) == 1, "jit_rt_list_in found");
	check(jit_rt_list_in(999, TYPE_INT, l1.v.list) == 0, "jit_rt_list_in not found");

	free_var(l1);
	free_var(l2);

	/* 7. get_prop test */
	int64_t prop_raw = 0;
	int64_t prop_type = INT64_C(0x5555555500000000);
	int ok = jit_rt_get_prop(0, "name", 2, &prop_raw, &prop_type, &rt_err);
	check(ok == 1 && rt_err == E_NONE && prop_type == TYPE_INT && prop_raw == 123,
	      "jit_rt_get_prop replaces the complete result tag");

	ok = jit_rt_get_prop(-1, "name", 2, &prop_raw, &prop_type, &rt_err);
	check(ok == 0 && rt_err == E_INVIND, "jit_rt_get_prop invalid object");

	ok = jit_rt_put_prop(0, "name", 2, 456, TYPE_INT, &rt_err);
	check(ok == 1 && rt_err == E_NONE, "jit_rt_put_prop valid property write");
	prop_type = INT64_C(0x5555555500000000);
	ok = jit_rt_get_prop(0, "name", 2, &prop_raw, &prop_type, &rt_err);
	check(ok == 1 && prop_type == TYPE_INT && prop_raw == 456,
	      "jit_rt_put_prop stored property value");
	ok = jit_rt_put_prop(-1, "name", 2, 456, TYPE_INT, &rt_err);
	check(ok == 0 && rt_err == E_INVIND, "jit_rt_put_prop invalid object");
	{
	    Var property;
	    Var returned;
	    double returned_float;
	    int refs;

	    property.type = TYPE_FLOAT;
	    property.v.fnum = box_fl(2.5);
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ok = jit_rt_get_prop(0, "value", 2, &prop_raw, &prop_type,
		&rt_err);
	    memcpy(&returned_float, &prop_raw, sizeof(returned_float));
	    check(ok == 1 && rt_err == E_NONE && prop_type == TYPE_FLOAT
		  && returned_float == 2.5,
		  "jit_rt_get_prop returned the wrong float");
	    check(var_refcount(property) == refs,
		  "jit_rt_get_prop leaked its temporary float reference");
	    returned_float = 4.25;
	    memcpy(&prop_raw, &returned_float, sizeof(prop_raw));
	    ok = jit_rt_put_prop(0, "value", 2, prop_raw, TYPE_FLOAT,
		&rt_err);
	    check(ok == 1 && rt_err == E_NONE,
		  "jit_rt_put_prop rejected a float value");
	    ok = jit_rt_get_prop(0, "value", 2, &prop_raw, &prop_type,
		&rt_err);
	    memcpy(&returned_float, &prop_raw, sizeof(returned_float));
	    check(ok == 1 && prop_type == TYPE_FLOAT
		  && returned_float == 4.25,
		  "JIT float property write did not round trip");
	    hir_test_reset_property();
	    free_var(property);

	    property.type = TYPE_STR;
	    property.v.str = str_dup("property string");
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ok = jit_rt_get_prop(0, "value", 2, &prop_raw, &prop_type,
		&rt_err);
	    returned.type = (var_type) prop_type;
	    returned.v.str = (const char *) (intptr_t) prop_raw;
	    check(ok == 1 && rt_err == E_NONE && returned.type == TYPE_STR
		  && returned.v.str == property.v.str
		  && var_refcount(property) == refs + 1,
		  "jit_rt_get_prop did not transfer its string reference");
	    free_var(returned);
	    hir_test_reset_property();
	    free_var(property);

	    property = new_list(1);
	    property.v.list[1].type = TYPE_INT;
	    property.v.list[1].v.num = 17;
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ok = jit_rt_get_prop(0, "value", 2, &prop_raw, &prop_type,
		&rt_err);
	    returned.type = (var_type) prop_type;
	    returned.v.list = (Var *) (intptr_t) prop_raw;
	    check(ok == 1 && rt_err == E_NONE && returned.type == TYPE_LIST
		  && returned.v.list == property.v.list
		  && returned.v.list[1].v.num == 17
		  && var_refcount(property) == refs + 1,
		  "jit_rt_get_prop did not transfer its list reference");
	    free_var(returned);
	    refs = var_refcount(property);
	    ok = jit_rt_put_prop(0, "value", 2,
		(int64_t) (intptr_t) property.v.list, TYPE_LIST, &rt_err);
	    check(ok == 1 && rt_err == E_NONE
		  && var_refcount(property) == refs,
		  "JIT list property write changed caller ownership");
	    hir_test_reset_property();
	    free_var(property);

#ifdef WAIF_CORE
	    property = hir_test_new_waif();
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ok = jit_rt_get_prop(0, "value", 2, &prop_raw, &prop_type,
		&rt_err);
	    returned.type = (var_type) prop_type;
	    returned.v.waif = (Waif *) (intptr_t) prop_raw;
	    check(ok == 1 && rt_err == E_NONE && returned.type == TYPE_WAIF
		  && returned.v.waif == property.v.waif
		  && var_refcount(property) == refs + 1,
		  "jit_rt_get_prop did not transfer its waif reference");
	    free_var(returned);
	    refs = var_refcount(property);
	    ok = jit_rt_put_prop(0, "value", 2,
		(int64_t) (intptr_t) property.v.waif, TYPE_WAIF, &rt_err);
	    check(ok == 1 && rt_err == E_NONE
		  && var_refcount(property) == refs,
		  "JIT waif property write changed caller ownership");
	    hir_test_reset_property();
	    free_var(property);
#endif
	}
	{
	    JITProgram *native_get = owned_property_result_program();
	    Var native_env[2];
	    Var property;
	    JITRunResult status;
	    int refs;

	    native_env[0].type = TYPE_OBJ;
	    native_env[0].v.obj = 0;
	    native_env[1].type = TYPE_STR;
	    native_env[1].v.str = str_dup("value");

	    property.type = TYPE_FLOAT;
	    property.v.fnum = box_fl(6.25);
	    hir_test_set_property(property);
	    ticks = 10;
	    status = jit_program_execute(native_get, native_env, &result, &ticks,
				 &timed_out, &error, 0, 0, 0);
	    check(status == JIT_RUN_RETURNED && result.type == TYPE_FLOAT
		  && fl_unbox(result.v.fnum) == 6.25,
		  "owned native float property result did not return intact");
	    free_var(result);
	    hir_test_reset_property();
	    free_var(property);

#ifdef WAIF_CORE
	    property = hir_test_new_waif();
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ticks = 10;
	    status = jit_program_execute(native_get, native_env, &result, &ticks,
				 &timed_out, &error, 0, 0, 0);
	    check(status == JIT_RUN_RETURNED && result.type == TYPE_WAIF
		  && result.v.waif == property.v.waif
		  && var_refcount(property) == refs + 1,
		  "owned native waif property result did not return intact");
	    free_var(result);
	    hir_test_reset_property();
	    free_var(property);
#else
	    (void) refs;
#endif
	    free_var(native_env[1]);
	    jit_program_free(native_get);
	}
	{
	    JITProgram *repeated_get = repeated_owned_property_program();
	    Var repeated_env[2];
	    Var property = new_list(1);
	    int refs;

	    repeated_env[0].type = TYPE_OBJ;
	    repeated_env[0].v.obj = 0;
	    repeated_env[1].type = TYPE_STR;
	    repeated_env[1].v.str = str_dup("value");
	    property.v.list[1].type = TYPE_STR;
	    property.v.list[1].v.str = str_dup("reused property owner");
	    hir_test_set_property(property);
	    refs = var_refcount(property);
	    ticks = 10;
	    check(jit_program_execute(repeated_get, repeated_env, &result,
				      &ticks, &timed_out, &error, 0, 0, 0)
		  == JIT_RUN_RETURNED,
		  "repeated native property reads did not return");
	    check(result.type == TYPE_LIST && result.v.list == property.v.list
		  && var_refcount(property) == refs + 1,
		  "reused property owner retained more than its final value");
	    free_var(result);
	    hir_test_reset_property();
	    free_var(property);
	    free_var(repeated_env[1]);
	    jit_program_free(repeated_get);
	}
	{
	    Var property;
	    Var returned;
	    int refs;

	    property.type = TYPE_STR;
	    property.v.str = str_dup("built-in property string");
	    hir_test_set_property(property);
	    hir_test_set_builtin_property(BP_NAME);
	    refs = var_refcount(property);
	    ok = jit_rt_get_prop(0, "name", 2, &prop_raw, &prop_type,
		&rt_err);
	    returned.type = (var_type) prop_type;
	    returned.v.str = (const char *) (intptr_t) prop_raw;
	    check(ok == 1 && rt_err == E_NONE && returned.type == TYPE_STR
		  && returned.v.str == property.v.str
		  && var_refcount(property) == refs + 1,
		  "JIT built-in property read did not transfer ownership");
	    free_var(returned);
	    refs = var_refcount(property);
	    ok = jit_rt_get_prop(0, "name", 1, &prop_raw, &prop_type,
		&rt_err);
	    returned.type = (var_type) prop_type;
	    returned.v.str = (const char *) (intptr_t) prop_raw;
	    check(ok == 1 && rt_err == E_NONE
		  && returned.type == TYPE_STR
		  && returned.v.str == property.v.str
		  && var_refcount(property) == refs + 1,
		  "unprotected built-in property rejected a nonwizard read");
	    free_var(returned);
	    hir_test_set_builtin_property_protected(BP_NAME, 1);
	    refs = var_refcount(property);
	    prop_raw = 111;
	    prop_type = 222;
	    ok = jit_rt_get_prop(0, "name", 1, &prop_raw, &prop_type,
		&rt_err);
	    check(ok == 0 && rt_err == E_PERM && prop_raw == 111
		  && prop_type == 222 && var_refcount(property) == refs,
		  "protected built-in property leaked or changed its outputs");
	    hir_test_set_builtin_property_protected(BP_NAME, 0);
	    hir_test_set_builtin_property(BP_NONE);
	    hir_test_reset_property();
	    free_var(property);
	}

	hir_test_set_property_allowed(0);
	prop_raw = 111;
	prop_type = 222;
	ok = jit_rt_get_prop(0, "name", 2, &prop_raw, &prop_type, &rt_err);
	check(ok == 0 && rt_err == E_PERM && prop_raw == 111
	      && prop_type == 222,
	      "jit_rt_get_prop permission denial changed its outputs");
	ok = jit_rt_put_prop(0, "name", 2, 456, TYPE_INT, &rt_err);
	check(ok == 0 && rt_err == E_PERM,
	      "jit_rt_put_prop ignored ordinary-property permissions");
	hir_test_set_property_allowed(1);

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
	JITProgram *profile_program = new_jit_program();
	JITProgramStats stats;
	profile_program->potential_exit_sites = 17;
	profile_program->elided_exit_sites = 11;
	profile_program->type_guard_sites = 7;
	profile_program->eliminated_type_guard_sites = 3;

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
	jit_profile_record_entry(profile_program);
	jit_profile_record_entry(profile_program);
	jit_profile_record_completed(profile_program);
	jit_profile_record_vm_call(profile_program);
	{
	    JITExecutionContext context = { 0 };
	    JITNativeFrame root = { 0 };
	    JITNativeFrame child = { 0 };
	    JITNativeFrame leaf = { 0 };

	    root.program = child.program = leaf.program = profile_program;
	    child.caller = &root;
	    leaf.caller = &child;
	    context.current_frame = &child;
	    context.native_depth = 1;
	    jit_profile_record_native_call(&context);
	    context.current_frame = &leaf;
	    context.native_depth = 2;
	    jit_profile_record_native_call(&context);
	    jit_profile_record_native_return(&child);
	    jit_profile_record_native_return(&root);
	    jit_profile_record_native_promotion(&root);
	    jit_profile_record_native_promotion(&child);
	    jit_profile_record_native_promotion(&leaf);
	    jit_profile_native_frame_acquired(&child, 512);
	    jit_program_stats(profile_program, &stats);
	    check(stats.native_chain_active_frames == 1
		  && stats.native_chain_frame_bytes == 512
		  && stats.accounted_bytes == stats.metadata_bytes
		     + stats.runtime_bytes + stats.native_allocated_bytes
		     + stats.continuation_bytes + 512,
		  "live native frame accounting is wrong");
	    jit_profile_native_frame_released(&child, 512);
	}

	JITDeoptState deopt_sample;
	memset(&deopt_sample, 0, sizeof(deopt_sample));
	deopt_sample.bytecode_pc = 42;
	deopt_sample.source_lineno = 10;
	deopt_sample.reason = JIT_DEOPT_BUILTIN_CALL;
	jit_profile_record_deopt(profile_program, 0, "do_command", &deopt_sample);

	deopt_sample.bytecode_pc = 18;
	deopt_sample.source_lineno = 5;
	deopt_sample.operation = HIR_OP_GET_PROP;
	deopt_sample.reason = JIT_DEOPT_PROPERTY_READ;
	jit_profile_record_deopt(profile_program, 1, "eval", &deopt_sample);

	deopt_sample.bytecode_pc = 20;
	deopt_sample.source_lineno = 6;
	deopt_sample.operation = HIR_OP_SCATTER;
	deopt_sample.reason = JIT_DEOPT_UNSUPPORTED_OP;
	jit_profile_record_deopt(profile_program, 69, "parse_parties",
				 &deopt_sample);

	deopt_sample.bytecode_pc = 21;
	deopt_sample.source_lineno = 7;
	deopt_sample.operation = HIR_OP_ADD;
	deopt_sample.reason = JIT_DEOPT_TYPE_GUARD;
	deopt_sample.guard_value[0] = 3;
	deopt_sample.guard_local[0] = 2;
	deopt_sample.guard_expected[0] = JIT_TYPE_MASK(TYPE_INT)
	    | JIT_TYPE_MASK(TYPE_OBJ) | JIT_TYPE_MASK(TYPE_STR)
	    | JIT_TYPE_MASK(TYPE_ERR) | JIT_TYPE_MASK(TYPE_LIST)
	    | JIT_TYPE_MASK(TYPE_CLEAR) | JIT_TYPE_MASK(TYPE_NONE)
	    | JIT_TYPE_MASK(TYPE_CATCH) | JIT_TYPE_MASK(TYPE_FINALLY)
	    | JIT_TYPE_MASK(TYPE_FLOAT) | JIT_TYPE_MASK(TYPE_WAIF);
	deopt_sample.guard_actual[0] = TYPE_STR;
	deopt_sample.guard_value[1] = 4;
	deopt_sample.guard_local[1] = -1;
	deopt_sample.guard_expected[1] = JIT_TYPE_MASK(TYPE_INT);
	deopt_sample.guard_actual[1] = (var_type) 127;
	jit_profile_record_deopt(profile_program, 70, 0, &deopt_sample);

	jit_program_stats(profile_program, &stats);
	check(stats.entries == 2 && stats.completions == 1
	      && stats.vm_calls == 1 && stats.deopts == 4,
	      "per-program JIT usage totals are wrong");
	check(stats.deopts_by_reason[JIT_DEOPT_BUILTIN_CALL] == 1
	      && stats.deopts_by_reason[JIT_DEOPT_PROPERTY_READ] == 1
	      && stats.deopts_by_reason[JIT_DEOPT_UNSUPPORTED_OP] == 1
	      && stats.deopts_by_reason[JIT_DEOPT_TYPE_GUARD] == 1,
	      "per-program JIT deopt reason totals are wrong");
	check(stats.last_used_generation > 0 && stats.last_used_time > 0,
	      "per-program JIT last-use statistics are wrong");
	check(stats.potential_exit_sites == 17 && stats.elided_exit_sites == 11
	      && stats.type_guard_sites == 7
	      && stats.eliminated_type_guard_sites == 3,
	      "per-program exit-proof statistics are wrong");
	check(stats.native_chain_calls == 2 && stats.native_chain_returns == 2
	      && stats.native_chain_promotions == 3
	      && stats.native_chain_max_depth == 3
	      && stats.native_chain_active_frames == 0
	      && stats.native_chain_frame_bytes == 0,
	      "per-program native chain statistics are wrong");

	/* Exercise aggregation, invalid samples, and every report category. */
	memset(&deopt_sample, 0, sizeof(deopt_sample));
	deopt_sample.bytecode_pc = 42;
	deopt_sample.source_lineno = 10;
	deopt_sample.reason = JIT_DEOPT_BUILTIN_CALL;
	jit_profile_record_deopt(profile_program, 0, "do_command",
				 &deopt_sample);
	deopt_sample.bytecode_pc = 21;
	deopt_sample.source_lineno = 7;
	deopt_sample.reason = JIT_DEOPT_TYPE_GUARD;
	deopt_sample.operation = HIR_OP_ADD;
	jit_profile_record_deopt(profile_program, 70, 0, &deopt_sample);
	for (int reason = JIT_DEOPT_NONE; reason < JIT_DEOPT_NUM_REASONS;
	     reason++) {
	    memset(&deopt_sample, 0, sizeof(deopt_sample));
	    deopt_sample.bytecode_pc = 100 + reason;
	    deopt_sample.source_lineno = 20 + reason;
	    deopt_sample.reason = (JITDeoptReason) reason;
	    deopt_sample.operation = reason == JIT_DEOPT_UNSUPPORTED_OP
		? HIR_OP_FORK : -1;
	    deopt_sample.builtin_func = reason == JIT_DEOPT_BUILTIN_CALL
		? 0 : -1;
	    jit_profile_record_deopt(profile_program, 100 + reason,
		"coverage", &deopt_sample);
	}
	deopt_sample.reason = (JITDeoptReason) JIT_DEOPT_NUM_REASONS;
	jit_profile_record_deopt(0, -1, 0, &deopt_sample);
	jit_profile_record_deopt(0, -2, 0, 0);

	/* Trigger report generation */
	jit_profile_report();

	/* Trigger periodic check */
	jit_profile_maybe_report(100);
	jit_profile_maybe_report(2000);

	jit_profile_reset();
	jit_program_free(profile_program);
    }
    {
	JITPoolStats pool_stats;
	JITPoolPolicyStats policy_stats;
	JITProgram *prog = binary_program(10, 2, HIR_OP_DIV);
	JITProgram *cold = binary_program(10, 2, HIR_OP_DIV);
	JITNativeFrame frame = { 0 };
	uint64_t generation;

	check(prog != 0, "failed to create test program for pool verification");
	check(cold != 0, "failed to create cold program for pool verification");
	check(jit_pool_set_policy(3, 0), "failed to set JIT pool test policy");
	jit_pool_maintain();
	generation = jit_program_warmup_generation(prog);
	check(generation != 0,
	      "pending program did not adopt the active pool generation");
	check(!jit_program_admit_interpreter_entry(prog)
	      && jit_program_warmup_count(prog) == 1,
	      "first pending invocation was not counted");
	check(!jit_program_admit_interpreter_entry(prog)
	      && jit_program_warmup_count(prog) == 2,
	      "second pending invocation was not counted");
	check(jit_program_claim_native_entry(prog)
	      && jit_program_warmup_count(prog) == 3,
	      "native threshold invocation was not claimed");
	check(jit_program_compile(prog), "failed to compile program for pool test");
	check(jit_program_warmup_count(prog) == 0,
	      "compiled program retained its warmup count");
	jit_pool_stats(&pool_stats);
	check(pool_stats.active_programs >= 1, "pool active program count is wrong");
	check(pool_stats.total_machine_code_bytes >= prog->machine_code_len,
	      "pool machine code byte count is wrong");
	check(pool_stats.total_native_allocated_bytes >= pool_stats.total_machine_code_bytes,
	      "pool native allocated byte count is wrong");
	frame.program = prog;
	jit_profile_native_frame_acquired(&frame, 256);
	jit_pool_stats(&pool_stats);
	check(pool_stats.native_chain_active_frames == 1
	      && pool_stats.native_chain_frame_bytes == 256,
	      "pool native frame accounting is wrong");
	jit_profile_native_frame_released(&frame, 256);

	/* Reset pool and verify invalidation of active programs */
	check(!jit_program_admit_interpreter_entry(cold)
	      && jit_program_warmup_count(cold) == 1,
	      "cold program invocation was not counted");
	jit_pool_reset();
	check(jit_program_state(prog) == JIT_STATE_PENDING,
	      "jit_pool_reset did not return program to pending state");
	check(jit_program_warmup_generation(prog) != generation,
	      "pool rotation did not update the program generation");
	check(jit_program_warmup_count(prog) == 0
	      && jit_program_warmup_count(cold) == 0,
	      "pool rotation did not reset pending warmup counts");
	jit_pool_stats(&pool_stats);
	check(pool_stats.active_programs == 0, "pool has remaining active programs after reset");
	check(pool_stats.total_machine_code_bytes == 0, "pool machine code bytes not zeroed");

	/* Recompile into a constrained pool and rotate after crossing its limit. */
	check(jit_pool_set_policy(3, 1), "failed to lower JIT pool limit");
	jit_pool_policy_stats(&policy_stats);
	check(!policy_stats.rotation_pending,
	      "empty constrained JIT pool unexpectedly requested rotation");
	check(jit_program_compile(prog), "failed to recompile program after pool reset");
	check(jit_program_state(prog) == JIT_STATE_COMPILED,
	      "program did not compile after pool reset");
	jit_pool_policy_stats(&policy_stats);
	check(policy_stats.rotation_pending,
	      "JIT pool growth beyond its limit did not request rotation");
	jit_pool_maintain();
	jit_pool_policy_stats(&policy_stats);
	check(!policy_stats.rotation_pending && policy_stats.active_programs == 0,
	      "JIT pool maintenance did not complete rotation");
	check(jit_pool_set_policy(32, (size_t) 256 * 1024 * 1024),
	      "failed to restore default JIT pool policy");

	jit_program_free(prog);
	jit_program_free(cold);
	jit_shutdown();
	jit_pool_stats(&pool_stats);
	check(pool_stats.active_programs == 0, "pool active programs not zero after shutdown");
    }
    {
	JITProgram *program = new_jit_program();
	JITDeoptMap *base;
	JITDeoptMap *change;
	JITDeoptMap *remove;

	program->num_deopt_maps = 3;
	program->num_values = 4;
	program->deopt_maps = allocate(sizeof(JITDeoptMap) * 3);
	base = &program->deopt_maps[0];
	change = &program->deopt_maps[1];
	remove = &program->deopt_maps[2];
	base->num_locals = change->num_locals = remove->num_locals = 2;
	allocate_map_locals(base, 2);
	base->local_values[0].value = 1;
	base->local_values[1].value = 2;
	set_program_value_type(program, 2, TYPE_STR);
	change->local_base = 1;
	allocate_map_locals(change, 1);
	change->local_values[0].value = 3;
	set_program_value_type(program, 3, TYPE_OBJ);
	remove->local_base = 2;
	allocate_map_locals(remove, 1);
	remove->local_values[0].slot = 1;
	remove->local_values[0].value = 0;

	check(jit_deopt_map_local_value(program, change, 0) == 3
	      && jit_deopt_map_local_value(program, change, 1) == 2,
	      "deopt local base did not inherit unchanged value");
	check(jit_deopt_map_local_type(program, change, 0) == TYPE_OBJ
	      && jit_deopt_map_local_type(program, change, 1) == TYPE_STR,
	      "deopt local base did not inherit unchanged type");
	check(jit_deopt_map_local_value(program, remove, 0) == 3
	      && jit_deopt_map_local_value(program, remove, 1) == 0,
	      "deopt local tombstone did not mask base value");
	jit_program_free(program);
    }

    return failures != 0;
}
