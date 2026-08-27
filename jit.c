#include "jit.h"

#include "config.h"
#include "options.h"

#include "my-stdio.h"
#include "my-string.h"
#include "my-time.h"

#include "db.h"
#include "exceptions.h"
#include "jit_internal.h"
#include "list.h"
#include "log.h"
#include "server.h"
#include "storage.h"
#include "utils.h"

#include "mir.h"
#include "mir-gen.h"

#include <limits.h>
#include <stddef.h>
#include <string.h>

#ifdef IGNORE_PROP_PROTECTED
#define bi_prop_protected(prop, progr) (0)
#else
#define bi_prop_protected(prop, progr) ((!is_wizard(progr)) && server_flag_option_cached(prop))
#endif

static inline double
raw_to_double(int64_t raw)
{
    double d;
    memcpy(&d, &raw, sizeof(d));
    return d;
}

static inline int64_t
double_to_raw(double d)
{
    int64_t raw;
    memcpy(&raw, &d, sizeof(raw));
    return raw;
}

/* JIT Runtime Helpers for Complex Values and Properties */

int
jit_rt_is_true(int64_t raw_val, int val_type)
{
    Var v;

    v.type = (var_type) val_type;
    if (val_type == TYPE_FLOAT)
	v.v.fnum = box_fl((FlNum) raw_to_double(raw_val));
    else if (val_type == TYPE_STR)
	v.v.str = (const char *) (intptr_t) raw_val;
    else if (val_type == TYPE_LIST)
	v.v.list = (Var *) (intptr_t) raw_val;
    else
	v.v.num = (Num) raw_val;
    return is_true(v);
}

int
jit_rt_equality(int64_t raw1, int type1, int64_t raw2, int type2, int case_matters)
{
    Var v1, v2;

    v1.type = (var_type) type1;
    if (type1 == TYPE_FLOAT)
	v1.v.fnum = box_fl((FlNum) raw_to_double(raw1));
    else if (type1 == TYPE_STR)
	v1.v.str = (const char *) (intptr_t) raw1;
    else if (type1 == TYPE_LIST)
	v1.v.list = (Var *) (intptr_t) raw1;
    else
	v1.v.num = (Num) raw1;

    v2.type = (var_type) type2;
    if (type2 == TYPE_FLOAT)
	v2.v.fnum = box_fl((FlNum) raw_to_double(raw2));
    else if (type2 == TYPE_STR)
	v2.v.str = (const char *) (intptr_t) raw2;
    else if (type2 == TYPE_LIST)
	v2.v.list = (Var *) (intptr_t) raw2;
    else
	v2.v.num = (Num) raw2;

    return equality(v1, v2, case_matters);
}

int
jit_rt_str_cmp(const char *s1, const char *s2, int case_matters)
{
    if (!s1)
	s1 = "";
    if (!s2)
	s2 = "";
    if (case_matters)
	return strcmp(s1, s2);
    else
	return mystrcasecmp(s1, s2);
}

const char *
jit_rt_str_concat(const char *s1, const char *s2, int32_t *err_out)
{
    size_t l1, l2, total;
    char *res;

    if (!s1)
	s1 = "";
    if (!s2)
	s2 = "";
    l1 = memo_strlen(s1);
    l2 = memo_strlen(s2);
    total = l1 + l2;

    if ((size_t) server_int_option_cached(SVO_MAX_STRING_CONCAT) < total) {
	*err_out = E_QUOTA;
	return 0;
    }
    res = mymalloc(total + 1, M_STRING);
    memcpy(res, s1, l1);
    memcpy(res + l1, s2, l2);
    res[total] = '\0';
    *err_out = E_NONE;
    return res;
}

const char *
jit_rt_str_ref(const char *str, int64_t idx, int32_t *err_out)
{
    size_t len;
    char *res;

    if (!str) {
	*err_out = E_RANGE;
	return 0;
    }
    len = memo_strlen(str);
    if (idx < 1 || (size_t) idx > len) {
	*err_out = E_RANGE;
	return 0;
    }
    res = mymalloc(2, M_STRING);
    res[0] = str[idx - 1];
    res[1] = '\0';
    *err_out = E_NONE;
    return res;
}

Var *
jit_rt_list_concat(Var *l1, Var *l2, int32_t *err_out)
{
    Var v1, v2, res;

    if (!l1 || !l2) {
	*err_out = E_TYPE;
	return 0;
    }
    v1.type = TYPE_LIST;
    v1.v.list = l1;
    v2.type = TYPE_LIST;
    v2.v.list = l2;

    res = listconcat(var_ref(v1), var_ref(v2));
    if (res.type == TYPE_ERR) {
	*err_out = res.v.err;
	return 0;
    }
    *err_out = E_NONE;
    return res.v.list;
}

Var *
jit_rt_make_singleton_list(int64_t elem_raw, int elem_type)
{
    Var list = new_list(1);
    Var elem;

    elem.type = (var_type) elem_type;
    if (elem_type == TYPE_FLOAT)
	elem.v.fnum = box_fl((FlNum) raw_to_double(elem_raw));
    else if (elem_type == TYPE_STR)
	elem.v.str = str_ref((const char *) (intptr_t) elem_raw);
    else if (elem_type == TYPE_LIST) {
	elem.v.list = (Var *) (intptr_t) elem_raw;
	elem = var_ref(elem);
    } else
	elem.v.num = (Num) elem_raw;

    list.v.list[1] = elem;
    return list.v.list;
}

Var *
jit_rt_list_append(Var *list, int64_t elem_raw, int elem_type)
{
    Var l, elem, res;

    l.type = TYPE_LIST;
    l.v.list = list;

    elem.type = (var_type) elem_type;
    if (elem_type == TYPE_FLOAT)
	elem.v.fnum = box_fl((FlNum) raw_to_double(elem_raw));
    else if (elem_type == TYPE_STR)
	elem.v.str = str_ref((const char *) (intptr_t) elem_raw);
    else if (elem_type == TYPE_LIST) {
	elem.v.list = (Var *) (intptr_t) elem_raw;
	elem = var_ref(elem);
    } else
	elem.v.num = (Num) elem_raw;

    res = listappend(var_ref(l), elem);
    return res.v.list;
}

Var *
jit_rt_sublist_from(Var *list, int64_t start)
{
    int len;
    int count;
    Var r;
    int i;

    if (!list)
	return new_list(0).v.list;
    len = list[0].v.num;
    if (start > len || start < 1)
	return new_list(0).v.list;
    count = len - start + 1;
    r = new_list(count);
    for (i = 0; i < count; i++)
	r.v.list[i + 1] = var_ref(list[start + i]);
    return r.v.list;
}

int64_t
jit_rt_list_in(int64_t elem_raw, int elem_type, Var *list)
{
    Var elem, l;

    l.type = TYPE_LIST;
    l.v.list = list;

    elem.type = (var_type) elem_type;
    if (elem_type == TYPE_FLOAT)
	elem.v.fnum = box_fl((FlNum) raw_to_double(elem_raw));
    else if (elem_type == TYPE_STR)
	elem.v.str = (const char *) (intptr_t) elem_raw;
    else if (elem_type == TYPE_LIST)
	elem.v.list = (Var *) (intptr_t) elem_raw;
    else
	elem.v.num = (Num) elem_raw;

    return ismember(elem, l, 0);
}

int
jit_rt_get_prop(int64_t oid_num, const char *pname, int64_t progr_num,
		int64_t *out_raw, int32_t *out_type, int32_t *err_out)
{
    Objid oid = (Objid) oid_num;
    Objid progr = (Objid) progr_num;
    Var prop, val;
    db_prop_handle h;

    if (!valid(oid)) {
	*err_out = E_INVIND;
	return 0;
    }
    h = db_find_property(oid, pname, &prop);
    if (!h.ptr) {
	*err_out = E_PROPNF;
	return 0;
    }
    if (h.built_in ? bi_prop_protected(h.built_in, progr)
		   : !db_property_allows(h, progr, PF_READ)) {
	*err_out = E_PERM;
	return 0;
    }
    val = h.built_in ? prop : var_ref(prop);
    *out_type = val.type;
    if (val.type == TYPE_FLOAT) {
	double d = (double) fl_unbox(val.v.fnum);
	*out_raw = double_to_raw(d);
    }
    else if (val.type == TYPE_STR)
	*out_raw = (intptr_t) val.v.str;
    else if (val.type == TYPE_LIST)
	*out_raw = (intptr_t) val.v.list;
    else
	*out_raw = (int64_t) val.v.num;

    *err_out = E_NONE;
    return 1;
}

int64_t
jit_rt_seconds_left(void)
{
    return (int64_t) current_task_seconds_left();
}

int64_t
jit_rt_time(void)
{
    return (int64_t) time(0);
}

int64_t
jit_rt_index(const char *source, const char *what)
{
    return (int64_t) strindex(source, what, 0);
}

int64_t
jit_rt_rindex(const char *source, const char *what)
{
    return (int64_t) strrindex(source, what, 0);
}

int64_t
jit_rt_valid(int64_t oid)
{
    return (int64_t) valid((Objid) oid);
}

int64_t
jit_rt_parent(int64_t oid, int32_t *err_out)
{
    Objid obj = (Objid) oid;
    if (!valid(obj)) {
	*err_out = E_INVARG;
	return 0;
    }
    *err_out = E_NONE;
    return (int64_t) db_object_parent(obj);
}

typedef int64_t (*NativeFunction) (Var *, Var *, int *, int *, enum error *,
				   JITSourceLocation *, int *, Num *, Objid);

typedef struct {
    MIR_context_t context;
    MIR_module_t module;
    MIR_item_t function;
    MIR_item_t proto_is_true;
    MIR_item_t import_is_true;
    MIR_item_t proto_equality;
    MIR_item_t import_equality;
    MIR_item_t proto_str_cmp;
    MIR_item_t import_str_cmp;
    MIR_item_t proto_str_concat;
    MIR_item_t import_str_concat;
    MIR_item_t proto_str_ref;
    MIR_item_t import_str_ref;
    MIR_item_t proto_list_concat;
    MIR_item_t import_list_concat;
    MIR_item_t proto_singleton_list;
    MIR_item_t import_singleton_list;
    MIR_item_t proto_list_append;
    MIR_item_t import_list_append;
    MIR_item_t proto_sublist_from;
    MIR_item_t import_sublist_from;
    MIR_item_t proto_list_in;
    MIR_item_t import_list_in;
    MIR_item_t proto_get_prop;
    MIR_item_t import_get_prop;
    MIR_item_t proto_seconds_left;
    MIR_item_t import_seconds_left;
    MIR_item_t proto_time;
    MIR_item_t import_time;
    MIR_item_t proto_index;
    MIR_item_t import_index;
    MIR_item_t proto_rindex;
    MIR_item_t import_rindex;
    MIR_item_t proto_valid;
    MIR_item_t import_valid;
    MIR_item_t proto_parent;
    MIR_item_t import_parent;
} MIRBuild;

typedef struct JITStatusExit JITStatusExit;

struct JITStatusExit {
    MIR_label_t label;
    JITRunResult status;
    enum error error;
    unsigned bytecode_pc;
    unsigned source_lineno;
    JITStatusExit *next;
};

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
    case HIR_OP_DIV:
	return MIR_DIV;
    case HIR_OP_MOD:
	return MIR_MOD;
    case HIR_OP_BITOR:
	return MIR_OR;
    case HIR_OP_BITXOR:
	return MIR_XOR;
    case HIR_OP_BITAND:
	return MIR_AND;
    case HIR_OP_SHL:
	return MIR_LSH;
    case HIR_OP_SHR:
	return MIR_RSH;
    case HIR_OP_LSHR:
	return MIR_URSH;
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

static MIR_insn_code_t
float_binary_code(HIROp op)
{
    switch (op) {
    case HIR_OP_ADD:
	return MIR_DADD;
    case HIR_OP_SUB:
	return MIR_DSUB;
    case HIR_OP_MUL:
	return MIR_DMUL;
    case HIR_OP_DIV:
	return MIR_DDIV;
    case HIR_OP_EQ:
	return MIR_DEQ;
    case HIR_OP_NE:
	return MIR_DNE;
    case HIR_OP_LT:
	return MIR_DLT;
    case HIR_OP_LE:
	return MIR_DLE;
    case HIR_OP_GT:
	return MIR_DGT;
    case HIR_OP_GE:
	return MIR_DGE;
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

static void
return_status(MIRBuild *build, MIR_reg_t status, MIR_label_t common_return,
	      JITRunResult value)
{
    append(build, MIR_new_insn(build->context, MIR_MOV,
			      MIR_new_reg_op(build->context, status),
			      MIR_new_int_op(build->context, value)));
    append(build, MIR_new_insn(build->context, MIR_JMP,
			      MIR_new_label_op(build->context, common_return)));
}

static MIR_label_t
new_status_exit(MIRBuild *build, JITStatusExit **first, JITStatusExit **last,
		JITRunResult status, enum error error, unsigned bytecode_pc,
		unsigned source_lineno)
{
    JITStatusExit *exit = mymalloc(sizeof(JITStatusExit), M_PROGRAM);

    exit->label = MIR_new_label(build->context);
    exit->status = status;
    exit->error = error;
    exit->bytecode_pc = bytecode_pc;
    exit->source_lineno = source_lineno;
    exit->next = 0;
    if (*last)
	(*last)->next = exit;
    else
	*first = exit;
    *last = exit;
    return exit->label;
}

static void
append_float_result_check(MIRBuild *build, JITInstruction *instr,
			  MIR_reg_t *values, MIR_reg_t deopt_values,
			  JITStatusExit **status_exits,
			  JITStatusExit **last_status_exit, int *copy_serial)
{
    char name[32];
    MIR_reg_t bits;
    MIR_reg_t exponent;
    MIR_reg_t exponent_mask;
    MIR_label_t float_error = new_status_exit(build, status_exits,
	last_status_exit, JIT_RUN_ERROR, E_FLOAT, instr->bytecode_pc,
	instr->source_lineno);

    sprintf(name, "float_bits%d", *copy_serial);
    bits = new_reg(build, name);
    sprintf(name, "float_exp%d", (*copy_serial)++);
    exponent = new_reg(build, name);
    sprintf(name, "float_exp_mask%d", (*copy_serial)++);
    exponent_mask = new_reg(build, name);
    append(build, MIR_new_insn(build->context, MIR_DMOV,
	MIR_new_mem_op(build->context, MIR_T_D,
			   instr->value * sizeof(Num), deopt_values, 0, 1),
	MIR_new_reg_op(build->context, values[instr->value])));
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_reg_op(build->context, bits),
	MIR_new_mem_op(build->context, MIR_T_I64,
			   instr->value * sizeof(Num), deopt_values, 0, 1)));
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_reg_op(build->context, exponent_mask),
	MIR_new_int_op(build->context, 0x7ff0000000000000LL)));
    append(build, MIR_new_insn(build->context, MIR_AND,
	MIR_new_reg_op(build->context, exponent),
	MIR_new_reg_op(build->context, bits),
	MIR_new_reg_op(build->context, exponent_mask)));
    append(build, MIR_new_insn(build->context, MIR_BEQ,
	MIR_new_label_op(build->context, float_error),
	MIR_new_reg_op(build->context, exponent),
	MIR_new_reg_op(build->context, exponent_mask)));
}

static void
append_status_exits(MIRBuild *build, JITStatusExit *exit,
		    MIR_reg_t source_location, MIR_reg_t error_out,
		    MIR_reg_t status, MIR_label_t common_return)
{
    while (exit) {
	JITStatusExit *next = exit->next;

	append(build, exit->label);
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context, MIR_T_I32,
			   offsetof(JITSourceLocation, bytecode_pc),
			   source_location, 0, 1),
	    MIR_new_int_op(build->context, exit->bytecode_pc)));
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context, MIR_T_I32,
			   offsetof(JITSourceLocation, error_pc),
			   source_location, 0, 1),
	    MIR_new_int_op(build->context, exit->bytecode_pc)));
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context, MIR_T_I32,
			   offsetof(JITSourceLocation, source_lineno),
			   source_location, 0, 1),
	    MIR_new_int_op(build->context, exit->source_lineno)));
	if (exit->error != E_NONE)
	    append(build, MIR_new_insn(build->context, MIR_MOV,
		MIR_new_mem_op(build->context, MIR_T_I32,
			       0, error_out, 0, 1),
		MIR_new_int_op(build->context, exit->error)));
	return_status(build, status, common_return, exit->status);
	myfree(exit, M_PROGRAM);
	exit = next;
    }
}

static void
append_deopt_exit(MIRBuild *build, JITProgram *program, int map_id,
		  MIR_reg_t *values, MIR_reg_t deopt_map_out,
		  MIR_reg_t deopt_values, MIR_reg_t status,
		  MIR_label_t common_return)
{
    JITDeoptMap *map = &program->deopt_maps[map_id];
    int i;

    for (i = 0; i < map->num_locals; i++) {
	int val = map->local_values[i];
	if (val > 0) {
	    if (program->value_types && program->value_types[val] == TYPE_FLOAT) {
		append(build, MIR_new_insn(build->context, MIR_DMOV,
		    MIR_new_mem_op(build->context, MIR_T_D,
				   val * sizeof(Num),
				   deopt_values, 0, 1),
		    MIR_new_reg_op(build->context, values[val])));
	    } else {
		append(build, MIR_new_insn(build->context, MIR_MOV,
		    MIR_new_mem_op(build->context,
				   sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				   val * sizeof(Num),
				   deopt_values, 0, 1),
		    MIR_new_reg_op(build->context, values[val])));
	    }
	}
    }
    for (i = 0; i < (int) map->stack_depth; i++) {
	int sval = map->stack_values[i];
	if (sval > 0) {
	    if (program->value_types && program->value_types[sval] == TYPE_FLOAT) {
		append(build, MIR_new_insn(build->context, MIR_DMOV,
		    MIR_new_mem_op(build->context, MIR_T_D,
				   sval * sizeof(Num),
				   deopt_values, 0, 1),
		    MIR_new_reg_op(build->context, values[sval])));
	    } else {
		append(build, MIR_new_insn(build->context, MIR_MOV,
		    MIR_new_mem_op(build->context,
				   sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				   sval * sizeof(Num),
				   deopt_values, 0, 1),
		    MIR_new_reg_op(build->context, values[sval])));
	    }
	}
    }
    append(build, MIR_new_insn(build->context, MIR_MOV,
			      MIR_new_mem_op(build->context, MIR_T_I32,
					     0, deopt_map_out, 0, 1),
			      MIR_new_int_op(build->context, map_id)));
    return_status(build, status, common_return, JIT_RUN_FALLBACK);
}

static int
build_mir(JITProgram *program, MIRBuild *build)
{
    MIR_type_t result_type = MIR_T_I64;
    MIR_reg_t env, result, ticks, timed_out, error_out, deopt_map_out;
    MIR_reg_t source_location, deopt_values, progr;
    MIR_reg_t tick_result, timeout_value, status;
    MIR_reg_t *values;
    MIR_label_t *labels;
    MIR_label_t fallback;
    MIR_label_t tick_abort = 0, seconds_abort = 0;
    MIR_label_t common_return;
    JITStatusExit *status_exits = 0;
    JITStatusExit *last_status_exit = 0;
    JITBlock *block;
    int max_block_id = 0;
    int copy_serial = 0;
    int i;

    memset(build, 0, sizeof(MIRBuild));
    build->context = MIR_init();
    if (!build->context)
	return 0;
    build->module = MIR_new_module(build->context, "lambda_moo_jit");
    MIR_type_t res_i64 = MIR_T_I64;
    MIR_type_t res_p = MIR_T_P;
    MIR_type_t res_i32 = MIR_T_I32;
    MIR_type_t tag_t = sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32;

    MIR_load_external(build->context, "jit_rt_is_true", (void *) jit_rt_is_true);
    MIR_load_external(build->context, "jit_rt_equality", (void *) jit_rt_equality);
    MIR_load_external(build->context, "jit_rt_str_cmp", (void *) jit_rt_str_cmp);
    MIR_load_external(build->context, "jit_rt_str_concat", (void *) jit_rt_str_concat);
    MIR_load_external(build->context, "jit_rt_str_ref", (void *) jit_rt_str_ref);
    MIR_load_external(build->context, "jit_rt_list_concat", (void *) jit_rt_list_concat);
    MIR_load_external(build->context, "jit_rt_make_singleton_list", (void *) jit_rt_make_singleton_list);
    MIR_load_external(build->context, "jit_rt_list_append", (void *) jit_rt_list_append);
    MIR_load_external(build->context, "jit_rt_sublist_from", (void *) jit_rt_sublist_from);
    MIR_load_external(build->context, "jit_rt_list_in", (void *) jit_rt_list_in);
    MIR_load_external(build->context, "jit_rt_get_prop", (void *) jit_rt_get_prop);
    MIR_load_external(build->context, "jit_rt_seconds_left", (void *) jit_rt_seconds_left);
    MIR_load_external(build->context, "jit_rt_time", (void *) jit_rt_time);
    MIR_load_external(build->context, "jit_rt_index", (void *) jit_rt_index);
    MIR_load_external(build->context, "jit_rt_rindex", (void *) jit_rt_rindex);
    MIR_load_external(build->context, "jit_rt_valid", (void *) jit_rt_valid);
    MIR_load_external(build->context, "jit_rt_parent", (void *) jit_rt_parent);

    build->proto_is_true = MIR_new_proto(build->context, "proto_is_true", 1, &res_i32, 2,
					 MIR_T_I64, "raw", MIR_T_I32, "type");
    build->import_is_true = MIR_new_import(build->context, "jit_rt_is_true");

    build->proto_equality = MIR_new_proto(build->context, "proto_equality", 1, &res_i32, 5,
					  MIR_T_I64, "r1", MIR_T_I32, "t1",
					  MIR_T_I64, "r2", MIR_T_I32, "t2",
					  MIR_T_I32, "cm");
    build->import_equality = MIR_new_import(build->context, "jit_rt_equality");

    build->proto_str_cmp = MIR_new_proto(build->context, "proto_str_cmp", 1, &res_i32, 3,
					 MIR_T_P, "s1", MIR_T_P, "s2", MIR_T_I32, "cm");
    build->import_str_cmp = MIR_new_import(build->context, "jit_rt_str_cmp");

    build->proto_str_concat = MIR_new_proto(build->context, "proto_str_concat", 1, &res_p, 3,
					    MIR_T_P, "s1", MIR_T_P, "s2", MIR_T_P, "err");
    build->import_str_concat = MIR_new_import(build->context, "jit_rt_str_concat");

    build->proto_str_ref = MIR_new_proto(build->context, "proto_str_ref", 1, &res_p, 3,
					 MIR_T_P, "s", MIR_T_I64, "idx", MIR_T_P, "err");
    build->import_str_ref = MIR_new_import(build->context, "jit_rt_str_ref");

    build->proto_list_concat = MIR_new_proto(build->context, "proto_list_concat", 1, &res_p, 3,
					     MIR_T_P, "l1", MIR_T_P, "l2", MIR_T_P, "err");
    build->import_list_concat = MIR_new_import(build->context, "jit_rt_list_concat");

    build->proto_singleton_list = MIR_new_proto(build->context, "proto_singleton_list", 1, &res_p, 2,
						MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type");
    build->import_singleton_list = MIR_new_import(build->context, "jit_rt_make_singleton_list");

    build->proto_list_append = MIR_new_proto(build->context, "proto_list_append", 1, &res_p, 3,
					     MIR_T_P, "l", MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type");
    build->import_list_append = MIR_new_import(build->context, "jit_rt_list_append");

    build->proto_sublist_from = MIR_new_proto(build->context, "proto_sublist_from", 1, &res_p, 2,
					     MIR_T_P, "list", MIR_T_I64, "start");
    build->import_sublist_from = MIR_new_import(build->context, "jit_rt_sublist_from");

    build->proto_list_in = MIR_new_proto(build->context, "proto_list_in", 1, &res_i64, 3,
					 MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type", MIR_T_P, "l");
    build->import_list_in = MIR_new_import(build->context, "jit_rt_list_in");

    build->proto_get_prop = MIR_new_proto(build->context, "proto_get_prop", 1, &res_i32, 6,
					  MIR_T_I64, "oid", MIR_T_P, "pname", MIR_T_I64, "progr",
					  MIR_T_P, "out_raw", MIR_T_P, "out_type", MIR_T_P, "err");
    build->import_get_prop = MIR_new_import(build->context, "jit_rt_get_prop");

    build->proto_seconds_left = MIR_new_proto(build->context, "proto_seconds_left", 1, &res_i64, 0);
    build->import_seconds_left = MIR_new_import(build->context, "jit_rt_seconds_left");

    build->proto_time = MIR_new_proto(build->context, "proto_time", 1, &res_i64, 0);
    build->import_time = MIR_new_import(build->context, "jit_rt_time");

    build->proto_index = MIR_new_proto(build->context, "proto_index", 1, &res_i64, 2,
				       MIR_T_P, "source", MIR_T_P, "what");
    build->import_index = MIR_new_import(build->context, "jit_rt_index");

    build->proto_rindex = MIR_new_proto(build->context, "proto_rindex", 1, &res_i64, 2,
					MIR_T_P, "source", MIR_T_P, "what");
    build->import_rindex = MIR_new_import(build->context, "jit_rt_rindex");

    build->proto_valid = MIR_new_proto(build->context, "proto_valid", 1, &res_i64, 1,
				       MIR_T_I64, "oid");
    build->import_valid = MIR_new_import(build->context, "jit_rt_valid");

    build->proto_parent = MIR_new_proto(build->context, "proto_parent", 1, &res_i64, 2,
					MIR_T_I64, "oid", MIR_T_P, "err");
    build->import_parent = MIR_new_import(build->context, "jit_rt_parent");

    build->function = MIR_new_func(build->context, "jit_verb", 1,
				   &result_type, 9,
				   MIR_T_P, "env", MIR_T_P, "result",
				   MIR_T_P, "ticks", MIR_T_P, "timed_out",
				   MIR_T_P, "error_out", MIR_T_P, "source_location",
				   MIR_T_P, "deopt_map_out", MIR_T_P, "deopt_values",
				   MIR_T_I64, "progr");
    env = MIR_reg(build->context, "env", build->function->u.func);
    result = MIR_reg(build->context, "result", build->function->u.func);
    ticks = MIR_reg(build->context, "ticks", build->function->u.func);
    timed_out = MIR_reg(build->context, "timed_out", build->function->u.func);
    error_out = MIR_reg(build->context, "error_out", build->function->u.func);
    source_location = MIR_reg(build->context, "source_location",
			      build->function->u.func);
    deopt_map_out = MIR_reg(build->context, "deopt_map_out",
			    build->function->u.func);
    deopt_values = MIR_reg(build->context, "deopt_values",
			   build->function->u.func);
    progr = MIR_reg(build->context, "progr", build->function->u.func);
    tick_result = new_reg(build, "tick_result");
    timeout_value = new_reg(build, "timeout_value");
    status = new_reg(build, "status");
    fallback = MIR_new_label(build->context);
    common_return = MIR_new_label(build->context);

    values = mymalloc(sizeof(MIR_reg_t) * program->num_values, M_PROGRAM);
    memset(values, 0, sizeof(MIR_reg_t) * program->num_values);
    for (i = 1; i < program->num_values; i++) {
	char name[32];
	sprintf(name, "v%d", i);
	if (program->value_types && program->value_types[i] == TYPE_FLOAT)
	    values[i] = MIR_new_func_reg(build->context, build->function->u.func,
					 MIR_T_D, name);
	else
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
		    if (instr->op != HIR_OP_CHARGE_TICK) {
			tick_abort = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ABORT_TICKS, E_NONE,
			    instr->bytecode_pc, instr->source_lineno);
			seconds_abort = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ABORT_SECONDS, E_NONE,
			    instr->bytecode_pc, instr->source_lineno);
		    }
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
		    if (instr->op == HIR_OP_CHARGE_TICK)
			break;
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
		case HIR_TAC_DEOPT:
		    append_deopt_exit(build, program, instr->deopt_map, values,
			deopt_map_out, deopt_values, status, common_return);
		    break;
		case HIR_TAC_CONST:
		    if (program->value_types
			&& program->value_types[instr->value] == TYPE_FLOAT) {
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context,
								 sizeof(Num) == 8
								 ? MIR_T_I64 : MIR_T_I32,
								 instr->value * sizeof(Num),
								 deopt_values, 0, 1),
						  MIR_new_int_op(build->context,
								 instr->literal)));
			append(build, MIR_new_insn(build->context, MIR_DMOV,
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_mem_op(build->context, MIR_T_D,
								 instr->value * sizeof(Num),
								 deopt_values, 0, 1)));
		    } else {
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_int_op(build->context,
								 instr->literal)));
		    }
		    if (program->value_is_tagged
			&& program->value_is_tagged[instr->value]) {
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_mem_op(build->context, tag_t,
				(program->num_values + instr->value) * sizeof(Num),
				deopt_values, 0, 1),
			    MIR_new_int_op(build->context, instr->literal_type)));
		    }
		    break;
		case HIR_TAC_LOAD_LOCAL:
		    {
			MIR_label_t deopt = MIR_new_label(build->context);
			MIR_label_t loaded = MIR_new_label(build->context);
			var_type expected_type = instr->literal_type;
			char name[32];
			sprintf(name, "var_type%d", copy_serial++);
			MIR_reg_t var_type = new_reg(build, name);

			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, var_type),
				MIR_new_mem_op(build->context, MIR_T_I32,
					instr->local_id * sizeof(Var)
					+ offsetof(Var, type), env, 0, 1)));
			append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, var_type),
				MIR_new_int_op(build->context, expected_type)));
			if (expected_type == TYPE_NONE) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context,
					       values[instr->value]),
				MIR_new_int_op(build->context, 0)));
			} else if (program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT) {
#if FLOATS_ARE_BOXED
			    sprintf(name, "fl_ptr%d", copy_serial++);
			    MIR_reg_t fl_ptr = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
						      MIR_new_reg_op(build->context, fl_ptr),
						      MIR_new_mem_op(build->context, MIR_T_P,
							      instr->local_id * sizeof(Var)
							      + offsetof(Var, v.fnum),
							      env, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_mem_op(build->context, MIR_T_D,
								     0, fl_ptr, 0, 1)));
#else
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_mem_op(build->context, MIR_T_D,
							      instr->local_id * sizeof(Var)
							      + offsetof(Var, v.fnum),
							      env, 0, 1)));
#endif
			} else {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_mem_op(build->context,
								     (expected_type == TYPE_LIST
								      || expected_type == TYPE_STR)
								     ? MIR_T_P
								     : (sizeof(Num) == 8
								     ? MIR_T_I64 : MIR_T_I32),
								     instr->local_id * sizeof(Var)
								     + (expected_type == TYPE_LIST
									? offsetof(Var, v.list)
									: (expected_type == TYPE_STR
									   ? offsetof(Var, v.str)
									   : offsetof(Var, v.num))),
								     env, 0, 1)));
			}
			append(build, MIR_new_insn(build->context, MIR_JMP,
					      MIR_new_label_op(build->context, loaded)));
			append(build, deopt);
			append_deopt_exit(build, program, instr->deopt_map, values,
					   deopt_map_out, deopt_values, status,
					   common_return);
			append(build, loaded);
		    }
		    break;
		case HIR_TAC_UNARY:
		    if (instr->kind == HIR_TAC_DEOPT) {
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->op == HIR_OP_MAKE_SINGLETON_LIST) {
			char name[32];
			sprintf(name, "sing_elem_type%d", copy_serial++);
			MIR_reg_t type_reg = new_reg(build, name);
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			} else {
			    var_type elem_type = (program->value_types
						  && instr->src1 > 0
						  && instr->src1 < program->num_values)
				? program->value_types[instr->src1] : TYPE_INT;
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_int_op(build->context, elem_type)));
			}
			append(build, MIR_new_call_insn(build->context, 5,
			    MIR_new_ref_op(build->context, build->proto_singleton_list),
			    MIR_new_ref_op(build->context, build->import_singleton_list),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, type_reg)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->value) * sizeof(Num),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			break;
		    }
		    if (instr->op == HIR_OP_CHECK_LIST_FOR_SPLICE) {
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    char name[32];
			    sprintf(name, "splice_tag%d", copy_serial++);
			    MIR_reg_t tag = new_reg(build, name);
			    MIR_label_t deopt = MIR_new_label(build->context);
			    MIR_label_t done = MIR_new_label(build->context);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, tag),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, tag),
				MIR_new_int_op(build->context, TYPE_LIST)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1])));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr->deopt_map,
				values, deopt_map_out, deopt_values, status, common_return);
			    append(build, done);
			} else if (program->value_types
				   && program->value_types[instr->src1] == TYPE_LIST) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1])));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			} else {
			    append_deopt_exit(build, program, instr->deopt_map,
				values, deopt_map_out, deopt_values, status, common_return);
			}
			break;
		    }
		    if (instr->op == HIR_OP_TICKS_LEFT) {
			append(build, MIR_new_insn(build->context, MIR_MOV,
					  MIR_new_reg_op(build->context,
							 values[instr->value]),
					  MIR_new_mem_op(build->context, MIR_T_I32,
							 0, ticks, 0, 1)));
		    } else if (instr->op == HIR_OP_SECONDS_LEFT) {
			append(build, MIR_new_call_insn(build->context, 3,
				MIR_new_ref_op(build->context,
					       build->proto_seconds_left),
				MIR_new_ref_op(build->context,
					       build->import_seconds_left),
				MIR_new_reg_op(build->context,
					       values[instr->value])));
		    } else if (instr->op == HIR_OP_TIME) {
			append(build, MIR_new_call_insn(build->context, 3,
				MIR_new_ref_op(build->context, build->proto_time),
				MIR_new_ref_op(build->context, build->import_time),
				MIR_new_reg_op(build->context,
					       values[instr->value])));
		    } else if (instr->op == HIR_OP_VALID) {
			if (program->value_types
			    && program->value_types[instr->src1] == TYPE_OBJ) {
			    append(build, MIR_new_call_insn(build->context, 4,
				MIR_new_ref_op(build->context, build->proto_valid),
				MIR_new_ref_op(build->context, build->import_valid),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1])));
			    break;
			}
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    } else if (instr->op == HIR_OP_PARENT) {
			if (program->value_types
			    && program->value_types[instr->src1] == TYPE_OBJ) {
			    char name[32];
			    sprintf(name, "parent_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t invalid_arg = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_INVARG, instr->bytecode_pc,
				instr->source_lineno);
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context, build->proto_parent),
				MIR_new_ref_op(build->context, build->import_parent),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, invalid_arg),
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_int_op(build->context, E_NONE)));
			    break;
			}
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    } else if (instr->op == HIR_OP_TOINT) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			if (val_fl || src_fl) {
			    append_deopt_exit(build, program, instr->deopt_map,
					      values, deopt_map_out, deopt_values,
					      status, common_return);
			    break;
			}
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_reg_op(build->context,
								 values[instr->src1])));
		    } else if (instr->op == HIR_OP_TYPEOF) {
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context,
								 values[instr->value]),
						  MIR_new_int_op(build->context,
								 instr->literal)));
		    } else if (instr->op == HIR_OP_ABS) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			if (val_fl != src_fl) {
			    append_deopt_exit(build, program, instr->deopt_map,
					      values, deopt_map_out, deopt_values,
					      status, common_return);
			    break;
			}
			if (src_fl) {
			    MIR_label_t is_pos = MIR_new_label(build->context);
			    MIR_label_t done = MIR_new_label(build->context);
			    char name[32];
			    sprintf(name, "zero_abs%d", copy_serial++);
			    MIR_reg_t zero = MIR_new_func_reg(build->context,
							       build->function->u.func,
							       MIR_T_D, name);
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context, zero),
						      MIR_new_mem_op(build->context, MIR_T_D,
								     0, deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_DBGE,
						      MIR_new_label_op(build->context, is_pos),
						      MIR_new_reg_op(build->context, values[instr->src1]),
						      MIR_new_reg_op(build->context, zero)));
			    append(build, MIR_new_insn(build->context, MIR_DNEG,
						      MIR_new_reg_op(build->context, values[instr->value]),
						      MIR_new_reg_op(build->context, values[instr->src1])));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
						      MIR_new_label_op(build->context, done)));
			    append(build, is_pos);
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context, values[instr->value]),
						      MIR_new_reg_op(build->context, values[instr->src1])));
			    append(build, done);
			} else {
			    MIR_label_t is_pos = MIR_new_label(build->context);
			    MIR_label_t done = MIR_new_label(build->context);
			    append(build, MIR_new_insn(build->context, MIR_BGE,
						      MIR_new_label_op(build->context, is_pos),
						      MIR_new_reg_op(build->context, values[instr->src1]),
						      MIR_new_int_op(build->context, 0)));
			    append(build, MIR_new_insn(build->context, MIR_NEG,
						      MIR_new_reg_op(build->context, values[instr->value]),
						      MIR_new_reg_op(build->context, values[instr->src1])));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
						      MIR_new_label_op(build->context, done)));
			    append(build, is_pos);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
						      MIR_new_reg_op(build->context, values[instr->value]),
						      MIR_new_reg_op(build->context, values[instr->src1])));
			    append(build, done);
			}
		    } else if (instr->op == HIR_OP_LENGTH) {
			MIR_reg_t list_ptr = values[instr->src1];
			MIR_label_t deopt = MIR_new_label(build->context);
			MIR_label_t loaded = MIR_new_label(build->context);
			MIR_label_t is_str = MIR_new_label(build->context);
			MIR_label_t is_list = MIR_new_label(build->context);
			append(build, MIR_new_insn(build->context, MIR_BEQ,
						  MIR_new_label_op(build->context, deopt),
						  MIR_new_reg_op(build->context, list_ptr),
						  MIR_new_int_op(build->context, 0)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    char name[32];
			    sprintf(name, "len_tag%d", copy_serial++);
			    MIR_reg_t tag = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, tag),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, is_list),
				MIR_new_reg_op(build->context, tag),
				MIR_new_int_op(build->context, TYPE_LIST)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, is_str),
				MIR_new_reg_op(build->context, tag),
				MIR_new_int_op(build->context, TYPE_STR)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, deopt)));
			} else if (program->value_types
				   && program->value_types[instr->src1] == TYPE_STR) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, is_str)));
			} else {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, is_list)));
			}

			/* String length */
			append(build, is_str);
			{
			    MIR_label_t scan = MIR_new_label(build->context);
			    MIR_reg_t offset;
			    MIR_reg_t byte;
#if UNICODE_STRINGS
			    MIR_label_t continuation = MIR_new_label(build->context);
			    MIR_reg_t prefix;
#endif
			    char name[32];

			    sprintf(name, "str_offset%d", copy_serial);
			    offset = new_reg(build, name);
			    sprintf(name, "str_byte%d", copy_serial);
			    byte = new_reg(build, name);
#if UNICODE_STRINGS
			    sprintf(name, "str_prefix%d", copy_serial++);
			    prefix = new_reg(build, name);
#else
			    copy_serial++;
#endif
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, offset),
				MIR_new_int_op(build->context, 0)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_int_op(build->context, 0)));
			    append(build, scan);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, byte),
				MIR_new_mem_op(build->context, MIR_T_U8, 0,
					       list_ptr, offset, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, loaded),
				MIR_new_reg_op(build->context, byte),
				MIR_new_int_op(build->context, 0)));
#if UNICODE_STRINGS
			    append(build, MIR_new_insn(build->context, MIR_AND,
				MIR_new_reg_op(build->context, prefix),
				MIR_new_reg_op(build->context, byte),
				MIR_new_int_op(build->context, 0xc0)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, continuation),
				MIR_new_reg_op(build->context, prefix),
				MIR_new_int_op(build->context, 0x80)));
#endif
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_int_op(build->context, 1)));
#if UNICODE_STRINGS
			    append(build, continuation);
#endif
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, offset),
				MIR_new_reg_op(build->context, offset),
				MIR_new_int_op(build->context, 1)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, scan)));
			}

			/* List length */
			append(build, is_list);
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_mem_op(build->context,
				sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				offsetof(Var, v.num), list_ptr, 0, 1)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->value) * sizeof(Num),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			}
			append(build, MIR_new_insn(build->context, MIR_JMP,
						  MIR_new_label_op(build->context, loaded)));
			append(build, deopt);
			append_deopt_exit(build, program, instr->deopt_map, values,
					  deopt_map_out, deopt_values, status, common_return);
			append(build, loaded);
		    } else if (instr->op == HIR_OP_NEGATE) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			if (val_fl != src_fl) {
			    append_deopt_exit(build, program, instr->deopt_map,
					      values, deopt_map_out, deopt_values,
					      status, common_return);
			    break;
			}
			if (src_fl)
			    append(build, MIR_new_insn(build->context, MIR_DNEG,
							  MIR_new_reg_op(build->context,
									 values[instr->value]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1])));
			else
			    append(build, MIR_new_insn(build->context, MIR_NEG,
							  MIR_new_reg_op(build->context,
									 values[instr->value]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1])));
		    } else if (instr->op == HIR_OP_NOT) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			if (val_fl) {
			    append_deopt_exit(build, program, instr->deopt_map,
					      values, deopt_map_out, deopt_values,
					      status, common_return);
			    break;
			}
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    char name[32];
			    sprintf(name, "not_truth%d", copy_serial++);
			    MIR_reg_t truth = new_reg(build, name);
			    sprintf(name, "not_type%d", copy_serial++);
			    MIR_reg_t type_reg = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context, build->proto_is_true),
				MIR_new_ref_op(build->context, build->import_is_true),
				MIR_new_reg_op(build->context, truth),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, type_reg)));
			    append(build, MIR_new_insn(build->context, MIR_EQ,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, truth),
				MIR_new_int_op(build->context, 0)));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    break;
			}
			if (program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT) {
			    char name[32];
			    sprintf(name, "zero_not%d", copy_serial++);
			    MIR_reg_t zero = MIR_new_func_reg(build->context,
							       build->function->u.func,
							       MIR_T_D, name);
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context, zero),
						      MIR_new_mem_op(build->context, MIR_T_D,
								     0, deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_DEQ,
							  MIR_new_reg_op(build->context,
									 values[instr->value]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1]),
							  MIR_new_reg_op(build->context, zero)));
			} else if (program->value_types
				   && (program->value_types[instr->src1] == TYPE_STR
				       || program->value_types[instr->src1] == TYPE_LIST
				       || program->value_types[instr->src1] == TYPE_OBJ
				       || program->value_types[instr->src1] == TYPE_ERR)) {
			    char name[32];
			    sprintf(name, "not_truth%d", copy_serial++);
			    MIR_reg_t truth = new_reg(build, name);
			    sprintf(name, "not_type%d", copy_serial++);
			    MIR_reg_t type_reg = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_int_op(build->context, program->value_types[instr->src1])));
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context, build->proto_is_true),
				MIR_new_ref_op(build->context, build->import_is_true),
				MIR_new_reg_op(build->context, truth),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, type_reg)));
			    append(build, MIR_new_insn(build->context, MIR_EQ,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, truth),
				MIR_new_int_op(build->context, 0)));
			} else
			    append(build, MIR_new_insn(build->context, MIR_EQ,
							  MIR_new_reg_op(build->context,
									 values[instr->value]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1]),
							  MIR_new_int_op(build->context, 0)));
		    } else {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			if (val_fl || src_fl) {
			    append_deopt_exit(build, program, instr->deopt_map,
					      values, deopt_map_out, deopt_values,
					      status, common_return);
			    break;
			}
			append(build, MIR_new_insn(build->context, MIR_XOR,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1]),
						      MIR_new_int_op(build->context, -1)));
		    }
		    break;
		case HIR_TAC_BINARY:
		    if (instr->kind == HIR_TAC_DEOPT) {
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->op == HIR_OP_LIST_ADD_TAIL) {
			char name[32];
			int tagged_list = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			MIR_label_t deopt = 0;
			MIR_label_t done = 0;

			if (tagged_list) {
			    MIR_reg_t list_type;

			    sprintf(name, "tail_list_type%d", copy_serial++);
			    list_type = new_reg(build, name);
			    deopt = MIR_new_label(build->context);
			    done = MIR_new_label(build->context);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, list_type),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, list_type),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			sprintf(name, "tail_elem_type%d", copy_serial++);
			MIR_reg_t type_reg = new_reg(build, name);
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src2]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src2) * sizeof(Num),
				    deopt_values, 0, 1)));
			} else {
			    var_type elem_type = (program->value_types
						  && instr->src2 > 0
						  && instr->src2 < program->num_values)
				? program->value_types[instr->src2] : TYPE_INT;
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_int_op(build->context, elem_type)));
			}
			append(build, MIR_new_call_insn(build->context, 6,
			    MIR_new_ref_op(build->context, build->proto_list_append),
			    MIR_new_ref_op(build->context, build->import_list_append),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, values[instr->src2]),
			    MIR_new_reg_op(build->context, type_reg)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->value) * sizeof(Num),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			if (tagged_list) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr->deopt_map,
				values, deopt_map_out, deopt_values, status,
				common_return);
			    append(build, done);
			}
			break;
		    }
		    if (instr->op == HIR_OP_GET_PROP) {
			int obj_tagged = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int obj_is_obj = program->value_types
			    && program->value_types[instr->src1] == TYPE_OBJ;

			if ((obj_is_obj || obj_tagged)
			    && program->value_types
			    && program->value_types[instr->src2] == TYPE_STR) {
			    char name[32];
			    sprintf(name, "prop_ok%d", copy_serial++);
			    MIR_reg_t prop_ok = new_reg(build, name);
			    sprintf(name, "out_raw_ptr%d", copy_serial++);
			    MIR_reg_t out_raw_ptr = new_reg(build, name);
			    sprintf(name, "out_type_ptr%d", copy_serial++);
			    MIR_reg_t out_type_ptr = new_reg(build, name);
			    MIR_label_t prop_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_NONE, instr->bytecode_pc,
				instr->source_lineno);

			    if (obj_tagged) {
				sprintf(name, "obj_type%d", copy_serial++);
				MIR_reg_t obj_type = new_reg(build, name);
				MIR_label_t deopt = MIR_new_label(build->context);
				MIR_label_t obj_ok = MIR_new_label(build->context);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, obj_type),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src1) * sizeof(Num),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BEQ,
				    MIR_new_label_op(build->context, obj_ok),
				    MIR_new_reg_op(build->context, obj_type),
				    MIR_new_int_op(build->context, TYPE_OBJ)));
				append(build, deopt);
				append_deopt_exit(build, program, instr->deopt_map,
						  values, deopt_map_out, deopt_values,
						  status, common_return);
				append(build, obj_ok);
			    }
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, out_raw_ptr),
				MIR_new_reg_op(build->context, deopt_values),
				MIR_new_int_op(build->context, instr->value * sizeof(Num))));
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, out_type_ptr),
				MIR_new_reg_op(build->context, deopt_values),
				MIR_new_int_op(build->context, (program->num_values + instr->value) * sizeof(Num))));
			    append(build, MIR_new_call_insn(build->context, 9,
				MIR_new_ref_op(build->context, build->proto_get_prop),
				MIR_new_ref_op(build->context, build->import_get_prop),
				MIR_new_reg_op(build->context, prop_ok),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2]),
				MIR_new_reg_op(build->context, progr),
				MIR_new_reg_op(build->context, out_raw_ptr),
				MIR_new_reg_op(build->context, out_type_ptr),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, prop_err),
				MIR_new_reg_op(build->context, prop_ok),
				MIR_new_int_op(build->context, 0)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_mem_op(build->context,
				    (program->value_types && program->value_types[instr->value] == TYPE_FLOAT)
				    ? MIR_T_D : (sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32),
				    instr->value * sizeof(Num), deopt_values, 0, 1)));
			    break;
			}
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->op == HIR_OP_SUBLIST_FROM) {
			append(build, MIR_new_call_insn(build->context, 5,
			    MIR_new_ref_op(build->context, build->proto_sublist_from),
			    MIR_new_ref_op(build->context, build->import_sublist_from),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, values[instr->src2])));
			break;
		    }
		    if (instr->op == HIR_OP_LIST_APPEND) {
			int tagged_l1 = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_l2 = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			MIR_label_t deopt = 0, done = 0;
			if (tagged_l1 || tagged_l2) {
			    deopt = MIR_new_label(build->context);
			    done = MIR_new_label(build->context);
			    if (tagged_l1) {
				char name[32];
				sprintf(name, "lapp_t1_%d", copy_serial++);
				MIR_reg_t t1 = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src1) * sizeof(Num),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			    if (tagged_l2) {
				char name[32];
				sprintf(name, "lapp_t2_%d", copy_serial++);
				MIR_reg_t t2 = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src2) * sizeof(Num),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			}
			append(build, MIR_new_call_insn(build->context, 6,
			    MIR_new_ref_op(build->context, build->proto_list_concat),
			    MIR_new_ref_op(build->context, build->import_list_concat),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, values[instr->src2]),
			    MIR_new_reg_op(build->context, error_out)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->value) * sizeof(Num),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			if (tagged_l1 || tagged_l2) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr->deopt_map,
				values, deopt_map_out, deopt_values, status, common_return);
			    append(build, done);
			}
			break;
		    }
		    if (instr->op == HIR_OP_IN) {
			int tagged_list = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];

			if (tagged_list || (program->value_types
			    && program->value_types[instr->src2] == TYPE_LIST)) {
			    var_type elem_type = program->value_types[instr->src1];
			    char name[32];
			    MIR_label_t deopt = 0, done = 0;
			    sprintf(name, "in_type%d", copy_serial++);
			    MIR_reg_t in_type = new_reg(build, name);
			    if (tagged_list) {
				MIR_reg_t list_type;

				sprintf(name, "in_list_type%d", copy_serial++);
				list_type = new_reg(build, name);
				deopt = MIR_new_label(build->context);
				done = MIR_new_label(build->context);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, list_type),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src2) * sizeof(Num),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, list_type),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->src1])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, in_type),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src1) * sizeof(Num),
					deopt_values, 0, 1)));
			    else
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, in_type),
				    MIR_new_int_op(build->context, elem_type)));
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context, build->proto_list_in),
				MIR_new_ref_op(build->context, build->import_list_in),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, in_type),
				MIR_new_reg_op(build->context, values[instr->src2])));
			    if (tagged_list) {
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));
				append(build, deopt);
				append_deopt_exit(build, program, instr->deopt_map,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, done);
			    }
			    break;
			}
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->op == HIR_OP_INDEX_BF
			|| instr->op == HIR_OP_RINDEX_BF) {
			int tagged_s1 = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_s2 = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			int is_str1 = program->value_types
			    && program->value_types[instr->src1] == TYPE_STR;
			int is_str2 = program->value_types
			    && program->value_types[instr->src2] == TYPE_STR;

			if ((tagged_s1 || is_str1) && (tagged_s2 || is_str2)) {
			    MIR_item_t proto = (instr->op == HIR_OP_INDEX_BF)
				? build->proto_index : build->proto_rindex;
			    MIR_item_t import = (instr->op == HIR_OP_INDEX_BF)
				? build->import_index : build->import_rindex;
			    MIR_label_t deopt = 0;
			    MIR_label_t done = 0;

			    if (tagged_s1 || tagged_s2) {
				char name[32];

				deopt = MIR_new_label(build->context);
				done = MIR_new_label(build->context);
				if (tagged_s1) {
				    MIR_reg_t type;

				    sprintf(name, "index_s1_type%d", copy_serial++);
				    type = new_reg(build, name);
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, type),
					MIR_new_mem_op(build->context, tag_t,
					    (program->num_values + instr->src1)
					    * sizeof(Num), deopt_values, 0, 1)));
				    append(build, MIR_new_insn(build->context, MIR_BNE,
					MIR_new_label_op(build->context, deopt),
					MIR_new_reg_op(build->context, type),
					MIR_new_int_op(build->context, TYPE_STR)));
				}
				if (tagged_s2) {
				    MIR_reg_t type;

				    sprintf(name, "index_s2_type%d", copy_serial++);
				    type = new_reg(build, name);
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, type),
					MIR_new_mem_op(build->context, tag_t,
					    (program->num_values + instr->src2)
					    * sizeof(Num), deopt_values, 0, 1)));
				    append(build, MIR_new_insn(build->context, MIR_BNE,
					MIR_new_label_op(build->context, deopt),
					MIR_new_reg_op(build->context, type),
					MIR_new_int_op(build->context, TYPE_STR)));
				}
			    }
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context, proto),
				MIR_new_ref_op(build->context, import),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2])));
			    if (tagged_s1 || tagged_s2) {
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));
				append(build, deopt);
				append_deopt_exit(build, program, instr->deopt_map,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, done);
			    }
			    break;
			}
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if ((instr->op == HIR_OP_EQ || instr->op == HIR_OP_NE)
			&& program->value_is_tagged
			&& (program->value_is_tagged[instr->src1]
			    || program->value_is_tagged[instr->src2])) {
			char name[32];
			MIR_reg_t eq_res, type1, type2, case_reg;

			sprintf(name, "tag_eq%d", copy_serial++);
			eq_res = new_reg(build, name);
			sprintf(name, "tag_type%d", copy_serial++);
			type1 = new_reg(build, name);
			sprintf(name, "tag_type%d", copy_serial++);
			type2 = new_reg(build, name);
			sprintf(name, "case_reg%d", copy_serial++);
			case_reg = new_reg(build, name);
			if (program->value_is_tagged[instr->src1])
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type1),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			else
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type1),
				MIR_new_int_op(build->context,
				    program->value_types[instr->src1])));
			if (program->value_is_tagged[instr->src2])
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type2),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src2) * sizeof(Num),
				    deopt_values, 0, 1)));
			else
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type2),
				MIR_new_int_op(build->context,
				    program->value_types[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, case_reg),
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_call_insn(build->context, 8,
			    MIR_new_ref_op(build->context, build->proto_equality),
			    MIR_new_ref_op(build->context, build->import_equality),
			    MIR_new_reg_op(build->context, eq_res),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, type1),
			    MIR_new_reg_op(build->context, values[instr->src2]),
			    MIR_new_reg_op(build->context, type2),
			    MIR_new_reg_op(build->context, case_reg)));
			if (instr->op == HIR_OP_EQ)
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, eq_res)));
			else
			    append(build, MIR_new_insn(build->context, MIR_EQ,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, eq_res),
				MIR_new_int_op(build->context, 0)));
			break;
		    }
		    if (program->value_types
			&& program->value_types[instr->src1] == TYPE_STR
			&& program->value_types[instr->src2] == TYPE_STR
			&& (instr->op == HIR_OP_EQ || instr->op == HIR_OP_NE
			    || instr->op == HIR_OP_LT || instr->op == HIR_OP_LE
			    || instr->op == HIR_OP_GT || instr->op == HIR_OP_GE)) {
			char name[32];
			sprintf(name, "str_cmp%d", copy_serial++);
			MIR_reg_t cmp_res = new_reg(build, name);
			sprintf(name, "case_reg%d", copy_serial++);
			MIR_reg_t case_reg = new_reg(build, name);
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, case_reg),
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_call_insn(build->context, 6,
			    MIR_new_ref_op(build->context, build->proto_str_cmp),
			    MIR_new_ref_op(build->context, build->import_str_cmp),
			    MIR_new_reg_op(build->context, cmp_res),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, values[instr->src2]),
			    MIR_new_reg_op(build->context, case_reg)));
			MIR_insn_code_t code = (instr->op == HIR_OP_EQ) ? MIR_EQ
					     : (instr->op == HIR_OP_NE) ? MIR_NE
					     : (instr->op == HIR_OP_LT) ? MIR_LT
					     : (instr->op == HIR_OP_LE) ? MIR_LE
					     : (instr->op == HIR_OP_GT) ? MIR_GT
					     : MIR_GE;
			append(build, MIR_new_insn(build->context, code,
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, cmp_res),
			    MIR_new_int_op(build->context, 0)));
			break;
		    }
		    if (program->value_types
			&& program->value_types[instr->src1] == TYPE_LIST
			&& program->value_types[instr->src2] == TYPE_LIST
			&& (instr->op == HIR_OP_EQ || instr->op == HIR_OP_NE)) {
			char name[32];
			sprintf(name, "list_eq%d", copy_serial++);
			MIR_reg_t eq_res = new_reg(build, name);
			sprintf(name, "ltype_reg%d", copy_serial++);
			MIR_reg_t ltype_reg = new_reg(build, name);
			sprintf(name, "case_reg%d", copy_serial++);
			MIR_reg_t case_reg = new_reg(build, name);
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, ltype_reg),
			    MIR_new_int_op(build->context, TYPE_LIST)));
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, case_reg),
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_call_insn(build->context, 8,
			    MIR_new_ref_op(build->context, build->proto_equality),
			    MIR_new_ref_op(build->context, build->import_equality),
			    MIR_new_reg_op(build->context, eq_res),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, ltype_reg),
			    MIR_new_reg_op(build->context, values[instr->src2]),
			    MIR_new_reg_op(build->context, ltype_reg),
			    MIR_new_reg_op(build->context, case_reg)));
			if (instr->op == HIR_OP_EQ)
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, eq_res)));
			else
			    append(build, MIR_new_insn(build->context, MIR_EQ,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, eq_res),
				MIR_new_int_op(build->context, 0)));
			break;
		    }
		    if (instr->op == HIR_OP_ADD) {
			int is_str1 = program->value_types
			    && program->value_types[instr->src1] == TYPE_STR;
			int is_str2 = program->value_types
			    && program->value_types[instr->src2] == TYPE_STR;
			int tagged_s1 = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_s2 = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];

			if (is_str1 && is_str2) {
			    char name[32];
			    sprintf(name, "str_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t quota_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_QUOTA, instr->bytecode_pc,
				instr->source_lineno);
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context, build->proto_str_concat),
				MIR_new_ref_op(build->context, build->import_str_concat),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2]),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, quota_error),
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_int_op(build->context, E_NONE)));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_STR)));
			    }
			    break;
			}
			if ((is_str1 || tagged_s1) && (is_str2 || tagged_s2)) {
			    MIR_label_t deopt = MIR_new_label(build->context);
			    MIR_label_t done = MIR_new_label(build->context);
			    MIR_label_t do_concat = MIR_new_label(build->context);
			    MIR_label_t do_add = MIR_new_label(build->context);
			    char name[32];
			    sprintf(name, "add_t1_%d", copy_serial++);
			    MIR_reg_t t1 = new_reg(build, name);
			    sprintf(name, "add_t2_%d", copy_serial++);
			    MIR_reg_t t2 = new_reg(build, name);
			    sprintf(name, "str_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t quota_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_QUOTA, instr->bytecode_pc,
				instr->source_lineno);

			    if (tagged_s1) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src1) * sizeof(Num),
					deopt_values, 0, 1)));
			    } else {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_int_op(build->context, is_str1 ? TYPE_STR : TYPE_INT)));
			    }
			    if (tagged_s2) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src2) * sizeof(Num),
					deopt_values, 0, 1)));
			    } else {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_int_op(build->context, is_str2 ? TYPE_STR : TYPE_INT)));
			    }

			    /* If both are TYPE_STR -> do_concat */
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, do_add),
				MIR_new_reg_op(build->context, t1),
				MIR_new_int_op(build->context, TYPE_STR)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, do_concat),
				MIR_new_reg_op(build->context, t2),
				MIR_new_int_op(build->context, TYPE_STR)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, deopt)));

			    /* Check if both are TYPE_INT -> do_add */
			    append(build, do_add);
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, t1),
				MIR_new_int_op(build->context, TYPE_INT)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, t2),
				MIR_new_int_op(build->context, TYPE_INT)));
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2])));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));

			    /* Concat */
			    append(build, do_concat);
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context, build->proto_str_concat),
				MIR_new_ref_op(build->context, build->import_str_concat),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2]),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, quota_error),
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_int_op(build->context, E_NONE)));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_STR)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));

			    append(build, deopt);
			    append_deopt_exit(build, program, instr->deopt_map,
				values, deopt_map_out, deopt_values, status, common_return);
			    append(build, done);
			    break;
			}
		    }
		    if (program->value_types
			&& (instr->op == HIR_OP_ADD || instr->op == HIR_OP_SUB
			    || instr->op == HIR_OP_MUL || instr->op == HIR_OP_DIV
			    || instr->op == HIR_OP_MOD || instr->op == HIR_OP_EXP
			    || instr->op == HIR_OP_EQ || instr->op == HIR_OP_NE
			    || instr->op == HIR_OP_LT || instr->op == HIR_OP_LE
			    || instr->op == HIR_OP_GT || instr->op == HIR_OP_GE)
			&& (program->value_types[instr->value] == TYPE_FLOAT
			    || program->value_types[instr->src1] == TYPE_FLOAT
			    || program->value_types[instr->src2] == TYPE_FLOAT)) {
			int is_float_arith = (instr->op == HIR_OP_ADD
					      || instr->op == HIR_OP_SUB
					      || instr->op == HIR_OP_MUL
					      || instr->op == HIR_OP_DIV);
			int is_float_cmp = (instr->op == HIR_OP_EQ
					    || instr->op == HIR_OP_NE
					    || instr->op == HIR_OP_LT
					    || instr->op == HIR_OP_LE
					    || instr->op == HIR_OP_GT
					    || instr->op == HIR_OP_GE);
			int valid_float_op = (is_float_arith
					      && program->value_types[instr->value] == TYPE_FLOAT
					      && program->value_types[instr->src1] == TYPE_FLOAT
					      && program->value_types[instr->src2] == TYPE_FLOAT)
			    || (is_float_cmp
				&& program->value_types[instr->src1] == TYPE_FLOAT
				&& program->value_types[instr->src2] == TYPE_FLOAT);

			if (!valid_float_op) {
			    append_deopt_exit(build, program, instr->deopt_map,
					      values, deopt_map_out, deopt_values,
					      status, common_return);
			    break;
			}
			if (is_float_cmp) {
			    append(build, MIR_new_insn(build->context,
						      float_binary_code(instr->op),
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1]),
						      MIR_new_reg_op(build->context,
								     values[instr->src2])));
			    break;
			}
			if (instr->op == HIR_OP_DIV) {
			    char name[32];
			    sprintf(name, "zero_div%d", copy_serial++);
			    MIR_reg_t zero = MIR_new_func_reg(build->context,
							       build->function->u.func,
							       MIR_T_D, name);
			    MIR_label_t division_by_zero = new_status_exit(build,
				&status_exits, &last_status_exit, JIT_RUN_ERROR,
				E_DIV, instr->bytecode_pc, instr->source_lineno);
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context, zero),
						      MIR_new_mem_op(build->context, MIR_T_D,
								     0, deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_DBEQ,
						      MIR_new_label_op(build->context,
								       division_by_zero),
						      MIR_new_reg_op(build->context,
								     values[instr->src2]),
						      MIR_new_reg_op(build->context, zero)));
			    append(build, MIR_new_insn(build->context, MIR_DDIV,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_reg_op(build->context,
								     values[instr->src1]),
						      MIR_new_reg_op(build->context,
								     values[instr->src2])));
			} else {
			    if (values[instr->value] == values[instr->src1]
				&& values[instr->value] == values[instr->src2]) {
				char name[32];
				sprintf(name, "fl_tmp%d", copy_serial++);
				MIR_reg_t tmp = MIR_new_func_reg(build->context,
								   build->function->u.func,
								   MIR_T_D, name);
				append(build, MIR_new_insn(build->context,
							  float_binary_code(instr->op),
							  MIR_new_reg_op(build->context, tmp),
							  MIR_new_reg_op(build->context,
									 values[instr->src1]),
							  MIR_new_reg_op(build->context,
									 values[instr->src2])));
				append(build, MIR_new_insn(build->context, MIR_DMOV,
							  MIR_new_reg_op(build->context,
									 values[instr->value]),
							  MIR_new_reg_op(build->context, tmp)));
			    } else {
				append(build, MIR_new_insn(build->context,
							  float_binary_code(instr->op),
							  MIR_new_reg_op(build->context,
									 values[instr->value]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1]),
							  MIR_new_reg_op(build->context,
									 values[instr->src2])));
			    }
			}
			if (instr->op == HIR_OP_ADD || instr->op == HIR_OP_SUB
			    || instr->op == HIR_OP_MUL || instr->op == HIR_OP_DIV)
			    append_float_result_check(build, instr, values,
				deopt_values, &status_exits, &last_status_exit,
				&copy_serial);
			break;
		    }
		    if (instr->op == HIR_OP_MIN) {
			MIR_label_t is_lhs = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);
			append(build, MIR_new_insn(build->context, MIR_BLT,
						  MIR_new_label_op(build->context, is_lhs),
						  MIR_new_reg_op(build->context, values[instr->src1]),
						  MIR_new_reg_op(build->context, values[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context, values[instr->value]),
						  MIR_new_reg_op(build->context, values[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_JMP,
						  MIR_new_label_op(build->context, done)));
			append(build, is_lhs);
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context, values[instr->value]),
						  MIR_new_reg_op(build->context, values[instr->src1])));
			append(build, done);
			break;
		    }
		    if (instr->op == HIR_OP_MAX) {
			MIR_label_t is_lhs = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);
			append(build, MIR_new_insn(build->context, MIR_BGT,
						  MIR_new_label_op(build->context, is_lhs),
						  MIR_new_reg_op(build->context, values[instr->src1]),
						  MIR_new_reg_op(build->context, values[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context, values[instr->value]),
						  MIR_new_reg_op(build->context, values[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_JMP,
						  MIR_new_label_op(build->context, done)));
			append(build, is_lhs);
			append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_reg_op(build->context, values[instr->value]),
						  MIR_new_reg_op(build->context, values[instr->src1])));
			append(build, done);
			break;
		    }
		    {
			MIR_label_t arithmetic_error = 0;
			MIR_label_t invalid_argument = 0;
			MIR_label_t range_error = 0;

			if (instr->op == HIR_OP_DIV || instr->op == HIR_OP_MOD
			    || instr->op == HIR_OP_EXP)
			    arithmetic_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_DIV,
				instr->bytecode_pc, instr->source_lineno);
			if (instr->op == HIR_OP_SHL || instr->op == HIR_OP_SHR
			    || instr->op == HIR_OP_LSHR)
			    invalid_argument = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_INVARG,
				instr->bytecode_pc, instr->source_lineno);
			if (instr->op == HIR_OP_INDEX)
			    range_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_RANGE,
				instr->bytecode_pc, instr->source_lineno);
		    if (instr->op == HIR_OP_INDEX) {
			if (program->value_types
			    && program->value_types[instr->src1] == TYPE_STR) {
			    char name[32];
			    sprintf(name, "str_idx_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t range_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_RANGE,
				instr->bytecode_pc, instr->source_lineno);
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context, build->proto_str_ref),
				MIR_new_ref_op(build->context, build->import_str_ref),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2]),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, range_err),
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_int_op(build->context, E_NONE)));
			    break;
			}
			MIR_label_t deopt = MIR_new_label(build->context);
			MIR_label_t loaded = MIR_new_label(build->context);
			MIR_label_t is_list = MIR_new_label(build->context);
			MIR_label_t is_str = MIR_new_label(build->context);
			MIR_reg_t list_ptr = values[instr->src1];
			MIR_reg_t index = values[instr->src2];
			char name[32];
			sprintf(name, "list_len%d", copy_serial);
			MIR_reg_t list_len = new_reg(build, name);
			sprintf(name, "elem_offset%d", copy_serial);
			MIR_reg_t elem_offset = new_reg(build, name);
			sprintf(name, "elem_addr%d", copy_serial);
			MIR_reg_t elem_addr = new_reg(build, name);
			sprintf(name, "elem_type%d", copy_serial);
			MIR_reg_t elem_type = new_reg(build, name);
			int tagged_base = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_index = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			var_type expected_elem_type = program->value_types
			    ? program->value_types[instr->value] : TYPE_INT;
			int tagged_result = program->value_is_tagged
			    && program->value_is_tagged[instr->value];
			copy_serial++;

			if (tagged_index) {
			    MIR_reg_t index_type;

			    sprintf(name, "index_type%d", copy_serial++);
			    index_type = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, index_type),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src2) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, index_type),
				MIR_new_int_op(build->context, TYPE_INT)));
			}
			if (tagged_base) {
			    MIR_reg_t base_type;

			    sprintf(name, "base_type%d", copy_serial++);
			    base_type = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, base_type),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, is_list),
				MIR_new_reg_op(build->context, base_type),
				MIR_new_int_op(build->context, TYPE_LIST)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, is_str),
				MIR_new_reg_op(build->context, base_type),
				MIR_new_int_op(build->context, TYPE_STR)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, deopt)));

			    /* String indexing */
			    append(build, is_str);
			    char name_err[32];
			    sprintf(name_err, "str_idx_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name_err);
			    MIR_label_t str_range_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_RANGE,
				instr->bytecode_pc, instr->source_lineno);
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context, build->proto_str_ref),
				MIR_new_ref_op(build->context, build->import_str_ref),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2]),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, str_range_err),
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_int_op(build->context, E_NONE)));
			    if (tagged_result) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->value) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_STR)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, loaded)));

			    append(build, is_list);
			}
			append(build, MIR_new_insn(build->context, MIR_BLT,
				MIR_new_label_op(build->context, range_error),
				MIR_new_reg_op(build->context, index),
				MIR_new_int_op(build->context, 1)));
			append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, list_ptr),
				MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, list_len),
				MIR_new_mem_op(build->context,
					sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
					offsetof(Var, v.num), list_ptr, 0, 1)));
			append(build, MIR_new_insn(build->context, MIR_BGT,
				MIR_new_label_op(build->context, range_error),
				MIR_new_reg_op(build->context, index),
				MIR_new_reg_op(build->context, list_len)));
			append(build, MIR_new_insn(build->context, MIR_MUL,
				MIR_new_reg_op(build->context, elem_offset),
				MIR_new_reg_op(build->context, index),
				MIR_new_int_op(build->context, sizeof(Var))));
			append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, elem_addr),
				MIR_new_reg_op(build->context, list_ptr),
				MIR_new_reg_op(build->context, elem_offset)));
			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, elem_type),
				MIR_new_mem_op(build->context, MIR_T_I32,
					offsetof(Var, type), elem_addr, 0, 1)));

			if (tagged_result)
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->value) * sizeof(Num),
				    deopt_values, 0, 1),
				MIR_new_reg_op(build->context, elem_type)));
			else
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, elem_type),
				MIR_new_int_op(build->context, expected_elem_type)));
			if (tagged_result) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_mem_op(build->context,
				    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				    offsetof(Var, v.num), elem_addr, 0, 1)));
			} else if (expected_elem_type == TYPE_FLOAT) {
#if FLOATS_ARE_BOXED
			    sprintf(name, "elem_fl_ptr%d", copy_serial++);
			    MIR_reg_t elem_fl_ptr = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
						      MIR_new_reg_op(build->context, elem_fl_ptr),
						      MIR_new_mem_op(build->context, MIR_T_P,
							      offsetof(Var, v.fnum),
							      elem_addr, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_mem_op(build->context, MIR_T_D,
								     0, elem_fl_ptr, 0, 1)));
#else
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context,
								     values[instr->value]),
						      MIR_new_mem_op(build->context, MIR_T_D,
							      offsetof(Var, v.fnum),
							      elem_addr, 0, 1)));
#endif
			} else {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_mem_op(build->context,
					(expected_elem_type == TYPE_LIST
					 || expected_elem_type == TYPE_STR)
					? MIR_T_P
					: (sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32),
					(expected_elem_type == TYPE_LIST
					 ? offsetof(Var, v.list)
					 : (expected_elem_type == TYPE_STR
					    ? offsetof(Var, v.str)
					    : offsetof(Var, v.num))),
					elem_addr, 0, 1)));
			}
			append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, loaded)));
			append(build, deopt);
			append_deopt_exit(build, program, instr->deopt_map, values,
					  deopt_map_out, deopt_values, status,
					  common_return);
			append(build, loaded);
		    } else {
			int tagged_src1 = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_src2 = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			int tagged_dst = program->value_is_tagged
			    && program->value_is_tagged[instr->value];

			if (tagged_src1 || tagged_src2) {
			    MIR_label_t deopt = MIR_new_label(build->context);
			    MIR_label_t type_checked = MIR_new_label(build->context);
			    if (tagged_src1) {
				char name[32];
				sprintf(name, "arith_t1_%d", copy_serial++);
				MIR_reg_t t1 = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src1) * sizeof(Num),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    if (tagged_src2) {
				char name[32];
				sprintf(name, "arith_t2_%d", copy_serial++);
				MIR_reg_t t2 = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + instr->src2) * sizeof(Num),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, type_checked)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr->deopt_map,
				values, deopt_map_out, deopt_values, status, common_return);
			    append(build, type_checked);
			}
			if (tagged_dst) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->value) * sizeof(Num),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			}
			if (instr->op == HIR_OP_EXP) {
			MIR_label_t nonnegative = MIR_new_label(build->context);
			MIR_label_t negative_one = MIR_new_label(build->context);
			MIR_label_t loop = MIR_new_label(build->context);
			MIR_label_t skip_multiply = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);
			MIR_reg_t base, power, low_bit;
			char name[32];

			sprintf(name, "power_base%d", copy_serial);
			base = new_reg(build, name);
			sprintf(name, "power_exp%d", copy_serial);
			power = new_reg(build, name);
			sprintf(name, "power_bit%d", copy_serial++);
			low_bit = new_reg(build, name);
			append(build, MIR_new_insn(build->context, MIR_BGE,
				MIR_new_label_op(build->context, nonnegative),
				MIR_new_reg_op(build->context,
						 values[instr->src2]),
				MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_BF,
				MIR_new_label_op(build->context,
						 arithmetic_error),
				MIR_new_reg_op(build->context,
						 values[instr->src1])));
			append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, negative_one),
				MIR_new_reg_op(build->context,
						 values[instr->src1]),
				MIR_new_int_op(build->context, -1)));
			append(build, MIR_new_insn(build->context, MIR_EQ,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->src1]),
				MIR_new_int_op(build->context, 1)));
			append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			append(build, negative_one);
			append(build, MIR_new_insn(build->context, MIR_AND,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->src2]),
				MIR_new_int_op(build->context, 1)));
			append(build, MIR_new_insn(build->context, MIR_MUL,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_int_op(build->context, 2)));
			append(build, MIR_new_insn(build->context, MIR_SUB,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_int_op(build->context, 1)));
			append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			append(build, nonnegative);
			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, base),
				MIR_new_reg_op(build->context,
						 values[instr->src1])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, power),
				MIR_new_reg_op(build->context,
						 values[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_int_op(build->context, 1)));
			append(build, loop);
			append(build, MIR_new_insn(build->context, MIR_BF,
				MIR_new_label_op(build->context, done),
				MIR_new_reg_op(build->context, power)));
			append(build, MIR_new_insn(build->context, MIR_AND,
				MIR_new_reg_op(build->context, low_bit),
				MIR_new_reg_op(build->context, power),
				MIR_new_int_op(build->context, 1)));
			append(build, MIR_new_insn(build->context, MIR_BF,
				MIR_new_label_op(build->context, skip_multiply),
				MIR_new_reg_op(build->context, low_bit)));
			append(build, MIR_new_insn(build->context, MIR_MUL,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context, base)));
			append(build, skip_multiply);
		    {
			char bsq_name[32];
			sprintf(bsq_name, "base_sq%d", copy_serial);
			MIR_reg_t base_sq = new_reg(build, bsq_name);
			append(build, MIR_new_insn(build->context, MIR_MUL,
				MIR_new_reg_op(build->context, base_sq),
				MIR_new_reg_op(build->context, base),
				MIR_new_reg_op(build->context, base)));
			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, base),
				MIR_new_reg_op(build->context, base_sq)));
		    }
			append(build, MIR_new_insn(build->context, MIR_URSH,
				MIR_new_reg_op(build->context, power),
				MIR_new_reg_op(build->context, power),
				MIR_new_int_op(build->context, 1)));
			append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, loop)));
			append(build, done);
		    } else if (instr->op == HIR_OP_DIV || instr->op == HIR_OP_MOD) {
			MIR_label_t normal = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);

			append(build, MIR_new_insn(build->context, MIR_BF,
				MIR_new_label_op(build->context,
						 arithmetic_error),
				MIR_new_reg_op(build->context,
						 values[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, normal),
				MIR_new_reg_op(build->context,
						 values[instr->src2]),
				MIR_new_int_op(build->context, -1)));
			append(build, instr->op == HIR_OP_DIV
			       ? MIR_new_insn(build->context, MIR_NEG,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->src1]))
			       : MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			append(build, normal);
			append(build, MIR_new_insn(build->context,
						  binary_code(instr->op),
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->src1]),
				MIR_new_reg_op(build->context,
						 values[instr->src2])));
			append(build, done);
		    } else {
			if (instr->op == HIR_OP_SHL || instr->op == HIR_OP_SHR
			    || instr->op == HIR_OP_LSHR) {
			    append(build, MIR_new_insn(build->context, MIR_BLT,
				MIR_new_label_op(build->context,
						 invalid_argument),
				MIR_new_reg_op(build->context,
						 values[instr->src2]),
				MIR_new_int_op(build->context, 0)));
			    append(build, MIR_new_insn(build->context, MIR_BGE,
				MIR_new_label_op(build->context,
						 invalid_argument),
				MIR_new_reg_op(build->context,
						 values[instr->src2]),
				MIR_new_int_op(build->context,
						 sizeof(Num) * CHAR_BIT)));
			}
			if (values[instr->value] == values[instr->src1]
			    && values[instr->value] == values[instr->src2]) {
			    char name[32];
			    sprintf(name, "bin_tmp%d", copy_serial++);
			    MIR_reg_t tmp = new_reg(build, name);
			    append(build, MIR_new_insn(build->context,
						      binary_code(instr->op),
				MIR_new_reg_op(build->context, tmp),
				MIR_new_reg_op(build->context,
						 values[instr->src1]),
				MIR_new_reg_op(build->context,
						 values[instr->src2])));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context, tmp)));
			} else {
			    append(build, MIR_new_insn(build->context,
						      binary_code(instr->op),
				MIR_new_reg_op(build->context,
						 values[instr->value]),
				MIR_new_reg_op(build->context,
						 values[instr->src1]),
				MIR_new_reg_op(build->context,
						 values[instr->src2])));
			}
		    }
		    }
		    }
		    break;
		case HIR_TAC_PARALLEL_COPY:
		    {
			JITCopy *copy;
			int count = 0;
			int n = 0;
			MIR_reg_t *temps;
			MIR_reg_t *tag_temps;
			for (copy = instr->copies; copy; copy = copy->next)
			    count++;
			temps = mymalloc(sizeof(MIR_reg_t) * count, M_PROGRAM);
			tag_temps = mymalloc(sizeof(MIR_reg_t) * count, M_PROGRAM);
			memset(tag_temps, 0, sizeof(MIR_reg_t) * count);
			for (copy = instr->copies; copy; copy = copy->next) {
			    char name[32];
			    sprintf(name, "copy%d", copy_serial++);
			    if (program->value_types
				&& program->value_types[copy->src] == TYPE_FLOAT) {
				temps[n] = MIR_new_func_reg(build->context,
							    build->function->u.func,
							    MIR_T_D, name);
				append(build, MIR_new_insn(build->context, MIR_DMOV,
							  MIR_new_reg_op(build->context,
									 temps[n]),
							  MIR_new_reg_op(build->context,
									 values[copy->src])));
			    } else {
				temps[n] = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
							  MIR_new_reg_op(build->context,
									 temps[n]),
							  MIR_new_reg_op(build->context,
									 values[copy->src])));
			    }
			    if (program->value_is_tagged
				&& program->value_is_tagged[copy->dst]) {
				sprintf(name, "copy_tag%d", copy_serial++);
				tag_temps[n] = new_reg(build, name);
				if (program->value_is_tagged[copy->src])
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, tag_temps[n]),
					MIR_new_mem_op(build->context, tag_t,
					    (program->num_values + copy->src) * sizeof(Num),
					    deopt_values, 0, 1)));
				else
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, tag_temps[n]),
					MIR_new_int_op(build->context,
					    program->value_types[copy->src])));
			    }
			    n++;
			}
			n = 0;
			for (copy = instr->copies; copy; copy = copy->next) {
			    int src_fl = program->value_types
				&& program->value_types[copy->src] == TYPE_FLOAT;
			    int dst_fl = program->value_types
				&& program->value_types[copy->dst] == TYPE_FLOAT;

			    if (src_fl && dst_fl) {
				append(build, MIR_new_insn(build->context, MIR_DMOV,
							  MIR_new_reg_op(build->context,
									 values[copy->dst]),
							  MIR_new_reg_op(build->context,
									 temps[n])));
			    } else if (!src_fl && !dst_fl) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
							  MIR_new_reg_op(build->context,
									 values[copy->dst]),
							  MIR_new_reg_op(build->context,
									 temps[n])));
			    } else if (!src_fl && dst_fl) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
							  MIR_new_mem_op(build->context,
									 sizeof(Num) == 8
									 ? MIR_T_I64 : MIR_T_I32,
									 copy->dst * sizeof(Num),
									 deopt_values, 0, 1),
							  MIR_new_reg_op(build->context,
									 temps[n])));
				append(build, MIR_new_insn(build->context, MIR_DMOV,
							  MIR_new_reg_op(build->context,
									 values[copy->dst]),
							  MIR_new_mem_op(build->context,
									 MIR_T_D,
									 copy->dst * sizeof(Num),
									 deopt_values, 0, 1)));
			    } else {
				append(build, MIR_new_insn(build->context, MIR_DMOV,
							  MIR_new_mem_op(build->context,
									 MIR_T_D,
									 copy->dst * sizeof(Num),
									 deopt_values, 0, 1),
							  MIR_new_reg_op(build->context,
									 temps[n])));
				append(build, MIR_new_insn(build->context, MIR_MOV,
							  MIR_new_reg_op(build->context,
									 values[copy->dst]),
							  MIR_new_mem_op(build->context,
									 sizeof(Num) == 8
									 ? MIR_T_I64 : MIR_T_I32,
									 copy->dst * sizeof(Num),
									 deopt_values, 0, 1)));
			    }
			    if (tag_temps[n])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					(program->num_values + copy->dst) * sizeof(Num),
					deopt_values, 0, 1),
				    MIR_new_reg_op(build->context, tag_temps[n])));
			    n++;
			}
			myfree(tag_temps, M_PROGRAM);
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
		    if (instr->kind == HIR_TAC_DEOPT) {
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (block->num_successors == 2) {
			if (program->value_types
			    && (program->value_types[instr->src1] == TYPE_STR
				|| program->value_types[instr->src1] == TYPE_LIST)) {
			    char name[32];
			    sprintf(name, "truth%d", copy_serial++);
			    MIR_reg_t truth = new_reg(build, name);
			    sprintf(name, "type_reg%d", copy_serial++);
			    MIR_reg_t type_reg = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_int_op(build->context, program->value_types[instr->src1])));
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context, build->proto_is_true),
				MIR_new_ref_op(build->context, build->import_is_true),
				MIR_new_reg_op(build->context, truth),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, type_reg)));
			    append(build, MIR_new_insn(build->context, MIR_BF,
				MIR_new_label_op(build->context,
						 labels[block->successors[0]]),
				MIR_new_reg_op(build->context, truth)));
			} else if (program->value_is_tagged
				   && program->value_is_tagged[instr->src1]) {
			    char name[32];
			    sprintf(name, "truth%d", copy_serial++);
			    MIR_reg_t truth = new_reg(build, name);
			    sprintf(name, "type_reg%d", copy_serial++);
			    MIR_reg_t type_reg = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_mem_op(build->context, tag_t,
				    (program->num_values + instr->src1) * sizeof(Num),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context, build->proto_is_true),
				MIR_new_ref_op(build->context, build->import_is_true),
				MIR_new_reg_op(build->context, truth),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, type_reg)));
			    append(build, MIR_new_insn(build->context, MIR_BF,
				MIR_new_label_op(build->context,
						 labels[block->successors[0]]),
				MIR_new_reg_op(build->context, truth)));
			} else if (program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT) {
			    char name[32];
			    sprintf(name, "zero_bf%d", copy_serial++);
			    MIR_reg_t zero = MIR_new_func_reg(build->context,
							       build->function->u.func,
							       MIR_T_D, name);
			    append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_reg_op(build->context, zero),
						      MIR_new_mem_op(build->context, MIR_T_D,
								     0, deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_DBEQ,
							  MIR_new_label_op(build->context,
							     labels[block->successors[0]]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1]),
							  MIR_new_reg_op(build->context, zero)));
			} else {
			    append(build, MIR_new_insn(build->context, MIR_BF,
							  MIR_new_label_op(build->context,
							     labels[block->successors[0]]),
							  MIR_new_reg_op(build->context,
									 values[instr->src1])));
			}
			append(build, MIR_new_insn(build->context, MIR_JMP,
			    MIR_new_label_op(build->context,
					     labels[block->successors[1]])));
		    }
		    break;
		case HIR_TAC_RETURN:
		    if (instr->kind == HIR_TAC_DEOPT) {
			append_deopt_exit(build, program, instr->deopt_map,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (program->value_types
			&& program->value_types[instr->src1] == TYPE_FLOAT) {
#if FLOATS_ARE_BOXED
			/* Box if needed */
#else
			append(build, MIR_new_insn(build->context, MIR_DMOV,
						      MIR_new_mem_op(build->context,
								     MIR_T_D,
								     offsetof(Var, v.fnum),
								     result, 0, 1),
						      MIR_new_reg_op(build->context,
								     values[instr->src1])));
#endif
		    } else {
			append(build, MIR_new_insn(build->context, MIR_MOV,
						      MIR_new_mem_op(build->context,
								     (instr->literal_type == TYPE_LIST
								      || instr->literal_type == TYPE_STR)
								     ? MIR_T_P
								     : (sizeof(Num) == 8
									? MIR_T_I64 : MIR_T_I32),
								     (instr->literal_type == TYPE_LIST
								      ? offsetof(Var, v.list)
								      : (instr->literal_type == TYPE_STR
									 ? offsetof(Var, v.str)
									 : offsetof(Var, v.num))),
								     result, 0, 1),
						      MIR_new_reg_op(build->context,
								     values[instr->src1])));
		    }
		    append(build, MIR_new_insn(build->context, MIR_MOV,
						  MIR_new_mem_op(build->context, MIR_T_I32,
								 offsetof(Var, type), result, 0, 1),
						  MIR_new_int_op(build->context, instr->literal_type)));
		    return_status(build, status, common_return, JIT_RUN_RETURNED);
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
		    return_status(build, status, common_return, JIT_RUN_RETURNED);
		    break;
		case HIR_TAC_CALL:
		case HIR_TAC_CALL_VERB:
		case HIR_TAC_PUT_PROP:
		case HIR_TAC_RANGE_REF:
		case HIR_TAC_RANGE_SET:
		    append_deopt_exit(build, program, instr->deopt_map, values,
				      deopt_map_out, deopt_values, status,
				      common_return);
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
    append(build, MIR_new_insn(build->context, MIR_MOV,
			      MIR_new_mem_op(build->context, MIR_T_I32,
					     0, deopt_map_out, 0, 1),
			      MIR_new_int_op(build->context, 0)));
    return_status(build, status, common_return, JIT_RUN_FALLBACK);
    append_status_exits(build, status_exits, source_location, error_out, status,
			common_return);
    append(build, common_return);
    append(build, MIR_new_ret_insn(build->context, 1,
				  MIR_new_reg_op(build->context, status)));
    finish_build(build);
    myfree(labels, M_PROGRAM);
    myfree(values, M_PROGRAM);
    return 1;
}

JITProgram *
jit_program_unsupported_with_diagnostic(const char *reason, const char *diagnostic)
{
    JITProgram *program = mymalloc(sizeof(JITProgram), M_PROGRAM);

    memset(program, 0, sizeof(JITProgram));
    program->state = JIT_STATE_UNSUPPORTED;
    program->reason = str_dup(reason ? reason : "unsupported-program");
    program->diagnostic = str_dup(diagnostic ? diagnostic : "none");
    return program;
}

JITProgram *
jit_program_unsupported(const char *reason)
{
    return jit_program_unsupported_with_diagnostic(reason, 0);
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
    if (program->deopt_maps)
	{
	    int i;

	    for (i = 0; i < program->num_deopt_maps; i++) {
		if (program->deopt_maps[i].local_values)
		    myfree(program->deopt_maps[i].local_values, M_PROGRAM);
		if (program->deopt_maps[i].local_types)
		    myfree(program->deopt_maps[i].local_types, M_PROGRAM);
		if (program->deopt_maps[i].stack_values)
		    myfree(program->deopt_maps[i].stack_values, M_PROGRAM);
		if (program->deopt_maps[i].stack_types)
		    myfree(program->deopt_maps[i].stack_types, M_PROGRAM);
	    }
	    myfree(program->deopt_maps, M_PROGRAM);
	}
    if (program->deopt_values)
	myfree(program->deopt_values, M_PROGRAM);
    if (program->value_types)
	myfree(program->value_types, M_PROGRAM);
    if (program->value_is_tagged)
	myfree(program->value_is_tagged, M_PROGRAM);
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
	    if (instr->kind == HIR_TAC_CONST && instr->literal_type == TYPE_STR
		&& instr->literal)
		free_str((const char *) (intptr_t) instr->literal);
	    else if (instr->kind == HIR_TAC_CONST && instr->literal_type == TYPE_LIST
		&& instr->literal) {
		Var list_var;
		list_var.type = TYPE_LIST;
		list_var.v.list = (Var *) (intptr_t) instr->literal;
		free_var(list_var);
	    }
	    myfree(instr, M_PROGRAM);
	    instr = next_instr;
	}
	myfree(block, M_PROGRAM);
	block = next_block;
    }
    if (program->reason)
	free_str(program->reason);
    if (program->diagnostic)
	free_str(program->diagnostic);
    myfree(program, M_PROGRAM);
}

int
jit_program_bytes(JITProgram *program)
{
    int bytes = 0;
    int i;
    JITBlock *block;

    if (!program)
	return 0;
    bytes = sizeof(JITProgram);
    bytes += sizeof(JITDeoptMap) * program->num_deopt_maps;
    bytes += sizeof(Num) * program->num_values * 2;
    if (program->value_types)
	bytes += sizeof(var_type) * program->num_values;
    if (program->value_is_tagged)
	bytes += sizeof(unsigned char) * program->num_values;
    for (i = 0; i < program->num_deopt_maps; i++)
	bytes += sizeof(int) * (program->deopt_maps[i].num_locals
			      + program->deopt_maps[i].stack_depth);
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

const char *
jit_program_diagnostic(JITProgram *program)
{
    return (program && program->diagnostic) ? program->diagnostic : "none";
}

int
jit_program_is_eligible(JITProgram *program)
{
    return program && program->eligible;
}

int
jit_program_may_error(JITProgram *program)
{
    return program && program->may_error;
}

int
jit_program_anchor_count(JITProgram *program)
{
    return program ? program->num_resume_anchors : 0;
}

int
jit_program_deopt_map_count(JITProgram *program)
{
    return program ? program->num_deopt_maps : 0;
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
	if (program->reason)
	    free_str(program->reason);
	program->reason = str_dup("code-generation-failed");
	if (program->diagnostic)
	    free_str(program->diagnostic);
	program->diagnostic = str_dup("mir build module failed");
	return 0;
    }
    MIR_load_module(build.context, build.module);
    MIR_gen_init(build.context);
    MIR_gen_set_optimize_level(build.context, 0);
    MIR_link(build.context, MIR_set_gen_interface, 0);
    program->native_function = MIR_gen(build.context, build.function);
    if (!program->native_function) {
	MIR_gen_finish(build.context);
	MIR_finish(build.context);
	program->state = JIT_STATE_FAILED;
	if (program->reason)
	    free_str(program->reason);
	program->reason = str_dup("code-generation-failed");
	if (program->diagnostic)
	    free_str(program->diagnostic);
	program->diagnostic = str_dup("mir generator failed");
	return 0;
    }
    program->machine_code = build.function->u.func->machine_code;
    program->machine_code_len = build.function->u.func->machine_code_len;
    program->mir_context = build.context;
    program->deopt_values = mymalloc(sizeof(Num) * program->num_values * 2,
				     M_PROGRAM);
    memset(program->deopt_values, 0, sizeof(Num) * program->num_values * 2);
    program->state = JIT_STATE_COMPILED;
    return 1;
}

static Var
materialize_deopt_value(var_type type, Num raw)
{
    Var value;

    if (type == TYPE_NONE)
	return (Var){ .type = TYPE_NONE, .v = { .num = 0 } };
    value.type = type;
    if (type == TYPE_STR) {
	if (!raw)
	    return (Var){ .type = TYPE_NONE, .v = { .num = 0 } };
	value.v.str = (const char *) (intptr_t) raw;
    } else if (type == TYPE_LIST) {
	if (!raw)
	    return (Var){ .type = TYPE_NONE, .v = { .num = 0 } };
	value.v.list = (Var *) (intptr_t) raw;
    } else if (type == TYPE_OBJ)
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

JITRunResult
jit_program_execute(JITProgram *program, Var *env, Var *result,
		    int *ticks, int *timed_out, enum error *error,
		    JITSourceLocation *source_location, JITDeoptState *deopt,
		    Var *deopt_stack, Objid progr)
{
    NativeFunction function;
    int64_t native_result;
    int deopt_map = -1;
    JITSourceLocation ignored_location;

    if (!source_location)
	source_location = &ignored_location;
    source_location->bytecode_pc = 0;
    source_location->error_pc = 0;
    source_location->source_lineno = 0;
    if (deopt) {
	memset(deopt, 0, sizeof(*deopt));
	if (program && program->num_deopt_maps > 0) {
	    deopt->bytecode_pc = program->deopt_maps[0].bytecode_pc;
	    deopt->error_pc = program->deopt_maps[0].error_pc;
	    deopt->source_lineno = program->deopt_maps[0].source_lineno;
	    deopt->stack_depth = program->deopt_maps[0].stack_depth;
	    deopt->ticks_charged = program->deopt_maps[0].ticks_charged;
	    deopt->reason = program->deopt_maps[0].reason;
	}
    }
    if (!jit_program_compile(program))
	return JIT_RUN_FALLBACK;
    function = (NativeFunction) program->native_function;
    native_result = function(env, result, ticks, timed_out, error,
			     source_location, &deopt_map,
			     program->deopt_values, progr);
    if (native_result == JIT_RUN_FALLBACK) {
	JITDeoptMap *map;
	int i;

	if (deopt_map < 0 || deopt_map >= program->num_deopt_maps)
	    return JIT_RUN_FALLBACK;
	map = &program->deopt_maps[deopt_map];
	for (i = 0; i < map->num_locals; i++)
	    if (map->local_values[i] > 0) {
		var_type type = map->local_types ? map->local_types[i] : TYPE_INT;
		if (type == TYPE_ANY)
		    type = (var_type) program->deopt_values[program->num_values
			+ map->local_values[i]];
		Var value = materialize_deopt_value(type,
			program->deopt_values[map->local_values[i]]);

		free_var(env[i]);
		env[i] = value;
	    }
	for (i = 0; deopt_stack && i < (int) map->stack_depth; i++) {
	    var_type type = map->stack_types ? map->stack_types[i] : TYPE_INT;
	    if (type == TYPE_ANY)
		type = (var_type) program->deopt_values[program->num_values
		    + map->stack_values[i]];

	    deopt_stack[i] = materialize_deopt_value(type,
		program->deopt_values[map->stack_values[i]]);
	}
	if (deopt) {
	    deopt->bytecode_pc = map->bytecode_pc;
	    deopt->error_pc = map->error_pc;
	    deopt->source_lineno = map->source_lineno;
	    deopt->stack_depth = map->stack_depth;
	    deopt->ticks_charged = map->ticks_charged;
	    deopt->reason = map->reason;
	}
    }
    if (native_result == JIT_RUN_RETURNED) {
	if (result)
	    *result = var_ref(*result);
    }
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

int
jit_program_dump_machine(JITProgram *program,
			 void (*add_line)(const char *, void *), void *data)
{
    const unsigned char *code;
    size_t offset;

    if (!jit_program_compile(program) || !program->machine_code
	|| !program->machine_code_len)
	return 0;
    code = program->machine_code;
    for (offset = 0; offset < program->machine_code_len; offset += 16) {
	char line[80];
	size_t count = program->machine_code_len - offset;
	size_t i;
	int used;

	if (count > 16)
	    count = 16;
	used = snprintf(line, sizeof(line), "%04lx:", (unsigned long) offset);
	for (i = 0; i < count; i++)
	    used += snprintf(line + used, sizeof(line) - used, " %02x",
			     code[offset + i]);
	add_line(line, data);
    }
    return 1;
}

typedef struct JITDeoptSite {
    Objid vloc;
    char *verbname;
    unsigned bytecode_pc;
    unsigned source_lineno;
    JITDeoptReason reason;
    uint64_t count;
    struct JITDeoptSite *next;
} JITDeoptSite;

#define JIT_DEOPT_HASH_SIZE 256
static JITDeoptSite *deopt_sites_hash[JIT_DEOPT_HASH_SIZE];
static uint64_t total_jit_entries = 0;
static uint64_t total_jit_completed = 0;
static uint64_t total_deopts = 0;
static uint64_t deopt_reason_counts[JIT_DEOPT_NUM_REASONS];
static time_t last_deopt_report_time = 0;

const char *
jit_deopt_reason_name(JITDeoptReason reason)
{
    switch (reason) {
    case JIT_DEOPT_NONE:
	return "none";
    case JIT_DEOPT_BUILTIN_CALL:
	return "builtin_call";
    case JIT_DEOPT_VERB_CALL:
	return "verb_call";
    case JIT_DEOPT_PROPERTY_READ:
	return "property_read";
    case JIT_DEOPT_PROPERTY_WRITE:
	return "property_write";
    case JIT_DEOPT_RANGE_OP:
	return "range_operation";
    case JIT_DEOPT_TYPE_GUARD:
	return "type_guard_failure";
    case JIT_DEOPT_BRANCH_TYPE:
	return "branch_type_mismatch";
    case JIT_DEOPT_CONTROL_FLOW:
	return "control_flow";
    case JIT_DEOPT_ARITHMETIC_TYPE:
	return "arithmetic_type";
    case JIT_DEOPT_UNSUPPORTED_OP:
    default:
	return "unsupported_operation";
    }
}

void
jit_profile_record_entry(void)
{
    total_jit_entries++;
}

void
jit_profile_record_completed(void)
{
    total_jit_completed++;
}

void
jit_profile_record_deopt(Objid vloc, const char *verbname,
			 const JITDeoptState *deopt)
{
    JITDeoptReason reason = (deopt && deopt->reason < JIT_DEOPT_NUM_REASONS)
	? deopt->reason : JIT_DEOPT_UNSUPPORTED_OP;
    Num log_mode;
    unsigned h;
    JITDeoptSite *site;

    total_deopts++;
    deopt_reason_counts[reason]++;

    log_mode = server_int_option("jit_deopt_log_mode", 0);
    if (log_mode == 1) {
	oklog("JIT_DEOPT: #%"PRIdN":%s line %u (pc %u): %s\n",
	      vloc, verbname ? verbname : "?",
	      deopt ? deopt->source_lineno : 0,
	      deopt ? deopt->bytecode_pc : 0,
	      jit_deopt_reason_name(reason));
    }

    h = ((unsigned) vloc * 31 + (deopt ? deopt->bytecode_pc : 0) * 17 + (unsigned) reason) % JIT_DEOPT_HASH_SIZE;
    for (site = deopt_sites_hash[h]; site; site = site->next) {
	if (site->vloc == vloc
	    && site->bytecode_pc == (deopt ? deopt->bytecode_pc : 0)
	    && site->reason == reason
	    && ((!site->verbname && !verbname)
		|| (site->verbname && verbname && strcmp(site->verbname, verbname) == 0))) {
	    site->count++;
	    return;
	}
    }
    site = mymalloc(sizeof(JITDeoptSite), M_PROGRAM);
    site->vloc = vloc;
    site->verbname = verbname ? str_dup(verbname) : 0;
    site->bytecode_pc = deopt ? deopt->bytecode_pc : 0;
    site->source_lineno = deopt ? deopt->source_lineno : 0;
    site->reason = reason;
    site->count = 1;
    site->next = deopt_sites_hash[h];
    deopt_sites_hash[h] = site;
}

void
jit_profile_report(void)
{
    int r, i, j, k;
    JITDeoptSite *top_sites[10];

    if (total_deopts == 0 && total_jit_entries == 0)
	return;

    oklog("JIT: ===== Deoptimization Profile Report =====\n");
    oklog("JIT: Total entries: %"PRIu64" | Completed: %"PRIu64" (%.2f%%) | Deopts: %"PRIu64" (%.2f%%)\n",
	  total_jit_entries,
	  total_jit_completed,
	  total_jit_entries > 0 ? (100.0 * (double) total_jit_completed / (double) total_jit_entries) : 0.0,
	  total_deopts,
	  total_jit_entries > 0 ? (100.0 * (double) total_deopts / (double) total_jit_entries) : 0.0);

    oklog("JIT: Deopt Reason Breakdown:\n");
    for (r = 1; r < JIT_DEOPT_NUM_REASONS; r++) {
	if (deopt_reason_counts[r] > 0) {
	    oklog("JIT:   %-22s: %10"PRIu64" (%6.2f%%)\n",
		  jit_deopt_reason_name((JITDeoptReason) r),
		  deopt_reason_counts[r],
		  total_deopts > 0 ? (100.0 * (double) deopt_reason_counts[r] / (double) total_deopts) : 0.0);
	}
    }

    memset(top_sites, 0, sizeof(top_sites));
    for (i = 0; i < JIT_DEOPT_HASH_SIZE; i++) {
	for (JITDeoptSite *s = deopt_sites_hash[i]; s; s = s->next) {
	    for (j = 0; j < 10; j++) {
		if (!top_sites[j] || s->count > top_sites[j]->count) {
		    for (k = 9; k > j; k--)
			top_sites[k] = top_sites[k - 1];
		    top_sites[j] = s;
		    break;
		}
	    }
	}
    }

    if (top_sites[0]) {
	oklog("JIT: Top Deoptimizing Call Sites:\n");
	for (j = 0; j < 10 && top_sites[j]; j++) {
	    JITDeoptSite *s = top_sites[j];
	    oklog("JIT:   #%"PRIdN":%s line %u (pc %u): %s (count: %"PRIu64")\n",
		  s->vloc, s->verbname ? s->verbname : "?",
		  s->source_lineno, s->bytecode_pc,
		  jit_deopt_reason_name(s->reason),
		  s->count);
	}
    }
    oklog("JIT: =========================================\n");
}

void
jit_profile_maybe_report(int now)
{
    Num log_mode = server_int_option("jit_deopt_log_mode", 0);
    Num interval;

    if (log_mode == 2)
	return;

    interval = server_int_option("jit_deopt_log_interval", 1800);
    if (interval <= 0)
	return;

    if (last_deopt_report_time == 0) {
	last_deopt_report_time = now;
	return;
    }

    if (now - last_deopt_report_time >= interval) {
	last_deopt_report_time = now;
	jit_profile_report();
    }
}

void
jit_profile_reset(void)
{
    int i;
    for (i = 0; i < JIT_DEOPT_HASH_SIZE; i++) {
	JITDeoptSite *s = deopt_sites_hash[i];
	while (s) {
	    JITDeoptSite *next = s->next;
	    if (s->verbname)
		free_str(s->verbname);
	    myfree(s, M_PROGRAM);
	    s = next;
	}
	deopt_sites_hash[i] = 0;
    }
    total_jit_entries = 0;
    total_jit_completed = 0;
    total_deopts = 0;
    memset(deopt_reason_counts, 0, sizeof(deopt_reason_counts));
    last_deopt_report_time = 0;
}
