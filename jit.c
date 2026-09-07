#include "jit.h"

#include "config.h"
#include "options.h"

#include "my-stdio.h"
#include "my-stdlib.h"
#include "my-string.h"
#include "my-time.h"
#include "my-unistd.h"

#include "compiler.h"
#include "db.h"
#include "eval_env.h"
#include "exceptions.h"
#include "execute.h"
#include "functions.h"
#include "jit_internal.h"
#include "list.h"
#include "log.h"
#include "server.h"
#include "storage.h"
#include "utf.h"
#include "utils.h"
#ifdef WAIF_CORE
#include "waif.h"
#endif

#include "mir.h"
#include "mir-gen.h"

#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <string.h>

#ifdef IGNORE_PROP_PROTECTED
#define bi_prop_protected(prop, progr) (0)
#else
#define bi_prop_protected(prop, progr) ((!is_wizard(progr)) && server_flag_option_cached(prop))
#endif

/* Bound asynchronous timeout latency within long straight-line blocks. */
#define JIT_TIMEOUT_CHECK_TICK_INTERVAL 16
#define JIT_NATIVE_RETURNED_OWNED (JIT_RUN_ABORT_SECONDS + 1)
#define JIT_REGION_HOT_THRESHOLD 16

static int jit_runtime_value_slots(JITProgram *);
static void jit_program_release_ir(JITProgram *, int);
static void jit_program_release_native(JITProgram *);
static int jit_program_restore_ir(JITProgram *);
static void jit_region_site_mark_spliced(JITProgram *, int);
static int jit_region_site_snapshot(JITProgram *, int, Program **, Objid *,
	uint64_t *);
static void jit_region_request_specialization(JITProgram *);

static int
jit_deopt_map_bridges_builtin(JITDeoptMap *map)
{
    return (map->reason == JIT_DEOPT_BUILTIN_CALL && map->builtin_func >= 0)
	|| (jit_deopt_map_is_specialized_builtin(map)
	    && builtin_function_is_protected((unsigned) map->builtin_func));
}

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

static Var
raw_to_var(int64_t raw, int type)
{
    Var value;

    value.type = (var_type) type;
    if (type == TYPE_FLOAT)
	value.v.fnum = box_fl((FlNum) raw_to_double(raw));
    else if (type == TYPE_STR)
	value.v.str = (const char *) (intptr_t) raw;
    else if (type == TYPE_LIST)
	value.v.list = (Var *) (intptr_t) raw;
#ifdef WAIF_CORE
    else if (type == TYPE_WAIF)
	value.v.waif = (Waif *) (intptr_t) raw;
#endif
    else
	value.v.num = (Num) raw;
    return value;
}

/* JIT Runtime Helpers for Complex Values and Properties */

int
jit_rt_is_true(int64_t raw_val, int val_type)
{
    return is_true(raw_to_var(raw_val, val_type));
}

int
jit_rt_equality(int64_t raw1, int type1, int64_t raw2, int type2, int case_matters)
{
    Var v1, v2;

    v1 = raw_to_var(raw1, type1);
    v2 = raw_to_var(raw2, type2);

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

int
jit_rt_str_concat_owned(Var *owned_values, int owner, const char *s1,
			const char *s2, int last_use, int64_t *result_out,
			int32_t *err_out)
{
    const char *result;
    Var *home;
    int consumes_home;

    assert(owned_values && owner >= 0);
    home = &owned_values[owner];
    assert(home->type == TYPE_NONE || home->type == TYPE_STR);
    consumes_home = home->type == TYPE_NONE
	|| ((last_use & JIT_LAST_USE_SRC1) && home->v.str == s1)
	|| ((last_use & JIT_LAST_USE_SRC2) && home->v.str == s2);
    if (!consumes_home) {
	*err_out = E_NONE;
	return 0;
    }
    result = jit_rt_str_concat(s1, s2, err_out);
    if (*err_out != E_NONE)
	return 1;
    free_var(*home);
    home->type = TYPE_STR;
    home->v.str = result;
    *result_out = (int64_t) (intptr_t) result;
    return 1;
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

static inline int
jit_rangeref_fails(Num length, Num from, Num after)
{
    return !(from >= after || (1 <= from && after <= length + 1));
}

const char *
jit_rt_str_range_ref(const char *str, int64_t from, int64_t to, int32_t *err_out)
{
    Var base, res;
    Num bfromafter[2];

    if (!str) {
	*err_out = E_TYPE;
	return 0;
    }
    bfromafter[0] = from;
    bfromafter[1] = to + 1;
    utf_byte_range(str, bfromafter);
    if (jit_rangeref_fails(memo_strlen(str), bfromafter[0], bfromafter[1])) {
	*err_out = E_RANGE;
	return 0;
    }
    base.type = TYPE_STR;
    base.v.str = str;
    res = substr(var_ref(base), bfromafter[0], bfromafter[1]);
    *err_out = E_NONE;
    return res.v.str;
}

Var *
jit_rt_list_range_ref(Var *list, int64_t from, int64_t to, int32_t *err_out)
{
    Var base, res;

    if (!list) {
	*err_out = E_TYPE;
	return 0;
    }
    if (jit_rangeref_fails(list[0].v.num, from, to + 1)) {
	*err_out = E_RANGE;
	return 0;
    }
    base.type = TYPE_LIST;
    base.v.list = list;
    res = sublist(var_ref(base), from, to + 1);
    *err_out = E_NONE;
    return res.v.list;
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
    *err_out = E_NONE;
    return res.v.list;
}

Var *
jit_rt_make_singleton_list(int64_t elem_raw, int elem_type)
{
    Var list = new_list(1);
    Var elem;

    elem = var_ref(raw_to_var(elem_raw, elem_type));

    list.v.list[1] = elem;
    return list.v.list;
}

Var *
jit_rt_make_fixed_list_head(int64_t elem_raw, int elem_type, int capacity)
{
    Var elem, list;

    assert(capacity > 1);
    elem = var_ref(raw_to_var(elem_raw, elem_type));
    list = new_list(capacity);
    list.v.list[0].v.num = 1;
    list.v.list[1] = elem;
    return list.v.list;
}

Var *
jit_rt_list_append(Var *list, int64_t elem_raw, int elem_type)
{
    Var l, elem, res;

    l.type = TYPE_LIST;
    l.v.list = list;

    elem = var_ref(raw_to_var(elem_raw, elem_type));

    res = listappend(var_ref(l), elem);
    return res.v.list;
}

Var *
jit_rt_list_append_owned(Var *owned_values, unsigned *home_capacities,
			 int owner, Var *list,
			 int64_t elem_raw, int elem_type)
{
    Var elem, res;

    assert(owned_values && owner >= 0);
    assert(owned_values[owner].type == TYPE_NONE
	   || (owned_values[owner].type == TYPE_LIST
	       && owned_values[owner].v.list == list));
    elem = var_ref(raw_to_var(elem_raw, elem_type));
    if (owned_values[owner].type == TYPE_LIST) {
	res = owned_values[owner];
	owned_values[owner].type = TYPE_NONE;
	owned_values[owner].v.num = 0;
    } else {
	res.type = TYPE_LIST;
	res.v.list = list;
	res = var_ref(res);
    }
    res = listappend(res, elem);
    owned_values[owner] = res;
    home_capacities[owner] = 0;
    return res.v.list;
}

Var *
jit_rt_fixed_list_append_owned(Var *owned_values, unsigned *home_capacities,
			       int owner, Var *list,
			       int index, int64_t elem_raw, int elem_type)
{
    Var elem, res;

    assert(owned_values && owner >= 0);
    /*
     * Promotion may transfer the partially constructed list to the
     * canonical activation.  The resumed continuation then borrows that
     * same list even though its native owner home is empty.
     */
    assert(owned_values[owner].type == TYPE_NONE
	   || (owned_values[owner].type == TYPE_LIST
	       && owned_values[owner].v.list == list));
    assert(index > 1 && list[0].v.num == index - 1);
    elem = var_ref(raw_to_var(elem_raw, elem_type));

    if (owned_values[owner].type == TYPE_LIST
	&& home_capacities[owner] >= (unsigned) index) {
	list[index] = elem;
	list[0].v.num = index;
	return list;
    }
    if (owned_values[owner].type == TYPE_LIST) {
	res = owned_values[owner];
	owned_values[owner].type = TYPE_NONE;
	owned_values[owner].v.num = 0;
	res = listappend(res, elem);
	owned_values[owner] = res;
    } else {
	res.type = TYPE_LIST;
	res.v.list = list;
	res = listappend(var_ref(res), elem);
    }
    home_capacities[owner] = 0;
    return res.v.list;
}

Var *
jit_rt_fixed_list_store(Var *list, int index, int64_t elem_raw, int elem_type)
{
    assert(list && index > 1 && list[0].v.num == index - 1);
    list[index] = var_ref(raw_to_var(elem_raw, elem_type));
    list[0].v.num = index;
    return list;
}

void
jit_rt_owned_replace(Var *owned_values, int value, int64_t raw, int type)
{
    free_var(owned_values[value]);
    owned_values[value] = raw_to_var(raw, type);
}

void
jit_rt_owned_move(Var *owned_values, int destination, int source)
{
    if (destination == source)
	return;
    free_var(owned_values[destination]);
    owned_values[destination] = owned_values[source];
    owned_values[source].type = TYPE_NONE;
    owned_values[source].v.num = 0;
}

Var *
jit_rt_make_empty_list(void)
{
    return new_list(0).v.list;
}

void
jit_rt_discard_owned(Var *owned_values, int owner, int64_t raw, int type)
{
    if (owner >= 0) {
	assert(owned_values && owned_values[owner].type != TYPE_NONE);
	free_var(owned_values[owner]);
	owned_values[owner].type = TYPE_NONE;
	owned_values[owner].v.num = 0;
    } else
	free_var(raw_to_var(raw, type));
}

void
jit_rt_retain_raw(int64_t raw, int type)
{
    var_ref(raw_to_var(raw, type));
}

Var *
jit_rt_list_index_set(Var *env, int local_id, Var *list, int64_t index,
		      int64_t value_raw, int value_type, int32_t *err_out)
{
    Var base, value, result;

    if (!env || local_id < 0 || !list) {
	*err_out = E_TYPE;
	return 0;
    }
    if (index < 1 || index > list[0].v.num) {
	*err_out = E_RANGE;
	return 0;
    }

    base.type = TYPE_LIST;
    base.v.list = list;
    value = var_ref(raw_to_var(value_raw, value_type));
    result = listset(var_dup(base), value, (int) index);
    free_var(env[local_id]);
    env[local_id] = result;
    *err_out = E_NONE;
    return result.v.list;
}

Var *
jit_rt_list_nested_index_set(Var *env, int local_id, int64_t outer_idx,
			     int64_t inner_idx, int64_t value_raw,
			     int value_type, int32_t *err_out)
{
    Var root;
    Var sub;
    Var value;
    Var new_sub;
    Var new_root;

    assert(env && local_id >= 0);
    root = env[local_id];
    if (root.type != TYPE_LIST) {
	*err_out = E_TYPE;
	return 0;
    }
    if (outer_idx < 1 || outer_idx > root.v.list[0].v.num) {
	*err_out = E_RANGE;
	return 0;
    }
    sub = root.v.list[outer_idx];
    if (sub.type != TYPE_LIST) {
	*err_out = E_TYPE;
	return 0;
    }
    if (inner_idx < 1 || inner_idx > sub.v.list[0].v.num) {
	*err_out = E_RANGE;
	return 0;
    }
    value = var_ref(raw_to_var(value_raw, value_type));
    new_sub = listset(var_dup(sub), value, (int) inner_idx);
    new_root = listset(var_dup(root), new_sub, (int) outer_idx);
    free_var(env[local_id]);
    env[local_id] = new_root;
    *err_out = E_NONE;
    return new_root.v.list;
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

    elem = raw_to_var(elem_raw, elem_type);

    return ismember(elem, l, 0);
}

int64_t
jit_rt_region_guard(int64_t receiver_raw, int receiver_type,
		    int64_t receiver_class, int64_t dispatch_epoch)
{
    if ((uint64_t) dispatch_epoch != db_dispatch_epoch())
	return 0;
    if (receiver_type == TYPE_OBJ)
	return (Objid) receiver_raw == (Objid) receiver_class;
#ifdef WAIF_CORE
    if (receiver_type == TYPE_WAIF && receiver_raw)
	return ((Waif *) (intptr_t) receiver_raw)->class
	    == (Objid) receiver_class;
#endif
    return 0;
}

int
jit_rt_get_prop_typed(int64_t receiver_raw, int receiver_type,
		      const char *pname, int64_t progr_num, int64_t *out_raw,
		      int64_t *out_type, int32_t *err_out)
{
    Objid progr = (Objid) progr_num;
    Var prop, val;
    db_prop_handle h;

#ifdef WAIF_CORE
    if (receiver_type == TYPE_WAIF) {
	enum error error = waif_get_prop((Waif *) (intptr_t) receiver_raw,
					 pname, &val, progr);

	if (error != E_NONE) {
	    *err_out = error;
	    return 0;
	}
	goto return_value;
    }
#endif
    if (receiver_type != TYPE_OBJ) {
	*err_out = E_TYPE;
	return 0;
    }
    if (!valid((Objid) receiver_raw)) {
	*err_out = E_INVIND;
	return 0;
    }
    h = db_find_property((Objid) receiver_raw, pname, &prop);
    if (!h.ptr) {
	*err_out = E_PROPNF;
	return 0;
    }
    if (h.built_in ? bi_prop_protected(h.built_in, progr)
		   : !db_property_allows(h, progr, PF_READ)) {
	if (h.built_in)
	    free_var(prop);
	*err_out = E_PERM;
	return 0;
    }
    /* Built-in complex properties are constructed or retained by
       db_find_property(); ordinary property values are borrowed.  Normalize
       both paths to an owned result before returning to native code. */
    val = prop;
    if (!h.built_in)
	val = var_ref(val);
#ifdef WAIF_CORE
return_value:
#endif
    *out_type = val.type;
    if (val.type == TYPE_FLOAT) {
	double d = (double) fl_unbox(val.v.fnum);
	*out_raw = double_to_raw(d);
	free_var(val);
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

int
jit_rt_get_prop(int64_t oid_num, const char *pname, int64_t progr_num,
		int64_t *out_raw, int64_t *out_type, int32_t *err_out)
{
    return jit_rt_get_prop_typed(oid_num, TYPE_OBJ, pname, progr_num,
				 out_raw, out_type, err_out);
}

int64_t
jit_rt_get_prop_int(int64_t receiver_raw, int receiver_type,
		    const char *pname, int64_t progr_num, int32_t *err_out)
{
    int64_t raw = 0;
    int64_t type = TYPE_NONE;

    if (!jit_rt_get_prop_typed(receiver_raw, receiver_type, pname, progr_num,
	    &raw, &type, err_out))
	return 0;
    if (type != TYPE_INT) {
	free_var(raw_to_var(raw, type));
	*err_out = E_TYPE;
	return 0;
    }
    return raw;
}

int
jit_rt_put_prop(int64_t oid_num, const char *pname, int64_t progr_num,
		int64_t rhs_raw, int rhs_type, int32_t *err_out)
{
    Objid oid = (Objid) oid_num;
    Objid progr = (Objid) progr_num;
    Var rhs;
    db_prop_handle h;

    if (!valid(oid)) {
	*err_out = E_INVIND;
	return 0;
    }
    h = db_find_property(oid, pname, 0);
    if (!h.ptr) {
	*err_out = E_PROPNF;
	return 0;
    }

    rhs.type = (var_type) rhs_type;
    if (rhs_type == TYPE_FLOAT)
	rhs.v.fnum = box_fl((FlNum) raw_to_double(rhs_raw));
    else if (rhs_type == TYPE_STR)
	rhs.v.str = (const char *) (intptr_t) rhs_raw;
    else if (rhs_type == TYPE_LIST)
	rhs.v.list = (Var *) (intptr_t) rhs_raw;
#ifdef WAIF_CORE
    else if (rhs_type == TYPE_WAIF)
	rhs.v.waif = (Waif *) (intptr_t) rhs_raw;
#endif
    else
	rhs.v.num = (Num) rhs_raw;

    if (!h.built_in) {
	if (!db_property_allows(h, progr, PF_WRITE)) {
	    *err_out = E_PERM;
	    return 0;
	}
    } else {
	switch (h.built_in) {
	case BP_NAME:
	    if (rhs.type != TYPE_STR) {
		*err_out = E_TYPE;
		return 0;
	    }
	    if (!is_wizard(progr)
		&& (is_user(oid) || bi_prop_protected(h.built_in, progr)
		    || progr != db_object_owner(oid))) {
		*err_out = E_PERM;
		return 0;
	    }
	    break;
	case BP_OWNER:
	    if (rhs.type != TYPE_OBJ) {
		*err_out = E_TYPE;
		return 0;
	    }
	    if (!is_wizard(progr)) {
		*err_out = E_PERM;
		return 0;
	    }
	    break;
	case BP_PROGRAMMER:
	    if (!is_wizard(progr)) {
		*err_out = E_PERM;
		return 0;
	    }
	    break;
	case BP_WIZARD:
	    if (!is_wizard(progr)) {
		*err_out = E_PERM;
		return 0;
	    }
	    if (!is_true(rhs) != !is_wizard(oid))
		return -1;
	    break;
	case BP_R:
	case BP_W:
	case BP_F:
	    if (!is_wizard(progr)
		&& (bi_prop_protected(h.built_in, progr)
		    || progr != db_object_owner(oid))) {
		*err_out = E_PERM;
		return 0;
	    }
	    break;
	case BP_LOCATION:
	case BP_CONTENTS:
	    *err_out = E_PERM;
	    return 0;
	default:
	    return -1;
	}
    }

    db_set_property_value(h, var_ref(rhs));
    if (rhs.type == TYPE_FLOAT)
	free_var(rhs);
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

int64_t
jit_rt_var_raw(const Var *value)
{
    if (value->type == TYPE_FLOAT)
	return double_to_raw(fl_unbox(value->v.fnum));
    if (value->type == TYPE_STR)
	return (int64_t) (intptr_t) value->v.str;
    if (value->type == TYPE_LIST)
	return (int64_t) (intptr_t) value->v.list;
#ifdef WAIF_CORE
    if (value->type == TYPE_WAIF)
	return (int64_t) (intptr_t) value->v.waif;
#endif
    if (value->type == TYPE_OBJ)
	return value->v.obj;
    if (value->type == TYPE_ERR)
	return value->v.err;
    return value->v.num;
}

typedef int64_t (*NativeFunction) (JITExecutionContext *, JITNativeFrame *,
				   Var *, Var *, int *, int *, enum error *,
				   JITSourceLocation *, int *, Num *, Objid,
				   int, Var *, Var *, Var *);

struct JITPromotionPlan {
    JITExecutionContext *context;
    JITNativeFrame **frames;
    unsigned num_frames;
};

static JITContinuationFrame *continuation_frames;

static void
jit_continuation_unlink(JITContinuationFrame *frame)
{
    if (frame->previous)
	frame->previous->next = frame->next;
    else if (continuation_frames == frame)
	continuation_frames = frame->next;
    else if (frame->next)
	panic("JIT continuation list backlink is invalid");
    if (frame->next)
	frame->next->previous = frame->previous;
    frame->previous = 0;
    frame->next = 0;
}

void
jit_execution_context_init(JITExecutionContext *context,
			   JITNativeFrame *root, JITProgram *program, Var *env,
			   unsigned root_index, unsigned canonical_depth,
			   unsigned activation_limit, int *ticks,
			   int *timed_out, enum error *error, int entry_map)
{
    memset(context, 0, sizeof(*context));
    memset(root, 0, sizeof(*root));
    context->root_frame = root;
    context->current_frame = root;
    context->root_activation_index = root_index;
    context->canonical_depth = canonical_depth;
    context->activation_limit = activation_limit;
    context->ticks_remaining = ticks;
    context->task_timed_out = timed_out;
    context->pending_error = error;
    root->context = context;
    root->program = program;
    root->env = env;
    root->canonical_index = root_index;
    root->entry_map = entry_map;
    root->current_map = entry_map;
    root->kind = JIT_FRAME_ROOT_OVERLAY;
    root->state = JIT_FRAME_RUNNING;
}

int
jit_execution_context_push_overlay(JITExecutionContext *context,
				   JITNativeFrame *frame, JITProgram *program,
				   Var *env, unsigned canonical_index,
				   int entry_map)
{
    JITNativeFrame *caller;

    if (!context || !frame || !program || !(caller = context->current_frame)
	|| caller->state != JIT_FRAME_RUNNING || caller->callee
	|| canonical_index >= context->activation_limit)
	return 0;
    memset(frame, 0, sizeof(*frame));
    frame->context = context;
    frame->program = program;
    frame->caller = caller;
    frame->env = env;
    frame->canonical_index = canonical_index;
    frame->entry_map = entry_map;
    frame->current_map = entry_map;
    frame->kind = JIT_FRAME_CANONICAL_OVERLAY;
    frame->state = JIT_FRAME_RUNNING;
    caller->state = JIT_FRAME_SUSPENDED;
    caller->callee = frame;
    context->current_frame = frame;
    if (jit_native_frame_verify_runtime(context, frame))
	return 1;

    context->current_frame = caller;
    caller->callee = 0;
    caller->state = JIT_FRAME_RUNNING;
    memset(frame, 0, sizeof(*frame));
    return 0;
}

int
jit_execution_context_pop_overlay(JITExecutionContext *context,
				  JITNativeFrame *frame)
{
    JITNativeFrame *caller;

    if (!context || !frame || context->current_frame != frame
	|| frame->kind == JIT_FRAME_COMPACT || frame->callee
	|| frame->runtime_storage || frame->owns_boundary_stack
	|| !(caller = frame->caller)
	|| caller->callee != frame || caller->state != JIT_FRAME_SUSPENDED)
	return 0;
    caller->callee = 0;
    caller->state = JIT_FRAME_RUNNING;
    context->current_frame = caller;
    frame->caller = 0;
    frame->context = 0;
    frame->state = JIT_FRAME_DETACHED;
    return jit_native_frame_verify_runtime(context, caller);
}

int
jit_execution_context_push_compact(JITExecutionContext *context,
				   JITNativeFrame *frame, JITProgram *program,
				   Var *env, JITCallerResume *resume,
				   int entry_map)
{
    JITNativeFrame *caller;

    if (!context || !frame || !program || !resume
	|| !(caller = context->current_frame)
	|| caller->state != JIT_FRAME_RUNNING || caller->callee
	|| caller->outgoing || resume->caller != caller
	|| resume->state != JIT_RESUME_PREPARING || resume->map_id <= 0
	|| resume->map_id >= caller->program->num_deopt_maps
	|| (resume->continuation
	    ? (!jit_native_frame_continuation_matches(caller, resume->map_id)
	       || resume->continuation != caller->runtime_borrower
	       || resume->result_home != UINT_MAX)
	    : ((resume->result_home == UINT_MAX
		? caller->pending_resume_map != resume->map_id
		: (resume->result_home >= caller->num_homes
		   || caller->home_states[resume->result_home]
		      != JIT_HOME_EMPTY))))
	|| context->canonical_depth + context->native_depth
	    >= context->activation_limit)
	return 0;

    memset(frame, 0, sizeof(*frame));
    frame->context = context;
    frame->program = program;
    frame->caller = caller;
    frame->incoming = resume;
    frame->env = env;
    frame->entry_map = entry_map;
    frame->current_map = entry_map;
    frame->kind = JIT_FRAME_COMPACT;
    frame->state = JIT_FRAME_RUNNING;
    resume->state = JIT_RESUME_DISPATCHED;
    caller->state = JIT_FRAME_SUSPENDED;
    caller->outgoing = resume;
    caller->callee = frame;
    context->current_frame = frame;
    context->native_depth++;
    if (jit_native_frame_verify_runtime(context, frame))
	return 1;

    context->native_depth--;
    context->current_frame = caller;
    caller->callee = 0;
    caller->outgoing = 0;
    caller->state = JIT_FRAME_RUNNING;
    resume->state = JIT_RESUME_PREPARING;
    memset(frame, 0, sizeof(*frame));
    return 0;
}

int
jit_execution_context_return_compact(JITExecutionContext *context,
				     JITNativeFrame *frame, Var *result)
{
    JITNativeFrame *caller;
    JITCallerResume *resume;

    if (!context || !frame || !result || context->current_frame != frame
	|| frame->kind != JIT_FRAME_COMPACT || frame->state != JIT_FRAME_RUNNING
	|| frame->callee || frame->outgoing || frame->runtime_storage
	|| frame->owns_boundary_stack
	|| !(caller = frame->caller) || caller->callee != frame
	|| caller->state != JIT_FRAME_SUSPENDED
	|| !(resume = frame->incoming) || resume->caller != caller
	|| caller->outgoing != resume || resume->state != JIT_RESUME_DISPATCHED
	|| context->native_depth == 0
	|| !jit_native_frame_verify_runtime(context, frame))
	return 0;

    if (resume->continuation) {
	jit_continuation_set_result(resume->continuation, *result);
	result->type = TYPE_NONE;
	result->v.num = 0;
    } else if (resume->result_home == UINT_MAX) {
	if (caller->has_resume_result)
	    return 0;
	caller->resume_result = *result;
	caller->has_resume_result = 1;
	result->type = TYPE_NONE;
	result->v.num = 0;
    } else if (!jit_native_frame_home_move(caller, resume->result_home, result))
	return 0;

    caller->callee = 0;
    caller->outgoing = 0;
    caller->state = JIT_FRAME_RUNNING;
    context->current_frame = caller;
    context->native_depth--;
    resume->state = JIT_RESUME_RETURNED;
    frame->caller = 0;
    frame->incoming = 0;
    frame->context = 0;
    frame->state = JIT_FRAME_RETURNED;
    jit_native_frame_release_invocation(frame);
    return jit_native_frame_verify_runtime(context, caller);
}

JITPromotionPlan *
jit_native_chain_prepare_promotion(JITExecutionContext *context)
{
    JITPromotionPlan *plan;
    JITNativeFrame *frame;
    JITNativeFrame *last = 0;
    unsigned count = 0;
    unsigned i;

    if (!context || !context->root_frame || !context->current_frame)
	return 0;
    for (frame = context->root_frame; frame; frame = frame->callee) {
	if (!jit_native_frame_verify_runtime(context, frame)
	    || (frame->callee && !frame->outgoing)
	    || (!frame->callee && (frame->current_map < 0
		|| frame->current_map >= frame->program->num_deopt_maps)))
	    return 0;
	count++;
	last = frame;
    }
    if (last != context->current_frame
	|| count != context->native_depth + 1)
	return 0;

    plan = mymalloc(sizeof(*plan), M_PROGRAM);
    plan->frames = mymalloc(sizeof(JITNativeFrame *) * count, M_PROGRAM);
    plan->context = context;
    plan->num_frames = count;
    frame = context->root_frame;
    for (i = 0; i < count; i++) {
	plan->frames[i] = frame;
	frame = frame->callee;
    }
    return plan;
}

int
jit_native_chain_commit_promotion(JITPromotionPlan *plan,
				  JITPromotionMaterializer materialize,
				  void *data)
{
    JITExecutionContext *context;
    unsigned i;

    if (!plan || !plan->num_frames || !materialize
	|| !(context = plan->context)
	|| context->root_frame != plan->frames[0]
	|| context->current_frame != plan->frames[plan->num_frames - 1]
	|| context->native_depth + 1 != plan->num_frames)
	return 0;
    for (i = 0; i < plan->num_frames; i++) {
	JITNativeFrame *frame = plan->frames[i];

	if (!jit_native_frame_verify_runtime(context, frame)
	    || frame->caller != (i ? plan->frames[i - 1] : 0)
	    || frame->callee != (i + 1 < plan->num_frames
		? plan->frames[i + 1] : 0))
	    return 0;
    }

    for (i = 0; i < plan->num_frames; i++) {
	JITNativeFrame *frame = plan->frames[i];

	materialize(frame, frame->outgoing, data);
	if (frame->outgoing) {
	    frame->outgoing->state = JIT_RESUME_PROMOTED;
	    frame->outgoing->continuation = 0;
	}
	frame->state = JIT_FRAME_PROMOTED;
    }
    for (i = plan->num_frames; i > 0; i--) {
	JITNativeFrame *frame = plan->frames[i - 1];

	frame->caller = 0;
	frame->callee = 0;
	frame->incoming = 0;
	frame->outgoing = 0;
	frame->context = 0;
    }
    context->native_depth = 0;
    context->root_frame = 0;
    context->current_frame = 0;
    plan->context = 0;
    return 1;
}

void
jit_native_chain_discard_promotion(JITPromotionPlan *plan)
{
    if (!plan)
	return;
    myfree(plan->frames, M_PROGRAM);
    myfree(plan, M_PROGRAM);
}

unsigned
jit_native_chain_promotion_count(const JITPromotionPlan *plan)
{
    return plan ? plan->num_frames : 0;
}

JITNativeFrame *
jit_native_chain_promotion_frame(const JITPromotionPlan *plan, unsigned index)
{
    if (!plan || index >= plan->num_frames)
	return 0;
    return plan->frames[index];
}

int
jit_execution_context_finish(JITExecutionContext *context,
			     JITNativeFrame *root)
{
    if (!context || !root || context->root_frame != root
	|| context->current_frame != root || root->caller || root->callee
	|| root->runtime_storage || root->owns_boundary_stack
	|| !jit_native_frame_verify_runtime(context, root))
	return 0;
    root->context = 0;
    root->state = JIT_FRAME_DETACHED;
    context->root_frame = 0;
    context->current_frame = 0;
    jit_execution_context_free_runtime_pool(context);
    return 1;
}

int
jit_native_frame_bind_activation(JITNativeFrame *frame, const activation *a)
{
    if (!frame || !a || !a->prog || !a->rt_env || !a->verb
	|| !a->verbname || frame->owns_invocation)
	return 0;
    frame->bytecode_program = a->prog;
    frame->env = a->rt_env;
#ifdef WAIF_CORE
    frame->receiver = a->THIS;
#endif
    frame->this = a->this;
    frame->player = a->player;
    frame->progr = a->progr;
    frame->vloc = a->vloc;
    frame->verb = a->verb;
    frame->verbname = a->verbname;
    frame->debug = a->debug;
    return 1;
}

int
jit_native_frame_copy_invocation(JITNativeFrame *frame, const activation *a)
{
    if (!frame || !a || frame->kind != JIT_FRAME_COMPACT
	|| frame->owns_invocation || frame->bytecode_program
	|| !a->prog || !a->rt_env || !a->verb || !a->verbname)
	return 0;
    frame->bytecode_program = program_ref(a->prog);
    frame->env = copy_rt_env(a->rt_env, a->prog->num_var_names);
#ifdef WAIF_CORE
    frame->receiver = var_ref(a->THIS);
#endif
    frame->this = a->this;
    frame->player = a->player;
    frame->progr = a->progr;
    frame->vloc = a->vloc;
    frame->verb = str_ref(a->verb);
    frame->verbname = str_ref(a->verbname);
    frame->debug = a->debug;
    frame->owns_invocation = 1;
    return 1;
}

int
jit_native_frame_take_prepared_invocation(JITNativeFrame *frame,
					  PreparedVerbCall *prepared)
{
    if (!frame || !prepared || frame->kind != JIT_FRAME_COMPACT
	|| frame->owns_invocation || frame->bytecode_program
	|| !prepared->program || !prepared->env || !prepared->verb
	|| !prepared->verbname || frame->env != prepared->env)
	return 0;
    frame->bytecode_program = prepared->program;
#ifdef WAIF_CORE
    frame->receiver = prepared->receiver;
#endif
    frame->this = prepared->this;
    frame->player = prepared->player;
    frame->progr = prepared->progr;
    frame->vloc = prepared->vloc;
    frame->verb = prepared->verb;
    frame->verbname = prepared->verbname;
    frame->debug = prepared->debug;
    frame->owns_invocation = 1;
    memset(prepared, 0, sizeof(*prepared));
    return 1;
}

void
jit_native_frame_release_invocation(JITNativeFrame *frame)
{
    if (!frame || !frame->owns_invocation)
	return;
    free_rt_env(frame->env, frame->bytecode_program->num_var_names);
#ifdef WAIF_CORE
    free_var(frame->receiver);
    frame->receiver.type = TYPE_NONE;
    frame->receiver.v.num = 0;
#endif
    free_str(frame->verb);
    free_str(frame->verbname);
    free_program(frame->bytecode_program);
    frame->bytecode_program = 0;
    frame->env = 0;
    frame->verb = 0;
    frame->verbname = 0;
    frame->owns_invocation = 0;
}

void
jit_native_frame_bind_runtime(JITNativeFrame *frame, void *storage,
			      size_t bytes, Var *homes, unsigned num_homes,
			      unsigned char *home_states,
			      unsigned *home_capacities)
{
    frame->runtime_storage = storage;
    frame->runtime_bytes = bytes;
    frame->homes = homes;
    frame->num_homes = num_homes;
    frame->home_states = home_states;
    frame->home_capacities = home_capacities;
}

void
jit_native_frame_mark_runtime_owned(JITNativeFrame *frame)
{
    if (frame && frame->runtime_storage)
	frame->owns_runtime = 1;
}

int
jit_native_frame_adopt_continuation_runtime(JITNativeFrame *frame,
					    JITContinuationFrame *continuation)
{
    if (!frame || !continuation || frame->runtime_storage
	|| frame->runtime_borrower || frame->program != continuation->program
	|| !continuation->runtime_storage || !continuation->owns_runtime
	|| continuation->runtime_owner
	|| (continuation->owner
	    && (continuation->owner->jit_continuation != continuation
		|| (!continuation->previous
		    && continuation_frames != continuation)
		|| (continuation->previous
		    && continuation->previous->next != continuation)
		|| (continuation->next
		    && continuation->next->previous != continuation))))
	return 0;
    if (continuation->owner) {
	continuation->owner->jit_continuation = 0;
	continuation->owner = 0;
	jit_continuation_unlink(continuation);
    }
    jit_native_frame_bind_runtime(frame, continuation->runtime_storage,
	continuation->runtime_bytes, continuation->owned_values,
	continuation->program->num_owned_slots, continuation->home_states,
	continuation->home_capacities);
    jit_native_frame_mark_runtime_owned(frame);
    frame->runtime_borrower = continuation;
    continuation->runtime_owner = frame;
    continuation->owns_runtime = 0;
    return 1;
}

int
jit_native_frame_return_continuation_runtime(
    JITNativeFrame *frame, JITContinuationFrame *continuation)
{
    if (!frame || !continuation || frame->runtime_borrower != continuation
	|| continuation->runtime_owner != frame || !frame->owns_runtime
	|| continuation->owns_runtime
	|| frame->runtime_storage != continuation->runtime_storage
	|| frame->runtime_bytes != continuation->runtime_bytes
	|| frame->homes != continuation->owned_values
	|| frame->home_capacities != continuation->home_capacities
	|| frame->home_states != continuation->home_states)
	return 0;
    frame->runtime_borrower = 0;
    continuation->runtime_owner = 0;
    continuation->owns_runtime = 1;
    jit_native_frame_unbind_runtime(frame);
    return 1;
}

int
jit_native_frame_continuation_matches(const JITNativeFrame *frame, int map_id)
{
    JITContinuationFrame *continuation;

    if (!frame || !(continuation = frame->runtime_borrower))
	return 0;
    return continuation->program == frame->program
	&& continuation->map_id == map_id
	&& continuation->runtime_owner == frame
	&& !continuation->owns_runtime
	&& frame->owns_runtime
	&& continuation->runtime_storage == frame->runtime_storage
	&& continuation->home_capacities == frame->home_capacities;
}

static void
jit_native_frame_release_resume_roots(JITNativeFrame *frame)
{
    unsigned i;

    for (i = 0; i < frame->num_resume_roots; i++)
	free_var(frame->resume_roots[i]);
    if (frame->resume_roots) {
	frame->program->active_runtime_bytes -= sizeof(Var)
	    * frame->resume_roots_capacity;
	myfree(frame->resume_roots, M_PROGRAM);
    }
    frame->resume_roots = 0;
    frame->num_resume_roots = 0;
    frame->resume_roots_capacity = 0;
    frame->pending_resume_map = 0;
}

typedef struct JITRuntimePoolBlock {
    struct JITRuntimePoolBlock *next;
    size_t capacity;
} JITRuntimePoolBlock;

#define JIT_RUNTIME_POOL_LIMIT 32
#define JIT_RUNTIME_POOL_BYTE_LIMIT (256 * 1024)

static void *
jit_runtime_storage_acquire(JITExecutionContext *context, size_t bytes)
{
    JITRuntimePoolBlock **link;
    JITRuntimePoolBlock *block;
    size_t capacity = bytes ? bytes : sizeof(Num);

    link = (JITRuntimePoolBlock **) &context->runtime_pool;
    while (*link && (*link)->capacity < capacity)
	link = &(*link)->next;
    if (*link) {
	block = *link;
	*link = block->next;
	context->runtime_pool_count--;
    } else {
	return mymalloc(capacity, M_PROGRAM);
    }
    return block;
}

static void
jit_runtime_storage_recycle_sized(JITExecutionContext *context, void *storage,
				  size_t capacity)
{
    JITRuntimePoolBlock *block;

    if (!storage)
	return;
    if (context && capacity >= sizeof(*block)
	&& capacity <= JIT_RUNTIME_POOL_BYTE_LIMIT
	&& context->runtime_pool_count < JIT_RUNTIME_POOL_LIMIT) {
	block = storage;
	block->capacity = capacity ? capacity : sizeof(Num);
	block->next = context->runtime_pool;
	context->runtime_pool = block;
	context->runtime_pool_count++;
    } else
	myfree(storage, M_PROGRAM);
}

void
jit_execution_context_free_runtime_pool(JITExecutionContext *context)
{
    JITRuntimePoolBlock *block;

    if (!context)
	return;
    block = context->runtime_pool;
    context->runtime_pool = 0;
    context->runtime_pool_count = 0;
    while (block) {
	JITRuntimePoolBlock *next = block->next;

	myfree(block, M_PROGRAM);
	block = next;
    }
}

void
jit_native_frame_release_runtime(JITNativeFrame *frame)
{
    Var *borrowed_locals;
    int i;

    if (!frame || !frame->runtime_storage)
	return;
    if (frame->runtime_borrower)
	panic("Releasing native runtime with a live continuation borrower");
    if (!frame->owns_runtime) {
	jit_native_frame_unbind_runtime(frame);
	return;
    }
    borrowed_locals = (Var *) ((char *) frame->runtime_storage
	+ frame->program->runtime_layout.borrowed_offset);
    for (i = 0; i < frame->program->num_borrowed_locals; i++)
	free_var(borrowed_locals[i]);
    for (i = 0; i < frame->program->num_owned_slots; i++)
	free_var(frame->homes[i]);
    jit_native_frame_release_resume_roots(frame);
    if (frame->has_resume_result)
	free_var(frame->resume_result);
    frame->program->active_runtime_bytes -= frame->runtime_bytes;
    jit_runtime_storage_recycle_sized(frame->context, frame->runtime_storage,
				      frame->runtime_bytes);
    jit_native_frame_unbind_runtime(frame);
}

void
jit_native_frame_unbind_runtime(JITNativeFrame *frame)
{
    if (frame->runtime_borrower)
	panic("Unbinding native runtime with a live continuation borrower");
    frame->runtime_storage = 0;
    frame->runtime_bytes = 0;
    frame->homes = 0;
    frame->num_homes = 0;
    frame->home_states = 0;
    frame->home_capacities = 0;
    frame->owns_runtime = 0;
    frame->resume_roots = 0;
    frame->num_resume_roots = 0;
    frame->resume_roots_capacity = 0;
    frame->pending_resume_map = 0;
    frame->resume_result.type = TYPE_NONE;
    frame->resume_result.v.num = 0;
    frame->has_resume_result = 0;
}

int
jit_native_frame_capture_boundary(JITNativeFrame *frame, Var *stack,
				  unsigned depth, int map_id)
{
    Var *captured = 0;
    unsigned i;

    if (!frame || (depth && !stack) || frame->owns_boundary_stack
	|| frame->boundary_stack || frame->boundary_depth
	|| !frame->program || map_id <= 0
	|| map_id >= frame->program->num_deopt_maps)
	return 0;
    for (i = 0; i < depth; i++)
	if (stack[i].type == TYPE_NONE)
	    return 0;
    if (depth)
	captured = mymalloc(sizeof(Var) * depth, M_PROGRAM);
    for (i = 0; i < depth; i++) {
	captured[i] = stack[i];
	stack[i].type = TYPE_NONE;
	stack[i].v.num = 0;
    }
    frame->boundary_stack = captured;
    frame->boundary_depth = depth;
    frame->boundary_map = map_id;
    frame->current_map = map_id;
    frame->owns_boundary_stack = 1;
    frame->program->active_runtime_bytes += sizeof(Var) * depth;
    return 1;
}

void
jit_native_frame_release_boundary(JITNativeFrame *frame)
{
    unsigned i;

    if (!frame || !frame->owns_boundary_stack)
	return;
    for (i = 0; i < frame->boundary_depth; i++)
	free_var(frame->boundary_stack[i]);
    if (frame->program->active_runtime_bytes
	< sizeof(Var) * frame->boundary_depth)
	panic("Native boundary stack accounting underflow");
    frame->program->active_runtime_bytes -= sizeof(Var)
	* frame->boundary_depth;
    if (frame->boundary_stack)
	myfree(frame->boundary_stack, M_PROGRAM);
    frame->boundary_stack = 0;
    frame->boundary_depth = 0;
    frame->boundary_map = 0;
    frame->owns_boundary_stack = 0;
}

static int
jit_native_home_needs_owner(var_type type)
{
    return type == TYPE_STR || type == TYPE_LIST || type == TYPE_FLOAT
#ifdef WAIF_CORE
	|| type == TYPE_WAIF
#endif
	;
}

int
jit_native_frame_verify(const JITExecutionContext *context,
			const JITNativeFrame *frame)
{
    unsigned i;

    if (!context || !frame || frame->context != context
	|| !context->root_frame
	|| !context->current_frame || !frame->program
	|| context->canonical_depth > context->activation_limit
	|| context->native_depth > context->activation_limit
	|| context->canonical_depth + context->native_depth
	    > context->activation_limit)
	return 0;
    if (context->root_frame->kind != JIT_FRAME_ROOT_OVERLAY
	|| context->root_frame->caller
	|| context->root_frame->canonical_index
	    != context->root_activation_index)
	return 0;
    if (frame->caller && frame->caller->callee != frame)
	return 0;
    if (frame->callee && frame->callee->caller != frame)
	return 0;
    if ((frame == context->current_frame
	 && frame->state != JIT_FRAME_RUNNING)
	|| (frame != context->current_frame && frame->callee
	    && frame->state != JIT_FRAME_SUSPENDED))
	return 0;
    if (frame->incoming
	&& (!frame->caller || frame->incoming->caller != frame->caller
	    || frame->incoming->state != JIT_RESUME_DISPATCHED
	    || frame->incoming->map_id <= 0
	    || frame->incoming->map_id >= frame->incoming->caller->program->num_deopt_maps
	    || (frame->incoming->continuation
		? (frame->incoming->continuation
		   != frame->incoming->caller->runtime_borrower
		   || frame->incoming->result_home != UINT_MAX
		   || frame->incoming->bytecode_pc
		      != frame->incoming->caller->program->deopt_maps[
			  frame->incoming->map_id].bytecode_pc
		   || frame->incoming->error_pc
		      != frame->incoming->caller->program->deopt_maps[
			  frame->incoming->map_id].error_pc
		   || !jit_native_frame_continuation_matches(
		       frame->incoming->caller, frame->incoming->map_id))
		: (frame->incoming->result_home == UINT_MAX
		   ? frame->incoming->caller->pending_resume_map
		     != frame->incoming->map_id
		   : frame->incoming->result_home
		     >= frame->incoming->caller->num_homes))))
	return 0;
    if (frame->outgoing
	&& (frame->outgoing->caller != frame
	    || frame->outgoing->state != JIT_RESUME_DISPATCHED
	    || !frame->callee || frame->callee->incoming != frame->outgoing
	    || frame->outgoing->map_id <= 0
	    || frame->outgoing->map_id >= frame->program->num_deopt_maps
	    || (frame->outgoing->continuation
		? (frame->outgoing->continuation != frame->runtime_borrower
		   || frame->outgoing->result_home != UINT_MAX
		   || frame->outgoing->bytecode_pc
		      != frame->program->deopt_maps[
			  frame->outgoing->map_id].bytecode_pc
		   || frame->outgoing->error_pc
		      != frame->program->deopt_maps[
			  frame->outgoing->map_id].error_pc
		   || !jit_native_frame_continuation_matches(
		       frame, frame->outgoing->map_id))
		: (frame->outgoing->result_home == UINT_MAX
		   ? frame->pending_resume_map != frame->outgoing->map_id
		   : frame->outgoing->result_home >= frame->num_homes))))
	return 0;
    if (frame->kind != JIT_FRAME_COMPACT
	&& frame->canonical_index >= context->activation_limit)
	return 0;
    if (frame->entry_map < -1 || frame->current_map < -1
	|| frame->entry_map >= frame->program->num_deopt_maps
	|| frame->current_map >= frame->program->num_deopt_maps)
	return 0;
    if (frame->owns_boundary_stack) {
	if ((frame->boundary_depth && !frame->boundary_stack)
	    || frame->boundary_map <= 0
	    || frame->boundary_map >= frame->program->num_deopt_maps
	    || frame->current_map != frame->boundary_map)
	    return 0;
    } else if (frame->boundary_stack || frame->boundary_depth
	       || frame->boundary_map)
	return 0;
    if (frame->owns_invocation
	&& (frame->kind != JIT_FRAME_COMPACT || !frame->bytecode_program
	    || !frame->env || !frame->verb || !frame->verbname))
	return 0;
    if (frame->owns_runtime
	&& (!frame->runtime_storage
	    || frame->program->active_runtime_bytes < frame->runtime_bytes
	       + sizeof(Var) * frame->resume_roots_capacity))
	return 0;
    if (frame->owns_boundary_stack
	&& frame->program->active_runtime_bytes
	   < frame->runtime_bytes + sizeof(Var) * frame->boundary_depth)
	return 0;
    if (frame->runtime_borrower
	&& (!frame->owns_runtime
	    || frame->runtime_borrower->runtime_owner != frame
	    || frame->runtime_borrower->owns_runtime
	    || frame->runtime_borrower->program != frame->program
	    || frame->runtime_borrower->runtime_storage
	       != frame->runtime_storage
	    || frame->runtime_borrower->owned_values != frame->homes
	    || frame->runtime_borrower->home_capacities
	       != frame->home_capacities
	    || frame->runtime_borrower->home_states != frame->home_states
	    || frame->runtime_borrower->runtime_bytes != frame->runtime_bytes))
	return 0;
    if ((frame->num_resume_roots && !frame->resume_roots)
	|| (!frame->num_resume_roots && frame->resume_roots
	    && !frame->resume_roots_capacity)
	|| frame->num_resume_roots > frame->resume_roots_capacity
	|| (frame->pending_resume_map
	    && (!frame->owns_runtime || frame->pending_resume_map <= 0
		|| frame->pending_resume_map >= frame->program->num_deopt_maps)))
	return 0;
    if ((frame->num_homes
	 && (!frame->homes || !frame->home_states || !frame->home_capacities))
	|| (!frame->num_homes
	    && (frame->homes || frame->home_states || frame->home_capacities)))
	return 0;
    for (i = 0; i < frame->num_homes; i++) {
	unsigned j;

	if (frame->home_states[i] == JIT_HOME_EMPTY
	    || frame->home_states[i] == JIT_HOME_CONSUMED) {
	    if (frame->homes[i].type != TYPE_NONE)
		return 0;
	} else if (frame->home_states[i] == JIT_HOME_OWNED) {
	    if (frame->homes[i].type == TYPE_NONE)
		return 0;
	} else
	    return 0;
	if (frame->home_states[i] == JIT_HOME_OWNED
	    && jit_native_home_needs_owner(frame->homes[i].type))
	    for (j = 0; j < i; j++)
		if (frame->home_states[j] == JIT_HOME_OWNED
		    && frame->homes[j].type == frame->homes[i].type
		    && frame->homes[j].v.num == frame->homes[i].v.num)
		    return 0;
    }
    return 1;
}

int
jit_native_frame_home_move(JITNativeFrame *frame, unsigned home, Var *value)
{
    if (!frame || !value || home >= frame->num_homes
	|| frame->home_states[home] != JIT_HOME_EMPTY
	|| frame->homes[home].type != TYPE_NONE || value->type == TYPE_NONE)
	return 0;
    frame->homes[home] = *value;
    frame->home_states[home] = JIT_HOME_OWNED;
    value->type = TYPE_NONE;
    value->v.num = 0;
    return 1;
}

int
jit_native_frame_home_take(JITNativeFrame *frame, unsigned home, Var *value)
{
    if (!frame || !value || home >= frame->num_homes
	|| frame->home_states[home] != JIT_HOME_OWNED
	|| frame->homes[home].type == TYPE_NONE)
	return 0;
    *value = frame->homes[home];
    frame->homes[home].type = TYPE_NONE;
    frame->homes[home].v.num = 0;
    frame->home_states[home] = JIT_HOME_CONSUMED;
    return 1;
}

typedef union JITMIRAllocationHeader JITMIRAllocationHeader;

/* Preserve malloc alignment while recording actual retained bytes.  The list
 * also lets allocator teardown reclaim detached MIR allocations. */
union JITMIRAllocationHeader {
    struct {
	size_t size;
	JITMIRAllocationHeader *previous;
	JITMIRAllocationHeader *next;
    } allocation;
    long double align_long_double;
    void *align_pointer;
    void (*align_function)(void);
};

typedef struct {
    struct MIR_alloc interface;
    JITMIRAllocationHeader *allocations;
    size_t live_bytes;
    size_t live_allocations;
} JITMIRAllocator;

static void *
jit_mir_allocate(size_t size, int clear, JITMIRAllocator *allocator)
{
    JITMIRAllocationHeader *header;
    size_t total;

    if (size > UINT_MAX - sizeof(JITMIRAllocationHeader))
	return 0;
    total = sizeof(JITMIRAllocationHeader) + size;
    header = mymalloc((unsigned) total, M_PROGRAM);
    if (clear)
	memset(header, 0, total);
    header->allocation.size = size;
    header->allocation.previous = 0;
    header->allocation.next = allocator->allocations;
    if (allocator->allocations)
	allocator->allocations->allocation.previous = header;
    allocator->allocations = header;
    allocator->live_bytes += total;
    allocator->live_allocations++;
    return header + 1;
}

static void *
jit_mir_malloc(size_t size, void *data)
{
    return jit_mir_allocate(size, 0, data);
}

static void *
jit_mir_calloc(size_t count, size_t size, void *data)
{
    if (count && size > (size_t) -1 / count)
	return 0;
    return jit_mir_allocate(count * size, 1, data);
}

static void *
jit_mir_realloc(void *ptr, size_t old_size, size_t new_size, void *data)
{
    JITMIRAllocator *allocator = data;
    JITMIRAllocationHeader *header;
    JITMIRAllocationHeader *new_header;
    size_t old_total, new_total;

    if (!ptr)
	return jit_mir_allocate(new_size, 0, allocator);
    header = (JITMIRAllocationHeader *) ptr - 1;
    assert(header->allocation.size == old_size);
    (void) old_size;
    if (!new_size) {
	old_total = sizeof(JITMIRAllocationHeader) + header->allocation.size;
	if (header->allocation.previous)
	    header->allocation.previous->allocation.next
		= header->allocation.next;
	else
	    allocator->allocations = header->allocation.next;
	if (header->allocation.next)
	    header->allocation.next->allocation.previous
		= header->allocation.previous;
	allocator->live_bytes -= old_total;
	allocator->live_allocations--;
	myfree(header, M_PROGRAM);
	return 0;
    }
    if (new_size > UINT_MAX - sizeof(JITMIRAllocationHeader))
	return 0;
    old_total = sizeof(JITMIRAllocationHeader) + header->allocation.size;
    new_total = sizeof(JITMIRAllocationHeader) + new_size;
    new_header = myrealloc(header, (unsigned) new_total, M_PROGRAM);
    new_header->allocation.size = new_size;
    if (new_header->allocation.previous)
	new_header->allocation.previous->allocation.next = new_header;
    else
	allocator->allocations = new_header;
    if (new_header->allocation.next)
	new_header->allocation.next->allocation.previous = new_header;
    allocator->live_bytes = allocator->live_bytes - old_total + new_total;
    return new_header + 1;
}

static void
jit_mir_free(void *ptr, void *data)
{
    JITMIRAllocator *allocator = data;
    JITMIRAllocationHeader *header;

    if (!ptr)
	return;
    header = (JITMIRAllocationHeader *) ptr - 1;
    if (header->allocation.previous)
	header->allocation.previous->allocation.next = header->allocation.next;
    else
	allocator->allocations = header->allocation.next;
    if (header->allocation.next)
	header->allocation.next->allocation.previous = header->allocation.previous;
    allocator->live_bytes -= (sizeof(JITMIRAllocationHeader)
			      + header->allocation.size);
    allocator->live_allocations--;
    myfree(header, M_PROGRAM);
}

static JITMIRAllocator *
jit_mir_allocator_new(void)
{
    JITMIRAllocator *allocator = mymalloc(sizeof(JITMIRAllocator), M_PROGRAM);

    memset(allocator, 0, sizeof(JITMIRAllocator));
    allocator->interface.malloc = jit_mir_malloc;
    allocator->interface.calloc = jit_mir_calloc;
    allocator->interface.realloc = jit_mir_realloc;
    allocator->interface.free = jit_mir_free;
    allocator->interface.user_data = allocator;
    return allocator;
}

static void
jit_mir_allocator_free(JITMIRAllocator *allocator)
{
    JITMIRAllocationHeader *header;

    if (!allocator)
	return;
    while ((header = allocator->allocations)) {
	allocator->allocations = header->allocation.next;
	allocator->live_bytes -= (sizeof(JITMIRAllocationHeader)
				 + header->allocation.size);
	allocator->live_allocations--;
	myfree(header, M_PROGRAM);
    }
    assert(allocator->live_bytes == 0);
    assert(allocator->live_allocations == 0);
    myfree(allocator, M_PROGRAM);
}

#ifdef JIT_TESTING
int
jit_test_mir_allocator(void)
{
    JITMIRAllocator *allocator = jit_mir_allocator_new();
    void *first;
    void *second;
    void *third;
    int ok;

    first = allocator->interface.calloc(2, 8, allocator);
    second = allocator->interface.malloc(16, allocator);
    ok = first && second && !((unsigned char *) first)[0]
	&& allocator->live_allocations == 2;
    first = allocator->interface.realloc(first, 16, 32, allocator);
    third = allocator->interface.realloc(0, 0, 12, allocator);
    second = allocator->interface.realloc(second, 16, 0, allocator);
    ok = ok && first && !second && third
	&& allocator->live_allocations == 2
	&& !allocator->interface.calloc((size_t) -1, 2, allocator)
	&& !allocator->interface.malloc((size_t) UINT_MAX, allocator);
    allocator->interface.free(0, allocator);
    allocator->interface.free(first, allocator);
    ok = ok && allocator->live_allocations == 1;
    third = allocator->interface.realloc(third, 12, 0, allocator);
    ok = ok && !third && allocator->live_allocations == 0;
    third = allocator->interface.malloc(4, allocator);
    ok = ok && third && allocator->live_allocations == 1;
    jit_mir_allocator_free(allocator);
    jit_mir_allocator_free(0);
    return ok;
}
#endif

typedef struct JITPool {
    MIR_context_t context;
    JITMIRAllocator *allocator;
    uint64_t generation;
    uint64_t compiled_count;
    size_t total_machine_code_bytes;
    JITProgram *active_head;
    JITProgram *active_tail;
} JITPool;

#define JIT_CONTEXT_COUNT 4
#define JIT_NO_POOL UINT_MAX
static JITPool jit_pools[JIT_CONTEXT_COUNT];
static uint64_t jit_next_pool_generation = 1;
#define JIT_DEFAULT_HOT_THRESHOLD 32
#define JIT_DEFAULT_MAX_POOL_BYTES ((size_t) 256 * 1024 * 1024)
typedef enum {
    JIT_ROTATION_NONE,
    JIT_ROTATION_MEMORY_LIMIT,
    JIT_ROTATION_MANUAL,
    JIT_ROTATION_PROTECTION_CHANGE
} JITRotationReason;

typedef struct {
    size_t max_pool_bytes;
    time_t generation_started_at;
    uint64_t rotations;
    unsigned hot_threshold;
    unsigned effective_hot_threshold;
    unsigned region_specialization_rotations;
    JITRotationReason pending_reason;
    JITRotationReason last_reason;
    uint64_t activity_requests;
    uint64_t activity_epoch;
    uint64_t activity_last_use;
    uint64_t logical_generation;
    int compilation_demand;
} JITPoolPolicy;

static JITPoolPolicy jit_pool_policy = {
    JIT_DEFAULT_MAX_POOL_BYTES, 0, 0, JIT_DEFAULT_HOT_THRESHOLD,
    JIT_DEFAULT_HOT_THRESHOLD, 0, JIT_ROTATION_NONE, JIT_ROTATION_NONE,
    0, 0, 0, 1, 0
};
static uint64_t next_module_serial = 0;
static JITProgram *jit_specialization_queue = 0;
static FILE *jit_perf_map_file = 0;
static char jit_perf_map_filename[64];
static time_t jit_profile_detail_time = 0;
#ifdef JIT_TESTING
static int jit_profile_detail = 1;
#else
static int jit_profile_detail = 0;
#endif

static void
jit_perf_map_write_program(JITProgram *program)
{
    char name[160];

    if (!jit_perf_map_file || !program || !program->machine_code
	|| !program->machine_code_len)
	return;
    if (program->diagnostic_object >= 0 && program->diagnostic_verb > 0)
	snprintf(name, sizeof(name), "moo_jit_#%" PRIdN "_%u",
		 program->diagnostic_object, program->diagnostic_verb);
    else
	snprintf(name, sizeof(name), "moo_jit_unknown_%lx",
		 (unsigned long) (uintptr_t) program->machine_code);
    fprintf(jit_perf_map_file, "%lx %lx %s\n",
	    (unsigned long) (uintptr_t) program->machine_code,
	    (unsigned long) program->machine_code_len, name);
    fflush(jit_perf_map_file);
}

static const char *
jit_rotation_reason_name(JITRotationReason reason)
{
    switch (reason) {
    case JIT_ROTATION_MEMORY_LIMIT:
	return "memory-limit";
    case JIT_ROTATION_MANUAL:
	return "manual";
    case JIT_ROTATION_PROTECTION_CHANGE:
	return "protection-change";
    case JIT_ROTATION_NONE:
    default:
	return "none";
    }
}

static size_t
jit_context_reclaimable_bytes(JITPool *pool)
{
    size_t bytes = 0;

    if (pool->context)
	bytes += _MIR_code_allocated_size(pool->context);
    if (pool->allocator)
	bytes += pool->allocator->live_bytes;
    return bytes;
}

static size_t
jit_pool_reclaimable_bytes(void)
{
    size_t bytes = 0;
    unsigned i;

    for (i = 0; i < JIT_CONTEXT_COUNT; i++)
	bytes += jit_context_reclaimable_bytes(&jit_pools[i]);
    return bytes;
}

static size_t
jit_pool_target_bytes(void)
{
    return jit_pool_policy.max_pool_bytes
	- jit_pool_policy.max_pool_bytes / (2 * JIT_CONTEXT_COUNT);
}

static uint64_t
jit_pool_resident_programs(void)
{
    uint64_t count = 0;
    unsigned i;

    for (i = 0; i < JIT_CONTEXT_COUNT; i++)
	count += jit_pools[i].compiled_count;
    return count;
}

static void
jit_pool_advance_activity(void)
{
    uint64_t requests = (uint64_t) jit_pool_policy.hot_threshold
	* MAX(jit_pool_resident_programs(), 1);

    if (requests < 4096)
	requests = 4096;
    if (++jit_pool_policy.activity_requests < requests)
	return;
    jit_pool_policy.activity_requests = 0;
    jit_pool_policy.activity_epoch++;
    if (jit_pool_policy.max_pool_bytes) {
	size_t used = jit_pool_reclaimable_bytes();
	size_t target = jit_pool_target_bytes();
	unsigned adjustment = MAX(jit_pool_policy.effective_hot_threshold / 8, 1);

	if (used < target
	    && jit_pool_policy.effective_hot_threshold
	       > jit_pool_policy.hot_threshold) {
	    if (adjustment > jit_pool_policy.effective_hot_threshold
		- jit_pool_policy.hot_threshold)
		adjustment = jit_pool_policy.effective_hot_threshold
		    - jit_pool_policy.hot_threshold;
	    jit_pool_policy.effective_hot_threshold -= adjustment;
	} else if (used > target && jit_pool_policy.compilation_demand
		   && jit_pool_policy.effective_hot_threshold < UCHAR_MAX) {
	    if (adjustment > UCHAR_MAX
		- jit_pool_policy.effective_hot_threshold)
		adjustment = UCHAR_MAX
		    - jit_pool_policy.effective_hot_threshold;
	    jit_pool_policy.effective_hot_threshold += adjustment;
	}
    }
    jit_pool_policy.compilation_demand = 0;
}

static unsigned
jit_program_normalized_heat(JITProgram *program)
{
    uint64_t elapsed;

    if (!program)
	return 0;
    elapsed = jit_pool_policy.activity_epoch - program->residency_heat_epoch;
    while (elapsed-- && program->residency_heat)
	program->residency_heat
	    = (unsigned char) (program->residency_heat * 7 / 8);
    program->residency_heat_epoch = jit_pool_policy.activity_epoch;
    return program->residency_heat;
}

static void
jit_program_note_activity(JITProgram *program)
{
    if (!program)
	return;
    jit_program_normalized_heat(program);
    if (program->residency_heat < UCHAR_MAX)
	program->residency_heat++;
    program->residency_last_use = ++jit_pool_policy.activity_last_use;
    jit_pool_advance_activity();
}

static void
jit_pool_request_rotation_reason(JITRotationReason reason)
{
    if (jit_pool_policy.pending_reason == JIT_ROTATION_NONE)
	jit_pool_policy.pending_reason = reason;
}

static int
jit_pool_rotation_blocks_native_entry(void)
{
    return jit_pool_policy.pending_reason != JIT_ROTATION_NONE;
}

int
jit_perf_map_start(void)
{
    JITProgram *program;
    unsigned i;

    if (jit_perf_map_file)
	return 1;
    snprintf(jit_perf_map_filename, sizeof(jit_perf_map_filename),
	     "/tmp/perf-%ld.map", (long) getpid());
    jit_perf_map_file = fopen(jit_perf_map_filename, "w");
    if (!jit_perf_map_file) {
	jit_perf_map_filename[0] = '\0';
	return 0;
    }
    for (i = 0; i < JIT_CONTEXT_COUNT; i++)
	for (program = jit_pools[i].active_head; program;
	     program = program->pool_next)
	    jit_perf_map_write_program(program);
    return 1;
}

void
jit_perf_map_stop(void)
{
    if (!jit_perf_map_file)
	return;
    fclose(jit_perf_map_file);
    jit_perf_map_file = 0;
}

int
jit_perf_map_active(void)
{
    return jit_perf_map_file != 0;
}

const char *
jit_perf_map_path(void)
{
    return jit_perf_map_filename;
}

static void
jit_load_externals(MIR_context_t context)
{
    MIR_load_external(context, "jit_rt_is_true", (void *) jit_rt_is_true);
    MIR_load_external(context, "jit_rt_equality", (void *) jit_rt_equality);
    MIR_load_external(context, "jit_rt_str_cmp", (void *) jit_rt_str_cmp);
    MIR_load_external(context, "jit_rt_str_concat", (void *) jit_rt_str_concat);
    MIR_load_external(context, "jit_rt_str_concat_owned",
		      (void *) jit_rt_str_concat_owned);
    MIR_load_external(context, "jit_rt_str_ref", (void *) jit_rt_str_ref);
    MIR_load_external(context, "jit_rt_str_range_ref", (void *) jit_rt_str_range_ref);
    MIR_load_external(context, "jit_rt_list_range_ref", (void *) jit_rt_list_range_ref);
    MIR_load_external(context, "jit_rt_list_concat", (void *) jit_rt_list_concat);
    MIR_load_external(context, "jit_rt_make_singleton_list", (void *) jit_rt_make_singleton_list);
    MIR_load_external(context, "jit_rt_make_fixed_list_head",
		      (void *) jit_rt_make_fixed_list_head);
    MIR_load_external(context, "jit_rt_make_empty_list",
		      (void *) jit_rt_make_empty_list);
    MIR_load_external(context, "jit_rt_list_append", (void *) jit_rt_list_append);
    MIR_load_external(context, "jit_rt_list_append_owned",
		      (void *) jit_rt_list_append_owned);
    MIR_load_external(context, "jit_rt_fixed_list_append_owned",
		      (void *) jit_rt_fixed_list_append_owned);
    MIR_load_external(context, "jit_rt_fixed_list_store",
		      (void *) jit_rt_fixed_list_store);
    MIR_load_external(context, "jit_rt_owned_replace", (void *) jit_rt_owned_replace);
    MIR_load_external(context, "jit_rt_owned_move", (void *) jit_rt_owned_move);
    MIR_load_external(context, "jit_rt_discard_owned",
		      (void *) jit_rt_discard_owned);
    MIR_load_external(context, "jit_rt_retain_raw",
		      (void *) jit_rt_retain_raw);
    MIR_load_external(context, "jit_rt_list_index_set", (void *) jit_rt_list_index_set);
    MIR_load_external(context, "jit_rt_list_nested_index_set",
		      (void *) jit_rt_list_nested_index_set);
    MIR_load_external(context, "jit_rt_sublist_from", (void *) jit_rt_sublist_from);
    MIR_load_external(context, "jit_rt_list_in", (void *) jit_rt_list_in);
    MIR_load_external(context, "jit_rt_region_guard",
		      (void *) jit_rt_region_guard);
    MIR_load_external(context, "jit_rt_get_prop", (void *) jit_rt_get_prop);
    MIR_load_external(context, "jit_rt_get_prop_typed",
		      (void *) jit_rt_get_prop_typed);
    MIR_load_external(context, "jit_rt_get_prop_int",
		      (void *) jit_rt_get_prop_int);
    MIR_load_external(context, "jit_rt_put_prop", (void *) jit_rt_put_prop);
    MIR_load_external(context, "jit_rt_seconds_left", (void *) jit_rt_seconds_left);
    MIR_load_external(context, "jit_rt_time", (void *) jit_rt_time);
    MIR_load_external(context, "jit_rt_index", (void *) jit_rt_index);
    MIR_load_external(context, "jit_rt_rindex", (void *) jit_rt_rindex);
    MIR_load_external(context, "jit_rt_valid", (void *) jit_rt_valid);
    MIR_load_external(context, "jit_rt_parent", (void *) jit_rt_parent);
    MIR_load_external(context, "jit_rt_var_raw", (void *) jit_rt_var_raw);
}

static int
jit_ensure_context(JITPool *pool)
{
    if (pool->context)
	return 1;
    pool->allocator = jit_mir_allocator_new();
    if (!pool->allocator)
	return 0;
    pool->context = MIR_init2(&pool->allocator->interface, 0);
    if (!pool->context) {
	jit_mir_allocator_free(pool->allocator);
	pool->allocator = 0;
	return 0;
    }
    pool->generation = jit_next_pool_generation++;
    if (jit_next_pool_generation == 0)
	jit_next_pool_generation = 1;
    jit_load_externals(pool->context);
    if (jit_pool_policy.generation_started_at == 0)
	jit_pool_policy.generation_started_at = time(0);
    return 1;
}

static JITPool *
jit_pool_select_compile(unsigned *index)
{
    JITPool *best = &jit_pools[0];
    size_t best_bytes = jit_context_reclaimable_bytes(best);
    unsigned i;

    for (i = 1; i < JIT_CONTEXT_COUNT; i++) {
	size_t bytes = jit_context_reclaimable_bytes(&jit_pools[i]);

	if (bytes < best_bytes) {
	    best = &jit_pools[i];
	    best_bytes = bytes;
	}
    }
    if (index)
	*index = best - jit_pools;
    return best;
}

static void
jit_pool_register(JITProgram *program)
{
    JITPool *pool;

    if (!program || program->pool_index >= JIT_CONTEXT_COUNT)
	return;
    pool = &jit_pools[program->pool_index];
    if (program->pool_generation == pool->generation
	&& (pool->active_head == program || program->pool_prev
	    || program->pool_next))
	return;
    program->pool_generation = pool->generation;
    program->pool_prev = pool->active_tail;
    program->pool_next = 0;
    if (pool->active_tail)
	pool->active_tail->pool_next = program;
    else
	pool->active_head = program;
    pool->active_tail = program;
    pool->compiled_count++;
    pool->total_machine_code_bytes += program->machine_code_len;
    jit_perf_map_write_program(program);
    if (jit_pool_policy.max_pool_bytes
	&& jit_pool_reclaimable_bytes() >= jit_pool_policy.max_pool_bytes)
	jit_pool_request_rotation_reason(JIT_ROTATION_MEMORY_LIMIT);
}

static void
jit_pool_unregister(JITProgram *program)
{
    JITPool *pool;

    if (!program || program->pool_index >= JIT_CONTEXT_COUNT) {
	if (program) {
	    program->pool_generation = 0;
	    program->pool_index = JIT_NO_POOL;
	    program->pool_prev = 0;
	    program->pool_next = 0;
	}
	return;
    }
    pool = &jit_pools[program->pool_index];
    if (program->pool_generation != pool->generation) {
	program->pool_generation = 0;
	program->pool_index = JIT_NO_POOL;
	program->pool_prev = program->pool_next = 0;
	return;
    }
    if (program->pool_prev)
	program->pool_prev->pool_next = program->pool_next;
    else
	pool->active_head = program->pool_next;
    if (program->pool_next)
	program->pool_next->pool_prev = program->pool_prev;
    else
	pool->active_tail = program->pool_prev;
    if (pool->compiled_count > 0)
	pool->compiled_count--;
    if (pool->total_machine_code_bytes >= program->machine_code_len)
	pool->total_machine_code_bytes -= program->machine_code_len;
    else
	pool->total_machine_code_bytes = 0;
    program->pool_generation = 0;
    program->pool_index = JIT_NO_POOL;
    program->pool_prev = 0;
    program->pool_next = 0;
}

static void
jit_context_rotate(unsigned index)
{
    JITPool *pool = &jit_pools[index];
    JITProgram *current = pool->active_head;

    while (current) {
	JITProgram *next = current->pool_next;

	current->state = JIT_STATE_PENDING;
	current->native_function = 0;
	current->machine_code = 0;
	current->machine_code_len = 0;
	current->pool_generation = jit_pool_policy.logical_generation;
	current->pool_index = JIT_NO_POOL;
	if (jit_program_normalized_heat(current)
	    >= jit_pool_policy.hot_threshold)
	    current->warmup_count = jit_pool_policy.effective_hot_threshold;
	current->pool_prev = current->pool_next = 0;
	current = next;
    }
    pool->active_head = pool->active_tail = 0;
    pool->compiled_count = 0;
    pool->total_machine_code_bytes = 0;
    if (pool->context)
	MIR_finish(pool->context);
    if (pool->allocator)
	jit_mir_allocator_free(pool->allocator);
    memset(pool, 0, sizeof(*pool));
}

static unsigned
jit_pool_select_victim(void)
{
    unsigned victim = 0, i;
    uint64_t victim_heat = UINT64_MAX;
    size_t victim_bytes = 1;

    for (i = 0; i < JIT_CONTEXT_COUNT; i++) {
	JITProgram *program;
	uint64_t heat = 0;
	size_t bytes = jit_context_reclaimable_bytes(&jit_pools[i]);

	if (!bytes)
	    continue;
	for (program = jit_pools[i].active_head; program;
	     program = program->pool_next)
	    heat += jit_program_normalized_heat(program);
	if (victim_heat == UINT64_MAX
	    || heat * victim_bytes < victim_heat * bytes) {
	    victim = i;
	    victim_heat = heat;
	    victim_bytes = bytes;
	}
    }
    return victim;
}

static void
jit_pool_evict_one(void)
{
    unsigned victim = jit_pool_select_victim();
    JITPoolStats before;

    jit_pool_stats(&before);
    jit_continuation_materialize_all();

    jit_pool_stats(&before);
    if (before.native_chain_active_frames != 0)
	panic("Evicting JIT context with active native frames");
    jit_context_rotate(victim);
    jit_pool_policy.pending_reason = jit_pool_policy.max_pool_bytes
	&& jit_pool_reclaimable_bytes() > jit_pool_target_bytes()
	? JIT_ROTATION_MEMORY_LIMIT : JIT_ROTATION_NONE;
    jit_pool_policy.region_specialization_rotations = 0;
    jit_pool_policy.rotations++;
    jit_pool_policy.last_reason = JIT_ROTATION_MEMORY_LIMIT;
    oklog("JIT_POOL_EVICT: context=%u active=%"PRIu64
	  " reclaimable=%lu remaining=%lu max=%lu\n", victim,
	  before.active_programs,
	  (unsigned long) (before.total_native_allocated_bytes
			   + before.total_mir_heap_bytes),
	  (unsigned long) jit_pool_reclaimable_bytes(),
	  (unsigned long) jit_pool_policy.max_pool_bytes);
}

static void
jit_pool_rotate(JITRotationReason reason, int log_rotation)
{
    JITPoolStats before;
    time_t now = time(0);
    time_t elapsed = 0;

    jit_pool_stats(&before);
    if (jit_pool_policy.generation_started_at > 0
	&& now >= jit_pool_policy.generation_started_at)
	elapsed = now - jit_pool_policy.generation_started_at;
    jit_continuation_materialize_all();

    jit_pool_stats(&before);
    if (before.native_chain_active_frames != 0)
	panic("Rotating JIT pool with active native frames");

    {
	unsigned i;

	for (i = 0; i < JIT_CONTEXT_COUNT; i++)
	    jit_context_rotate(i);
    }
    jit_pool_policy.logical_generation++;
    if (jit_pool_policy.logical_generation == 0)
	jit_pool_policy.logical_generation = 1;
    jit_pool_policy.generation_started_at = now;
    jit_pool_policy.pending_reason = JIT_ROTATION_NONE;
    jit_pool_policy.region_specialization_rotations = 0;
    if (log_rotation) {
	jit_pool_policy.rotations++;
	jit_pool_policy.last_reason = reason;
	oklog("JIT_POOL_ROTATE: reason=%s generation=%"PRIu64"->%"PRIu64
	      " elapsed=%lds active=%"PRIu64" machine=%lu native=%lu"
	      " mir_heap=%lu reclaimable=%lu max=%lu hot_threshold=%u\n",
	      jit_rotation_reason_name(reason), before.generation,
	      jit_pool_policy.logical_generation, (long) elapsed,
	      before.active_programs,
	      (unsigned long) before.total_machine_code_bytes,
	      (unsigned long) before.total_native_allocated_bytes,
	      (unsigned long) before.total_mir_heap_bytes,
	      (unsigned long) (before.total_native_allocated_bytes
			       + before.total_mir_heap_bytes),
	      (unsigned long) jit_pool_policy.max_pool_bytes,
	      jit_pool_policy.hot_threshold);
    }
}

void
jit_pool_reset(void)
{
    jit_pool_rotate(JIT_ROTATION_MANUAL, 1);
}

void
jit_pool_request_rotation(void)
{
    jit_pool_request_rotation_reason(JIT_ROTATION_MANUAL);
}

void
jit_pool_maintain(void)
{
    JITRotationReason reason = jit_pool_policy.pending_reason;

    if (jit_specialization_queue) {
	JITProgram *program;

	jit_continuation_materialize_all();
	while ((program = jit_specialization_queue)) {
	    jit_specialization_queue = program->specialization_next;
	    program->specialization_next = 0;
	    program->specialization_pending = 0;
	    if (program->specialization_epoch != db_dispatch_epoch())
		continue;
	    if (program->state == JIT_STATE_COMPILED) {
		jit_program_release_native(program);
		program->state = JIT_STATE_PENDING;
		program->warmup_count = jit_pool_policy.hot_threshold;
	    }
	}
    }

    if (reason != JIT_ROTATION_NONE) {
	if (reason == JIT_ROTATION_MEMORY_LIMIT)
	    jit_pool_evict_one();
	else
	    jit_pool_rotate(reason, 1);
    }
}

int
jit_pool_set_policy(unsigned hot_threshold, size_t max_pool_bytes)
{
    size_t current_bytes = jit_pool_reclaimable_bytes();

    if (hot_threshold < 1 || hot_threshold > UCHAR_MAX)
	return 0;
    jit_pool_policy.hot_threshold = hot_threshold;
    jit_pool_policy.effective_hot_threshold = hot_threshold;
    jit_pool_policy.max_pool_bytes = max_pool_bytes;
    if (jit_pool_policy.pending_reason == JIT_ROTATION_MEMORY_LIMIT
	&& (!max_pool_bytes || current_bytes < max_pool_bytes))
	jit_pool_policy.pending_reason = JIT_ROTATION_NONE;
    if (max_pool_bytes && current_bytes >= max_pool_bytes)
	jit_pool_request_rotation_reason(JIT_ROTATION_MEMORY_LIMIT);
    return 1;
}

void
jit_pool_policy_stats(JITPoolPolicyStats *stats)
{
    JITPoolStats pool;
    time_t now = time(0);

    if (!stats)
	return;
    jit_pool_stats(&pool);
    memset(stats, 0, sizeof(*stats));
    stats->generation = pool.generation;
    stats->rotations = jit_pool_policy.rotations;
    stats->active_programs = pool.active_programs;
    stats->max_pool_bytes = jit_pool_policy.max_pool_bytes;
    stats->machine_code_bytes = pool.total_machine_code_bytes;
    stats->native_allocated_bytes = pool.total_native_allocated_bytes;
    stats->mir_heap_bytes = pool.total_mir_heap_bytes;
    stats->reclaimable_bytes = pool.total_native_allocated_bytes
	+ pool.total_mir_heap_bytes;
    stats->generation_started_at = jit_pool_policy.generation_started_at;
    if (stats->generation_started_at > 0 && now >= stats->generation_started_at)
	stats->generation_age = now - stats->generation_started_at;
    stats->hot_threshold = jit_pool_policy.hot_threshold;
    stats->effective_hot_threshold = jit_pool_policy.effective_hot_threshold;
    stats->context_count = JIT_CONTEXT_COUNT;
    stats->region_specialization_rotations =
	jit_pool_policy.region_specialization_rotations;
    stats->activity_requests = jit_pool_policy.activity_requests;
    stats->activity_epoch = jit_pool_policy.activity_epoch;
    stats->rotation_pending
	= jit_pool_policy.pending_reason != JIT_ROTATION_NONE;
    stats->last_rotation_reason
	= jit_rotation_reason_name(jit_pool_policy.last_reason);
}

void
jit_shutdown(void)
{
    jit_pool_rotate(JIT_ROTATION_NONE, 0);
    jit_perf_map_stop();
}

void
jit_pool_stats(JITPoolStats *stats)
{
    JITContinuationFrame *frame;
    JITProgram *program;

    if (!stats)
	return;
    memset(stats, 0, sizeof(*stats));
    stats->generation = jit_pool_policy.logical_generation;
    {
	unsigned i;

	for (i = 0; i < JIT_CONTEXT_COUNT; i++) {
	    JITPool *pool = &jit_pools[i];

	    stats->active_programs += pool->compiled_count;
	    stats->total_machine_code_bytes += pool->total_machine_code_bytes;
	    if (pool->context)
		stats->total_native_allocated_bytes
		    += _MIR_code_allocated_size(pool->context);
	    if (pool->allocator)
		stats->total_mir_heap_bytes += pool->allocator->live_bytes;
	}
    }
    for (frame = continuation_frames; frame; frame = frame->next) {
	stats->active_continuations++;
	stats->continuation_bytes += sizeof(*frame)
	    + sizeof(Var) * (frame->retained_capacity
		+ frame->spare_retained_capacity);
    }
    {
	unsigned i;

	for (i = 0; i < JIT_CONTEXT_COUNT; i++)
	    for (program = jit_pools[i].active_head; program;
		 program = program->pool_next) {
		stats->native_chain_active_frames += program->active_native_frames;
		stats->native_chain_frame_bytes += program->active_native_frame_bytes;
	    }
    }
}

typedef struct {
    JITProgram *program;
    MIR_context_t context;
    MIR_module_t module;
    MIR_item_t function;
    MIR_reg_t execution_context;
    MIR_reg_t native_frame;
    MIR_reg_t owned_values;
    MIR_reg_t home_capacities;
    MIR_item_t proto_is_true;
    MIR_item_t import_is_true;
    MIR_item_t proto_equality;
    MIR_item_t import_equality;
    MIR_item_t proto_str_cmp;
    MIR_item_t import_str_cmp;
    MIR_item_t proto_str_concat;
    MIR_item_t import_str_concat;
    MIR_item_t proto_str_concat_owned;
    MIR_item_t import_str_concat_owned;
    MIR_item_t proto_str_ref;
    MIR_item_t import_str_ref;
    MIR_item_t proto_str_range_ref;
    MIR_item_t import_str_range_ref;
    MIR_item_t proto_list_range_ref;
    MIR_item_t import_list_range_ref;
    MIR_item_t proto_list_concat;
    MIR_item_t import_list_concat;
    MIR_item_t proto_singleton_list;
    MIR_item_t import_singleton_list;
    MIR_item_t proto_fixed_list_head;
    MIR_item_t import_fixed_list_head;
    MIR_item_t proto_empty_list;
    MIR_item_t import_empty_list;
    MIR_item_t proto_list_append;
    MIR_item_t import_list_append;
    MIR_item_t proto_list_append_owned;
    MIR_item_t import_list_append_owned;
    MIR_item_t proto_fixed_list_append_owned;
    MIR_item_t import_fixed_list_append_owned;
    MIR_item_t proto_fixed_list_store;
    MIR_item_t import_fixed_list_store;
    MIR_item_t proto_owned_replace;
    MIR_item_t import_owned_replace;
    MIR_item_t proto_owned_move;
    MIR_item_t import_owned_move;
    MIR_item_t proto_discard_owned;
    MIR_item_t import_discard_owned;
    MIR_item_t proto_retain_raw;
    MIR_item_t import_retain_raw;
    MIR_item_t proto_list_index_set;
    MIR_item_t import_list_index_set;
    MIR_item_t proto_list_nested_index_set;
    MIR_item_t import_list_nested_index_set;
    MIR_item_t proto_sublist_from;
    MIR_item_t import_sublist_from;
    MIR_item_t proto_list_in;
    MIR_item_t import_list_in;
    MIR_item_t proto_region_guard;
    MIR_item_t import_region_guard;
    MIR_item_t proto_get_prop;
    MIR_item_t import_get_prop;
    MIR_item_t proto_get_prop_int;
    MIR_item_t import_get_prop_int;
    MIR_item_t proto_put_prop;
    MIR_item_t import_put_prop;
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
    MIR_item_t proto_var_raw;
    MIR_item_t import_var_raw;
    MIR_label_t shared_return[JIT_RUN_ABORT_SECONDS + 1];
} MIRBuild;

typedef struct JITStatusExit JITStatusExit;

struct JITStatusExit {
    MIR_label_t label;
    JITRunResult status;
    enum error error;
    int deopt_map;
    int location_id;
    unsigned bytecode_pc;
    unsigned source_lineno;
    JITStatusExit *next;
};

typedef struct JITTickBatchExit JITTickBatchExit;

struct JITTickBatchExit {
    MIR_label_t label;
    MIR_label_t tick_abort;
    MIR_label_t seconds_abort;
    JITTickBatchExit *next;
};

typedef struct JITNegativeModExit JITNegativeModExit;

struct JITNegativeModExit {
    MIR_label_t label;
    MIR_label_t continuation;
    MIR_reg_t source;
    MIR_reg_t destination;
    UNum mask;
    JITNegativeModExit *next;
};

static int
status_location_id(JITProgram *program, unsigned bytecode_pc,
		   unsigned source_lineno)
{
    JITSourceLocation *locations;
    int i;

    for (i = 0; i < program->num_status_locations; i++)
	if (program->status_locations[i].bytecode_pc == bytecode_pc
	    && program->status_locations[i].error_pc == bytecode_pc
	    && program->status_locations[i].source_lineno == source_lineno)
	    return i;
    locations = myrealloc(program->status_locations,
	sizeof(JITSourceLocation) * (program->num_status_locations + 1),
	M_PROGRAM);
    program->status_locations = locations;
    i = program->num_status_locations++;
    locations[i].bytecode_pc = bytecode_pc;
    locations[i].error_pc = bytecode_pc;
    locations[i].source_lineno = source_lineno;
    return i;
}

static uint64_t
elapsed_us(const struct timeval *started, const struct timeval *finished)
{
    uint64_t seconds;
    long microseconds;

    if (finished->tv_sec < started->tv_sec
	|| (finished->tv_sec == started->tv_sec
	    && finished->tv_usec < started->tv_usec))
	return 0;
    seconds = finished->tv_sec - started->tv_sec;
    microseconds = finished->tv_usec - started->tv_usec;
    if (microseconds < 0) {
	seconds--;
	microseconds += 1000000;
    }
    return seconds * 1000000 + microseconds;
}

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

static void
append_source_marker(MIRBuild *build, JITInstruction *instr, int *serial)
{
    MIR_reg_t marker;
    char name[64];

    if (instr->source_lineno == 0)
	return;
    sprintf(name, "pc_%u_line_%u_%d", instr->bytecode_pc,
	    instr->source_lineno, (*serial)++);
    marker = new_reg(build, name);
    append(build, MIR_new_insn(build->context, MIR_PRSET,
	MIR_new_reg_op(build->context, marker),
	MIR_new_int_op(build->context, 1)));
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

static void
jit_build_constant_values(JITProgram *program)
{
    JITBlock *block;
    Num *dense;
    int value;

    if (program->value_constant_bits || program->num_values <= 0
	|| program->num_values > UINT16_MAX)
	return;
    program->value_constant_bits = mymalloc((program->num_values + 7) / 8,
	M_PROGRAM);
    dense = mymalloc(sizeof(Num) * program->num_values, M_PROGRAM);
    memset(program->value_constant_bits, 0, (program->num_values + 7) / 8);
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_CONST && instr->value > 0
		&& instr->value < program->num_values
		&& instr->literal_type != TYPE_STR
		&& instr->literal_type != TYPE_LIST
#ifdef WAIF_CORE
		&& instr->literal_type != TYPE_WAIF
#endif
		) {
		program->value_constant_bits[instr->value / 8]
		    |= 1U << (instr->value % 8);
		dense[instr->value] = (Num) instr->literal;
		program->num_constant_values++;
	    }
	    if (instr == block->last)
		break;
	}
    }
    program->value_constants = program->num_constant_values
	? mymalloc(sizeof(Num) * program->num_constant_values, M_PROGRAM) : 0;
    program->constant_value_ids = program->num_constant_values
	? mymalloc(sizeof(uint16_t) * program->num_constant_values, M_PROGRAM) : 0;
    program->num_constant_values = 0;
    for (value = 1; value < program->num_values; value++)
	if (program->value_constant_bits[value / 8]
	    & (1U << (value % 8))) {
	    program->constant_value_ids[program->num_constant_values] = value;
	    program->value_constants[program->num_constant_values++] = dense[value];
	}
    myfree(dense, M_PROGRAM);
}

static int
jit_value_has_constant(JITProgram *program, int value)
{
    return program->value_constant_bits
	&& (program->value_constant_bits[value / 8]
	    & (1U << (value % 8)));
}

static Num
jit_constant_value(JITProgram *program, int value)
{
    int first = 0;
    int last = program->num_constant_values;

    assert(jit_value_has_constant(program, value));
    while (first < last) {
	int middle = first + (last - first) / 2;

	if (program->constant_value_ids[middle] < value)
	    first = middle + 1;
	else
	    last = middle;
    }
    assert(first < program->num_constant_values
	&& program->constant_value_ids[first] == value);
    return program->value_constants[first];
}

static int
integer_constant_value(JITProgram *program, int value, Num *constant)
{
    JITBlock *block;

    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_CONST && instr->value == value
		&& instr->literal_type == TYPE_INT) {
		*constant = (Num) instr->literal;
		return 1;
	    }
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

static int
positive_power_of_two_shift(Num value)
{
    UNum bits;
    int shift = 0;

    if (value <= 0)
	return -1;
    bits = (UNum) value;
    if (bits & (bits - 1))
	return -1;
    while (bits > 1) {
	bits >>= 1;
	shift++;
    }
    return shift;
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
	      int value)
{
    append(build, MIR_new_insn(build->context, MIR_MOV,
			      MIR_new_reg_op(build->context, status),
			      MIR_new_int_op(build->context, value)));
    append(build, MIR_new_insn(build->context, MIR_JMP,
			      MIR_new_label_op(build->context, common_return)));
}

static void
return_shared_status(MIRBuild *build, JITRunResult value)
{
    if (!build->shared_return[value])
	build->shared_return[value] = MIR_new_label(build->context);
    append(build, MIR_new_insn(build->context, MIR_JMP,
	MIR_new_label_op(build->context, build->shared_return[value])));
}

static void
append_shared_return_stubs(MIRBuild *build, MIR_reg_t status,
			   MIR_label_t common_return)
{
    int value;

    for (value = 0; value <= JIT_RUN_ABORT_SECONDS; value++)
	if (build->shared_return[value]) {
	    append(build, build->shared_return[value]);
	    return_status(build, status, common_return, (JITRunResult) value);
	}
}

static void
append_return_zero(MIRBuild *build, MIR_reg_t result, MIR_reg_t status,
		   MIR_label_t common_return)
{
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_mem_op(build->context,
		       sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		       offsetof(Var, v.num), result, 0, 1),
	MIR_new_int_op(build->context, 0)));
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_mem_op(build->context, MIR_T_I32,
		       offsetof(Var, type), result, 0, 1),
	MIR_new_int_op(build->context, TYPE_INT)));
    return_status(build, status, common_return, JIT_RUN_RETURNED);
}

static MIR_label_t
new_status_exit(MIRBuild *build, JITStatusExit **first, JITStatusExit **last,
		JITRunResult status, enum error error, int deopt_map,
		unsigned bytecode_pc, unsigned source_lineno)
{
    JITStatusExit *exit;

    for (exit = *first; exit; exit = exit->next)
	if (exit->status == status && exit->error == error
	    && exit->deopt_map == deopt_map
	    && exit->bytecode_pc == bytecode_pc
	    && exit->source_lineno == source_lineno)
	    return exit->label;
    exit = mymalloc(sizeof(JITStatusExit), M_PROGRAM);

    exit->label = MIR_new_label(build->context);
    exit->status = status;
    exit->error = error;
    exit->deopt_map = deopt_map;
    exit->location_id = status_location_id(build->program, bytecode_pc,
					   source_lineno);
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

static int
jit_tag_index(JITProgram *program, int value)
{
    if (!program->value_tag_slots)
	return program->num_values + value;
    return program->num_values + program->value_tag_slots[value];
}

static size_t
jit_tag_offset(JITProgram *program, int value)
{
    return (size_t) jit_tag_index(program, value) * sizeof(Num);
}

static void
jit_take_returned_owner(JITProgram *program, Var *result, Var *owned_values,
			unsigned char *home_states,
			unsigned *home_capacities)
{
    int i;

    for (i = 0; i < program->num_owned_slots; i++) {
	Var *home = &owned_values[i];
	int matches = home_states[i] == JIT_HOME_OWNED
	    && home->type == result->type;

	if (matches) {
	    switch (result->type) {
	    case TYPE_STR:
		matches = home->v.str == result->v.str;
		break;
	    case TYPE_LIST:
		matches = home->v.list == result->v.list;
		break;
	    case TYPE_FLOAT:
		matches = home->v.fnum == result->v.fnum;
		break;
#ifdef WAIF_CORE
	    case TYPE_WAIF:
		matches = home->v.waif == result->v.waif;
		break;
#endif
	    default:
		matches = 0;
		break;
	    }
	}
	if (matches) {
	    home->type = TYPE_NONE;
	    home->v.num = 0;
	    home_states[i] = JIT_HOME_CONSUMED;
	    home_capacities[i] = 0;
	    return;
	}
    }
}

static var_type
jit_runtime_type_from_db_type(var_type type)
{
    switch (type) {
    case _TYPE_STR:
	return TYPE_STR;
    case _TYPE_LIST:
	return TYPE_LIST;
    case _TYPE_FLOAT:
	return TYPE_FLOAT;
    case _TYPE_WAIF:
	return TYPE_WAIF;
    default:
	return type;
    }
}

static int
jit_runtime_base_value_slots(JITProgram *program)
{
    return program->num_values + (program->value_tag_slots
	? program->num_tag_slots : program->num_values);
}

static int
jit_runtime_value_slots(JITProgram *program)
{
    return jit_runtime_base_value_slots(program)
	+ program->num_region_exit_values;
}

static size_t
jit_region_exit_value_offset(JITProgram *program, int slot)
{
    return (size_t) (jit_runtime_base_value_slots(program) + slot)
	* sizeof(Num);
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
	last_status_exit, JIT_RUN_ERROR, E_FLOAT, instr->deopt_map,
	instr->bytecode_pc,
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

static MIR_reg_t
append_raw_value(MIRBuild *build, JITProgram *program, MIR_reg_t *values,
		 int value, MIR_reg_t deopt_values, int *serial)
{
    MIR_reg_t raw;
    char name[32];

    if ((program->value_is_tagged && program->value_is_tagged[value])
	|| !program->value_types || program->value_types[value] != TYPE_FLOAT)
	return values[value];
    sprintf(name, "raw_value%d", (*serial)++);
    raw = new_reg(build, name);
    append(build, MIR_new_insn(build->context, MIR_DMOV,
	MIR_new_mem_op(build->context, MIR_T_D, value * sizeof(Num),
		       deopt_values, 0, 1),
	MIR_new_reg_op(build->context, values[value])));
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_reg_op(build->context, raw),
	MIR_new_mem_op(build->context,
		       sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		       value * sizeof(Num), deopt_values, 0, 1)));
    return raw;
}

static void
append_materialized_exit(MIRBuild *, JITProgram *, int, MIR_reg_t *,
			 MIR_reg_t, MIR_reg_t, MIR_reg_t, MIR_label_t,
			 JITRunResult);

static void
append_status_exits(MIRBuild *build, JITStatusExit *exit,
		    JITProgram *program, MIR_reg_t *values,
		    MIR_label_t *labels,
		    MIR_reg_t source_location, MIR_reg_t deopt_map_out,
		    MIR_reg_t deopt_values, MIR_reg_t error_out,
		    MIR_reg_t status, MIR_label_t common_return)
{
    while (exit) {
	JITStatusExit *next = exit->next;

	append(build, exit->label);
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context, MIR_T_I32,
			   offsetof(JITSourceLocation, bytecode_pc),
			   source_location, 0, 1),
	    MIR_new_int_op(build->context, exit->location_id)));
	if (exit->error != E_NONE)
	    append(build, MIR_new_insn(build->context, MIR_MOV,
		MIR_new_mem_op(build->context, MIR_T_I32,
			       0, error_out, 0, 1),
		MIR_new_int_op(build->context, exit->error)));
	if (exit->status == JIT_RUN_ERROR && exit->deopt_map > 0
	    && exit->deopt_map < program->num_deopt_maps
	    && program->deopt_maps[exit->deopt_map].native_error_block > 0)
	    append(build, MIR_new_insn(build->context, MIR_JMP,
		MIR_new_label_op(build->context,
		    labels[program->deopt_maps[exit->deopt_map].native_error_block])));
	else if (exit->status == JIT_RUN_ERROR && exit->deopt_map > 0
	    && exit->deopt_map < program->num_deopt_maps)
	    append_materialized_exit(build, program, exit->deopt_map, values,
		deopt_map_out, deopt_values, status, common_return,
		JIT_RUN_ERROR);
	else
	    return_shared_status(build, exit->status);
	myfree(exit, M_PROGRAM);
	exit = next;
    }
}

static JITInstruction *jit_value_definition(JITProgram *, int);

static int
append_materialized_value(MIRBuild *build, JITProgram *program, int value,
			  int owner_slot, MIR_reg_t *values,
			  MIR_reg_t deopt_values)
{
    JITInstruction *definition = jit_value_definition(program, value);

    if (jit_value_has_constant(program, value))
	return 0;

    if (owner_slot >= 0)
	return 0;
    if (definition && definition->kind == HIR_TAC_CONST) {
	if (definition->literal_type == TYPE_FLOAT) {
	    double number = raw_to_double(definition->literal);

	    append(build, MIR_new_insn(build->context, MIR_DMOV,
		MIR_new_mem_op(build->context, MIR_T_D, value * sizeof(Num),
		    deopt_values, 0, 1),
		MIR_new_double_op(build->context, number)));
	} else
	    append(build, MIR_new_insn(build->context, MIR_MOV,
		MIR_new_mem_op(build->context,
		    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		    value * sizeof(Num), deopt_values, 0, 1),
		MIR_new_int_op(build->context, definition->literal)));
	return 1;
    }
    if (program->value_types && program->value_types[value] == TYPE_FLOAT
	&& !(program->value_is_tagged && program->value_is_tagged[value]))
	append(build, MIR_new_insn(build->context, MIR_DMOV,
	    MIR_new_mem_op(build->context, MIR_T_D, value * sizeof(Num),
		deopt_values, 0, 1),
	    MIR_new_reg_op(build->context, values[value])));
    else
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context,
		sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		value * sizeof(Num), deopt_values, 0, 1),
	    MIR_new_reg_op(build->context, values[value])));
    return 1;
}

static void
append_materialized_values(MIRBuild *build, JITProgram *program, int map_id,
			   MIR_reg_t *values, MIR_reg_t deopt_values)
{
    JITDeoptMap *map = &program->deopt_maps[map_id];
    unsigned char *materialized = mymalloc(program->num_values, M_PROGRAM);
    int i;

    memset(materialized, 0, program->num_values);
    for (i = 0; i < map->num_locals; i++) {
	int val = jit_deopt_map_local_value(program, map, i);
	if (val > 0 && !materialized[val])
	    materialized[val] = append_materialized_value(build, program, val,
		map->local_owner_slots ? map->local_owner_slots[i] : -1, values,
				      deopt_values);
    }
    for (i = 0; i < (int) map->stack_depth; i++) {
	int sval = map->stack_values[i];
	if ((!map->stack_slots || map->stack_slots[i].kind == RSS_VALUE)
	    && sval > 0 && !materialized[sval]) {
	    materialized[sval] = append_materialized_value(build, program, sval,
		map->stack_owner_slots ? map->stack_owner_slots[i] : -1, values,
				      deopt_values);
	}
    }
    for (i = 0; map->native_resume
	 && i < map->native_resume->num_values; i++) {
	int value = map->native_resume->values[i].value;

	if (map->native_resume->values[i].source == JIT_RESUME_RESULT
	    || map->native_resume->values[i].source == JIT_RESUME_OPERAND
	    || value <= 0 || value >= program->num_values)
	    continue;
	if (materialized[value])
	    continue;
	materialized[value] = append_materialized_value(build, program, value,
	    map->native_resume->values[i].source == JIT_RESUME_OWNER
	    ? map->native_resume->values[i].index : -1,
	    values, deopt_values);
    }
    myfree(materialized, M_PROGRAM);
}

static void
append_materialized_exit(MIRBuild *build, JITProgram *program, int map_id,
			 MIR_reg_t *values, MIR_reg_t deopt_map_out,
			 MIR_reg_t deopt_values, MIR_reg_t status UNUSED_,
			 MIR_label_t common_return UNUSED_, JITRunResult result)
{
    append_materialized_values(build, program, map_id, values, deopt_values);
    append(build, MIR_new_insn(build->context, MIR_MOV,
			      MIR_new_mem_op(build->context, MIR_T_I32,
					     0, deopt_map_out, 0, 1),
			      MIR_new_int_op(build->context, map_id)));
    return_shared_status(build, result);
}

static void
append_deopt_exit(MIRBuild *build, JITProgram *program, JITInstruction *instr,
		  MIR_reg_t *values, MIR_reg_t deopt_map_out,
		  MIR_reg_t deopt_values, MIR_reg_t status,
		  MIR_label_t common_return)
{
    int map_id = instr->deopt_map;

    if (instr->exit_classified) {
	assert(instr->exit_mask != JIT_EXIT_NONE);
	if (instr->bytecode_pc != NO_BYTECODE_PC)
	    assert(map_id > 0);
    }
    append_materialized_exit(build, program, map_id, values, deopt_map_out,
			     deopt_values, status, common_return,
			     JIT_RUN_FALLBACK);
}

static void
append_resume_value(MIRBuild *build, JITProgram *program, MIR_reg_t *values,
		    int value, MIR_reg_t stack, int stack_index,
		    MIR_reg_t deopt_values, int *serial)
{
    MIR_reg_t raw, address;
    char name[32];

    if (value <= 0 || value >= program->num_values)
	return;
    sprintf(name, "resume_raw%d", (*serial)++);
    raw = new_reg(build, name);
    sprintf(name, "resume_addr%d", (*serial)++);
    address = new_reg(build, name);
    append(build, MIR_new_insn(build->context, MIR_ADD,
			      MIR_new_reg_op(build->context, address),
			      MIR_new_reg_op(build->context, stack),
			      MIR_new_int_op(build->context,
					     stack_index * sizeof(Var))));
    append(build, MIR_new_call_insn(build->context, 4,
	MIR_new_ref_op(build->context, build->proto_var_raw),
	MIR_new_ref_op(build->context, build->import_var_raw),
	MIR_new_reg_op(build->context, raw),
	MIR_new_reg_op(build->context, address)));
    if (program->value_types && program->value_types[value] == TYPE_FLOAT
	&& !(program->value_is_tagged && program->value_is_tagged[value])) {
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context,
		    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		    value * sizeof(Num), deopt_values, 0, 1),
	    MIR_new_reg_op(build->context, raw)));
	append(build, MIR_new_insn(build->context, MIR_DMOV,
	    MIR_new_reg_op(build->context, values[value]),
	    MIR_new_mem_op(build->context, MIR_T_D, value * sizeof(Num),
			   deopt_values, 0, 1)));
    } else
	append(build, MIR_new_insn(build->context, MIR_MOV,
				  MIR_new_reg_op(build->context, values[value]),
				  MIR_new_reg_op(build->context, raw)));
    if (program->value_is_tagged && program->value_is_tagged[value])
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context,
		    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		    jit_tag_offset(program, value),
		    deopt_values, 0, 1),
	    MIR_new_mem_op(build->context, MIR_T_I32,
		    stack_index * sizeof(Var) + offsetof(Var, type),
		    stack, 0, 1)));
}

static void
append_stored_resume_value(MIRBuild *build, JITProgram *program,
			   MIR_reg_t *values, int value,
			   MIR_reg_t deopt_values)
{
    if (value <= 0 || value >= program->num_values)
	return;
    if (program->value_types && program->value_types[value] == TYPE_FLOAT
	&& !(program->value_is_tagged && program->value_is_tagged[value]))
	append(build, MIR_new_insn(build->context, MIR_DMOV,
	    MIR_new_reg_op(build->context, values[value]),
	    MIR_new_mem_op(build->context, MIR_T_D, value * sizeof(Num),
		deopt_values, 0, 1)));
    else
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_reg_op(build->context, values[value]),
	    MIR_new_mem_op(build->context,
		sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		value * sizeof(Num), deopt_values, 0, 1)));
}

static int
jit_call_has_native_continuation(JITProgram *program, JITInstruction *call)
{
    return call->deopt_map > 0 && call->deopt_map < program->num_deopt_maps
	&& program->deopt_maps[call->deopt_map].native_resume
	&& program->deopt_maps[call->deopt_map].native_resume->valid;
}

static JITInstruction *
jit_value_definition(JITProgram *program, int value)
{
    JITBlock *block;

    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->value == value)
		return instr;
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

static JITInstruction *
jit_unique_list_tail_user(JITProgram *program, int value)
{
    JITBlock *block;

    if (!program->value_use_counts || value <= 0
	|| value >= program->num_values
	|| program->value_use_counts[value] != 1)
	return 0;

    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->src1 == value && instr->kind == HIR_TAC_BINARY
		&& instr->op == HIR_OP_LIST_ADD_TAIL)
		return instr;
	    if (instr == block->last)
		break;
	}
    }
    return 0;
}

static int
jit_fixed_list_capacity(JITProgram *program, JITInstruction *head)
{
    JITInstruction *tail;
    int capacity = 1;

    if (!head || head->kind != HIR_TAC_UNARY
	|| head->op != HIR_OP_MAKE_SINGLETON_LIST)
	return 1;
    while ((tail = jit_unique_list_tail_user(program, head->value)) != 0) {
	if (!program->value_ownership || !program->value_owned_slots
	    || head->value <= 0 || head->value >= program->num_values
	    || tail->value <= 0 || tail->value >= program->num_values
	    || program->value_ownership[head->value] != JIT_OWNERSHIP_OWNED
	    || program->value_owned_slots[head->value] < 0
	    || program->value_owned_slots[tail->value]
	       != program->value_owned_slots[head->value])
	    break;
	capacity++;
	head = tail;
    }
    return capacity;
}

static int
jit_fixed_list_tail_index(JITProgram *program, JITInstruction *tail)
{
    JITInstruction *current = tail;
    JITInstruction *definition;
    int index = 2;

    if (!tail || tail->kind != HIR_TAC_BINARY
	|| tail->op != HIR_OP_LIST_ADD_TAIL)
	return 0;
    while ((definition = jit_value_definition(program, current->src1)) != 0) {
	if (jit_unique_list_tail_user(program, definition->value) != current)
	    return 0;
	if (definition->kind == HIR_TAC_UNARY
	    && definition->op == HIR_OP_MAKE_SINGLETON_LIST)
	    return jit_fixed_list_capacity(program, definition) >= index
		? index : 0;
	if (definition->kind != HIR_TAC_BINARY
	    || definition->op != HIR_OP_LIST_ADD_TAIL)
	    return 0;
	current = definition;
	index++;
    }
    return 0;
}

static int
jit_fixed_list_tail_has_fresh_capacity(JITProgram *program,
				       JITInstruction *tail)
{
    JITInstruction *head = tail;
    JITInstruction *definition;
    JITInstruction *instr;
    int value;
    int owner;

    while ((definition = jit_value_definition(program, head->src1)) != 0) {
	if (definition->kind == HIR_TAC_UNARY
	    && definition->op == HIR_OP_MAKE_SINGLETON_LIST) {
	    head = definition;
	    break;
	}
	if (definition->kind != HIR_TAC_BINARY
	    || definition->op != HIR_OP_LIST_ADD_TAIL)
	    return 0;
	head = definition;
    }
    if (!definition || !program->value_owned_slots
	|| head->value <= 0 || head->value >= program->num_values)
	return 0;
    owner = program->value_owned_slots[head->value];
    if (owner < 0)
	return 0;
    value = head->value;
    for (instr = head->next; instr && instr != tail; instr = instr->next) {
	if (instr->exit_mask != JIT_EXIT_NONE)
	    return 0;
	if (instr->kind == HIR_TAC_CONST)
	    continue;
	if (instr->kind != HIR_TAC_BINARY
	    || instr->op != HIR_OP_LIST_ADD_TAIL
	    || instr->src1 != value || instr->value <= 0
	    || instr->value >= program->num_values
	    || program->value_owned_slots[instr->value] != owner)
	    return 0;
	value = instr->value;
    }
    return instr == tail && tail->src1 == value
	&& program->value_owned_slots[tail->value] == owner;
}

#define JIT_REGION_MAX_ARGUMENTS 4
#define JIT_REGION_MAX_DEPTH 4
#define JIT_REGION_MAX_BLOCKS 32
#define JIT_REGION_MAX_INSTRUCTIONS 128
#define JIT_REGION_MAX_VALUES 128
#define JIT_REGION_MAX_COPIES 128
#define JIT_REGION_MAX_CALLS 8
#define JIT_REGION_MAX_LOOPS 4
#define JIT_REGION_TICK_CHUNK 1024

typedef struct JITRegionCFG JITRegionCFG;

typedef enum {
    JIT_REGION_VALUE_ARGUMENT,
    JIT_REGION_VALUE_CONSTANT,
    JIT_REGION_VALUE_TEMPORARY
} JITRegionCFGValueKind;

typedef struct {
    JITRegionCFGValueKind kind;
    int argument;
    int source_value;
    Num constant;
    var_type type;
    int owner;
} JITRegionCFGValue;

typedef struct {
    int target_value;
    int region_value;
} JITRegionCFGSnapshotValue;

typedef struct {
    int map;
    int num_values;
    JITRegionCFGSnapshotValue *values;
} JITRegionCFGSnapshot;

typedef struct {
    int dst;
    int src;
} JITRegionCFGCopy;

typedef struct {
    HIRTacKind kind;
    HIROp op;
    int value;
    int src1;
    int src2;
    int copy_base;
    int num_copies;
    int call;
    unsigned ticks;
    int loop_check;
    int list_index;
    int list_capacity;
    const char *property;
    JITRegionCFGSnapshot exit;
} JITRegionCFGInstruction;

typedef struct {
    JITRegionCFG *target;
    Objid receiver_class;
    uint64_t dispatch_epoch;
    const char *verb;
    JITRegionCFGSnapshot caller;
    int num_arguments;
    int arguments[JIT_REGION_MAX_ARGUMENTS];
} JITRegionCFGCall;

typedef enum {
    JIT_REGION_CFG_JUMP,
    JIT_REGION_CFG_BRANCH,
    JIT_REGION_CFG_RETURN,
    JIT_REGION_CFG_EXIT
} JITRegionCFGTerminator;

typedef struct {
    int instruction_base;
    int num_instructions;
    JITRegionCFGTerminator terminator;
    int condition;
    int result;
    int false_successor;
    int true_successor;
    int loop_header;
    int loop_check;
    JITRegionCFGSnapshot exit;
} JITRegionCFGBlock;

struct JITRegionCFG {
    JITProgram *program;
    JITRegionCFGValue values[JIT_REGION_MAX_VALUES];
    JITRegionCFGInstruction instructions[JIT_REGION_MAX_INSTRUCTIONS];
    JITRegionCFGCopy copies[JIT_REGION_MAX_COPIES];
    JITRegionCFGCall calls[JIT_REGION_MAX_CALLS];
    JITRegionCFGBlock blocks[JIT_REGION_MAX_BLOCKS];
    int num_values;
    int num_instructions;
    int num_copies;
    int num_calls;
    int num_blocks;
    int num_arguments;
    int num_loops;
    int has_effect;
    int owner_base;
    int num_owners;
    int entry;
};

typedef struct {
    int target_value;
    int runtime_slot;
} JITRegionExitValue;

typedef struct {
    JITProgram *target;
    Program *bytecode_program;
    const char *verb;
    Objid receiver_class;
    int map;
    int dispatched;
    int num_values;
    JITRegionExitValue *values;
    int num_arguments;
    int argument_slots[JIT_REGION_MAX_ARGUMENTS];
} JITRegionExitFrame;

struct JITRegionExit {
    uint64_t dispatch_epoch;
    int caller_map;
    int tick_slot;
    int num_frames;
    JITRegionExitFrame *frames;
};

#define JIT_REGION_EXIT_ENCODE(id) (-2 - (id))
#define JIT_REGION_EXIT_DECODE(map) (-2 - (map))

static void
jit_program_clear_region_exits(JITProgram *program)
{
    int i;

    if (!program)
	return;
    for (i = 0; i < program->num_region_exits; i++) {
	JITRegionExit *exit = &program->region_exits[i];
	int frame;

	for (frame = 0; frame < exit->num_frames; frame++) {
	    if (exit->frames[frame].verb)
		free_str(exit->frames[frame].verb);
	    if (exit->frames[frame].values)
		myfree(exit->frames[frame].values, M_PROGRAM);
	}
	if (exit->frames)
	    myfree(exit->frames, M_PROGRAM);
    }
    if (program->region_exits)
	myfree(program->region_exits, M_PROGRAM);
    program->region_exits = 0;
    program->num_region_exits = 0;
    program->region_exit_capacity = 0;
    program->num_region_exit_values = 0;
    if (program->num_region_owned_slots) {
	if (program->num_region_owned_slots > program->num_owned_slots)
	    panic("Region owner-slot count exceeds program owner slots");
	program->num_owned_slots -= program->num_region_owned_slots;
	program->num_region_owned_slots = 0;
    }
    for (i = 0; i < program->num_region_literals; i++)
	free_str(program->region_literals[i]);
    if (program->region_literals)
	myfree(program->region_literals, M_PROGRAM);
    program->region_literals = 0;
    program->num_region_literals = 0;
    program->region_literal_capacity = 0;
}

static const char *
jit_region_literal_register(JITProgram *program, const char *literal)
{
    int i;

    for (i = 0; i < program->num_region_literals; i++)
	if (!strcmp(program->region_literals[i], literal))
	    return program->region_literals[i];
    if (program->num_region_literals == program->region_literal_capacity) {
	int capacity = program->region_literal_capacity
	    ? program->region_literal_capacity * 2 : 4;

	program->region_literals = myrealloc(program->region_literals,
	    sizeof(const char *) * capacity, M_PROGRAM);
	program->region_literal_capacity = capacity;
    }
    program->region_literals[program->num_region_literals] = str_ref(literal);
    return program->region_literals[program->num_region_literals++];
}

typedef struct {
    JITRegionCFG *region;
    JITRegionCFGCall *call;
    int *arguments;
    MIR_reg_t *caller_values;
    MIR_op_t *actuals;
    MIR_reg_t *region_values;
} JITRegionExitPath;

static void
jit_region_exit_frame_register(JITProgram *program, JITRegionExitFrame *frame,
	JITRegionCFG *region, JITRegionCFGSnapshot *snapshot, int dispatched,
	JITRegionCFGCall *call)
{
    int i;

    frame->target = region->program;
    frame->bytecode_program = region->program->bytecode_program;
    frame->map = snapshot->map;
    frame->dispatched = dispatched;
    frame->num_values = snapshot->num_values;
    if (frame->num_values)
	frame->values = mymalloc(sizeof(JITRegionExitValue)
	    * frame->num_values, M_PROGRAM);
    for (i = 0; i < frame->num_values; i++) {
	frame->values[i].target_value = snapshot->values[i].target_value;
	frame->values[i].runtime_slot = program->num_region_exit_values++;
    }
    if (!call)
	return;
    frame->verb = str_ref(call->verb);
    frame->receiver_class = call->receiver_class;
    frame->num_arguments = call->num_arguments;
    for (i = 0; i < frame->num_arguments; i++)
	frame->argument_slots[i] = program->num_region_exit_values++;
}

static int
jit_region_exit_register(JITProgram *program, JITRegionExitPath *path,
	int depth, JITRegionCFG *region, JITRegionCFGSnapshot *snapshot,
	int caller_map)
{
    JITRegionExit *exit;
    int frame;

    if (!program || depth < 0 || depth > JIT_REGION_MAX_DEPTH
	|| !region || !region->program
	|| !region->program->bytecode_program || snapshot->map <= 0
	|| snapshot->map >= region->program->num_deopt_maps
	|| caller_map <= 0 || caller_map >= program->num_deopt_maps)
	return -1;
    for (frame = 0; frame < depth; frame++)
	if (!path[frame].region || !path[frame].region->program
	    || !path[frame].region->program->bytecode_program
	    || !path[frame].call || !path[frame].call->verb
	    || path[frame].call->caller.map <= 0)
	    return -1;
    if (program->num_region_exits == program->region_exit_capacity) {
	int capacity = program->region_exit_capacity
	    ? program->region_exit_capacity * 2 : 4;

	program->region_exits = program->region_exits
	    ? myrealloc(program->region_exits,
		sizeof(JITRegionExit) * capacity, M_PROGRAM)
	    : mymalloc(sizeof(JITRegionExit) * capacity, M_PROGRAM);
	memset(program->region_exits + program->region_exit_capacity, 0,
	    sizeof(JITRegionExit) * (capacity - program->region_exit_capacity));
	program->region_exit_capacity = capacity;
    }
    exit = &program->region_exits[program->num_region_exits];
    memset(exit, 0, sizeof(*exit));
    exit->dispatch_epoch = db_dispatch_epoch();
    exit->caller_map = caller_map;
    exit->tick_slot = program->num_region_exit_values++;
    exit->num_frames = depth + 1;
    exit->frames = mymalloc(sizeof(JITRegionExitFrame) * exit->num_frames,
	M_PROGRAM);
    memset(exit->frames, 0,
	sizeof(JITRegionExitFrame) * exit->num_frames);
    for (frame = 0; frame < depth; frame++)
	jit_region_exit_frame_register(program, &exit->frames[frame],
	    path[frame].region, &path[frame].call->caller, 1,
	    path[frame].call);
    jit_region_exit_frame_register(program, &exit->frames[depth], region,
	snapshot, 0, 0);
    return program->num_region_exits++;
}

static int jit_region_is_this(JITProgram *, int, int);

static int
jit_fixed_list_values(JITProgram *program, int list_value, int *arguments,
		      int *count)
{
    JITInstruction *definition = jit_value_definition(program, list_value);

    if (!definition)
	return 0;
    if (definition->kind == HIR_TAC_UNARY
	&& definition->op == HIR_OP_MAKE_SINGLETON_LIST) {
	if (*count != 0)
	    return 0;
	arguments[(*count)++] = definition->src1;
	return 1;
    }
    if (definition->kind != HIR_TAC_BINARY
	|| definition->op != HIR_OP_LIST_ADD_TAIL
	|| !jit_fixed_list_values(program, definition->src1, arguments, count)
	|| *count >= JIT_REGION_MAX_ARGUMENTS)
	return 0;
    arguments[(*count)++] = definition->src2;
    return 1;
}

static int
jit_region_cfg_supported_binary(HIROp op)
{
    return op == HIR_OP_ADD || op == HIR_OP_SUB || op == HIR_OP_MUL
	|| op == HIR_OP_DIV || op == HIR_OP_MOD
	|| op == HIR_OP_EQ || op == HIR_OP_NE || op == HIR_OP_LT
	|| op == HIR_OP_LE || op == HIR_OP_GT || op == HIR_OP_GE
	|| op == HIR_OP_BITOR || op == HIR_OP_BITXOR || op == HIR_OP_BITAND
	|| op == HIR_OP_SHL || op == HIR_OP_SHR || op == HIR_OP_LSHR;
}

static int
jit_region_cfg_argument_index(JITProgram *program, int value)
{
    JITInstruction *definition = jit_value_definition(program, value);
    JITInstruction *base;
    Num index;

    if (!definition || definition->kind != HIR_TAC_BINARY
	|| definition->op != HIR_OP_INDEX)
	return 0;
    base = jit_value_definition(program, definition->src1);
    if (!base || base->kind != HIR_TAC_LOAD_LOCAL
	|| base->local_id != SLOT_ARGS
	|| !integer_constant_value(program, definition->src2, &index)
	|| index <= 0 || index > JIT_REGION_MAX_ARGUMENTS)
	return 0;
    return (int) index;
}

static int
jit_region_cfg_fold_binary(HIROp op, Num left, Num right, Num *result)
{
    switch (op) {
    case HIR_OP_EQ:
	*result = left == right;
	return 1;
    case HIR_OP_NE:
	*result = left != right;
	return 1;
    case HIR_OP_LT:
	*result = left < right;
	return 1;
    case HIR_OP_LE:
	*result = left <= right;
	return 1;
    case HIR_OP_GT:
	*result = left > right;
	return 1;
    case HIR_OP_GE:
	*result = left >= right;
	return 1;
    default:
	return 0;
    }
}

static int
jit_region_cfg_add_value(JITRegionCFG *region, JITRegionCFGValueKind kind,
			 int argument, int source_value, Num constant,
			 var_type type)
{
    JITRegionCFGValue *value;
    int i;

    for (i = 0; i < region->num_values; i++) {
	value = &region->values[i];
	if (value->kind == kind && value->argument == argument
	    && value->source_value == source_value
	    && value->constant == constant && value->type == type)
	    return i;
    }
    if (region->num_values >= JIT_REGION_MAX_VALUES)
	return -1;
    value = &region->values[region->num_values++];
    value->kind = kind;
    value->argument = argument;
    value->source_value = source_value;
    value->constant = constant;
    value->type = type;
    value->owner = -1;
    return region->num_values - 1;
}

static int
jit_region_cfg_value(JITProgram *program, JITRegionCFG *region,
		     int *value_map, int value)
{
    JITInstruction *definition;
    Num constant;
    int argument;

    if (value <= 0 || value >= program->num_values)
	return -1;
    if (value_map[value] >= 0)
	return value_map[value];
    definition = jit_value_definition(program, value);
    argument = jit_region_cfg_argument_index(program, value);
    if (argument)
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_ARGUMENT, argument, value, 0, TYPE_INT);
    else if (integer_constant_value(program, value, &constant))
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_CONSTANT, 0, value, constant, TYPE_INT);
    else if (definition && definition->kind == HIR_TAC_CONST
	     && definition->literal_type == TYPE_OBJ)
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_CONSTANT, 0, value, definition->literal, TYPE_OBJ);
    else if (definition && definition->kind == HIR_TAC_CONST
	     && definition->literal_type == TYPE_LIST
	     && definition->literal) {
	Var *list = (Var *) (intptr_t) definition->literal;

	if (list[0].v.num != 0)
	    return -1;
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_TEMPORARY, value, value, 0, TYPE_LIST);
    }
    else if (definition && definition->kind == HIR_TAC_UNARY
	     && definition->op == HIR_OP_LENGTH) {
	JITInstruction *source = jit_value_definition(program,
	    definition->src1);

	if (!source || source->kind != HIR_TAC_LOAD_LOCAL
	    || source->local_id != SLOT_ARGS)
	    return -1;
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_CONSTANT, 0, value, region->num_arguments,
	    TYPE_INT);
    } else if (definition && definition->kind == HIR_TAC_BINARY) {
	int left = jit_region_cfg_value(program, region, value_map,
	    definition->src1);
	int right = jit_region_cfg_value(program, region, value_map,
	    definition->src2);

	if (left < 0 || right < 0
	    || region->values[left].kind != JIT_REGION_VALUE_CONSTANT
	    || region->values[right].kind != JIT_REGION_VALUE_CONSTANT
	    || !jit_region_cfg_fold_binary(definition->op,
		region->values[left].constant, region->values[right].constant,
		&constant))
	    goto ordinary_value;
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_CONSTANT, 0, value, constant, TYPE_INT);
    }
    else if (definition && (definition->kind == HIR_TAC_LOAD_LOCAL
			    || definition->kind == HIR_TAC_CONST
			    || (definition->kind == HIR_TAC_BINARY
				&& definition->op == HIR_OP_INDEX)))
	return -1;
    else {
ordinary_value:
	value_map[value] = jit_region_cfg_add_value(region,
	    JIT_REGION_VALUE_TEMPORARY, value, value, 0,
	    program->value_types && program->value_is_tagged
	    && !program->value_is_tagged[value]
	    ? program->value_types[value] : TYPE_ANY);
    }
    return value_map[value];
}

static int
jit_region_cfg_mark_blocks(JITBlock **blocks, int max_block,
			   unsigned char *state, int *block_map,
			   JITRegionCFG *region, int id)
{
    JITBlock *block;
    int successor;

    if (id <= 0 || id > max_block || !(block = blocks[id]))
	return 0;
    if (state[id] == 1) {
	JITRegionCFGBlock *header = &region->blocks[block_map[id]];

	if (!header->loop_header) {
	    if (region->num_loops >= JIT_REGION_MAX_LOOPS)
		return 0;
	    header->loop_header = 1;
	    region->num_loops++;
	}
	return 1;
    }
    if (state[id] == 2)
	return 1;
    if (region->num_blocks >= JIT_REGION_MAX_BLOCKS)
	return 0;
    state[id] = 1;
    block_map[id] = region->num_blocks++;
    for (successor = 0; successor < block->num_successors; successor++)
	if (!jit_region_cfg_mark_blocks(blocks, max_block, state, block_map,
		region, block->successors[successor]))
	    return 0;
    state[id] = 2;
    return 1;
}

static int
jit_region_cfg_add_instruction(JITRegionCFG *region, HIRTacKind kind,
			       HIROp op, int value, int src1, int src2)
{
    JITRegionCFGInstruction *instruction;

    if (region->num_instructions >= JIT_REGION_MAX_INSTRUCTIONS)
	return 0;
    instruction = &region->instructions[region->num_instructions++];
    memset(instruction, 0, sizeof(*instruction));
    instruction->kind = kind;
    instruction->op = op;
    instruction->value = value;
    instruction->src1 = src1;
    instruction->src2 = src2;
    return 1;
}

static void
jit_region_cfg_clear(JITRegionCFG *region)
{
    int block;
    int call;
    int instruction;

    for (block = 0; block < region->num_blocks; block++)
	if (region->blocks[block].exit.values) {
	    myfree(region->blocks[block].exit.values, M_PROGRAM);
	    region->blocks[block].exit.values = 0;
	}
    for (instruction = 0; instruction < region->num_instructions;
	 instruction++)
	if (region->instructions[instruction].exit.values) {
	    myfree(region->instructions[instruction].exit.values, M_PROGRAM);
	    region->instructions[instruction].exit.values = 0;
	}

    for (call = 0; call < region->num_calls; call++) {
	if (region->calls[call].caller.values) {
	    myfree(region->calls[call].caller.values, M_PROGRAM);
	    region->calls[call].caller.values = 0;
	}
	if (region->calls[call].target) {
	    jit_region_cfg_clear(region->calls[call].target);
	    myfree(region->calls[call].target, M_PROGRAM);
	    region->calls[call].target = 0;
	}
    }
    region->num_calls = 0;
}

static int jit_region_cfg_depth(JITProgram *, JITRegionCFG *, int, int);

static var_type
jit_region_cfg_return_type(JITRegionCFG *region)
{
    var_type type = TYPE_NONE;
    int block;

    for (block = 0; block < region->num_blocks; block++)
	if (region->blocks[block].terminator == JIT_REGION_CFG_RETURN) {
	    int result = region->blocks[block].result;
	    var_type result_type;

	    if (result < 0 || result >= region->num_values)
		return TYPE_ANY;
	    result_type = region->values[result].type;
	    if (type == TYPE_NONE)
		type = result_type;
	    else if (type != result_type)
		return TYPE_ANY;
	}
    return type;
}

static int
jit_region_cfg_snapshot_value(JITProgram *program, JITRegionCFG *region,
			      JITRegionCFGSnapshot *snapshot, int *value_map,
			      int target_value, var_type type)
{
    int region_value;
    int i;

    if (target_value <= 0 || target_value >= program->num_values
	|| (type != TYPE_INT && type != TYPE_ANY))
	return 0;

    for (i = 0; i < snapshot->num_values; i++)
	if (snapshot->values[i].target_value == target_value)
	    return 1;
    if (snapshot->num_values >= JIT_REGION_MAX_VALUES
	|| (region_value = jit_region_cfg_value(program, region, value_map,
		target_value)) < 0)
	return 0;
    snapshot->values[snapshot->num_values].target_value = target_value;
    snapshot->values[snapshot->num_values].region_value = region_value;
    snapshot->num_values++;
    return 1;
}

static int
jit_region_cfg_snapshot_depth(JITProgram *program, JITRegionCFG *region,
		       JITRegionCFGSnapshot *snapshot, int *value_map, int map_id,
		       unsigned stack_depth)
{
    JITDeoptMap *map;
    int i;

    if (map_id <= 0 || map_id >= program->num_deopt_maps)
	return 0;
    map = &program->deopt_maps[map_id];
    if (stack_depth > map->stack_depth)
	return 0;
    snapshot->values = mymalloc(sizeof(JITRegionCFGSnapshotValue)
	* JIT_REGION_MAX_VALUES, M_PROGRAM);
    for (i = 0; i < map->num_locals; i++) {
	int value = jit_deopt_map_local_value(program, map, i);
	JITInstruction *definition;

	if (value <= 0)
	    continue;
	definition = jit_value_definition(program, value);
	if (definition && definition->kind == HIR_TAC_LOAD_LOCAL
	    && definition->local_id == i)
	    continue;
	if (!jit_region_cfg_snapshot_value(program, region, snapshot, value_map,
		value, jit_deopt_map_local_type(program, map, i)))
	    goto fail;
    }
    for (i = 0; i < (int) stack_depth; i++) {
	ResumeStackSlot slot = map->stack_slots
	    ? map->stack_slots[i]
	    : (ResumeStackSlot){ .kind = RSS_VALUE, .data = 0 };

	if (slot.kind == RSS_VALUE
	    && !jit_region_cfg_snapshot_value(program, region, snapshot, value_map,
		map->stack_values[i], jit_deopt_map_stack_type(program, map, i)))
	    goto fail;
    }
    snapshot->map = map_id;
    return 1;

fail:
    myfree(snapshot->values, M_PROGRAM);
    memset(snapshot, 0, sizeof(*snapshot));
    return 0;
}

static int
jit_region_cfg_snapshot(JITProgram *program, JITRegionCFG *region,
		       JITRegionCFGSnapshot *snapshot, int *value_map, int map_id)
{
    if (map_id <= 0 || map_id >= program->num_deopt_maps)
	return 0;
    return jit_region_cfg_snapshot_depth(program, region, snapshot, value_map,
	map_id, program->deopt_maps[map_id].stack_depth);
}

static int
jit_region_cfg_import_block(JITProgram *program, JITRegionCFG *region,
	JITBlock *block, int *value_map, int *block_map, int depth)
{
    JITRegionCFGBlock *region_block = &region->blocks[block_map[block->id]];
    JITInstruction *instr;
    int loop_header = region_block->loop_header;

    memset(region_block, 0, sizeof(*region_block));
    region_block->loop_header = loop_header;
    region_block->instruction_base = region->num_instructions;
    region_block->condition = -1;
    region_block->result = -1;
    region_block->false_successor = -1;
    region_block->true_successor = -1;
    for (instr = block->first; instr; instr = instr->next) {
	int value;
	int src1;
	int src2;

	switch (instr->kind) {
	case HIR_TAC_LOAD_LOCAL:
	    if (instr->local_id != SLOT_ARGS && instr->local_id != SLOT_THIS)
		return 0;
	    break;
	case HIR_TAC_CONST:
	    if (instr->literal_type == TYPE_INT
		&& jit_region_cfg_value(program, region, value_map,
		    instr->value) < 0)
		return 0;
	    if (instr->literal_type == TYPE_LIST) {
		value = jit_region_cfg_value(program, region, value_map,
		    instr->value);
		if (value < 0 || region->values[value].type != TYPE_LIST
		    || !jit_region_cfg_add_instruction(region, instr->kind,
			instr->op, value, -1, -1))
		    return 0;
	    }
	    break;
	case HIR_TAC_TICK:
	    {
		unsigned ticks = instr->tick_batch_count
		    ? instr->tick_batch_count : 1;

		if (instr->tick_batch_count == (unsigned char) -1)
		    break;
		if (!jit_region_cfg_add_instruction(region, instr->kind,
			instr->op, -1, -1, -1))
		    return 0;
		region->instructions[region->num_instructions - 1].ticks = ticks;
	    }
	    break;
	case HIR_TAC_PARALLEL_COPY:
	    {
		JITRegionCFGInstruction *copy_instruction;
		JITCopy *copy;

		if (region->num_instructions >= JIT_REGION_MAX_INSTRUCTIONS)
		    return 0;
		copy_instruction =
		    &region->instructions[region->num_instructions++];
		memset(copy_instruction, 0, sizeof(*copy_instruction));
		copy_instruction->kind = HIR_TAC_PARALLEL_COPY;
		copy_instruction->copy_base = region->num_copies;
		for (copy = instr->copies; copy; copy = copy->next) {
		    int dst = jit_region_cfg_value(program, region, value_map,
			copy->dst);
		    int src = jit_region_cfg_value(program, region, value_map,
			copy->src);

		    if (dst < 0 || src < 0)
			return 0;
		    if (dst == src)
			continue;
		    if (region->values[dst].kind
			!= JIT_REGION_VALUE_TEMPORARY
			|| region->num_copies >= JIT_REGION_MAX_COPIES)
			return 0;
		    region->copies[region->num_copies].dst = dst;
		    region->copies[region->num_copies].src = src;
		    region->values[dst].type = region->values[src].type;
		    region->num_copies++;
		    copy_instruction->num_copies++;
		}
		if (!copy_instruction->num_copies)
		    region->num_instructions--;
	    }
	    break;
	case HIR_TAC_UNARY:
	    if (instr->op == HIR_OP_CHECK_LIST_FOR_SPLICE) {
		src1 = jit_region_cfg_value(program, region, value_map,
		    instr->src1);
		if (src1 < 0 || region->values[src1].type != TYPE_LIST)
		    return 0;
		value_map[instr->value] = src1;
		break;
	    }
	    if (instr->op == HIR_OP_MAKE_SINGLETON_LIST) {
		value = jit_region_cfg_value(program, region, value_map,
		    instr->value);
		src1 = jit_region_cfg_value(program, region, value_map,
		    instr->src1);
		if (value < 0 || src1 < 0
		    || region->values[src1].type != TYPE_INT
		    || !jit_region_cfg_add_instruction(region, instr->kind,
			instr->op, value, src1, -1))
		    return 0;
		region->values[value].type = TYPE_LIST;
		region->instructions[region->num_instructions - 1].list_capacity
		    = jit_fixed_list_capacity(program, instr);
		break;
	    }
	    if (instr->op == HIR_OP_LENGTH) {
		value = jit_region_cfg_value(program, region, value_map,
		    instr->value);
		if (value < 0 || region->values[value].kind
		    != JIT_REGION_VALUE_CONSTANT)
		    return 0;
		break;
	    }
	    if (instr->op != HIR_OP_COMPLEMENT)
		return 0;
	    value = jit_region_cfg_value(program, region, value_map,
		instr->value);
	    src1 = jit_region_cfg_value(program, region, value_map,
		instr->src1);
	    if (value < 0 || src1 < 0
		|| region->values[value].kind != JIT_REGION_VALUE_TEMPORARY
		|| !jit_region_cfg_add_instruction(region, instr->kind,
		    instr->op, value, src1, -1))
		return 0;
	    region->values[value].type = TYPE_INT;
	    break;
	case HIR_TAC_BINARY:
	    if (instr->op == HIR_OP_GET_PROP) {
		JITInstruction *property = jit_value_definition(program,
		    instr->src2);

		value = jit_region_cfg_value(program, region, value_map,
		    instr->value);
		src1 = jit_region_cfg_value(program, region, value_map,
		    instr->src1);
		if (value < 0 || src1 < 0
		    || region->values[src1].type != TYPE_OBJ
		    || !property || property->kind != HIR_TAC_CONST
		    || property->literal_type != TYPE_STR || !property->literal
		    || region->values[value].kind
		       != JIT_REGION_VALUE_TEMPORARY
		    || !jit_region_cfg_add_instruction(region, instr->kind,
			instr->op, value, src1, -1))
		    return 0;
		region->values[value].type = TYPE_INT;
		region->instructions[region->num_instructions - 1].property =
		    (const char *) (intptr_t) property->literal;
		break;
	    }
	    if (instr->op == HIR_OP_LIST_ADD_TAIL
		|| instr->op == HIR_OP_LIST_APPEND) {
		value = jit_region_cfg_value(program, region, value_map,
		    instr->value);
		src1 = jit_region_cfg_value(program, region, value_map,
		    instr->src1);
		src2 = jit_region_cfg_value(program, region, value_map,
		    instr->src2);
		if (value < 0 || src1 < 0 || src2 < 0
		    || region->values[src1].type != TYPE_LIST
		    || (instr->op == HIR_OP_LIST_ADD_TAIL
			&& region->values[src2].type != TYPE_INT)
		    || (instr->op == HIR_OP_LIST_APPEND
			&& region->values[src2].type != TYPE_LIST)
		    || !jit_region_cfg_add_instruction(region, instr->kind,
			instr->op, value, src1, src2))
		    return 0;
		region->values[value].type = TYPE_LIST;
		if (instr->op == HIR_OP_LIST_ADD_TAIL)
		    region->instructions[region->num_instructions - 1].list_index
			= jit_fixed_list_tail_index(program, instr);
		break;
	    }
	    value = jit_region_cfg_value(program, region, value_map,
		instr->value);
	    if (value >= 0
		&& region->values[value].kind == JIT_REGION_VALUE_CONSTANT)
		break;
	    if (instr->op == HIR_OP_INDEX
		&& value >= 0
		&& region->values[value].kind == JIT_REGION_VALUE_ARGUMENT)
		break;
	    if (!jit_region_cfg_supported_binary(instr->op))
		return 0;
	    src1 = jit_region_cfg_value(program, region, value_map,
		instr->src1);
	    src2 = jit_region_cfg_value(program, region, value_map,
		instr->src2);
	    if (value < 0 || src1 < 0 || src2 < 0
		|| region->values[value].kind != JIT_REGION_VALUE_TEMPORARY
		|| ((instr->op == HIR_OP_SHL || instr->op == HIR_OP_SHR
		     || instr->op == HIR_OP_LSHR)
		    && region->values[src2].kind == JIT_REGION_VALUE_CONSTANT
		    && (region->values[src2].constant < 0
			|| region->values[src2].constant
			   >= (Num) (sizeof(Num) * CHAR_BIT)))
		|| !jit_region_cfg_add_instruction(region, instr->kind,
		    instr->op, value, src1, src2))
		return 0;
	    region->values[value].type = TYPE_INT;
	    if ((((instr->op == HIR_OP_SHL || instr->op == HIR_OP_SHR
		   || instr->op == HIR_OP_LSHR)
		  && region->values[src2].kind != JIT_REGION_VALUE_CONSTANT)
		 || ((instr->op == HIR_OP_DIV || instr->op == HIR_OP_MOD)
		     && (region->values[src2].kind
			 != JIT_REGION_VALUE_CONSTANT
			 || region->values[src2].constant == 0)))
		&& instr->deopt_map > 0)
		(void) jit_region_cfg_snapshot(program, region,
		    &region->instructions[region->num_instructions - 1].exit,
		    value_map, instr->deopt_map);
	    if ((instr->op == HIR_OP_DIV || instr->op == HIR_OP_MOD)
		&& (region->values[src2].kind != JIT_REGION_VALUE_CONSTANT
		    || region->values[src2].constant == 0)
		&& instr->deopt_map <= 0)
		return 0;
	    break;
	case HIR_TAC_CALL_VERB:
	    {
		JITRegionCFGCall *region_call;
		JITRegionCFGInstruction *region_instruction;
		Program *target_program;
		JITDeoptMap *call_map;
		JITNativeResume *resume;
		Objid receiver_class;
		uint64_t dispatch_epoch;
		int arguments[JIT_REGION_MAX_ARGUMENTS];
		int argument_count = 0;
		int call_index;
		int argument;

		memset(arguments, 0, sizeof(arguments));
		if (depth >= JIT_REGION_MAX_DEPTH
		    || region->num_calls >= JIT_REGION_MAX_CALLS
		    || !jit_region_is_this(program, instr->src1, 0)
		    || !jit_fixed_list_values(program, instr->src3, arguments,
			&argument_count)
		    || !jit_region_site_status(program, instr->deopt_map,
			0, 0, 0)
		    || !jit_region_site_snapshot(program, instr->deopt_map,
			&target_program, &receiver_class, &dispatch_epoch)
		    || dispatch_epoch != db_dispatch_epoch()
		    || !target_program || !target_program->jit)
		    return 0;
		call_map = &program->deopt_maps[instr->deopt_map];
		resume = call_map->native_resume;
		if (call_map->reason != JIT_DEOPT_VERB_CALL
		    || jit_call_stack_operands(call_map) != 3
		    || !call_map->resume_key.site || !resume || !resume->valid
		    || !resume->cached_verb
		    || resume->cached_dispatch_epoch != dispatch_epoch
		    || resume->cached_program != target_program)
		    return 0;
		value = jit_region_cfg_value(program, region, value_map,
		    instr->value);
		if (value < 0
		    || region->values[value].kind
		       != JIT_REGION_VALUE_TEMPORARY)
		    return 0;
		call_index = region->num_calls++;
		region_call = &region->calls[call_index];
		memset(region_call, 0, sizeof(*region_call));
		region_call->receiver_class = receiver_class;
		region_call->dispatch_epoch = dispatch_epoch;
		region_call->verb = resume->cached_verb;
		region_call->num_arguments = argument_count;
		for (argument = 0; argument < argument_count; argument++) {
		    region_call->arguments[argument] = jit_region_cfg_value(
			program, region, value_map, arguments[argument]);
			if (region_call->arguments[argument] < 0)
			    return 0;
		}
		if (!jit_region_cfg_snapshot_depth(program, region,
			&region_call->caller, value_map, instr->deopt_map,
			call_map->stack_depth - 3))
		    return 0;
		region_call->target = mymalloc(sizeof(*region_call->target),
		    M_PROGRAM);
		memset(region_call->target, 0, sizeof(*region_call->target));
		if (!jit_region_cfg_depth(target_program->jit,
			region_call->target, depth + 1, argument_count)
		    || !jit_region_cfg_add_instruction(region,
			HIR_TAC_CALL_VERB, 0, value, call_index, -1))
		    return 0;
		region->values[value].type =
		    jit_region_cfg_return_type(region_call->target);
		if (region->values[value].type != TYPE_INT
		    && region->values[value].type != TYPE_LIST)
		    return 0;
		region_instruction =
		    &region->instructions[region->num_instructions - 1];
		region_instruction->call = call_index;
	    }
	    break;
	case HIR_TAC_PUT_PROP:
	    {
		JITInstruction *property;
		JITDeoptMap *map;
		int rhs;

		if (depth != 0 || region->has_effect
		    || block->num_successors != 0 || instr->next != block->last
		    || !instr->next || instr->next->kind != HIR_TAC_RETURN
		    || instr->next->src1 != instr->value
		    || !jit_region_is_this(program, instr->src1, 0)
		    || instr->deopt_map <= 0
		    || instr->deopt_map >= program->num_deopt_maps)
		    return 0;
		property = jit_value_definition(program, instr->src2);
		map = &program->deopt_maps[instr->deopt_map];
		if (!property || property->kind != HIR_TAC_CONST
		    || property->literal_type != TYPE_STR || !property->literal
		    || map->reason != JIT_DEOPT_PROPERTY_WRITE
		    || map->stack_depth < 1 || !map->stack_values)
		    return 0;
		rhs = map->stack_values[map->stack_depth - 1];
		if (instr->value <= 0 || instr->value >= program->num_values
		    || rhs <= 0 || rhs >= program->num_values
		    || !program->value_types
		    || (value = jit_region_cfg_value(program, region, value_map,
			rhs)) < 0)
		    return 0;
		if (region->values[value].kind != JIT_REGION_VALUE_ARGUMENT
		    && ((program->value_is_tagged
			 && program->value_is_tagged[rhs])
			|| program->value_types[rhs] != TYPE_INT))
		    return 0;
		value_map[instr->value] = value;
		if (!jit_region_cfg_add_instruction(region, instr->kind,
			instr->op, value, -1, -1))
		    return 0;
		region->instructions[region->num_instructions - 1].property =
		    (const char *) (intptr_t) property->literal;
		region->has_effect = 1;
	    }
	    break;
	case HIR_TAC_GUARD_TYPE:
	    {
		int guard_values[JIT_MAX_GUARD_OPERANDS] = {
		    instr->src1, instr->src2
		};
		int operand;

		for (operand = 0; operand < JIT_MAX_GUARD_OPERANDS;
		     operand++)
		    if (instr->guarded_operands & (1U << operand)) {
			int guarded = jit_region_cfg_value(program, region,
			    value_map, guard_values[operand]);

			if (guarded < 0
			    || !(instr->guarded_type_masks[operand]
				 & JIT_TYPE_MASK(TYPE_INT)))
			    return 0;
		    }
		if (region_block->loop_header && !region_block->loop_check) {
		    JITRegionCFGInstruction *loop_check;

		    if (!jit_region_cfg_add_instruction(region, instr->kind,
			    instr->op, -1, -1, -1))
			return 0;
		    loop_check =
			&region->instructions[region->num_instructions - 1];
		    loop_check->loop_check = 1;
		    (void) jit_region_cfg_snapshot(program, region,
			&loop_check->exit, value_map, instr->deopt_map);
		    region_block->loop_check = 1;
		}
	    }
	    break;
	case HIR_TAC_DEOPT:
	    jit_region_cfg_snapshot(program, region, &region_block->exit, value_map,
		instr->deopt_map);
	    region_block->terminator = JIT_REGION_CFG_EXIT;
	    goto finished;
	case HIR_TAC_RETURN0:
	    region_block->terminator = JIT_REGION_CFG_EXIT;
	    goto finished;
	case HIR_TAC_LABEL:
	case HIR_TAC_JUMP:
	    break;
	case HIR_TAC_BRANCH_FALSE:
	    if (instr != block->last || block->num_successors != 2
		|| (region_block->condition = jit_region_cfg_value(program,
		    region, value_map, instr->src1)) < 0)
		return 0;
	    region_block->terminator = JIT_REGION_CFG_BRANCH;
	    region_block->false_successor = block_map[block->successors[0]];
	    region_block->true_successor = block_map[block->successors[1]];
	    break;
	case HIR_TAC_RETURN:
	    if (instr != block->last
		|| (region_block->result = jit_region_cfg_value(program, region,
		    value_map, instr->src1)) < 0)
		return 0;
	    region_block->terminator = JIT_REGION_CFG_RETURN;
	    break;
	default:
	    return 0;
	}
	if (instr == block->last)
	    break;
    }
finished:
    region_block->num_instructions = region->num_instructions
	- region_block->instruction_base;
    if (region_block->loop_header && !region_block->loop_check)
	return 0;
    if (region_block->condition >= 0 || region_block->result >= 0
	|| region_block->terminator == JIT_REGION_CFG_EXIT)
	return 1;
    if (block->num_successors != 1)
	return 0;
    region_block->terminator = JIT_REGION_CFG_JUMP;
    region_block->true_successor = block_map[block->successors[0]];
    return region_block->true_successor >= 0;
}

static int
jit_region_cfg_depth(JITProgram *program, JITRegionCFG *region, int depth,
		     int num_arguments)
{
    JITBlock *block;
    JITBlock **blocks = 0;
    unsigned char *state = 0;
    int *block_map = 0;
    int *value_map = 0;
    int max_block = 0;
    int release_ir;
    int valid = 0;

    if (!program || !program->eligible)
	return 0;
    memset(region, 0, sizeof(*region));
    region->program = program;
    region->num_arguments = num_arguments;
    release_ir = !program->blocks;
    if (release_ir && !jit_program_restore_ir(program))
	return 0;
    for (block = program->blocks; block; block = block->next)
	if (block->id > max_block)
	    max_block = block->id;
    if (!program->blocks || max_block <= 0)
	goto done;
    blocks = mymalloc((max_block + 1) * sizeof(*blocks), M_PROGRAM);
    state = mymalloc(max_block + 1, M_PROGRAM);
    block_map = mymalloc((max_block + 1) * sizeof(*block_map), M_PROGRAM);
    value_map = mymalloc(program->num_values * sizeof(*value_map), M_PROGRAM);
    memset(blocks, 0, (max_block + 1) * sizeof(*blocks));
    memset(state, 0, max_block + 1);
    memset(block_map, -1, (max_block + 1) * sizeof(*block_map));
    memset(value_map, -1, program->num_values * sizeof(*value_map));
    for (block = program->blocks; block; block = block->next) {
	if (block->id <= 0 || block->id > max_block || blocks[block->id])
	    goto done;
	blocks[block->id] = block;
    }
    if (!jit_region_cfg_mark_blocks(blocks, max_block, state, block_map,
	    region, program->blocks->id))
	goto done;
    region->entry = block_map[program->blocks->id];
    for (block = program->blocks; block; block = block->next)
	if (block_map[block->id] >= 0
	    && !jit_region_cfg_import_block(program, region, block, value_map,
		block_map, depth))
	    goto done;
    valid = region->num_blocks > 0;

done:
    if (value_map)
	myfree(value_map, M_PROGRAM);
    if (block_map)
	myfree(block_map, M_PROGRAM);
    if (state)
	myfree(state, M_PROGRAM);
    if (blocks)
	myfree(blocks, M_PROGRAM);
    if (!valid)
	jit_region_cfg_clear(region);
    if (release_ir)
	jit_program_release_ir(program, 0);
    return valid;
}

#ifdef JIT_TESTING
static int
jit_region_cfg(JITProgram *program, JITRegionCFG *region)
{
    return jit_region_cfg_depth(program, region, 0,
	JIT_REGION_MAX_ARGUMENTS);
}
#endif

static int
jit_region_is_this(JITProgram *program, int value, int depth)
{
    JITInstruction *definition;
    JITBlock *block;
    int matched = 0;

    if (value <= 0 || value >= program->num_values
	|| depth >= program->num_values)
	return 0;
    definition = jit_value_definition(program, value);
    if (definition && definition->kind == HIR_TAC_LOAD_LOCAL)
	return definition->local_id == SLOT_THIS;
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;

	    if (instr->kind == HIR_TAC_PARALLEL_COPY)
		for (copy = instr->copies; copy; copy = copy->next)
		    if (copy->dst == value) {
			if (!jit_region_is_this(program, copy->src, depth + 1))
			    return 0;
			matched = 1;
		    }
	    if (instr == block->last)
		break;
	}
    }
    return matched;
}

static int
jit_region_cfg_call(JITProgram *program, JITInstruction *call,
		    JITRegionCFG *region, int *arguments, int *argument_count,
		    Objid *receiver_class, uint64_t *dispatch_epoch)
{
    Program *target_program;

    *argument_count = 0;
    if (!call || call->kind != HIR_TAC_CALL_VERB
	|| call->deopt_map <= 0 || call->deopt_map >= program->num_deopt_maps
	|| !jit_region_site_status(program, call->deopt_map, 0, 0, 0)
	|| !call->src3
	|| !jit_region_site_snapshot(program, call->deopt_map,
	    &target_program, receiver_class, dispatch_epoch)
	|| *dispatch_epoch != db_dispatch_epoch()
	|| !target_program || !target_program->jit
	|| !jit_fixed_list_values(program, call->src3, arguments,
	    argument_count)
	|| !jit_region_cfg_depth(target_program->jit, region, 0,
	    *argument_count))
	return 0;
    return 1;
}

static int
jit_region_cfg_call_supported(JITProgram *program, JITInstruction *call)
{
    JITRegionCFG region;
    int arguments[JIT_REGION_MAX_ARGUMENTS];
    int argument_count;
    Objid receiver_class;
    uint64_t dispatch_epoch;
    int supported;

    memset(arguments, 0, sizeof(arguments));
    supported = jit_region_cfg_call(program, call, &region, arguments,
	&argument_count, &receiver_class, &dispatch_epoch);
    if (supported)
	jit_region_cfg_clear(&region);
    return supported;
}

static JITInstruction *
jit_region_deferred_list_tail(JITProgram *program, JITInstruction *call)
{
    JITInstruction *tail;
    JITInstruction *between;
    int head;

    if (!call || call->kind != HIR_TAC_CALL_VERB || call->src3 <= 0
	|| call->src3 >= program->num_values || !program->value_types
	|| !program->value_is_tagged || !program->value_ownership
	|| !program->value_owned_slots || !program->value_use_counts
	|| !program->value_escape_flags)
	return 0;
    tail = jit_value_definition(program, call->src3);
    if (!tail || tail->kind != HIR_TAC_BINARY
	|| tail->op != HIR_OP_LIST_ADD_TAIL || tail->value != call->src3
	|| program->value_use_counts[tail->value] != 1
	|| program->value_is_tagged[tail->value]
	|| program->value_types[tail->value] != TYPE_LIST
	|| tail->src1 <= 0 || tail->src1 >= program->num_values
	|| program->value_is_tagged[tail->src1]
	|| program->value_types[tail->src1] != TYPE_LIST
	|| tail->src2 <= 0 || tail->src2 >= program->num_values
	|| (!(program->value_is_tagged[tail->src2])
	    && program->value_types[tail->src2] != TYPE_INT)
	|| (program->value_is_tagged[tail->src2]
	    && (program->value_ownership[tail->src2] == JIT_OWNERSHIP_OWNED
		|| program->value_ownership[tail->src2]
		   == JIT_OWNERSHIP_OWNED_PROPERTY)))
	return 0;
    head = tail->src1;
    if (program->value_ownership[head] != JIT_OWNERSHIP_OWNED
	|| program->value_use_counts[head] != 1
	|| (program->value_escape_flags[head]
	    & (JIT_ESCAPE_RETURN | JIT_ESCAPE_CALL | JIT_ESCAPE_STORE
	       | JIT_ESCAPE_MERGE | JIT_ESCAPE_MULTIPLE_USES))
	|| program->value_owned_slots[head] < 0
	|| program->value_owned_slots[tail->value]
	   != program->value_owned_slots[head])
	return 0;
    for (between = tail->next; between && between != call;
	 between = between->next)
	if (between->kind != HIR_TAC_TICK)
	    return 0;
    if (between != call)
	return 0;
    return tail;
}

#ifdef JIT_TESTING
int
jit_test_region_cfg(JITProgram *program, int *blocks, int *instructions,
		    int *branches, int *returns)
{
    JITRegionCFG region;
    int block;

    if (!jit_region_cfg(program, &region))
	return 0;
    *blocks = region.num_blocks;
    *instructions = region.num_instructions;
    *branches = 0;
    *returns = 0;
    for (block = 0; block < region.num_blocks; block++) {
	if (region.blocks[block].terminator == JIT_REGION_CFG_BRANCH)
	    (*branches)++;
	else if (region.blocks[block].terminator == JIT_REGION_CFG_RETURN)
	    (*returns)++;
    }
    jit_region_cfg_clear(&region);
    return 1;
}

static void
jit_test_region_cfg_call_counts(JITRegionCFG *region, int depth,
				int *calls, int *maximum_depth)
{
    int call;

    if (depth > *maximum_depth)
	*maximum_depth = depth;
    for (call = 0; call < region->num_calls; call++) {
	(*calls)++;
	jit_test_region_cfg_call_counts(region->calls[call].target, depth + 1,
	    calls, maximum_depth);
    }
}

int
jit_test_region_cfg_calls(JITProgram *program, int *calls,
			  int *maximum_depth)
{
    JITRegionCFG region;

    if (!jit_region_cfg(program, &region))
	return 0;
    *calls = 0;
    *maximum_depth = 0;
    jit_test_region_cfg_call_counts(&region, 0, calls, maximum_depth);
    jit_region_cfg_clear(&region);
    return 1;
}

int
jit_test_region_cfg_exits(JITProgram *program, int *exits, int *values)
{
    JITRegionCFG region;
    int block;
    int instruction;

    if (!jit_region_cfg(program, &region))
	return 0;
    *exits = 0;
    *values = 0;
    for (block = 0; block < region.num_blocks; block++)
	if (region.blocks[block].exit.map > 0) {
	    (*exits)++;
	    *values += region.blocks[block].exit.num_values;
	}
    for (instruction = 0; instruction < region.num_instructions;
	 instruction++)
	if (region.instructions[instruction].exit.map > 0) {
	    (*exits)++;
	    *values += region.instructions[instruction].exit.num_values;
	}
    jit_region_cfg_clear(&region);
    return 1;
}
#endif

static MIR_op_t
jit_region_cfg_operand(MIRBuild *build, JITRegionCFG *region, int value,
	int *arguments, MIR_reg_t *caller_values, MIR_op_t *actuals,
	MIR_reg_t *region_values)
{
    JITRegionCFGValue *region_value = &region->values[value];

    if (region_value->kind == JIT_REGION_VALUE_ARGUMENT) {
	if (actuals)
	    return actuals[region_value->argument - 1];
	return MIR_new_reg_op(build->context,
	    caller_values[arguments[region_value->argument - 1]]);
    }
    if (region_value->kind == JIT_REGION_VALUE_CONSTANT)
	return MIR_new_int_op(build->context, region_value->constant);
    return MIR_new_reg_op(build->context, region_values[value]);
}

static int
jit_region_cfg_assign_owners(JITProgram *root_program, JITRegionCFG *region)
{
    int value;
    int call;
    int instruction;

    region->owner_base = root_program->num_owned_slots;
    region->num_owners = region->program->num_owned_slots;
    root_program->num_owned_slots += region->num_owners;
    root_program->num_region_owned_slots += region->num_owners;
    for (value = 0; value < region->num_values; value++)
	if (region->values[value].type == TYPE_LIST) {
	    int owner = jit_resolve_owner_slot(region->program,
		region->values[value].source_value);

	    if (owner >= 0)
		region->values[value].owner = region->owner_base + owner;
	    else {
		region->values[value].owner = root_program->num_owned_slots++;
		root_program->num_region_owned_slots++;
		region->num_owners++;
	    }
	}
    for (instruction = 0; instruction < region->num_instructions;
	 instruction++) {
	JITRegionCFGInstruction *instr = &region->instructions[instruction];

	if (instr->kind == HIR_TAC_BINARY
	    && instr->op == HIR_OP_LIST_ADD_TAIL)
	    region->values[instr->value].owner = region->values[instr->src1].owner;
	else if (instr->kind == HIR_TAC_PARALLEL_COPY) {
	    int copy;

	    for (copy = 0; copy < instr->num_copies; copy++) {
		JITRegionCFGCopy *item = &region->copies[instr->copy_base + copy];

		if (region->values[item->src].type == TYPE_LIST) {
		    region->values[item->dst].type = TYPE_LIST;
		    region->values[item->dst].owner =
			region->values[item->src].owner;
		}
	    }
	}
    }
    for (call = 0; call < region->num_calls; call++)
	if (!jit_region_cfg_assign_owners(root_program,
		region->calls[call].target))
	    return 0;
    return 1;
}

static int
jit_region_cfg_return_owner(JITRegionCFG *region, int result)
{
    if (result < 0 || result >= region->num_values
	|| region->values[result].type != TYPE_LIST)
	return -1;
    return region->values[result].owner;
}

static void
append_region_deferred_tail(MIRBuild *build, JITProgram *program,
	JITInstruction *deferred_tail, MIR_reg_t *values,
	MIR_reg_t deopt_values, MIR_reg_t owned_values, int *copy_serial)
{
    MIR_reg_t raw;
    MIR_op_t type;

    if (!deferred_tail)
	return;
    raw = append_raw_value(build, program, values, deferred_tail->src2,
	deopt_values, copy_serial);
    type = program->value_is_tagged[deferred_tail->src2]
	? MIR_new_mem_op(build->context, MIR_T_I32,
	    jit_tag_offset(program, deferred_tail->src2), deopt_values, 0, 1)
	: MIR_new_int_op(build->context, TYPE_INT);
    append(build, MIR_new_call_insn(build->context, 9,
	MIR_new_ref_op(build->context, build->proto_list_append_owned),
	MIR_new_ref_op(build->context, build->import_list_append_owned),
	MIR_new_reg_op(build->context, values[deferred_tail->value]),
	MIR_new_reg_op(build->context, owned_values),
	MIR_new_reg_op(build->context, build->home_capacities),
	MIR_new_int_op(build->context,
	    program->value_owned_slots[deferred_tail->src1]),
	MIR_new_reg_op(build->context, values[deferred_tail->src1]),
	MIR_new_reg_op(build->context, raw), type));
}

static void
append_region_exit_frame(MIRBuild *build, JITRegionExitFrame *frame,
	JITRegionCFGSnapshot *snapshot, JITRegionExitPath *source,
	JITProgram *root_program, MIR_reg_t deopt_values)
{
    int value;

    for (value = 0; value < snapshot->num_values; value++)
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context,
		sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		jit_region_exit_value_offset(root_program,
		    frame->values[value].runtime_slot), deopt_values, 0, 1),
	    jit_region_cfg_operand(build, source->region,
		snapshot->values[value].region_value, source->arguments,
		source->caller_values, source->actuals,
		source->region_values)));
    if (source->call)
	for (value = 0; value < source->call->num_arguments; value++)
	    append(build, MIR_new_insn(build->context, MIR_MOV,
		MIR_new_mem_op(build->context,
		    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
		    jit_region_exit_value_offset(root_program,
			frame->argument_slots[value]), deopt_values, 0, 1),
		jit_region_cfg_operand(build, source->region,
		    source->call->arguments[value], source->arguments,
		    source->caller_values, source->actuals,
		    source->region_values)));
}

static void
append_region_exact_exit(MIRBuild *build, JITRegionCFG *region,
	JITRegionCFGSnapshot *snapshot, int exit_id, int *arguments,
	MIR_reg_t *caller_values, MIR_op_t *actuals, MIR_reg_t *region_values,
	JITRegionExitPath *path, int depth,
	MIR_reg_t path_ticks, MIR_label_t cold, JITProgram *root_program,
	MIR_reg_t deopt_values, MIR_reg_t owned_values, MIR_reg_t tick_result,
	MIR_reg_t deopt_map_out, int caller_map, JITInstruction *deferred_tail,
	int *copy_serial)
{
    JITRegionExit *exit = &root_program->region_exits[exit_id];
    JITRegionExitPath source;
    int frame;

    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_mem_op(build->context,
	    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
	    jit_region_exit_value_offset(root_program, exit->tick_slot),
	    deopt_values, 0, 1),
	MIR_new_reg_op(build->context, path_ticks)));
    for (frame = 0; frame < depth; frame++)
	append_region_exit_frame(build, &exit->frames[frame],
	    &path[frame].call->caller, &path[frame], root_program,
	    deopt_values);
    memset(&source, 0, sizeof(source));
    source.region = region;
    source.arguments = arguments;
    source.caller_values = caller_values;
    source.actuals = actuals;
    source.region_values = region_values;
    append_region_exit_frame(build, &exit->frames[depth], snapshot, &source,
	root_program, deopt_values);
    append(build, MIR_new_insn(build->context, MIR_BLE,
	MIR_new_label_op(build->context, cold),
	MIR_new_reg_op(build->context, tick_result),
	MIR_new_reg_op(build->context, path_ticks)));
    append_region_deferred_tail(build, root_program, deferred_tail,
	caller_values, deopt_values, owned_values, copy_serial);
    append_materialized_values(build, root_program, caller_map,
	caller_values, deopt_values);
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_mem_op(build->context, MIR_T_I32, 0, deopt_map_out, 0, 1),
	MIR_new_int_op(build->context, JIT_REGION_EXIT_ENCODE(exit_id))));
    return_shared_status(build, JIT_RUN_REGION_EXIT);
}

static void
append_region_cfg_body(MIRBuild *build, JITRegionCFG *region,
	int *arguments, MIR_reg_t *caller_values, MIR_op_t *actuals,
	MIR_reg_t path_ticks, MIR_label_t cold, MIR_op_t result,
	MIR_label_t continuation, JITProgram *root_program,
	MIR_reg_t deopt_values, MIR_reg_t owned_values, MIR_reg_t tick_result,
	MIR_reg_t timed_out, MIR_reg_t receiver, MIR_reg_t progr,
	MIR_reg_t error_out, MIR_reg_t deopt_map_out, int caller_map,
	JITInstruction *deferred_tail, JITRegionExitPath *path, int depth,
	int result_owner, int *copy_serial)
{
    MIR_label_t labels[JIT_REGION_MAX_BLOCKS];
    MIR_label_t instruction_exits[JIT_REGION_MAX_INSTRUCTIONS];
    MIR_reg_t region_values[JIT_REGION_MAX_VALUES];
    int instruction_exit_ids[JIT_REGION_MAX_INSTRUCTIONS];
    int block;
    int instruction_index;
    int value;
    char name[32];

    memset(region_values, 0, sizeof(region_values));
    for (value = 0; value < region->num_values; value++)
	if (region->values[value].kind == JIT_REGION_VALUE_TEMPORARY) {
	    sprintf(name, "region_value%d", (*copy_serial)++);
	    region_values[value] = new_reg(build, name);
	}
    for (block = 0; block < region->num_blocks; block++)
	labels[block] = MIR_new_label(build->context);
    memset(instruction_exits, 0, sizeof(instruction_exits));
    memset(instruction_exit_ids, -1, sizeof(instruction_exit_ids));
    for (instruction_index = 0;
	 instruction_index < region->num_instructions;
	 instruction_index++)
	if (region->instructions[instruction_index].exit.map > 0) {
	    int exit_id = jit_region_exit_register(root_program, path, depth,
		region, &region->instructions[instruction_index].exit,
		caller_map);

	    if (exit_id >= 0) {
		instruction_exits[instruction_index] =
		    MIR_new_label(build->context);
		instruction_exit_ids[instruction_index] = exit_id;
	    }
	}
    append(build, MIR_new_insn(build->context, MIR_JMP,
	MIR_new_label_op(build->context, labels[region->entry])));

    for (block = 0; block < region->num_blocks; block++) {
	JITRegionCFGBlock *region_block = &region->blocks[block];
	append(build, labels[block]);
	for (instruction_index = region_block->instruction_base;
	     instruction_index < region_block->instruction_base
		+ region_block->num_instructions; instruction_index++) {
	    JITRegionCFGInstruction *instruction =
		&region->instructions[instruction_index];
	    MIR_op_t dst;
	    MIR_op_t src1;
	    MIR_op_t src2;

	    if (instruction->kind == HIR_TAC_TICK) {
		append(build, MIR_new_insn(build->context, MIR_ADD,
		    MIR_new_reg_op(build->context, path_ticks),
		    MIR_new_reg_op(build->context, path_ticks),
		    MIR_new_int_op(build->context, instruction->ticks)));
		continue;
	    }
	    if (instruction->loop_check) {
		MIR_label_t exact = instruction_exits[instruction_index];

		if (!exact)
		    exact = cold;
		append(build, MIR_new_insn(build->context, MIR_BNE,
		    MIR_new_label_op(build->context, exact),
		    MIR_new_mem_op(build->context, MIR_T_I32, 0,
			timed_out, 0, 1),
		    MIR_new_int_op(build->context, 0)));
		append(build, MIR_new_insn(build->context, MIR_BLE,
		    MIR_new_label_op(build->context, cold),
		    MIR_new_reg_op(build->context, tick_result),
		    MIR_new_reg_op(build->context, path_ticks)));
		append(build, MIR_new_insn(build->context, MIR_BGE,
		    MIR_new_label_op(build->context, exact),
		    MIR_new_reg_op(build->context, path_ticks),
		    MIR_new_int_op(build->context, JIT_REGION_TICK_CHUNK)));
		continue;
	    }
	    if (instruction->kind == HIR_TAC_PARALLEL_COPY) {
		MIR_reg_t temps[JIT_REGION_MAX_COPIES];
		int copy;

		for (copy = 0; copy < instruction->num_copies; copy++) {
		    JITRegionCFGCopy *region_copy = &region->copies[
			instruction->copy_base + copy];

		    sprintf(name, "region_copy%d", (*copy_serial)++);
		    temps[copy] = new_reg(build, name);
		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_reg_op(build->context, temps[copy]),
			jit_region_cfg_operand(build, region,
			    region_copy->src, arguments, caller_values,
			    actuals, region_values)));
		}
		for (copy = 0; copy < instruction->num_copies; copy++) {
		    JITRegionCFGCopy *region_copy = &region->copies[
			instruction->copy_base + copy];

		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_reg_op(build->context,
			    region_values[region_copy->dst]),
			MIR_new_reg_op(build->context, temps[copy])));
		}
		continue;
	    }
	    if (instruction->kind == HIR_TAC_CONST
		&& region->values[instruction->value].type == TYPE_LIST) {
		int owner = region->values[instruction->value].owner;

		append(build, MIR_new_call_insn(build->context, 3,
		    MIR_new_ref_op(build->context, build->proto_empty_list),
		    MIR_new_ref_op(build->context, build->import_empty_list),
		    MIR_new_reg_op(build->context,
			region_values[instruction->value])));
		append(build, MIR_new_call_insn(build->context, 6,
		    MIR_new_ref_op(build->context, build->proto_owned_replace),
		    MIR_new_ref_op(build->context, build->import_owned_replace),
		    MIR_new_reg_op(build->context, owned_values),
		    MIR_new_int_op(build->context, owner),
		    MIR_new_reg_op(build->context,
			region_values[instruction->value]),
		    MIR_new_int_op(build->context, TYPE_LIST)));
		continue;
	    }
	    if (instruction->kind == HIR_TAC_UNARY
		&& instruction->op == HIR_OP_MAKE_SINGLETON_LIST) {
		int owner = region->values[instruction->value].owner;
		MIR_op_t source = jit_region_cfg_operand(build, region,
		    instruction->src1, arguments, caller_values, actuals,
		    region_values);

		if (instruction->list_capacity > 1)
		    append(build, MIR_new_call_insn(build->context, 6,
			MIR_new_ref_op(build->context,
			    build->proto_fixed_list_head),
			MIR_new_ref_op(build->context,
			    build->import_fixed_list_head),
			MIR_new_reg_op(build->context,
			    region_values[instruction->value]), source,
			MIR_new_int_op(build->context, TYPE_INT),
			MIR_new_int_op(build->context,
			    instruction->list_capacity)));
		else
		    append(build, MIR_new_call_insn(build->context, 5,
			MIR_new_ref_op(build->context,
			    build->proto_singleton_list),
			MIR_new_ref_op(build->context,
			    build->import_singleton_list),
			MIR_new_reg_op(build->context,
			    region_values[instruction->value]), source,
			MIR_new_int_op(build->context, TYPE_INT)));
		append(build, MIR_new_call_insn(build->context, 6,
		    MIR_new_ref_op(build->context, build->proto_owned_replace),
		    MIR_new_ref_op(build->context, build->import_owned_replace),
		    MIR_new_reg_op(build->context, owned_values),
		    MIR_new_int_op(build->context, owner),
		    MIR_new_reg_op(build->context,
			region_values[instruction->value]),
		    MIR_new_int_op(build->context, TYPE_LIST)));
		if (instruction->list_capacity > 1)
		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_mem_op(build->context, MIR_T_I32,
			    owner * sizeof(unsigned), build->home_capacities,
			    0, 1),
			MIR_new_int_op(build->context,
			    instruction->list_capacity)));
		continue;
	    }
	    if (instruction->kind == HIR_TAC_BINARY
		&& instruction->op == HIR_OP_LIST_ADD_TAIL) {
		int owner = region->values[instruction->src1].owner;
		MIR_op_t list = jit_region_cfg_operand(build, region,
		    instruction->src1, arguments, caller_values, actuals,
		    region_values);
		MIR_op_t element = jit_region_cfg_operand(build, region,
		    instruction->src2, arguments, caller_values, actuals,
		    region_values);

		if (owner < 0 || owner != region->values[instruction->value].owner)
		    panic("Region list-tail ownership was not coalesced");
		if (instruction->list_index > 1)
		    append(build, MIR_new_call_insn(build->context, 7,
			MIR_new_ref_op(build->context,
			    build->proto_fixed_list_store),
			MIR_new_ref_op(build->context,
			    build->import_fixed_list_store),
			MIR_new_reg_op(build->context,
			    region_values[instruction->value]),
			list,
			MIR_new_int_op(build->context,
			    instruction->list_index), element,
			MIR_new_int_op(build->context, TYPE_INT)));
		else
		    append(build, MIR_new_call_insn(build->context, 9,
			MIR_new_ref_op(build->context,
			    build->proto_list_append_owned),
			MIR_new_ref_op(build->context,
			    build->import_list_append_owned),
			MIR_new_reg_op(build->context,
			    region_values[instruction->value]),
			MIR_new_reg_op(build->context, owned_values),
			MIR_new_reg_op(build->context, build->home_capacities),
			MIR_new_int_op(build->context, owner), list, element,
			MIR_new_int_op(build->context, TYPE_INT)));
		continue;
	    }
	    if (instruction->kind == HIR_TAC_BINARY
		&& instruction->op == HIR_OP_LIST_APPEND) {
		int owner = region->values[instruction->value].owner;

		append(build, MIR_new_call_insn(build->context, 6,
		    MIR_new_ref_op(build->context, build->proto_list_concat),
		    MIR_new_ref_op(build->context, build->import_list_concat),
		    MIR_new_reg_op(build->context,
			region_values[instruction->value]),
		    jit_region_cfg_operand(build, region, instruction->src1,
			arguments, caller_values, actuals, region_values),
		    jit_region_cfg_operand(build, region, instruction->src2,
			arguments, caller_values, actuals, region_values),
		    MIR_new_reg_op(build->context, error_out)));
		append(build, MIR_new_call_insn(build->context, 6,
		    MIR_new_ref_op(build->context, build->proto_owned_replace),
		    MIR_new_ref_op(build->context, build->import_owned_replace),
		    MIR_new_reg_op(build->context, owned_values),
		    MIR_new_int_op(build->context, owner),
		    MIR_new_reg_op(build->context,
			region_values[instruction->value]),
		    MIR_new_int_op(build->context, TYPE_LIST)));
		continue;
	    }
	    if (instruction->kind == HIR_TAC_BINARY
		&& instruction->op == HIR_OP_GET_PROP) {
		MIR_label_t normal = MIR_new_label(build->context);
		const char *property = jit_region_literal_register(root_program,
		    instruction->property);

		append(build, MIR_new_call_insn(build->context, 8,
		    MIR_new_ref_op(build->context, build->proto_get_prop_int),
		    MIR_new_ref_op(build->context, build->import_get_prop_int),
		    MIR_new_reg_op(build->context,
			region_values[instruction->value]),
		    jit_region_cfg_operand(build, region, instruction->src1,
			arguments, caller_values, actuals, region_values),
		    MIR_new_int_op(build->context, TYPE_OBJ),
		    MIR_new_int_op(build->context, (intptr_t) property),
		    MIR_new_reg_op(build->context, progr),
		    MIR_new_reg_op(build->context, error_out)));
		append(build, MIR_new_insn(build->context, MIR_BEQ,
		    MIR_new_label_op(build->context, normal),
		    MIR_new_mem_op(build->context, MIR_T_I32, 0,
			error_out, 0, 1),
		    MIR_new_int_op(build->context, E_NONE)));
		append(build, MIR_new_insn(build->context, MIR_MOV,
		    MIR_new_mem_op(build->context, MIR_T_I32, 0,
			error_out, 0, 1),
		    MIR_new_int_op(build->context, E_NONE)));
		append(build, MIR_new_insn(build->context, MIR_JMP,
		    MIR_new_label_op(build->context, cold)));
		append(build, normal);
		continue;
	    }
	    if (instruction->kind == HIR_TAC_CALL_VERB) {
		JITRegionCFGCall *region_call =
		    &region->calls[instruction->call];
		MIR_op_t nested_actuals[JIT_REGION_MAX_ARGUMENTS];
		MIR_label_t nested_continuation =
		    MIR_new_label(build->context);
		int argument;

		for (argument = 0; argument < region_call->num_arguments;
		     argument++)
		    nested_actuals[argument] = jit_region_cfg_operand(build,
			region, region_call->arguments[argument], arguments,
			caller_values, actuals, region_values);
		path[depth].region = region;
		path[depth].call = region_call;
		path[depth].arguments = arguments;
		path[depth].caller_values = caller_values;
		path[depth].actuals = actuals;
		path[depth].region_values = region_values;
		append_region_cfg_body(build, region_call->target, arguments,
		    caller_values, nested_actuals, path_ticks, cold,
		    MIR_new_reg_op(build->context,
			region_values[instruction->value]),
		    nested_continuation, root_program, deopt_values, owned_values,
		    tick_result, timed_out, receiver, progr, error_out,
		    deopt_map_out, caller_map, deferred_tail, path, depth + 1,
		    region->values[instruction->value].owner, copy_serial);
		append(build, nested_continuation);
		continue;
	    }
	    if (instruction->kind == HIR_TAC_PUT_PROP) {
		MIR_label_t committed = MIR_new_label(build->context);
		MIR_reg_t put_ok;
		const char *property = jit_region_literal_register(root_program,
		    instruction->property);

		append(build, MIR_new_insn(build->context, MIR_BLE,
		    MIR_new_label_op(build->context, cold),
		    MIR_new_reg_op(build->context, tick_result),
		    MIR_new_reg_op(build->context, path_ticks)));
		sprintf(name, "region_put%d", (*copy_serial)++);
		put_ok = new_reg(build, name);
		append(build, MIR_new_call_insn(build->context, 9,
		    MIR_new_ref_op(build->context, build->proto_put_prop),
		    MIR_new_ref_op(build->context, build->import_put_prop),
		    MIR_new_reg_op(build->context, put_ok),
		    MIR_new_reg_op(build->context, receiver),
		    MIR_new_int_op(build->context, (intptr_t) property),
		    MIR_new_reg_op(build->context, progr),
		    jit_region_cfg_operand(build, region, instruction->value,
			arguments, caller_values, actuals, region_values),
		    MIR_new_int_op(build->context, TYPE_INT),
		    MIR_new_reg_op(build->context, error_out)));
		append(build, MIR_new_insn(build->context, MIR_BGT,
		    MIR_new_label_op(build->context, committed),
		    MIR_new_reg_op(build->context, put_ok),
		    MIR_new_int_op(build->context, 0)));
		append(build, MIR_new_insn(build->context, MIR_MOV,
		    MIR_new_mem_op(build->context, MIR_T_I32, 0,
			error_out, 0, 1),
		    MIR_new_int_op(build->context, E_NONE)));
		append(build, MIR_new_insn(build->context, MIR_JMP,
		    MIR_new_label_op(build->context, cold)));
		append(build, committed);
		continue;
	    }
	    dst = MIR_new_reg_op(build->context,
		region_values[instruction->value]);
	    src1 = jit_region_cfg_operand(build, region, instruction->src1,
		arguments, caller_values, actuals, region_values);
	    if (instruction->kind == HIR_TAC_UNARY)
		append(build, MIR_new_insn(build->context, MIR_XOR,
		    dst, src1, MIR_new_int_op(build->context, -1)));
	    else {
		src2 = jit_region_cfg_operand(build, region,
		    instruction->src2, arguments, caller_values, actuals,
		    region_values);
		if (instruction->op == HIR_OP_DIV
		    || instruction->op == HIR_OP_MOD) {
		    MIR_label_t exceptional =
			instruction_exits[instruction_index]
			? instruction_exits[instruction_index] : cold;
		    MIR_label_t normal = MIR_new_label(build->context);
		    MIR_label_t done = MIR_new_label(build->context);

		    append(build, MIR_new_insn(build->context, MIR_BF,
			MIR_new_label_op(build->context, exceptional), src2));
		    append(build, MIR_new_insn(build->context, MIR_BNE,
			MIR_new_label_op(build->context, normal), src2,
			MIR_new_int_op(build->context, -1)));
		    append(build, instruction->op == HIR_OP_DIV
			? MIR_new_insn(build->context, MIR_NEG, dst, src1)
			: MIR_new_insn(build->context, MIR_MOV, dst,
			    MIR_new_int_op(build->context, 0)));
		    append(build, MIR_new_insn(build->context, MIR_JMP,
			MIR_new_label_op(build->context, done)));
		    append(build, normal);
		    append(build, MIR_new_insn(build->context,
			binary_code(instruction->op), dst, src1, src2));
		    append(build, done);
		} else {
		    if (instruction->op == HIR_OP_SHL
			|| instruction->op == HIR_OP_SHR
			|| instruction->op == HIR_OP_LSHR) {
			append(build, MIR_new_insn(build->context, MIR_BLT,
			    MIR_new_label_op(build->context,
				instruction_exits[instruction_index]
				? instruction_exits[instruction_index] : cold), src2,
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_BGE,
			    MIR_new_label_op(build->context,
				instruction_exits[instruction_index]
				? instruction_exits[instruction_index] : cold), src2,
			    MIR_new_int_op(build->context,
				sizeof(Num) * CHAR_BIT)));
		    }
		    append(build, MIR_new_insn(build->context,
			binary_code(instruction->op), dst, src1, src2));
		}
	    }
	}
    if (region_block->terminator == JIT_REGION_CFG_RETURN) {
	int source_owner = jit_region_cfg_return_owner(region,
	    region_block->result);

	if (source_owner >= 0 && result_owner >= 0)
	    append(build, MIR_new_call_insn(build->context, 5,
		MIR_new_ref_op(build->context, build->proto_owned_move),
		MIR_new_ref_op(build->context, build->import_owned_move),
		MIR_new_reg_op(build->context, owned_values),
		MIR_new_int_op(build->context, result_owner),
		MIR_new_int_op(build->context, source_owner)));
	append(build, MIR_new_insn(build->context, MIR_MOV, result,
		jit_region_cfg_operand(build, region, region_block->result,
		    arguments, caller_values, actuals, region_values)));
	    append(build, MIR_new_insn(build->context, MIR_JMP,
		MIR_new_label_op(build->context, continuation)));
	} else if (region_block->terminator == JIT_REGION_CFG_BRANCH) {
	    append(build, MIR_new_insn(build->context, MIR_BF,
		MIR_new_label_op(build->context,
		    labels[region_block->false_successor]),
		jit_region_cfg_operand(build, region,
		    region_block->condition, arguments, caller_values,
		    actuals, region_values)));
	    append(build, MIR_new_insn(build->context, MIR_JMP,
		MIR_new_label_op(build->context,
		    labels[region_block->true_successor])));
	} else if (region_block->terminator == JIT_REGION_CFG_EXIT) {
	    int exit_id = jit_region_exit_register(root_program, path, depth,
		region, &region_block->exit, caller_map);

	    if (exit_id >= 0) {
		append_region_exact_exit(build, region, &region_block->exit,
		    exit_id, arguments, caller_values, actuals, region_values,
		    path, depth,
		    path_ticks, cold, root_program, deopt_values, owned_values,
		    tick_result, deopt_map_out, caller_map, deferred_tail,
		    copy_serial);
		continue;
	    }
	    append(build, MIR_new_insn(build->context, MIR_JMP,
		MIR_new_label_op(build->context, cold)));
	}
	else
	    append(build, MIR_new_insn(build->context, MIR_JMP,
		MIR_new_label_op(build->context,
		    labels[region_block->true_successor])));
    }
    for (instruction_index = 0; instruction_index < region->num_instructions;
	 instruction_index++)
	if (instruction_exits[instruction_index]) {
	    append(build, instruction_exits[instruction_index]);
	    append_region_exact_exit(build, region,
		&region->instructions[instruction_index].exit,
		instruction_exit_ids[instruction_index], arguments, caller_values,
		actuals, region_values, path, depth, path_ticks, cold, root_program,
		deopt_values, owned_values, tick_result, deopt_map_out,
		caller_map, deferred_tail, copy_serial);
	}
}

static void
append_region_cfg_dependency_guards(MIRBuild *build, JITRegionCFG *region,
	MIR_reg_t receiver, MIR_op_t receiver_type, Objid root_class,
	uint64_t root_epoch, MIR_label_t cold, int *copy_serial)
{
    int call;

    for (call = 0; call < region->num_calls; call++) {
	JITRegionCFGCall *region_call = &region->calls[call];

	if (region_call->receiver_class != root_class
	    || region_call->dispatch_epoch != root_epoch) {
	    MIR_reg_t guard;
	    char name[32];

	    sprintf(name, "region_guard%d", (*copy_serial)++);
	    guard = new_reg(build, name);
	    append(build, MIR_new_call_insn(build->context, 7,
		MIR_new_ref_op(build->context, build->proto_region_guard),
		MIR_new_ref_op(build->context, build->import_region_guard),
		MIR_new_reg_op(build->context, guard),
		MIR_new_reg_op(build->context, receiver), receiver_type,
		MIR_new_int_op(build->context,
		    region_call->receiver_class),
		MIR_new_int_op(build->context,
		    region_call->dispatch_epoch)));
	    append(build, MIR_new_insn(build->context, MIR_BF,
		MIR_new_label_op(build->context, cold),
		MIR_new_reg_op(build->context, guard)));
	}
	append_region_cfg_dependency_guards(build, region_call->target,
	    receiver, receiver_type, root_class, root_epoch, cold,
	    copy_serial);
    }
}

static int
append_region_cfg_call(MIRBuild *build, JITProgram *program,
	JITInstruction *call, MIR_reg_t *values, MIR_reg_t tick_result,
	MIR_reg_t timed_out, MIR_reg_t progr, MIR_reg_t error_out,
	MIR_reg_t owned_values, MIR_reg_t deopt_map_out, MIR_reg_t deopt_values,
	MIR_reg_t status, MIR_label_t common_return, MIR_label_t continuation,
	JITInstruction *deferred_tail, int *copy_serial)
{
    JITRegionCFG region;
    JITDeoptMap *map;
    MIR_label_t cold;
    MIR_label_t success;
    MIR_reg_t dispatch_guard;
    MIR_reg_t path_ticks;
    MIR_op_t receiver_type;
    JITRegionExitPath path[JIT_REGION_MAX_DEPTH + 1];
    int arguments[JIT_REGION_MAX_ARGUMENTS];
    unsigned char guarded_arguments[JIT_REGION_MAX_ARGUMENTS];
    int argument_count;
    var_type result_type;
    int result_owner = -1;
    int node;
    int operand;
    Objid receiver_class;
    uint64_t dispatch_epoch;
    char name[32];

    memset(arguments, 0, sizeof(arguments));
    memset(path, 0, sizeof(path));
    if (!continuation)
	return 0;
    if (!jit_region_cfg_call(program, call, &region, arguments,
	    &argument_count, &receiver_class, &dispatch_epoch))
	return 0;
    result_type = jit_region_cfg_return_type(&region);
    if (call->value <= 0 || call->value >= program->num_values
	|| call->src1 <= 0 || call->src1 >= program->num_values
	|| (result_type != TYPE_INT && result_type != TYPE_LIST)
	|| (!program->value_is_tagged[call->value]
	    && program->value_types[call->value] != result_type))
	goto fail;
    for (node = 0; node < region.num_values; node++) {
	JITRegionCFGValue *region_value = &region.values[node];

	if (region_value->kind == JIT_REGION_VALUE_ARGUMENT) {
	    int argument = region_value->argument;
	    int value;

	    if (argument <= 0 || argument > argument_count)
		goto fail;
	    value = arguments[argument - 1];
	    if (value <= 0 || value >= program->num_values
		|| (!program->value_is_tagged[value]
		    && program->value_types[value] != TYPE_INT))
		goto fail;
	}
    }
    if (result_type == TYPE_LIST)
	result_owner = jit_resolve_owner_slot(program, call->value);
    if (!jit_region_cfg_assign_owners(program, &region))
	goto fail;

    cold = MIR_new_label(build->context);
    success = MIR_new_label(build->context);
    sprintf(name, "region_guard%d", (*copy_serial)++);
    dispatch_guard = new_reg(build, name);
    receiver_type = program->value_is_tagged[call->src1]
	? MIR_new_mem_op(build->context, MIR_T_I32,
	    jit_tag_offset(program, call->src1), deopt_values, 0, 1)
	: MIR_new_int_op(build->context, program->value_types[call->src1]);
    append(build, MIR_new_call_insn(build->context, 7,
	MIR_new_ref_op(build->context, build->proto_region_guard),
	MIR_new_ref_op(build->context, build->import_region_guard),
	MIR_new_reg_op(build->context, dispatch_guard),
	MIR_new_reg_op(build->context, values[call->src1]),
	receiver_type,
	MIR_new_int_op(build->context, receiver_class),
	MIR_new_int_op(build->context, dispatch_epoch)));
    append(build, MIR_new_insn(build->context, MIR_BF,
	MIR_new_label_op(build->context, cold),
	MIR_new_reg_op(build->context, dispatch_guard)));
    append_region_cfg_dependency_guards(build, &region, values[call->src1],
	receiver_type, receiver_class, dispatch_epoch, cold, copy_serial);

    memset(guarded_arguments, 0, sizeof(guarded_arguments));
    for (node = 0; node < region.num_values; node++)
	if (region.values[node].kind == JIT_REGION_VALUE_ARGUMENT
	    && !guarded_arguments[region.values[node].argument - 1]) {
	    int argument = region.values[node].argument;
	    int value = arguments[argument - 1];

	    guarded_arguments[argument - 1] = 1;
	    if (program->value_is_tagged[value])
		append(build, MIR_new_insn(build->context, MIR_BNE,
		    MIR_new_label_op(build->context, cold),
		    MIR_new_mem_op(build->context, MIR_T_I32,
			jit_tag_offset(program, value), deopt_values, 0, 1),
		    MIR_new_int_op(build->context, TYPE_INT)));
	}
    append(build, MIR_new_insn(build->context, MIR_BNE,
	MIR_new_label_op(build->context, cold),
	MIR_new_mem_op(build->context, MIR_T_I32, 0, timed_out, 0, 1),
	MIR_new_int_op(build->context, 0)));

    sprintf(name, "region_ticks%d", (*copy_serial)++);
    path_ticks = new_reg(build, name);
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_reg_op(build->context, path_ticks),
	MIR_new_int_op(build->context, 0)));
    append_region_cfg_body(build, &region, arguments, values, 0, path_ticks,
	cold, MIR_new_reg_op(build->context, values[call->value]), success,
	program, deopt_values, owned_values, tick_result, timed_out,
	values[call->src1], progr, error_out, deopt_map_out, call->deopt_map,
	deferred_tail, path, 0, result_owner, copy_serial);
    append(build, success);
    append(build, MIR_new_insn(build->context, MIR_BLE,
	MIR_new_label_op(build->context, cold),
	MIR_new_reg_op(build->context, tick_result),
	MIR_new_reg_op(build->context, path_ticks)));
    append(build, MIR_new_insn(build->context, MIR_SUB,
	MIR_new_reg_op(build->context, tick_result),
	MIR_new_reg_op(build->context, tick_result),
	MIR_new_reg_op(build->context, path_ticks)));
    if (program->value_is_tagged[call->value])
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_mem_op(build->context, MIR_T_I32,
		jit_tag_offset(program, call->value), deopt_values, 0, 1),
	    MIR_new_int_op(build->context, result_type)));
    map = &program->deopt_maps[call->deopt_map];
    for (operand = 0; map->stack_boundary_ownership
	 && operand < (int) map->stack_depth; operand++)
	if (map->stack_boundary_ownership[operand]
	    == JIT_BOUNDARY_VALUE_RELEASE_AFTER_RESUME) {
	    int value = map->stack_values[operand];
	    int owner = map->stack_owner_slots
		? map->stack_owner_slots[operand] : -1;
	    int raw_value = deferred_tail && value == deferred_tail->value
		&& owner >= 0 ? deferred_tail->src1 : value;
	    MIR_reg_t raw = append_raw_value(build, program, values, raw_value,
		deopt_values, copy_serial);

	    append(build, MIR_new_call_insn(build->context, 6,
		MIR_new_ref_op(build->context, build->proto_discard_owned),
		MIR_new_ref_op(build->context, build->import_discard_owned),
		MIR_new_reg_op(build->context, owned_values),
		MIR_new_int_op(build->context, owner),
		MIR_new_reg_op(build->context, raw),
		MIR_new_int_op(build->context, TYPE_LIST)));
	}
    append(build, MIR_new_insn(build->context, MIR_JMP,
	MIR_new_label_op(build->context, continuation)));
    append(build, cold);
    append_region_deferred_tail(build, program, deferred_tail, values,
	deopt_values, owned_values, copy_serial);
    append_materialized_exit(build, program, call->deopt_map, values,
	deopt_map_out, deopt_values, status, common_return, JIT_RUN_CALL_VERB);
    jit_region_site_mark_spliced(program, call->deopt_map);
    jit_region_cfg_clear(&region);
    return 1;

fail:
    jit_region_cfg_clear(&region);
    return 0;
}

static int
append_region_call(MIRBuild *build, JITProgram *program,
	JITInstruction *call, MIR_reg_t *values, MIR_reg_t tick_result,
	MIR_reg_t timed_out, MIR_reg_t progr, MIR_reg_t error_out,
	MIR_reg_t owned_values, MIR_reg_t deopt_map_out, MIR_reg_t deopt_values,
	MIR_reg_t status, MIR_label_t common_return, MIR_label_t continuation,
	JITInstruction *deferred_tail, int *copy_serial)
{
    return append_region_cfg_call(build, program, call, values, tick_result,
	timed_out, progr, error_out, owned_values, deopt_map_out, deopt_values,
	status, common_return, continuation, deferred_tail, copy_serial);
}

typedef enum {
    JIT_LIST_APPEND_BORROWED,
    JIT_LIST_APPEND_CONSUME_HOME
} JITListAppendMode;

static JITListAppendMode
jit_list_tail_consume_mode(JITProgram *program, JITInstruction *tail)
{
    int value;

    if (!program->value_ownership || !program->value_owned_slots
	|| !program->value_use_counts || !program->value_escape_flags
	|| tail->op != HIR_OP_LIST_ADD_TAIL)
	return JIT_LIST_APPEND_BORROWED;
    value = tail->src1;
    if (value <= 0 || value >= program->num_values
	|| tail->value <= 0 || tail->value >= program->num_values
	|| program->value_ownership[value] != JIT_OWNERSHIP_OWNED
	|| program->value_use_counts[value] != 1
	|| (program->value_escape_flags[value]
	    & (JIT_ESCAPE_RETURN | JIT_ESCAPE_CALL | JIT_ESCAPE_STORE
	       | JIT_ESCAPE_MERGE | JIT_ESCAPE_MULTIPLE_USES)))
	return JIT_LIST_APPEND_BORROWED;
    if (program->value_owned_slots[value] < 0)
	return JIT_LIST_APPEND_BORROWED;
    return program->value_owned_slots[tail->value]
	== program->value_owned_slots[value]
	? JIT_LIST_APPEND_CONSUME_HOME : JIT_LIST_APPEND_BORROWED;
}

static int
jit_value_is_dead_owned_list(JITProgram *program, JITInstruction *instr)
{
    if (!program->value_types || !program->value_is_tagged
	|| !program->value_ownership || !program->value_use_counts
	|| !program->value_escape_flags || instr->value <= 0
	|| instr->value >= program->num_values
	|| program->value_is_tagged[instr->value]
	|| program->value_types[instr->value] != TYPE_LIST
	|| program->value_ownership[instr->value] != JIT_OWNERSHIP_OWNED
	|| program->value_use_counts[instr->value] != 0
	|| program->value_escape_flags[instr->value] != JIT_ESCAPE_NONE)
	return 0;
    return instr->kind == HIR_TAC_BINARY
	&& (instr->op == HIR_OP_LIST_ADD_TAIL
	    || instr->op == HIR_OP_LIST_APPEND
	    || instr->op == HIR_OP_SUBLIST_FROM);
}

static int
jit_value_is_owned_string_result(JITProgram *program, int value)
{
    JITInstruction *definition;

    if (!program->value_ownership || !program->value_types
	|| !program->value_is_tagged
	|| value <= 0 || value >= program->num_values
	|| program->value_ownership[value] != JIT_OWNERSHIP_OWNED)
	return 0;
    if (!program->value_is_tagged[value])
	return program->value_types[value] == TYPE_STR;
    definition = jit_value_definition(program, value);
    return definition
	&& ((definition->kind == HIR_TAC_BINARY
	     && definition->op == HIR_OP_ADD)
	    || (definition->kind == HIR_TAC_BINARY
		&& definition->op == HIR_OP_INDEX
		&& !program->value_is_tagged[definition->src1]
		&& program->value_types[definition->src1] == TYPE_STR)
	    || (definition->kind == HIR_TAC_RANGE_REF
		&& !program->value_is_tagged[definition->src1]
		&& program->value_types[definition->src1] == TYPE_STR));
}

static int
jit_value_is_owned_list_result(JITProgram *program, int value)
{
    if (!program->value_ownership || !program->value_types
	|| !program->value_is_tagged
	|| value <= 0 || value >= program->num_values
	|| program->value_ownership[value] != JIT_OWNERSHIP_OWNED)
	return 0;
    return !program->value_is_tagged[value]
	&& program->value_types[value] == TYPE_LIST;
}

static int
jit_value_is_owned_index_result(JITProgram *program, int value)
{
    JITInstruction *definition;

    if (!program->value_ownership || value <= 0
	|| value >= program->num_values
	|| program->value_ownership[value] != JIT_OWNERSHIP_OWNED)
	return 0;
    definition = jit_value_definition(program, value);
    return definition && definition->kind == HIR_TAC_BINARY
	&& definition->op == HIR_OP_INDEX;
}

#ifdef JIT_TESTING
int
jit_test_value_is_dead_owned_list(JITProgram *program, JITInstruction *instr)
{
    return jit_value_is_dead_owned_list(program, instr);
}

int
jit_test_value_is_owned_string_result(JITProgram *program, int value)
{
    return jit_value_is_owned_string_result(program, value);
}

int
jit_test_list_tail_consumes_home(JITProgram *program, JITInstruction *instr)
{
    return jit_list_tail_consume_mode(program, instr)
	== JIT_LIST_APPEND_CONSUME_HOME;
}
#endif

static int
jit_owned_alias_root(int *roots, int value)
{
    while (roots[value] != value) {
	roots[value] = roots[roots[value]];
	value = roots[value];
    }
    return value;
}

static void
jit_join_owned_aliases(int *roots, int left, int right)
{
    left = jit_owned_alias_root(roots, left);
    right = jit_owned_alias_root(roots, right);
    if (left != right)
	roots[right] = left;
}

static void
jit_owned_liveness(JITProgram *program, JITInstruction *instr,
		   unsigned char *uses, unsigned char *defs)
{
    JITCopy *copy;
    JITDeoptMap *map;
    int value;

    if (instr->value > 0 && instr->value < program->num_values
	&& (instr->kind == HIR_TAC_CONST
	    || instr->kind == HIR_TAC_LOAD_LOCAL
	    || instr->kind == HIR_TAC_LOAD_ERROR
	    || instr->kind == HIR_TAC_UNARY
	    || instr->kind == HIR_TAC_BINARY
	    || instr->kind == HIR_TAC_CALL
	    || instr->kind == HIR_TAC_CALL_VERB
	    || instr->kind == HIR_TAC_PUT_PROP
	    || instr->kind == HIR_TAC_INDEX_SET
	    || instr->kind == HIR_TAC_RANGE_REF
	    || instr->kind == HIR_TAC_RANGE_SET
	    || instr->kind == HIR_TAC_UNSUPPORTED))
	defs[instr->value] = 1;
    if (instr->kind == HIR_TAC_PARALLEL_COPY)
	for (copy = instr->copies; copy; copy = copy->next) {
	    if (copy->src > 0 && copy->src < program->num_values)
		uses[copy->src] = 1;
	    if (copy->dst > 0 && copy->dst < program->num_values)
		defs[copy->dst] = 1;
	}
    if (instr->src1 > 0 && instr->src1 < program->num_values)
	uses[instr->src1] = 1;
    if (instr->src2 > 0 && instr->src2 < program->num_values)
	uses[instr->src2] = 1;
    if (instr->src3 > 0 && instr->src3 < program->num_values)
	uses[instr->src3] = 1;
    if (instr->deopt_map <= 0
	|| instr->deopt_map >= program->num_deopt_maps)
	return;
    map = &program->deopt_maps[instr->deopt_map];
    for (value = 0; value < map->num_locals; value++) {
	int local = jit_deopt_map_local_value(program, map, value);

	if (local > 0 && local < program->num_values)
	    uses[local] = 1;
    }
    for (value = 0; value < (int) map->stack_depth; value++)
	if ((!map->stack_slots || map->stack_slots[value].kind == RSS_VALUE)
	    && map->stack_values[value] > 0
	    && map->stack_values[value] < program->num_values)
	    uses[map->stack_values[value]] = 1;
}

static int
jit_owned_alias_is_live(JITProgram *program, int *roots,
			unsigned char *owned_roots, unsigned char *live,
			JITInstruction *instr, int source)
{
    int root;
    int value;

    if (source <= 0 || source >= program->num_values)
	return 1;
    root = jit_owned_alias_root(roots, source);
    if (!owned_roots[root])
	return 1;
    if (instr->kind == HIR_TAC_UNARY
	&& instr->op == HIR_OP_CHECK_LIST_FOR_SPLICE
	&& instr->value > 0 && instr->value < program->num_values
	&& live[instr->value]
	&& jit_owned_alias_root(roots, instr->value) == root)
	return 1;
    for (value = 1; value < program->num_values; value++)
	if (live[value] && jit_owned_alias_root(roots, value) == root
	    && (!(instr->value > 0 && instr->value < program->num_values)
		|| value != instr->value))
	    return 1;
    return 0;
}

static int
jit_owned_alias_is_in_deopt_frame(JITProgram *program, JITDeoptMap *map,
				  int *roots, int root, int operand_slot)
{
    int slot;

    for (slot = 0; slot < map->num_locals; slot++) {
	int value = jit_deopt_map_local_value(program, map, slot);

	if (value > 0 && value < program->num_values
	    && jit_owned_alias_root(roots, value) == root)
	    return 1;
    }
    for (slot = 0; slot < (int) map->stack_depth; slot++) {
	int value;

	if (slot == operand_slot)
	    continue;
	if (map->stack_slots && map->stack_slots[slot].kind != RSS_VALUE)
	    continue;
	value = map->stack_values[slot];
	if (value > 0 && value < program->num_values
	    && jit_owned_alias_root(roots, value) == root)
	    return 1;
    }
    return 0;
}

static void
jit_mark_boundary_owned_moves(JITProgram *program, JITInstruction *instr,
			      int *roots, unsigned char *owned_roots,
			      unsigned char *live)
{
    JITDeoptMap *map;
    int first;
    int operands;
    int slot;

    if ((instr->kind != HIR_TAC_CALL && instr->kind != HIR_TAC_CALL_VERB)
	|| instr->deopt_map <= 0
	|| instr->deopt_map >= program->num_deopt_maps)
	return;
    map = &program->deopt_maps[instr->deopt_map];
    operands = jit_call_stack_operands(map);
    if (operands < 0 || (unsigned) operands > map->stack_depth)
	return;
    first = map->stack_depth - operands;
    for (slot = first; slot < (int) map->stack_depth; slot++) {
	var_type type;
	int root;
	int value;

	if (map->stack_slots && map->stack_slots[slot].kind != RSS_VALUE)
	    continue;
	value = map->stack_values[slot];
	if (value <= 0 || value >= program->num_values
	    || program->value_ownership[value] != JIT_OWNERSHIP_OWNED)
	    continue;
	type = program->value_types[value];
	if (instr->kind == HIR_TAC_CALL_VERB
	    && (slot != (int) map->stack_depth - 1 || type != TYPE_LIST))
	    continue;
	if ((!program->value_is_tagged || !program->value_is_tagged[value])
	    && type != TYPE_STR && type != TYPE_LIST
#ifdef WAIF_CORE
	    && type != TYPE_WAIF
#endif
	    )
	    continue;
	root = jit_owned_alias_root(roots, value);
	if (jit_owned_alias_is_live(program, roots, owned_roots, live,
		instr, value)
	    || jit_owned_alias_is_in_deopt_frame(program, map, roots, root,
					  slot))
	    continue;
	if (!map->stack_boundary_ownership) {
	    map->stack_boundary_ownership = mymalloc(map->stack_depth,
					       M_PROGRAM);
	    memset(map->stack_boundary_ownership,
		   JIT_BOUNDARY_VALUE_RETAINED, map->stack_depth);
	}
	map->stack_boundary_ownership[slot] =
	    instr->kind == HIR_TAC_CALL_VERB
	    ? JIT_BOUNDARY_VALUE_RELEASE_AFTER_RESUME
	    : program->value_owned_slots[value] >= 0
	      ? JIT_BOUNDARY_VALUE_MOVED_OWNER : JIT_BOUNDARY_VALUE_MOVED_RAW;
    }
}

void
jit_analyze_owned_last_uses(JITProgram *program)
{
    JITBlock *block;
    unsigned char **live_in, **live_out, **block_use, **block_def;
    unsigned char *owned_roots;
    int *roots;
    int max_block = 0;
    int changed;
    int i;

    if (!program || !program->blocks || program->num_values <= 1
	|| !program->value_ownership)
	return;
    for (i = 0; i < program->num_deopt_maps; i++)
	if (program->deopt_maps[i].stack_boundary_ownership) {
	    myfree(program->deopt_maps[i].stack_boundary_ownership, M_PROGRAM);
	    program->deopt_maps[i].stack_boundary_ownership = 0;
	}
    roots = mymalloc(sizeof(int) * program->num_values, M_PROGRAM);
    owned_roots = mymalloc(program->num_values, M_PROGRAM);
    for (i = 0; i < program->num_values; i++)
	roots[i] = i;
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	if (block->id > max_block)
	    max_block = block->id;
	for (instr = block->first; instr; instr = instr->next) {
	    JITCopy *copy;

	    instr->owned_last_use = JIT_LAST_USE_NONE;
	    /* A copy may select different values on different incoming edges.
	       Joining all of them deliberately over-approximates aliases. */
	    for (copy = instr->copies; copy; copy = copy->next)
		if (copy->src > 0 && copy->src < program->num_values
		    && copy->dst > 0 && copy->dst < program->num_values)
		    jit_join_owned_aliases(roots, copy->src, copy->dst);
	    if (instr->kind == HIR_TAC_UNARY
		&& instr->op == HIR_OP_CHECK_LIST_FOR_SPLICE
		&& instr->src1 > 0 && instr->src1 < program->num_values
		&& instr->value > 0 && instr->value < program->num_values)
		jit_join_owned_aliases(roots, instr->src1, instr->value);
	    if (instr == block->last)
		break;
	}
    }

    for (i = 1; program->value_owner_root && i < program->num_values; i++)
	if ((program->value_ownership[i] == JIT_OWNERSHIP_OWNED
	     || program->value_ownership[i] == JIT_OWNERSHIP_OWNED_PROPERTY)
	    && program->value_owner_root[i] > 0
	    && program->value_owner_root[i] < program->num_values)
	    jit_join_owned_aliases(roots, i, program->value_owner_root[i]);
    memset(owned_roots, 0, program->num_values);
    for (i = 1; i < program->num_values; i++)
	if (program->value_ownership[i] == JIT_OWNERSHIP_OWNED
	    || program->value_ownership[i] == JIT_OWNERSHIP_OWNED_PROPERTY)
	    owned_roots[jit_owned_alias_root(roots, i)] = 1;

    live_in = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    live_out = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    block_use = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    block_def = mymalloc(sizeof(unsigned char *) * (max_block + 1), M_PROGRAM);
    memset(live_in, 0, sizeof(unsigned char *) * (max_block + 1));
    memset(live_out, 0, sizeof(unsigned char *) * (max_block + 1));
    memset(block_use, 0, sizeof(unsigned char *) * (max_block + 1));
    memset(block_def, 0, sizeof(unsigned char *) * (max_block + 1));
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;
	unsigned char *seen_defs;
	unsigned char *uses;
	unsigned char *defs;

	live_in[block->id] = mymalloc(program->num_values, M_PROGRAM);
	live_out[block->id] = mymalloc(program->num_values, M_PROGRAM);
	block_use[block->id] = mymalloc(program->num_values, M_PROGRAM);
	block_def[block->id] = mymalloc(program->num_values, M_PROGRAM);
	seen_defs = mymalloc(program->num_values, M_PROGRAM);
	uses = mymalloc(program->num_values, M_PROGRAM);
	defs = mymalloc(program->num_values, M_PROGRAM);
	memset(live_in[block->id], 0, program->num_values);
	memset(live_out[block->id], 0, program->num_values);
	memset(block_use[block->id], 0, program->num_values);
	memset(block_def[block->id], 0, program->num_values);
	memset(seen_defs, 0, program->num_values);
	for (instr = block->first; instr; instr = instr->next) {
	    int value;

	    memset(uses, 0, program->num_values);
	    memset(defs, 0, program->num_values);
	    jit_owned_liveness(program, instr, uses, defs);
	    for (value = 1; value < program->num_values; value++) {
		if (uses[value] && !seen_defs[value])
		    block_use[block->id][value] = 1;
		if (defs[value]) {
		    seen_defs[value] = 1;
		    block_def[block->id][value] = 1;
		}
	    }
	    if (instr == block->last)
		break;
	}
	myfree(defs, M_PROGRAM);
	myfree(uses, M_PROGRAM);
	myfree(seen_defs, M_PROGRAM);
    }
    do {
	changed = 0;
	for (block = program->blocks; block; block = block->next) {
	    int successor;
	    int value;

	    for (value = 1; value < program->num_values; value++) {
		int out = 0;

		for (successor = 0; successor < block->num_successors;
		     successor++)
		    if (block->successors[successor] >= 0
			&& block->successors[successor] <= max_block
			&& live_in[block->successors[successor]]
			&& live_in[block->successors[successor]][value])
			out = 1;
		if (live_out[block->id][value] != out) {
		    live_out[block->id][value] = out;
		    changed = 1;
		}
		out = block_use[block->id][value]
		    || (out && !block_def[block->id][value]);
		if (live_in[block->id][value] != out) {
		    live_in[block->id][value] = out;
		    changed = 1;
		}
	    }
	}
    } while (changed);

    for (block = program->blocks; block; block = block->next) {
	JITInstruction **instructions;
	JITInstruction *instr;
	unsigned char *live;
	unsigned char *uses;
	unsigned char *defs;
	int count = 0;
	int index;

	for (instr = block->first; instr; instr = instr->next) {
	    count++;
	    if (instr == block->last)
		break;
	}
	instructions = mymalloc(sizeof(JITInstruction *) * count, M_PROGRAM);
	count = 0;
	for (instr = block->first; instr; instr = instr->next) {
	    instructions[count++] = instr;
	    if (instr == block->last)
		break;
	}
	live = mymalloc(program->num_values, M_PROGRAM);
	uses = mymalloc(program->num_values, M_PROGRAM);
	defs = mymalloc(program->num_values, M_PROGRAM);
	memcpy(live, live_out[block->id], program->num_values);
	for (index = count - 1; index >= 0; index--) {
	    int value;

	    instr = instructions[index];
	    jit_mark_boundary_owned_moves(program, instr, roots, owned_roots, live);
	    /* The newly defined value may carry a replacement allocation.  It
	       does not keep the consumed dynamic instance alive. */
	    if (instr->src1 > 0
		&& !jit_owned_alias_is_live(program, roots, owned_roots,
		    live, instr, instr->src1))
		instr->owned_last_use |= JIT_LAST_USE_SRC1;
	    if (instr->src2 > 0
		&& !jit_owned_alias_is_live(program, roots, owned_roots,
		    live, instr, instr->src2))
		instr->owned_last_use |= JIT_LAST_USE_SRC2;
	    if (instr->src3 > 0
		&& !jit_owned_alias_is_live(program, roots, owned_roots,
		    live, instr, instr->src3))
		instr->owned_last_use |= JIT_LAST_USE_SRC3;
	    memset(uses, 0, program->num_values);
	    memset(defs, 0, program->num_values);
	    jit_owned_liveness(program, instr, uses, defs);
	    for (value = 1; value < program->num_values; value++)
		live[value] = uses[value] || (live[value] && !defs[value]);
	}
	myfree(defs, M_PROGRAM);
	myfree(uses, M_PROGRAM);
	myfree(live, M_PROGRAM);
	myfree(instructions, M_PROGRAM);
    }
    for (i = 0; i <= max_block; i++) {
	if (live_in[i]) myfree(live_in[i], M_PROGRAM);
	if (live_out[i]) myfree(live_out[i], M_PROGRAM);
	if (block_use[i]) myfree(block_use[i], M_PROGRAM);
	if (block_def[i]) myfree(block_def[i], M_PROGRAM);
    }
    myfree(block_def, M_PROGRAM);
    myfree(block_use, M_PROGRAM);
    myfree(live_out, M_PROGRAM);
    myfree(live_in, M_PROGRAM);
    myfree(owned_roots, M_PROGRAM);
    myfree(roots, M_PROGRAM);
}

static int
build_mir(JITProgram *program, MIRBuild *build, MIR_context_t context)
{
    MIR_type_t result_type = MIR_T_I64;
    MIR_reg_t env, result, ticks, timed_out, error_out, deopt_map_out;
    MIR_reg_t source_location, deopt_values, progr, resume_map, resume_stack;
    MIR_reg_t continuation_values, owned_values;
    MIR_reg_t tick_result, timeout_value, status;
    MIR_reg_t *values;
    unsigned char *deferred_region_lists;
    MIR_label_t *labels;
    MIR_label_t *resume_entries, *resume_continuations;
    MIR_label_t fallback;
    MIR_label_t tick_abort = 0, seconds_abort = 0;
    MIR_label_t common_return;
    JITStatusExit *status_exits = 0;
    JITStatusExit *last_status_exit = 0;
    JITTickBatchExit *tick_batch_exits = 0;
    JITTickBatchExit *last_tick_batch_exit = 0;
    JITNegativeModExit *negative_mod_exits = 0;
    JITNegativeModExit *last_negative_mod_exit = 0;
    JITBlock *block;
    char module_name[64];
    char func_name[64];
    int max_block_id = 0;
    int copy_serial = 0;
    int source_marker_serial = 0;
    int i;

    memset(build, 0, sizeof(MIRBuild));
    jit_build_constant_values(program);
    if (program->status_locations) {
	myfree(program->status_locations, M_PROGRAM);
	program->status_locations = 0;
    }
    program->num_status_locations = 0;
    build->program = program;
    build->context = context;
    snprintf(module_name, sizeof(module_name), "moo_mod_%" PRIu64, ++next_module_serial);
    build->module = MIR_new_module(build->context, module_name);
    MIR_type_t res_i64 = MIR_T_I64;
    MIR_type_t res_p = MIR_T_P;
    MIR_type_t res_i32 = MIR_T_I32;
    MIR_type_t tag_t = sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32;

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
    build->proto_str_concat_owned = MIR_new_proto(build->context,
	"proto_str_concat_owned", 1, &res_i32, 7, MIR_T_P, "owned_values",
	MIR_T_I32, "owner", MIR_T_P, "s1", MIR_T_P, "s2", MIR_T_I32,
	"last_use", MIR_T_P, "result", MIR_T_P, "err");
    build->import_str_concat_owned = MIR_new_import(build->context,
	"jit_rt_str_concat_owned");

    build->proto_str_ref = MIR_new_proto(build->context, "proto_str_ref", 1, &res_p, 3,
					 MIR_T_P, "s", MIR_T_I64, "idx", MIR_T_P, "err");
    build->import_str_ref = MIR_new_import(build->context, "jit_rt_str_ref");

    build->proto_str_range_ref = MIR_new_proto(build->context, "proto_str_range_ref", 1, &res_p, 4,
					       MIR_T_P, "s", MIR_T_I64, "from", MIR_T_I64, "to", MIR_T_P, "err");
    build->import_str_range_ref = MIR_new_import(build->context, "jit_rt_str_range_ref");

    build->proto_list_range_ref = MIR_new_proto(build->context, "proto_list_range_ref", 1, &res_p, 4,
						MIR_T_P, "l", MIR_T_I64, "from", MIR_T_I64, "to", MIR_T_P, "err");
    build->import_list_range_ref = MIR_new_import(build->context, "jit_rt_list_range_ref");

    build->proto_list_concat = MIR_new_proto(build->context, "proto_list_concat", 1, &res_p, 3,
					     MIR_T_P, "l1", MIR_T_P, "l2", MIR_T_P, "err");
    build->import_list_concat = MIR_new_import(build->context, "jit_rt_list_concat");

    build->proto_singleton_list = MIR_new_proto(build->context, "proto_singleton_list", 1, &res_p, 2,
						MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type");
    build->import_singleton_list = MIR_new_import(build->context, "jit_rt_make_singleton_list");
    build->proto_fixed_list_head = MIR_new_proto(build->context,
	"proto_fixed_list_head", 1, &res_p, 3, MIR_T_I64, "elem_raw",
	MIR_T_I32, "elem_type", MIR_T_I32, "capacity");
    build->import_fixed_list_head = MIR_new_import(build->context,
	"jit_rt_make_fixed_list_head");
    build->proto_empty_list = MIR_new_proto(build->context,
	"proto_empty_list", 1, &res_p, 0);
    build->import_empty_list = MIR_new_import(build->context,
	"jit_rt_make_empty_list");

    build->proto_list_append = MIR_new_proto(build->context, "proto_list_append", 1, &res_p, 3,
					     MIR_T_P, "l", MIR_T_I64, "elem_raw",
					     MIR_T_I32, "elem_type");
    build->import_list_append = MIR_new_import(build->context, "jit_rt_list_append");
    build->proto_list_append_owned = MIR_new_proto(build->context,
	"proto_list_append_owned", 1, &res_p, 6, MIR_T_P, "owned_values",
	MIR_T_P, "home_capacities", MIR_T_I32, "owner", MIR_T_P, "l",
	MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type");
    build->import_list_append_owned = MIR_new_import(build->context,
	"jit_rt_list_append_owned");
    build->proto_fixed_list_append_owned = MIR_new_proto(build->context,
	"proto_fixed_list_append_owned", 1, &res_p, 7, MIR_T_P,
	"owned_values", MIR_T_P, "home_capacities", MIR_T_I32, "owner",
	MIR_T_P, "l", MIR_T_I32, "index", MIR_T_I64, "elem_raw",
	MIR_T_I32, "elem_type");
    build->import_fixed_list_append_owned = MIR_new_import(build->context,
	"jit_rt_fixed_list_append_owned");
    build->proto_fixed_list_store = MIR_new_proto(build->context,
	"proto_fixed_list_store", 1, &res_p, 4, MIR_T_P, "list",
	MIR_T_I32, "index", MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type");
    build->import_fixed_list_store = MIR_new_import(build->context,
	"jit_rt_fixed_list_store");

    build->proto_owned_replace = MIR_new_proto(build->context,
	"proto_owned_replace", 0, 0, 4, MIR_T_P, "owned_values",
	MIR_T_I32, "value", MIR_T_I64, "raw", MIR_T_I32, "type");
    build->import_owned_replace = MIR_new_import(build->context,
	"jit_rt_owned_replace");
    build->proto_owned_move = MIR_new_proto(build->context,
	"proto_owned_move", 0, 0, 3, MIR_T_P, "owned_values",
	MIR_T_I32, "destination", MIR_T_I32, "source");
    build->import_owned_move = MIR_new_import(build->context,
	"jit_rt_owned_move");
    build->proto_discard_owned = MIR_new_proto(build->context,
	"proto_discard_owned", 0, 0, 4, MIR_T_P, "owned_values",
	MIR_T_I32, "owner", MIR_T_I64, "raw", MIR_T_I32, "type");
    build->import_discard_owned = MIR_new_import(build->context,
	"jit_rt_discard_owned");
    build->proto_retain_raw = MIR_new_proto(build->context,
	"proto_retain_raw", 0, 0, 2, MIR_T_I64, "raw", MIR_T_I32, "type");
    build->import_retain_raw = MIR_new_import(build->context,
	"jit_rt_retain_raw");

    build->proto_list_index_set = MIR_new_proto(build->context, "proto_list_index_set", 1, &res_p, 7,
						MIR_T_P, "env", MIR_T_I32, "local", MIR_T_P, "list",
						MIR_T_I64, "index", MIR_T_I64, "value_raw",
						MIR_T_I32, "value_type", MIR_T_P, "err");
    build->import_list_index_set = MIR_new_import(build->context, "jit_rt_list_index_set");

    build->proto_list_nested_index_set = MIR_new_proto(build->context, "proto_list_nested_index_set", 1, &res_p, 7,
						MIR_T_P, "env", MIR_T_I32, "local",
						MIR_T_I64, "outer_index", MIR_T_I64, "inner_index",
						MIR_T_I64, "value_raw", MIR_T_I32, "value_type",
						MIR_T_P, "err");
    build->import_list_nested_index_set = MIR_new_import(build->context, "jit_rt_list_nested_index_set");

    build->proto_sublist_from = MIR_new_proto(build->context, "proto_sublist_from", 1, &res_p, 2,
					     MIR_T_P, "list", MIR_T_I64, "start");
    build->import_sublist_from = MIR_new_import(build->context, "jit_rt_sublist_from");

    build->proto_list_in = MIR_new_proto(build->context, "proto_list_in", 1, &res_i64, 3,
					 MIR_T_I64, "elem_raw", MIR_T_I32, "elem_type", MIR_T_P, "l");
    build->import_list_in = MIR_new_import(build->context, "jit_rt_list_in");

    build->proto_region_guard = MIR_new_proto(build->context,
	"proto_region_guard", 1, &res_i64, 4, MIR_T_I64, "receiver_raw",
	MIR_T_I32, "receiver_type", MIR_T_I64, "receiver_class",
	MIR_T_I64, "dispatch_epoch");
    build->import_region_guard = MIR_new_import(build->context,
	"jit_rt_region_guard");

    build->proto_get_prop = MIR_new_proto(build->context, "proto_get_prop", 1, &res_i32, 7,
					  MIR_T_I64, "receiver", MIR_T_I32, "receiver_type",
					  MIR_T_P, "pname", MIR_T_I64, "progr",
					  MIR_T_P, "out_raw", MIR_T_P, "out_type", MIR_T_P, "err");
    build->import_get_prop = MIR_new_import(build->context,
					    "jit_rt_get_prop_typed");
    build->proto_get_prop_int = MIR_new_proto(build->context,
	"proto_get_prop_int", 1, &res_i64, 5, MIR_T_I64, "receiver",
	MIR_T_I32, "receiver_type", MIR_T_P, "pname", MIR_T_I64, "progr",
	MIR_T_P, "err");
    build->import_get_prop_int = MIR_new_import(build->context,
	"jit_rt_get_prop_int");

    build->proto_put_prop = MIR_new_proto(build->context, "proto_put_prop", 1, &res_i32, 6,
					  MIR_T_I64, "oid", MIR_T_P, "pname", MIR_T_I64, "progr",
					  MIR_T_I64, "rhs_raw", MIR_T_I32, "rhs_type", MIR_T_P, "err");
    build->import_put_prop = MIR_new_import(build->context, "jit_rt_put_prop");

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

    build->proto_var_raw = MIR_new_proto(build->context, "proto_var_raw", 1,
					 &res_i64, 1, MIR_T_P, "value");
    build->import_var_raw = MIR_new_import(build->context, "jit_rt_var_raw");

    if (program->diagnostic_object >= 0 && program->diagnostic_verb > 0)
	snprintf(func_name, sizeof(func_name), "jit_o%" PRIdN "_v%u_%" PRIu64,
		 program->diagnostic_object, program->diagnostic_verb,
		 next_module_serial);
    else
	snprintf(func_name, sizeof(func_name), "jit_verb_%" PRIu64,
		 next_module_serial);
    build->function = MIR_new_func(build->context, func_name, 1,
				   &result_type, 15,
				   MIR_T_P, "execution_context",
				   MIR_T_P, "native_frame",
				   MIR_T_P, "env", MIR_T_P, "result",
				   MIR_T_P, "ticks", MIR_T_P, "timed_out",
				   MIR_T_P, "error_out", MIR_T_P, "source_location",
				   MIR_T_P, "deopt_map_out", MIR_T_P, "deopt_values",
				   MIR_T_I64, "progr", MIR_T_I32, "resume_map",
				   MIR_T_P, "resume_stack",
				   MIR_T_P, "continuation_values",
				   MIR_T_P, "owned_values");
    build->execution_context = MIR_reg(build->context, "execution_context",
				       build->function->u.func);
    build->native_frame = MIR_reg(build->context, "native_frame",
				  build->function->u.func);
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
    resume_map = MIR_reg(build->context, "resume_map", build->function->u.func);
    resume_stack = MIR_reg(build->context, "resume_stack", build->function->u.func);
    continuation_values = MIR_reg(build->context, "continuation_values",
				  build->function->u.func);
    owned_values = MIR_reg(build->context, "owned_values",
			  build->function->u.func);
    build->owned_values = owned_values;
    build->home_capacities = new_reg(build, "home_capacities");
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_reg_op(build->context, build->home_capacities),
	MIR_new_mem_op(build->context, MIR_T_P,
	    offsetof(JITNativeFrame, home_capacities), build->native_frame, 0, 1)));
    tick_result = new_reg(build, "tick_result");
    timeout_value = new_reg(build, "timeout_value");
    status = new_reg(build, "status");
    fallback = MIR_new_label(build->context);
    common_return = MIR_new_label(build->context);

    values = mymalloc(sizeof(MIR_reg_t) * program->num_values, M_PROGRAM);
    memset(values, 0, sizeof(MIR_reg_t) * program->num_values);
    deferred_region_lists = mymalloc(program->num_values, M_PROGRAM);
    memset(deferred_region_lists, 0, program->num_values);
    for (i = 1; i < program->num_values; i++) {
	char name[32];
	sprintf(name, "v%d", i);
	if (program->value_types && program->value_types[i] == TYPE_FLOAT
	    && !(program->value_is_tagged && program->value_is_tagged[i]))
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

    resume_entries = mymalloc(sizeof(MIR_label_t) * program->num_deopt_maps,
			      M_PROGRAM);
    resume_continuations = mymalloc(sizeof(MIR_label_t)
				    * program->num_deopt_maps, M_PROGRAM);
    memset(resume_entries, 0,
	   sizeof(MIR_label_t) * program->num_deopt_maps);
    memset(resume_continuations, 0,
	   sizeof(MIR_label_t) * program->num_deopt_maps);

    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_reg_op(build->context, tick_result),
	MIR_new_mem_op(build->context, MIR_T_I32, 0, ticks, 0, 1)));
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->deopt_map > 0
		&& instr->deopt_map < program->num_deopt_maps
		&& (instr->kind == HIR_TAC_CALL_VERB
		 || jit_deopt_map_bridges_builtin(
		     &program->deopt_maps[instr->deopt_map]))
		&& jit_call_has_native_continuation(program, instr)
		&& program->deopt_maps[instr->deopt_map].stack_depth
		   >= (unsigned) jit_call_stack_operands(
		       &program->deopt_maps[instr->deopt_map])) {
		resume_entries[instr->deopt_map] = MIR_new_label(build->context);
		resume_continuations[instr->deopt_map] = MIR_new_label(build->context);
	    }
	    if (instr == block->last)
		break;
	}
    }
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_CALL_VERB && instr->deopt_map > 0
		&& instr->deopt_map < program->num_deopt_maps
		&& resume_continuations[instr->deopt_map]) {
		JITInstruction *tail;

		tail = jit_region_deferred_list_tail(program, instr);
		if (tail && jit_region_cfg_call_supported(program, instr))
		    deferred_region_lists[tail->value] = 1;
	    }
	    if (instr == block->last)
		break;
	}
    }
    for (i = 1; i < program->num_deopt_maps; i++)
	if (resume_entries[i])
	    append(build, MIR_new_insn(build->context, MIR_BEQ,
		MIR_new_label_op(build->context, resume_entries[i]),
		MIR_new_reg_op(build->context, resume_map),
		MIR_new_int_op(build->context, i)));
    if (program->blocks)
	append(build, MIR_new_insn(build->context, MIR_JMP,
				  MIR_new_label_op(build->context,
						   labels[program->blocks->id])));
    else
	append(build, MIR_new_insn(build->context, MIR_JMP,
				  MIR_new_label_op(build->context, fallback)));
    for (i = 1; i < program->num_deopt_maps; i++) {
	JITDeoptMap *map;
	int j, outer_depth;
	MIR_label_t compact, values_loaded;

	if (!resume_entries[i])
	    continue;
	map = &program->deopt_maps[i];
	outer_depth = map->stack_depth - jit_call_stack_operands(map);
	compact = MIR_new_label(build->context);
	values_loaded = MIR_new_label(build->context);
	append(build, resume_entries[i]);
	append(build, MIR_new_insn(build->context, MIR_BNE,
				  MIR_new_label_op(build->context, compact),
				  MIR_new_reg_op(build->context,
						 continuation_values),
				  MIR_new_int_op(build->context, 0)));
	for (j = 0; map->native_resume
	     && j < map->native_resume->num_values; j++)
	    if (map->native_resume->values[j].source == JIT_RESUME_OWNER) {
		append(build, MIR_new_insn(build->context, MIR_JMP,
					  MIR_new_label_op(build->context,
							   fallback)));
		break;
	    }
	for (j = 0; map->native_resume
	     && j < map->native_resume->num_values; j++) {
	    JITResumeValue *resume = &map->native_resume->values[j];

	    if (resume->source == JIT_RESUME_LOCAL
		|| resume->source == JIT_RESUME_BORROWED_LOCAL)
		append_resume_value(build, program, values, resume->value, env,
				    resume->index, deopt_values, &copy_serial);
	    else if (resume->source == JIT_RESUME_STACK)
		append_resume_value(build, program, values, resume->value,
				    resume_stack, resume->index, deopt_values,
				    &copy_serial);
	    else if (resume->source == JIT_RESUME_RESULT)
		append_resume_value(build, program, values, resume->value,
				    resume_stack, outer_depth, deopt_values,
				    &copy_serial);
	}
	append(build, MIR_new_insn(build->context, MIR_JMP,
				  MIR_new_label_op(build->context, values_loaded)));
	append(build, compact);
	for (j = 0; map->native_resume
	     && j < map->native_resume->num_values; j++) {
	    JITResumeValue *resume = &map->native_resume->values[j];

	    if (resume->source == JIT_RESUME_RESULT)
		append_resume_value(build, program, values, resume->value,
				    continuation_values, 0, deopt_values,
				    &copy_serial);
	    else if (resume->source == JIT_RESUME_OWNER)
		append_resume_value(build, program, values, resume->value,
				    owned_values, resume->index, deopt_values,
				    &copy_serial);
	    else if (resume->source != JIT_RESUME_CONSTANT
		     && resume->source != JIT_RESUME_OPERAND)
		append_stored_resume_value(build, program, values,
		    resume->value, deopt_values);
	}
	for (j = 0; map->stack_boundary_ownership
	     && j < (int) map->stack_depth; j++)
	    if (map->stack_boundary_ownership[j]
		== JIT_BOUNDARY_VALUE_RELEASE_AFTER_RESUME) {
		int value = map->stack_values[j];
		int owner = map->stack_owner_slots
		    ? map->stack_owner_slots[j] : -1;
		MIR_reg_t raw = append_raw_value(build, program, values, value,
		    deopt_values, &copy_serial);

		append(build, MIR_new_call_insn(build->context, 6,
		    MIR_new_ref_op(build->context, build->proto_discard_owned),
		    MIR_new_ref_op(build->context, build->import_discard_owned),
		    MIR_new_reg_op(build->context, owned_values),
		    MIR_new_int_op(build->context, owner),
		    MIR_new_reg_op(build->context, raw),
		    MIR_new_int_op(build->context, TYPE_LIST)));
	    }
	append(build, values_loaded);
	for (j = 0; map->native_resume
	     && j < map->native_resume->num_values; j++) {
	    JITResumeValue *resume = &map->native_resume->values[j];

	    if (resume->source == JIT_RESUME_CONSTANT) {
		JITResumeLiteral *literal = &map->native_resume->literals[
		    resume->index];

		if (program->value_types[resume->value] == TYPE_FLOAT
		    && !(program->value_is_tagged && program->value_is_tagged[resume->value])) {
		    double d = raw_to_double(literal->literal);
		    append(build, MIR_new_insn(build->context, MIR_DMOV,
			MIR_new_reg_op(build->context, values[resume->value]),
			MIR_new_double_op(build->context, d)));
		} else
		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_reg_op(build->context, values[resume->value]),
			MIR_new_int_op(build->context, literal->literal)));
		if (program->value_is_tagged[resume->value])
		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_mem_op(build->context,
			    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
			    jit_tag_offset(program, resume->value),
			    deopt_values, 0, 1),
			    MIR_new_int_op(build->context,
				literal->literal_type)));
	    }
	}
	append(build, MIR_new_insn(build->context, MIR_JMP,
				  MIR_new_label_op(build->context,
						   resume_continuations[i])));
    }

    for (block = program->blocks; block; block = block->next) {
	    JITInstruction *instr;
	    int ticks_since_timeout_check = 0;

	    append(build, labels[block->id]);
	    for (instr = block->first; instr; instr = instr->next) {
		if (instr->value > 0 && instr->value < program->num_values
		    && deferred_region_lists[instr->value]) {
		    if (instr == block->last)
			break;
		    continue;
		}
		append_source_marker(build, instr, &source_marker_serial);
		switch (instr->kind) {
		case HIR_TAC_LOAD_ERROR:
		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_reg_op(build->context, values[instr->value]),
			MIR_new_mem_op(build->context, MIR_T_I32,
				       0, error_out, 0, 1)));
		    break;
		case HIR_TAC_TICK:
		    if (instr->tick_batch_count == (unsigned char) -1)
			break;
		    if (instr->tick_batch_count > 1) {
			JITTickBatchExit *batch_exit
			    = mymalloc(sizeof(JITTickBatchExit), M_PROGRAM);

			tick_abort = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ABORT_TICKS, E_NONE,
			    -1, instr->bytecode_pc, instr->source_lineno);
			seconds_abort = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ABORT_SECONDS, E_NONE,
			    -1, instr->bytecode_pc, instr->source_lineno);
			batch_exit->label = MIR_new_label(build->context);
			batch_exit->tick_abort = tick_abort;
			batch_exit->seconds_abort = seconds_abort;
			batch_exit->next = 0;
			if (last_tick_batch_exit)
			    last_tick_batch_exit->next = batch_exit;
			else
			    tick_batch_exits = batch_exit;
			last_tick_batch_exit = batch_exit;
			if (!ticks_since_timeout_check)
			    append(build, MIR_new_insn(build->context, MIR_BT,
				MIR_new_label_op(build->context, batch_exit->label),
				MIR_new_mem_op(build->context, MIR_T_I32, 0,
				    timed_out, 0, 1)));
			append(build, MIR_new_insn(build->context, MIR_BLE,
			    MIR_new_label_op(build->context, batch_exit->label),
			    MIR_new_reg_op(build->context, tick_result),
			    MIR_new_int_op(build->context,
				instr->tick_batch_count)));
			append(build, MIR_new_insn(build->context, MIR_SUB,
			    MIR_new_reg_op(build->context, tick_result),
			    MIR_new_reg_op(build->context, tick_result),
			    MIR_new_int_op(build->context,
				instr->tick_batch_count)));
			ticks_since_timeout_check += instr->tick_batch_count;
			if (ticks_since_timeout_check
			    >= JIT_TIMEOUT_CHECK_TICK_INTERVAL)
			    ticks_since_timeout_check = 0;
			break;
		    }
		    if (instr->op != HIR_OP_CHARGE_TICK) {
			tick_abort = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ABORT_TICKS, E_NONE,
			    -1, instr->bytecode_pc, instr->source_lineno);
			seconds_abort = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ABORT_SECONDS, E_NONE,
			    -1, instr->bytecode_pc, instr->source_lineno);
		    }
		    append(build, MIR_new_insn(build->context, MIR_SUB,
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_int_op(build->context,
							instr->tick_batch_count
							? instr->tick_batch_count : 1)));
		    if (instr->op == HIR_OP_CHARGE_TICK)
			break;
		    append(build, MIR_new_insn(build->context, MIR_BLE,
						  MIR_new_label_op(build->context,
								   tick_abort),
						  MIR_new_reg_op(build->context,
								 tick_result),
						  MIR_new_int_op(build->context, 0)));
		    if (!ticks_since_timeout_check) {
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, timeout_value),
			    MIR_new_mem_op(build->context, MIR_T_I32, 0,
				timed_out, 0, 1)));
			append(build, MIR_new_insn(build->context, MIR_BT,
			    MIR_new_label_op(build->context, seconds_abort),
			    MIR_new_reg_op(build->context, timeout_value)));
		    }
		    ticks_since_timeout_check += instr->tick_batch_count
			? instr->tick_batch_count : 1;
		    if (ticks_since_timeout_check
			>= JIT_TIMEOUT_CHECK_TICK_INTERVAL)
			ticks_since_timeout_check = 0;
		    break;
		case HIR_TAC_DEOPT:
		    append_deopt_exit(build, program, instr, values,
			deopt_map_out, deopt_values, status, common_return);
		    break;
		case HIR_TAC_GUARD_TYPE:
		    {
			MIR_label_t deopt = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);
			int operand;
			int guard_values[JIT_MAX_GUARD_OPERANDS] = {
			    instr->src1, instr->src2
			};

			for (operand = 0; operand < JIT_MAX_GUARD_OPERANDS;
			     operand++)
			    if (instr->guarded_operands & (1U << operand)) {
				MIR_reg_t actual_type;
				MIR_label_t accepted = MIR_new_label(build->context);
				char name[32];
				int type;

				assert(guard_values[operand] > 0
				       && guard_values[operand] < program->num_values);
				assert(program->value_is_tagged[guard_values[operand]]);
				assert(instr->guarded_type_masks[operand]);
				sprintf(name, "guard_type%d", copy_serial++);
				actual_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, actual_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, guard_values[operand]),
					deopt_values, 0, 1)));
				for (type = 0; type <= TYPE_DB_MASK; type++)
				    if (instr->guarded_type_masks[operand]
					& JIT_TYPE_MASK(type))
					append(build, MIR_new_insn(build->context,
					    MIR_BEQ,
					    MIR_new_label_op(build->context, accepted),
					    MIR_new_reg_op(build->context, actual_type),
					    MIR_new_int_op(build->context,
						jit_runtime_type_from_db_type(
						    (var_type) type))));
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, deopt)));
				append(build, accepted);
			    }
			append(build, MIR_new_insn(build->context, MIR_JMP,
			    MIR_new_label_op(build->context, done)));
			append(build, deopt);
			append_deopt_exit(build, program, instr, values,
			    deopt_map_out, deopt_values, status, common_return);
			append(build, done);
		    }
		    break;
		case HIR_TAC_CONST:
		    if (program->value_types
			&& program->value_types[instr->value] == TYPE_FLOAT
			&& !(program->value_is_tagged && program->value_is_tagged[instr->value])) {
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
				jit_tag_offset(program, instr->value),
				deopt_values, 0, 1),
			    MIR_new_int_op(build->context, instr->literal_type)));
		    }
		    break;
		case HIR_TAC_LOAD_LOCAL:
		    {
			var_type expected_type = instr->literal_type;
			int tagged = program->value_is_tagged
			    && program->value_is_tagged[instr->value];
			MIR_label_t deopt = tagged ? 0
			    : MIR_new_label(build->context);
			MIR_label_t loaded = tagged ? 0
			    : MIR_new_label(build->context);
			char name[32];
			sprintf(name, "var_type%d", copy_serial++);
			MIR_reg_t var_type = new_reg(build, name);

			append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, var_type),
				MIR_new_mem_op(build->context, MIR_T_I32,
					instr->local_id * sizeof(Var)
					+ offsetof(Var, type), env, 0, 1)));
			if (tagged) {
			    MIR_reg_t address;

			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
				    deopt_values, 0, 1),
				MIR_new_reg_op(build->context, var_type)));
			    sprintf(name, "local_addr%d", copy_serial++);
			    address = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, address),
				MIR_new_reg_op(build->context, env),
				MIR_new_int_op(build->context,
				    instr->local_id * sizeof(Var))));
			    append(build, MIR_new_call_insn(build->context, 4,
				MIR_new_ref_op(build->context, build->proto_var_raw),
				MIR_new_ref_op(build->context, build->import_var_raw),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, address)));
			} else
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, var_type),
				MIR_new_int_op(build->context, expected_type)));
			if (tagged) {
			    /* The helper loaded the tagged representation above. */
			} else if (expected_type == TYPE_NONE) {
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
			if (!tagged) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, loaded)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status,
				common_return);
			    append(build, loaded);
			}
		    }
		    break;
		case HIR_TAC_UNARY:
		    if (instr->deopt_map > 0
			&& instr->deopt_map < program->num_deopt_maps
			&& jit_deopt_map_bridges_builtin(
			    &program->deopt_maps[instr->deopt_map])) {
			append_materialized_exit(build, program, instr->deopt_map,
			 values, deopt_map_out, deopt_values, status,
			 common_return, JIT_RUN_CALL_VERB);
			if (resume_continuations[instr->deopt_map])
			    append(build, resume_continuations[instr->deopt_map]);
			break;
		    }
		    if (instr->kind == HIR_TAC_DEOPT) {
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->op == HIR_OP_MAKE_SINGLETON_LIST) {
			char name[32];
			MIR_reg_t raw_value;
			int fixed_capacity = jit_fixed_list_capacity(program,
			    instr);
			sprintf(name, "sing_elem_type%d", copy_serial++);
			MIR_reg_t type_reg = new_reg(build, name);
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src1),
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
			raw_value = append_raw_value(build, program, values,
				instr->src1, deopt_values, &copy_serial);
			if (fixed_capacity > 1)
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context,
				    build->proto_fixed_list_head),
				MIR_new_ref_op(build->context,
				    build->import_fixed_list_head),
				MIR_new_reg_op(build->context,
				    values[instr->value]),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_int_op(build->context,
				    fixed_capacity)));
			else
			    append(build, MIR_new_call_insn(build->context, 5,
				MIR_new_ref_op(build->context,
				    build->proto_singleton_list),
				MIR_new_ref_op(build->context,
				    build->import_singleton_list),
				MIR_new_reg_op(build->context,
				    values[instr->value]),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, type_reg)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
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
				    jit_tag_offset(program, instr->src1),
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
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
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
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			} else {
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status, common_return);
			}
			break;
		    }
		    if (instr->op == HIR_OP_TICKS_LEFT) {
			append(build, MIR_new_insn(build->context, MIR_MOV,
					  MIR_new_reg_op(build->context,
							 values[instr->value]),
					  MIR_new_reg_op(build->context,
							 tick_result)));
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
			int operand_is_obj = program->value_types
			    && program->value_types[instr->src1] == TYPE_OBJ;
			int operand_tagged = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];

			if (operand_is_obj || operand_tagged) {
			    if (operand_tagged) {
				char name[32];
				MIR_reg_t operand_type;
				MIR_label_t operand_ok = MIR_new_label(build->context);

				sprintf(name, "valid_type%d", copy_serial++);
				operand_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, operand_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BEQ,
				    MIR_new_label_op(build->context, operand_ok),
				    MIR_new_reg_op(build->context, operand_type),
				    MIR_new_int_op(build->context, TYPE_OBJ)));
			    append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, operand_ok);
			    }
			    append(build, MIR_new_call_insn(build->context, 4,
				MIR_new_ref_op(build->context, build->proto_valid),
				MIR_new_ref_op(build->context, build->import_valid),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->src1])));
			    break;
			}
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    } else if (instr->op == HIR_OP_PARENT) {
			int operand_is_obj = program->value_types
			    && program->value_types[instr->src1] == TYPE_OBJ;
			int operand_tagged = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];

			if (operand_is_obj || operand_tagged) {
			    char name[32];
			    if (operand_tagged) {
				MIR_reg_t operand_type;
				MIR_label_t operand_ok = MIR_new_label(build->context);

				sprintf(name, "parent_type%d", copy_serial++);
				operand_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, operand_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BEQ,
				    MIR_new_label_op(build->context, operand_ok),
				    MIR_new_reg_op(build->context, operand_type),
				    MIR_new_int_op(build->context, TYPE_OBJ)));
			    append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, operand_ok);
			    }
			    sprintf(name, "parent_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t invalid_arg = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_INVARG,
				instr->deopt_map, instr->bytecode_pc,
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
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_OBJ)));
			    break;
			}
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    } else if (instr->op == HIR_OP_TOINT) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			if (val_fl || src_fl) {
			    append_deopt_exit(build, program, instr,
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
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src1),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_AND,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_int_op(build->context, TYPE_DB_MASK)));
			} else
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_int_op(build->context,
					       instr->literal & TYPE_DB_MASK)));
		    } else if (instr->op == HIR_OP_ABS) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			int tagged_src = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int check_src = tagged_src
			    && !(instr->guarded_operands & 1U);
			MIR_label_t deopt = 0;
			MIR_label_t done = 0;
			if (check_src) {
			    char name[32];
			    MIR_reg_t type;

			    sprintf(name, "abs_type%d", copy_serial++);
			    type = new_reg(build, name);
			    deopt = MIR_new_label(build->context);
			    done = MIR_new_label(build->context);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src1),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, type),
				MIR_new_int_op(build->context, TYPE_INT)));
			}
			if (val_fl != src_fl) {
			    append_deopt_exit(build, program, instr,
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
			if (tagged_src) {
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    if (check_src) {
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));
				append(build, deopt);
				append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, done);
			    }
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
			    && program->value_is_tagged[instr->src1]
			    && (instr->guarded_operands & 1U)) {
			    if (instr->guarded_type_masks[0]
				== JIT_TYPE_MASK(TYPE_STR))
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, is_str)));
			    else if (instr->guarded_type_masks[0]
				     == JIT_TYPE_MASK(TYPE_LIST))
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, is_list)));
			    else {
				char name[32];
				MIR_reg_t tag;

				sprintf(name, "len_dispatch%d", copy_serial++);
				tag = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, tag),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BEQ,
				    MIR_new_label_op(build->context, is_str),
				    MIR_new_reg_op(build->context, tag),
				    MIR_new_int_op(build->context, TYPE_STR)));
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, is_list)));
			    }
			} else if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    char name[32];
			    sprintf(name, "len_tag%d", copy_serial++);
			    MIR_reg_t tag = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, tag),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src1),
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
			append(build, MIR_new_insn(build->context, MIR_JMP,
						  MIR_new_label_op(build->context, loaded)));
			append(build, deopt);
		    append_deopt_exit(build, program, instr, values,
					  deopt_map_out, deopt_values, status, common_return);
			append(build, loaded);
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			}
		    } else if (instr->op == HIR_OP_NEGATE) {
			int val_fl = program->value_types
			    && program->value_types[instr->value] == TYPE_FLOAT;
			int src_fl = program->value_types
			    && program->value_types[instr->src1] == TYPE_FLOAT;
			if (val_fl != src_fl) {
			    append_deopt_exit(build, program, instr,
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
			    append_deopt_exit(build, program, instr,
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
				    jit_tag_offset(program, instr->src1),
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
					jit_tag_offset(program, instr->value),
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
			    append_deopt_exit(build, program, instr,
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
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			}
		    }
		    break;
		case HIR_TAC_BINARY:
		    if (instr->deopt_map > 0
			&& instr->deopt_map < program->num_deopt_maps
			&& jit_deopt_map_bridges_builtin(
			    &program->deopt_maps[instr->deopt_map])) {
			append_materialized_exit(build, program, instr->deopt_map,
			 values, deopt_map_out, deopt_values, status,
			 common_return, JIT_RUN_CALL_VERB);
			if (resume_continuations[instr->deopt_map])
			    append(build, resume_continuations[instr->deopt_map]);
			break;
		    }
		    if (instr->kind == HIR_TAC_DEOPT) {
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->range_increment) {
			MIR_label_t increment = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);

			append(build, MIR_new_insn(build->context, MIR_BNE,
			    MIR_new_label_op(build->context, increment),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_int_op(build->context, NUM_MAX)));
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1])));
			append(build, MIR_new_insn(build->context, MIR_JMP,
			    MIR_new_label_op(build->context, done)));
			append(build, increment);
			append(build, MIR_new_insn(build->context, MIR_ADD,
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, values[instr->src2])));
			append(build, done);
			break;
		    }
		    if (instr->op == HIR_OP_LIST_ADD_TAIL) {
			char name[32];
			MIR_reg_t raw_value;
			JITListAppendMode consume_mode =
			    jit_list_tail_consume_mode(program, instr);
			int fixed_index = jit_fixed_list_tail_index(program, instr);
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
				    jit_tag_offset(program, instr->src1),
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
				    jit_tag_offset(program, instr->src2),
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
			raw_value = append_raw_value(build, program, values,
				instr->src2, deopt_values, &copy_serial);
			if (consume_mode == JIT_LIST_APPEND_CONSUME_HOME
			    && fixed_index > 0
			    && program->value_types && instr->src2 > 0
			    && instr->src2 < program->num_values
			    && !(program->value_is_tagged
				 && program->value_is_tagged[instr->src2])
			    && program->value_types[instr->src2] == TYPE_INT
			    && jit_fixed_list_tail_has_fresh_capacity(program,
				instr)) {
			    MIR_reg_t list = values[instr->src1];

			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context,
				    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				    fixed_index * sizeof(Var) + offsetof(Var, v.num),
				    list, 0, 1),
				MIR_new_reg_op(build->context, raw_value)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, MIR_T_I32,
				    fixed_index * sizeof(Var) + offsetof(Var, type),
				    list, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context,
				    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				    offsetof(Var, v.num), list, 0, 1),
				MIR_new_int_op(build->context, fixed_index)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, list)));
			} else if (consume_mode == JIT_LIST_APPEND_CONSUME_HOME
			    && fixed_index > 0
			    && program->value_types && instr->src2 > 0
			    && instr->src2 < program->num_values
			    && !(program->value_is_tagged
				 && program->value_is_tagged[instr->src2])
			    && program->value_types[instr->src2] == TYPE_INT) {
			    MIR_reg_t list = values[instr->src1];
			    MIR_reg_t capacity;
			    MIR_label_t slow = MIR_new_label(build->context);
			    MIR_label_t appended = MIR_new_label(build->context);

			    sprintf(name, "tail_capacity%d", copy_serial++);
			    capacity = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, capacity),
				MIR_new_mem_op(build->context, MIR_T_I32,
				    program->value_owned_slots[instr->src1]
					* sizeof(unsigned),
				    build->home_capacities, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BLT,
				MIR_new_label_op(build->context, slow),
				MIR_new_reg_op(build->context, capacity),
				MIR_new_int_op(build->context, fixed_index)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context,
				    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				    fixed_index * sizeof(Var) + offsetof(Var, v.num),
				    list, 0, 1),
				MIR_new_reg_op(build->context, raw_value)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, MIR_T_I32,
				    fixed_index * sizeof(Var) + offsetof(Var, type),
				    list, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context,
				    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				    offsetof(Var, v.num), list, 0, 1),
				MIR_new_int_op(build->context, fixed_index)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, list)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, appended)));
			    append(build, slow);
			    append(build, MIR_new_call_insn(build->context, 10,
				MIR_new_ref_op(build->context,
				    build->proto_fixed_list_append_owned),
				MIR_new_ref_op(build->context,
				    build->import_fixed_list_append_owned),
				MIR_new_reg_op(build->context,
				    values[instr->value]),
				MIR_new_reg_op(build->context, owned_values),
				MIR_new_reg_op(build->context,
				    build->home_capacities),
				MIR_new_int_op(build->context,
				    program->value_owned_slots[instr->src1]),
				MIR_new_reg_op(build->context,
				    values[instr->src1]),
				MIR_new_int_op(build->context, fixed_index),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, type_reg)));
			    append(build, appended);
			} else if (consume_mode == JIT_LIST_APPEND_CONSUME_HOME
			    && fixed_index > 0)
			    append(build, MIR_new_call_insn(build->context, 10,
				MIR_new_ref_op(build->context,
				    build->proto_fixed_list_append_owned),
				MIR_new_ref_op(build->context,
				    build->import_fixed_list_append_owned),
				MIR_new_reg_op(build->context,
				    values[instr->value]),
				MIR_new_reg_op(build->context, owned_values),
				MIR_new_reg_op(build->context,
				    build->home_capacities),
				MIR_new_int_op(build->context,
				    program->value_owned_slots[instr->src1]),
				MIR_new_reg_op(build->context,
				    values[instr->src1]),
				MIR_new_int_op(build->context, fixed_index),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, type_reg)));
			else if (consume_mode == JIT_LIST_APPEND_CONSUME_HOME)
			    append(build, MIR_new_call_insn(build->context, 9,
				MIR_new_ref_op(build->context,
				    build->proto_list_append_owned),
				MIR_new_ref_op(build->context,
				    build->import_list_append_owned),
				MIR_new_reg_op(build->context,
				    values[instr->value]),
				MIR_new_reg_op(build->context, owned_values),
				MIR_new_reg_op(build->context,
				    build->home_capacities),
				MIR_new_int_op(build->context,
				    program->value_owned_slots[instr->src1]),
				MIR_new_reg_op(build->context,
				    values[instr->src1]),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, type_reg)));
			else
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context,
				    build->proto_list_append),
				MIR_new_ref_op(build->context,
				    build->import_list_append),
				MIR_new_reg_op(build->context,
				    values[instr->value]),
				MIR_new_reg_op(build->context,
				    values[instr->src1]),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, type_reg)));
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value]) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			if (tagged_list) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status,
				common_return);
			    append(build, done);
			}
			break;
		    }
		    if (instr->op == HIR_OP_GET_PROP) {
			int obj_tagged = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int obj_is_obj = !obj_tagged && program->value_types
			    && program->value_types[instr->src1] == TYPE_OBJ;
			int obj_is_waif = !obj_tagged && program->value_types
			    && program->value_types[instr->src1] == TYPE_WAIF;
			int receiver_has_home =
			    jit_resolve_owner_slot(program, instr->src1) >= 0;

			/* An owned home may alias a complex receiver across a
			   continuation; keep that path canonical until the home can
			   be transferred with the receiver. */
			if ((obj_is_obj
			     || ((obj_is_waif || obj_tagged) && !receiver_has_home))
			    && !(program->value_is_tagged
				 && program->value_is_tagged[instr->src2])
			    && program->value_types
			    && program->value_types[instr->src2] == TYPE_STR) {
			    char name[32];
			    sprintf(name, "prop_ok%d", copy_serial++);
			    MIR_reg_t prop_ok = new_reg(build, name);
			    MIR_reg_t receiver_type;
			    sprintf(name, "out_raw_ptr%d", copy_serial++);
			    MIR_reg_t out_raw_ptr = new_reg(build, name);
			    sprintf(name, "out_type_ptr%d", copy_serial++);
			    MIR_reg_t out_type_ptr = new_reg(build, name);
			    MIR_label_t prop_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_NONE,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);

			    sprintf(name, "receiver_type%d", copy_serial++);
			    receiver_type = new_reg(build, name);
			    if (obj_tagged) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, receiver_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
			    }
			    else
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, receiver_type),
				    MIR_new_int_op(build->context,
					program->value_types[instr->src1])));
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, out_raw_ptr),
				MIR_new_reg_op(build->context, deopt_values),
				MIR_new_int_op(build->context, instr->value * sizeof(Num))));
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, out_type_ptr),
				MIR_new_reg_op(build->context, deopt_values),
				MIR_new_int_op(build->context, jit_tag_offset(program, instr->value))));
			    append(build, MIR_new_call_insn(build->context, 10,
				MIR_new_ref_op(build->context, build->proto_get_prop),
				MIR_new_ref_op(build->context, build->import_get_prop),
				MIR_new_reg_op(build->context, prop_ok),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, receiver_type),
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
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (instr->op == HIR_OP_SUBLIST_FROM) {
			int tagged_list = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_start = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			MIR_label_t deopt = 0;
			MIR_label_t done = 0;

			if (tagged_list || tagged_start) {
			    char name[32];

			    deopt = MIR_new_label(build->context);
			    done = MIR_new_label(build->context);
			    if (tagged_list) {
				MIR_reg_t type;

				sprintf(name, "sublist_type%d", copy_serial++);
				type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, type),
				    MIR_new_int_op(build->context, TYPE_LIST)));
			    }
			    if (tagged_start) {
				MIR_reg_t type;

				sprintf(name, "sublist_start_type%d", copy_serial++);
				type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src2),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, type),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			}
			append(build, MIR_new_call_insn(build->context, 5,
			    MIR_new_ref_op(build->context, build->proto_sublist_from),
			    MIR_new_ref_op(build->context, build->import_sublist_from),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_reg_op(build->context, values[instr->src2])));
			if (tagged_list || tagged_start) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status,
				common_return);
			    append(build, done);
			}
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
					jit_tag_offset(program, instr->src1),
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
					jit_tag_offset(program, instr->src2),
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
				    jit_tag_offset(program, instr->value),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			if (tagged_l1 || tagged_l2) {
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
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
			    MIR_reg_t raw_value;
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
					jit_tag_offset(program, instr->src2),
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
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
			    else
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, in_type),
				    MIR_new_int_op(build->context, elem_type)));
			    raw_value = append_raw_value(build, program, values,
				instr->src1, deopt_values, &copy_serial);
			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context, build->proto_list_in),
				MIR_new_ref_op(build->context, build->import_list_in),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, in_type),
				MIR_new_reg_op(build->context, values[instr->src2])));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    if (tagged_list) {
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));
				append(build, deopt);
			    append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, done);
			    }
			    break;
			}
			    append_deopt_exit(build, program, instr,
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
			int check_s1 = tagged_s1
			    && !(instr->guarded_operands & (1U << 0));
			int check_s2 = tagged_s2
			    && !(instr->guarded_operands & (1U << 1));
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

			    if (check_s1 || check_s2) {
				char name[32];

				deopt = MIR_new_label(build->context);
				done = MIR_new_label(build->context);
				if (check_s1) {
				    MIR_reg_t type;

				    sprintf(name, "index_s1_type%d", copy_serial++);
				    type = new_reg(build, name);
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, type),
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, instr->src1), deopt_values, 0, 1)));
				    append(build, MIR_new_insn(build->context, MIR_BNE,
					MIR_new_label_op(build->context, deopt),
					MIR_new_reg_op(build->context, type),
					MIR_new_int_op(build->context, TYPE_STR)));
				}
				if (check_s2) {
				    MIR_reg_t type;

				    sprintf(name, "index_s2_type%d", copy_serial++);
				    type = new_reg(build, name);
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, type),
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, instr->src2), deopt_values, 0, 1)));
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
			    if (check_s1 || check_s2) {
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));
				append(build, deopt);
			    append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, done);
			    }
			    break;
			}
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if ((instr->op == HIR_OP_EQ || instr->op == HIR_OP_NE)
			&& program->value_is_tagged
			&& (program->value_is_tagged[instr->src1]
			    || program->value_is_tagged[instr->src2])) {
			char name[32];
			MIR_reg_t eq_res, raw1, raw2, type1, type2, case_reg;

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
				    jit_tag_offset(program, instr->src1),
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
				    jit_tag_offset(program, instr->src2),
				    deopt_values, 0, 1)));
			else
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type2),
				MIR_new_int_op(build->context,
				    program->value_types[instr->src2])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, case_reg),
			    MIR_new_int_op(build->context, 0)));
			raw1 = append_raw_value(build, program, values, instr->src1,
						deopt_values, &copy_serial);
			raw2 = append_raw_value(build, program, values, instr->src2,
						deopt_values, &copy_serial);
			append(build, MIR_new_call_insn(build->context, 8,
			    MIR_new_ref_op(build->context, build->proto_equality),
			    MIR_new_ref_op(build->context, build->import_equality),
			    MIR_new_reg_op(build->context, eq_res),
			    MIR_new_reg_op(build->context, raw1),
			    MIR_new_reg_op(build->context, type1),
			    MIR_new_reg_op(build->context, raw2),
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
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->value])
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
				    deopt_values, 0, 1),
				MIR_new_int_op(build->context, TYPE_INT)));
			break;
		    }
		    if (!(program->value_is_tagged
			  && (program->value_is_tagged[instr->src1]
			      || program->value_is_tagged[instr->src2]))
			&& program->value_types
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
		    if (!(program->value_is_tagged
			  && (program->value_is_tagged[instr->src1]
			      || program->value_is_tagged[instr->src2]))
			&& program->value_types
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
			int tagged_s1 = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_s2 = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			int is_str1 = !tagged_s1 && program->value_types
			    && program->value_types[instr->src1] == TYPE_STR;
			int is_str2 = !tagged_s2 && program->value_types
			    && program->value_types[instr->src2] == TYPE_STR;

			if (is_str1 && is_str2) {
			    char name[32];
			    int owner = program->value_owned_slots
				? program->value_owned_slots[instr->value] : -1;
			    sprintf(name, "str_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t quota_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_QUOTA,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);

			    if (owner >= 0) {
				MIR_label_t done = MIR_new_label(build->context);
				MIR_reg_t transferred;
				MIR_reg_t result_out;

				sprintf(name, "str_owned%d", copy_serial++);
				transferred = new_reg(build, name);
				sprintf(name, "str_out%d", copy_serial++);
				result_out = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_ADD,
				    MIR_new_reg_op(build->context, result_out),
				    MIR_new_reg_op(build->context, deopt_values),
				    MIR_new_int_op(build->context,
					instr->value * sizeof(Num))));
				append(build, MIR_new_call_insn(build->context, 10,
				    MIR_new_ref_op(build->context,
					build->proto_str_concat_owned),
				    MIR_new_ref_op(build->context,
					build->import_str_concat_owned),
				    MIR_new_reg_op(build->context, transferred),
				    MIR_new_reg_op(build->context, owned_values),
				    MIR_new_int_op(build->context, owner),
				    MIR_new_reg_op(build->context,
					values[instr->src1]),
				    MIR_new_reg_op(build->context,
					values[instr->src2]),
				    MIR_new_int_op(build->context,
					instr->owned_last_use),
				    MIR_new_reg_op(build->context, result_out),
				    MIR_new_reg_op(build->context, error_out)));
				MIR_label_t fallback = MIR_new_label(build->context);
				append(build, MIR_new_insn(build->context, MIR_BF,
				    MIR_new_label_op(build->context, fallback),
				    MIR_new_reg_op(build->context, transferred)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0,
					error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, quota_error),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context,
					values[instr->value]),
				    MIR_new_mem_op(build->context, MIR_T_P,
					instr->value * sizeof(Num), deopt_values,
					0, 1)));
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));
				append(build, fallback);
				append(build, MIR_new_call_insn(build->context, 6,
				    MIR_new_ref_op(build->context,
					build->proto_str_concat),
				    MIR_new_ref_op(build->context,
					build->import_str_concat),
				    MIR_new_reg_op(build->context,
					values[instr->value]),
				    MIR_new_reg_op(build->context,
					values[instr->src1]),
				    MIR_new_reg_op(build->context,
					values[instr->src2]),
				    MIR_new_reg_op(build->context, error_out)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0,
					error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, quota_error),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
				append(build, done);
			    } else {
				append(build, MIR_new_call_insn(build->context, 6,
				    MIR_new_ref_op(build->context,
					build->proto_str_concat),
				    MIR_new_ref_op(build->context,
					build->import_str_concat),
				    MIR_new_reg_op(build->context,
					values[instr->value]),
				    MIR_new_reg_op(build->context,
					values[instr->src1]),
				    MIR_new_reg_op(build->context,
					values[instr->src2]),
				    MIR_new_reg_op(build->context, error_out)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0,
					error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, quota_error),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
			    }
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value]) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->value),
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
				&last_status_exit, JIT_RUN_ERROR, E_QUOTA,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);

			    if (tagged_s1) {
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
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
					jit_tag_offset(program, instr->src2),
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
					jit_tag_offset(program, instr->value),
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
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_STR)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));

			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
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
			int tagged_val = program->value_is_tagged
			    && instr->value > 0 && instr->value < program->num_values
			    && program->value_is_tagged[instr->value];
			int tagged_s1 = program->value_is_tagged
			    && instr->src1 > 0 && instr->src1 < program->num_values
			    && program->value_is_tagged[instr->src1];
			int tagged_s2 = program->value_is_tagged
			    && instr->src2 > 0 && instr->src2 < program->num_values
			    && program->value_is_tagged[instr->src2];
			int valid_float_op = !tagged_s1 && !tagged_s2
			    && ((is_float_arith && !tagged_val
				 && program->value_types[instr->value] == TYPE_FLOAT
				 && program->value_types[instr->src1] == TYPE_FLOAT
				 && program->value_types[instr->src2] == TYPE_FLOAT)
				|| (is_float_cmp
				    && program->value_types[instr->src1] == TYPE_FLOAT
				    && program->value_types[instr->src2] == TYPE_FLOAT));

			if (!valid_float_op) {
			    append_deopt_exit(build, program, instr,
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
				E_DIV, instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);
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
			    append(build, MIR_new_insn(build->context,
						      float_binary_code(instr->op),
						      MIR_new_reg_op(build->context,
							 values[instr->value]),
						      MIR_new_reg_op(build->context,
							 values[instr->src1]),
						      MIR_new_reg_op(build->context,
							 values[instr->src2])));
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
		    if (instr->op == HIR_OP_ROTL32) {
			MIR_reg_t left, right;
			Num count;
			char name[32];

			if (sizeof(Num) * CHAR_BIT <= 32
			    || !integer_constant_value(program, instr->src2, &count)
			    || count <= 0 || count >= 32) {
			    append_deopt_exit(build, program, instr, values,
				deopt_map_out, deopt_values, status, common_return);
			    break;
			}
			sprintf(name, "rotl_left%d", copy_serial++);
			left = new_reg(build, name);
			sprintf(name, "rotl_right%d", copy_serial++);
			right = new_reg(build, name);
			append(build, MIR_new_insn(build->context, MIR_LSHS,
			    MIR_new_reg_op(build->context, left),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_int_op(build->context, count)));
			append(build, MIR_new_insn(build->context, MIR_URSHS,
			    MIR_new_reg_op(build->context, right),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_int_op(build->context, 32 - count)));
			append(build, MIR_new_insn(build->context, MIR_ORS,
			    MIR_new_reg_op(build->context, left),
			    MIR_new_reg_op(build->context, left),
			    MIR_new_reg_op(build->context, right)));
			append(build, MIR_new_insn(build->context, MIR_UEXT32,
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, left)));
			break;
		    }
		    {
			MIR_label_t arithmetic_error = 0;
			MIR_label_t invalid_argument = 0;
			MIR_label_t range_error = 0;
			MIR_label_t type_error = 0;
			Num rhs_constant = 0;
			int modulus_shift = instr->op == HIR_OP_MOD
			    && integer_constant_value(program, instr->src2,
				&rhs_constant)
			    ? positive_power_of_two_shift(rhs_constant) : -1;

			if (instr->op == HIR_OP_DIV
			    || (instr->op == HIR_OP_MOD && modulus_shift < 0)
			    || instr->op == HIR_OP_EXP)
			    arithmetic_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_DIV,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);
			if (instr->op == HIR_OP_SHL || instr->op == HIR_OP_SHR
			    || instr->op == HIR_OP_LSHR)
			    invalid_argument = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_INVARG,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);
		    if (instr->op == HIR_OP_INDEX) {
			if (!(program->value_is_tagged
			      && program->value_is_tagged[instr->src1])
			    && program->value_types
			    && program->value_types[instr->src1] == TYPE_STR) {
			    char name[32];
			    int tagged_index = program->value_is_tagged
				&& program->value_is_tagged[instr->src2];
			    int tagged_result = program->value_is_tagged
				&& program->value_is_tagged[instr->value];

			    if (tagged_index) {
				MIR_reg_t index_type;

				type_error = new_status_exit(build, &status_exits,
				    &last_status_exit, JIT_RUN_ERROR, E_TYPE,
				    instr->deopt_map, instr->bytecode_pc,
				    instr->source_lineno);
				sprintf(name, "str_index_type%d", copy_serial++);
				index_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, index_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src2),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, type_error),
				    MIR_new_reg_op(build->context, index_type),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    sprintf(name, "str_idx_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    MIR_label_t range_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_RANGE,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);
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
			    if (tagged_result)
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_int_op(build->context, TYPE_STR)));
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
			range_error = new_status_exit(build, &status_exits,
			    &last_status_exit, JIT_RUN_ERROR, E_RANGE,
			    instr->deopt_map, instr->bytecode_pc,
			    instr->source_lineno);
			if (tagged_base || tagged_index)
			    type_error = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_TYPE,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);

			if (tagged_index) {
			    MIR_reg_t index_type;

			    sprintf(name, "index_type%d", copy_serial++);
			    index_type = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, index_type),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src2),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, type_error),
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
				    jit_tag_offset(program, instr->src1),
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
				MIR_new_label_op(build->context, type_error)));

			    /* String indexing */
			    append(build, is_str);
			    char name_err[32];
			    sprintf(name_err, "str_idx_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name_err);
			    MIR_label_t str_range_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_RANGE,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);
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
					jit_tag_offset(program, instr->value),
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
				    jit_tag_offset(program, instr->value),
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
			if (tagged_result
			    || (expected_elem_type & TYPE_COMPLEX_FLAG)) {
			    MIR_op_t retained_type = tagged_result
				? MIR_new_reg_op(build->context, elem_type)
				: MIR_new_int_op(build->context,
				    expected_elem_type);

			    append(build, MIR_new_call_insn(build->context, 4,
				MIR_new_ref_op(build->context,
				    build->proto_retain_raw),
				MIR_new_ref_op(build->context,
				    build->import_retain_raw),
				MIR_new_reg_op(build->context,
				    values[instr->value]), retained_type));
			}
			append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, loaded)));
			append(build, deopt);
		    append_deopt_exit(build, program, instr, values,
					  deopt_map_out, deopt_values, status,
					  common_return);
			append(build, loaded);
		    } else {
			int tagged_src1 = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_src2 = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];
			int check_src1 = tagged_src1
			    && !(instr->guarded_operands & (1U << 0));
			int check_src2 = tagged_src2
			    && !(instr->guarded_operands & (1U << 1));
			int tagged_dst = program->value_is_tagged
			    && program->value_is_tagged[instr->value];

			if (check_src1 || check_src2) {
			    MIR_label_t deopt = MIR_new_label(build->context);
			    MIR_label_t type_checked = MIR_new_label(build->context);
			    if (check_src1) {
				char name[32];
				sprintf(name, "arith_t1_%d", copy_serial++);
				MIR_reg_t t1 = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, t1),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    if (check_src2) {
				char name[32];
				sprintf(name, "arith_t2_%d", copy_serial++);
				MIR_reg_t t2 = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src2),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, t2),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    }
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, type_checked)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status, common_return);
			    append(build, type_checked);
			}
			if (tagged_dst) {
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->value),
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
		    } else if (instr->op == HIR_OP_MOD && modulus_shift >= 0) {
			JITNegativeModExit *exit = mymalloc(
			    sizeof(JITNegativeModExit), M_PROGRAM);
			UNum mask = ((UNum) 1 << modulus_shift) - 1;

			exit->label = MIR_new_label(build->context);
			exit->continuation = MIR_new_label(build->context);
			exit->source = values[instr->src1];
			exit->destination = values[instr->value];
			exit->mask = mask;
			exit->next = 0;
			if (last_negative_mod_exit)
			    last_negative_mod_exit->next = exit;
			else
			    negative_mod_exits = exit;
			last_negative_mod_exit = exit;
			append(build, MIR_new_insn(build->context, MIR_BLT,
			    MIR_new_label_op(build->context, exit->label),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_AND,
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, values[instr->src1]),
			    MIR_new_int_op(build->context, (Num) mask)));
			append(build, exit->continuation);
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
			    if (!instr->shift_count_proven_valid) {
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
			}
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
			    if (!(program->value_is_tagged
				  && program->value_is_tagged[copy->src])
				&& program->value_types
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
					    jit_tag_offset(program, copy->src),
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
			    int src_fl = !(program->value_is_tagged
					   && program->value_is_tagged[copy->src])
				&& program->value_types
				&& program->value_types[copy->src] == TYPE_FLOAT;
			    int dst_fl = !(program->value_is_tagged
					   && program->value_is_tagged[copy->dst])
				&& program->value_types
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
					jit_tag_offset(program, copy->dst),
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
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (block->num_successors == 2) {
			if (program->value_is_tagged
			    && program->value_is_tagged[instr->src1]) {
			    char name[32];
			    sprintf(name, "truth%d", copy_serial++);
			    MIR_reg_t truth = new_reg(build, name);
			    sprintf(name, "type_reg%d", copy_serial++);
			    MIR_reg_t type_reg = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, type_reg),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src1),
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
			    append_deopt_exit(build, program, instr,
					  values, deopt_map_out, deopt_values,
					  status, common_return);
			break;
		    }
		    if (program->value_is_tagged
			&& program->value_is_tagged[instr->src1]) {
			char name[32];
			MIR_reg_t return_type;

			sprintf(name, "return_type%d", copy_serial++);
			return_type = new_reg(build, name);
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_mem_op(build->context,
				sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				offsetof(Var, v.num), result, 0, 1),
			    MIR_new_reg_op(build->context, values[instr->src1])));
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, return_type),
			    MIR_new_mem_op(build->context, tag_t,
				jit_tag_offset(program, instr->src1),
				deopt_values, 0, 1)));
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_mem_op(build->context, MIR_T_I32,
				offsetof(Var, type), result, 0, 1),
			    MIR_new_reg_op(build->context, return_type)));
		    } else if (program->value_types
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
		    if (!(program->value_is_tagged
			  && program->value_is_tagged[instr->src1]))
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_mem_op(build->context, MIR_T_I32,
				offsetof(Var, type), result, 0, 1),
			    MIR_new_int_op(build->context, instr->literal_type)));
		    return_status(build, status, common_return,
			program->value_ownership
			&& (program->value_ownership[instr->src1]
			    == JIT_OWNERSHIP_OWNED
			 || program->value_ownership[instr->src1]
			    == JIT_OWNERSHIP_OWNED_PROPERTY)
			? JIT_NATIVE_RETURNED_OWNED : JIT_RUN_RETURNED);
		    break;
		case HIR_TAC_RETURN0:
		    append_return_zero(build, result, status, common_return);
		    break;
		case HIR_TAC_CALL:
		    if (instr->deopt_map > 0
			&& instr->deopt_map < program->num_deopt_maps
			&& jit_deopt_map_bridges_builtin(&program->deopt_maps[instr->deopt_map])) {
			append_materialized_exit(build, program, instr->deopt_map,
					 values,
					 deopt_map_out, deopt_values, status,
					 common_return, JIT_RUN_CALL_VERB);
			if (resume_continuations[instr->deopt_map])
			    append(build, resume_continuations[instr->deopt_map]);
		    } else
		    append_deopt_exit(build, program, instr, values,
					  deopt_map_out, deopt_values, status,
					  common_return);
		    break;
		case HIR_TAC_PUT_PROP:
		    if (instr->deopt_map > 0
			&& instr->deopt_map < program->num_deopt_maps) {
			JITDeoptMap *map = &program->deopt_maps[instr->deopt_map];
			int rhs = map->stack_depth >= 1
			    ? map->stack_values[map->stack_depth - 1] : 0;
		    int obj_tagged = program->value_is_tagged
			&& program->value_is_tagged[instr->src1];
		    int obj_is_obj = !obj_tagged && program->value_types
			&& program->value_types[instr->src1] == TYPE_OBJ;
		    int prop_tagged = program->value_is_tagged
			&& program->value_is_tagged[instr->src2];

		    if (rhs > 0 && rhs < program->num_values
			&& (obj_is_obj || obj_tagged) && program->value_types
			&& !prop_tagged
			&& program->value_types[instr->src2] == TYPE_STR) {
			    char name[32];
			    MIR_reg_t rhs_type;
			    MIR_reg_t rhs_raw;
			    MIR_reg_t prop_ok;
			    MIR_label_t deopt = MIR_new_label(build->context);
			    MIR_label_t done = MIR_new_label(build->context);
			    MIR_label_t prop_err = new_status_exit(build, &status_exits,
				&last_status_exit, JIT_RUN_ERROR, E_NONE,
				instr->deopt_map, instr->bytecode_pc,
				instr->source_lineno);

			    if (obj_tagged) {
				MIR_reg_t obj_type;
				MIR_label_t obj_ok = MIR_new_label(build->context);

				sprintf(name, "put_obj_type%d", copy_serial++);
				obj_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, obj_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BEQ,
				    MIR_new_label_op(build->context, obj_ok),
				    MIR_new_reg_op(build->context, obj_type),
				    MIR_new_int_op(build->context, TYPE_OBJ)));
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, deopt)));
				append(build, obj_ok);
			    }
			    sprintf(name, "put_rhs_type%d", copy_serial++);
			    rhs_type = new_reg(build, name);
			    if (program->value_is_tagged && program->value_is_tagged[rhs])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, rhs_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, rhs),
					deopt_values, 0, 1)));
			    else
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, rhs_type),
				    MIR_new_int_op(build->context,
					program->value_types[rhs])));
			    sprintf(name, "put_prop_ok%d", copy_serial++);
			    prop_ok = new_reg(build, name);
			    rhs_raw = append_raw_value(build, program, values, rhs,
				deopt_values, &copy_serial);
			    append(build, MIR_new_call_insn(build->context, 9,
				MIR_new_ref_op(build->context, build->proto_put_prop),
				MIR_new_ref_op(build->context, build->import_put_prop),
				MIR_new_reg_op(build->context, prop_ok),
				MIR_new_reg_op(build->context, values[instr->src1]),
				MIR_new_reg_op(build->context, values[instr->src2]),
				MIR_new_reg_op(build->context, progr),
				MIR_new_reg_op(build->context, rhs_raw),
				MIR_new_reg_op(build->context, rhs_type),
				MIR_new_reg_op(build->context, error_out)));
			    append(build, MIR_new_insn(build->context, MIR_BLT,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, prop_ok),
				MIR_new_int_op(build->context, 0)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, prop_err),
				MIR_new_reg_op(build->context, prop_ok),
				MIR_new_int_op(build->context, 0)));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, rhs_raw)));
			    else if (!(program->value_is_tagged
				       && program->value_is_tagged[rhs])
				&& program->value_types[rhs] == TYPE_FLOAT)
				append(build, MIR_new_insn(build->context, MIR_DMOV,
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, values[rhs])));
			    else
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, values[rhs])));
			    if (program->value_is_tagged
				&& program->value_is_tagged[instr->value])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->value),
					deopt_values, 0, 1),
				    MIR_new_reg_op(build->context, rhs_type)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
		    append_deopt_exit(build, program, instr, values,
				deopt_map_out, deopt_values, status, common_return);
			    append(build, done);
			    break;
			}
		    }
		    append_deopt_exit(build, program, instr, values,
				      deopt_map_out, deopt_values, status,
				      common_return);
		    break;
		case HIR_TAC_RANGE_SET:
		    append_deopt_exit(build, program, instr, values,
				      deopt_map_out, deopt_values, status,
				      common_return);
		    break;
		case HIR_TAC_INDEX_SET:
		    {
			char name[32];
			MIR_label_t deopt = MIR_new_label(build->context);
			MIR_label_t done = MIR_new_label(build->context);
			MIR_label_t range_error = new_status_exit(build,
			    &status_exits, &last_status_exit, JIT_RUN_ERROR,
			    E_RANGE, instr->deopt_map, instr->bytecode_pc,
			    instr->source_lineno);
			MIR_reg_t raw_value;
			MIR_reg_t value_type;

			if (instr->op == HIR_OP_INDEX) {
			    MIR_reg_t outer_idx = values[instr->src1];
			    MIR_reg_t inner_idx = values[instr->src2];
			    int tagged_outer = program->value_is_tagged
				&& program->value_is_tagged[instr->src1];
			    int tagged_inner = program->value_is_tagged
				&& program->value_is_tagged[instr->src2];

			    if (tagged_outer) {
				MIR_reg_t outer_type;
				sprintf(name, "set_outer_type%d", copy_serial++);
				outer_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, outer_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src1),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, outer_type),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    } else if (program->value_types
				       && program->value_types[instr->src1] != TYPE_INT) {
				append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				break;
			    }
			    if (tagged_inner) {
				MIR_reg_t inner_type;
				sprintf(name, "set_inner_type%d", copy_serial++);
				inner_type = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, inner_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src2),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, inner_type),
				    MIR_new_int_op(build->context, TYPE_INT)));
			    } else if (program->value_types
				       && program->value_types[instr->src2] != TYPE_INT) {
				append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				break;
			    }
			    sprintf(name, "set_value_type%d", copy_serial++);
			    value_type = new_reg(build, name);
			    if (program->value_is_tagged && program->value_is_tagged[instr->src3])
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, value_type),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, instr->src3),
					deopt_values, 0, 1)));
			    else
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, value_type),
				    MIR_new_int_op(build->context,
					program->value_types ? program->value_types[instr->src3] : TYPE_ANY)));
			    raw_value = append_raw_value(build, program, values,
				instr->src3, deopt_values, &copy_serial);
			    append(build, MIR_new_call_insn(build->context, 10,
				MIR_new_ref_op(build->context,
				    build->proto_list_nested_index_set),
				MIR_new_ref_op(build->context,
				    build->import_list_nested_index_set),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, env),
				MIR_new_int_op(build->context, instr->local_id),
				MIR_new_reg_op(build->context, outer_idx),
				MIR_new_reg_op(build->context, inner_idx),
				MIR_new_reg_op(build->context, raw_value),
				MIR_new_reg_op(build->context, value_type),
				MIR_new_reg_op(build->context, error_out)));
			    sprintf(name, "nested_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_mem_op(build->context, MIR_T_I32, 0,
				    error_out, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, range_error),
				MIR_new_reg_op(build->context, err_reg),
				MIR_new_int_op(build->context, E_RANGE)));
			    append(build, MIR_new_insn(build->context, MIR_BEQ,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_int_op(build->context, 0)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, deopt);
			    append_deopt_exit(build, program, instr, values,
				deopt_map_out, deopt_values, status, common_return);
			    append(build, done);
			    break;
			}

			MIR_reg_t base = values[instr->src1];
			MIR_reg_t index = values[instr->src2];
			MIR_reg_t list_len;
			int direct_int_list = instr->direct_int_list_index_set;
			int tagged_base = program->value_is_tagged
			    && program->value_is_tagged[instr->src1];
			int tagged_index = program->value_is_tagged
			    && program->value_is_tagged[instr->src2];

			if (!tagged_base
			    && program->value_types[instr->src1] != TYPE_LIST) {
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status,
				common_return);
			    break;
			}
			if (tagged_base) {
			    MIR_reg_t base_type;

			    sprintf(name, "set_base_type%d", copy_serial++);
			    base_type = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, base_type),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src1),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, base_type),
				MIR_new_int_op(build->context, TYPE_LIST)));
			}
			if (tagged_index) {
			    MIR_reg_t index_type;

			    sprintf(name, "set_index_type%d", copy_serial++);
			    index_type = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, index_type),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src2),
				    deopt_values, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, deopt),
				MIR_new_reg_op(build->context, index_type),
				MIR_new_int_op(build->context, TYPE_INT)));
			} else if (program->value_types[instr->src2] != TYPE_INT) {
			    append_deopt_exit(build, program, instr,
				values, deopt_map_out, deopt_values, status,
				common_return);
			    break;
			}
			append(build, MIR_new_insn(build->context, MIR_BEQ,
			    MIR_new_label_op(build->context, deopt),
			    MIR_new_reg_op(build->context, base),
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_BLT,
			    MIR_new_label_op(build->context, range_error),
			    MIR_new_reg_op(build->context, index),
			    MIR_new_int_op(build->context, 1)));
			sprintf(name, "set_list_len%d", copy_serial++);
			list_len = new_reg(build, name);
			append(build, MIR_new_insn(build->context, MIR_MOV,
			    MIR_new_reg_op(build->context, list_len),
			    MIR_new_mem_op(build->context,
				sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				offsetof(Var, v.num), base, 0, 1)));
			append(build, MIR_new_insn(build->context, MIR_BGT,
			    MIR_new_label_op(build->context, range_error),
			    MIR_new_reg_op(build->context, index),
			    MIR_new_reg_op(build->context, list_len)));

			sprintf(name, "set_value_type%d", copy_serial++);
			value_type = new_reg(build, name);
			if (program->value_is_tagged[instr->src3])
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, value_type),
				MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, instr->src3),
				    deopt_values, 0, 1)));
			else
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, value_type),
				MIR_new_int_op(build->context,
				    program->value_types[instr->src3])));
			raw_value = append_raw_value(build, program, values,
			    instr->src3, deopt_values, &copy_serial);
			if (direct_int_list) {
			    MIR_label_t shared = MIR_new_label(build->context);
			    MIR_reg_t refcount_reg;
			    MIR_reg_t elem_offset;
			    MIR_reg_t elem_addr;

			    sprintf(name, "set_refcount%d", copy_serial++);
			    refcount_reg = new_reg(build, name);
			    sprintf(name, "set_elem_offset%d", copy_serial++);
			    elem_offset = new_reg(build, name);
			    sprintf(name, "set_elem_addr%d", copy_serial++);
			    elem_addr = new_reg(build, name);
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, refcount_reg),
				MIR_new_mem_op(build->context, MIR_T_I32,
				    -(int) sizeof(int), base, 0, 1)));
			    append(build, MIR_new_insn(build->context, MIR_BNE,
				MIR_new_label_op(build->context, shared),
				MIR_new_reg_op(build->context, refcount_reg),
				MIR_new_int_op(build->context, 1)));
			    append(build, MIR_new_insn(build->context, MIR_MUL,
				MIR_new_reg_op(build->context, elem_offset),
				MIR_new_reg_op(build->context, index),
				MIR_new_int_op(build->context, sizeof(Var))));
			    append(build, MIR_new_insn(build->context, MIR_ADD,
				MIR_new_reg_op(build->context, elem_addr),
				MIR_new_reg_op(build->context, base),
				MIR_new_reg_op(build->context, elem_offset)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context,
				    sizeof(Num) == 8 ? MIR_T_I64 : MIR_T_I32,
				    offsetof(Var, v.num), elem_addr, 0, 1),
				MIR_new_reg_op(build->context, raw_value)));
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_reg_op(build->context, values[instr->value]),
				MIR_new_reg_op(build->context, base)));
			    append(build, MIR_new_insn(build->context, MIR_JMP,
				MIR_new_label_op(build->context, done)));
			    append(build, shared);
			}
			append(build, MIR_new_call_insn(build->context, 10,
			    MIR_new_ref_op(build->context,
				build->proto_list_index_set),
			    MIR_new_ref_op(build->context,
				build->import_list_index_set),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_reg_op(build->context, env),
			    MIR_new_int_op(build->context, instr->local_id),
			    MIR_new_reg_op(build->context, base),
			    MIR_new_reg_op(build->context, index),
			    MIR_new_reg_op(build->context, raw_value),
			    MIR_new_reg_op(build->context, value_type),
			    MIR_new_reg_op(build->context, error_out)));
			append(build, MIR_new_insn(build->context, MIR_BEQ,
			    MIR_new_label_op(build->context, deopt),
			    MIR_new_reg_op(build->context, values[instr->value]),
			    MIR_new_int_op(build->context, 0)));
			append(build, MIR_new_insn(build->context, MIR_JMP,
			    MIR_new_label_op(build->context, done)));
			append(build, deopt);
		    append_deopt_exit(build, program, instr, values,
			    deopt_map_out, deopt_values, status, common_return);
			append(build, done);
		    }
		    break;
		case HIR_TAC_RANGE_REF:
		    if (instr->deopt_map >= 0
			&& instr->deopt_map < program->num_deopt_maps) {
			JITDeoptMap *map = &program->deopt_maps[instr->deopt_map];
			int base_val = instr->src1;
			int from_val = instr->src2;
			int to_val = (map->stack_depth >= 1)
			    ? map->stack_values[map->stack_depth - 1] : 0;
			var_type base_type = program->value_types
			    ? program->value_types[base_val] : TYPE_ANY;
			int tagged_base = program->value_is_tagged
			    && program->value_is_tagged[base_val];
			int tagged_from = program->value_is_tagged
			    && program->value_is_tagged[from_val];
			int tagged_to = (to_val > 0 && program->value_is_tagged)
			    && program->value_is_tagged[to_val];

			if (to_val > 0 && (base_type == TYPE_STR || base_type == TYPE_LIST || tagged_base)) {
			    char name[32];
			    MIR_label_t deopt = 0;
			    MIR_label_t range_err = new_status_exit(build, &status_exits,
								    &last_status_exit,
								    JIT_RUN_ERROR,
								    E_RANGE,
								    instr->deopt_map,
								    instr->bytecode_pc,
								    instr->source_lineno);
			    sprintf(name, "range_err%d", copy_serial++);
			    MIR_reg_t err_reg = new_reg(build, name);

			    if (tagged_base || tagged_from || tagged_to) {
				deopt = MIR_new_label(build->context);
				if (tagged_from) {
				    MIR_reg_t ft;
				    sprintf(name, "range_ft%d", copy_serial++);
				    ft = new_reg(build, name);
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, ft),
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, from_val),
					    deopt_values, 0, 1)));
				    append(build, MIR_new_insn(build->context, MIR_BNE,
					MIR_new_label_op(build->context, deopt),
					MIR_new_reg_op(build->context, ft),
					MIR_new_int_op(build->context, TYPE_INT)));
				}
				if (tagged_to) {
				    MIR_reg_t tt;
				    sprintf(name, "range_tt%d", copy_serial++);
				    tt = new_reg(build, name);
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_reg_op(build->context, tt),
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, to_val),
					    deopt_values, 0, 1)));
				    append(build, MIR_new_insn(build->context, MIR_BNE,
					MIR_new_label_op(build->context, deopt),
					MIR_new_reg_op(build->context, tt),
					MIR_new_int_op(build->context, TYPE_INT)));
				}
			    }

			    if (base_type == TYPE_STR) {
				append(build, MIR_new_call_insn(build->context, 7,
				    MIR_new_ref_op(build->context, build->proto_str_range_ref),
				    MIR_new_ref_op(build->context, build->import_str_range_ref),
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, values[base_val]),
				    MIR_new_reg_op(build->context, values[from_val]),
				    MIR_new_reg_op(build->context, values[to_val]),
				    MIR_new_reg_op(build->context, error_out)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, range_err),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
				if (program->value_is_tagged && program->value_is_tagged[instr->value])
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, instr->value),
					    deopt_values, 0, 1),
					MIR_new_int_op(build->context, TYPE_STR)));
			    } else if (base_type == TYPE_LIST) {
				append(build, MIR_new_call_insn(build->context, 7,
				    MIR_new_ref_op(build->context, build->proto_list_range_ref),
				    MIR_new_ref_op(build->context, build->import_list_range_ref),
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, values[base_val]),
				    MIR_new_reg_op(build->context, values[from_val]),
				    MIR_new_reg_op(build->context, values[to_val]),
				    MIR_new_reg_op(build->context, error_out)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, range_err),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
				if (program->value_is_tagged && program->value_is_tagged[instr->value])
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, instr->value),
					    deopt_values, 0, 1),
					MIR_new_int_op(build->context, TYPE_LIST)));
			    } else {
				MIR_reg_t bt;
				MIR_label_t is_list = MIR_new_label(build->context);
				MIR_label_t done = MIR_new_label(build->context);
				sprintf(name, "range_bt%d", copy_serial++);
				bt = new_reg(build, name);
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, bt),
				    MIR_new_mem_op(build->context, tag_t,
					jit_tag_offset(program, base_val),
					deopt_values, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BEQ,
				    MIR_new_label_op(build->context, is_list),
				    MIR_new_reg_op(build->context, bt),
				    MIR_new_int_op(build->context, TYPE_LIST)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, deopt),
				    MIR_new_reg_op(build->context, bt),
				    MIR_new_int_op(build->context, TYPE_STR)));

				append(build, MIR_new_call_insn(build->context, 7,
				    MIR_new_ref_op(build->context, build->proto_str_range_ref),
				    MIR_new_ref_op(build->context, build->import_str_range_ref),
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, values[base_val]),
				    MIR_new_reg_op(build->context, values[from_val]),
				    MIR_new_reg_op(build->context, values[to_val]),
				    MIR_new_reg_op(build->context, error_out)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, range_err),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
				if (program->value_is_tagged && program->value_is_tagged[instr->value])
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, instr->value),
					    deopt_values, 0, 1),
					MIR_new_int_op(build->context, TYPE_STR)));
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, done)));

				append(build, is_list);
				append(build, MIR_new_call_insn(build->context, 7,
				    MIR_new_ref_op(build->context, build->proto_list_range_ref),
				    MIR_new_ref_op(build->context, build->import_list_range_ref),
				    MIR_new_reg_op(build->context, values[instr->value]),
				    MIR_new_reg_op(build->context, values[base_val]),
				    MIR_new_reg_op(build->context, values[from_val]),
				    MIR_new_reg_op(build->context, values[to_val]),
				    MIR_new_reg_op(build->context, error_out)));
				append(build, MIR_new_insn(build->context, MIR_MOV,
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_mem_op(build->context, MIR_T_I32, 0, error_out, 0, 1)));
				append(build, MIR_new_insn(build->context, MIR_BNE,
				    MIR_new_label_op(build->context, range_err),
				    MIR_new_reg_op(build->context, err_reg),
				    MIR_new_int_op(build->context, E_NONE)));
				if (program->value_is_tagged && program->value_is_tagged[instr->value])
				    append(build, MIR_new_insn(build->context, MIR_MOV,
					MIR_new_mem_op(build->context, tag_t,
					    jit_tag_offset(program, instr->value),
					    deopt_values, 0, 1),
					MIR_new_int_op(build->context, TYPE_LIST)));
				append(build, done);
			    }

			    if (deopt) {
				MIR_label_t loaded = MIR_new_label(build->context);
				append(build, MIR_new_insn(build->context, MIR_JMP,
				    MIR_new_label_op(build->context, loaded)));
				append(build, deopt);
			    append_deopt_exit(build, program, instr,
				    values, deopt_map_out, deopt_values, status,
				    common_return);
				append(build, loaded);
			    }
			    break;
			}
		    }
		    append_deopt_exit(build, program, instr, values,
				      deopt_map_out, deopt_values, status,
				      common_return);
		    break;
		case HIR_TAC_CALL_VERB:
		    if (!(instr->deopt_map > 0
			&& instr->deopt_map < program->num_deopt_maps
		    && append_region_call(build, program, instr, values,
			tick_result, timed_out, progr, error_out, owned_values,
			deopt_map_out, deopt_values, status, common_return,
			    resume_continuations[instr->deopt_map],
			    jit_region_deferred_list_tail(program, instr),
			    &copy_serial)))
			append_materialized_exit(build, program, instr->deopt_map,
			    values, deopt_map_out, deopt_values, status,
			    common_return, JIT_RUN_CALL_VERB);
		    if (instr->deopt_map > 0
			&& instr->deopt_map < program->num_deopt_maps
			&& resume_continuations[instr->deopt_map])
			append(build, resume_continuations[instr->deopt_map]);
		    break;
		case HIR_TAC_LABEL:
		case HIR_TAC_STORE_LOCAL:
		case HIR_TAC_UNSUPPORTED:
		case HIR_TAC_PHI:
		    break;
		}
		if (instr->kind == HIR_TAC_CALL
		    || instr->kind == HIR_TAC_CALL_VERB
		    || instr->kind == HIR_TAC_DEOPT
		    || instr->kind == HIR_TAC_PUT_PROP
		    || instr->kind == HIR_TAC_INDEX_SET
		    || instr->kind == HIR_TAC_RANGE_SET)
		    ticks_since_timeout_check = 0;
		if (instr->value > 0 && instr->value < program->num_values
		    && program->value_owned_slots
		    && program->value_owned_slots[instr->value] >= 0
		    && ((instr->kind == HIR_TAC_UNARY
			 && instr->op == HIR_OP_MAKE_SINGLETON_LIST)
			|| (program->value_ownership
			    && program->value_ownership[instr->value]
			       == JIT_OWNERSHIP_OWNED_PROPERTY)
			|| (instr->kind == HIR_TAC_BINARY
			    && instr->op == HIR_OP_LIST_ADD_TAIL
			    && jit_list_tail_consume_mode(program, instr)
			       != JIT_LIST_APPEND_CONSUME_HOME))) {
		    MIR_reg_t raw = append_raw_value(build, program, values,
			instr->value, deopt_values, &copy_serial);
		    MIR_op_t type;

		    if (program->value_is_tagged
			&& program->value_is_tagged[instr->value])
			type = MIR_new_mem_op(build->context, tag_t,
			    jit_tag_offset(program, instr->value),
			    deopt_values, 0, 1);
		    else
			type = MIR_new_int_op(build->context,
			    program->value_types[instr->value]);
		    append(build, MIR_new_insn(build->context, MIR_MOV,
			MIR_new_mem_op(build->context, MIR_T_I32,
			    program->value_owned_slots[instr->value]
				* sizeof(unsigned),
			    build->home_capacities, 0, 1),
			MIR_new_int_op(build->context, 0)));
		    append(build, MIR_new_call_insn(build->context, 6,
			MIR_new_ref_op(build->context,
			    build->proto_owned_replace),
			MIR_new_ref_op(build->context,
			    build->import_owned_replace),
			MIR_new_reg_op(build->context, owned_values),
			MIR_new_int_op(build->context,
			    program->value_owned_slots[instr->value]),
			MIR_new_reg_op(build->context, raw), type));
		    if (instr->kind == HIR_TAC_UNARY
			&& instr->op == HIR_OP_MAKE_SINGLETON_LIST) {
			int capacity = jit_fixed_list_capacity(program, instr);

			if (capacity > 1)
			    append(build, MIR_new_insn(build->context, MIR_MOV,
				MIR_new_mem_op(build->context, MIR_T_I32,
				    program->value_owned_slots[instr->value]
					* sizeof(unsigned),
				    build->home_capacities, 0, 1),
				MIR_new_int_op(build->context, capacity)));
		    }
		}
		{
		    int operands[3] = { instr->src1, instr->src2, instr->src3 };
		    unsigned char last_uses[3] = {
			JIT_LAST_USE_SRC1, JIT_LAST_USE_SRC2, JIT_LAST_USE_SRC3
		    };
		    int operand;

		    for (operand = 0; operand < 3; operand++) {
			int value = operands[operand];
			int previous;

			if (!(instr->owned_last_use & last_uses[operand])
			    || instr->kind == HIR_TAC_CALL
			    || instr->kind == HIR_TAC_CALL_VERB
			    || (!jit_value_is_owned_string_result(program, value)
				&& !jit_value_is_owned_list_result(program, value)
				&& !jit_value_is_owned_index_result(program, value)))
			    continue;
			if (((instr->op == HIR_OP_LIST_ADD_TAIL && operand == 0)
			     || (instr->op == HIR_OP_ADD
				 && program->value_types
				 && program->value_types[instr->value] == TYPE_STR
				 && ((operand == 0 && (instr->owned_last_use & JIT_LAST_USE_SRC1))
				     || (operand == 1 && (instr->owned_last_use & JIT_LAST_USE_SRC2)))))
			    && program->value_owned_slots
			    && program->value_owned_slots[instr->value] >= 0)
			    continue;
			for (previous = 0; previous < operand; previous++)
			    if (operands[previous] == value
				|| (program->value_owner_root
				    && (!program->value_ownership
					|| ((program->value_ownership[value] == JIT_OWNERSHIP_OWNED
					     || program->value_ownership[value] == JIT_OWNERSHIP_OWNED_PROPERTY)
					    && (program->value_ownership[operands[previous]] == JIT_OWNERSHIP_OWNED
						|| program->value_ownership[operands[previous]] == JIT_OWNERSHIP_OWNED_PROPERTY)))
				    && program->value_owner_root[value] >= 0
				    && program->value_owner_root[operands[previous]]
				       == program->value_owner_root[value]))
				break;
			if (previous != operand)
			    continue;
			{
			    MIR_reg_t raw = append_raw_value(build, program, values,
				value, deopt_values, &copy_serial);
			    MIR_op_t type = program->value_is_tagged[value]
				? MIR_new_mem_op(build->context, tag_t,
				    jit_tag_offset(program, value),
				    deopt_values, 0, 1)
				: MIR_new_int_op(build->context,
				    program->value_types[value]);
			    int owner = jit_resolve_owner_slot(program, value);
			    int result_owner = jit_resolve_owner_slot(program,
				instr->value);

			    if ((owner >= 0 && result_owner == owner)
				|| (program->value_owner_root
				    && (!program->value_ownership
					|| ((program->value_ownership[value] == JIT_OWNERSHIP_OWNED
					     || program->value_ownership[value] == JIT_OWNERSHIP_OWNED_PROPERTY)
					    && (program->value_ownership[instr->value] == JIT_OWNERSHIP_OWNED
						|| program->value_ownership[instr->value] == JIT_OWNERSHIP_OWNED_PROPERTY)))
				    && value > 0 && value < program->num_values
				    && instr->value > 0
				    && instr->value < program->num_values
				    && program->value_owner_root[value] > 0
				    && program->value_owner_root[value]
				       == program->value_owner_root[instr->value]))
				continue;

			    append(build, MIR_new_call_insn(build->context, 6,
				MIR_new_ref_op(build->context,
				    build->proto_discard_owned),
				MIR_new_ref_op(build->context,
				    build->import_discard_owned),
				MIR_new_reg_op(build->context, owned_values),
				MIR_new_int_op(build->context, owner),
				MIR_new_reg_op(build->context, raw), type));
			}
		    }
		}
		if (jit_value_is_dead_owned_list(program, instr)) {
		    MIR_reg_t raw = append_raw_value(build, program, values,
			instr->value, deopt_values, &copy_serial);
		    int owner = jit_resolve_owner_slot(program, instr->value);

		    append(build, MIR_new_call_insn(build->context, 6,
			MIR_new_ref_op(build->context,
			    build->proto_discard_owned),
			MIR_new_ref_op(build->context,
			    build->import_discard_owned),
			MIR_new_reg_op(build->context, owned_values),
			MIR_new_int_op(build->context, owner),
			MIR_new_reg_op(build->context, raw),
			MIR_new_int_op(build->context, TYPE_LIST)));
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
	    else if (block->num_successors == 0
		     && (!block->last
			 || (block->last->kind != HIR_TAC_RETURN
			     && block->last->kind != HIR_TAC_RETURN0)))
		append_return_zero(build, result, status, common_return);
    }

    append(build, fallback);
    append(build, MIR_new_insn(build->context, MIR_MOV,
			      MIR_new_mem_op(build->context, MIR_T_I32,
					     0, deopt_map_out, 0, 1),
			      MIR_new_int_op(build->context, 0)));
    return_status(build, status, common_return, JIT_RUN_FALLBACK);
    while (negative_mod_exits) {
	JITNegativeModExit *next = negative_mod_exits->next;
	MIR_reg_t magnitude, remainder;
	char name[32];

	sprintf(name, "cold_mod_magnitude%d", copy_serial++);
	magnitude = new_reg(build, name);
	sprintf(name, "cold_mod_remainder%d", copy_serial++);
	remainder = new_reg(build, name);
	append(build, negative_mod_exits->label);
	append(build, MIR_new_insn(build->context, MIR_NEG,
	    MIR_new_reg_op(build->context, magnitude),
	    MIR_new_reg_op(build->context, negative_mod_exits->source)));
	append(build, MIR_new_insn(build->context, MIR_AND,
	    MIR_new_reg_op(build->context, remainder),
	    MIR_new_reg_op(build->context, magnitude),
	    MIR_new_int_op(build->context, (Num) negative_mod_exits->mask)));
	append(build, MIR_new_insn(build->context, MIR_NEG,
	    MIR_new_reg_op(build->context, negative_mod_exits->destination),
	    MIR_new_reg_op(build->context, remainder)));
	append(build, MIR_new_insn(build->context, MIR_JMP,
	    MIR_new_label_op(build->context, negative_mod_exits->continuation)));
	myfree(negative_mod_exits, M_PROGRAM);
	negative_mod_exits = next;
    }
    while (tick_batch_exits) {
	JITTickBatchExit *next = tick_batch_exits->next;

	append(build, tick_batch_exits->label);
	append(build, MIR_new_insn(build->context, MIR_SUB,
	    MIR_new_reg_op(build->context, tick_result),
	    MIR_new_reg_op(build->context, tick_result),
	    MIR_new_int_op(build->context, 1)));
	append(build, MIR_new_insn(build->context, MIR_BLE,
	    MIR_new_label_op(build->context, tick_batch_exits->tick_abort),
	    MIR_new_reg_op(build->context, tick_result),
	    MIR_new_int_op(build->context, 0)));
	append(build, MIR_new_insn(build->context, MIR_BT,
	    MIR_new_label_op(build->context, tick_batch_exits->seconds_abort),
	    MIR_new_mem_op(build->context, MIR_T_I32, 0, timed_out, 0, 1)));
	append(build, MIR_new_insn(build->context, MIR_MOV,
	    MIR_new_reg_op(build->context, tick_result),
	    MIR_new_int_op(build->context, 0)));
	append(build, MIR_new_insn(build->context, MIR_JMP,
	    MIR_new_label_op(build->context, tick_batch_exits->tick_abort)));
	myfree(tick_batch_exits, M_PROGRAM);
	tick_batch_exits = next;
    }
    append_status_exits(build, status_exits, program, values, labels, source_location,
			deopt_map_out, deopt_values, error_out, status,
			common_return);
    append_shared_return_stubs(build, status, common_return);
    append(build, common_return);
    append(build, MIR_new_insn(build->context, MIR_MOV,
	MIR_new_mem_op(build->context, MIR_T_I32, 0, ticks, 0, 1),
	MIR_new_reg_op(build->context, tick_result)));
    append(build, MIR_new_ret_insn(build->context, 1,
				  MIR_new_reg_op(build->context, status)));
    finish_build(build);
    myfree(deferred_region_lists, M_PROGRAM);
    myfree(resume_continuations, M_PROGRAM);
    myfree(resume_entries, M_PROGRAM);
    myfree(labels, M_PROGRAM);
    myfree(values, M_PROGRAM);
    return 1;
}

JITProgram *
jit_program_unsupported_with_diagnostic(const char *reason, const char *diagnostic)
{
    JITProgram *program = mymalloc(sizeof(JITProgram), M_PROGRAM);

    memset(program, 0, sizeof(JITProgram));
    program->pool_index = JIT_NO_POOL;
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

static void
jit_program_release_native(JITProgram *program)
{
    if (!program)
	return;
    jit_pool_unregister(program);
    program->native_function = 0;
    program->machine_code = 0;
    program->machine_code_len = 0;
    jit_program_clear_region_exits(program);
}

static void
jit_free_instruction(JITInstruction *instr)
{
    JITCopy *copy = instr->copies;

    while (copy) {
	JITCopy *next = copy->next;
	myfree(copy, M_PROGRAM);
	copy = next;
    }
    if (instr->kind == HIR_TAC_CONST && instr->literal_type == TYPE_STR
	&& instr->literal)
	free_str((const char *) (intptr_t) instr->literal);
    else if (instr->kind == HIR_TAC_CONST && instr->literal_type == TYPE_LIST
	     && instr->literal) {
	Var value;
	value.type = TYPE_LIST;
	value.v.list = (Var *) (intptr_t) instr->literal;
	free_var(value);
    }
    myfree(instr, M_PROGRAM);
}

static void
jit_program_free_retained_constants(JITProgram *program)
{
    JITInstruction *instr = program->retained_constants;

    while (instr) {
	JITInstruction *next = instr->next;
	jit_free_instruction(instr);
	instr = next;
    }
    program->retained_constants = 0;
}

static void
jit_program_release_ir(JITProgram *program, int retain_constants)
{
    JITBlock *block = program->blocks;

    while (block) {
	JITBlock *next_block = block->next;
	JITInstruction *instr = block->first;

	while (instr) {
	    JITInstruction *next = instr->next;

	    if (retain_constants && instr->kind == HIR_TAC_CONST
		&& (instr->literal_type == TYPE_STR
		    || instr->literal_type == TYPE_LIST) && instr->literal) {
		instr->next = program->retained_constants;
		program->retained_constants = instr;
	    } else
		jit_free_instruction(instr);
	    instr = next;
	}
	myfree(block, M_PROGRAM);
	block = next_block;
    }
    program->blocks = program->last_block = 0;
    if (program->value_ownership) {
	myfree(program->value_ownership, M_PROGRAM);
	program->value_ownership = 0;
    }
    if (program->value_owner_root) {
	myfree(program->value_owner_root, M_PROGRAM);
	program->value_owner_root = 0;
    }
    if (program->value_use_counts) {
	myfree(program->value_use_counts, M_PROGRAM);
	program->value_use_counts = 0;
    }
    if (program->value_escape_flags) {
	myfree(program->value_escape_flags, M_PROGRAM);
	program->value_escape_flags = 0;
    }
    if (program->value_owned_slots) {
	myfree(program->value_owned_slots, M_PROGRAM);
	program->value_owned_slots = 0;
    }
    if (program->value_is_int_list) {
	myfree(program->value_is_int_list, M_PROGRAM);
	program->value_is_int_list = 0;
    }
}

static void
jit_program_find_borrowed_locals(JITProgram *program)
{
    unsigned char *used;
    JITBlock *block;
    int count = 0;
    int i;

    if (program->borrowed_local_slots || program->num_vars <= 0)
	return;
    used = mymalloc(program->num_vars, M_PROGRAM);
    memset(used, 0, program->num_vars);
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_LOAD_LOCAL && instr->local_id >= 0
		&& instr->local_id < program->num_vars)
		used[instr->local_id] = 1;
	    if (instr == block->last)
		break;
	}
    }
    for (i = 0; i < program->num_vars; i++)
	if (used[i])
	    count++;
    if (count) {
	int next = 0;

	program->borrowed_local_slots = mymalloc(sizeof(int) * count, M_PROGRAM);
	for (i = 0; i < program->num_vars; i++)
	    if (used[i])
		program->borrowed_local_slots[next++] = i;
	program->num_borrowed_locals = count;
    }
    myfree(used, M_PROGRAM);
}

static int
jit_program_restore_ir(JITProgram *program)
{
    JITProgram *rebuilt;

    if (program->blocks)
	return 1;
    if (!program->bytecode_program)
	return 1;
    rebuilt = compile_program_to_jit(program->bytecode_program);
    if (!rebuilt || !rebuilt->eligible
	|| rebuilt->num_values != program->num_values
	|| rebuilt->num_blocks != program->num_blocks
	|| rebuilt->num_deopt_maps != program->num_deopt_maps) {
	jit_program_free(rebuilt);
	return 0;
    }
    program->blocks = rebuilt->blocks;
    program->last_block = rebuilt->last_block;
    rebuilt->blocks = rebuilt->last_block = 0;
    program->value_ownership = rebuilt->value_ownership;
    rebuilt->value_ownership = 0;
    program->value_owner_root = rebuilt->value_owner_root;
    rebuilt->value_owner_root = 0;
    program->value_use_counts = rebuilt->value_use_counts;
    rebuilt->value_use_counts = 0;
    program->value_escape_flags = rebuilt->value_escape_flags;
    rebuilt->value_escape_flags = 0;
    program->value_owned_slots = rebuilt->value_owned_slots;
    rebuilt->value_owned_slots = 0;
    program->value_is_int_list = rebuilt->value_is_int_list;
    rebuilt->value_is_int_list = 0;
    jit_program_free(rebuilt);
    return 1;
}

void
jit_program_free(JITProgram *program)
{
    JITRegionSite *region_site;

    if (!program)
	return;

    if (program->specialization_pending) {
	JITProgram **link = &jit_specialization_queue;

	while (*link && *link != program)
	    link = &(*link)->specialization_next;
	if (*link)
	    *link = program->specialization_next;
	program->specialization_pending = 0;
	program->specialization_next = 0;
    }

    jit_program_release_native(program);
    jit_program_release_ir(program, 0);
    if (program->resume_map_index)
	myfree(program->resume_map_index, M_PROGRAM);
    if (program->deopt_maps)
	{
	    int i;

	    for (i = 0; i < program->num_deopt_maps; i++) {
		if (program->deopt_maps[i].local_values)
		    myfree(program->deopt_maps[i].local_values, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].tagged_values)
		    myfree(program->deopt_maps[i].tagged_values, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].stack_values)
		    myfree(program->deopt_maps[i].stack_values, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].stack_types)
		    myfree(program->deopt_maps[i].stack_types, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].stack_slots)
		    myfree(program->deopt_maps[i].stack_slots, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].local_owner_slots)
		    myfree(program->deopt_maps[i].local_owner_slots, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].stack_owner_slots)
		    myfree(program->deopt_maps[i].stack_owner_slots, M_PROGRAM);
		if ((!program->reconstruction_states
		     || program->reconstruction_states[
			 program->deopt_maps[i].reconstruction_state]
			.representative_map == i)
		    && program->deopt_maps[i].stack_boundary_ownership)
		    myfree(program->deopt_maps[i].stack_boundary_ownership,
			   M_PROGRAM);
		if (program->deopt_maps[i].native_resume) {
		    int literal;

		    if (program->deopt_maps[i].native_resume->cached_verb)
			free_str(program->deopt_maps[i].native_resume->cached_verb);
		    if (program->deopt_maps[i].native_resume->capture_actions)
			myfree(program->deopt_maps[i].native_resume->capture_actions,
			       M_PROGRAM);
		    if (program->deopt_maps[i].native_resume->required_homes)
			myfree(program->deopt_maps[i].native_resume->required_homes,
			       M_PROGRAM);
		    if (program->deopt_maps[i].native_resume->values)
			myfree(program->deopt_maps[i].native_resume->values,
			       M_PROGRAM);
		    for (literal = 0;
			 literal < program->deopt_maps[i].native_resume->num_literals;
			 literal++) {
			JITResumeLiteral *resume_literal =
			    &program->deopt_maps[i].native_resume->literals[literal];

			if (resume_literal->literal_type == TYPE_STR
			    || resume_literal->literal_type == TYPE_LIST
#ifdef WAIF_CORE
			    || resume_literal->literal_type == TYPE_WAIF
#endif
			    ) {
			    Var value;

			    value.type = resume_literal->literal_type;
			    value.v.num = resume_literal->literal;
			    free_var(value);
			}
		    }
		    if (program->deopt_maps[i].native_resume->literals)
			myfree(program->deopt_maps[i].native_resume->literals,
			       M_PROGRAM);
		    myfree(program->deopt_maps[i].native_resume, M_PROGRAM);
		}
	    }
	    myfree(program->deopt_maps, M_PROGRAM);
	}
    if (program->reconstruction_states)
	myfree(program->reconstruction_states, M_PROGRAM);
    if (program->status_locations)
	myfree(program->status_locations, M_PROGRAM);
    if (program->value_types)
	myfree(program->value_types, M_PROGRAM);
    if (program->value_is_tagged)
	myfree(program->value_is_tagged, M_PROGRAM);
    if (program->value_constant_bits)
	myfree(program->value_constant_bits, M_PROGRAM);
    if (program->constant_value_ids)
	myfree(program->constant_value_ids, M_PROGRAM);
    if (program->value_constants)
	myfree(program->value_constants, M_PROGRAM);
    if (program->value_tag_slots)
	myfree(program->value_tag_slots, M_PROGRAM);
    if (program->borrowed_local_slots)
	myfree(program->borrowed_local_slots, M_PROGRAM);
    if (program->usage)
	myfree(program->usage, M_PROGRAM);
    region_site = program->region_sites;
    while (region_site) {
	JITRegionSite *next = region_site->next;

	myfree(region_site, M_PROGRAM);
	region_site = next;
    }
    jit_program_free_retained_constants(program);
    if (program->reason)
	free_str(program->reason);
    if (program->diagnostic)
	free_str(program->diagnostic);
    myfree(program, M_PROGRAM);
}

static size_t
jit_program_metadata_bytes(JITProgram *program)
{
    size_t bytes = 0;
    int i;
    JITBlock *block;

    if (!program)
	return 0;
    bytes = sizeof(JITProgram);
    if (program->reason)
	bytes += memo_strlen(program->reason) + 1;
    if (program->diagnostic)
	bytes += memo_strlen(program->diagnostic) + 1;
    bytes += sizeof(JITDeoptMap) * program->num_deopt_maps;
    bytes += sizeof(JITResumeMapEntry) * program->num_resume_map_entries;
    bytes += sizeof(JITReconstructionState)
	* program->num_reconstruction_states;
    bytes += sizeof(JITSourceLocation) * program->num_status_locations;
    if (program->value_types)
	bytes += sizeof(int16_t) * program->num_values;
    if (program->value_is_tagged)
	bytes += sizeof(unsigned char) * program->num_values;
    if (program->value_constant_bits)
	bytes += (program->num_values + 7) / 8;
    if (program->constant_value_ids)
	bytes += sizeof(uint16_t) * program->num_constant_values;
    if (program->value_constants)
	bytes += sizeof(Num) * program->num_constant_values;
    if (program->value_tag_slots)
	bytes += sizeof(uint16_t) * program->num_values;
    if (program->value_ownership)
	bytes += sizeof(unsigned char) * program->num_values;
    if (program->value_owner_root)
	bytes += sizeof(int) * program->num_values;
    if (program->value_use_counts)
	bytes += sizeof(unsigned int) * program->num_values;
    if (program->value_escape_flags)
	bytes += sizeof(unsigned char) * program->num_values;
    if (program->value_owned_slots)
	bytes += sizeof(int) * program->num_values;
    if (program->value_is_int_list)
	bytes += sizeof(unsigned char) * program->num_values;
    if (program->borrowed_local_slots)
	bytes += sizeof(int) * program->num_borrowed_locals;
    if (program->usage)
	bytes += sizeof(JITProgramUsage);
    {
	JITRegionSite *site;

	for (site = program->region_sites; site; site = site->next)
	    bytes += sizeof(*site);
    }
    bytes += sizeof(JITRegionExit) * program->region_exit_capacity;

    bytes += sizeof(const char *) * program->region_literal_capacity;
    for (i = 0; i < program->num_region_literals; i++)
	bytes += memo_strlen(program->region_literals[i]) + 1;
    for (i = 0; i < program->num_region_exits; i++) {
	JITRegionExit *exit = &program->region_exits[i];
	int frame;

	bytes += sizeof(JITRegionExitFrame) * exit->num_frames;
	for (frame = 0; frame < exit->num_frames; frame++)
	    bytes += sizeof(JITRegionExitValue)
		* exit->frames[frame].num_values;
    }
    for (i = 0; i < program->num_deopt_maps; i++) {
	JITDeoptMap *map = &program->deopt_maps[i];
	int owns_state = !program->reconstruction_states
	    || program->reconstruction_states[map->reconstruction_state]
	       .representative_map == i;

	if (map->local_values)
	    bytes += sizeof(JITLocalValue) * map->num_local_values;
	if (owns_state && map->tagged_values)
	    bytes += sizeof(int) * map->num_tagged_values;
	if (owns_state && map->stack_values)
	    bytes += sizeof(int) * map->stack_depth;
	if (owns_state && map->stack_types)
	    bytes += sizeof(var_type) * map->stack_depth;
	if (owns_state && map->stack_slots)
	    bytes += sizeof(ResumeStackSlot) * map->stack_depth;
	if (owns_state && map->local_owner_slots)
	    bytes += sizeof(int) * map->num_locals;
	if (owns_state && map->stack_owner_slots)
	    bytes += sizeof(int) * map->stack_depth;
	if (owns_state && map->stack_boundary_ownership)
	    bytes += map->stack_depth;
	if (map->native_resume) {
	    bytes += sizeof(JITNativeResume);
	    if (map->native_resume->capture_actions)
		bytes += sizeof(JITResumeCaptureAction)
		    * map->native_resume->num_capture_actions;
	    if (map->native_resume->required_homes)
		bytes += sizeof(int) * map->native_resume->num_required_homes;
	    if (map->native_resume->values)
		bytes += sizeof(JITResumeValue) * map->native_resume->num_values;
	    if (map->native_resume->literals)
		bytes += sizeof(JITResumeLiteral) * map->native_resume->num_literals;
	}
    }
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
    {
	JITInstruction *instr;

	for (instr = program->retained_constants; instr; instr = instr->next)
	    bytes += sizeof(JITInstruction);
    }
    return bytes;
}

void
jit_program_stats(JITProgram *program, JITProgramStats *stats)
{
    if (!stats)
	return;
    memset(stats, 0, sizeof(*stats));
    if (!program)
	return;
    if (program->usage) {
	int reason;

	stats->entries = program->usage->entries;
	stats->completions = program->usage->completions;
	stats->vm_calls = program->usage->vm_calls;
	stats->deopts = program->usage->deopts;
	for (reason = 0; reason < JIT_DEOPT_NUM_REASONS; reason++)
	    stats->deopts_by_reason[reason]
		= program->usage->deopts_by_reason[reason];
	stats->last_used_generation = program->usage->last_used_generation;
	stats->last_used_time = program->usage->last_used_time;
	stats->continuation_captures = program->usage->continuation_captures;
	stats->continuation_resumes = program->usage->continuation_resumes;
	stats->continuation_materializations
	    = program->usage->continuation_materializations;
	stats->continuation_fast_suspends
	    = program->usage->continuation_fast_suspends;
	stats->native_chain_calls = program->usage->native_chain_calls;
	stats->native_chain_returns = program->usage->native_chain_returns;
	stats->native_chain_promotions = program->usage->native_chain_promotions;
	stats->native_chain_max_depth = program->usage->native_chain_max_depth;
    }
    stats->compile_attempts = program->compile_attempts;
    stats->compile_successes = program->compile_successes;
    stats->compile_failures = program->compile_failures;
    stats->compile_time_us = program->compile_time_us;
    stats->potential_exit_sites = program->potential_exit_sites;
    stats->elided_exit_sites = program->elided_exit_sites;
    stats->type_guard_sites = program->type_guard_sites;
    stats->eliminated_type_guard_sites
	= program->eliminated_type_guard_sites;
    stats->reconstruction_states = program->num_reconstruction_states;
    stats->metadata_bytes = jit_program_metadata_bytes(program);
    stats->runtime_bytes = program->active_runtime_bytes;
    stats->native_chain_active_frames = program->active_native_frames;
    stats->native_chain_frame_bytes = program->active_native_frame_bytes;
    stats->machine_code_bytes = program->machine_code_len;
    stats->pool_index = program->pool_index < JIT_CONTEXT_COUNT
	? (int) program->pool_index : -1;
    stats->residency_heat = jit_program_normalized_heat(program);
    stats->residency_heat_epoch = program->residency_heat_epoch;
    if (program->pool_index < JIT_CONTEXT_COUNT
	&& jit_pools[program->pool_index].context
	&& jit_pools[program->pool_index].total_machine_code_bytes > 0
	&& program->machine_code_len > 0) {
	JITPool *pool = &jit_pools[program->pool_index];
	size_t total_allocated = _MIR_code_allocated_size(pool->context);
	size_t share = (size_t) (((uint64_t) total_allocated * program->machine_code_len)
				 / pool->total_machine_code_bytes);
	stats->native_allocated_bytes = share > program->machine_code_len
	    ? share : program->machine_code_len;
    } else {
	stats->native_allocated_bytes = program->machine_code_len;
    }
    {
	JITContinuationFrame *frame;

	for (frame = continuation_frames; frame; frame = frame->next)
	    if (frame->program == program) {
		stats->active_continuations++;
		stats->continuation_bytes += sizeof(*frame)
		    + sizeof(Var) * (frame->retained_capacity
			+ frame->spare_retained_capacity);
	    }
    }
    stats->accounted_bytes = stats->metadata_bytes + stats->runtime_bytes
	+ stats->native_allocated_bytes + stats->continuation_bytes
	+ stats->native_chain_frame_bytes;
}

int
jit_program_bytes(JITProgram *program)
{
    JITProgramStats stats;

    jit_program_stats(program, &stats);
    return stats.accounted_bytes > INT_MAX ? INT_MAX : stats.accounted_bytes;
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

uint64_t
jit_program_compiled_generation(JITProgram *program)
{
    return program && program->state == JIT_STATE_COMPILED
	&& program->native_function
	&& program->pool_index < JIT_CONTEXT_COUNT
	&& program->pool_generation == jit_pools[program->pool_index].generation
	&& program->protection_generation == builtin_protection_generation()
	&& !jit_pool_rotation_blocks_native_entry()
	? program->pool_generation : 0;
}

int
jit_program_may_error(JITProgram *program)
{
    return program && program->may_error;
}

int
jit_program_is_direct_leaf(JITProgram *program)
{
    JITBlock *block;
    int release_ir;
    int direct_leaf = 1;

    if (!program || !program->eligible)
	return 0;

    if (program->direct_leaf)
	return program->direct_leaf > 0;
    release_ir = !program->blocks;
    if (release_ir && !jit_program_restore_ir(program))
	return 0;
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_CALL
		|| instr->kind == HIR_TAC_CALL_VERB
		|| instr->kind == HIR_TAC_PUT_PROP
		|| instr->kind == HIR_TAC_DEOPT) {
		direct_leaf = 0;
		break;
	    }
	    if (instr == block->last)
		break;
	}
	if (!direct_leaf)
	    break;
    }
    if (release_ir)
	jit_program_release_ir(program, 0);
    program->direct_leaf = direct_leaf ? 1 : -1;
    return direct_leaf;
}

static int
jit_region_leaf_loop_header(JITProgram *program, JITBlock *block)
{
    JITInstruction *instr;

    for (instr = block->first; instr; instr = instr->next) {
	if (instr->kind == HIR_TAC_GUARD_TYPE && instr->deopt_map > 0
	    && instr->deopt_map < program->num_deopt_maps)
	    return 1;
	if (instr == block->last)
	    break;
    }
    return 0;
}

static int
jit_region_leaf_terminal_put(JITBlock *block, JITInstruction *instr)
{
    JITInstruction *ret = instr->next;

    return block->num_successors == 0 && ret && ret == block->last
	&& ret->kind == HIR_TAC_RETURN && ret->src1 == instr->value;
}

static int
jit_region_leaf_visit(JITProgram *program, JITBlock **blocks,
		      unsigned char *colors, int max_block, int id,
		      int *instructions, int allow_verb_calls)
{
    JITBlock *block;
    JITInstruction *instr;
    int successor;

    if (id <= 0 || id > max_block || !blocks[id])
	return 0;
    if (colors[id] == 1)
	return jit_region_leaf_loop_header(program, blocks[id]);
    if (colors[id] == 2)
	return 1;
    colors[id] = 1;
    block = blocks[id];
    for (instr = block->first; instr; instr = instr->next) {
	if (++*instructions > 128
	    || instr->kind == HIR_TAC_CALL
	    || (instr->kind == HIR_TAC_CALL_VERB && !allow_verb_calls)
	    || (instr->kind == HIR_TAC_PUT_PROP
		&& !jit_region_leaf_terminal_put(block, instr))
	    || instr->kind == HIR_TAC_INDEX_SET
	    || instr->kind == HIR_TAC_RANGE_SET
	    || (instr->kind == HIR_TAC_UNARY
		&& (instr->op == HIR_OP_FORK
		    || instr->op == HIR_OP_TICKS_LEFT
		    || instr->op == HIR_OP_SECONDS_LEFT
		    || instr->op == HIR_OP_TIME
		    || instr->op == HIR_OP_GET_PROP)))
	    return 0;
	if (instr == block->last)
	    break;
    }
    for (successor = 0; successor < block->num_successors; successor++)
	if (!jit_region_leaf_visit(program, blocks, colors, max_block,
		block->successors[successor], instructions, allow_verb_calls))
	    return 0;
    colors[id] = 2;
    return 1;
}

static int
jit_program_is_region_kind(JITProgram *program, int allow_verb_calls)
{
    JITBlock *block;
    JITBlock **blocks;
    unsigned char *colors;
    int instructions = 0;
    int max_block = 0;
    int release_ir;
    int eligible = 0;

    if (!program || !program->eligible)
	return 0;
    release_ir = !program->blocks;
    if (release_ir && !jit_program_restore_ir(program))
	return 0;
    for (block = program->blocks; block; block = block->next)
	if (block->id > max_block)
	    max_block = block->id;
    if (!program->blocks || max_block <= 0)
	goto done;
    blocks = mymalloc((max_block + 1) * sizeof(JITBlock *), M_PROGRAM);
    colors = mymalloc(max_block + 1, M_PROGRAM);
    memset(blocks, 0, (max_block + 1) * sizeof(JITBlock *));
    memset(colors, 0, max_block + 1);
    for (block = program->blocks; block; block = block->next) {
	if (block->id <= 0 || block->id > max_block || blocks[block->id])
	    goto free_arrays;
	blocks[block->id] = block;
    }
    eligible = jit_region_leaf_visit(program, blocks, colors, max_block,
	    program->blocks->id, &instructions, allow_verb_calls);

free_arrays:
    myfree(colors, M_PROGRAM);
    myfree(blocks, M_PROGRAM);
done:
    if (release_ir)
	jit_program_release_ir(program, 0);
    return eligible;
}

int
jit_program_is_region_leaf(JITProgram *program)
{
    return jit_program_is_region_kind(program, 0);
}

static int
jit_program_is_recursive_region_candidate(JITProgram *program)
{
    JITBlock *block;
    int calls = 0;
    int release_ir;
    int eligible = 0;

    if (!jit_program_is_region_kind(program, 1))
	return 0;
    release_ir = !program->blocks;
    if (release_ir && !jit_program_restore_ir(program))
	return 0;
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	for (instr = block->first; instr; instr = instr->next) {
	    if (instr->kind == HIR_TAC_CALL_VERB) {
		int arguments[JIT_REGION_MAX_ARGUMENTS];
		int count = 0;

		if (++calls > JIT_REGION_MAX_CALLS
		    || !jit_region_is_this(program, instr->src1, 0)
		    || !jit_fixed_list_values(program, instr->src3,
			arguments, &count))
		    goto done;
	    }
	    if (instr == block->last)
		break;
	}
    }
    eligible = calls > 0;
done:
    if (release_ir)
	jit_program_release_ir(program, 0);
    return eligible;
}

static JITRegionSite *
jit_region_site(JITProgram *program, int map_id, int create)
{
    JITRegionSite *site;

    if (!program || map_id <= 0 || map_id >= program->num_deopt_maps)
	return 0;
    for (site = program->region_sites; site; site = site->next)
	if (site->map_id == map_id)
	    return site;
    if (!create)
	return 0;
    site = mymalloc(sizeof(*site), M_PROGRAM);
    memset(site, 0, sizeof(*site));
    site->map_id = map_id;
    site->next = program->region_sites;
    program->region_sites = site;
    return site;
}

#ifdef JIT_TESTING
void
jit_test_region_site_select(JITProgram *program, int map_id,
	Program *target_program, Objid receiver_class)
{
    JITRegionSite *site = jit_region_site(program, map_id, 1);
    JITDeoptMap *map = &program->deopt_maps[map_id];

    site->leaf = 1;
    site->hits = JIT_REGION_HOT_THRESHOLD;
    site->target_program = target_program;
    site->dispatch_epoch = db_dispatch_epoch();
    site->receiver_class = receiver_class;
    map->reason = JIT_DEOPT_VERB_CALL;
    map->stack_depth = 3;
    map->resume_key.site = 1;
    if (!map->native_resume) {
	map->native_resume = mymalloc(sizeof(JITNativeResume), M_PROGRAM);
	memset(map->native_resume, 0, sizeof(JITNativeResume));
    }
    map->native_resume->valid = 1;
    map->native_resume->cached_program = target_program;
    map->native_resume->cached_dispatch_epoch = site->dispatch_epoch;
    if (map->native_resume->cached_verb)
	free_str(map->native_resume->cached_verb);
    map->native_resume->cached_verb = str_dup("test_region");
}
#endif

void
jit_region_site_reset(JITProgram *program, int map_id)
{
    JITRegionSite *site = jit_region_site(program, map_id, 0);

    if (!site)
	return;
    site->leaf = 0;
    site->hits = 0;
    site->rotation_requested = 0;
    site->spliced_generation = 0;
    site->target_program = 0;
    site->dispatch_epoch = 0;
    site->receiver_class = NOTHING;
}

static int
jit_region_depends_on(JITProgram *root, JITProgram *target, int depth,
		      uint64_t dispatch_epoch)
{
    JITRegionSite *site;

    if (root == target)
	return 1;
    if (!root || depth >= JIT_REGION_MAX_DEPTH)
	return 0;
    for (site = root->region_sites; site; site = site->next)
	if (site->dispatch_epoch == dispatch_epoch && site->target_program
	    && site->target_program->jit
	    && jit_region_depends_on(site->target_program->jit, target,
		depth + 1, dispatch_epoch))
	    return 1;
    return 0;
}

static void
jit_region_request_specialization(JITProgram *changed)
{
    uint64_t dispatch_epoch = db_dispatch_epoch();
    unsigned i;

    for (i = 0; i < JIT_CONTEXT_COUNT; i++) {
	JITProgram *program;

	for (program = jit_pools[i].active_head; program;
	     program = program->pool_next)
	    if (!program->specialization_pending
		&& jit_region_depends_on(program, changed, 0,
		    dispatch_epoch)) {
		program->specialization_pending = 1;
		program->specialization_epoch = dispatch_epoch;
		program->specialization_next = jit_specialization_queue;
		jit_specialization_queue = program;
	    }
    }
}

int
jit_region_site_record_hit(JITProgram *program, int map_id,
			   JITProgram *target)
{
    JITRegionSite *site = jit_region_site(program, map_id, 1);

    if (!site)
	return 0;
    if (!site->leaf)
	site->leaf = (jit_program_is_region_leaf(target)
	    || jit_program_is_recursive_region_candidate(target)) ? 1 : -1;
    if (site->leaf < 0 || site->hits == UCHAR_MAX)
	return 1;
    site->hits++;
    if (site->hits >= JIT_REGION_HOT_THRESHOLD && !site->target_program) {
	JITNativeResume *resume = program->deopt_maps[map_id].native_resume;

	if (resume && resume->cached_program
	    && resume->cached_program->jit == target
	    && resume->cached_dispatch_epoch == db_dispatch_epoch()) {
	    site->target_program = resume->cached_program;
	    site->dispatch_epoch = resume->cached_dispatch_epoch;
	    site->receiver_class = resume->cached_class;
	}
    }
    if (site->hits >= JIT_REGION_HOT_THRESHOLD
	&& site->target_program
	&& !site->rotation_requested
	&& program->state == JIT_STATE_COMPILED) {
	site->rotation_requested = 1;
	jit_region_request_specialization(program);
    }
    return site->hits >= JIT_REGION_HOT_THRESHOLD && site->target_program;
}

static int
jit_region_site_snapshot(JITProgram *program, int map_id,
			 Program **target_program, Objid *receiver_class,
			 uint64_t *dispatch_epoch)
{
    JITRegionSite *site = jit_region_site(program, map_id, 0);

    if (!site || !site->target_program || !site->dispatch_epoch)
	return 0;
    *target_program = site->target_program;
    *receiver_class = site->receiver_class;
    *dispatch_epoch = site->dispatch_epoch;
    return 1;
}

int
jit_region_site_status(JITProgram *program, int map_id, int *leaf,
		       unsigned *hits, uint64_t *spliced_generation)
{
    JITRegionSite *site = jit_region_site(program, map_id, 0);

    if (leaf)
	*leaf = site ? site->leaf : 0;
    if (hits)
	*hits = site ? site->hits : 0;
    if (spliced_generation)
	*spliced_generation = site ? site->spliced_generation : 0;
    return site && site->leaf > 0 && site->hits >= JIT_REGION_HOT_THRESHOLD;
}

static void
jit_region_site_mark_spliced(JITProgram *program, int map_id)
{
    JITRegionSite *site = jit_region_site(program, map_id, 0);

    if (site)
	site->spliced_generation = program->pool_generation;
}

static void
jit_program_sync_warmup(JITProgram *program)
{
    if (program->state == JIT_STATE_PENDING
	&& program->pool_generation != jit_pool_policy.logical_generation) {
	program->pool_generation = jit_pool_policy.logical_generation;
	program->pool_index = JIT_NO_POOL;
	program->warmup_count = 0;
    }
}

int
jit_program_admit_interpreter_entry(JITProgram *program)
{
    if (!program || !program->eligible)
	return 0;
    if (program->state == JIT_STATE_COMPILED)
	return 1;
    if (program->state != JIT_STATE_PENDING)
	return 0;
    jit_program_note_activity(program);
    jit_pool_policy.compilation_demand = 1;
    jit_program_sync_warmup(program);
    if (program->residency_heat >= jit_pool_policy.hot_threshold
	&& (unsigned) program->warmup_count + 1
	   < jit_pool_policy.effective_hot_threshold)
	program->warmup_count = jit_pool_policy.effective_hot_threshold - 1;
    if (program->warmup_count < jit_pool_policy.effective_hot_threshold)
	program->warmup_count++;
    return program->warmup_count >= jit_pool_policy.effective_hot_threshold
	&& !jit_pool_rotation_blocks_native_entry();
}

int
jit_program_claim_native_entry(JITProgram *program)
{
    if (!program || !program->eligible)
	return 0;
    if (program->state == JIT_STATE_COMPILED)
	return 1;
    if (program->state != JIT_STATE_PENDING
	|| jit_pool_rotation_blocks_native_entry())
	return 0;
    jit_program_sync_warmup(program);
    if ((unsigned) program->warmup_count + 1
	< jit_pool_policy.effective_hot_threshold)
	return 0;
    program->warmup_count = jit_pool_policy.effective_hot_threshold;
    return 1;
}

unsigned
jit_program_warmup_count(JITProgram *program)
{
    if (!program || program->state == JIT_STATE_COMPILED)
	return 0;
    jit_program_sync_warmup(program);
    return program->warmup_count;
}

uint64_t
jit_program_warmup_generation(JITProgram *program)
{
    if (!program)
	return 0;
    jit_program_sync_warmup(program);
    return program->pool_generation;
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

static int
jit_resume_key_compare(ResumeKey a, ResumeKey b)
{
    if (a.code_unit != b.code_unit)
	return a.code_unit < b.code_unit ? -1 : 1;
    return a.site < b.site ? -1 : a.site != b.site;
}

static int
jit_resume_map_compare(const void *left, const void *right)
{
    const JITResumeMapEntry *a = left, *b = right;
    int order = jit_resume_key_compare(a->key, b->key);

    /* Preserve the old scan's first eligible map for duplicate keys. */
    return order ? order : a->map_id < b->map_id ? -1 : a->map_id != b->map_id;
}

static int
jit_resume_map_candidate(JITDeoptMap *map)
{
    /* Protection can change without rebuilding metadata. Index specialized
       built-ins even while unprotected, and check protection at lookup. */
    return (map->reason == JIT_DEOPT_VERB_CALL
	    || map->reason == JIT_DEOPT_BUILTIN_CALL
	    || jit_deopt_map_is_specialized_builtin(map))
	&& map->resume_key.site && map->native_resume
	&& map->native_resume->valid && map->native_resume->rehydratable
	&& map->stack_depth >= (unsigned) jit_call_stack_operands(map);
}

static void
jit_program_index_resume_maps(JITProgram *program)
{
    int i, count = 0;

    /* Built lazily after metadata construction; IR/pool rotation preserves
       these maps. A replacement program owns a separate index. */
    for (i = 1; i < program->num_deopt_maps; i++)
	if (jit_resume_map_candidate(&program->deopt_maps[i]))
	    count++;
    if (count) {
	program->resume_map_index = mymalloc(sizeof(JITResumeMapEntry) * count,
					   M_PROGRAM);
	count = 0;
	for (i = 1; i < program->num_deopt_maps; i++)
	    if (jit_resume_map_candidate(&program->deopt_maps[i])) {
		program->resume_map_index[count].key = program->deopt_maps[i].resume_key;
		program->resume_map_index[count++].map_id = i;
	    }
	qsort(program->resume_map_index, count, sizeof(JITResumeMapEntry),
	      jit_resume_map_compare);
    }
    program->num_resume_map_entries = count;
    program->resume_map_index_ready = 1;
}

int
jit_program_resume_map(JITProgram *program, ResumeKey key)
{
    int low = 0, high;

    if (!program || key.site == 0)
	return -1;
    if (!program->resume_map_index_ready)
	jit_program_index_resume_maps(program);
    high = program->num_resume_map_entries;
    while (low < high) {
	int mid = low + (high - low) / 2;

	if (jit_resume_key_compare(program->resume_map_index[mid].key, key) < 0)
	    low = mid + 1;
	else
	    high = mid;
    }
    for (; low < program->num_resume_map_entries; low++) {
	JITResumeMapEntry *entry = &program->resume_map_index[low];
	JITDeoptMap *map = &program->deopt_maps[entry->map_id];

	if (jit_resume_key_compare(entry->key, key))
	    break;
	if ((map->reason == JIT_DEOPT_VERB_CALL || jit_deopt_map_bridges_builtin(map))
	    && jit_resume_map_candidate(map))
	    return entry->map_id;
    }
    return -1;
}

int
jit_program_has_location(JITProgram *program)
{
    return program && program->diagnostic_object >= 0
	&& program->diagnostic_verb > 0;
}

void
jit_program_note_location(JITProgram *program, Objid oid, unsigned verb)
{
    if (!program || oid < 0 || verb == 0)
	return;
    if (program->diagnostic_object == oid && program->diagnostic_verb == verb)
	return;
    program->diagnostic_object = oid;
    program->diagnostic_verb = verb;
}

static void
jit_program_finalize_runtime_layout(JITProgram *program)
{
    JITRuntimeLayout *layout = &program->runtime_layout;
    size_t raw_bytes = sizeof(Num) * jit_runtime_value_slots(program);

    /* Keep Var arrays aligned after the raw values and compact tag slots.
       Slot counts are immutable for the lifetime of live native frames. */
    layout->borrowed_offset = ((raw_bytes + sizeof(Var) - 1) / sizeof(Var))
	* sizeof(Var);
    layout->owned_offset = layout->borrowed_offset
	+ sizeof(Var) * program->num_borrowed_locals;
    layout->capacities_offset = layout->owned_offset
	+ sizeof(Var) * program->num_owned_slots;
    layout->states_offset = layout->capacities_offset
	+ sizeof(unsigned) * program->num_owned_slots;
    layout->bytes = layout->states_offset + program->num_owned_slots;
}

int
jit_program_compile(JITProgram *program)
{
    MIRBuild build;
    JITPool *pool;
    struct timeval started, finished;
    unsigned generation;
    unsigned pool_index;

    if (!program || program->state == JIT_STATE_UNSUPPORTED
	|| program->state == JIT_STATE_FAILED)
	return 0;
    generation = builtin_protection_generation();
    if (program->state == JIT_STATE_COMPILED
	&& program->protection_generation != generation) {
	jit_pool_rotate(JIT_ROTATION_PROTECTION_CHANGE, 1);
    }
    if (program->state == JIT_STATE_COMPILED
	&& (program->pool_index >= JIT_CONTEXT_COUNT
	    || program->pool_generation
	       != jit_pools[program->pool_index].generation)) {
	jit_program_release_native(program);
	program->state = JIT_STATE_PENDING;
    }
    if (program->state == JIT_STATE_COMPILED)
	return 1;
    if (!jit_program_restore_ir(program))
	return 0;
    jit_program_find_borrowed_locals(program);
    jit_program_clear_region_exits(program);
    if (program->compile_attempts < UINT32_MAX)
	program->compile_attempts++;
    gettimeofday(&started, 0);
    pool = jit_pool_select_compile(&pool_index);
    if (!jit_ensure_context(pool)) {
	program->pool_index = JIT_NO_POOL;
	return 0;
    }
    program->pool_index = pool_index;
    program->pool_generation = pool->generation;
    if (!build_mir(program, &build, pool->context)) {
	gettimeofday(&finished, 0);
	program->compile_time_us += elapsed_us(&started, &finished);
	if (program->compile_failures < UINT32_MAX)
	    program->compile_failures++;
	program->state = JIT_STATE_FAILED;
	if (program->reason)
	    free_str(program->reason);
	program->reason = str_dup("code-generation-failed");
	if (program->diagnostic)
	    free_str(program->diagnostic);
	program->diagnostic = str_dup("mir build module failed");
	program->pool_index = JIT_NO_POOL;
	program->pool_generation = 0;
	return 0;
    }
    MIR_load_module(pool->context, build.module);
    MIR_gen_init(pool->context);
    MIR_gen_set_optimize_level(pool->context, 1);
    MIR_link(pool->context, MIR_set_gen_interface, 0);
    program->native_function = MIR_gen(pool->context, build.function);
    if (!program->native_function) {
	gettimeofday(&finished, 0);
	program->compile_time_us += elapsed_us(&started, &finished);
	if (program->compile_failures < UINT32_MAX)
	    program->compile_failures++;
	MIR_gen_finish(pool->context);
	program->state = JIT_STATE_FAILED;
	if (program->reason)
	    free_str(program->reason);
	program->reason = str_dup("code-generation-failed");
	if (program->diagnostic)
	    free_str(program->diagnostic);
	program->diagnostic = str_dup("mir generator failed");
	program->pool_index = JIT_NO_POOL;
	program->pool_generation = 0;
	return 0;
    }
    program->machine_code = build.function->u.func->machine_code;
    program->machine_code_len = build.function->u.func->machine_code_len;
    MIR_gen_finish(pool->context);
    jit_program_finalize_runtime_layout(program);
    program->protection_generation = generation;
    program->state = JIT_STATE_COMPILED;
    program->warmup_count = 0;
    jit_pool_register(program);
    gettimeofday(&finished, 0);
    program->compile_time_us += elapsed_us(&started, &finished);
    if (program->compile_successes < UINT32_MAX)
	program->compile_successes++;
    if (program->bytecode_program) {
	jit_program_free_retained_constants(program);
	jit_program_release_ir(program, 1);
    }
    return 1;
}

static int jit_runtime_type_is_valid(var_type);

static int
jit_continuation_type_needs_owner(var_type type)
{
    return type == TYPE_STR || type == TYPE_LIST
#ifdef WAIF_CORE
	|| type == TYPE_WAIF
#endif
	;
}

static Var
materialize_deopt_value_with_ownership(var_type type, Num raw, int retained)
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
#ifdef WAIF_CORE
    } else if (type == TYPE_WAIF) {
	if (!raw)
	    return (Var){ .type = TYPE_NONE, .v = { .num = 0 } };
	value.v.waif = (Waif *) (intptr_t) raw;
#endif
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
    return retained ? var_ref(value) : value;
}

static Var
materialize_deopt_value(var_type type, Num raw)
{
    return materialize_deopt_value_with_ownership(type, raw, 1);
}

static Num
jit_deopt_raw_value(JITProgram *program, int value, Num *deopt_values)
{
    if (jit_value_has_constant(program, value))
	return jit_constant_value(program, value);
    return deopt_values[value];
}

static Var *
jit_owner_home(JITProgram *program, int owner, Var *owned_values,
	       unsigned char *home_states)
{
    if (owner < 0 || owner >= program->num_owned_slots || !owned_values
	|| !home_states || home_states[owner] != JIT_HOME_OWNED
	|| owned_values[owner].type == TYPE_NONE)
	panic("Invalid owner-home reference at JIT boundary");
    return &owned_values[owner];
}

static Var
jit_take_boundary_stack_value(JITProgram *program, JITDeoptMap *map, int slot,
			      var_type type, Num *deopt_values,
			      Var *owned_values, unsigned char *home_states)
{
    JITBoundaryValueOwnership ownership = map->stack_boundary_ownership
	? map->stack_boundary_ownership[slot] : JIT_BOUNDARY_VALUE_RETAINED;
    int value = map->stack_values[slot];
    int owner = map->stack_owner_slots ? map->stack_owner_slots[slot] : -1;

    if (owner >= 0) {
	Var *home = jit_owner_home(program, owner, owned_values, home_states);

	type = home->type;
	if (ownership == JIT_BOUNDARY_VALUE_MOVED_OWNER) {
	    Var moved = *home;

	    home->type = TYPE_NONE;
	    home->v.num = 0;
	    home_states[owner] = JIT_HOME_EMPTY;
	    return moved;
	}
	return var_ref(*home);
    }

    if (ownership == JIT_BOUNDARY_VALUE_MOVED_OWNER) {
	panic("Owner-home move lacks an owner-home reference");
    }
    if (ownership == JIT_BOUNDARY_VALUE_MOVED_RAW) {
	Var moved = materialize_deopt_value_with_ownership(type,
	    jit_deopt_raw_value(program, value, deopt_values), 0);

	deopt_values[value] = 0;
	return moved;
    }
    return materialize_deopt_value(type,
	jit_deopt_raw_value(program, value, deopt_values));
}

#ifdef JIT_TESTING
Var
jit_test_take_boundary_stack_value(JITProgram *program,
				   JITBoundaryValueOwnership ownership,
				   int owner, var_type type, int value,
				   Num *deopt_values, Var *owned_values,
				   unsigned char *home_states)
{
    JITDeoptMap map;
    unsigned char stack_ownership[1];
    int stack_values[1];
    int stack_owner_slots[1];

    memset(&map, 0, sizeof(map));
    stack_ownership[0] = ownership;
    stack_values[0] = value;
    stack_owner_slots[0] = owner;
    map.stack_boundary_ownership = stack_ownership;
    map.stack_values = stack_values;
    map.stack_owner_slots = stack_owner_slots;
    return jit_take_boundary_stack_value(program, &map, 0, type,
	deopt_values, owned_values, home_states);
}
#endif

static JITResumeValue *
jit_continuation_resume_value(JITContinuationFrame *frame, int value)
{
    JITNativeResume *resume;
    int i;

    resume = frame->program->deopt_maps[frame->map_id].native_resume;
    for (i = 0; i < resume->num_values; i++) {
	if (resume->values[i].value == value) {
	    return &resume->values[i];
	}
    }
    return 0;
}

static int
jit_continuation_materialized_value(JITContinuationFrame *frame, int value,
				    Var *materialized)
{
    JITResumeValue *resume;
    var_type type;

    resume = jit_continuation_resume_value(frame, value);
    if (!resume)
	return 0;
    if (resume->source == JIT_RESUME_OPERAND)
	return 0;
    if (resume->source == JIT_RESUME_RESULT) {
	if (!frame->has_result)
	    return 0;
	*materialized = var_ref(frame->result);
	return 1;
    }
    if (resume->source == JIT_RESUME_CONSTANT) {
	JITNativeResume *native_resume = frame->program->deopt_maps[
	    frame->map_id].native_resume;
	JITResumeLiteral *literal;

	if (resume->index < 0 || resume->index >= native_resume->num_literals)
	    return 0;
	literal = &native_resume->literals[resume->index];
	*materialized = materialize_deopt_value(literal->literal_type,
	    literal->literal);
	return 1;
    }
    if (resume->source == JIT_RESUME_OWNER) {
	if (resume->index < 0
	    || resume->index >= frame->program->num_owned_slots
	    || !frame->home_states
	    || frame->home_states[resume->index] != JIT_HOME_OWNED
	    || frame->owned_values[resume->index].type == TYPE_NONE)
	    return 0;
	*materialized = var_ref(frame->owned_values[resume->index]);
	return 1;
    }
    type = frame->program->value_is_tagged
	&& frame->program->value_is_tagged[value]
	? (var_type) frame->deopt_values[
	    jit_tag_index(frame->program, value)]
	: frame->program->value_types[value];
    if (!jit_runtime_type_is_valid(type))
	return 0;
    *materialized = materialize_deopt_value(type,
	jit_deopt_raw_value(frame->program, value, frame->deopt_values));
    return 1;
}

#ifdef JIT_TESTING
static int
jit_resume_value_needs_capture(JITResumeValue *resume, var_type type)
{
    if (!jit_continuation_type_needs_owner(type))
	return 0;
    if (resume->source == JIT_RESUME_OPERAND)
	return 0;
    if (resume->source == JIT_RESUME_OWNER
	|| resume->source == JIT_RESUME_CONSTANT
	|| resume->source == JIT_RESUME_RESULT)
	return 0;
    if (resume->source == JIT_RESUME_BORROWED_LOCAL)
	return 0;
    return resume->source == JIT_RESUME_LOCAL
	|| resume->source == JIT_RESUME_STACK
	|| resume->source == JIT_RESUME_CAPTURED;
}
#endif

static var_type
jit_resume_capture_action_type(JITResumeCaptureAction *action,
			       Num *deopt_values)
{
    return action->tag_slot >= 0
	? (var_type) deopt_values[action->tag_slot] : action->type;
}

#ifdef JIT_TESTING
static void
jit_test_build_resume_recipe(JITProgram *program, JITNativeResume *resume)
{
    int i;

    if (!program || !resume)
	return;
    if (resume->capture_actions)
	myfree(resume->capture_actions, M_PROGRAM);
    if (resume->required_homes)
	myfree(resume->required_homes, M_PROGRAM);
    resume->capture_actions = 0;
    resume->required_homes = 0;
    resume->num_capture_actions = 0;
    resume->num_required_homes = 0;
    resume->capture_actions = resume->num_values
	? mymalloc(sizeof(JITResumeCaptureAction) * resume->num_values,
	    M_PROGRAM) : 0;
    resume->required_homes = resume->num_values
	? mymalloc(sizeof(int) * resume->num_values, M_PROGRAM) : 0;
    for (i = 0; i < resume->num_values; i++) {
	JITResumeValue *value = &resume->values[i];
	int j;

	if (value->source == JIT_RESUME_OWNER) {
	    for (j = 0; j < resume->num_required_homes; j++)
		if (resume->required_homes[j] == value->index)
		    break;
	    if (j == resume->num_required_homes)
		resume->required_homes[resume->num_required_homes++] =
		    value->index;
	    continue;
	}
	if (value->source != JIT_RESUME_LOCAL
	    && value->source != JIT_RESUME_STACK
	    && value->source != JIT_RESUME_CAPTURED)
	    continue;
	if (value->value <= 0 || value->value >= program->num_values) {
	    resume->capture_actions[resume->num_capture_actions].value =
		value->value;
	    resume->capture_actions[resume->num_capture_actions].type = TYPE_ANY;
	    resume->capture_actions[resume->num_capture_actions].tag_slot = -1;
	    resume->num_capture_actions++;
	    continue;
	}
	for (j = 0; j < resume->num_capture_actions; j++)
	    if (resume->capture_actions[j].value == value->value)
		break;
	if (j < resume->num_capture_actions)
	    continue;
	resume->capture_actions[j].value = value->value;
	resume->capture_actions[j].type = program->value_types[value->value];
	resume->capture_actions[j].tag_slot = program->value_is_tagged[value->value]
	    ? jit_tag_index(program, value->value) : -1;
	resume->num_capture_actions++;
    }
    resume->recipe_valid = 1;
}
#endif

#ifdef JIT_TESTING
int
jit_test_resume_value_needs_capture(JITResumeSource source, var_type type)
{
    JITResumeValue resume;

    memset(&resume, 0, sizeof(resume));
    resume.source = source;
    return jit_resume_value_needs_capture(&resume, type);
}
#endif

static int
jit_continuation_boundary_operand(JITContinuationFrame *frame, int value,
				  Var *boundary, unsigned boundary_depth,
				  Var *materialized)
{
    JITDeoptMap *map = &frame->program->deopt_maps[frame->map_id];
    int operands = jit_call_stack_operands(map);
    unsigned outer_depth;
    int unpack_builtin;
    int i;

    if (operands < 0 || (unsigned) operands > map->stack_depth)
	return 0;
    outer_depth = map->stack_depth - operands;
    unpack_builtin = jit_deopt_map_is_specialized_builtin(map);
    for (i = 0; i < operands; i++) {
	if (map->stack_values[outer_depth + i] != value)
	    continue;
	if (unpack_builtin) {
	    if (boundary_depth != 1 || boundary[0].type != TYPE_LIST
		|| i >= boundary[0].v.list[0].v.num)
		return 0;
	    *materialized = var_ref(boundary[0].v.list[i + 1]);
	} else {
	    if ((unsigned) i >= boundary_depth)
		return 0;
	    *materialized = var_ref(boundary[i]);
	}
	return 1;
    }
    return 0;
}

static int
jit_continuation_prepare_boundary_activation(JITContinuationFrame *frame,
					     activation *a, Var *boundary,
					     unsigned boundary_depth)
{
    JITProgram *program;
    JITDeoptMap *map;
    unsigned outer_depth;
    unsigned published_depth;
    unsigned i;
    int operands;
    int unpack_builtin;

    if (!frame || !a || !(program = frame->program)
	|| frame->map_id <= 0 || frame->map_id >= program->num_deopt_maps
	|| frame->dispatched || frame->has_result
	|| (boundary_depth && !boundary))
	return 0;
    map = &program->deopt_maps[frame->map_id];
    operands = jit_call_stack_operands(map);
    if (operands < 0 || (unsigned) operands > map->stack_depth)
	return 0;
    outer_depth = map->stack_depth - operands;
    unpack_builtin = jit_deopt_map_is_specialized_builtin(map);
    if (unpack_builtin
	&& (boundary_depth != 1 || boundary[0].type != TYPE_LIST
	    || boundary[0].v.list[0].v.num != map->builtin_args))
	return 0;
    published_depth = unpack_builtin
	? (unsigned) map->builtin_args : boundary_depth;
    if (outer_depth + published_depth > (unsigned) a->rt_stack_size
	|| a->top_rt_stack != a->base_rt_stack)
	return 0;
    for (i = 0; i < (unsigned) map->num_locals; i++) {
	int value = jit_deopt_map_local_value(program, map, i);

	if (value > 0 && !jit_continuation_resume_value(frame, value))
	    return 0;
    }
    for (i = 0; i < outer_depth; i++)
	if ((!map->stack_slots || map->stack_slots[i].kind == RSS_VALUE)
	    && !jit_continuation_resume_value(frame, map->stack_values[i]))
	    return 0;
    for (i = 0; i < (unsigned) map->num_locals; i++) {
	int value = jit_deopt_map_local_value(program, map, i);
	Var saved;

	if (value <= 0)
	    continue;
	if (jit_continuation_materialized_value(frame, value, &saved)
	    || jit_continuation_boundary_operand(frame, value, boundary,
		boundary_depth, &saved)) {
	    free_var(a->rt_env[i]);
	    a->rt_env[i] = saved;
	}
    }
    for (i = 0; i < outer_depth; i++) {
	ResumeStackSlot slot = map->stack_slots
	    ? map->stack_slots[i]
	    : (ResumeStackSlot){ .kind = RSS_VALUE, .data = 0 };
	Var value;

	if (slot.kind == RSS_VALUE) {
	    if (!jit_continuation_materialized_value(frame,
		map->stack_values[i], &value))
		return 0;
	} else {
	    value.type = slot.kind == RSS_CATCH ? TYPE_CATCH
		: slot.kind == RSS_FINALLY ? TYPE_FINALLY : TYPE_INT;
	    value.v.num = slot.data;
	}
	*a->top_rt_stack++ = value;
    }
    if (unpack_builtin) {
	for (i = 0; i < published_depth; i++)
	    *a->top_rt_stack++ = var_ref(boundary[0].v.list[i + 1]);
    } else {
	for (i = 0; i < boundary_depth; i++)
	    *a->top_rt_stack++ = var_ref(boundary[i]);
    }
    a->pc = map->bytecode_pc;
    a->error_pc = map->error_pc;
    a->resume_key = invalid_resume_key();
    return 1;
}

static int
jit_raw_value_is_retained(JITProgram *program, var_type type, Num raw,
			  Var *owned_values, unsigned char *home_states,
			  Var *new_values, int num_values)
{
    int i;

    if (!raw)
	return 1;
    if (owned_values && home_states) {
	for (i = 0; i < program->num_owned_slots; i++) {
	    if (home_states[i] == JIT_HOME_OWNED
		&& owned_values[i].type == type
		&& owned_values[i].v.num == raw)
		return 1;
	}
    }
    for (i = 0; i < num_values; i++) {
	if (new_values[i].type == type && new_values[i].v.num == raw)
	    return 1;
    }
    return 0;
}

static JITContinuationFrame *jit_continuation_capture(JITProgram *, int,
	Num *, void *, Var *, Var *, unsigned char *, unsigned *, size_t,
	JITContinuationFrame *);

int
jit_native_frame_preserve_resume(JITNativeFrame *frame, int map_id)
{
    JITProgram *program;
    JITDeoptMap *map;
    JITNativeResume *resume;
    Num *deopt_values;
    Var *new_roots = 0;
    unsigned num_roots = 0;
    unsigned root_capacity = 0;
    int i;

    if (!frame || !(program = frame->program) || !frame->runtime_storage
	|| !frame->owns_runtime || frame->runtime_borrower || map_id <= 0
	|| map_id >= program->num_deopt_maps)
	return 0;
    map = &program->deopt_maps[map_id];
#ifdef JIT_TESTING
    if (map->native_resume)
	jit_test_build_resume_recipe(program, map->native_resume);
#endif
    if (!(resume = map->native_resume) || !resume->valid
	|| !resume->recipe_valid)
	return 0;
    deopt_values = frame->runtime_storage;
    for (i = 0; i < resume->num_required_homes; i++) {
	int home = resume->required_homes[i];

	if (home < 0 || home >= program->num_owned_slots
	    || !frame->home_states
	    || frame->home_states[home] != JIT_HOME_OWNED
	    || frame->homes[home].type == TYPE_NONE)
	    goto fail;
    }
    if (!resume->num_capture_actions) {
	jit_native_frame_release_resume_roots(frame);
	frame->pending_resume_map = map_id;
	return 1;
    }
    for (i = 0; i < resume->num_capture_actions; i++) {
	JITResumeCaptureAction *action = &resume->capture_actions[i];
	var_type type = jit_resume_capture_action_type(action, deopt_values);
	Num raw;

	if (!jit_runtime_type_is_valid(type))
	    goto fail;
	if (!jit_continuation_type_needs_owner(type))
	    continue;
	raw = jit_deopt_raw_value(program, action->value, deopt_values);
	if (!jit_raw_value_is_retained(program, type, raw, frame->homes,
		frame->home_states, 0, 0))
	    root_capacity++;
    }
    if (root_capacity)
	new_roots = mymalloc(sizeof(Var) * root_capacity, M_PROGRAM);
    for (i = 0; root_capacity && i < resume->num_capture_actions; i++) {
	JITResumeCaptureAction *action = &resume->capture_actions[i];
	var_type type = jit_resume_capture_action_type(action, deopt_values);
	Num raw;

	if (!jit_continuation_type_needs_owner(type))
	    continue;
	raw = jit_deopt_raw_value(program, action->value, deopt_values);
	if (!jit_raw_value_is_retained(program, type, raw, frame->homes,
		frame->home_states, new_roots, num_roots))
	    new_roots[num_roots++] = materialize_deopt_value(type, raw);
    }
    jit_native_frame_release_resume_roots(frame);
    frame->resume_roots = new_roots;
    frame->num_resume_roots = num_roots;
    frame->resume_roots_capacity = root_capacity;
    frame->pending_resume_map = map_id;
    program->active_runtime_bytes += sizeof(Var) * root_capacity;
    return 1;

  fail:
    for (i = 0; i < (int) num_roots; i++)
	free_var(new_roots[i]);
    if (new_roots)
	myfree(new_roots, M_PROGRAM);
    return 0;
}

JITContinuationFrame *
jit_native_frame_capture_continuation(JITNativeFrame *frame, int map_id)
{
    JITContinuationFrame *continuation;
    JITProgram *program;
    Num *deopt_values;
    Var *borrowed_locals = 0;

    if (!frame || !(program = frame->program) || !frame->runtime_storage
	|| !frame->owns_runtime || frame->runtime_borrower
	|| frame->pending_resume_map != map_id)
	return 0;
    deopt_values = frame->runtime_storage;
    if (program->num_borrowed_locals)
	borrowed_locals = (Var *) ((char *) frame->runtime_storage
	    + program->runtime_layout.borrowed_offset);
    continuation = jit_continuation_capture(program, map_id, deopt_values,
	frame->runtime_storage, borrowed_locals, frame->homes,
	frame->home_states, frame->home_capacities, frame->runtime_bytes, 0);
    if (!continuation)
	return 0;
    jit_native_frame_release_resume_roots(frame);
    jit_native_frame_unbind_runtime(frame);
    return continuation;
}

static JITContinuationFrame *
jit_continuation_capture(JITProgram *program, int map_id, Num *deopt_values,
			 void *runtime_storage, Var *borrowed_locals,
			 Var *owned_values, unsigned char *home_states,
			 unsigned *home_capacities,
			 size_t runtime_bytes,
			 JITContinuationFrame *frame)
{
    JITDeoptMap *map;
    Var *new_values;
    int new_values_capacity;
    int captured_values = 0;
    JITNativeResume *recipe;
    int i;

    if (!program || map_id <= 0 || map_id >= program->num_deopt_maps)
	return 0;
    if (frame && frame->runtime_owner
	&& (frame->owns_runtime
	    || frame->runtime_owner->runtime_borrower != frame
	    || !frame->runtime_owner->owns_runtime
	    || frame->runtime_owner->runtime_storage != runtime_storage
	    || frame->runtime_storage != runtime_storage
	    || frame->owned_values != owned_values
	    || frame->home_states != home_states
	    || frame->runtime_bytes != runtime_bytes))
	return 0;
    map = &program->deopt_maps[map_id];
#ifdef JIT_TESTING
    if (map->native_resume)
	jit_test_build_resume_recipe(program, map->native_resume);
#endif
    if (!(recipe = map->native_resume) || !recipe->valid
	|| !recipe->recipe_valid)
	return 0;
    for (i = 0; i < recipe->num_required_homes; i++) {
	int home = recipe->required_homes[i];

	if (home < 0 || home >= program->num_owned_slots || !home_states
	    || home_states[home] != JIT_HOME_OWNED
	    || owned_values[home].type == TYPE_NONE)
	    return 0;
    }
    for (i = 0; i < recipe->num_capture_actions; i++) {
	JITResumeCaptureAction *action = &recipe->capture_actions[i];
	var_type type = jit_resume_capture_action_type(action, deopt_values);
	Num raw;
	int duplicate = 0;
	int j;

	if (!jit_runtime_type_is_valid(type))
	    return 0;
	if (!jit_continuation_type_needs_owner(type))
	    continue;
	raw = jit_deopt_raw_value(program, action->value, deopt_values);
	if (jit_raw_value_is_retained(program, type, raw, owned_values,
		home_states, 0, 0))
	    continue;
	for (j = 0; j < i; j++) {
	    JITResumeCaptureAction *previous = &recipe->capture_actions[j];
	    var_type previous_type = jit_resume_capture_action_type(previous,
		deopt_values);

	    if (previous_type == type
		&& jit_continuation_type_needs_owner(previous_type)
		&& jit_deopt_raw_value(program, previous->value,
		    deopt_values) == raw) {
		duplicate = 1;
		break;
	    }
	}
	if (!duplicate)
	    captured_values++;
    }
    new_values_capacity = captured_values;
    if (frame) {
	new_values = frame->spare_retained;
	new_values_capacity = frame->spare_retained_capacity;
	if (new_values_capacity < captured_values) {
	    if (new_values)
		new_values = myrealloc(new_values,
		    sizeof(Var) * captured_values, M_PROGRAM);
	    else
		new_values = mymalloc(
		    sizeof(Var) * captured_values, M_PROGRAM);
	    new_values_capacity = captured_values;
	}
    } else
	new_values = captured_values
	    ? mymalloc(sizeof(Var) * captured_values, M_PROGRAM)
	    : 0;
    for (i = 0; i < captured_values; i++)
	new_values[i].type = TYPE_NONE;
    captured_values = 0;
    for (i = 0; i < recipe->num_capture_actions; i++) {
	JITResumeCaptureAction *action = &recipe->capture_actions[i];
	var_type type = jit_resume_capture_action_type(action, deopt_values);

	if (jit_continuation_type_needs_owner(type)) {
	    Num raw = jit_deopt_raw_value(program, action->value, deopt_values);

	    if (!jit_raw_value_is_retained(program, type, raw, owned_values,
		    home_states, new_values, captured_values))
		new_values[captured_values++] =
		    materialize_deopt_value(type, raw);
	}
    }
    if (!frame) {
	frame = mymalloc(sizeof(JITContinuationFrame), M_PROGRAM);
	memset(frame, 0, sizeof(JITContinuationFrame));
	frame->owns_runtime = runtime_storage != 0;
    } else {
	Var *old_values = frame->retained_values;
	int old_values_capacity = frame->retained_capacity;

	for (i = 0; i < frame->num_retained; i++)
	    free_var(frame->retained_values[i]);
	if (frame->has_result)
	    free_var(frame->result);
	frame->spare_retained = old_values;
	frame->spare_retained_capacity = old_values_capacity;
	frame->has_result = 0;
	frame->dispatched = 0;
    }
    frame->program = program;
    frame->map_id = map_id;
    frame->num_retained = captured_values;
    frame->retained_values = new_values;
    frame->retained_capacity = new_values_capacity;
    frame->runtime_storage = runtime_storage;
    frame->deopt_values = deopt_values;
    frame->borrowed_locals = borrowed_locals;
    frame->owned_values = owned_values;
    frame->home_capacities = home_capacities;
    frame->home_states = home_states;
    frame->runtime_bytes = runtime_bytes;
    if (jit_profile_detail && program->usage)
	program->usage->continuation_captures++;
    return frame;
}

#ifdef JIT_TESTING
JITContinuationFrame *
jit_test_continuation_capture(JITProgram *program, int map_id,
			      Num *deopt_values, void *runtime_storage,
			      Var *borrowed_locals, Var *owned_values,
			      unsigned char *home_states,
			      unsigned *home_capacities, size_t runtime_bytes,
			      JITContinuationFrame *frame)
{
    return jit_continuation_capture(program, map_id, deopt_values,
	runtime_storage, borrowed_locals, owned_values, home_states,
	home_capacities, runtime_bytes, frame);
}
#endif

int
jit_native_frame_prepare_activation(JITNativeFrame *native_frame,
				    activation *a, int map_id, int dispatched)
{
    JITContinuationFrame *continuation;
    JITDeoptMap *map;
    JITProgram *program;
    Num *deopt_values;
    Var *borrowed_locals = 0;
    unsigned stack_depth;

    if (!native_frame || !a || !(program = native_frame->program)
	|| a->jit_continuation || map_id < 0
	|| map_id >= program->num_deopt_maps
	|| (native_frame->owns_boundary_stack && dispatched))
	return 0;
    map = &program->deopt_maps[map_id];
    if ((map->num_locals && (!a->prog || !a->rt_env
	 || (unsigned) map->num_locals > a->prog->num_var_names))
	|| a->rt_stack_size < 0 || !a->base_rt_stack || !a->top_rt_stack
	|| a->top_rt_stack < a->base_rt_stack
	|| a->top_rt_stack > a->base_rt_stack + a->rt_stack_size)
	return 0;
    if (map_id == 0) {
	if (dispatched || native_frame->owns_boundary_stack
	    || native_frame->runtime_borrower
	    || a->top_rt_stack != a->base_rt_stack)
	    return 0;
	a->pc = map->bytecode_pc;
	a->error_pc = map->error_pc;
	a->resume_key = invalid_resume_key();
	return 1;
    }
    if (native_frame->owns_boundary_stack) {
	unsigned i;

	if (native_frame->boundary_map != map_id
	    || native_frame->boundary_depth > (unsigned) a->rt_stack_size
	    || a->top_rt_stack != a->base_rt_stack)
	    return 0;
	if (native_frame->runtime_borrower)
	    return jit_continuation_prepare_boundary_activation(
		native_frame->runtime_borrower, a,
		native_frame->boundary_stack, native_frame->boundary_depth);
	for (i = 0; i < native_frame->boundary_depth; i++)
	    *a->top_rt_stack++ = var_ref(native_frame->boundary_stack[i]);
	a->pc = map->bytecode_pc;
	a->error_pc = map->error_pc;
	a->resume_key = invalid_resume_key();
	return 1;
    }
    if (!native_frame->runtime_storage
	|| native_frame->num_homes != (unsigned) program->num_owned_slots)
	return 0;
    stack_depth = map->stack_depth;
    if (dispatched) {
	int operands = jit_call_stack_operands(map);

	if (operands < 0 || (unsigned) operands > stack_depth)
	    return 0;
	stack_depth -= operands;
    }
    if (stack_depth > (unsigned) a->rt_stack_size)
	return 0;
    deopt_values = native_frame->runtime_storage;
    if (native_frame->runtime_bytes < program->runtime_layout.owned_offset)
	return 0;
    if (program->num_borrowed_locals)
	borrowed_locals = (Var *) ((char *) native_frame->runtime_storage
	    + program->runtime_layout.borrowed_offset);
    continuation = jit_continuation_capture(program, map_id, deopt_values,
	0, borrowed_locals, native_frame->homes, native_frame->home_states,
	native_frame->home_capacities, 0, 0);
    if (!continuation)
	return 0;
    jit_continuation_attach(continuation, a);
    if (dispatched)
	jit_continuation_mark_dispatched(continuation);
    if (!jit_continuation_materialize(a)) {
	if (a->jit_continuation)
	    jit_continuation_free(a->jit_continuation);
	return 0;
    }
    return 1;
}

void
jit_continuation_attach(JITContinuationFrame *frame, activation *owner)
{
    if (!frame || !owner)
	return;
    if (frame->owner == owner && owner->jit_continuation == frame)
	return;
    if (owner->jit_continuation && owner->jit_continuation != frame)
	panic("Attaching two JIT continuations to one activation");
    if (frame->owner || frame->previous || frame->next
	|| continuation_frames == frame)
	panic("Attaching an already linked JIT continuation");
    frame->owner = owner;
    owner->jit_continuation = frame;
    frame->next = continuation_frames;
    if (continuation_frames)
	continuation_frames->previous = frame;
    continuation_frames = frame;
}

void
jit_continuation_relocate(JITContinuationFrame *frame, activation *owner)
{
    if (!frame || !owner)
	return;
    if (frame->owner && frame->owner->jit_continuation == frame)
	frame->owner->jit_continuation = 0;
    frame->owner = owner;
    owner->jit_continuation = frame;
}

void
jit_continuation_mark_dispatched(JITContinuationFrame *frame)
{
    if (frame) {
	frame->dispatched = 1;
	if (frame->owner)
	    frame->owner->top_rt_stack = frame->owner->base_rt_stack;
    }
}

int
jit_continuation_is_dispatched(const JITContinuationFrame *frame)
{
    return frame && frame->dispatched;
}

void
jit_continuation_set_result(JITContinuationFrame *frame, Var value)
{
    if (!frame)
	return;
    if (frame->has_result)
	free_var(frame->result);
    frame->result = value;
    frame->has_result = 1;
}

void
jit_continuation_free(JITContinuationFrame *frame)
{
    int i;

    if (!frame)
	return;
    if (frame->owner && frame->owner->jit_continuation == frame)
	frame->owner->jit_continuation = 0;
    jit_continuation_unlink(frame);
    for (i = 0; i < frame->num_retained; i++)
	free_var(frame->retained_values[i]);
    if (frame->retained_values)
	myfree(frame->retained_values, M_PROGRAM);
    if (frame->spare_retained)
	myfree(frame->spare_retained, M_PROGRAM);
    if (frame->has_result)
	free_var(frame->result);
    if (frame->runtime_owner) {
	if (frame->runtime_owner->runtime_borrower != frame)
	    panic("Continuation runtime owner backlink is invalid");
	frame->runtime_owner->runtime_borrower = 0;
	frame->runtime_owner = 0;
    }
    if (frame->runtime_storage && frame->owns_runtime) {
	for (i = 0; i < frame->program->num_borrowed_locals; i++)
	    free_var(frame->borrowed_locals[i]);
	for (i = 0; i < frame->program->num_owned_slots; i++)
	    free_var(frame->owned_values[i]);
	frame->program->active_runtime_bytes -= frame->runtime_bytes;
	myfree(frame->runtime_storage, M_PROGRAM);
    }
    myfree(frame, M_PROGRAM);
}

int
jit_continuation_materialize(activation *a)
{
    JITContinuationFrame *frame;
    JITProgram *program;
    JITDeoptMap *map;
    const ResumePoint *point;
    unsigned depth, i;

    if (!a || !(frame = a->jit_continuation))
	return 1;
    program = frame->program;
    if (!program || frame->map_id <= 0
	|| frame->map_id >= program->num_deopt_maps)
	return 0;
    map = &program->deopt_maps[frame->map_id];
    if (jit_profile_detail && program->usage)
	program->usage->continuation_materializations++;
    depth = map->stack_depth;
    if (frame->dispatched) {
	int operands = jit_call_stack_operands(map);

	if (operands < 0 || (unsigned) operands > depth)
	    return 0;
	depth -= operands;
    }
    point = resume_point_for_key(a->prog, map->resume_key);
    if (frame->dispatched && !point)
	return 0;
    for (i = 0; i < (unsigned) map->num_locals; i++) {
	int value = jit_deopt_map_local_value(program, map, i);

	if (value > 0 && !jit_continuation_resume_value(frame, value))
	    return 0;
    }
    for (i = 0; i < depth; i++)
	if ((!map->stack_slots || map->stack_slots[i].kind == RSS_VALUE)
	    && !jit_continuation_resume_value(frame, map->stack_values[i]))
	    return 0;
    for (i = 0; i < (unsigned) map->num_locals; i++) {
	int value = jit_deopt_map_local_value(program, map, i);
	Var saved;

	if (value > 0
	    && jit_continuation_materialized_value(frame, value, &saved)) {
	    free_var(a->rt_env[i]);
	    a->rt_env[i] = saved;
	}
    }
    while (a->top_rt_stack > a->base_rt_stack)
	free_var(*--a->top_rt_stack);
    for (i = 0; i < depth; i++) {
	ResumeStackSlot slot = map->stack_slots
	    ? map->stack_slots[i]
	    : (ResumeStackSlot){ .kind = RSS_VALUE, .data = 0 };
	Var value;

	if (slot.kind == RSS_VALUE) {
	    if (!jit_continuation_materialized_value(frame,
		map->stack_values[i], &value))
		return 0;
	} else {
	    value.type = slot.kind == RSS_CATCH ? TYPE_CATCH
		: slot.kind == RSS_FINALLY ? TYPE_FINALLY : TYPE_INT;
	    value.v.num = slot.data;
	}
	*a->top_rt_stack++ = value;
    }
    if (frame->has_result)
	*a->top_rt_stack++ = var_ref(frame->result);
    if (frame->dispatched) {
	a->pc = point->pc;
	a->error_pc = point->error_pc;
	a->resume_key = point->key;
    } else {
	a->pc = map->bytecode_pc;
	a->error_pc = map->error_pc;
	a->resume_key = invalid_resume_key();
    }
    free_var(a->temp);
    a->temp.type = TYPE_NONE;
    a->temp.v.num = 0;
    jit_continuation_free(frame);
    return 1;
}

int
jit_continuation_materialize_boundary(activation *a, Var *boundary,
				      unsigned boundary_depth)
{
    JITContinuationFrame *frame;

    if (!a || !(frame = a->jit_continuation))
	return 1;
    if (!jit_continuation_prepare_boundary_activation(frame, a, boundary,
	    boundary_depth))
	return 0;
    if (jit_profile_detail && frame->program->usage)
	frame->program->usage->continuation_materializations++;
    free_var(a->temp);
    a->temp.type = TYPE_NONE;
    a->temp.v.num = 0;
    jit_continuation_free(frame);
    return 1;
}

static JITRegionExitValue *
jit_region_exit_value(JITRegionExitFrame *frame, int target_value)
{
    int i;

    for (i = 0; i < frame->num_values; i++)
	if (frame->values[i].target_value == target_value)
	    return &frame->values[i];
    return 0;
}

int
jit_region_exit_frame_count(JITProgram *program, int exit_id)
{
    if (!program || exit_id < 0 || exit_id >= program->num_region_exits
	|| program->region_exits[exit_id].dispatch_epoch != db_dispatch_epoch())
	return 0;
    return program->region_exits[exit_id].num_frames;
}

int
jit_region_exit_materialize(JITProgram *program, int exit_id, int frame_id,
	JITContinuationFrame *continuation, activation *a, int *ticks)
{
    JITRegionExit *exit;
    JITRegionExitFrame *frame;
    JITDeoptMap *map;
    const ResumePoint *point = 0;
    unsigned stack_depth;
    Num path_ticks;
    int i;

    if (!program || exit_id < 0 || exit_id >= program->num_region_exits
	|| !continuation || continuation->program != program
	|| !continuation->deopt_values || !a || !a->prog || !a->rt_env
	|| !a->base_rt_stack || !a->top_rt_stack || !ticks)
	return 0;
    exit = &program->region_exits[exit_id];
    if (exit->dispatch_epoch != db_dispatch_epoch()
	|| frame_id < 0 || frame_id >= exit->num_frames)
	return 0;
    frame = &exit->frames[frame_id];
    if (!frame->target || a->prog != frame->bytecode_program
	|| a->prog->jit != frame->target || frame->map <= 0
	|| frame->map >= frame->target->num_deopt_maps)
	return 0;
    map = &frame->target->deopt_maps[frame->map];
    stack_depth = map->stack_depth;
    if (frame->dispatched) {
	if (jit_call_stack_operands(map) != 3 || stack_depth < 3
	    || !(point = resume_point_for_key(a->prog, map->resume_key)))
	    return 0;
	stack_depth -= 3;
    } else if (frame_id != exit->num_frames - 1)
	return 0;
    if (map->num_locals > (int) a->prog->num_var_names
	|| stack_depth > (unsigned) a->rt_stack_size)
	return 0;
    for (i = 0; i < (int) stack_depth; i++) {
	ResumeStackSlot slot = map->stack_slots
	    ? map->stack_slots[i]
	    : (ResumeStackSlot){ .kind = RSS_VALUE, .data = 0 };

	if (slot.kind == RSS_VALUE
	    && !jit_region_exit_value(frame, map->stack_values[i]))
	    return 0;
    }
    path_ticks = continuation->deopt_values[
	jit_runtime_base_value_slots(program) + exit->tick_slot];
    if (path_ticks < 0 || path_ticks >= *ticks)
	return 0;
    for (i = 0; i < map->num_locals; i++) {
	int target_value = jit_deopt_map_local_value(frame->target, map, i);
	JITRegionExitValue *value = jit_region_exit_value(frame, target_value);

	if (value) {
	    Var materialized;

	    materialized.type = TYPE_INT;
	    materialized.v.num = continuation->deopt_values[
		jit_runtime_base_value_slots(program) + value->runtime_slot];
	    free_var(a->rt_env[i]);
	    a->rt_env[i] = materialized;
	}
    }
    while (a->top_rt_stack > a->base_rt_stack)
	free_var(*--a->top_rt_stack);
    for (i = 0; i < (int) stack_depth; i++) {
	ResumeStackSlot slot = map->stack_slots
	    ? map->stack_slots[i]
	    : (ResumeStackSlot){ .kind = RSS_VALUE, .data = 0 };
	Var materialized;

	if (slot.kind == RSS_VALUE) {
	    JITRegionExitValue *value = jit_region_exit_value(frame,
		map->stack_values[i]);

	    materialized.type = TYPE_INT;
	    materialized.v.num = continuation->deopt_values[
		jit_runtime_base_value_slots(program) + value->runtime_slot];
	} else {
	    materialized.type = slot.kind == RSS_CATCH ? TYPE_CATCH
		: slot.kind == RSS_FINALLY ? TYPE_FINALLY : TYPE_INT;
	    materialized.v.num = slot.data;
	}
	*a->top_rt_stack++ = materialized;
    }
    if (frame->dispatched) {
	a->pc = point->pc;
	a->error_pc = point->error_pc;
	a->resume_key = point->key;
    } else {
	*ticks -= (int) path_ticks;
	a->pc = map->bytecode_pc;
	a->error_pc = map->error_pc;
	a->resume_key = invalid_resume_key();
    }
    free_var(a->temp);
    a->temp.type = TYPE_NONE;
    a->temp.v.num = 0;
    return 1;
}

int
jit_region_exit_call(JITProgram *program, int exit_id, int frame_id,
	JITContinuationFrame *continuation, Var *args, Objid *receiver_class,
	const char **verb)
{
    JITRegionExit *exit;
    JITRegionExitFrame *frame;
    int i;

    if (!program || exit_id < 0 || exit_id >= program->num_region_exits
	|| !continuation || continuation->program != program
	|| !continuation->deopt_values || !args || !receiver_class || !verb)
	return 0;
    exit = &program->region_exits[exit_id];
    if (exit->dispatch_epoch != db_dispatch_epoch()
	|| frame_id < 0 || frame_id >= exit->num_frames - 1)
	return 0;
    frame = &exit->frames[frame_id];
    if (!frame->dispatched || !frame->verb || frame->num_arguments < 0
	|| frame->num_arguments > JIT_REGION_MAX_ARGUMENTS)
	return 0;
    *args = new_list(frame->num_arguments);
    for (i = 0; i < frame->num_arguments; i++) {
	args->v.list[i + 1].type = TYPE_INT;
	args->v.list[i + 1].v.num = continuation->deopt_values[
	    jit_runtime_base_value_slots(program) + frame->argument_slots[i]];
    }
    *receiver_class = frame->receiver_class;
    *verb = frame->verb;
    return 1;
}

#ifdef JIT_TESTING
int
jit_test_region_exit_materialize(JITProgram *program, JITProgram *target,
	Program *bytecode_program, int target_map, int target_value, Num raw,
	Num path_ticks, activation *a, int *ticks)
{
    JITContinuationFrame continuation;
    Num *deopt_values;
    int slots;
    int result;

    if (!program || !target || !bytecode_program)
	return 0;
    jit_program_clear_region_exits(program);
    program->region_exits = mymalloc(sizeof(JITRegionExit), M_PROGRAM);
    memset(program->region_exits, 0, sizeof(JITRegionExit));
    program->num_region_exits = program->region_exit_capacity = 1;
    program->num_region_exit_values = 2;
    program->region_exits[0].dispatch_epoch = db_dispatch_epoch();
    program->region_exits[0].tick_slot = 0;
    program->region_exits[0].num_frames = 1;
    program->region_exits[0].frames = mymalloc(sizeof(JITRegionExitFrame),
	M_PROGRAM);
    memset(program->region_exits[0].frames, 0,
	sizeof(JITRegionExitFrame));
    program->region_exits[0].frames[0].target = target;
    program->region_exits[0].frames[0].bytecode_program = bytecode_program;
    program->region_exits[0].frames[0].map = target_map;
    program->region_exits[0].frames[0].num_values = 1;
    program->region_exits[0].frames[0].values =
	mymalloc(sizeof(JITRegionExitValue), M_PROGRAM);
    program->region_exits[0].frames[0].values[0].target_value = target_value;
    program->region_exits[0].frames[0].values[0].runtime_slot = 1;
    slots = jit_runtime_value_slots(program);
    deopt_values = mymalloc(sizeof(Num) * slots, M_PROGRAM);
    memset(deopt_values, 0, sizeof(Num) * slots);
    deopt_values[jit_runtime_base_value_slots(program)] = path_ticks;
    deopt_values[jit_runtime_base_value_slots(program) + 1] = raw;
    memset(&continuation, 0, sizeof(continuation));
    continuation.program = program;
    continuation.deopt_values = deopt_values;
    result = jit_region_exit_materialize(program, 0, 0, &continuation, a,
	ticks);
    myfree(deopt_values, M_PROGRAM);
    jit_program_clear_region_exits(program);
    return result;
}

int
jit_test_region_exit_chain(JITProgram *program, JITProgram *parent,
	Program *parent_bytecode, int parent_map, JITProgram *target,
	Program *target_bytecode, int target_map, activation *parent_activation,
	activation *target_activation, int *ticks, Var *args)
{
    JITContinuationFrame continuation;
    JITRegionExit *exit;
    Num *deopt_values;
    Objid receiver_class;
    const char *verb;
    int slots;
    int result;

    if (!program || !parent || !parent_bytecode || !target
	|| !target_bytecode || !parent_activation || !target_activation
	|| !ticks || !args)
	return 0;
    jit_program_clear_region_exits(program);
    program->region_exits = mymalloc(sizeof(JITRegionExit), M_PROGRAM);
    memset(program->region_exits, 0, sizeof(JITRegionExit));
    program->num_region_exits = program->region_exit_capacity = 1;
    program->num_region_exit_values = 4;
    exit = &program->region_exits[0];
    exit->dispatch_epoch = db_dispatch_epoch();
    exit->tick_slot = 0;
    exit->num_frames = 2;
    exit->frames = mymalloc(sizeof(JITRegionExitFrame) * 2, M_PROGRAM);
    memset(exit->frames, 0, sizeof(JITRegionExitFrame) * 2);
    exit->frames[0].target = parent;
    exit->frames[0].bytecode_program = parent_bytecode;
    exit->frames[0].verb = str_dup("nested_region");
    exit->frames[0].receiver_class = 2;
    exit->frames[0].map = parent_map;
    exit->frames[0].dispatched = 1;
    exit->frames[0].num_values = 1;
    exit->frames[0].values = mymalloc(sizeof(JITRegionExitValue), M_PROGRAM);
    exit->frames[0].values[0].target_value = 1;
    exit->frames[0].values[0].runtime_slot = 1;
    exit->frames[0].num_arguments = 1;
    exit->frames[0].argument_slots[0] = 2;
    exit->frames[1].target = target;
    exit->frames[1].bytecode_program = target_bytecode;
    exit->frames[1].map = target_map;
    exit->frames[1].num_values = 1;
    exit->frames[1].values = mymalloc(sizeof(JITRegionExitValue), M_PROGRAM);
    exit->frames[1].values[0].target_value = 1;
    exit->frames[1].values[0].runtime_slot = 3;
    slots = jit_runtime_value_slots(program);
    deopt_values = mymalloc(sizeof(Num) * slots, M_PROGRAM);
    memset(deopt_values, 0, sizeof(Num) * slots);
    deopt_values[jit_runtime_base_value_slots(program)] = 3;
    deopt_values[jit_runtime_base_value_slots(program) + 1] = 41;
    deopt_values[jit_runtime_base_value_slots(program) + 2] = 43;
    deopt_values[jit_runtime_base_value_slots(program) + 3] = 42;
    memset(&continuation, 0, sizeof(continuation));
    continuation.program = program;
    continuation.deopt_values = deopt_values;
    result = jit_region_exit_frame_count(program, 0) == 2
	&& jit_region_exit_materialize(program, 0, 0, &continuation,
	    parent_activation, ticks)
	&& jit_region_exit_call(program, 0, 0, &continuation, args,
	    &receiver_class, &verb)
	&& receiver_class == 2 && !strcmp(verb, "nested_region")
	&& jit_region_exit_materialize(program, 0, 1, &continuation,
	    target_activation, ticks);
    myfree(deopt_values, M_PROGRAM);
    jit_program_clear_region_exits(program);
    return result;
}
#endif

void
jit_continuation_materialize_all(void)
{
    while (continuation_frames) {
	JITContinuationFrame *frame = continuation_frames;

	if (!frame->owner || !jit_continuation_materialize(frame->owner))
	    panic("JIT continuation materialization failed");
    }
}

static int
jit_runtime_type_is_valid(var_type type)
{
    switch (type) {
    case TYPE_INT:
    case TYPE_OBJ:
    case TYPE_STR:
    case TYPE_ERR:
    case TYPE_LIST:
    case TYPE_CLEAR:
    case TYPE_NONE:
    case TYPE_CATCH:
    case TYPE_FINALLY:
    case TYPE_FLOAT:
#ifdef WAIF_CORE
    case TYPE_WAIF:
#endif
	return 1;
    default:
	return 0;
    }
}

static int
jit_deopt_map_is_suspend_zero(JITProgram *program, JITDeoptMap *map,
			       Num *deopt_values, Var *owned_values,
			       unsigned char *home_states)
{
    int slot;
    int value;
    var_type type;

    if (!jit_deopt_map_bridges_builtin(map)
	|| strcmp(name_func_by_num(map->builtin_func), "suspend")
	|| map->stack_depth == 0)
	return 0;
    slot = map->stack_depth - 1;
    if (map->stack_slots && map->stack_slots[slot].kind != RSS_VALUE)
	return 0;
    value = map->stack_values[slot];
    if (value <= 0 || value >= program->num_values)
	return 0;
    type = jit_deopt_map_stack_type(program, map, slot);
    if (map->stack_owner_slots && map->stack_owner_slots[slot] >= 0) {
	Var *home = jit_owner_home(program, map->stack_owner_slots[slot],
	    owned_values, home_states);

	type = home->type;
	if (map->builtin_args == 1)
	    return type == TYPE_INT && home->v.num == 0;
	if (map->builtin_args < 0 && type == TYPE_LIST)
	    return home->v.list && home->v.list[0].v.num == 1
		&& home->v.list[1].type == TYPE_INT
		&& home->v.list[1].v.num == 0;
	return 0;
    } else if (type == TYPE_ANY)
	type = (var_type) deopt_values[jit_tag_index(program, value)];
    if (map->builtin_args == 1)
	return type == TYPE_INT
	    && jit_deopt_raw_value(program, value, deopt_values) == 0;
    if (map->builtin_args < 0 && type == TYPE_LIST) {
	Var *args = (Var *) (intptr_t)
	    jit_deopt_raw_value(program, value, deopt_values);

	return args && args[0].v.num == 1 && args[1].type == TYPE_INT
	    && args[1].v.num == 0;
    }
    return 0;
}

#ifdef JIT_TESTING
int
jit_test_deopt_map_is_suspend_zero(JITProgram *program, JITDeoptMap *map,
				    Num *deopt_values, Var *owned_values,
				    unsigned char *home_states)
{
    return jit_deopt_map_is_suspend_zero(program, map, deopt_values,
	owned_values, home_states);
}
#endif

static var_type
jit_guard_actual_type(JITProgram *program, JITDeoptMap *map, Var *env,
		      Num *deopt_values, Var *owned_values,
		      unsigned char *home_states, int operand)
{
    int value = map->guard_value[operand];
    int local = map->guard_local[operand];
    int slot;

    if (!map->guard_expected[operand])
	return TYPE_NONE;
    if (local >= 0 && local < program->num_vars && env)
	return env[local].type;
    if (value > 0 && value < program->num_values) {
	for (slot = 0; map->local_owner_slots && slot < map->num_locals; slot++)
	    if (jit_deopt_map_local_value(program, map, slot) == value
		&& map->local_owner_slots[slot] >= 0)
		return jit_owner_home(program, map->local_owner_slots[slot],
		    owned_values, home_states)->type;
	for (slot = 0; map->stack_owner_slots
	     && slot < (int) map->stack_depth; slot++)
	    if (map->stack_values[slot] == value
		&& map->stack_owner_slots[slot] >= 0)
		return jit_owner_home(program, map->stack_owner_slots[slot],
		    owned_values, home_states)->type;
	if (program->value_is_tagged && program->value_is_tagged[value])
	    return (var_type) deopt_values[jit_tag_index(program, value)];
	if (program->value_types)
	    return program->value_types[value];
    }
    return TYPE_NONE;
}

#ifdef JIT_TESTING
var_type
jit_test_guard_actual_type(JITProgram *program, JITDeoptMap *map, Var *env,
			   Num *deopt_values, Var *owned_values,
			   unsigned char *home_states, int operand)
{
    return jit_guard_actual_type(program, map, env, deopt_values,
	owned_values, home_states, operand);
}
#endif

#ifdef JIT_VERIFY_NATIVE_FRAMES
static void
jit_validate_materialized_tags(JITProgram *program, JITDeoptMap *map,
			       Num *deopt_values)
{
    int i;

    for (i = 0; i < map->num_tagged_values; i++) {
	int value = map->tagged_values[i];

	if (!jit_runtime_type_is_valid((var_type)
	    deopt_values[jit_tag_index(program, value)])) {
	    errlog("JIT: missing runtime tag for value %d at pc %u\n",
		   value, map->bytecode_pc);
	    panic("JIT runtime tag invariant violated");
	}
    }
}
#endif

static void
jit_initialize_deopt(JITProgram *program, JITDeoptState *deopt, int entry)
{
    if (!deopt)
	return;
    memset(deopt, 0, sizeof(*deopt));
    deopt->map_id = -1;
    deopt->region_exit = -1;
    deopt->builtin_func = -1;
    deopt->operation = -1;
    deopt->guard_local[0] = deopt->guard_local[1] = -1;
    if (entry && program->num_deopt_maps > 0) {
	JITDeoptMap *map = &program->deopt_maps[0];

	deopt->bytecode_pc = map->bytecode_pc;
	deopt->error_pc = map->error_pc;
	deopt->source_lineno = map->source_lineno;
	deopt->stack_depth = map->stack_depth;
	deopt->ticks_charged = map->ticks_charged;
	deopt->builtin_func = map->builtin_func;
	deopt->operation = map->operation;
	memcpy(deopt->guard_value, map->guard_value, sizeof(deopt->guard_value));
	memcpy(deopt->guard_local, map->guard_local, sizeof(deopt->guard_local));
	memcpy(deopt->guard_expected, map->guard_expected,
	       sizeof(deopt->guard_expected));
	deopt->reason = map->reason;
    }
}

static void
jit_initialize_return_deopt(JITDeoptState *deopt)
{
    if (!deopt)
	return;
    deopt->map_id = -1;
    deopt->region_exit = -1;
    deopt->materialized = 0;
    deopt->boundary = JIT_BOUNDARY_NONE;
}

JITRunResult
jit_program_execute_in_context(JITProgram *program,
			       JITExecutionContext *execution_context,
			       JITNativeFrame *native_frame, Var *env,
			       Var *result, int *ticks, int *timed_out,
			       enum error *error,
			       JITSourceLocation *source_location,
			       JITDeoptState *deopt, Var *deopt_stack,
			       Objid progr, int resume_map,
			       JITContinuationFrame *continuation_in,
			       JITContinuationFrame **continuation_out,
			       int prepared_entry)
{
    NativeFunction function;
    int64_t native_result;
    int deopt_map = -1;
    int region_exit = -1;
    Num *deopt_values;
    Var *borrowed_locals = 0;
    Var *owned_values = 0;
    unsigned *home_capacities = 0;
    unsigned char *home_states = 0;
    void *runtime_storage;
    size_t runtime_bytes;
    JITSourceLocation ignored_location;
    int runtime_from_continuation = continuation_in != 0;
    int runtime_from_frame = !continuation_in
	&& native_frame->runtime_storage != 0;
    int runtime_borrowed_from_frame = 0;
    int runtime_transferred = 0;
    int runtime_preserved_in_frame = 0;
    int returned_owned;
    int i;

    if (!execution_context || !native_frame
	|| execution_context->current_frame != native_frame
	|| native_frame->program != program || native_frame->env != env
	|| !jit_native_frame_verify_runtime(execution_context, native_frame))
	return JIT_RUN_FALLBACK;
    if (continuation_out)
	*continuation_out = 0;
    if (continuation_in) {
	if (continuation_in->program != program
	    || continuation_in->map_id <= 0
	    || continuation_in->map_id >= program->num_deopt_maps
	    || !program->deopt_maps[continuation_in->map_id].native_resume
	    || !program->deopt_maps[continuation_in->map_id].native_resume->valid)
	    return JIT_RUN_FALLBACK;
	if (continuation_in->owns_runtime) {
	    if (continuation_in->runtime_owner)
		return JIT_RUN_FALLBACK;
	} else {
	    if (continuation_in->runtime_owner != native_frame
		|| native_frame->runtime_borrower != continuation_in
		|| !native_frame->owns_runtime
		|| native_frame->runtime_storage
		   != continuation_in->runtime_storage)
		return JIT_RUN_FALLBACK;
	    runtime_borrowed_from_frame = 1;
	}
	resume_map = continuation_in->map_id;
	if (jit_profile_detail && program->usage)
	    program->usage->continuation_resumes++;
    }

    if (!source_location)
	source_location = &ignored_location;
    source_location->bytecode_pc = (unsigned) -1;
    source_location->error_pc = 0;
    source_location->source_lineno = 0;
    /* A successful return exposes only neutral boundary state.  Complete
       reconstruction metadata is initialized on a cold exit below. */
    jit_initialize_return_deopt(deopt);
    if (prepared_entry
	? (program->state != JIT_STATE_COMPILED || !program->native_function)
	: !jit_program_compile(program)) {
	jit_initialize_deopt(program, deopt, 1);
	return JIT_RUN_FALLBACK;
    }
    runtime_bytes = program->runtime_layout.bytes;
    if (runtime_from_continuation) {
	runtime_storage = continuation_in->runtime_storage;
	deopt_values = continuation_in->deopt_values;
	borrowed_locals = continuation_in->borrowed_locals;
	owned_values = continuation_in->owned_values;
	home_capacities = continuation_in->home_capacities;
	home_states = continuation_in->home_states;
    } else if (runtime_from_frame) {
	if (!native_frame->owns_runtime || native_frame->runtime_borrower
	    || resume_map <= 0
	    || native_frame->pending_resume_map != resume_map)
	    return JIT_RUN_FALLBACK;
	runtime_storage = native_frame->runtime_storage;
	deopt_values = runtime_storage;
	owned_values = native_frame->homes;
	home_capacities = native_frame->home_capacities;
	home_states = native_frame->home_states;
	if (program->num_borrowed_locals)
	    borrowed_locals = (Var *) ((char *) runtime_storage
		+ program->runtime_layout.borrowed_offset);
    } else {
	runtime_storage = jit_runtime_storage_acquire(execution_context,
					      runtime_bytes);
	deopt_values = runtime_storage;
	/* Float lowering uses raw slot zero as its native 0.0 constant. */
	deopt_values[0] = 0;
	{
	    int i;
#ifdef JIT_VERIFY_NATIVE_FRAMES
	    int tag_slots = program->value_tag_slots
		? program->num_tag_slots : program->num_values;

	    for (i = 0; i < tag_slots; i++)
		deopt_values[program->num_values + i] = TYPE_ANY;
#endif
	    if (program->num_borrowed_locals) {
		borrowed_locals = (Var *) ((char *) runtime_storage
		    + program->runtime_layout.borrowed_offset);
		for (i = 0; i < program->num_borrowed_locals; i++)
		    borrowed_locals[i] = var_ref(
			env[program->borrowed_local_slots[i]]);
	    }
	    owned_values = program->num_owned_slots
		? (Var *) ((char *) runtime_storage
		    + program->runtime_layout.owned_offset) : 0;
	    home_capacities = program->num_owned_slots
		? (unsigned *) ((char *) runtime_storage
		    + program->runtime_layout.capacities_offset) : 0;
	    home_states = program->num_owned_slots
		? (unsigned char *) runtime_storage
		    + program->runtime_layout.states_offset : 0;
	    for (i = 0; i < program->num_owned_slots; i++) {
		owned_values[i].type = TYPE_NONE;
		home_capacities[i] = 0;
		home_states[i] = JIT_HOME_EMPTY;
	    }
	}
	program->active_runtime_bytes += runtime_bytes;
    }
    jit_native_frame_bind_runtime(native_frame, runtime_storage, runtime_bytes,
	owned_values, program->num_owned_slots, home_states, home_capacities);
    if (!runtime_from_continuation)
	jit_native_frame_mark_runtime_owned(native_frame);
    function = (NativeFunction) program->native_function;
    native_result = function(execution_context, native_frame, env, result,
			     ticks, timed_out, error,
			     source_location, &deopt_map,
			     deopt_values, progr, resume_map,
			     deopt_stack,
			     continuation_in && continuation_in->has_result
			     ? &continuation_in->result
			     : native_frame->has_resume_result
			       ? &native_frame->resume_result : 0,
			     owned_values);
    if (native_result == JIT_RUN_REGION_EXIT) {
	region_exit = JIT_REGION_EXIT_DECODE(deopt_map);
	if (region_exit < 0 || region_exit >= program->num_region_exits) {
	    native_result = JIT_RUN_FALLBACK;
	    deopt_map = -1;
	} else {
	    deopt_map = program->region_exits[region_exit].caller_map;
	}
    }
    if (continuation_in && continuation_in->has_result) {
	continuation_in->has_result = 0;
	continuation_in->result.type = TYPE_NONE;
	continuation_in->result.v.num = 0;
    }
    if (native_frame->has_resume_result) {
	native_frame->has_resume_result = 0;
	native_frame->resume_result.type = TYPE_NONE;
	native_frame->resume_result.v.num = 0;
    }
    returned_owned = native_result == JIT_NATIVE_RETURNED_OWNED;
    if (native_result == JIT_RUN_RETURNED || returned_owned) {
	for (i = 0; i < program->num_owned_slots; i++)
	    home_states[i] = owned_values[i].type == TYPE_NONE
		? JIT_HOME_EMPTY : JIT_HOME_OWNED;
	if (result && returned_owned)
	    jit_take_returned_owner(program, result, owned_values, home_states,
				    home_capacities);
	else if (result)
	    *result = var_ref(*result);
	if (runtime_from_frame)
	    jit_native_frame_release_runtime(native_frame);
	if (!runtime_from_continuation && !runtime_from_frame) {
	    for (i = 0; i < program->num_borrowed_locals; i++)
		free_var(borrowed_locals[i]);
	    for (i = 0; i < program->num_owned_slots; i++)
		free_var(owned_values[i]);
	    program->active_runtime_bytes -= runtime_bytes;
	    jit_runtime_storage_recycle_sized(execution_context, runtime_storage,
					      runtime_bytes);
	}
	if (!runtime_borrowed_from_frame)
	    jit_native_frame_unbind_runtime(native_frame);
	source_location->bytecode_pc = 0;
	source_location->error_pc = 0;
	source_location->source_lineno = 0;
	return JIT_RUN_RETURNED;
    }

    /* Everything below is the cold exit path. */
    if (deopt_map < 0 && native_result != JIT_RUN_RETURNED && !returned_owned)
	jit_initialize_deopt(program, deopt, 1);
    if (source_location->bytecode_pc < (unsigned) program->num_status_locations)
	*source_location = program->status_locations[source_location->bytecode_pc];
    else {
	source_location->bytecode_pc = 0;
	source_location->error_pc = 0;
	source_location->source_lineno = 0;
    }
    if (deopt && deopt_map >= 0 && deopt_map < program->num_deopt_maps)
	deopt->map_id = deopt_map;
    for (i = 0; i < program->num_owned_slots; i++)
	home_states[i] = owned_values[i].type == TYPE_NONE
	    ? JIT_HOME_EMPTY : JIT_HOME_OWNED;
    if (native_result == JIT_RUN_FALLBACK
	|| native_result == JIT_RUN_CALL_VERB
	|| native_result == JIT_RUN_REGION_EXIT
	|| (native_result == JIT_RUN_ERROR && deopt_map >= 0)) {
	JITDeoptMap *map;
	Var *stack_values = 0;
	unsigned materialized_depth;
	unsigned stack_start = 0;
	int compact_boundary = 0;
	int suspend_zero_boundary = 0;
	int i;

	if (deopt_map < 0 || deopt_map >= program->num_deopt_maps) {
	    if (!runtime_from_continuation) {
		int i;

		for (i = 0; i < program->num_borrowed_locals; i++)
		    free_var(borrowed_locals[i]);
		for (i = 0; i < program->num_owned_slots; i++)
		    free_var(owned_values[i]);
		program->active_runtime_bytes -= runtime_bytes;
		myfree(runtime_storage, M_PROGRAM);
	    }
	    if (!runtime_borrowed_from_frame)
		jit_native_frame_unbind_runtime(native_frame);
	    return JIT_RUN_FALLBACK;
	}
	map = &program->deopt_maps[deopt_map];
#ifdef JIT_VERIFY_NATIVE_FRAMES
	jit_validate_materialized_tags(program, map, deopt_values);
#endif
	materialized_depth = map->stack_depth;
	if ((native_result == JIT_RUN_CALL_VERB
	     || native_result == JIT_RUN_REGION_EXIT) && continuation_out
	    && (map->reason == JIT_DEOPT_VERB_CALL
		|| jit_deopt_map_bridges_builtin(map))) {
	    int operands = jit_call_stack_operands(map);
	    JITContinuationFrame *frame = 0;

	    if (native_result == JIT_RUN_CALL_VERB
		&& execution_context->lazy_verb_calls
		&& map->reason == JIT_DEOPT_VERB_CALL && operands >= 0
		&& (unsigned) operands <= map->stack_depth
		&& jit_native_frame_preserve_resume(native_frame, deopt_map)) {
		runtime_transferred = 1;
		runtime_preserved_in_frame = 1;
		compact_boundary = 1;
		stack_start = map->stack_depth - operands;
		materialized_depth = operands;
	    } else if (operands >= 0
		       && (unsigned) operands <= map->stack_depth)
		frame = jit_continuation_capture(program, deopt_map,
		    deopt_values, runtime_storage, borrowed_locals,
		    owned_values, home_states, home_capacities, runtime_bytes,
		    continuation_in);

	    if (frame) {
		if (runtime_from_frame)
		    jit_native_frame_release_resume_roots(native_frame);
		*continuation_out = frame;
		runtime_transferred = 1;
		compact_boundary = 1;
		stack_start = map->stack_depth - operands;
		materialized_depth = operands;
	    }
	}
	if (compact_boundary
	    && jit_deopt_map_is_suspend_zero(program, map, deopt_values,
		owned_values, home_states)) {
	    int first_operand = map->stack_depth - jit_call_stack_operands(map);

	    suspend_zero_boundary = 1;
	    if (jit_profile_detail && program->usage)
		program->usage->continuation_fast_suspends++;
	    for (i = first_operand; i < (int) map->stack_depth; i++)
		if (map->stack_boundary_ownership
		    && map->stack_boundary_ownership[i]
		       != JIT_BOUNDARY_VALUE_RETAINED) {
		    var_type type = jit_deopt_map_stack_type(program, map, i);
		    Var discarded = jit_take_boundary_stack_value(program, map, i,
			type, deopt_values, owned_values, home_states);

		    free_var(discarded);
		}
	    stack_start = map->stack_depth;
	    materialized_depth = 0;
	}
	for (i = 0; !compact_boundary && i < map->num_locals; i++) {
	    int local_value = jit_deopt_map_local_value(program, map, i);

	    if (local_value > 0) {
		var_type type = jit_deopt_map_local_type(program, map, i);
		int owner = map->local_owner_slots
		    ? map->local_owner_slots[i] : -1;
		Var value;

		if (owner >= 0)
		    value = var_ref(*jit_owner_home(program, owner,
			owned_values, home_states));
		else {
		    if (type == TYPE_ANY)
			type = (var_type) deopt_values[jit_tag_index(program,
			    local_value)];
		    value = materialize_deopt_value(type,
			jit_deopt_raw_value(program, local_value, deopt_values));
		}

		free_var(env[i]);
		env[i] = value;
	    }
	}
	if (!suspend_zero_boundary && deopt_stack && (map->stack_depth
			    || (jit_deopt_map_is_specialized_builtin(map)
				&& map->builtin_args == 0)))
	    stack_values = deopt_stack;
	for (i = stack_start; stack_values && i < (int) map->stack_depth; i++) {
	    ResumeStackSlot slot = map->stack_slots
		? map->stack_slots[i]
		: (ResumeStackSlot){ .kind = RSS_VALUE, .data = 0 };
	    var_type type = jit_deopt_map_stack_type(program, map, i);

	    if (slot.kind != RSS_VALUE) {
		stack_values[i - stack_start].type = slot.kind == RSS_CATCH ? TYPE_CATCH
		    : slot.kind == RSS_FINALLY ? TYPE_FINALLY : TYPE_INT;
		stack_values[i - stack_start].v.num = slot.data;
		continue;
	    }
	    if (map->stack_owner_slots && map->stack_owner_slots[i] >= 0)
		type = jit_owner_home(program, map->stack_owner_slots[i],
		    owned_values, home_states)->type;
	    else if (type == TYPE_ANY)
		type = (var_type) deopt_values[jit_tag_index(program,
		    map->stack_values[i])];

	    stack_values[i - stack_start] = jit_take_boundary_stack_value(program,
		map, i, type, deopt_values, owned_values, home_states);
	}
	if (stack_values && jit_deopt_map_is_specialized_builtin(map)) {
	    int outer_depth = compact_boundary ? 0
		: map->stack_depth - map->builtin_args;
	    Var args = new_list(map->builtin_args);

	    for (i = 0; i < map->builtin_args; i++)
		args.v.list[i + 1] = stack_values[outer_depth + i];
	    stack_values[outer_depth] = args;
	    materialized_depth = outer_depth + 1;
	}
	if (deopt) {
	    deopt->map_id = deopt_map;
	    deopt->bytecode_pc = map->bytecode_pc;
	    deopt->error_pc = map->error_pc;
	    deopt->source_lineno = map->source_lineno;
	    deopt->stack_depth = materialized_depth;
	    deopt->materialized = !compact_boundary;
	    deopt->ticks_charged = map->ticks_charged;
	    deopt->builtin_func = map->builtin_func;
	    deopt->operation = map->operation;
	    deopt->region_exit = region_exit;
	    memcpy(deopt->guard_value, map->guard_value,
		   sizeof(deopt->guard_value));
	    memcpy(deopt->guard_local, map->guard_local,
		   sizeof(deopt->guard_local));
	    memcpy(deopt->guard_expected, map->guard_expected,
		   sizeof(deopt->guard_expected));
	    for (i = 0; i < JIT_MAX_GUARD_OPERANDS; i++)
		deopt->guard_actual[i] = jit_guard_actual_type(program, map,
						      env, deopt_values,
						      owned_values, home_states, i);
	    deopt->reason = map->reason;
	    if (native_result == JIT_RUN_CALL_VERB
		|| native_result == JIT_RUN_REGION_EXIT) {
		if (suspend_zero_boundary)
		    deopt->boundary = JIT_BOUNDARY_SUSPEND_ZERO;
		else if (map->reason == JIT_DEOPT_VERB_CALL)
		    deopt->boundary = JIT_BOUNDARY_VERB;
		else if (jit_deopt_map_bridges_builtin(map))
		    deopt->boundary = JIT_BOUNDARY_BUILTIN;
	    }
	}
    }

    if (runtime_from_frame && !runtime_transferred
	&& native_frame->kind != JIT_FRAME_COMPACT)
	jit_native_frame_release_runtime(native_frame);
    if (!runtime_from_continuation && !runtime_from_frame
	&& !runtime_transferred) {
	for (i = 0; i < program->num_borrowed_locals; i++)
	    free_var(borrowed_locals[i]);
	for (i = 0; i < program->num_owned_slots; i++)
	    free_var(owned_values[i]);
	program->active_runtime_bytes -= runtime_bytes;
	myfree(runtime_storage, M_PROGRAM);
    }
    if (!runtime_borrowed_from_frame && !runtime_preserved_in_frame)
	jit_native_frame_unbind_runtime(native_frame);
    return native_result;
}

JITRunResult
jit_program_execute(JITProgram *program, Var *env, Var *result,
		    int *ticks, int *timed_out, enum error *error,
		    JITSourceLocation *source_location, JITDeoptState *deopt,
		    Var *deopt_stack, Objid progr, int resume_map,
		    JITContinuationFrame *continuation_in,
		    JITContinuationFrame **continuation_out)
{
    JITExecutionContext context;
    JITNativeFrame root;
    JITRunResult run_result;

    jit_execution_context_init(&context, &root, program, env, 0, 1,
	(unsigned) -1, ticks, timed_out, error, resume_map);
    run_result = jit_program_execute_in_context(program, &context, &root,
	env, result,
	ticks, timed_out, error, source_location, deopt, deopt_stack, progr,
	resume_map, continuation_in, continuation_out, 0);
    if (!jit_execution_context_finish(&context, &root))
	panic("JIT root execution context did not detach cleanly");
    return run_result;
}

int
jit_program_dump_hir(JITProgram *program, void (*add_line)(const char *, void *),
		     void *data)
{
    JITBlock *block;
    char line[512];
    int i;

    int release_ir;

    if (!program || !program->eligible)
	return 0;
    release_ir = !program->blocks;
    if (release_ir && !jit_program_restore_ir(program))
	return 0;
    snprintf(line, sizeof(line),
	     "HIR values=%d tag-slots=%d runtime-slots=%d blocks=%d deopt-maps=%d reconstruction-states=%d region-exits=%d region-exit-values=%d potential-exits=%u elided-exits=%u type-guards=%u eliminated-type-guards=%u",
	     program->num_values, program->num_tag_slots,
	     jit_runtime_value_slots(program), program->num_blocks,
	     program->num_deopt_maps, program->num_reconstruction_states,
	     program->num_region_exits, program->num_region_exit_values,
	     program->potential_exit_sites,
	     program->elided_exit_sites, program->type_guard_sites,
	     program->eliminated_type_guard_sites);
    add_line(line, data);
    for (i = 1; i < program->num_values; i++) {
	snprintf(line, sizeof(line),
	    "v%d type=%d tagged=%d ownership=%d root=%d uses=%u escapes=%u int-list=%d", i,
	    program->value_types ? program->value_types[i] : TYPE_ANY,
	    program->value_is_tagged ? program->value_is_tagged[i] : 0,
	    program->value_ownership ? program->value_ownership[i] : 0,
	    program->value_owner_root ? program->value_owner_root[i] : -1,
	    program->value_use_counts ? program->value_use_counts[i] : 0,
	    program->value_escape_flags ? program->value_escape_flags[i] : 0,
	    program->value_is_int_list ? program->value_is_int_list[i] : 0);
	add_line(line, data);
    }
    for (block = program->blocks; block; block = block->next) {
	JITInstruction *instr;

	snprintf(line, sizeof(line), "B%d:", block->id);
	add_line(line, data);
	for (instr = block->first; instr; instr = instr->next) {
	    int tagged = instr->value > 0 && program->value_is_tagged
		&& program->value_is_tagged[instr->value];
	    int type = instr->value > 0 && program->value_types
		? program->value_types[instr->value] : TYPE_ANY;
	    int owner_homes = 0;
	    int boundary_moves = 0;
	    const char *func_name = (instr->kind == HIR_TAC_CALL
				     && instr->func < FUNC_NOT_FOUND)
		? name_func_by_num(instr->func) : "-";

	    if (instr->deopt_map > 0
		&& instr->deopt_map < program->num_deopt_maps) {
		JITDeoptMap *map = &program->deopt_maps[instr->deopt_map];
		int slot;

		for (slot = 0; map->local_owner_slots
		     && slot < map->num_locals; slot++)
		    owner_homes += map->local_owner_slots[slot] >= 0;
		for (slot = 0; map->stack_owner_slots
		     && slot < (int) map->stack_depth; slot++)
		    owner_homes += map->stack_owner_slots[slot] >= 0;
		for (slot = 0; map->stack_boundary_ownership
		     && slot < (int) map->stack_depth; slot++)
		    boundary_moves += map->stack_boundary_ownership[slot]
			!= JIT_BOUNDARY_VALUE_RETAINED;
	    }
	    snprintf(line, sizeof(line),
		     "  pc %-5u line %-5u kind=%d op=%d func=%u/%s v%d <- v%d,v%d,v%d type=%d tagged=%d local=%d guard-mask=%u guarded=%u exits=%u deopt=%d resume=%d/%d locals=%d/%d stack=%u tags=%d state=%d owner-homes=%d boundary-moves=%d last-use=%u direct-int-list=%d tick-batch=%u shift-count-proven=%d",
		     instr->bytecode_pc, instr->source_lineno, instr->kind,
		     instr->op, instr->func, func_name, instr->value,
		     instr->src1, instr->src2,
		     instr->src3,
		     type, tagged, instr->local_id,
		     instr->guarded_type_masks[0] | instr->guarded_type_masks[1],
		     instr->guarded_operands, instr->exit_mask,
		     instr->deopt_map,
		     instr->deopt_map > 0
		     && program->deopt_maps[instr->deopt_map].native_resume
		     ? program->deopt_maps[instr->deopt_map].native_resume->valid : -1,
		     instr->deopt_map > 0
		     && program->deopt_maps[instr->deopt_map].native_resume
		     ? program->deopt_maps[instr->deopt_map].native_resume->rehydratable
		     : -1,
		     instr->deopt_map > 0
		     ? program->deopt_maps[instr->deopt_map].num_local_values : 0,
		     instr->deopt_map > 0
		     ? program->deopt_maps[instr->deopt_map].num_locals : 0,
		     instr->deopt_map > 0
		     ? program->deopt_maps[instr->deopt_map].stack_depth : 0,
		     instr->deopt_map > 0
		     ? program->deopt_maps[instr->deopt_map].num_tagged_values : 0,
		     instr->deopt_map > 0
		     ? program->deopt_maps[instr->deopt_map].reconstruction_state : -1,
		     owner_homes, boundary_moves, instr->owned_last_use,
		     instr->direct_int_list_index_set,
		     instr->tick_batch_count == (unsigned char) -1
		     ? 0 : instr->tick_batch_count,
		     instr->shift_count_proven_valid);
	    add_line(line, data);
	    if (instr->deopt_map > 0
		&& program->deopt_maps[instr->deopt_map].native_resume) {
		JITNativeResume *resume =
		    program->deopt_maps[instr->deopt_map].native_resume;
		int j;

		if (instr->kind == HIR_TAC_CALL_VERB) {
		    int region_leaf;
		    unsigned region_hits;
		    uint64_t spliced_generation;

		    jit_region_site_status(program, instr->deopt_map,
			&region_leaf, &region_hits, &spliced_generation);
		    snprintf(line, sizeof(line),
			     "    region target=%s leaf=%d hits=%u generation=%" PRIu64
			     " spliced=%d",
			     resume->cached_verb ? resume->cached_verb : "-",
			     region_leaf, region_hits,
			     resume->cached_jit_generation,
			     spliced_generation == program->pool_generation);
		    add_line(line, data);
		}

		for (j = 0; j < resume->num_values; j++) {
		    JITResumeValue *value = &resume->values[j];

		    snprintf(line, sizeof(line),
			     "    resume v%d source=%d index=%d type=%d tagged=%d",
			     value->value, value->source, value->index,
			     program->value_types[value->value],
			     program->value_is_tagged[value->value]);
		    add_line(line, data);
		}
	    }
	    if (instr->kind == HIR_TAC_PARALLEL_COPY) {
		JITCopy *copy;

		for (copy = instr->copies; copy; copy = copy->next) {
		    snprintf(line, sizeof(line), "    v%d <- v%d",
			     copy->dst, copy->src);
		    add_line(line, data);
		}
	    }
	    if (instr == block->last)
		break;
	}
    }
    if (release_ir)
	jit_program_release_ir(program, 0);
    return 1;
}

int
jit_program_dump_mir(JITProgram *program, void (*add_line)(const char *, void *),
		     void *data)
{
    JITMIRAllocator *allocator;
    MIR_context_t context;
    MIRBuild build;
    FILE *file;
    char line[1024];
    int release_ir;

    if (!program || !program->eligible)
	return 0;
    release_ir = !program->blocks;
    if (release_ir && !jit_program_restore_ir(program))
	return 0;
    allocator = jit_mir_allocator_new();
    if (!allocator)
	goto failure;
    context = MIR_init2(&allocator->interface, 0);
    if (!context) {
	jit_mir_allocator_free(allocator);
	goto failure;
    }
    jit_load_externals(context);
    if (!build_mir(program, &build, context)) {
	MIR_finish(context);
	jit_mir_allocator_free(allocator);
	goto failure;
    }
    file = tmpfile();
    if (!file) {
	MIR_finish(context);
	jit_mir_allocator_free(allocator);
	goto failure;
    }
    MIR_output_module(context, file, build.module);
    rewind(file);
    while (fgets(line, sizeof(line), file)) {
	size_t length = strlen(line);
	if (length && line[length - 1] == '\n')
	    line[length - 1] = '\0';
	add_line(line, data);
    }
    fclose(file);
    MIR_finish(context);
    jit_mir_allocator_free(allocator);
    if (release_ir)
	jit_program_release_ir(program, 0);
    return 1;

failure:
    if (release_ir)
	jit_program_release_ir(program, 0);
    return 0;
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
    int builtin_func;
    int operation;
    unsigned bytecode_pc;
    unsigned source_lineno;
    JITDeoptReason reason;
    int guard_value[JIT_MAX_GUARD_OPERANDS];
    int guard_local[JIT_MAX_GUARD_OPERANDS];
    JITTypeMask guard_expected[JIT_MAX_GUARD_OPERANDS];
    var_type guard_actual[JIT_MAX_GUARD_OPERANDS];
    uint64_t count;
    struct JITDeoptSite *next;
} JITDeoptSite;

#define JIT_DEOPT_HASH_SIZE 256
static JITDeoptSite *deopt_sites_hash[JIT_DEOPT_HASH_SIZE];
static uint64_t jit_use_generation = 0;
static uint64_t total_jit_entries = 0;
static uint64_t total_jit_completed = 0;
static uint64_t total_vm_calls = 0;
static uint64_t total_deopts = 0;
static uint64_t deopt_reason_counts[JIT_DEOPT_NUM_REASONS];
static uint64_t unsupported_operation_counts[HIR_OP_FORK + 1];
static time_t last_deopt_report_time = 0;

static const char *
jit_profile_type_name(var_type type)
{
    switch ((unsigned) type & TYPE_DB_MASK) {
    case TYPE_INT: return "int";
    case TYPE_OBJ: return "obj";
    case _TYPE_STR: return "str";
    case TYPE_ERR: return "err";
    case _TYPE_LIST: return "list";
    case TYPE_CLEAR: return "clear";
    case TYPE_NONE: return "none";
    case TYPE_CATCH: return "catch";
    case TYPE_FINALLY: return "finally";
    case _TYPE_FLOAT: return "float";
    case _TYPE_WAIF: return "waif";
    default: return "invalid";
    }
}

static void
jit_format_guard(char *buffer, size_t size, const int *values,
		 const int *locals, const JITTypeMask *expected,
		 const var_type *actual)
{
    int i;
    size_t used = 0;

    buffer[0] = '\0';
    for (i = 0; i < JIT_MAX_GUARD_OPERANDS; i++) {
	int type;
	int first = 1;
	int n;

	if (!expected[i])
	    continue;
	n = snprintf(buffer + used, size - used, "%s[v%d%s%d expected=",
		     used ? " " : " [guard ", values[i],
		     locals[i] >= 0 ? " local=" : " operand=",
		     locals[i] >= 0 ? locals[i] : i);
	if (n < 0 || (size_t) n >= size - used)
	    break;
	used += n;
	for (type = TYPE_INT; type <= _TYPE_WAIF; type++)
	    if (expected[i] & JIT_TYPE_MASK(type)) {
		n = snprintf(buffer + used, size - used, "%s%s",
			     first ? "" : "|", jit_profile_type_name((var_type) type));
		if (n < 0 || (size_t) n >= size - used)
		    break;
		used += n;
		first = 0;
	    }
	n = snprintf(buffer + used, size - used, " actual=%s]",
		     jit_profile_type_name(actual[i]));
	if (n < 0 || (size_t) n >= size - used)
	    break;
	used += n;
    }
    if (used && used + 1 < size) {
	buffer[used++] = ']';
	buffer[used] = '\0';
    }
}

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

static JITProgramUsage *
jit_program_usage(JITProgram *program)
{
    if (!program)
	return 0;
    if (!program->usage) {
	program->usage = mymalloc(sizeof(JITProgramUsage), M_PROGRAM);
	memset(program->usage, 0, sizeof(JITProgramUsage));
    }
    return program->usage;
}

void
jit_profile_record_entry(JITProgram *program)
{
    total_jit_entries++;
    jit_program_note_activity(program);

    if (jit_profile_detail && program) {
	jit_program_usage(program);
	if (!jit_profile_detail_time)
	    jit_profile_detail_time = time(0);
	program->usage->entries++;
	program->usage->last_used_generation = ++jit_use_generation;
	program->usage->last_used_time = jit_profile_detail_time;
    }
}

void
jit_profile_record_completed(JITProgram *program)
{
    total_jit_completed++;
    if (jit_profile_detail && program && program->usage)
	program->usage->completions++;
}

void
jit_profile_record_vm_call(JITProgram *program)
{
    total_vm_calls++;
    if (jit_profile_detail && program && program->usage)
	program->usage->vm_calls++;
}

void
jit_profile_record_native_call(JITExecutionContext *context)
{
    JITNativeFrame *frame;
    uint64_t depth;

    if (!jit_profile_detail || !context
	|| !(frame = context->current_frame) || !frame->caller)
	return;
    jit_program_usage(frame->caller->program)->native_chain_calls++;
    depth = context->native_depth + 1;
    for (; frame; frame = frame->caller) {
	JITProgramUsage *usage = jit_program_usage(frame->program);

	if (usage->native_chain_max_depth < depth)
	    usage->native_chain_max_depth = depth;
    }
}

void
jit_profile_record_native_return(JITNativeFrame *caller)
{
    if (jit_profile_detail && caller && caller->program)
	jit_program_usage(caller->program)->native_chain_returns++;
}

void
jit_profile_record_native_promotion(JITNativeFrame *frame)
{
    if (jit_profile_detail && frame && frame->program)
	jit_program_usage(frame->program)->native_chain_promotions++;
}

void
jit_profile_native_frame_acquired(JITNativeFrame *frame, size_t bytes)
{
    if (!frame || !frame->program || !bytes)
	return;
    frame->program->active_native_frames++;
    frame->program->active_native_frame_bytes += bytes;
}

void
jit_profile_native_frame_released(JITNativeFrame *frame, size_t bytes)
{
    JITProgram *program;

    if (!frame || !(program = frame->program) || !bytes)
	return;
    if (!program->active_native_frames
	|| program->active_native_frame_bytes < bytes)
	panic("Native call-frame accounting underflow");
    program->active_native_frames--;
    program->active_native_frame_bytes -= bytes;
}

void
jit_profile_record_deopt(JITProgram *program, Objid vloc, const char *verbname,
			 const JITDeoptState *deopt)
{
    JITDeoptReason reason = (deopt && (int) deopt->reason >= 0
	&& deopt->reason < JIT_DEOPT_NUM_REASONS)
	? deopt->reason : JIT_DEOPT_UNSUPPORTED_OP;
    Num log_mode;
    int builtin_func = reason == JIT_DEOPT_BUILTIN_CALL && deopt
	? deopt->builtin_func : -1;
    int operation = deopt ? deopt->operation : -1;
    const char *builtin_name = builtin_func >= 0
	? name_func_by_num((unsigned) builtin_func) : 0;
    char operation_label[32];
    char guard_label[256];
    const char *operation_name = 0;
    unsigned h;
    JITDeoptSite *site;

    total_deopts++;
    deopt_reason_counts[reason]++;
    if (program && program->usage) {
	program->usage->deopts++;
	if (program->usage->deopts_by_reason[reason] < UINT32_MAX)
	    program->usage->deopts_by_reason[reason]++;
    }
    if (operation >= 0 && operation <= HIR_OP_FORK) {
	snprintf(operation_label, sizeof(operation_label), "op=%d", operation);
	operation_name = operation_label;
    }
    if (reason == JIT_DEOPT_UNSUPPORTED_OP && operation_name)
	unsupported_operation_counts[operation]++;
    guard_label[0] = '\0';
    if (deopt)
	jit_format_guard(guard_label, sizeof(guard_label), deopt->guard_value,
			 deopt->guard_local, deopt->guard_expected,
			 deopt->guard_actual);

    log_mode = server_int_option("jit_deopt_log_mode", 0);
    if (log_mode == 1) {
	oklog("JIT_DEOPT: #%"PRIdN":%s line %u (pc %u): %s%s%s%s%s%s%s%s\n",
	      vloc, verbname ? verbname : "?",
	      deopt ? deopt->source_lineno : 0,
	      deopt ? deopt->bytecode_pc : 0,
	      jit_deopt_reason_name(reason), builtin_name ? " [" : "",
	      builtin_name ? builtin_name : "", builtin_name ? "]" : "",
	      operation_name ? " [" : "", operation_name ? operation_name : "",
	      operation_name ? "]" : "", guard_label);
    }

    h = ((unsigned) vloc * 31 + (deopt ? deopt->bytecode_pc : 0) * 17
	 + (unsigned) reason + (unsigned) (builtin_func + 1) * 13
	 + (unsigned) (operation + 1) * 19)
	% JIT_DEOPT_HASH_SIZE;
    for (site = deopt_sites_hash[h]; site; site = site->next) {
	if (site->vloc == vloc
	    && site->bytecode_pc == (deopt ? deopt->bytecode_pc : 0)
	    && site->reason == reason
	    && site->builtin_func == builtin_func
	    && site->operation == operation
	    && ((!site->verbname && !verbname)
		|| (site->verbname && verbname && strcmp(site->verbname, verbname) == 0))) {
	    site->count++;
	    if (deopt)
		memcpy(site->guard_actual, deopt->guard_actual,
		       sizeof(site->guard_actual));
	    return;
	}
    }
    site = mymalloc(sizeof(JITDeoptSite), M_PROGRAM);
    site->vloc = vloc;
    site->verbname = verbname ? str_dup(verbname) : 0;
    site->builtin_func = builtin_func;
    site->operation = operation;
    site->bytecode_pc = deopt ? deopt->bytecode_pc : 0;
    site->source_lineno = deopt ? deopt->source_lineno : 0;
    site->reason = reason;
    if (deopt) {
	memcpy(site->guard_value, deopt->guard_value,
	       sizeof(site->guard_value));
	memcpy(site->guard_local, deopt->guard_local,
	       sizeof(site->guard_local));
	memcpy(site->guard_expected, deopt->guard_expected,
	       sizeof(site->guard_expected));
	memcpy(site->guard_actual, deopt->guard_actual,
	       sizeof(site->guard_actual));
    }
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
    oklog("JIT: Total entries: %"PRIu64" | Completed: %"PRIu64" (%.2f%%) | VM calls: %"PRIu64" (%.2f%%) | Deopts: %"PRIu64" (%.2f%%)\n",
	  total_jit_entries,
	  total_jit_completed,
	  total_jit_entries > 0 ? (100.0 * (double) total_jit_completed / (double) total_jit_entries) : 0.0,
	  total_vm_calls,
	  total_jit_entries > 0 ? (100.0 * (double) total_vm_calls / (double) total_jit_entries) : 0.0,
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

    if (deopt_reason_counts[JIT_DEOPT_UNSUPPORTED_OP] > 0) {
	oklog("JIT: Unsupported Operation Breakdown:\n");
	for (i = 0; i <= HIR_OP_FORK; i++)
	    if (unsupported_operation_counts[i] > 0)
		oklog("JIT:   op=%-19d: %10"PRIu64"\n", i,
		      unsupported_operation_counts[i]);
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
	    const char *builtin_name = s->builtin_func >= 0
		? name_func_by_num((unsigned) s->builtin_func) : 0;
	    char operation_label[32];
	    const char *operation_name = 0;
	    char guard_label[256];
	    if (s->operation >= 0 && s->operation <= HIR_OP_FORK) {
		snprintf(operation_label, sizeof(operation_label), "op=%d",
			 s->operation);
		operation_name = operation_label;
	    }
	    jit_format_guard(guard_label, sizeof(guard_label), s->guard_value,
			     s->guard_local, s->guard_expected,
			     s->guard_actual);
	    oklog("JIT:   #%"PRIdN":%s line %u (pc %u): %s%s%s%s%s%s%s%s (count: %"PRIu64")\n",
		  s->vloc, s->verbname ? s->verbname : "?",
		  s->source_lineno, s->bytecode_pc,
		  jit_deopt_reason_name(s->reason),
		  builtin_name ? " [" : "", builtin_name ? builtin_name : "",
		  builtin_name ? "]" : "",
		  operation_name ? " [" : "",
		  operation_name ? operation_name : "",
		  operation_name ? "]" : "", guard_label,
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

    jit_profile_detail_time = now;

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

int
jit_profile_detail_enabled(void)
{
    return jit_profile_detail;
}

void
jit_profile_set_detail(int enabled)
{
    enabled = !!enabled;
    if (enabled && !jit_profile_detail)
	jit_profile_detail_time = time(0);
    jit_profile_detail = enabled;
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
    total_vm_calls = 0;
    total_deopts = 0;
    memset(deopt_reason_counts, 0, sizeof(deopt_reason_counts));
    memset(unsupported_operation_counts, 0,
	   sizeof(unsupported_operation_counts));
    last_deopt_report_time = 0;
}
