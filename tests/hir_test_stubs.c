#include "db.h"
#include "functions.h"
#include "list.h"
#include "log.h"
#include "ref_count.h"
#include "server.h"
#include "storage.h"
#include "utils.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static inline int
refcount_overhead(Memory_Type type)
{
    switch (type) {
    case M_FLOAT:
	return sizeof(FlNum) > sizeof(int) ? sizeof(FlNum) : sizeof(int);
    case M_STRING:
#ifdef MEMO_STRLEN
	return sizeof(int) + sizeof(int);
#else
	return sizeof(int);
#endif
    case M_LIST:
	return sizeof(Var *) > sizeof(int) ? sizeof(Var *) : sizeof(int);
    default:
	return 0;
    }
}

void
panic(const char *message)
{
    fprintf(stderr, "PANIC: %s\n", message);
    abort();
}

void *
mymalloc(unsigned size, Memory_Type type)
{
    char *ptr;
    int offs = refcount_overhead(type);

    ptr = malloc(size + offs);
    if (!ptr) {
	fprintf(stderr, "mymalloc failed\n");
	abort();
    }
    if (offs) {
	ptr += offs;
	((int *) ptr)[-1] = 1;
    }

    return ptr;
}

void *
myrealloc(void *where, unsigned size, Memory_Type type)
{
    int offs = refcount_overhead(type);
    char *ptr;

    if (!where)
	return mymalloc(size, type);
    ptr = realloc((char *) where - offs, size + offs);
    if (!ptr) {
	fprintf(stderr, "myrealloc failed\n");
	abort();
    }

    return ptr + offs;
}

void
myfree(const void *where, Memory_Type type)
{
    int offs = refcount_overhead(type);

    if (where)
	free((char *) where - offs);
}

void
complex_free_var(Var value)
{
    if (value.type == TYPE_STR)
	free_str(value.v.str);
    else if (value.type == TYPE_LIST) {
	if (delref(value.v.list) == 0) {
	    int i;

	    for (i = value.v.list[0].v.num; i > 0; i--)
		free_var(value.v.list[i]);
	    myfree(value.v.list, M_LIST);
	}
    }
}

Var
complex_var_ref(Var value)
{
    if (value.type == TYPE_STR)
	addref(value.v.str);
    else if (value.type == TYPE_LIST)
	addref(value.v.list);
    return value;
}

int
var_refcount(Var v)
{
    if (v.type == TYPE_STR)
	return refcount(v.v.str);
    if (v.type == TYPE_LIST)
	return refcount(v.v.list);
    return 1;
}

const char *
name_func_by_num(unsigned id)
{
    switch (id) {
    case 1: return "toint";
    case 2: return "typeof";
    case 3: return "abs";
    case 4: return "min";
    case 5: return "max";
    case 6: return "length";
    default: return "unknown_func";
    }
}

const char *
str_ref(const char *s)
{
    addref(s);
    return s;
}

char *
str_dup(const char *s)
{
    char *r;

    if (!s)
	s = "";
    r = (char *) mymalloc(strlen(s) + 1, M_STRING);
    strcpy(r, s);
    return r;
}

Var
new_list(int size)
{
    Var new;

    new.type = TYPE_LIST;
    new.v.list = (Var *) mymalloc((size + 1) * sizeof(Var), M_LIST);
    new.v.list[0].type = TYPE_INT;
    new.v.list[0].v.num = size;
    return new;
}

Num _server_int_option_cache[256] = {
    [SVO_MAX_STRING_CONCAT] = 1000000,
    [SVO_MAX_LIST_CONCAT] = 1000000
};

int
is_true(Var v)
{
    return ((v.type == TYPE_INT && v.v.num != 0)
	    || (v.type == TYPE_FLOAT && fl_unbox(v.v.fnum) != 0.0)
	    || (v.type == TYPE_STR && v.v.str && *v.v.str != '\0')
	    || (v.type == TYPE_LIST && v.v.list[0].v.num != 0));
}

int
mystrcasecmp(const char *s1, const char *s2)
{
    if (!s1)
	s1 = "";
    if (!s2)
	s2 = "";
    return strcasecmp(s1, s2);
}


int
equality(Var lhs, Var rhs, int case_matters)
{
    if (lhs.type != rhs.type)
	return 0;
    switch (lhs.type) {
    case TYPE_INT:
	return lhs.v.num == rhs.v.num;
    case TYPE_FLOAT:
	return fl_unbox(lhs.v.fnum) == fl_unbox(rhs.v.fnum);
    case TYPE_OBJ:
	return lhs.v.obj == rhs.v.obj;
    case TYPE_ERR:
	return lhs.v.err == rhs.v.err;
    case TYPE_STR:
	return case_matters ? !strcmp(lhs.v.str, rhs.v.str)
			    : !strcasecmp(lhs.v.str, rhs.v.str);
    case TYPE_LIST:
	if (lhs.v.list[0].v.num != rhs.v.list[0].v.num)
	    return 0;
	if (lhs.v.list == rhs.v.list)
	    return 1;
	for (int i = 1; i <= lhs.v.list[0].v.num; i++) {
	    if (!equality(lhs.v.list[i], rhs.v.list[i], case_matters))
		return 0;
	}
	return 1;
    default:
	return 0;
    }
}

Var
listconcat(Var first, Var second)
{
    int len1 = first.v.list[0].v.num;
    int len2 = second.v.list[0].v.num;
    Var result = new_list(len1 + len2);
    int i;

    for (i = 1; i <= len1; i++)
	result.v.list[i] = var_ref(first.v.list[i]);
    for (i = 1; i <= len2; i++)
	result.v.list[len1 + i] = var_ref(second.v.list[i]);
    return result;
}

Var
listappend(Var list, Var value)
{
    int len = list.v.list[0].v.num;
    Var result = new_list(len + 1);
    int i;

    for (i = 1; i <= len; i++)
	result.v.list[i] = var_ref(list.v.list[i]);
    result.v.list[len + 1] = var_ref(value);
    return result;
}

int
ismember(Var value, Var list, int case_matters)
{
    int len, i;

    if (list.type != TYPE_LIST)
	return 0;
    len = list.v.list[0].v.num;
    for (i = 1; i <= len; i++) {
	if (equality(value, list.v.list[i], case_matters))
	    return i;
    }
    return 0;
}

int
valid(Objid oid)
{
    return oid >= 0;
}

int
is_wizard(Objid oid)
{
    return oid == 2 || oid == 3;
}

db_prop_handle
db_find_property(Objid oid, const char *name, Var *value)
{
    db_prop_handle h;

    memset(&h, 0, sizeof(h));
    if (oid >= 0 && name && *name) {
	h.ptr = (void *) 0x1;
	if (value) {
	    value->type = TYPE_INT;
	    value->v.num = 123;
	}
    }
    return h;
}

int
db_property_allows(db_prop_handle h, Objid progr, db_prop_flag flag)
{
    (void) h;
    (void) progr;
    (void) flag;
    return 1;
}

Num
server_int_option(const char *name, Num defallt)
{
    (void) name;
    return defallt;
}

void
oklog(const char *fmt, ...)
{
    (void) fmt;
}
