#include "functions.h"
#include "list.h"
#include "ref_count.h"
#include "storage.h"
#include "utils.h"

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
