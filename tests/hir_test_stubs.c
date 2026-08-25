#include "functions.h"
#include "storage.h"
#include "utils.h"

#include <stdio.h>
#include <stdlib.h>

void *
mymalloc(unsigned size, Memory_Type type)
{
    void *ptr;

    (void) type;
    ptr = malloc(size);
    if (!ptr) {
	fprintf(stderr, "mymalloc failed\n");
	abort();
    }

    return ptr;
}

void *
myrealloc(void *where, unsigned size, Memory_Type type)
{
    void *ptr;

    (void) type;
    ptr = realloc(where, size);
    if (!ptr) {
	fprintf(stderr, "myrealloc failed\n");
	abort();
    }

    return ptr;
}

void
myfree(const void *where, Memory_Type type)
{
    (void) type;
    free((void *) where);
}

void
complex_free_var(Var value)
{
    (void) value;
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
