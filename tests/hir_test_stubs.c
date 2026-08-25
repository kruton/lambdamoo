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
