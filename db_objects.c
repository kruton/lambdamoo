/******************************************************************************
  Copyright (c) 1995, 1996 Xerox Corporation.  All rights reserved.
  Portions of this code were written by Stephen White, aka ghond.
  Use and copying of this software and preparation of derivative works based
  upon this software are permitted.  Any distribution of this software or
  derivative works must comply with all applicable United States export
  control laws.  This software is made available AS IS, and Xerox Corporation
  makes no warranty about the software, its performance or its conformity to
  any specification.  Any person obtaining a copy of this software is requested
  to send their name and post office or electronic mail address to:
    Pavel Curtis
    Xerox PARC
    3333 Coyote Hill Rd.
    Palo Alto, CA 94304
    Pavel@Xerox.Com
 *****************************************************************************/

/*****************************************************************************
 * Routines for manipulating DB objects
 *****************************************************************************/

#include "db.h"
#include "db_private.h"

#include "config.h"
#include "options.h"

#include "my-string.h"

#include "list.h"
#include "program.h"
#include "storage.h"
#include "utils.h"
#include "waif.h"

static Object **objects;
static int num_objects = 0;
static int max_objects = 0;

static Var all_users;

typedef struct Object_Delta Object_Delta;

struct Object_Delta {
    Objid oid;
    Object *object;
    int frozen_nprops;
    Object_Delta *bucket_next;
    Object_Delta *next;
};

#define INITIAL_DELTA_BUCKETS 127

static Object_Delta **delta_buckets = NULL;
static size_t num_delta_buckets = 0;
static size_t num_deltas = 0;
static Object_Delta *delta_list = NULL;
static int checkpoint_num_objects = 0;

static void ensure_object_capacity(int needed);

static size_t
delta_bucket(Objid oid, size_t buckets)
{
    return (size_t) ((UNum) oid % buckets);
}

static Object_Delta *
find_delta(Objid oid)
{
    Object_Delta *delta;

    if (!delta_buckets)
	return NULL;
    for (delta = delta_buckets[delta_bucket(oid, num_delta_buckets)];
	 delta; delta = delta->bucket_next)
	if (delta->oid == oid)
	    return delta;
    return NULL;
}

static void
grow_delta_table(void)
{
    size_t new_count = num_delta_buckets * 2 + 1;
    Object_Delta **new_buckets;
    Object_Delta *delta;

    new_buckets = mymalloc(new_count * sizeof(*new_buckets), M_OBJECT_TABLE);
    memset(new_buckets, 0, new_count * sizeof(*new_buckets));
    for (delta = delta_list; delta; delta = delta->next) {
	size_t bucket = delta_bucket(delta->oid, new_count);

	delta->bucket_next = new_buckets[bucket];
	new_buckets[bucket] = delta;
    }
    myfree(delta_buckets, M_OBJECT_TABLE);
    delta_buckets = new_buckets;
    num_delta_buckets = new_count;
}

static Object_Delta *
new_delta(Objid oid, Object *object, int frozen_nprops)
{
    Object_Delta *delta;
    size_t bucket;

    if (num_deltas >= num_delta_buckets * 2)
	grow_delta_table();
    delta = mymalloc(sizeof(*delta), M_OBJECT_TABLE);
    delta->oid = oid;
    delta->object = object;
    delta->frozen_nprops = frozen_nprops;
    bucket = delta_bucket(oid, num_delta_buckets);
    delta->bucket_next = delta_buckets[bucket];
    delta_buckets[bucket] = delta;
    delta->next = delta_list;
    delta_list = delta;
    num_deltas++;
    return delta;
}

static void
free_object(Object *o, int nprops)
{
    Verbdef *v, *next;
    int i;

    free_str(o->name);
    for (i = 0; i < o->propdefs.cur_length; i++)
	free_str(o->propdefs.l[i].name);
    for (i = 0; i < nprops; i++)
	free_var(o->propval[i].var);
    if (o->propval)
	myfree(o->propval, M_PVAL);
    if (o->propdefs.l)
	myfree(o->propdefs.l, M_PROPDEF);
    for (v = o->verbdefs; v; v = next) {
	next = v->next;
	if (v->program)
	    free_program(v->program);
	free_str(v->name);
	myfree(v, M_VERBDEF);
    }
#ifdef WAIF_CORE
    free_waif_propdefs(o->waif_propdefs);
#endif
    myfree(o, M_OBJECT);
}

static Object *
clone_object(Object *old, int nprops)
{
    Object *o = mymalloc(sizeof(*o), M_OBJECT);
    Verbdef **tail = &o->verbdefs;
    Verbdef *v;
    int i;

    *o = *old;
    o->name = str_ref(old->name);
    o->verbdefs = NULL;
    for (v = old->verbdefs; v; v = v->next) {
	Verbdef *copy = mymalloc(sizeof(*copy), M_VERBDEF);

	*copy = *v;
	copy->name = str_ref(v->name);
	if (copy->program)
	    copy->program = program_ref(copy->program);
	copy->next = NULL;
	*tail = copy;
	tail = &copy->next;
    }
    o->propdefs.l = NULL;
    if (old->propdefs.max_length) {
	o->propdefs.l = mymalloc(old->propdefs.max_length * sizeof(Propdef),
				    M_PROPDEF);
	for (i = 0; i < old->propdefs.cur_length; i++) {
	    o->propdefs.l[i] = old->propdefs.l[i];
	    o->propdefs.l[i].name = str_ref(old->propdefs.l[i].name);
	}
    }
    o->propval = NULL;
    if (nprops) {
	o->propval = mymalloc(nprops * sizeof(Pval), M_PVAL);
	for (i = 0; i < nprops; i++) {
	    o->propval[i] = old->propval[i];
	    o->propval[i].var = var_ref(old->propval[i].var);
	}
    }
#ifdef WAIF_CORE
    o->waif_propdefs = old->waif_propdefs
	? ref_waif_propdefs(old->waif_propdefs) : NULL;
#endif
    return o;
}


/*********** Objects qua objects ***********/

Object *
dbpriv_find_object(Objid oid)
{
    Object_Delta *delta;

    if (oid < 0 || oid >= num_objects)
	return NULL;
    if (!delta_buckets)
	return objects[oid];
    delta = find_delta(oid);
    return delta ? delta->object : objects[oid];
}

Object *
dbpriv_find_frozen_object(Objid oid)
{
    if (oid < 0 || oid >= checkpoint_num_objects)
	return NULL;
    return objects[oid];
}

Objid
dbpriv_frozen_last_used_objid(void)
{
    return checkpoint_num_objects - 1;
}

int
dbpriv_checkpoint_active(void)
{
    return delta_buckets != NULL;
}

int
dbpriv_checkpoint_begin(void)
{
    if (delta_buckets)
	return 0;
    num_delta_buckets = INITIAL_DELTA_BUCKETS;
    delta_buckets = mymalloc(num_delta_buckets * sizeof(*delta_buckets),
			     M_OBJECT_TABLE);
    memset(delta_buckets, 0,
	   num_delta_buckets * sizeof(*delta_buckets));
    num_deltas = 0;
    delta_list = NULL;
    checkpoint_num_objects = num_objects;
    return 1;
}

Object *
dbpriv_checkpoint_touch_object(Objid oid)
{
    Object_Delta *delta;
    Object *old;
    int nprops;

    if (!delta_buckets)
	return dbpriv_find_object(oid);
    delta = find_delta(oid);
    if (delta)
	return delta->object;
    old = dbpriv_find_frozen_object(oid);
    if (!old)
	return NULL;
    nprops = dbpriv_count_properties(oid);
    delta = new_delta(oid, clone_object(old, nprops), nprops);
    return delta->object;
}

void
dbpriv_checkpoint_merge(void)
{
    Object_Delta *delta, *next;

    if (!delta_buckets)
	return;
    if (delta_list)
	/* Cached handles may point into frozen Verbdef lists.  Invalidate them
	 * before freeing any frozen objects during the overlay merge.
	 */
	db_priv_affected_callable_verb_lookup();
    ensure_object_capacity(num_objects);
    for (delta = delta_list; delta; delta = delta->next) {
	Object *old = delta->oid < checkpoint_num_objects
	    ? objects[delta->oid] : NULL;

	if (old)
	    free_object(old, delta->frozen_nprops);
	objects[delta->oid] = delta->object;
    }
    for (delta = delta_list; delta; delta = next) {
	next = delta->next;
	myfree(delta, M_OBJECT_TABLE);
    }
    myfree(delta_buckets, M_OBJECT_TABLE);
    delta_buckets = NULL;
    delta_list = NULL;
    num_delta_buckets = num_deltas = 0;
    checkpoint_num_objects = 0;
}

int
valid(Objid oid)
{
    return dbpriv_find_object(oid) != 0;
}

Objid
db_last_used_objid(void)
{
    return num_objects - 1;
}

void
db_reset_last_used_objid(void)
{
    while (num_objects > 0 && !dbpriv_find_object(num_objects - 1))
	num_objects--;
}

static void
ensure_object_capacity(int needed)
{
    if (needed > max_objects) {
	int i, new_max = max_objects ? max_objects : 100;
	Object **new_objects;

	while (new_max < needed)
	    new_max *= 2;
	new_objects = mymalloc(new_max * sizeof(Object *), M_OBJECT_TABLE);
	for (i = 0; i < max_objects; i++)
	    new_objects[i] = objects[i];
	for (i = max_objects; i < new_max; i++)
	    new_objects[i] = NULL;
	if (objects)
	    myfree(objects, M_OBJECT_TABLE);
	objects = new_objects;
	max_objects = new_max;
    }
}

Object *
dbpriv_new_object(void)
{
    Object *o;

    if (!delta_buckets)
	ensure_object_capacity(num_objects + 1);
    o = mymalloc(sizeof(Object), M_OBJECT);
    o->id = num_objects;
#ifdef WAIF_CORE
    o->waif_propdefs = NULL;
#endif
    if (delta_buckets)
	new_delta(num_objects, o, 0);
    else
	objects[num_objects] = o;
    num_objects++;

    return o;
}

void
dbpriv_new_recycled_object(void)
{
    ensure_object_capacity(num_objects + 1);
    objects[num_objects++] = NULL;
}

Objid
db_create_object(void)
{
    Object *o;
    Objid oid;

    o = dbpriv_new_object();
    oid = o->id;

    o->name = str_dup("");
    o->flags = 0;
    o->parent = o->child = o->sibling = NOTHING;
    o->location = o->contents = o->next = NOTHING;

    o->propval = 0;

    o->propdefs.max_length = 0;
    o->propdefs.cur_length = 0;
    o->propdefs.l = 0;

    o->verbdefs = 0;

    return oid;
}

void
db_destroy_object(Objid oid)
{
    Object *o = dbpriv_find_object(oid);
    Object_Delta *delta;
    int nprops;

    db_priv_affected_callable_verb_lookup();

    if (!o)
	panic("DB_DESTROY_OBJECT: Invalid object!");

    if (o->location != NOTHING || o->contents != NOTHING
	|| o->parent != NOTHING || o->child != NOTHING)
	panic("DB_DESTROY_OBJECT: Not a barren orphan!");

    if (is_user(oid)) {
	Var t;

	t.type = TYPE_OBJ;
	t.v.obj = oid;
	all_users = setremove(all_users, t);
    }
    nprops = dbpriv_count_properties(oid);
    if (!delta_buckets) {
	free_object(o, nprops);
	objects[oid] = NULL;
	return;
    }

    delta = find_delta(oid);
    if (delta) {
	if (delta->object)
	    free_object(delta->object, nprops);
	delta->object = NULL;
    } else
	new_delta(oid, NULL, nprops);
}

Objid
db_renumber_object(Objid old)
{
    Objid new;
    Object *o;

    db_priv_affected_callable_verb_lookup();
    db_checkpoint_barrier("renumbering an object");

    for (new = 0; new < old; new++) {
	if (objects[new] == 0) {
	    /* Change the identity of the object. */
	    o = objects[new] = objects[old];
	    objects[old] = 0;
	    objects[new]->id = new;

	    /* Fix up the parent/children hierarchy */
	    {
		Objid oid, *oidp;

		if (o->parent != NOTHING) {
		    oidp = &objects[o->parent]->child;
		    while (*oidp != old && *oidp != NOTHING)
			oidp = &objects[*oidp]->sibling;
		    if (*oidp == NOTHING)
			panic("Object not in parent's children list");
		    *oidp = new;
		}
		for (oid = o->child;
		     oid != NOTHING;
		     oid = objects[oid]->sibling)
		    objects[oid]->parent = new;
	    }

	    /* Fix up the location/contents hierarchy */
	    {
		Objid oid, *oidp;

		if (o->location != NOTHING) {
		    oidp = &objects[o->location]->contents;
		    while (*oidp != old && *oidp != NOTHING)
			oidp = &objects[*oidp]->next;
		    if (*oidp == NOTHING)
			panic("Object not in location's contents list");
		    *oidp = new;
		}
		for (oid = o->contents;
		     oid != NOTHING;
		     oid = objects[oid]->next)
		    objects[oid]->location = new;
	    }

	    /* Fix up the list of users, if necessary */
	    if (is_user(new)) {
		int i;

		for (i = 1; i <= all_users.v.list[0].v.num; i++)
		    if (all_users.v.list[i].v.obj == old) {
			all_users.v.list[i].v.obj = new;
			break;
		    }
	    }
	    /* Fix the owners of verbs, properties and objects */
	    {
		Objid oid;

		for (oid = 0; oid < num_objects; oid++) {
		    Object *o = objects[oid];
		    Verbdef *v;
		    Pval *p;
		    int i, count;

		    if (!o)
			continue;

		    if (o->owner == new)
			o->owner = NOTHING;
		    else if (o->owner == old)
			o->owner = new;

		    for (v = o->verbdefs; v; v = v->next)
			if (v->owner == new)
			    v->owner = NOTHING;
			else if (v->owner == old)
			    v->owner = new;

		    count = dbpriv_count_properties(oid);
		    p = o->propval;
		    for (i = 0; i < count; i++)
			if (p[i].owner == new)
			    p[i].owner = NOTHING;
			else if (p[i].owner == old)
			    p[i].owner = new;
		}
	    }

	    return new;
	}
    }

    /* There are no recycled objects less than `old', so keep its number. */
    return old;
}

int
db_object_bytes(Objid oid)
{
    Object *o = dbpriv_find_object(oid);
    int i, len, count;
    Verbdef *v;

    count = BQM_SIZEOF(Object) + BQM_SIZEOF_PTR_TO(Object);
    count += memo_strlen(o->name) + 1;

    for (v = o->verbdefs; v; v = v->next) {
	count += BQM_SIZEOF(Verbdef);
	count += memo_strlen(v->name) + 1;
	if (v->program)
	    count += program_bytes(v->program);
    }

    count += BQM_SIZEOF(Propdef) * o->propdefs.cur_length;
    for (i = 0; i < o->propdefs.cur_length; i++)
	count += memo_strlen(o->propdefs.l[i].name) + 1;

    len = dbpriv_count_properties(oid);
    count += (BQM_SIZEOF(Pval) - BQM_SIZEOF(Var)) * len;
    for (i = 0; i < len; i++)
	count += value_bytes(o->propval[i].var);

    return count;
}


/*********** Object attributes ***********/

Objid
db_object_owner(Objid oid)
{
    return dbpriv_find_object(oid)->owner;
}

void
db_set_object_owner(Objid oid, Objid owner)
{
    dbpriv_checkpoint_touch_object(oid)->owner = owner;
}

const char *
db_object_name(Objid oid)
{
    return dbpriv_find_object(oid)->name;
}

void
db_set_object_name(Objid oid, const char *name)
{
    Object *o = dbpriv_checkpoint_touch_object(oid);

    if (o->name)
	free_str(o->name);
    o->name = name;
}

Objid
db_object_parent(Objid oid)
{
    return dbpriv_find_object(oid)->parent;
}

int
db_count_children(Objid oid)
{
    Objid c;
    int i = 0;

    for (c = dbpriv_find_object(oid)->child; c != NOTHING;
	 c = dbpriv_find_object(c)->sibling)
	i++;

    return i;
}

int
db_for_all_children(Objid oid, int (*func) (void *, Objid), void *data)
{
    Objid c;

    for (c = dbpriv_find_object(oid)->child; c != NOTHING;
	 c = dbpriv_find_object(c)->sibling)
	if (func(data, c))
	    return 1;

    return 0;
}

#define LL_REMOVE(where, listname, what, nextname) { \
    Objid lid; \
    Object *where_o = dbpriv_checkpoint_touch_object(where); \
    Object *what_o = dbpriv_checkpoint_touch_object(what); \
    if (where_o->listname == what) \
	where_o->listname = what_o->nextname; \
    else { \
	for (lid = where_o->listname; lid != NOTHING; \
	      lid = dbpriv_find_object(lid)->nextname) { \
	    Object *lid_o = dbpriv_checkpoint_touch_object(lid); \
	    if (lid_o->nextname == what) { \
		lid_o->nextname = what_o->nextname; \
		break; \
	    } \
	} \
    } \
    what_o->nextname = NOTHING; \
}

#define LL_APPEND(where, listname, what, nextname) { \
    Objid lid; \
    Object *where_o = dbpriv_checkpoint_touch_object(where); \
    Object *what_o = dbpriv_checkpoint_touch_object(what); \
    if (where_o->listname == NOTHING) { \
	where_o->listname = what; \
    } else { \
	for (lid = where_o->listname; \
	     dbpriv_find_object(lid)->nextname != NOTHING; \
	     lid = dbpriv_find_object(lid)->nextname) \
	    ; \
	dbpriv_checkpoint_touch_object(lid)->nextname = what; \
    } \
    what_o->nextname = NOTHING; \
}

int
db_change_parent(Objid oid, Objid parent)
{
    Objid old_parent;

    if (!dbpriv_check_properties_for_chparent(oid, parent))
	return 0;

    db_checkpoint_barrier("changing an object's parent");

    if (dbpriv_find_object(oid)->child == NOTHING
	&& dbpriv_find_object(oid)->verbdefs == NULL) {
	/* Since this object has no children and no verbs, we know that it
	   can't have had any part in affecting verb lookup, since we use first
	   parent with verbs as a key in the verb lookup cache. */
	/* The "no kids" rule is necessary because potentially one of the kids
	   could have verbs on it--and that kid could have cache entries for
	   THIS object's parentage. */
	/* In any case, don't clear the cache. */
	;
    } else {
	db_priv_affected_callable_verb_lookup();
    }

    old_parent = dbpriv_find_object(oid)->parent;

    if (old_parent != NOTHING)
	LL_REMOVE(old_parent, child, oid, sibling);

    if (parent != NOTHING)
	LL_APPEND(parent, child, oid, sibling);

    dbpriv_checkpoint_touch_object(oid)->parent = parent;
    dbpriv_fix_properties_after_chparent(oid, old_parent);

    return 1;
}

Objid
db_object_location(Objid oid)
{
    return dbpriv_find_object(oid)->location;
}

int
db_count_contents(Objid oid)
{
    Objid c;
    int i = 0;

    for (c = dbpriv_find_object(oid)->contents; c != NOTHING;
	 c = dbpriv_find_object(c)->next)
	i++;

    return i;
}

int
db_for_all_contents(Objid oid, int (*func) (void *, Objid), void *data)
{
    Objid c;

    for (c = dbpriv_find_object(oid)->contents; c != NOTHING;
	 c = dbpriv_find_object(c)->next)
	if (func(data, c))
	    return 1;

    return 0;
}

void
db_change_location(Objid oid, Objid location)
{
    Objid old_location = dbpriv_find_object(oid)->location;

    if (valid(old_location))
	LL_REMOVE(old_location, contents, oid, next);

    if (valid(location))
	LL_APPEND(location, contents, oid, next);

    dbpriv_checkpoint_touch_object(oid)->location = location;
}

int
db_object_has_flag(Objid oid, db_object_flag f)
{
    return (dbpriv_find_object(oid)->flags & (1 << f)) != 0;
}

void
db_set_object_flag(Objid oid, db_object_flag f)
{
    dbpriv_checkpoint_touch_object(oid)->flags |= (1 << f);
    if (f == FLAG_USER) {
	Var v;

	v.type = TYPE_OBJ;
	v.v.obj = oid;
	all_users = setadd(all_users, v);
    }
}

void
db_clear_object_flag(Objid oid, db_object_flag f)
{
    dbpriv_checkpoint_touch_object(oid)->flags &= ~(1 << f);
    if (f == FLAG_USER) {
	Var v;

	v.type = TYPE_OBJ;
	v.v.obj = oid;
	all_users = setremove(all_users, v);
    }
}

int
db_object_allows(Objid oid, Objid progr, db_object_flag f)
{
    return (progr == db_object_owner(oid)
	    || is_wizard(progr)
	    || db_object_has_flag(oid, f));
}

int
is_wizard(Objid oid)
{
    return valid(oid) && db_object_has_flag(oid, FLAG_WIZARD);
}

int
is_programmer(Objid oid)
{
    return valid(oid) && db_object_has_flag(oid, FLAG_PROGRAMMER);
}

int
is_user(Objid oid)
{
    return valid(oid) && db_object_has_flag(oid, FLAG_USER);
}

Var
db_all_users(void)
{
    return all_users;
}

void
dbpriv_set_all_users(Var v)
{
    all_users = v;
}


/*
 * $Log$
 * Revision 2.5  1996/04/08  00:42:11  pavel
 * Adjusted computation in `db_object_bytes()' to account for change in the
 * definition of `value_bytes()'.  Release 1.8.0p3.
 *
 * Revision 2.4  1996/02/08  07:18:13  pavel
 * Updated copyright notice for 1996.  Release 1.8.0beta1.
 *
 * Revision 2.3  1996/01/16  07:23:45  pavel
 * Fixed object-array overrun when a recycled object is right on the boundary.
 * Release 1.8.0alpha6.
 *
 * Revision 2.2  1996/01/11  07:30:53  pavel
 * Fixed memory-smash bug in db_renumber_object().  Release 1.8.0alpha5.
 *
 * Revision 2.1  1995/12/11  08:08:28  pavel
 * Added `db_object_bytes()'.  Release 1.8.0alpha2.
 *
 * Revision 2.0  1995/11/30  04:20:51  pavel
 * New baseline version, corresponding to release 1.8.0alpha1.
 *
 * Revision 1.1  1995/11/30  04:20:41  pavel
 * Initial revision
 */
