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
 * Routines for manipulating properties on DB objects
 *****************************************************************************/

#include "db.h"
#include "db_private.h"

#include "list.h"
#include "storage.h"
#include "utils.h"
#include "waif.h"

#ifdef PROPERTY_CACHE
typedef struct {
    uint64_t id;
    const char *name;
    int hash;
    Objid definer;
} PropertyDescriptor;

struct PropertyLayout {
    unsigned refs;
    int count;
    int table_size;
    PropertyDescriptor *descriptors;
    int *name_index;
    int *id_index;
};

/* Property IDs exist only in memory.  Layouts use parent-first slots so that
 * inherited properties retain their slot in every derived layout. */
static uint64_t next_property_id = 1;

static struct PropertyLayout *
ref_layout(struct PropertyLayout *layout)
{
    if (layout)
	layout->refs++;
    return layout;
}

static void
free_layout(struct PropertyLayout *layout)
{
    int i;

    if (!layout || --layout->refs != 0)
	return;
    for (i = 0; i < layout->count; i++)
	free_str(layout->descriptors[i].name);
    myfree(layout->descriptors, M_PROPERTY_LAYOUT);
    myfree(layout->name_index, M_PROPERTY_LAYOUT);
    myfree(layout->id_index, M_PROPERTY_LAYOUT);
    myfree(layout, M_PROPERTY_LAYOUT);
}

void
dbpriv_ref_property_layout(Object *o)
{
    ref_layout(o->prop_layout);
}

void
dbpriv_renumber_property_layouts(Object *o, Objid old, Objid new)
{
    struct PropertyLayout *layout = o->prop_layout;
    Objid child;
    int i;

    if (layout)
	for (i = 0; i < layout->count; i++)
	    if (layout->descriptors[i].definer == old)
		layout->descriptors[i].definer = new;
    for (child = o->child; child != NOTHING;
	 child = dbpriv_find_object(child)->sibling)
	dbpriv_renumber_property_layouts(dbpriv_find_object(child), old, new);
}

void
dbpriv_release_property_layout(Object *o)
{
    free_layout(o->prop_layout);
    o->prop_layout = NULL;
}

static int
layout_slot_for_id(const struct PropertyLayout *layout, uint64_t id)
{
    int bucket, slot;

    if (!layout)
	return -1;
    bucket = (unsigned) id & (layout->table_size - 1);
    while ((slot = layout->id_index[bucket]) != -1) {
	if (layout->descriptors[slot].id == id)
	    return slot;
	bucket = (bucket + 1) & (layout->table_size - 1);
    }
    return -1;
}

static int
layout_slot_for_name(const struct PropertyLayout *layout, const char *name,
		    int hash)
{
    int bucket, slot;

    if (!layout)
	return -1;
    bucket = (unsigned) hash & (layout->table_size - 1);
    while ((slot = layout->name_index[bucket]) != -1) {
	PropertyDescriptor *d = &layout->descriptors[slot];

	if (d->hash == hash
	    && (d->name == name || !mystrcasecmp(d->name, name)))
	    return slot;
	bucket = (bucket + 1) & (layout->table_size - 1);
    }
    return -1;
}

static void
rebuild_name_index(struct PropertyLayout *layout)
{
    int i;

    for (i = 0; i < layout->table_size; i++)
	layout->name_index[i] = -1;
    for (i = 0; i < layout->count; i++) {
	int bucket = (unsigned) layout->descriptors[i].hash
	    & (layout->table_size - 1);

	while (layout->name_index[bucket] != -1)
	    bucket = (bucket + 1) & (layout->table_size - 1);
	layout->name_index[bucket] = i;
    }
}

static void
rebuild_id_index(struct PropertyLayout *layout)
{
    int i;

    for (i = 0; i < layout->table_size; i++)
	layout->id_index[i] = -1;
    for (i = 0; i < layout->count; i++) {
	int bucket = (unsigned) layout->descriptors[i].id
	    & (layout->table_size - 1);

	while (layout->id_index[bucket] != -1)
	    bucket = (bucket + 1) & (layout->table_size - 1);
	layout->id_index[bucket] = i;
    }
}

static struct PropertyLayout *
make_layout(Object *owner, struct PropertyLayout *parent)
{
    struct PropertyLayout *layout;
    int inherited = parent ? parent->count : 0;
    int count = inherited + owner->propdefs.cur_length;
    int i;

    if (owner->propdefs.cur_length == 0)
	return ref_layout(parent);
    if (count == 0)
	return NULL;

    layout = mymalloc(sizeof(*layout), M_PROPERTY_LAYOUT);
    layout->refs = 1;
    layout->count = count;
    layout->descriptors = mymalloc(count * sizeof(PropertyDescriptor),
				  M_PROPERTY_LAYOUT);
    for (i = 0; i < inherited; i++) {
	layout->descriptors[i] = parent->descriptors[i];
	layout->descriptors[i].name = str_ref(parent->descriptors[i].name);
    }
    for (i = 0; i < owner->propdefs.cur_length; i++) {
	Propdef *p = &owner->propdefs.l[i];
	PropertyDescriptor *d = &layout->descriptors[inherited + i];

	d->id = p->id;
	d->name = str_ref(p->name);
	d->hash = p->hash;
	d->definer = owner->id;
    }

    for (layout->table_size = 8; layout->table_size < count * 2;
	 layout->table_size *= 2)
	;
    layout->name_index = mymalloc(layout->table_size * sizeof(int),
				  M_PROPERTY_LAYOUT);
    layout->id_index = mymalloc(layout->table_size * sizeof(int),
				M_PROPERTY_LAYOUT);
    rebuild_name_index(layout);
    rebuild_id_index(layout);
    return layout;
}
#endif /* PROPERTY_CACHE */

Propdef
dbpriv_new_propdef(const char *name)
{
    Propdef newprop;

    newprop.name = str_ref(name);
    newprop.hash = str_hash(name);
#ifdef PROPERTY_CACHE
    newprop.id = next_property_id++;
#endif
    return newprop;
}

int
dbpriv_count_properties(Objid oid)
{
    Object *o;
    int nprops = 0;

    o = dbpriv_find_object(oid);
#ifdef PROPERTY_CACHE
    if (o && o->prop_layout)
	return o->prop_layout->count;
#endif
    for (; o; o = dbpriv_find_object(o->parent))
	nprops += o->propdefs.cur_length;

    return nprops;
}

#ifdef PROPERTY_CACHE
Pval *
dbpriv_property_value_for_definition(Object *o, uint64_t id)
{
    int slot = layout_slot_for_id(o->prop_layout, id);

    if (slot < 0)
	panic("Property definition missing from object layout");
    return &o->propval[slot];
}

static int
legacy_property_position(Object *o, uint64_t id)
{
    int position = 0;

    for (; o; o = dbpriv_find_object(o->parent)) {
	int i;

	for (i = 0; i < o->propdefs.cur_length; i++, position++)
	    if (o->propdefs.l[i].id == id)
		return position;
    }
    return -1;
}

static void
build_loaded_layouts(Object *o, struct PropertyLayout *parent)
{
    Pval *old_values = o->propval;
    int count, i;
    Objid child;

    /* Database files store values local-first; live layouts are parent-first. */
    o->prop_layout = make_layout(o, parent);
    count = o->prop_layout ? o->prop_layout->count : 0;
    if (count) {
	Pval *new_values = mymalloc(count * sizeof(Pval), M_PVAL);

	for (i = 0; i < count; i++) {
	    int old_slot = legacy_property_position(
		o, o->prop_layout->descriptors[i].id);

	    if (old_slot < 0)
		panic("Invalid property layout while loading database");
	    new_values[i] = old_values[old_slot];
	}
	o->propval = new_values;
	myfree(old_values, M_PVAL);
    }
    for (child = o->child; child != NOTHING;
	 child = dbpriv_find_object(child)->sibling)
	build_loaded_layouts(dbpriv_find_object(child), o->prop_layout);
}

void
dbpriv_build_property_layouts(void)
{
    Objid oid;

    for (oid = 0; oid <= db_last_used_objid(); oid++) {
	Object *o = dbpriv_find_object(oid);

	if (o && o->parent == NOTHING)
	    build_loaded_layouts(o, NULL);
    }
}
#endif /* PROPERTY_CACHE */

int
dbpriv_count_frozen_properties(Objid oid)
{
    Object *o;
    int nprops = 0;

    for (o = dbpriv_find_frozen_object(oid); o;
	 o = dbpriv_find_frozen_object(o->parent))
	nprops += o->propdefs.cur_length;
    return nprops;
}

static int
property_defined_at_or_below(const char *pname, int phash, Objid oid)
{
    /* Return true iff some descendant of OID defines a property named PNAME.
     */
    Objid c;
    Proplist *props = &dbpriv_find_object(oid)->propdefs;
    int length = props->cur_length;
    int i;

    for (i = 0; i < length; i++)
	if (props->l[i].hash == phash
	    && (props->l[i].name == pname
		|| !mystrcasecmp(props->l[i].name, pname)))
	    return 1;

    for (c = dbpriv_find_object(oid)->child;
	 c != NOTHING;
	 c = dbpriv_find_object(c)->sibling)
	if (property_defined_at_or_below(pname, phash, c))
	    return 1;

    return 0;
}

#ifdef PROPERTY_CACHE
static void
invalidate_property_waifs(Object *o)
{
#ifdef WAIF_CORE
    free_waif_propdefs(o->waif_propdefs);
    o->waif_propdefs = NULL;
#else
    (void) o;
#endif
}

static void
install_property_layout(Object *o, struct PropertyLayout *layout, Pval *values)
{
    struct PropertyLayout *old_layout = o->prop_layout;
    Pval *old_values = o->propval;

    o->prop_layout = layout;
    o->propval = values;
    if (old_values)
	myfree(old_values, M_PVAL);
    free_layout(old_layout);
    invalidate_property_waifs(o);
}

static void
rename_property_in_layouts(Object *o,
			   struct PropertyLayout *shared_parent_layout,
			   uint64_t id, const char *name, int hash)
{
    struct PropertyLayout *layout = o->prop_layout;
    Objid child;

    /* A child with no local definitions shares its parent's layout.  Update
     * each distinct layout just once, in place; renaming cannot move slots. */
    if (layout != shared_parent_layout) {
	int slot = layout_slot_for_id(layout, id);

	if (slot < 0)
	    panic("Renamed property is not present in descendant layout");
	free_str(layout->descriptors[slot].name);
	layout->descriptors[slot].name = str_ref(name);
	layout->descriptors[slot].hash = hash;
	rebuild_name_index(layout);
    }

    for (child = o->child; child != NOTHING;
	 child = dbpriv_find_object(child)->sibling)
	rename_property_in_layouts(dbpriv_find_object(child), layout, id,
				   name, hash);
}

static void
insert_property_slot(Object *o, uint64_t added_id, Object *added_definer,
		     const Pval *added_value)
{
    struct PropertyLayout *old_layout = o->prop_layout;
    struct PropertyLayout *parent_layout = NULL;
    Pval *old_values = o->propval;
    struct PropertyLayout *new_layout;
    Pval *new_values;
    int old_count = old_layout ? old_layout->count : 0;
    int new_count, added_slot, i;
    Objid child;

    if (o->parent != NOTHING)
	parent_layout = dbpriv_find_object(o->parent)->prop_layout;
    new_layout = make_layout(o, parent_layout);
    new_count = new_layout ? new_layout->count : 0;
    added_slot = layout_slot_for_id(new_layout, added_id);
    if (new_count != old_count + 1 || added_slot < 0)
	panic("Invalid property layout while adding property");

    new_values = mymalloc(new_count * sizeof(Pval), M_PVAL);
    for (i = 0; i < added_slot; i++)
	new_values[i] = old_values[i];
    for (i = added_slot + 1; i < new_count; i++)
	new_values[i] = old_values[i - 1];

    if (o == added_definer) {
	new_values[added_slot] = *added_value;
	new_values[added_slot].var = var_ref(added_value->var);
	if (new_values[added_slot].perms & PF_CHOWN)
	    new_values[added_slot].owner = o->owner;
    } else {
	Object *parent = dbpriv_find_object(o->parent);
	int parent_slot = layout_slot_for_id(parent->prop_layout, added_id);

	if (parent_slot < 0)
	    panic("New property is not present in parent layout");
	new_values[added_slot] = parent->propval[parent_slot];
	new_values[added_slot].var.type = TYPE_CLEAR;
	if (new_values[added_slot].perms & PF_CHOWN)
	    new_values[added_slot].owner = o->owner;
    }

    install_property_layout(o, new_layout, new_values);

    for (child = o->child; child != NOTHING;
	 child = dbpriv_find_object(child)->sibling)
	insert_property_slot(dbpriv_find_object(child), added_id,
			     added_definer, added_value);
}

static void
remove_property_slot(Object *o, uint64_t deleted_id)
{
    struct PropertyLayout *old_layout = o->prop_layout;
    struct PropertyLayout *parent_layout = NULL;
    Pval *old_values = o->propval;
    struct PropertyLayout *new_layout;
    Pval *new_values;
    int old_count = old_layout ? old_layout->count : 0;
    int new_count, deleted_slot, i;
    Objid child;

    deleted_slot = layout_slot_for_id(old_layout, deleted_id);
    if (deleted_slot < 0)
	panic("Deleted property is not present in old layout");
    if (o->parent != NOTHING)
	parent_layout = dbpriv_find_object(o->parent)->prop_layout;
    new_layout = make_layout(o, parent_layout);
    new_count = new_layout ? new_layout->count : 0;
    if (new_count != old_count - 1)
	panic("Invalid property layout while deleting property");

    new_values = new_count ? mymalloc(new_count * sizeof(Pval), M_PVAL) : NULL;
    for (i = 0; i < deleted_slot; i++)
	new_values[i] = old_values[i];
    for (i = deleted_slot; i < new_count; i++)
	new_values[i] = old_values[i + 1];
    free_var(old_values[deleted_slot].var);
    install_property_layout(o, new_layout, new_values);

    for (child = o->child; child != NOTHING;
	 child = dbpriv_find_object(child)->sibling)
	remove_property_slot(dbpriv_find_object(child), deleted_id);
}

static void
remap_reparented_subtree(Object *o)
{
    struct PropertyLayout *old_layout = o->prop_layout;
    struct PropertyLayout *parent_layout = NULL;
    Pval *old_values = o->propval;
    struct PropertyLayout *new_layout;
    Pval *new_values;
    int old_count = old_layout ? old_layout->count : 0;
    int new_count, i;
    Objid child;

    if (o->parent != NOTHING)
	parent_layout = dbpriv_find_object(o->parent)->prop_layout;
    new_layout = make_layout(o, parent_layout);
    new_count = new_layout ? new_layout->count : 0;
    new_values = new_count ? mymalloc(new_count * sizeof(Pval), M_PVAL) : NULL;

    for (i = 0; i < new_count; i++) {
	PropertyDescriptor *d = &new_layout->descriptors[i];
	int old_slot = layout_slot_for_id(old_layout, d->id);

	if (old_slot >= 0)
	    new_values[i] = old_values[old_slot];
	else if (o->parent != NOTHING) {
	    Object *parent = dbpriv_find_object(o->parent);
	    int parent_slot = layout_slot_for_id(parent->prop_layout, d->id);

	    if (parent_slot < 0)
		panic("New property is not present in parent layout");
	    new_values[i] = parent->propval[parent_slot];
	    new_values[i].var.type = TYPE_CLEAR;
	    if (new_values[i].perms & PF_CHOWN)
		new_values[i].owner = o->owner;
	} else
	    panic("New local property has no initial value");
    }

    for (i = 0; i < old_count; i++)
	if (layout_slot_for_id(new_layout,
			      old_layout->descriptors[i].id) < 0)
	    free_var(old_values[i].var);
    install_property_layout(o, new_layout, new_values);

    for (child = o->child; child != NOTHING;
	 child = dbpriv_find_object(child)->sibling)
	remap_reparented_subtree(dbpriv_find_object(child));
}
#else
static void
insert_prop(Objid oid, int pos, Pval pval)
{
    Pval *new_propval;
    Object *o;
    int i, nprops;

    nprops = dbpriv_count_properties(oid);
    new_propval = mymalloc(nprops * sizeof(Pval), M_PVAL);

    o = dbpriv_find_object(oid);

#ifdef WAIF_CORE
    free_waif_propdefs(o->waif_propdefs);
    o->waif_propdefs = NULL;
#endif

    for (i = 0; i < pos; i++)
	new_propval[i] = o->propval[i];

    new_propval[pos] = pval;
    new_propval[pos].var = var_ref(pval.var);
    if (new_propval[pos].perms & PF_CHOWN)
	new_propval[pos].owner = o->owner;

    for (i = pos + 1; i < nprops; i++)
	new_propval[i] = o->propval[i - 1];

    if (o->propval)
	myfree(o->propval, M_PVAL);
    o->propval = new_propval;
}

static void
insert_prop_recursively(Objid root, int root_pos, Pval pv)
{
    Objid c;

    insert_prop(root, root_pos, pv);
    pv.var.type = TYPE_CLEAR;	/* do after initial insert_prop so only
				   children will be TYPE_CLEAR */
    for (c = dbpriv_find_object(root)->child;
	 c != NOTHING;
	 c = dbpriv_find_object(c)->sibling) {
	int new_prop_count = dbpriv_find_object(c)->propdefs.cur_length;

	insert_prop_recursively(c, new_prop_count + root_pos, pv);
    }
}
#endif /* PROPERTY_CACHE */

int
db_add_propdef(Objid oid, const char *pname, Var value, Objid owner,
	       unsigned flags)
{
    Object *o;
    Pval pval;
    int i;
    db_prop_handle h;

    h = db_find_property(oid, pname, 0);

    if (h.ptr || property_defined_at_or_below(pname, str_hash(pname), oid))
	return 0;

    db_checkpoint_barrier("adding a property");

    o = dbpriv_find_object(oid);
    if (o->propdefs.cur_length == o->propdefs.max_length) {
	Propdef *old_props = o->propdefs.l;
	int new_size = (o->propdefs.max_length == 0
			? 8 : 2 * o->propdefs.max_length);

	o->propdefs.l = mymalloc(new_size * sizeof(Propdef), M_PROPDEF);
	for (i = 0; i < o->propdefs.max_length; i++)
	    o->propdefs.l[i] = old_props[i];
	o->propdefs.max_length = new_size;

	if (old_props)
	    myfree(old_props, M_PROPDEF);
    }
    o->propdefs.l[o->propdefs.cur_length++] = dbpriv_new_propdef(pname);

    pval.var = value;
    pval.owner = owner;
    pval.perms = flags;

#ifdef PROPERTY_CACHE
    insert_property_slot(o,
			 o->propdefs.l[o->propdefs.cur_length - 1].id,
			 o, &pval);
#else
    insert_prop_recursively(oid, o->propdefs.cur_length - 1, pval);
#endif

    return 1;
}

#ifdef WAIF_CORE

static void
rename_prop_recursively(Objid root, const char *old, const char *new)
{
    Objid c;
    Object *o = dbpriv_find_object(root);

    if (o->waif_propdefs)
	waif_rename_propdef(o, old, new);
    for (c = o->child; c != NOTHING; c = dbpriv_find_object(c)->sibling)
	rename_prop_recursively(c, old, new);
}

#endif  /* WAIF_CORE */

int
db_rename_propdef(Objid oid, const char *old, const char *new)
{
    Proplist *props = &dbpriv_find_object(oid)->propdefs;
    int hash = str_hash(old);
    int count = props->cur_length;
    int i;
    db_prop_handle h;

    for (i = 0; i < count; i++) {
	Propdef p;

	p = props->l[i];
	if (p.hash == hash
	    && (p.name == old || !mystrcasecmp(p.name, old))) {
	    if (mystrcasecmp(old, new) != 0) {	/* Not changing just the case */
		h = db_find_property(oid, new, 0);
		if (h.ptr
		|| property_defined_at_or_below(new, str_hash(new), oid))
		    return 0;
	    }
	    db_checkpoint_barrier("renaming a property");
	    props = &dbpriv_find_object(oid)->propdefs;
#ifdef WAIF_CORE
	    rename_prop_recursively(oid, props->l[i].name, new);
#endif
	    free_str(props->l[i].name);
	    props->l[i].name = str_ref(new);
	    props->l[i].hash = str_hash(new);
#ifdef PROPERTY_CACHE
	    rename_property_in_layouts(dbpriv_find_object(oid), NULL, p.id,
				       props->l[i].name, props->l[i].hash);
#endif

	    return 1;
	}
    }

    return 0;
}

#ifndef PROPERTY_CACHE
static void
remove_prop(Objid oid, int pos)
{
    Pval *new_propval;
    Object *o;
    int i, nprops;

    o = dbpriv_find_object(oid);
    nprops = dbpriv_count_properties(oid);

#ifdef WAIF_CORE
    free_waif_propdefs(o->waif_propdefs);
    o->waif_propdefs = NULL;
#endif

    free_var(o->propval[pos].var);	/* free deleted property */

    if (nprops) {
	new_propval = mymalloc(nprops * sizeof(Pval), M_PVAL);
	for (i = 0; i < pos; i++)
	    new_propval[i] = o->propval[i];
	for (i = pos; i < nprops; i++)
	    new_propval[i] = o->propval[i + 1];
    } else
	new_propval = 0;

    if (o->propval)
	myfree(o->propval, M_PVAL);
    o->propval = new_propval;
}

static void
remove_prop_recursively(Objid root, int root_pos)
{
    Objid c;

    remove_prop(root, root_pos);
    for (c = dbpriv_find_object(root)->child;
	 c != NOTHING;
	 c = dbpriv_find_object(c)->sibling) {
	int new_prop_count = dbpriv_find_object(c)->propdefs.cur_length;

	remove_prop_recursively(c, new_prop_count + root_pos);
    }
}
#endif /* !PROPERTY_CACHE */

int
db_delete_propdef(Objid oid, const char *pname)
{
    Proplist *props = &dbpriv_find_object(oid)->propdefs;
    int hash = str_hash(pname);
    int count = props->cur_length;
    int max = props->max_length;
    int i, j;

    for (i = 0; i < count; i++) {
	Propdef p;

	p = props->l[i];
	if (p.hash == hash
	    && (p.name == pname || !mystrcasecmp(p.name, pname))) {
	    db_checkpoint_barrier("deleting a property");
	    props = &dbpriv_find_object(oid)->propdefs;
	    count = props->cur_length;
	    max = props->max_length;
	    if (p.name)
		free_str(p.name);

	    if (max > 8 && props->cur_length <= ((max * 3) / 8)) {
		int new_size = max / 2;
		Propdef *new_props;

		new_props = mymalloc(new_size * sizeof(Propdef), M_PROPDEF);

		for (j = 0; j < i; j++)
		    new_props[j] = props->l[j];
		for (j = i + 1; j < count; j++)
		    new_props[j - 1] = props->l[j];

		myfree(props->l, M_PROPDEF);
		props->l = new_props;
		props->max_length = new_size;
	    } else
		for (j = i + 1; j < count; j++)
		    props->l[j - 1] = props->l[j];

	    props->cur_length--;
#ifdef PROPERTY_CACHE
	    remove_property_slot(dbpriv_find_object(oid), p.id);
#else
	    remove_prop_recursively(oid, i);
#endif

	    return 1;
	}
    }

    return 0;
}

int
db_count_propdefs(Objid oid)
{
    return dbpriv_find_object(oid)->propdefs.cur_length;
}

int
db_for_all_propdefs(Objid oid, int (*func) (void *, const char *), void *data)
{
    int i;
    Object *o = dbpriv_find_object(oid);
    int len = o->propdefs.cur_length;

    for (i = 0; i < len; i++)
	if (func(data, o->propdefs.l[i].name))
	    return 1;

    return 0;
}

struct contents_data {
    Var r;
    int i;
};

static int
add_to_list(void *data, Objid c)
{
    struct contents_data *d = data;

    d->i++;
    d->r.v.list[d->i].type = TYPE_OBJ;
    d->r.v.list[d->i].v.obj = c;

    return 0;
}

static void
get_bi_value(db_prop_handle h, Var * value)
{
    Objid oid = *((Objid *) h.ptr);

    switch (h.built_in) {
    case BP_NAME:
	value->type = TYPE_STR;
	value->v.str = str_ref(db_object_name(oid));
	break;
    case BP_OWNER:
	value->type = TYPE_OBJ;
	value->v.obj = db_object_owner(oid);
	break;
    case BP_PROGRAMMER:
	value->type = TYPE_INT;
	value->v.num = db_object_has_flag(oid, FLAG_PROGRAMMER);
	break;
    case BP_WIZARD:
	value->type = TYPE_INT;
	value->v.num = db_object_has_flag(oid, FLAG_WIZARD);
	break;
    case BP_R:
	value->type = TYPE_INT;
	value->v.num = db_object_has_flag(oid, FLAG_READ);
	break;
    case BP_W:
	value->type = TYPE_INT;
	value->v.num = db_object_has_flag(oid, FLAG_WRITE);
	break;
    case BP_F:
	value->type = TYPE_INT;
	value->v.num = db_object_has_flag(oid, FLAG_FERTILE);
	break;
    case BP_LOCATION:
	value->type = TYPE_OBJ;
	value->v.obj = db_object_location(oid);
	break;
    case BP_CONTENTS:
	{
	    struct contents_data d;

	    d.r = new_list(db_count_contents(oid));
	    d.i = 0;
	    db_for_all_contents(oid, add_to_list, &d);

	    *value = d.r;
	}
	break;
    default:
	panic("Unknown built-in property in GET_BI_VALUE!");
    }
}

db_prop_handle
db_find_property(Objid oid, const char *name, Var * value)
{
    static struct {
	const char *name;
	enum bi_prop prop;
	int hash;
    } ptable[] = {
#define _ENTRY(P,p) { #p, BP_##P, 0 },
      BUILTIN_PROPERTIES(_ENTRY)
#undef _ENTRY
    };
    static int ptable_init = 0;
    int i;
#ifndef PROPERTY_CACHE
    int n;
#endif
    db_prop_handle h;
    int hash = str_hash(name);
    Object *o;

    if (!ptable_init) {
        for (i = 0; i < (int)Arraysize(ptable); i++)
	    ptable[i].hash = str_hash(ptable[i].name);
	ptable_init = 1;
    }
    h.definer = NOTHING;
    h.oid = oid;
    h.index = -1;
    for (i = 0; i < (int)Arraysize(ptable); i++) {
	if (ptable[i].hash == hash
	    && (name == ptable[i].name
		|| !mystrcasecmp(name, ptable[i].name))) {
	    static Objid ret;

	    ret = oid;
	    h.built_in = ptable[i].prop;
	    h.ptr = &ret;
	    if (value)
		get_bi_value(h, value);
	    return h;
	}
    }

    h.built_in = BP_NONE;
#ifdef PROPERTY_CACHE
    o = dbpriv_find_object(oid);
    i = layout_slot_for_name(o->prop_layout, name, hash);
    if (i >= 0) {
	PropertyDescriptor *d = &o->prop_layout->descriptors[i];
	Pval *prop = &o->propval[i];

	h.definer = d->definer;
	h.ptr = prop;
	h.index = i;
	if (value) {
	    while (prop->var.type == TYPE_CLEAR) {
		o = dbpriv_find_object(o->parent);
		if (!o || !o->prop_layout || i >= o->prop_layout->count
		    || o->prop_layout->descriptors[i].id != d->id)
		    panic("Broken inherited property layout");
		prop = &o->propval[i];
	    }
	    *value = prop->var;
	}
	return h;
    }
#else
    n = 0;
    for (o = dbpriv_find_object(oid); o; o = dbpriv_find_object(o->parent)) {
	Proplist *props = &(o->propdefs);
	Propdef *defs = props->l;
	int length = props->cur_length;

	for (i = 0; i < length; i++, n++) {
	    if (defs[i].hash == hash
		&& (defs[i].name == name
		    || !mystrcasecmp(defs[i].name, name))) {
		Pval *prop;

		h.definer = o->id;
		o = dbpriv_find_object(oid);
		prop = h.ptr = o->propval + n;
		h.index = n;

		if (value) {
		    while (prop->var.type == TYPE_CLEAR) {
			n -= o->propdefs.cur_length;
			o = dbpriv_find_object(o->parent);
			prop = o->propval + n;
		    }
		    *value = prop->var;
		}
		return h;
	    }
	}
    }
#endif /* PROPERTY_CACHE */

    h.ptr = 0;
    return h;
}

Var
db_property_value(db_prop_handle h)
{
    Var value;

    if (h.built_in)
	get_bi_value(h, &value);
    else {
	Pval *prop = h.ptr;

	value = prop->var;
    }

    return value;
}

void
db_set_property_value(db_prop_handle h, Var value)
{
    if (!h.built_in) {
	Pval *prop;

	if (h.index < 0)
	    panic("DB_SET_PROPERTY_VALUE: Invalid property handle!");
	prop = dbpriv_checkpoint_touch_object(h.oid)->propval + h.index;

	free_var(prop->var);
	prop->var = value;
    } else {
	Objid oid = *((Objid *) h.ptr);
	db_object_flag flag;

	switch (h.built_in) {
	case BP_NAME:
	    if (value.type != TYPE_STR)
		goto complain;
	    db_set_object_name(oid, value.v.str);
	    break;
	case BP_OWNER:
	    if (value.type != TYPE_OBJ)
		goto complain;
	    db_set_object_owner(oid, value.v.obj);
	    break;
	case BP_PROGRAMMER:
	    flag = FLAG_PROGRAMMER;
	    goto finish_flag;
	case BP_WIZARD:
	    flag = FLAG_WIZARD;
	    goto finish_flag;
	case BP_R:
	    flag = FLAG_READ;
	    goto finish_flag;
	case BP_W:
	    flag = FLAG_WRITE;
	    goto finish_flag;
	case BP_F:
	    flag = FLAG_FERTILE;
	  finish_flag:
	    if (is_true(value))
		db_set_object_flag(oid, flag);
	    else
		db_clear_object_flag(oid, flag);
	    free_var(value);
	    break;
	case BP_LOCATION:
	case BP_CONTENTS:
	  complain:
	    panic("Inappropriate value in DB_SET_PROPERTY_VALUE!");
	default:
	    panic("Unknown built-in property in DB_SET_PROPERTY_VALUE!");
	}
    }
}

Objid
db_property_owner(db_prop_handle h)
{
    if (h.built_in) {
	panic("Built-in property in DB_PROPERTY_OWNER!");
    } else {
	Pval *prop = h.ptr;

	return prop->owner;
    }
}

void
db_set_property_owner(db_prop_handle h, Objid oid)
{
    if (h.built_in)
	panic("Built-in property in DB_SET_PROPERTY_OWNER!");
    else {
	Pval *prop;

	if (h.index < 0)
	    panic("DB_SET_PROPERTY_OWNER: Invalid property handle!");
	prop = dbpriv_checkpoint_touch_object(h.oid)->propval + h.index;

	prop->owner = oid;
    }
}

unsigned
db_property_flags(db_prop_handle h)
{
    if (h.built_in) {
	panic("Built-in property in DB_PROPERTY_FLAGS!");
    } else {
	Pval *prop = h.ptr;

	return prop->perms;
    }
}

void
db_set_property_flags(db_prop_handle h, unsigned flags)
{
    if (h.built_in)
	panic("Built-in property in DB_SET_PROPERTY_FLAGS!");
    else {
	Pval *prop;

	if (h.index < 0)
	    panic("DB_SET_PROPERTY_FLAGS: Invalid property handle!");
	prop = dbpriv_checkpoint_touch_object(h.oid)->propval + h.index;

	prop->perms = flags;
    }
}

int
db_property_allows(db_prop_handle h, Objid progr, db_prop_flag flag)
{
    return ((db_property_flags(h) & flag)
	    || progr == db_property_owner(h)
	    || is_wizard(progr));
}

#ifndef PROPERTY_CACHE
static void
fix_props(Objid oid, int parent_local, int old, int new, int common)
{
    Object *me = dbpriv_find_object(oid);
    Object *parent = dbpriv_find_object(me->parent);
    Pval *new_propval;
    int local = parent_local;
    int i;
    Objid c;

#ifdef WAIF_CORE
    /* This will invalidate waif_propdefs */
    free_waif_propdefs(me->waif_propdefs);
    me->waif_propdefs = NULL;
#endif

    local += me->propdefs.cur_length;

    for (i = local; i < local + old; i++)
	free_var(me->propval[i].var);

    if (local + new + common != 0) {
	new_propval = mymalloc((local + new + common) * sizeof(Pval), M_PVAL);
	for (i = 0; i < local; i++)
	    new_propval[i] = me->propval[i];
	for (i = 0; i < new; i++) {
	    Pval pv;

	    pv = parent->propval[parent_local + i];
	    new_propval[local + i] = pv;
	    new_propval[local + i].var.type = TYPE_CLEAR;
	    if (pv.perms & PF_CHOWN)
		new_propval[local + i].owner = me->owner;
	}
	for (i = 0; i < common; i++)
	    new_propval[local + new + i] = me->propval[local + old + i];
    } else
	new_propval = 0;

    if (me->propval)
	myfree(me->propval, M_PVAL);
    me->propval = new_propval;

    for (c = me->child; c != NOTHING; c = dbpriv_find_object(c)->sibling)
	fix_props(c, local, old, new, common);
}
#endif /* !PROPERTY_CACHE */

int
dbpriv_check_properties_for_chparent(Objid oid, Objid new_parent)
{
    Object *o;
    int i;

    for (o = dbpriv_find_object(new_parent);
	 o;
	 o = dbpriv_find_object(o->parent)) {
	Proplist *props = &o->propdefs;

	for (i = 0; i < props->cur_length; i++)
	    if (property_defined_at_or_below(props->l[i].name,
					     props->l[i].hash,
					     oid))
		return 0;
    }

    return 1;
}

void
dbpriv_fix_properties_after_chparent(Objid oid, Objid old_parent)
{
#ifdef PROPERTY_CACHE
    (void) old_parent;
    remap_reparented_subtree(dbpriv_find_object(oid));
#else
    Objid o1, o2, common, new_parent;
    int common_props, old_props, new_props;

    /* Find the nearest common ancestor between old & new parent */
    new_parent = db_object_parent(oid);
    common = NOTHING;
    for (o1 = new_parent; o1 != NOTHING; o1 = db_object_parent(o1))
	for (o2 = old_parent; o2 != NOTHING; o2 = db_object_parent(o2))
	    if (o1 == o2) {
		common = o1;
		goto endouter;
	    }
  endouter:

    if (common != NOTHING)
	common_props = dbpriv_count_properties(common);
    else
	common_props = 0;

    old_props = dbpriv_count_properties(old_parent) - common_props;
    new_props = dbpriv_count_properties(new_parent) - common_props;

    fix_props(oid, 0, old_props, new_props, common_props);
#endif
}


/*
 * $Log$
 * Revision 2.6  1996/04/08  01:08:32  pavel
 * Fixed `db_rename_propdef()' to allow case-only changes.  Release 1.8.0p3.
 *
 * Revision 2.5  1996/02/11  00:46:48  pavel
 * Enhanced db_find_property() to report the defining object of the found
 * property.  Release 1.8.0beta2.
 *
 * Revision 2.4  1996/02/08  07:18:02  pavel
 * Renamed TYPE_NUM to TYPE_INT.  Updated copyright notice for 1996.
 * Release 1.8.0beta1.
 *
 * Revision 2.3  1995/12/31  03:27:40  pavel
 * Removed a few more uses of `unsigned'.  Reordered things in
 * db_delete_propdef() to fix an occasional memory smash.
 * Release 1.8.0alpha4.
 *
 * Revision 2.2  1995/12/28  00:41:34  pavel
 * Made *all* built-in property references return fresh value references.
 * Release 1.8.0alpha3.
 *
 * Revision 2.1  1995/12/11  07:52:27  pavel
 * Added support for renaming propdefs.
 *
 * Release 1.8.0alpha2.
 *
 * Revision 2.0  1995/11/30  04:21:13  pavel
 * New baseline version, corresponding to release 1.8.0alpha1.
 *
 * Revision 1.1  1995/11/30  04:21:02  pavel
 * Initial revision
 */
