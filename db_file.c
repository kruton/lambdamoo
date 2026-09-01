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
 * Routines for initializing, loading, dumping, and shutting down the database
 *****************************************************************************/

#include "db.h"

#include "config.h"
#include "options.h"

#include "my-stat.h"
#include "my-unistd.h"
#include "my-stdio.h"
#include "my-stdlib.h"
#include "my-string.h"

#if CHECKPOINT_MODE == CPM_THREADED
#  include <pthread.h>
#endif

#include "db_io.h"
#include "db_private.h"
#include "exceptions.h"
#include "list.h"
#include "log.h"
#include "ref_count.h"
#include "server.h"
#include "storage.h"
#include "streams.h"
#include "str_intern.h"
#include "tasks.h"
#include "timers.h"
#include "utils.h"
#include "version.h"
#include "waif.h"

static char *input_db_name, *dump_db_name;
static int dump_generation = 0;
static Var checkpoint_users = { .type = TYPE_NONE };
static Var checkpoint_connections = { .type = TYPE_NONE };
static const char *header_format_string
= "** LambdaMOO Database, Format Version %u **";

DB_Version dbio_input_version;

#if CHECKPOINT_MODE == CPM_THREADED
static pthread_t checkpoint_thread;
static pthread_mutex_t checkpoint_mutex = PTHREAD_MUTEX_INITIALIZER;
static int checkpoint_thread_running = 0;
static int checkpoint_thread_done = 0;
static int checkpoint_thread_success = 0;
static int checkpoint_stop_requested = 0;
static char *checkpoint_temp_name = NULL;
#endif

static int checkpoint_result_pending = 0;
static int checkpoint_result_success = 0;

#if CHECKPOINT_MODE == CPM_THREADED || CHECKPOINT_MODE == CPM_JOURNALED
#  define CHECKPOINT_BARRIER_ABORT_LIMIT 2
static unsigned checkpoint_barrier_aborts = 0;
#endif

#if CHECKPOINT_MODE == CPM_JOURNALED
#  define JOURNALED_OBJECT_BATCH 64
#  define JOURNALED_PROGRAM_BATCH 16

typedef enum {
    JOURNALED_IDLE, JOURNALED_OBJECTS, JOURNALED_PROGRAMS,
    JOURNALED_ROOTS
} Journaled_Phase;

static Journaled_Phase journaled_phase = JOURNALED_IDLE;
static FILE *journaled_file = NULL;
static char *journaled_temp_name = NULL;
static Objid journaled_max_oid;
static Objid journaled_oid;
static Verbdef *journaled_verb;
static int journaled_verb_index;
static int journaled_nprogs;
static int journaled_written_progs;
#endif

static int
checkpoint_should_stop(void)
{
#if CHECKPOINT_MODE == CPM_THREADED
    int stop;

    pthread_mutex_lock(&checkpoint_mutex);
    stop = checkpoint_stop_requested;
    pthread_mutex_unlock(&checkpoint_mutex);
    return stop;
#else
    return 0;
#endif
}


/*********** Verb and property I/O ***********/

static int
read_verbdef(Verbdef * v)
{
    v->next = 0;
    v->program = 0;
    return (dbio_read_string_intern(&v->name) &&
	    dbio_read_objid(&v->owner) &&
	    dbio_read_uint16(&v->perms) &&
	    dbio_read_int16(&v->prep));
}

static void
write_verbdef(Verbdef * v)
{
    dbio_write_string(v->name);
    dbio_write_objid(v->owner);
    dbio_write_intmax(v->perms);
    dbio_write_intmax(v->prep);
}

static int
read_propdef(Propdef *p)
{
    const char *name;
    return dbio_read_string_intern(&name) &&
	((*p = dbpriv_new_propdef(name)), 1);
}

static void
write_propdef(Propdef * p)
{
    dbio_write_string(p->name);
}

static int
read_propval(Pval * p)
{
    return
	dbio_read_var(&p->var)      &&
	dbio_read_objid(&p->owner)  &&
	dbio_read_uint16(&p->perms);
}

static void
write_propval(Pval * p)
{
    dbio_write_var(p->var);
    dbio_write_objid(p->owner);
    dbio_write_intmax(p->perms);
}


/*********** Object I/O ***********/

static int
read_object(void)
{
    Objid oid;
    Object *o;

    int sc = dbio_scxnf("#%"SCNdN"\v recycled", &oid);
    if (!sc) {
	errlog("READ_OBJECT: Bad first line\n");
	return 0;
    }
    if (oid != db_last_used_objid() + 1) {
	errlog("READ_OBJECT: Object number is out of order (expecting 1+#%"PRIdN")\n",
	       db_last_used_objid());
	return 0;
    }

    if (sc == 2) {
	dbpriv_new_recycled_object();
	return 1;
    }

    /* Every 'return 0' from here to the end of this function
     * should arguably be jumping to or calling a routine that
     * frees this partly-created object, but since
     *   returning 0 from here does
     *   an immediate return 0 from read_db_file() which does
     *   an immediate return 0 from db_load() which does
     *   an immediate exit(1),
     * it is not clear there would be any point --wrog
     */
    o = dbpriv_new_object();

    intmax_t i;
    intmax_t nverbdefs;
    if (!(dbio_read_string_intern(&o->name) &&
	  dbio_skip_lines(1, "READ_OBJECT") &&
	  /* discard old handles string */

	  dbio_read_uint16(&o->flags)   &&
	  dbio_read_objid(&o->owner)    &&

	  dbio_read_objid(&o->location) &&
	  dbio_read_objid(&o->contents) &&
	  dbio_read_objid(&o->next)     &&

	  dbio_read_objid(&o->parent)   &&
	  dbio_read_objid(&o->child)    &&
	  dbio_read_objid(&o->sibling)  &&
	  dbio_read_intmax(&nverbdefs)))
	return 0;

    Verbdef **prevv = &(o->verbdefs);
    *prevv = NULL;
    for (i = nverbdefs; i > 0; --i) {
	Verbdef *v = mymalloc(sizeof(Verbdef), M_VERBDEF);
	if (!read_verbdef(v))
	    return 0;
	*prevv = v;
	prevv = &(v->next);
    }


    intmax_t npropdefs;
    if (!dbio_read_intmax(&npropdefs))
	return 0;

    o->propdefs.cur_length = npropdefs;
    o->propdefs.max_length = npropdefs;
    o->propdefs.l = NULL;
    if (npropdefs != 0) {
	o->propdefs.l = mymalloc(npropdefs * sizeof(Propdef), M_PROPDEF);
	for (i = 0; i < npropdefs; i++)
	    if (!read_propdef(&o->propdefs.l[i]))
		return 0;
    }

    intmax_t nprops;
    if (!dbio_read_intmax(&nprops))
	return 0;

    if (nprops)
	o->propval = mymalloc(nprops * sizeof(Pval), M_PVAL);
    else
	o->propval = 0;

    for (i = 0; i < nprops; i++) {
	if (!read_propval(o->propval + i))
	    return 0;
    }

    return 1;
}

static void
write_object(Objid oid)
{
    Object *o;
    Verbdef *v;
    int i;
    int nverbdefs, nprops;

    if (dbpriv_checkpoint_active())
	o = dbpriv_find_frozen_object(oid);
    else
	o = dbpriv_find_object(oid);
    if (!o) {
	dbio_printf("#%"PRIdN" recycled\n", oid);
	return;
    }

    dbio_printf("#%"PRIdN"\n", oid);
    dbio_write_string(o->name);
    dbio_write_string("");	/* placeholder for old handles string */
    dbio_write_intmax(o->flags);

    dbio_write_objid(o->owner);

    dbio_write_objid(o->location);
    dbio_write_objid(o->contents);
    dbio_write_objid(o->next);

    dbio_write_objid(o->parent);
    dbio_write_objid(o->child);
    dbio_write_objid(o->sibling);

    for (v = o->verbdefs, nverbdefs = 0; v; v = v->next)
	nverbdefs++;

    dbio_write_intmax(nverbdefs);
    for (v = o->verbdefs; v; v = v->next)
	write_verbdef(v);

    dbio_write_intmax(o->propdefs.cur_length);
    for (i = 0; i < o->propdefs.cur_length; i++)
	write_propdef(&o->propdefs.l[i]);

    nprops = dbpriv_checkpoint_active()
	? dbpriv_count_frozen_properties(oid)
	: dbpriv_count_properties(oid);

    dbio_write_intmax(nprops);
    for (i = 0; i < nprops; i++)
	write_propval(o->propval + i);
}


/*********** File-IO Hooks ***********/

#define  DB_HOOK_TABLE_SIZE  5

static
struct db_file_hook {
    db_before_hook before;
    db_after_hook after;
    int seq;
    const char *msg;
}
    load_hooks[DB_HOOK_TABLE_SIZE],
    save_hooks[DB_HOOK_TABLE_SIZE];

static unsigned
    next_load = 0,
    next_save = 0,
    hooks_initialized = 0;

static void
register_db_hooks(struct db_file_hook hooks[], unsigned *next,
		  int seq, db_before_hook before, db_after_hook after,
		  const char *message)
{
    if (*next >= DB_HOOK_TABLE_SIZE)
	panic("need to increase DB_HOOK_TABLE_SIZE in " __FILE__);
    if (hooks_initialized)
	panic("register_db_hooks() called too late");

    struct db_file_hook *dfh = hooks + *next;
    dfh->seq    = seq;
    dfh->before = before;
    dfh->after  = after;
    dfh->msg    = message;
    ++*next;
}

static void
db_run_before_hooks(struct db_file_hook hooks[], unsigned next,
		    const char *which)
{
    unsigned i;
    for (i = 0; i < next; ++i)
	if (hooks[i].before) {
	    oklog("BEFORE(%s): %s\n", which, hooks[i].msg);
	    hooks[i].before();
	}
}

static void
db_run_after_hooks(struct db_file_hook hooks[], unsigned next,
		   const char *which, int success)
{
    unsigned i = next;
    while (i--)
	if (hooks[i].after) {
	    oklog("AFTER(%s): %s\n", which, hooks[i].msg);
	    hooks[i].after(success);
	}
}

/* yes, I hate writing things twice; how could you tell? */
#define DO_LOADSAVE_(DO)   DO(load)   DO(save)

#define FNS_(load)						\
void								\
register_db_##load##_hooks(int seq,				\
			   db_before_hook before,		\
			   db_after_hook after,			\
			   const char *message)			\
{								\
    register_db_hooks(load##_hooks, &next_##load,		\
		      seq, before, after, message);		\
}								\
								\
static inline void						\
db_run_before_##load##_hooks(void)				\
{								\
    db_run_before_hooks(load##_hooks, next_##load, #load);	\
}								\
								\
static inline void						\
db_run_after_##load##_hooks(int success)			\
{								\
    db_run_after_hooks(load##_hooks, next_##load,		\
		       #load, success);				\
}								\

DO_LOADSAVE_(FNS_)
#undef FNS_

static int
dfh_compare(const void *dfh_a, const void *dfh_b)
{
    const struct db_file_hook *a = dfh_a;
    const struct db_file_hook *b = dfh_b;

    return a->seq < b->seq ? -1 : (a->seq == b->seq ? 0 : 1);
}

void
db_init_hooks(void)
{
    if (hooks_initialized)
	panic("db_init_hooks() called twice?");
    ++hooks_initialized;

#   define QS_(load)				\
    qsort(load##_hooks, next_##load,		\
	  sizeof(struct db_file_hook),		\
	  dfh_compare);				\

    DO_LOADSAVE_(QS_)
#   undef QS_
}

#undef DO_LOADSAVE_

/*********** File-level Input ***********/

static int
validate_hierarchies(void)
{
    Objid oid;
    Objid size = db_last_used_objid() + 1;
    int broken = 0;
    int fixed_nexts = 0;

    oklog("VALIDATING the object hierarchies ...\n");

#   define MAYBE_LOG_PROGRESS					\
    {								\
        if (log_report_progress()) {				\
	    oklog("VALIDATE: Done through #%"PRIdN" ...\n", oid);	\
	}							\
    }

    oklog("VALIDATE: Phase 1: Check for invalid objects ...\n");
    for (oid = 0; oid < size; oid++) {
	Object *o = dbpriv_find_object(oid);

	MAYBE_LOG_PROGRESS;
	if (o) {
	    if (o->location == NOTHING && o->next != NOTHING) {
		o->next = NOTHING;
		fixed_nexts++;
	    }
#	    define CHECK(field, name) 					\
	    {								\
	        if (o->field != NOTHING					\
		    && !dbpriv_find_object(o->field)) {			\
		    errlog("VALIDATE: #%"PRIdN".%s = #%"PRIdN" <invalid> ... fixed.\n", \
			   oid, name, o->field);			\
		    o->field = NOTHING;				  	\
		}							\
	    }

	    CHECK(parent, "parent");
	    CHECK(child, "child");
	    CHECK(sibling, "sibling");
	    CHECK(location, "location");
	    CHECK(contents, "contents");
	    CHECK(next, "next");

#	    undef CHECK
	}
    }

    if (fixed_nexts != 0)
	errlog("VALIDATE: Fixed %d should-be-null next pointer(s) ...\n",
	       fixed_nexts);

    oklog("VALIDATE: Phase 2: Check for cycles ...\n");
    for (oid = 0; oid < size; oid++) {
	Object *o = dbpriv_find_object(oid);

	MAYBE_LOG_PROGRESS;
	if (o) {
#	    define CHECK(start, field, name)			\
	    {							\
		Objid slower = start;				\
		Objid faster = slower;				\
		while (faster != NOTHING) {			\
		    faster = dbpriv_find_object(faster)->field;	\
		    if (faster == NOTHING)			\
			break;					\
		    faster = dbpriv_find_object(faster)->field;	\
		    slower = dbpriv_find_object(slower)->field;	\
		    if (faster == slower) {			\
			errlog("VALIDATE: Cycle in `%s' chain of #%"PRIdN"\n", \
			       name, oid);			\
			broken = 1;				\
			break;					\
		    }						\
		}						\
	    }

	    CHECK(o->parent, parent, "parent");
	    CHECK(o->child, sibling, "child");
	    CHECK(o->location, location, "location");
	    CHECK(o->contents, next, "contents");

#	    undef CHECK

	    /* setup for phase 3:  set two temp flags on every object */
	    o->flags |= (3<<FLAG_FIRST_TEMP);
	}
    }

    if (broken)			/* Can't continue if cycles found */
	return 0;

    oklog("VALIDATE: Phase 3a: Finding delusional parents ...\n");
    for (oid = 0; oid < size; oid++) {
	Object *o = dbpriv_find_object(oid);

	MAYBE_LOG_PROGRESS;
	if (o) {
#	    define CHECK(up, down, down_name, across, FLAG)	\
	    {							\
		Objid	oidkid;					\
		Object *okid;					\
								\
		for (oidkid = o->down;				\
		     oidkid != NOTHING;				\
		     oidkid = okid->across) {			\
								\
		    okid = dbpriv_find_object(oidkid);		\
		    if (okid->up != oid) {			\
			errlog(					\
			    "VALIDATE: #%"PRIdN" erroneously on #%"PRIdN"'s %s list.\n", \
			    oidkid, oid, down_name);		\
			broken = 1;				\
		    }						\
		    else {					\
			/* mark okid as properly claimed */	\
			okid->flags &= ~(1<<(FLAG));		\
		    }						\
		}						\
	    }

	    CHECK(parent,   child,    "child",    sibling, FLAG_FIRST_TEMP);
	    CHECK(location, contents, "contents", next,    FLAG_FIRST_TEMP+1);

#	    undef CHECK
	}
    }

    oklog("VALIDATE: Phase 3b: Finding delusional children ...\n");
    for (oid = 0; oid < size; oid++) {
	Object *o = dbpriv_find_object(oid);

	MAYBE_LOG_PROGRESS;
	if (o) {
#	    define CHECK(up, up_name, down_name, FLAG)			\
	    {								\
		/* If oid is unclaimed, up must be NOTHING */		\
		if ((o->flags & (1<<(FLAG))) && o->up != NOTHING) {	\
		    errlog("VALIDATE: #%"PRIdN" not in %s (#%"PRIdN")'s %s list.\n", \
			   oid, up_name, o->up, down_name);		\
		    broken = 1;						\
		}							\
	    }

	    CHECK(parent,   "parent",   "child",    FLAG_FIRST_TEMP);
	    CHECK(location, "location", "contents", FLAG_FIRST_TEMP+1);

	    /* clear temp flags */
	    o->flags &= ~(3<<FLAG_FIRST_TEMP);

#	    undef CHECK
	}
    }

    oklog("VALIDATING the object hierarchies ... finished.\n");
    return !broken;
}

static const char *
fmt_verb_name(void *data)
{
    db_verb_handle *h = data;
    static Stream *s = 0;

    if (!s)
	s = new_stream(40);

    stream_printf(s, "#%"PRIdN":%s", db_verb_definer(*h), db_verb_names(*h));
    return reset_stream(s);
}

static int
read_db_file(void)
{
    /* Evidently, prehistory DBs had no header line, they would just
     * go straight to the object count.  Therefore, a prehistory DB
     * will not start with '*'.  Since stdio allows us to put back
     * one character, we can do a quick probe.  I prefer this to
     * further messing with dbio_scxnf.  --wrog
     */
    int first_byte = dbio_peek_byte();
    if (header_format_string[0] != first_byte) {
	dbio_input_version = DBV_Prehistory;
    }
    else if (!dbio_scxnf(header_format_string, &dbio_input_version)) {
	errlog("READ_DB_FILE: Bad DB header (no version?)\n");
	return 0;
    }
    else if (!check_db_version(dbio_input_version)) {
	errlog("READ_DB_FILE: Unknown DB version number: %u\n",
	       dbio_input_version);
	return 0;
    }

    UNum i,
	nobjs = 0,
	nprogs = 0,
	nusers = 0;

    if (first_byte != EOF &&
	!dbio_scxnf("%"SCNuN"\n%"SCNuN"\n%*d\n%"SCNuN,
		    &nobjs, &nprogs, &nusers)) {
	errlog("READ_DB_FILE: Bad DB header (missing counts?)\n");
	return 0;
    }

    Var user_list = new_list(nusers);
    for (i = 1; i <= nusers; i++) {
	user_list.v.list[i].type = TYPE_OBJ;
	if (!dbio_read_objid(&user_list.v.list[i].v.obj))
	    return 0;
    }
    dbpriv_set_all_users(user_list);

    oklog("LOADING: Reading %"PRIdN" objects...\n", nobjs);
    for (i = 1; i <= nobjs; i++) {
	if (!read_object()) {
	    errlog("READ_DB_FILE: Bad object #%"PRIdN".\n", i - 1);
	    return 0;
	}
	if (i == nobjs || log_report_progress())
	    oklog("LOADING: Done reading %"PRIdN" objects ...\n", i);
    }

    if (!validate_hierarchies()) {
	errlog("READ_DB_FILE: Errors in object hierarchies.\n");
	return 0;
    }
    oklog("LOADING: Reading %"PRIdN" MOO verb programs...\n", nprogs);
    for (i = 1; i <= nprogs; i++) {
	Objid oid;
	UNum vnum;
	if (!dbio_scxnf("#%"SCNdN":%"SCNdN, &oid, &vnum)) {
	    errlog("READ_DB_FILE: Bad program header, i = %"PRIdN".\n", i);
	    return 0;
	}
	if (!valid(oid)) {
	    errlog("READ_DB_FILE: Verb for non-existant object: #%"PRIdN":%"PRIdN".\n",
		   oid, vnum);
	    return 0;
	}

	db_verb_handle h = db_find_indexed_verb(oid, vnum + 1);	/* DB file is 0-based. */
	if (!h.ptr) {
	    errlog("READ_DB_FILE: Unknown verb index: #%"PRIdN":%"PRIdN".\n", oid, vnum);
	    return 0;
	}

	Program *program = dbio_read_program(dbio_input_version, fmt_verb_name, &h);
	if (!program) {
	    errlog("READ_DB_FILE: Unparsable program #%"PRIdN":%"PRIdN".\n", oid, vnum);
	    return 0;
	}
	db_set_verb_program(h, program);
	if (i == nprogs || log_report_progress())
	    oklog("LOADING: Done reading %"PRIdN" verb programs...\n", i);
    }

    oklog("LOADING: Reading forked and suspended tasks...\n");
    if (first_byte != EOF && !read_task_queue()) {
	errlog("READ_DB_FILE: Can't read task queue.\n");
	return 0;
    }
    oklog("LOADING: Reading list of formerly active connections...\n");
    if (!read_active_connections()) {
	errlog("DB_READ: Can't read active connections.\n");
	return 0;
    }
    dbpriv_dbio_input_finished();
    return 1;
}


/*********** File-level Output ***********/

static int
write_db_file(const char *reason)
{
    Objid oid;
    Objid max_oid = dbpriv_checkpoint_active()
	? dbpriv_frozen_last_used_objid()
	: db_last_used_objid();
    Verbdef *v;
    Var user_list;
    int i;
    volatile int nprogs = 0;
    volatile int success = 1;

    db_run_before_save_hooks();

    for (oid = 0; oid <= max_oid; oid++) {
	Object *o = dbpriv_checkpoint_active()
	    ? dbpriv_find_frozen_object(oid) : dbpriv_find_object(oid);

	if (o)
	    for (v = o->verbdefs; v; v = v->next)
		if (v->program)
		    nprogs++;
    }

    user_list = checkpoint_users.type == TYPE_LIST
	? checkpoint_users : db_all_users();

    TRY {
	dbio_printf(header_format_string, current_db_version);
	dbio_printf("\n%"PRIdN"\n%d\n%d\n%"PRIdN"\n",
		    max_oid + 1, nprogs, 0, user_list.v.list[0].v.num);
	for (i = 1; i <= user_list.v.list[0].v.num; i++)
	    dbio_write_objid(user_list.v.list[i].v.obj);
	oklog("%s: Writing %"PRIdN" objects...\n", reason, max_oid + 1);
	for (oid = 0; oid <= max_oid; oid++) {
	    if (checkpoint_should_stop())
		RAISE(dbpriv_dbio_failed, 0);
	    write_object(oid);
	    if (oid == max_oid || log_report_progress())
		oklog("%s: Done writing %"PRIdN" objects...\n", reason, oid + 1);
	}
	oklog("%s: Writing %d MOO verb programs...\n", reason, nprogs);
	for (i = 0, oid = 0; oid <= max_oid; oid++) {
	    Object *o = dbpriv_checkpoint_active()
		? dbpriv_find_frozen_object(oid) : dbpriv_find_object(oid);

	    if (checkpoint_should_stop())
		RAISE(dbpriv_dbio_failed, 0);

	    if (o) {
		int vcount = 0;

		for (v = o->verbdefs; v; v = v->next) {
		    if (v->program) {
			dbio_printf("#%"PRIdN":%d\n", oid, vcount);
			dbio_write_program(v->program);
			if (++i == nprogs || log_report_progress())
			    oklog("%s: Done writing %d verb programs...\n",
				  reason, i);
		    }
		    vcount++;
		}
	    }
	}
	if (checkpoint_should_stop())
	    RAISE(dbpriv_dbio_failed, 0);
	oklog("%s: Writing forked and suspended tasks...\n", reason);
	if (dbpriv_checkpoint_active())
	    tasks_checkpoint_write();
	else
	    write_task_queue();
	oklog("%s: Writing list of formerly active connections...\n", reason);
	if (checkpoint_connections.type == TYPE_LIST)
	    write_active_connections_snapshot(checkpoint_connections);
	else
	    write_active_connections();
    }
    EXCEPT(dbpriv_dbio_failed)
	success = 0;
    ENDTRY;

    db_run_after_save_hooks(success);

    dbpriv_dbio_output_finished();
    return success;
}

typedef enum {
    DUMP_SHUTDOWN, DUMP_CHECKPOINT, DUMP_PANIC
} Dump_Reason;
const char *reason_names[] =
{"DUMPING", "CHECKPOINTING", "PANIC-DUMPING"};

static int
write_dump_path(const char *temp_name, Dump_Reason reason)
{
    FILE *f;
    int success = 1;

    if ((f = fopen(temp_name, "w")) != 0) {
	dbpriv_set_dbio_output(f);
	if (!write_db_file(reason_names[reason])) {
	    log_perror("Trying to dump database");
	    fclose(f);
	    remove(temp_name);
	    success = 0;
	} else {
	    fflush(f);
	    fsync(fileno(f));
	    fclose(f);
	    oklog("%s on %s finished\n", reason_names[reason], temp_name);
	    if (reason != DUMP_PANIC) {
		if (rename(temp_name, dump_db_name) != 0) {
		    log_perror("Renaming temporary dump file");
		    success = 0;
		}
	    }
	}
    } else {
	log_perror("Opening temporary dump file");
	success = 0;
    }

    return success;
}

#if CHECKPOINT_MODE == CPM_JOURNALED

static void
finish_journaled_checkpoint(int success)
{
    db_run_after_save_hooks(success);
    dbpriv_dbio_output_finished();
    if (journaled_file) {
	if (success) {
	    fflush(journaled_file);
	    fsync(fileno(journaled_file));
	}
	fclose(journaled_file);
	journaled_file = NULL;
    }
    if (success && rename(journaled_temp_name, dump_db_name) != 0) {
	log_perror("Renaming temporary dump file");
	success = 0;
    }
    if (!success)
	remove(journaled_temp_name);

    dbpriv_checkpoint_merge();
#if WAIF_CORE
    waif_checkpoint_merge();
#endif
    tasks_checkpoint_end();
    free_var(checkpoint_users);
    checkpoint_users.type = TYPE_NONE;
    free_var(checkpoint_connections);
    checkpoint_connections.type = TYPE_NONE;
    free_str(journaled_temp_name);
    journaled_temp_name = NULL;
    journaled_phase = JOURNALED_IDLE;
    checkpoint_result_success = success;
    checkpoint_result_pending = 1;
}

static int
start_journaled_checkpoint(const char *temp_name)
{
    Objid oid;
    Verbdef *v;
    Var user_list;
    int i;
    volatile int success = 1;

    if (journaled_phase != JOURNALED_IDLE)
	return 1;
    if (!dbpriv_checkpoint_begin())
	return 0;
#if WAIF_CORE
    waif_checkpoint_begin();
#endif
    tasks_checkpoint_begin();
    checkpoint_users = var_ref(db_all_users());
    checkpoint_connections = active_connections_snapshot();
    journaled_temp_name = str_dup(temp_name);
    journaled_max_oid = dbpriv_frozen_last_used_objid();
    journaled_nprogs = 0;
    for (oid = 0; oid <= journaled_max_oid; oid++) {
	Object *o = dbpriv_find_frozen_object(oid);

	if (o)
	    for (v = o->verbdefs; v; v = v->next)
		if (v->program)
		    journaled_nprogs++;
    }

    db_run_before_save_hooks();
    journaled_file = fopen(temp_name, "w");
    if (!journaled_file) {
	log_perror("Opening temporary dump file");
	finish_journaled_checkpoint(0);
	checkpoint_result_pending = 0;
	return 0;
    }
    dbpriv_set_dbio_output(journaled_file);
    user_list = checkpoint_users;
    TRY {
	dbio_printf(header_format_string, current_db_version);
	dbio_printf("\n%"PRIdN"\n%d\n%d\n%"PRIdN"\n",
		    journaled_max_oid + 1, journaled_nprogs, 0,
		    user_list.v.list[0].v.num);
	for (i = 1; i <= user_list.v.list[0].v.num; i++)
	    dbio_write_objid(user_list.v.list[i].v.obj);
    }
    EXCEPT(dbpriv_dbio_failed)
	success = 0;
    ENDTRY;
    if (!success) {
	finish_journaled_checkpoint(0);
	checkpoint_result_pending = 0;
	return 0;
    }

    journaled_oid = 0;
    journaled_verb = NULL;
    journaled_verb_index = 0;
    journaled_written_progs = 0;
    journaled_phase = JOURNALED_OBJECTS;
    oklog("CHECKPOINTING: Writing %"PRIdN" objects cooperatively...\n",
	  journaled_max_oid + 1);
    reset_command_history();
    return 1;
}

static void
advance_journaled_checkpoint(void)
{
    int work = 0;
    volatile int success = 1;

    if (journaled_phase == JOURNALED_IDLE)
	return;
    TRY {
	while (journaled_phase == JOURNALED_OBJECTS
	       && work++ < JOURNALED_OBJECT_BATCH) {
	    if (journaled_oid <= journaled_max_oid)
		write_object(journaled_oid++);
	    else {
		journaled_phase = JOURNALED_PROGRAMS;
		journaled_oid = 0;
		work = 0;
		oklog("CHECKPOINTING: Writing %d MOO verb programs cooperatively...\n",
		      journaled_nprogs);
	    }
	}
	while (journaled_phase == JOURNALED_PROGRAMS
	       && work++ < JOURNALED_PROGRAM_BATCH) {
	    while (!journaled_verb && journaled_oid <= journaled_max_oid) {
		Object *o = dbpriv_find_frozen_object(journaled_oid);

		journaled_verb = o ? o->verbdefs : NULL;
		journaled_verb_index = 0;
		if (!journaled_verb)
		    journaled_oid++;
	    }
	    if (!journaled_verb) {
		journaled_phase = JOURNALED_ROOTS;
		break;
	    }
	    if (journaled_verb->program) {
		dbio_printf("#%"PRIdN":%d\n", journaled_oid,
			    journaled_verb_index);
		dbio_write_program(journaled_verb->program);
		journaled_written_progs++;
	    }
	    journaled_verb = journaled_verb->next;
	    journaled_verb_index++;
	    if (!journaled_verb)
		journaled_oid++;
	}
	if (journaled_phase == JOURNALED_ROOTS) {
	    oklog("CHECKPOINTING: Writing forked and suspended tasks...\n");
	    tasks_checkpoint_write();
	    oklog("CHECKPOINTING: Writing list of formerly active connections...\n");
	    write_active_connections_snapshot(checkpoint_connections);
	}
    }
    EXCEPT(dbpriv_dbio_failed)
	success = 0;
    ENDTRY;

    if (!success) {
	errlog("Abandoning checkpoint attempt...\n");
	finish_journaled_checkpoint(0);
    } else if (journaled_phase == JOURNALED_ROOTS) {
	oklog("CHECKPOINTING on %s finished\n", journaled_temp_name);
	finish_journaled_checkpoint(1);
    }
}

#endif /* CHECKPOINT_MODE == CPM_JOURNALED */

#if CHECKPOINT_MODE == CPM_THREADED

static void *
checkpoint_thread_main(void *unused UNUSED_)
{
#ifdef CHECKPOINT_TEST_DELAY
    /* Test builds use this delay to make the snapshot/mutation race
     * deterministic; production builds do not define it.
     */
    sleep(CHECKPOINT_TEST_DELAY);
#endif
    int success = write_dump_path(checkpoint_temp_name, DUMP_CHECKPOINT);

    pthread_mutex_lock(&checkpoint_mutex);
    checkpoint_thread_success = success;
    checkpoint_thread_done = 1;
    pthread_mutex_unlock(&checkpoint_mutex);
    return NULL;
}

static void
finish_checkpoint_thread(int wait, int stop)
{
    int done;

    pthread_mutex_lock(&checkpoint_mutex);
    if (!checkpoint_thread_running) {
	pthread_mutex_unlock(&checkpoint_mutex);
	return;
    }
    if (stop)
	checkpoint_stop_requested = 1;
    done = checkpoint_thread_done;
    pthread_mutex_unlock(&checkpoint_mutex);
    if (!wait && !done)
	return;

    pthread_join(checkpoint_thread, NULL);
    pthread_mutex_lock(&checkpoint_mutex);
    checkpoint_result_success = checkpoint_thread_success;
    checkpoint_result_pending = 1;
    checkpoint_thread_running = 0;
    checkpoint_thread_done = 0;
    checkpoint_stop_requested = 0;
    pthread_mutex_unlock(&checkpoint_mutex);

    dbpriv_checkpoint_merge();
#if WAIF_CORE
    waif_checkpoint_merge();
#endif
    tasks_checkpoint_end();
    free_var(checkpoint_users);
    checkpoint_users.type = TYPE_NONE;
    free_var(checkpoint_connections);
    checkpoint_connections.type = TYPE_NONE;
    free_str(checkpoint_temp_name);
    checkpoint_temp_name = NULL;
}

#endif /* CHECKPOINT_MODE == CPM_THREADED */

static int
dump_database(Dump_Reason reason)
{
    Stream *s = new_stream(100);
    char *temp_name;
    int success;

  retryDumping:

    stream_printf(s, "%s.#%d#", dump_db_name, dump_generation);
    remove(reset_stream(s));	/* Remove previous checkpoint */

    if (reason == DUMP_PANIC)
	stream_printf(s, "%s.PANIC", dump_db_name);
    else {
	dump_generation++;
	stream_printf(s, "%s.#%d#", dump_db_name, dump_generation);
    }
    temp_name = reset_stream(s);

    oklog("%s on %s ...\n", reason_names[reason], temp_name);

#if CHECKPOINT_MODE == CPM_FORKED
    if (reason == DUMP_CHECKPOINT) {
	switch (fork_server("checkpointer")) {
	case FORK_PARENT:
	    reset_command_history();
	    free_stream(s);
	    return 1;
	case FORK_ERROR:
	    free_stream(s);
	    return 0;
	case FORK_CHILD:
	    set_server_cmdline("(MOO checkpointer)");
	    break;
	}
    }
#elif CHECKPOINT_MODE == CPM_THREADED
    if (reason == DUMP_CHECKPOINT) {
	if (checkpoint_thread_running) {
	    free_stream(s);
	    return 1;
	}
	if (!dbpriv_checkpoint_begin()) {
	    free_stream(s);
	    return 0;
	}
#if WAIF_CORE
	waif_checkpoint_begin();
#endif
	tasks_checkpoint_begin();
	checkpoint_users = var_ref(db_all_users());
	checkpoint_connections = active_connections_snapshot();
	checkpoint_temp_name = str_dup(temp_name);
	checkpoint_thread_done = 0;
	checkpoint_thread_success = 0;
	checkpoint_result_success = 0;
	checkpoint_stop_requested = 0;
	if (pthread_create(&checkpoint_thread, NULL,
			   checkpoint_thread_main, NULL) != 0) {
	    free_str(checkpoint_temp_name);
	    checkpoint_temp_name = NULL;
	    free_var(checkpoint_users);
	    checkpoint_users.type = TYPE_NONE;
	    free_var(checkpoint_connections);
	    checkpoint_connections.type = TYPE_NONE;
	    dbpriv_checkpoint_merge();
#if WAIF_CORE
	    waif_checkpoint_merge();
#endif
	    tasks_checkpoint_end();
	    free_stream(s);
	    return 0;
	}
	checkpoint_thread_running = 1;
	reset_command_history();
	free_stream(s);
	return 1;
    }
#elif CHECKPOINT_MODE == CPM_JOURNALED
    if (reason == DUMP_CHECKPOINT) {
	success = start_journaled_checkpoint(temp_name);
	free_stream(s);
	return success;
    }
#endif

#if CHECKPOINT_MODE == CPM_UNFORKED
    reset_command_history();
#endif

    success = write_dump_path(temp_name, reason);

    if (!success && reason != DUMP_CHECKPOINT) {
	int retry_interval = 60;

	errlog("Waiting %d seconds and retrying dump...\n", retry_interval);
	timer_sleep(retry_interval);
	goto retryDumping;
    }

    if (!success && reason == DUMP_CHECKPOINT)
	errlog("Abandoning checkpoint attempt...\n");

    free_stream(s);

#if CHECKPOINT_MODE == CPM_FORKED
    if (reason == DUMP_CHECKPOINT)
	/* We're a child, so we'd better go away. */
	exit(!success);
#endif

    return success;
}


/*********** External interface ***********/

const char *
db_usage_string(void)
{
    return "input-db-file output-db-file";
}

static FILE *input_db;

int
db_initialize(int *pargc, char ***pargv)
{
    FILE *f;

    if (*pargc < 2)
	return 0;

    input_db_name = str_dup((*pargv)[0]);
    dump_db_name = str_dup((*pargv)[1]);
    *pargc -= 2;
    *pargv += 2;

    if (!(f = fopen(input_db_name, "r"))) {
	fprintf(stderr, "Cannot open input database file: %s\n",
		input_db_name);
	return 0;
    }
    input_db = f;
    dbpriv_build_prep_table();

    return 1;
}

int
db_load(void)
{
    dbpriv_set_dbio_input(input_db);

    db_run_before_load_hooks();

    oklog("LOADING: %s\n", input_db_name);
    if (!read_db_file()) {
	/* XXX is there any point to this? */
	db_run_after_load_hooks(0);

	errlog("DB_LOAD: Cannot load database!\n");
	return 0;
    }
    oklog("LOADING: %s done, will dump new database on %s\n",
	  input_db_name, dump_db_name);

    db_run_after_load_hooks(1);

    fclose(input_db);
    return 1;
}

int
db_flush(enum db_flush_type type)
{
    int success = 0;

#if CHECKPOINT_MODE == CPM_THREADED
    finish_checkpoint_thread(0, 0);
#elif CHECKPOINT_MODE == CPM_JOURNALED
    if (type == FLUSH_IF_FULL || type == FLUSH_ONE_SECOND)
	advance_journaled_checkpoint();
#endif

    switch (type) {
    case FLUSH_IF_FULL:
    case FLUSH_ONE_SECOND:
	success = 1;
	break;

    case FLUSH_ALL_NOW:
	success = dump_database(DUMP_CHECKPOINT);
	break;

    case FLUSH_PANIC:
	success = dump_database(DUMP_PANIC);
	break;
    }

    return success;
}

#if CHECKPOINT_MODE == CPM_THREADED || CHECKPOINT_MODE == CPM_JOURNALED
static void
checkpoint_barrier_aborted(const char *operation)
{
    checkpoint_barrier_aborts++;
    errlog("CHECKPOINTING: blocked by %s (%u/%u); retrying checkpoint...\n",
	   operation, checkpoint_barrier_aborts,
	   CHECKPOINT_BARRIER_ABORT_LIMIT);
}
#endif

void
db_checkpoint_barrier(const char *operation)
{
#if CHECKPOINT_MODE == CPM_THREADED
    int active = dbpriv_checkpoint_active();

    if (!active)
	return;
    if (checkpoint_barrier_aborts >= CHECKPOINT_BARRIER_ABORT_LIMIT) {
	errlog("CHECKPOINTING: blocked repeatedly by %s; waiting for checkpoint to finish...\n",
	       operation);
	finish_checkpoint_thread(1, 0);
	if (checkpoint_result_success)
	    checkpoint_barrier_aborts = 0;
	else
	    errlog("CHECKPOINTING: checkpoint failed while %s was waiting.\n",
		   operation);
    } else {
	finish_checkpoint_thread(1, 1);
	if (!checkpoint_result_success) {
	    checkpoint_barrier_aborted(operation);
	    server_request_checkpoint();
	}
    }
#elif CHECKPOINT_MODE == CPM_JOURNALED
    if (journaled_phase != JOURNALED_IDLE) {
	if (checkpoint_barrier_aborts >= CHECKPOINT_BARRIER_ABORT_LIMIT) {
	    errlog("CHECKPOINTING: blocked repeatedly by %s; finishing checkpoint before continuing...\n",
		   operation);
	    while (journaled_phase != JOURNALED_IDLE)
		advance_journaled_checkpoint();
	    if (checkpoint_result_success)
		checkpoint_barrier_aborts = 0;
	    else
		errlog("CHECKPOINTING: checkpoint failed while %s was waiting.\n",
		       operation);
	} else {
	    finish_journaled_checkpoint(0);
	    checkpoint_barrier_aborted(operation);
	    server_request_checkpoint();
	}
    }
#else
    if (dbpriv_checkpoint_active())
	dbpriv_checkpoint_merge();
#endif
}

int
db_checkpoint_finished(int *success)
{
#if CHECKPOINT_MODE == CPM_THREADED
    finish_checkpoint_thread(0, 0);
#elif CHECKPOINT_MODE == CPM_JOURNALED
    advance_journaled_checkpoint();
#endif
    if (!checkpoint_result_pending)
	return 0;
    *success = checkpoint_result_success;
#if CHECKPOINT_MODE == CPM_THREADED || CHECKPOINT_MODE == CPM_JOURNALED
    if (*success)
	checkpoint_barrier_aborts = 0;
#endif
    checkpoint_result_pending = 0;
    return 1;
}

int64_t
db_disk_size(void)
{
    struct stat st;

    if ((dump_generation == 0 || stat(dump_db_name, &st) < 0)
	&& stat(input_db_name, &st) < 0)
	return -1;
    else
	return st.st_size;
}

void
db_shutdown(void)
{
    db_checkpoint_barrier("shutdown");
    dump_database(DUMP_SHUTDOWN);

    free_str(input_db_name);
    free_str(dump_db_name);
}


/*
 * $Log$
 * Revision 2.5  1996/04/08  01:07:21  pavel
 * Changed a boot-time error message to go directly to stderr, instead of
 * through the logging package.  Release 1.8.0p3.
 *
 * Revision 2.4  1996/02/08  07:20:18  pavel
 * Renamed err/logf() to errlog/oklog().  Updated copyright notice for 1996.
 * Release 1.8.0beta1.
 *
 * Revision 2.3  1995/12/31  03:27:54  pavel
 * Added missing #include "options.h".  Release 1.8.0alpha4.
 *
 * Revision 2.2  1995/12/28  00:51:39  pavel
 * Added db_disk_size().  Added support for printing location of
 * MOO-compilation warnings and errors during loading.  More slight
 * improvements to load-time progress messages.  Added dump-time progress
 * messages.  Added init-time call to build preposition table.
 * Release 1.8.0alpha3.
 *
 * Revision 2.1  1995/12/11  07:55:01  pavel
 * Added missing #include of "my-stdlib.h".  Slightly improved clarity of the
 * progress messages during DB loading.
 *
 * Release 1.8.0alpha2.
 *
 * Revision 2.0  1995/11/30  04:19:37  pavel
 * New baseline version, corresponding to release 1.8.0alpha1.
 *
 * Revision 1.1  1995/11/30  04:19:11  pavel
 * Initial revision
 */
