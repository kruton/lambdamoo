/******************************************************************************
  Copyright (c) 1992, 1995, 1996 Xerox Corporation.  All rights reserved.
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

#include "verbs.h"
#include "bf_register.h"

#include "config.h"

#include "my-string.h"

#include "db.h"
#include "exceptions.h"
#include "execute.h"
#include "functions.h"
#ifdef ENABLE_JIT
#include "jit.h"
#endif
#include "list.h"
#include "log.h"
#include "match.h"
#include "parse_cmd.h"
#include "parser.h"
#include "server.h"
#include "storage.h"
#include "unparse.h"
#include "utils.h"

struct verb_data {
    Var r;
    int i;
};

static int
add_to_list(void *data, const char *verb_name)
{
    struct verb_data *d = data;

    d->i++;
    d->r.v.list[d->i].type = TYPE_STR;
    d->r.v.list[d->i].v.str = str_ref(verb_name);

    return 0;
}

static package
bf_verbs(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object) */
    Objid oid = arglist.v.list[1].v.obj;

    free_var(arglist);

    if (!valid(oid))
	return make_error_pack(E_INVARG);
    else if (!db_object_allows(oid, progr, FLAG_READ))
	return make_error_pack(E_PERM);
    else {
	struct verb_data d;

	d.r = new_list(db_count_verbs(oid));
	d.i = 0;
	db_for_all_verbs(oid, add_to_list, &d);

	return make_var_pack(d.r);
    }
}

static enum error
validate_verb_info(Var v, Objid * owner, unsigned *flags, const char **names)
{
    const char *s;

    if (!(v.type == TYPE_LIST
	  && v.v.list[0].v.num == 3
	  && v.v.list[1].type == TYPE_OBJ
	  && v.v.list[2].type == TYPE_STR
	  && v.v.list[3].type == TYPE_STR))
	return E_TYPE;

    *owner = v.v.list[1].v.obj;
    if (!valid(*owner))
	return E_INVARG;

    for (*flags = 0, s = v.v.list[2].v.str; *s; s++) {
	switch (*s) {
	case 'r':
	case 'R':
	    *flags |= VF_READ;
	    break;
	case 'w':
	case 'W':
	    *flags |= VF_WRITE;
	    break;
	case 'x':
	case 'X':
	    *flags |= VF_EXEC;
	    break;
	case 'd':
	case 'D':
	    *flags |= VF_DEBUG;
	    break;
	default:
	    return E_INVARG;
	}
    }

    *names = v.v.list[3].v.str;
    while (**names == ' ')
	(*names)++;
    if (**names == '\0')
	return E_INVARG;

    *names = str_dup(*names);

    return E_NONE;
}

static int
match_arg_spec(const char *s, db_arg_spec * spec)
{
    if (!mystrcasecmp(s, "none")) {
	*spec = ASPEC_NONE;
	return 1;
    } else if (!mystrcasecmp(s, "any")) {
	*spec = ASPEC_ANY;
	return 1;
    } else if (!mystrcasecmp(s, "this")) {
	*spec = ASPEC_THIS;
	return 1;
    } else
	return 0;
}

static int
match_prep_spec(const char *s, db_prep_spec * spec)
{
    if (!mystrcasecmp(s, "none")) {
	*spec = PREP_NONE;
	return 1;
    } else if (!mystrcasecmp(s, "any")) {
	*spec = PREP_ANY;
	return 1;
    } else
	return (*spec = db_match_prep(s)) != PREP_NONE;
}

static enum error
validate_verb_args(Var v, db_arg_spec * dobj, db_prep_spec * prep,
		   db_arg_spec * iobj)
{
    if (!(v.type == TYPE_LIST
	  && v.v.list[0].v.num == 3
	  && v.v.list[1].type == TYPE_STR
	  && v.v.list[2].type == TYPE_STR
	  && v.v.list[3].type == TYPE_STR))
	return E_TYPE;

    if (!match_arg_spec(v.v.list[1].v.str, dobj)
	|| !match_prep_spec(v.v.list[2].v.str, prep)
	|| !match_arg_spec(v.v.list[3].v.str, iobj))
	return E_INVARG;

    return E_NONE;
}

static package
bf_add_verb(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, info, args) */
    Objid oid = arglist.v.list[1].v.obj;
    Var info = arglist.v.list[2];
    Var args = arglist.v.list[3];
    Var result;
    Objid owner;
    unsigned flags;
    const char *names;
    db_arg_spec dobj, iobj;
    db_prep_spec prep;
    enum error e;

    if ((e = validate_verb_info(info, &owner, &flags, &names)) != E_NONE)
	/* Already failed */ ;
    else if ((e = validate_verb_args(args, &dobj, &prep, &iobj)) != E_NONE)
	free_str(names);
    else if (!valid(oid)) {
	free_str(names);
	e = E_INVARG;
    } else if (!db_object_allows(oid, progr, FLAG_WRITE)
	       || (progr != owner && !is_wizard(progr))) {
	free_str(names);
	e = E_PERM;
    } else {
	result.type = TYPE_INT;
	result.v.num = db_add_verb(oid, names, owner, flags, dobj, prep, iobj);
    }

    free_var(arglist);
    if (e == E_NONE)
	return make_var_pack(result);
    else
	return make_error_pack(e);
}

enum error
validate_verb_descriptor(Var desc)
{
    if (desc.type == TYPE_STR)
	return E_NONE;
    else if (desc.type != TYPE_INT)
	return E_TYPE;
    else if (desc.v.num <= 0)
	return E_INVARG;
    else
	return E_NONE;
}

db_verb_handle
find_described_verb(Objid oid, Var desc)
{
    if (desc.type == TYPE_INT)
	return db_find_indexed_verb(oid, desc.v.num);
    else {
	int flag = server_flag_option("support_numeric_verbname_strings", 0);

	return db_find_defined_verb(oid, desc.v.str, flag);
    }
}

static package
bf_delete_verb(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc) */
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    db_verb_handle h;
    enum error e;

    if ((e = validate_verb_descriptor(desc)) != E_NONE);	/* Do nothing; e is already set. */
    else if (!valid(oid))
	e = E_INVARG;
    else if (!db_object_allows(oid, progr, FLAG_WRITE))
	e = E_PERM;
    else {
	h = find_described_verb(oid, desc);
	if (h.ptr)
	    db_delete_verb(h);
	else
	    e = E_VERBNF;
    }

    free_var(arglist);
    if (e == E_NONE)
	return no_var_pack();
    else
	return make_error_pack(e);
}

#ifdef ENABLE_JIT
static Var
jit_metadata_pair(const char *name, Var value)
{
    Var pair = new_list(2);

    pair.v.list[1].type = TYPE_STR;
    pair.v.list[1].v.str = str_dup(name);
    pair.v.list[2] = value;
    return pair;
}

static Var
jit_metadata_num_pair(const char *name, uint64_t number)
{
    Var value;

    value.type = TYPE_INT;
    value.v.num = number > NUM_MAX ? NUM_MAX : (Num) number;
    return jit_metadata_pair(name, value);
}

static Var
jit_deopt_metadata(const JITProgramStats *stats)
{
    Var reasons = new_list(JIT_DEOPT_NUM_REASONS - 1);
    int reason;

    for (reason = 1; reason < JIT_DEOPT_NUM_REASONS; reason++)
	reasons.v.list[reason] = jit_metadata_num_pair(
	    jit_deopt_reason_name((JITDeoptReason) reason),
	    stats->deopts_by_reason[reason]);
    return reasons;
}

static Var
jit_metadata(JITProgram *program)
{
    JITProgramStats stats;
    Var metadata = new_list(37);
    Var value;

    jit_program_stats(program, &stats);

    value.type = TYPE_STR;
    value.v.str = str_dup(jit_program_state_name(program));
    metadata.v.list[1] = jit_metadata_pair("state", value);
    value.type = TYPE_INT;
    value.v.num = jit_program_is_eligible(program);
    metadata.v.list[2] = jit_metadata_pair("eligible", value);
    value.type = TYPE_STR;
    value.v.str = str_dup("mir");
    metadata.v.list[3] = jit_metadata_pair("backend", value);
    value.type = TYPE_STR;
    value.v.str = str_dup("a8ab7c31cd5f9b23b77d84c60b3d83e62d9d304c");
    metadata.v.list[4] = jit_metadata_pair("backend_version", value);
    value.type = TYPE_STR;
    value.v.str = str_dup("integer-v1");
    metadata.v.list[5] = jit_metadata_pair("tier", value);
    value.type = TYPE_STR;
    value.v.str = str_dup(jit_program_reason(program));
    metadata.v.list[6] = jit_metadata_pair("reason", value);
    value.type = TYPE_INT;
    value.v.num = jit_program_anchor_count(program);
    metadata.v.list[7] = jit_metadata_pair("anchors", value);
    value.v.num = jit_program_deopt_map_count(program);
    metadata.v.list[8] = jit_metadata_pair("deopt_maps", value);
    value.type = TYPE_STR;
    value.v.str = str_dup(jit_program_diagnostic(program));
    metadata.v.list[9] = jit_metadata_pair("diagnostic", value);
    metadata.v.list[10] = jit_metadata_num_pair("entries", stats.entries);
    metadata.v.list[11] = jit_metadata_num_pair("completions",
					       stats.completions);
    metadata.v.list[12] = jit_metadata_num_pair("vm_calls", stats.vm_calls);
    metadata.v.list[13] = jit_metadata_num_pair("deopts", stats.deopts);
    metadata.v.list[14] = jit_metadata_pair("deopts_by_reason",
					    jit_deopt_metadata(&stats));
    metadata.v.list[15] = jit_metadata_num_pair("last_used_generation",
					       stats.last_used_generation);
    metadata.v.list[16] = jit_metadata_num_pair("last_used_time",
					       stats.last_used_time < 0
					       ? 0 : stats.last_used_time);
    metadata.v.list[17] = jit_metadata_num_pair("compile_attempts",
					       stats.compile_attempts);
    metadata.v.list[18] = jit_metadata_num_pair("compile_successes",
					       stats.compile_successes);
    metadata.v.list[19] = jit_metadata_num_pair("compile_failures",
					       stats.compile_failures);
    metadata.v.list[20] = jit_metadata_num_pair("compile_time_us",
					       stats.compile_time_us);
    metadata.v.list[21] = jit_metadata_num_pair("metadata_bytes",
					       stats.metadata_bytes);
    metadata.v.list[22] = jit_metadata_num_pair("runtime_bytes",
					       stats.runtime_bytes);
    metadata.v.list[23] = jit_metadata_num_pair("machine_code_bytes",
					       stats.machine_code_bytes);
    metadata.v.list[24] = jit_metadata_num_pair("native_allocated_bytes",
					       stats.native_allocated_bytes);
    metadata.v.list[25] = jit_metadata_num_pair("accounted_bytes",
					       stats.accounted_bytes);
    metadata.v.list[26] = jit_metadata_num_pair("continuation_captures",
					       stats.continuation_captures);
    metadata.v.list[27] = jit_metadata_num_pair("continuation_resumes",
					       stats.continuation_resumes);
    metadata.v.list[28] = jit_metadata_num_pair("continuation_materializations",
					       stats.continuation_materializations);
    metadata.v.list[29] = jit_metadata_num_pair("active_continuations",
					       stats.active_continuations);
    metadata.v.list[30] = jit_metadata_num_pair("continuation_bytes",
					       stats.continuation_bytes);
    metadata.v.list[31] = jit_metadata_num_pair("continuation_fast_suspends",
					       stats.continuation_fast_suspends);
    metadata.v.list[32] = jit_metadata_num_pair("native_chain_calls",
					       stats.native_chain_calls);
    metadata.v.list[33] = jit_metadata_num_pair("native_chain_returns",
					       stats.native_chain_returns);
    metadata.v.list[34] = jit_metadata_num_pair("native_chain_promotions",
					       stats.native_chain_promotions);
    metadata.v.list[35] = jit_metadata_num_pair("native_chain_max_depth",
					       stats.native_chain_max_depth);
    metadata.v.list[36] = jit_metadata_num_pair("native_chain_active_frames",
					       stats.native_chain_active_frames);
    metadata.v.list[37] = jit_metadata_num_pair("native_chain_frame_bytes",
					       stats.native_chain_frame_bytes);
    return metadata;
}
#endif

static package
bf_verb_info(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc) */
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    db_verb_handle h;
    Var r;
    unsigned flags;
    char perms[5], *s;
    enum error e;
#ifdef ENABLE_JIT
    int include_jit = arglist.v.list[0].v.num == 3
	&& is_true(arglist.v.list[3]);
#endif

    if ((e = validate_verb_descriptor(desc)) != E_NONE
	|| (e = E_INVARG, !valid(oid))) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    free_var(arglist);

    if (!h.ptr)
	return make_error_pack(E_VERBNF);
    else if (!db_verb_allows(h, progr, VF_READ))
	return make_error_pack(E_PERM);

    r = new_list(
#ifdef ENABLE_JIT
		 include_jit ? 4 :
#endif
		 3);
    r.v.list[1].type = TYPE_OBJ;
    r.v.list[1].v.obj = db_verb_owner(h);
    r.v.list[2].type = TYPE_STR;
    s = perms;
    flags = db_verb_flags(h);
    if (flags & VF_READ)
	*s++ = 'r';
    if (flags & VF_WRITE)
	*s++ = 'w';
    if (flags & VF_EXEC)
	*s++ = 'x';
    if (flags & VF_DEBUG)
	*s++ = 'd';
    *s = '\0';
    r.v.list[2].v.str = str_dup(perms);
    r.v.list[3].type = TYPE_STR;
    r.v.list[3].v.str = str_ref(db_verb_names(h));
#ifdef ENABLE_JIT
    if (include_jit)
	r.v.list[4] = jit_metadata(db_verb_program(h)->jit);
#endif

    return make_var_pack(r);
}

static package
bf_set_verb_info(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc, {owner, flags, names}) */
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    Var info = arglist.v.list[3];
    Objid new_owner;
    unsigned new_flags;
    const char *new_names;
    enum error e;
    db_verb_handle h;

    if ((e = validate_verb_descriptor(desc)) != E_NONE);	/* Do nothing; e is already set. */
    else if (!valid(oid))
	e = E_INVARG;
    else
	e = validate_verb_info(info, &new_owner, &new_flags, &new_names);

    if (e != E_NONE) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    free_var(arglist);

    if (!h.ptr) {
	free_str(new_names);
	return make_error_pack(E_VERBNF);
    } else if (!db_verb_allows(h, progr, VF_WRITE)
	       || (!is_wizard(progr) && db_verb_owner(h) != new_owner)) {
	free_str(new_names);
	return make_error_pack(E_PERM);
    }
    db_set_verb_owner(h, new_owner);
    db_set_verb_flags(h, new_flags);
    db_set_verb_names(h, new_names);

    return no_var_pack();
}

static const char *
unparse_arg_spec(db_arg_spec spec)
{
    switch (spec) {
    case ASPEC_NONE:
	return str_dup("none");
    case ASPEC_ANY:
	return str_dup("any");
    case ASPEC_THIS:
	return str_dup("this");
    default:
	panic("UNPARSE_ARG_SPEC: Unknown db_arg_spec!");
    }
}

static package
bf_verb_args(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc) */
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    db_verb_handle h;
    db_arg_spec dobj, iobj;
    db_prep_spec prep;
    Var r;
    enum error e;

    if ((e = validate_verb_descriptor(desc)) != E_NONE
	|| (e = E_INVARG, !valid(oid))) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    free_var(arglist);

    if (!h.ptr)
	return make_error_pack(E_VERBNF);
    else if (!db_verb_allows(h, progr, VF_READ))
	return make_error_pack(E_PERM);

    db_verb_arg_specs(h, &dobj, &prep, &iobj);
    r = new_list(3);
    r.v.list[1].type = TYPE_STR;
    r.v.list[1].v.str = unparse_arg_spec(dobj);
    r.v.list[2].type = TYPE_STR;
    r.v.list[2].v.str = str_dup(db_unparse_prep(prep));
    r.v.list[3].type = TYPE_STR;
    r.v.list[3].v.str = unparse_arg_spec(iobj);

    return make_var_pack(r);
}

static package
bf_set_verb_args(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc, {dobj, prep, iobj}) */
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    Var args = arglist.v.list[3];
    enum error e;
    db_verb_handle h;
    db_arg_spec dobj, iobj;
    db_prep_spec prep;

    if ((e = validate_verb_descriptor(desc)) != E_NONE);	/* Do nothing; e is already set. */
    else if (!valid(oid))
	e = E_INVARG;
    else
	e = validate_verb_args(args, &dobj, &prep, &iobj);

    if (e != E_NONE) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    free_var(arglist);

    if (!h.ptr)
	return make_error_pack(E_VERBNF);
    else if (!db_verb_allows(h, progr, VF_WRITE))
	return make_error_pack(E_PERM);

    db_set_verb_arg_specs(h, dobj, prep, iobj);

    return no_var_pack();
}

static void
lister(void *data, const char *line)
{
    Var *r = (Var *) data;
    Var v;

    v.type = TYPE_STR;
    v.v.str = str_dup(line);
    *r = listappend(*r, v);
}

static package
bf_verb_code(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc [, fully-paren [, indent]]) */
    int nargs = arglist.v.list[0].v.num;
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    int parens = nargs >= 3 && is_true(arglist.v.list[3]);
    int indent = nargs < 4 || is_true(arglist.v.list[4]);
    db_verb_handle h;
    Var code;
    enum error e;

    if ((e = validate_verb_descriptor(desc)) != E_NONE
	|| (e = E_INVARG, !valid(oid))) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    free_var(arglist);

    if (!h.ptr)
	return make_error_pack(E_VERBNF);
    else if (!db_verb_allows(h, progr, VF_READ))
	return make_error_pack(E_PERM);

    code = new_list(0);
    unparse_program(db_verb_program(h), lister, &code, parens, indent,
		    MAIN_VECTOR);

    return make_var_pack(code);
}

static package
bf_set_verb_code(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{				/* (object, verb-desc, code) */
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    Var code = arglist.v.list[3];
    int i;
    Program *program;
    db_verb_handle h;
    Var errors;
    enum error e;

    for (i = 1; i <= code.v.list[0].v.num; i++)
	if (code.v.list[i].type != TYPE_STR) {
	    free_var(arglist);
	    return make_error_pack(E_TYPE);
	}
    if ((e = validate_verb_descriptor(desc)) != E_NONE
	|| (e = E_INVARG, !valid(oid))) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    if (!h.ptr) {
	free_var(arglist);
	return make_error_pack(E_VERBNF);
    } else if (!is_programmer(progr) || !db_verb_allows(h, progr, VF_WRITE)) {
	free_var(arglist);
	return make_error_pack(E_PERM);
    }
    program = parse_list_as_program(code, &errors);
    if (program) {
	if (task_timed_out)
	    free_program(program);
	else
	    db_set_verb_program(h, program);
    }
    free_var(arglist);
    return make_var_pack(errors);
}

static package
bf_eval(Var arglist, Byte next, void *data UNUSED_, Objid progr)
{
    package p;
    if (next == 1) {

	if (!is_programmer(progr)) {
	    free_var(arglist);
	    p = make_error_pack(E_PERM);
	} else {
	    Var errors;
	    Program *program = parse_list_as_program(arglist, &errors);

	    free_var(arglist);
	    if (program) {
		free_var(errors);
		if (setup_activ_for_eval(program))
		    p = make_call_pack(2, 0);
		else {
		    free_program(program);
		    p = make_error_pack(E_MAXREC);
		}
	    } else {
		Var r;

		r = new_list(2);
		r.v.list[1].type = TYPE_INT;
		r.v.list[1].v.num = 0;
		r.v.list[2] = errors;
		p = make_var_pack(r);
	    }
	}
    } else {			/* next == 2 */
	Var r;

	r = new_list(2);
	r.v.list[1].type = TYPE_INT;
	r.v.list[1].v.num = 1;
	r.v.list[2] = arglist;
	p = make_var_pack(r);
    }
    return p;
}

#ifdef ENABLE_JIT
static package
bf_jit_compile(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{
    Objid oid = arglist.v.list[1].v.obj;
    Var desc = arglist.v.list[2];
    db_verb_handle h;
    enum error e;
    Var metadata;

    if (!is_wizard(progr)) {
	free_var(arglist);
	return make_error_pack(E_PERM);
    }
    if ((e = validate_verb_descriptor(desc)) != E_NONE
	|| (e = E_INVARG, !valid(oid))) {
	free_var(arglist);
	return make_error_pack(e);
    }
    h = find_described_verb(oid, desc);
    free_var(arglist);
    if (!h.ptr)
	return make_error_pack(E_VERBNF);

    jit_program_note_location(db_verb_program(h)->jit, oid, db_verb_index(h));
    (void) jit_program_compile(db_verb_program(h)->jit);
    metadata = jit_metadata(db_verb_program(h)->jit);
    return make_var_pack(metadata);
}

static package
bf_jit_perf_map(Var arglist, Byte next UNUSED_, void *vdata UNUSED_, Objid progr)
{
    int nargs = arglist.v.list[0].v.num;
    int enabled = nargs == 0 || is_true(arglist.v.list[1]);
    Var result;

    free_var(arglist);
    if (!is_wizard(progr))
	return make_error_pack(E_PERM);
    if (nargs > 0) {
	if (enabled) {
	    if (!jit_perf_map_start())
		return make_error_pack(E_QUOTA);
	} else
	    jit_perf_map_stop();
    }
    result = new_list(2);
    result.v.list[1].type = TYPE_INT;
    result.v.list[1].v.num = jit_perf_map_active();
    result.v.list[2].type = TYPE_STR;
    result.v.list[2].v.str = str_dup(jit_perf_map_path());
    return make_var_pack(result);
}
#endif

void
register_verbs(void)
{
    register_function("verbs", 1, 1, bf_verbs, TYPE_OBJ);
#ifdef ENABLE_JIT
    register_function("verb_info", 2, 3, bf_verb_info,
		      TYPE_OBJ, TYPE_ANY, TYPE_ANY);
    register_function("jit_compile", 2, 2, bf_jit_compile,
		      TYPE_OBJ, TYPE_ANY);
    register_function("jit_perf_map", 0, 1, bf_jit_perf_map, TYPE_ANY);
#else
    register_function("verb_info", 2, 2, bf_verb_info, TYPE_OBJ, TYPE_ANY);
#endif
    register_function("set_verb_info", 3, 3, bf_set_verb_info,
		      TYPE_OBJ, TYPE_ANY, TYPE_LIST);
    register_function("verb_args", 2, 2, bf_verb_args, TYPE_OBJ, TYPE_ANY);
    register_function("set_verb_args", 3, 3, bf_set_verb_args,
		      TYPE_OBJ, TYPE_ANY, TYPE_LIST);
    register_function("add_verb", 3, 3, bf_add_verb,
		      TYPE_OBJ, TYPE_LIST, TYPE_LIST);
    register_function("delete_verb", 2, 2, bf_delete_verb, TYPE_OBJ, TYPE_ANY);
    register_function("verb_code", 2, 4, bf_verb_code,
		      TYPE_OBJ, TYPE_ANY, TYPE_ANY, TYPE_ANY);
    register_function("set_verb_code", 3, 3, bf_set_verb_code,
		      TYPE_OBJ, TYPE_ANY, TYPE_LIST);
    register_function("eval", 1, 1, bf_eval, TYPE_STR);
}


/*
 * $Log$
 * Revision 2.8  1996/05/12  21:29:46  pavel
 * Fixed memory leak for verb names string in bf_add_verb.  Release 1.8.0p5.
 *
 * Revision 2.7  1996/03/19  07:19:13  pavel
 * Fixed off-by-one bug in type-checking in set_verb_code().  Release 1.8.0p2.
 *
 * Revision 2.6  1996/02/08  06:39:44  pavel
 * Renamed TYPE_NUM to TYPE_INT.  Updated copyright notice for 1996.
 * Release 1.8.0beta1.
 *
 * Revision 2.5  1996/01/16  07:29:04  pavel
 * Fixed `parens' and `indent' arguments to verb_code() to allow values of any
 * type.  Release 1.8.0alpha6.
 *
 * Revision 2.4  1996/01/11  07:51:42  pavel
 * Fixed bad free() in bf_add_verb().  Release 1.8.0alpha5.
 *
 * Revision 2.3  1995/12/31  03:28:27  pavel
 * Fixed C syntax botch in bf_delete_verb().  Release 1.8.0alpha4.
 *
 * Revision 2.2  1995/12/28  00:25:40  pavel
 * Added support for using numbers to designate defined verbs in built-in
 * functions.  Release 1.8.0alpha3.
 *
 * Revision 2.1  1995/12/11  07:53:59  pavel
 * Accounted for verb programs never being NULL any more.
 *
 * Release 1.8.0alpha2.
 *
 * Revision 2.0  1995/11/30  04:43:36  pavel
 * New baseline version, corresponding to release 1.8.0alpha1.
 *
 * Revision 1.16  1992/10/23  23:03:47  pavel
 * Added copyright notice.
 *
 * Revision 1.15  1992/10/23  22:23:43  pavel
 * Eliminated all uses of the useless macro NULL.
 *
 * Revision 1.14  1992/10/21  03:02:35  pavel
 * Converted to use new automatic configuration system.
 *
 * Revision 1.13  1992/10/17  20:58:25  pavel
 * Global rename of strdup->str_dup, strref->str_ref, vardup->var_dup, and
 * varref->var_ref.
 *
 * Revision 1.12  1992/10/06  18:25:57  pavel
 * Changed name of global Parser_Client to avoid a name clash.
 *
 * Revision 1.11  1992/09/24  16:44:38  pavel
 * Made the parsing done by eval() and set_verb_code() abort if the task runs
 * out of seconds.
 *
 * Revision 1.10  1992/09/21  17:38:05  pavel
 * Restored RCS log information.
 *
 * Revision 1.9  1992/09/14  18:41:15  pjames
 * Moved rcsid to bottom.
 * Changed bf_eval to avoid a compiler warning when compiled un-optimized.
 *
 * Revision 1.8  1992/09/14  17:31:23  pjames
 * Moved db_modification code to db modules.
 *
 * Revision 1.7  1992/09/08  22:00:18  pjames
 * Renambed bf_verb.c to verbs.c
 *
 * Revision 1.6  1992/08/31  22:29:24  pjames
 * Changed some `char *'s to `const char *'
 *
 * Revision 1.5  1992/08/28  16:16:14  pjames
 * Changed myfree(*, M_STRING) to free_str(*).
 * Changed some strref's to strdup.
 *
 * Revision 1.4  1992/08/21  00:42:59  pavel
 * Renamed include file "parse_command.h" to "parse_cmd.h".
 *
 * Revision 1.3  1992/08/10  17:21:32  pjames
 * Updated #includes.  Updated to use new registration format.  Built in
 * functions now only receive programmer, instead of entire Parse_Info.
 *
 * Revision 1.2  1992/07/20  23:55:24  pavel
 * Added rcsid_<filename-root> declaration to hold the RCS ident. string.
 *
 * Revision 1.1  1992/07/20  23:23:12  pavel
 * Initial RCS-controlled version.
 */
