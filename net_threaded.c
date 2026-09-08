/******************************************************************************
  Copyright (c) 1992, 1995, 1996 Xerox Corporation.  All rights reserved.
  Portions of this code were written by Stephen White, aka ghond.
  Use and copying of this software and preparation of derivative works based
  upon this software are permitted.  Any distribution of this software or
  derivative works must comply with all applicable United States export
  control laws.  This software is made available AS IS, and Xerox Corporation
  makes no warranty about the software, its performance or its conformity to
  any specification.
 *****************************************************************************/

/* Multi-user networking with descriptor I/O isolated in one pthread. */

#include "net_multi.h"

#include "config.h"
#include "options.h"

#include <errno.h>
#include "my-ctype.h"
#include "my-fcntl.h"
#include "my-ioctl.h"
#include "my-signal.h"
#include "my-stdio.h"
#include "my-stdlib.h"
#include "my-string.h"
#include "my-time.h"
#include "my-unistd.h"
#include <pthread.h>
#include <stdatomic.h>

#include "exceptions.h"
#include "list.h"
#include "log.h"
#include "net_mplex.h"
#include "net_proto.h"
#include "network.h"
#include "server.h"
#include "streams.h"
#include "structures.h"
#include "storage.h"
#include "utf.h"
#include "utf-ctype.h"
#include "utils.h"

static struct proto proto;
static int eol_length;

/* These are batching and initial-capacity choices, not queue limits.  The
 * configured MAX_QUEUED_* values remain the actual per-connection limits.
 */
#define INPUT_READ_CHUNK_SIZE		4096 /* bounds each worker allocation */
#define WAKE_DRAIN_CHUNK_SIZE		64   /* amortizes wake-pipe reads */
#define IO_WAIT_TIMEOUT			60   /* periodic lost-wakeup safeguard */
#define INITIAL_INPUT_STREAM_SIZE	100  /* retained from net_multi.c */
#define INITIAL_REGISTERED_FDS		5    /* retained from net_multi.c */
#define REGISTERED_FD_GROWTH_FACTOR	2

/* RFC 3629 UTF-8 encodes a Unicode scalar value in at most four bytes. */
#define UTF8_MAX_CHARACTER_BYTES	4

#if NETWORK_PROTOCOL == NP_TCP
#  define TELNET_COMMAND_LENGTH	3
#  define TELNET_IAC		255
#  define TELNET_WILL		251
#  define TELNET_WONT		252
#  define TELNET_ECHO		1
#endif

#ifdef EAGAIN
static int eagain = EAGAIN;
#else
static int eagain = -1;
#endif

#ifdef EWOULDBLOCK
static int ewouldblock = EWOULDBLOCK;
#else
static int ewouldblock = -1;
#endif

typedef struct byte_block {
    struct byte_block *next;
    size_t length;
    size_t offset;
    char data[];
} byte_block;

typedef enum {
    LISTENER_NOT_READY, LISTENER_READY, LISTENER_PROCESSING
} listener_readiness;

typedef struct nhandle {
    struct nhandle *next, **prev;
    server_handle shandle;
    int rfd, wfd;
    const char *name;
    Stream *input;
    int last_input_was_CR;
    int input_suspended;
    byte_block *input_head;
    byte_block **input_tail;
    size_t input_length;
    byte_block *output_head;
    byte_block **output_tail;
    size_t output_length;
    int output_lines_flushed;
    char *overflow_notice;
    size_t overflow_notice_length, overflow_notice_offset;
    int outbound, binary;
    int closing, closed, notify_close;
    char excess_utf[UTF8_MAX_CHARACTER_BYTES - 1];
    size_t excess_utf_count;
#if NETWORK_PROTOCOL == NP_TCP
    int client_echo;
#endif
} nhandle;

typedef struct nlistener {
    struct nlistener *next, **prev;
    server_listener slistener;
    int fd;
    const char *name;
    int active, closing, closed;
    listener_readiness ready;
} nlistener;

typedef struct {
    int fd;
    network_fd_callback readable;
    network_fd_callback writable;
    void *data;
    int read_ready, write_ready;
} fd_reg;

static nhandle *all_nhandles = NULL;
static nlistener *all_nlisteners = NULL;
static fd_reg *reg_fds = NULL;
static int max_reg_fds;
static int *pocket_descriptors = NULL;

static pthread_t io_thread;
static pthread_mutex_t io_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t event_cond = PTHREAD_COND_INITIALIZER;
static atomic_int work_pending = ATOMIC_VAR_INIT(0);
typedef enum {
    WAKE_READ, WAKE_WRITE, WAKE_ENDS
} wake_pipe_end;

static int wake_pipe[WAKE_ENDS] = {-1, -1};
static int io_started, io_stopping;

static byte_block *
new_byte_block(const char *data, size_t length)
{
    byte_block *b = mymalloc(sizeof(byte_block) + length, M_NETWORK);

    if (!b)
	return NULL;
    b->next = NULL;
    b->length = length;
    b->offset = 0;
    if (data && length)
	memcpy(b->data, data, length);
    return b;
}

static void
free_blocks(byte_block *b)
{
    while (b) {
	byte_block *next = b->next;
	myfree(b, M_NETWORK);
	b = next;
    }
}

static void
signal_execution_thread(void)
{
    atomic_store_explicit(&work_pending, 1, memory_order_release);
    pthread_cond_signal(&event_cond);
}

static ssize_t
read_uninterrupted(int fd, void *buffer, size_t length)
{
    ssize_t count;

    do
	count = read(fd, buffer, length);
    while (count < 0 && errno == EINTR);
    return count;
}

static ssize_t
write_uninterrupted(int fd, const void *buffer, size_t length)
{
    ssize_t count;

    do
	count = write(fd, buffer, length);
    while (count < 0 && errno == EINTR);
    return count;
}

static void
wake_io_thread(void)
{
    char c = 0;

    if (wake_pipe[WAKE_WRITE] >= 0)
	(void) write_uninterrupted(wake_pipe[WAKE_WRITE], &c, sizeof(c));
}

static int
set_nonblocking(int fd)
{
#ifdef FIONBIO
    int yes = 1;

    return ioctl(fd, FIONBIO, &yes) >= 0;
#else
    int flags = fcntl(fd, F_GETFL, 0);

    return flags >= 0 && fcntl(fd, F_SETFL, flags | NONBLOCK_FLAG) >= 0;
#endif
}

int
network_set_nonblocking(int fd)
{
    return set_nonblocking(fd);
}

static int
worker_push_output(nhandle *h)
{
    if (!h->overflow_notice && h->output_lines_flushed > 0) {
	static const char format[] =
	    "%s>> Network buffer overflow: %u line%s of output to you "
	    "%s been lost <<%s";
	unsigned lines = h->output_lines_flushed;
	int length = snprintf(NULL, 0, format, proto.eol_out_string, lines,
			      lines == 1 ? "" : "s",
			      lines == 1 ? "has" : "have",
			      proto.eol_out_string);

	if (length < 0
	    || !(h->overflow_notice = mymalloc((size_t)length + 1,
					 M_NETWORK)))
	    return 0;
	(void) snprintf(h->overflow_notice, (size_t)length + 1, format,
			proto.eol_out_string, lines, lines == 1 ? "" : "s",
			lines == 1 ? "has" : "have", proto.eol_out_string);
	h->overflow_notice_length = length;
	h->overflow_notice_offset = 0;
	h->output_lines_flushed = 0;
    }
    while (h->overflow_notice) {
	ssize_t count = write_uninterrupted(
	    h->wfd, h->overflow_notice + h->overflow_notice_offset,
	    h->overflow_notice_length - h->overflow_notice_offset);

	if (count < 0)
	    return errno == eagain || errno == ewouldblock;
	if (count == 0)
	    return 1;
	h->overflow_notice_offset += count;
	if (h->overflow_notice_offset == h->overflow_notice_length) {
	    myfree(h->overflow_notice, M_NETWORK);
	    h->overflow_notice = NULL;
	    h->overflow_notice_length = h->overflow_notice_offset = 0;
	}
    }
    while (h->output_head) {
	byte_block *b = h->output_head;
	ssize_t count = write_uninterrupted(h->wfd, b->data + b->offset,
				    b->length - b->offset);

	if (count < 0)
	    return errno == eagain || errno == ewouldblock;
	if (count == 0)
	    return 1;
	b->offset += count;
	h->output_length -= count;
	if (b->offset == b->length) {
	    h->output_head = b->next;
	    myfree(b, M_NETWORK);
	}
    }
    h->output_tail = &h->output_head;
    return 1;
}

static int
worker_pull_input(nhandle *h)
{
    char buffer[INPUT_READ_CHUNK_SIZE];
    size_t room = MAX_QUEUED_INPUT > h->input_length
	? MAX_QUEUED_INPUT - h->input_length : 0;
    ssize_t count;
    byte_block *b;

    if (!room)
	return 1;
    if (room > sizeof(buffer))
	room = sizeof(buffer);
    count = read_uninterrupted(h->rfd, buffer, room);
    if (count > 0) {
	b = new_byte_block(buffer, count);
	if (!b)
	    return 0;
	*h->input_tail = b;
	h->input_tail = &b->next;
	h->input_length += count;
	signal_execution_thread();
	return 1;
    }
    return (count == 0 && !proto.believe_eof)
	|| (count < 0 && (errno == eagain || errno == ewouldblock));
}

static void
drain_wake_pipe(void)
{
    char buffer[WAKE_DRAIN_CHUNK_SIZE];

    while (read_uninterrupted(wake_pipe[WAKE_READ], buffer,
			      sizeof(buffer)) > 0)
	;
}

static void
worker_close_handle(nhandle *h)
{
    if (!h->closed) {
	(void) worker_push_output(h);
	proto_close_connection(h->rfd, h->wfd);
	h->closed = 1;
	signal_execution_thread();
    }
}

static void *
network_io_main(void *unused UNUSED_)
{
    for (;;) {
	nhandle *h;
	nlistener *l;
	fd_reg *reg;

	pthread_mutex_lock(&io_mutex);
	if (io_stopping) {
	    pthread_mutex_unlock(&io_mutex);
	    break;
	}
	mplex_clear();
	mplex_add_reader(wake_pipe[WAKE_READ]);
	for (l = all_nlisteners; l; l = l->next)
	    if (l->active && !l->closing && !l->ready)
		mplex_add_reader(l->fd);
	for (h = all_nhandles; h; h = h->next) {
	    if (!h->closing && !h->closed && !h->input_suspended
		&& h->input_length < MAX_QUEUED_INPUT)
		mplex_add_reader(h->rfd);
	    if (!h->closed && h->output_head)
		mplex_add_writer(h->wfd);
	}
	for (reg = reg_fds; reg < reg_fds + max_reg_fds; reg++)
	    if (reg->fd >= 0) {
		if (reg->readable && !reg->read_ready)
		    mplex_add_reader(reg->fd);
		if (reg->writable && !reg->write_ready)
		    mplex_add_writer(reg->fd);
	    }
	pthread_mutex_unlock(&io_mutex);

	errno = 0;
	if (mplex_wait(IO_WAIT_TIMEOUT) && errno != 0)
	    continue;  /* Rebuild readiness sets after EINTR or another error. */

	pthread_mutex_lock(&io_mutex);
	if (mplex_is_readable(wake_pipe[WAKE_READ]))
	    drain_wake_pipe();
	for (l = all_nlisteners; l; l = l->next) {
	    if (l->closing) {
		if (!l->closed) {
		    proto_close_listener(l->fd);
		    l->closed = 1;
		    signal_execution_thread();
		}
	    } else if (!l->ready && mplex_is_readable(l->fd)) {
		l->ready = LISTENER_READY;
		signal_execution_thread();
	    }
	}
	for (h = all_nhandles; h; h = h->next) {
	    if (h->closing) {
		worker_close_handle(h);
		continue;
	    }
	    if (h->closed)
		continue;
	    if ((!h->input_suspended && mplex_is_readable(h->rfd)
		 && !worker_pull_input(h))
		|| (h->output_head && mplex_is_writable(h->wfd)
		    && !worker_push_output(h))) {
		h->notify_close = 1;
		h->closing = 1;
		worker_close_handle(h);
	    }
	}
	for (reg = reg_fds; reg < reg_fds + max_reg_fds; reg++)
	    if (reg->fd >= 0) {
		if (reg->readable && !reg->read_ready
		    && mplex_is_readable(reg->fd))
		    reg->read_ready = 1;
		if (reg->writable && !reg->write_ready
		    && mplex_is_writable(reg->fd))
		    reg->write_ready = 1;
		if (reg->read_ready || reg->write_ready)
		    signal_execution_thread();
	    }
	pthread_mutex_unlock(&io_mutex);
    }
    return NULL;
}

static int
start_io_thread(void)
{
    if (io_started)
	return 1;
    if (pipe(wake_pipe) < 0 || !set_nonblocking(wake_pipe[WAKE_READ])
	|| !set_nonblocking(wake_pipe[WAKE_WRITE])) {
	log_perror("Creating network wake pipe");
	return 0;
    }
    if (pthread_create(&io_thread, NULL, network_io_main, NULL) != 0) {
	errlog("Creating network I/O thread failed\n");
	close(wake_pipe[WAKE_READ]);
	close(wake_pipe[WAKE_WRITE]);
	wake_pipe[WAKE_READ] = wake_pipe[WAKE_WRITE] = -1;
	return 0;
    }
    io_started = 1;
    return 1;
}

static nhandle *
new_nhandle(int rfd, int wfd, const char *local_name, const char *remote_name,
	    int outbound)
{
    nhandle *h = mymalloc(sizeof(nhandle), M_NETWORK);
    Stream *s;

    if (!set_nonblocking(rfd) || (rfd != wfd && !set_nonblocking(wfd)))
	log_perror("Setting connection non-blocking");
    *h = (nhandle){0};
    h->rfd = rfd;
    h->wfd = wfd;
    h->input = new_stream(INITIAL_INPUT_STREAM_SIZE);
    h->input_tail = &h->input_head;
    h->output_tail = &h->output_head;
    h->outbound = outbound;
#if NETWORK_PROTOCOL == NP_TCP
    h->client_echo = 1;
#endif
    s = new_stream(0);
    stream_printf(s, "%s %s %s", local_name, outbound ? "to" : "from",
		  remote_name);
    h->name = str_dup_then_free_stream(s);

    pthread_mutex_lock(&io_mutex);
    if (all_nhandles)
	all_nhandles->prev = &h->next;
    h->next = all_nhandles;
    h->prev = &all_nhandles;
    all_nhandles = h;
    pthread_mutex_unlock(&io_mutex);
    return h;
}

static void
free_nhandle(nhandle *h)
{
    *h->prev = h->next;
    if (h->next)
	h->next->prev = h->prev;
    free_blocks(h->input_head);
    free_blocks(h->output_head);
    if (h->overflow_notice)
	myfree(h->overflow_notice, M_NETWORK);
    free_stream(h->input);
    free_str(h->name);
    myfree(h, M_NETWORK);
}

static void
make_new_connection(server_listener sl, int rfd, int wfd,
		    const char *local_name, const char *remote_name,
		    int outbound)
{
    network_handle nh;
    nhandle *h;

    nh.ptr = h = new_nhandle(rfd, wfd, local_name, remote_name, outbound);
    h->shandle = server_new_connection(sl, nh, outbound);
    wake_io_thread();
}

static void
get_pocket_descriptors(void)
{
    unsigned i;

    if (!pocket_descriptors)
	pocket_descriptors = mymalloc(proto.pocket_size * sizeof(int), M_NETWORK);
    for (i = 0; i < proto.pocket_size; i++) {
	pocket_descriptors[i] = dup(0);
	if (pocket_descriptors[i] < 0)
	    panic("Can't get pocket descriptors");
    }
}

static void
accept_new_connection(nlistener *l)
{
    int rfd, wfd;
    unsigned i;
    const char *host_name;

    switch (proto_accept_connection(l->fd, l->slistener,
				    &rfd, &wfd, &host_name)) {
    case PA_OKAY:
	make_new_connection(l->slistener, rfd, wfd, l->name, host_name, 0);
	break;
    case PA_FULL:
	for (i = 0; i < proto.pocket_size; i++)
	    close(pocket_descriptors[i]);
	if (proto_accept_connection(l->fd, l->slistener,
				    &rfd, &wfd, &host_name) == PA_OKAY) {
	    network_handle nh;
	    nhandle *h;

	    nh.ptr = h = new_nhandle(rfd, wfd, l->name, host_name, 0);
	    server_refuse_connection(l->slistener, nh);
	    pthread_mutex_lock(&io_mutex);
	    h->closing = 1;
	    pthread_mutex_unlock(&io_mutex);
	    wake_io_thread();
	}
	get_pocket_descriptors();
	break;
    case PA_OTHER:
	break;
    }
}

static void
consume_input(nhandle *h, byte_block *blocks)
{
    byte_block *b;

    for (b = blocks; b; b = b->next) {
	char buffer[INPUT_READ_CHUNK_SIZE + UTF8_MAX_CHARACTER_BYTES - 1];
	char *ptr, *end;
	size_t count = b->length - b->offset;

	memcpy(buffer, h->excess_utf, h->excess_utf_count);
	memcpy(buffer + h->excess_utf_count, b->data + b->offset, count);
	count += h->excess_utf_count;
	if (h->binary) {
	    stream_add_moobinary_from_raw_bytes(h->input, buffer, count);
	    server_receive_line(h->shandle, reset_stream(h->input));
	    h->last_input_was_CR = 0;
	    h->excess_utf_count = 0;
	    continue;
	}
	for (ptr = buffer, end = buffer + count;
	     ptr < end && ptr + clearance_utf(*ptr) <= end;) {
	    int c = get_utf((const char **)&ptr);

	    if (my_is_printable(c))
		stream_add_utf(h->input, c);
#ifdef INPUT_APPLY_BACKSPACE
	    else if (c == 0x08 || c == 0x7f)
		stream_delete_utf(h->input);
#endif
	    else if (c == '\r' || (c == '\n' && !h->last_input_was_CR))
		server_receive_line(h->shandle, reset_stream(h->input));
	    h->last_input_was_CR = c == '\r';
	}
	if (ptr < end)
	    memcpy(h->excess_utf, ptr, end - ptr);
	h->excess_utf_count = end - ptr;
    }
    free_blocks(blocks);
}

static int
enqueue_output(network_handle nh, const char *line, size_t line_length,
	       int add_eol, int flush_ok)
{
    nhandle *h = nh.ptr;
    size_t length = line_length + (add_eol ? eol_length : 0);
    byte_block *b;

    pthread_mutex_lock(&io_mutex);
    if (h->closing || h->closed) {
	pthread_mutex_unlock(&io_mutex);
	return 0;
    }
    while (h->output_length && h->output_length + length > MAX_QUEUED_OUTPUT) {
	byte_block *old;

	if (!flush_ok) {
	    pthread_mutex_unlock(&io_mutex);
	    return 0;
	}
	old = h->output_head;
	if (!old)
	    break;
	h->output_head = old->next;
	h->output_length -= old->length - old->offset;
	h->output_lines_flushed++;
	myfree(old, M_NETWORK);
    }
    b = new_byte_block(NULL, length);
    if (!b) {
	pthread_mutex_unlock(&io_mutex);
	return 0;
    }
    memcpy(b->data, line, line_length);
    if (add_eol)
	memcpy(b->data + line_length, proto.eol_out_string, eol_length);
    *h->output_tail = b;
    h->output_tail = &b->next;
    h->output_length += length;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
    return 1;
}

const char *
network_protocol_name(void)
{
    return proto_name();
}

const char *
network_usage_string(void)
{
    return proto_usage_string();
}

int
network_initialize(int argc, char **argv, Var *desc)
{
    if (!proto_initialize(&proto, desc, argc, argv))
	return 0;
    eol_length = strlen(proto.eol_out_string);
    get_pocket_descriptors();
    signal(SIGPIPE, SIG_IGN);
    return start_io_thread();
}

enum error
network_make_listener(server_listener sl, Var desc, network_listener *nl,
		      Var *canon, const char **name)
{
    int fd;
    enum error e = proto_make_listener(desc, &fd, canon, name);
    nlistener *l;

    if (e != E_NONE)
	return e;
    l = mymalloc(sizeof(nlistener), M_NETWORK);
    *l = (nlistener){0};
    l->fd = fd;
    l->slistener = sl;
    l->name = str_dup(*name);
    pthread_mutex_lock(&io_mutex);
    if (all_nlisteners)
	all_nlisteners->prev = &l->next;
    l->next = all_nlisteners;
    l->prev = &all_nlisteners;
    all_nlisteners = l;
    pthread_mutex_unlock(&io_mutex);
    nl->ptr = l;
    wake_io_thread();
    return E_NONE;
}

int
network_listen(network_listener nl)
{
    nlistener *l = nl.ptr;
    int result = proto_listen(l->fd);

    if (result) {
	pthread_mutex_lock(&io_mutex);
	l->active = 1;
	pthread_mutex_unlock(&io_mutex);
    }
    wake_io_thread();
    return result;
}

int
network_send_line(network_handle nh, const char *line, int flush_ok)
{
    return enqueue_output(nh, line, strlen(line), 1, flush_ok);
}

int
network_send_bytes(network_handle nh, const char *buffer, size_t buflen,
		   int flush_ok)
{
    return enqueue_output(nh, buffer, buflen, 0, flush_ok);
}

int
network_buffered_output_length(network_handle nh)
{
    nhandle *h = nh.ptr;
    int length;

    pthread_mutex_lock(&io_mutex);
    length = h->output_length;
    pthread_mutex_unlock(&io_mutex);
    return length;
}

void
network_suspend_input(network_handle nh)
{
    pthread_mutex_lock(&io_mutex);
    ((nhandle *)nh.ptr)->input_suspended = 1;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
}

void
network_resume_input(network_handle nh)
{
    pthread_mutex_lock(&io_mutex);
    ((nhandle *)nh.ptr)->input_suspended = 0;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
}

int
network_work_pending(void)
{
    return atomic_load_explicit(&work_pending, memory_order_acquire);
}

static int
events_remain(void)
{
    nhandle *h;
    nlistener *l;
    fd_reg *reg;

    for (l = all_nlisteners; l; l = l->next)
	if (l->ready || l->closed)
	    return 1;
    for (h = all_nhandles; h; h = h->next)
	if (h->input_head || h->closed)
	    return 1;
    for (reg = reg_fds; reg < reg_fds + max_reg_fds; reg++)
	if (reg->fd >= 0 && (reg->read_ready || reg->write_ready))
	    return 1;
    return 0;
}

int
network_process_io(int timeout)
{
    int did_io = 0;

    pthread_mutex_lock(&io_mutex);
    if (timeout && !events_remain()) {
	struct timespec until;

	until.tv_sec = time(0) + timeout;
	until.tv_nsec = 0;
	(void) pthread_cond_timedwait(&event_cond, &io_mutex, &until);
    }
    pthread_mutex_unlock(&io_mutex);

    for (;;) {
	nlistener *l = NULL;
	nhandle *h = NULL;
	byte_block *input = NULL;
	server_handle close_sh = {NULL};
	int notify_close = 0;
	int i;

	pthread_mutex_lock(&io_mutex);
	for (l = all_nlisteners; l && !l->ready && !l->closed; l = l->next)
	    ;
	if (l && l->ready)
	    l->ready = LISTENER_PROCESSING;
	else if (l && l->closed) {
	    *l->prev = l->next;
	    if (l->next)
		l->next->prev = l->prev;
	    free_str(l->name);
	    myfree(l, M_NETWORK);
	    l = NULL;
	    did_io = 1;
	}
	else {
	    for (h = all_nhandles; h && !h->input_head && !h->closed;
		 h = h->next)
		;
	    if (h && h->input_head) {
		input = h->input_head;
		h->input_head = NULL;
		h->input_tail = &h->input_head;
		h->input_length = 0;
	    } else if (h && h->closed) {
		close_sh = h->shandle;
		notify_close = h->notify_close;
		free_nhandle(h);
	    } else
		h = NULL;
	}
	if (!l && !h) {
	    for (i = 0; i < max_reg_fds; i++) {
		fd_reg *reg = &reg_fds[i];
		network_fd_callback readable, writable;
		void *data;
		int fd;

		if (reg->fd < 0 || (!reg->read_ready && !reg->write_ready))
		    continue;
		fd = reg->fd;
		readable = reg->read_ready ? reg->readable : NULL;
		writable = reg->write_ready ? reg->writable : NULL;
		data = reg->data;
		pthread_mutex_unlock(&io_mutex);
		if (readable)
		    readable(fd, data);
		if (writable)
		    writable(fd, data);
		pthread_mutex_lock(&io_mutex);
		if (i < max_reg_fds && reg_fds[i].fd == fd)
		    reg_fds[i].read_ready = reg_fds[i].write_ready = 0;
		did_io = 1;
		break;
	    }
	}
	if (!events_remain())
	    atomic_store_explicit(&work_pending, 0, memory_order_release);
	pthread_mutex_unlock(&io_mutex);

	if (l) {
	    if (l->ready == LISTENER_PROCESSING) {
		accept_new_connection(l);
		pthread_mutex_lock(&io_mutex);
		l->ready = LISTENER_NOT_READY;
		pthread_mutex_unlock(&io_mutex);
	    }
	    did_io = 1;
	    wake_io_thread();
	} else if (h) {
	    if (input)
		consume_input(h, input);
	    else if (notify_close)
		server_close(close_sh);
	    did_io = 1;
	    wake_io_thread();
	} else {
	    pthread_mutex_lock(&io_mutex);
	    if (!events_remain()) {
		pthread_mutex_unlock(&io_mutex);
		break;
	    }
	    pthread_mutex_unlock(&io_mutex);
	}
    }
    return did_io;
}

const char *
network_connection_name(network_handle nh)
{
    return ((nhandle *)nh.ptr)->name;
}

void
network_set_connection_binary(network_handle nh, int do_binary)
{
    ((nhandle *)nh.ptr)->binary = do_binary;
}

#if NETWORK_PROTOCOL == NP_LOCAL
#  define NETWORK_CO_TABLE(DEFINE, nh, value, _)
#elif NETWORK_PROTOCOL == NP_TCP
#  define NETWORK_CO_TABLE(DEFINE, nh, value, _)                     \
    DEFINE(client-echo, _, TYPE_INT, num,                             \
	   ((nhandle *)nh.ptr)->client_echo,                           \
	   network_set_client_echo(nh, is_true(value));)

void
network_set_client_echo(network_handle nh, int is_on)
{
    nhandle *h = nh.ptr;
    static unsigned char telnet_cmd[TELNET_COMMAND_LENGTH]
	= {TELNET_IAC, 0, TELNET_ECHO};

    h->client_echo = is_on;
    telnet_cmd[1] = is_on ? TELNET_WONT : TELNET_WILL;
    enqueue_output(nh, (char *)telnet_cmd, sizeof(telnet_cmd), 0, 1);
}
#else
#  error "NP_SINGLE cannot use threaded networking"
#endif

#ifdef OUTBOUND_NETWORK
enum error
network_open_connection(Var arglist, server_listener sl)
{
    int rfd, wfd;
    const char *local_name, *remote_name;
    enum error e;

    if (!proto.can_connect_outbound)
	return E_PERM;
    e = proto_open_connection(arglist, sl, &rfd, &wfd,
			      &local_name, &remote_name);
    if (e == E_NONE)
	make_new_connection(sl, rfd, wfd, local_name, remote_name, 1);
    return e;
}
#endif

void
network_close(network_handle nh)
{
    nhandle *h = nh.ptr;

    pthread_mutex_lock(&io_mutex);
    h->closing = 1;
    h->notify_close = 0;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
}

void
network_close_listener(network_listener nl)
{
    nlistener *l = nl.ptr;

    pthread_mutex_lock(&io_mutex);
    l->closing = 1;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
}

void
network_register_fd(int fd, network_fd_callback readable,
		    network_fd_callback writable, void *data)
{
    int i;

    pthread_mutex_lock(&io_mutex);
    for (i = 0; i < max_reg_fds && reg_fds[i].fd >= 0; i++)
	;
    if (i == max_reg_fds) {
	int old_max = max_reg_fds;
	int new_max = old_max
	    ? old_max * REGISTERED_FD_GROWTH_FACTOR
	    : INITIAL_REGISTERED_FDS;
	fd_reg *new_regs = reg_fds
	    ? myrealloc(reg_fds, new_max * sizeof(fd_reg), M_NETWORK)
	    : mymalloc(new_max * sizeof(fd_reg), M_NETWORK);

	if (!new_regs) {
	    pthread_mutex_unlock(&io_mutex);
	    panic("Cannot allocate registered descriptor table");
	}
	reg_fds = new_regs;
	max_reg_fds = new_max;
	for (i = old_max; i < new_max; i++)
	    reg_fds[i].fd = -1;
	i = old_max;
    }
    reg_fds[i].fd = fd;
    reg_fds[i].readable = readable;
    reg_fds[i].writable = writable;
    reg_fds[i].data = data;
    reg_fds[i].read_ready = reg_fds[i].write_ready = 0;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
}

void
network_unregister_fd(int fd)
{
    int i;

    pthread_mutex_lock(&io_mutex);
    for (i = 0; i < max_reg_fds; i++)
	if (reg_fds[i].fd == fd)
	    reg_fds[i].fd = -1;
    pthread_mutex_unlock(&io_mutex);
    wake_io_thread();
}

void
network_shutdown(void)
{
    nhandle *h;
    nlistener *l;

    if (io_started) {
	pthread_mutex_lock(&io_mutex);
	for (h = all_nhandles; h; h = h->next)
	    h->closing = 1;
	for (l = all_nlisteners; l; l = l->next)
	    l->closing = 1;
	io_stopping = 1;
	pthread_mutex_unlock(&io_mutex);
	wake_io_thread();
	pthread_join(io_thread, NULL);
	io_started = 0;
    }
    pthread_mutex_lock(&io_mutex);
    while ((h = all_nhandles)) {
	if (!h->closed)
	    worker_close_handle(h);
	free_nhandle(h);
    }
    while ((l = all_nlisteners)) {
	*l->prev = l->next;
	if (l->next)
	    l->next->prev = l->prev;
	if (!l->closed)
	    proto_close_listener(l->fd);
	free_str(l->name);
	myfree(l, M_NETWORK);
    }
    pthread_mutex_unlock(&io_mutex);
    if (wake_pipe[WAKE_READ] >= 0)
	close(wake_pipe[WAKE_READ]);
    if (wake_pipe[WAKE_WRITE] >= 0)
	close(wake_pipe[WAKE_WRITE]);
    wake_pipe[WAKE_READ] = wake_pipe[WAKE_WRITE] = -1;
    if (reg_fds)
	myfree(reg_fds, M_NETWORK);
    reg_fds = NULL;
    max_reg_fds = 0;
}
