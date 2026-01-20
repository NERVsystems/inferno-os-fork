/*
 * CBMC Stubs for Inferno Kernel Functions
 *
 * These stubs replace external functions that CBMC cannot analyze directly.
 * They model the essential behavior while remaining verification-friendly.
 */

#include <stddef.h>
#include <limits.h>

/* Type definitions (simplified) */
typedef struct Lock {
    int dummy; /* Simplified lock for verification */
} Lock;

typedef struct Ref {
    int ref;
    Lock lk;
} Ref;

/* Memory allocation stubs */
void* malloc(size_t size) {
    void *ptr;

    if(size == 0)
        return NULL;

    /* For verification, assume malloc always succeeds for reasonable sizes.
     * In the actual code, malloc failure calls error() which never returns. */
    __CPROVER_assume(size < 1024*1024); /* Reasonable size bound */
    __CPROVER_assume(ptr != NULL); /* Always succeeds */

    return ptr;
}

void free(void *ptr) {
    /* No-op for verification - CBMC tracks allocation */
    (void)ptr;
}

/* Error handling stubs */
#define Enomem "out of memory"

void error(char *msg) {
    __CPROVER_assume(0); /* Never returns - marks path as infeasible */
}

void nexterror(void) {
    __CPROVER_assume(0); /* Never returns */
}

int waserror(void) {
    int nondet;
    /* Non-deterministically return 0 or 1 to model exception paths */
    __CPROVER_assume(nondet == 0 || nondet == 1);
    return nondet;
}

void poperror(void) {
    /* No-op for verification */
}

/* Reference counting stubs with assertions */
int incref(Ref *r) {
    __CPROVER_assert(r != NULL, "incref: non-null reference");
    __CPROVER_assert(r->ref >= 0, "incref: refcount non-negative");
    __CPROVER_assert(r->ref < INT_MAX, "incref: no overflow");

    r->ref++;
    return r->ref;
}

int decref(Ref *r) {
    __CPROVER_assert(r != NULL, "decref: non-null reference");
    __CPROVER_assert(r->ref > 0, "decref: refcount positive before decrement");

    r->ref--;
    return r->ref;
}

/* Lock stubs (no-op for single-threaded verification) */
void lock(Lock *l) {
    (void)l;
}

void unlock(Lock *l) {
    (void)l;
}

void wlock(void *rw) {
    (void)rw;
}

void wunlock(void *rw) {
    (void)rw;
}

void rlock(void *rw) {
    (void)rw;
}

void runlock(void *rw) {
    (void)rw;
}

/* String operations */
void kstrdup(char **dst, char *src) {
    if(src == NULL) {
        *dst = NULL;
        return;
    }

    /* Allocate symbolic string */
    *dst = (char*)malloc(256); /* Bounded string length */
    __CPROVER_assume(*dst != NULL);
}

/* Channel operations (simplified) */
typedef struct Chan Chan;

void cclose(Chan *c) {
    /* No-op - assume channel management is correct */
    (void)c;
}

Chan* cclone(Chan *c) {
    /* Return symbolic channel */
    Chan *nc;
    __CPROVER_assume(nc != NULL);
    return nc;
}

int eqchan(Chan *a, Chan *b, int flag) {
    /* Symbolic boolean result */
    int result;
    __CPROVER_assume(result == 0 || result == 1);
    return result;
}

/* Mount operations (forward declarations) */
typedef struct Mhead Mhead;
typedef struct Mount Mount;

Mhead* newmhead(Chan *c);
Mount* newmount(Mhead *mh, Chan *to, int flag, char *spec);
void mountfree(Mount *m);
void putmhead(Mhead *f);

/* Print stub */
void print(char *fmt, ...) {
    (void)fmt;
}
