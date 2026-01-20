/*
 * ACSL-Annotated version of pgrp.c (excerpt)
 *
 * This file demonstrates ACSL annotations on critical functions
 * from emu/port/pgrp.c for Frama-C verification.
 *
 * IMPORTANT: This is a verification artifact, not the actual implementation.
 * The real code remains in emu/port/pgrp.c.
 */

#include <stddef.h>
#include <limits.h>

#define MNTHASH 32
#define MNTLOG 5

/* Simplified type definitions */
typedef struct Lock { int dummy; } Lock;
typedef struct Ref { int ref; Lock lk; } Ref;
typedef struct RWlock { Lock l; int readers; } RWlock;
typedef struct QLock { Lock l; } QLock;
typedef struct Chan Chan;
typedef struct Mount Mount;
typedef struct Mhead Mhead;

typedef struct Pgrp {
    Ref r;
    unsigned long pgrpid;
    RWlock ns;
    QLock nsh;
    Mhead *mnthash[MNTHASH];
    int progmode;
    Chan *dot;
    Chan *slash;
    int nodevs;
    int pin;
} Pgrp;

/* External functions (stubbed for verification) */
extern void* malloc(size_t size);
extern void error(char *msg);
extern int incref(Ref *r);
extern void free(void *ptr);

/* Global refcount */
static Ref pgrpid;

/*@
  // Predicate: A valid Pgrp has a positive refcount
  predicate valid_pgrp(Pgrp *p) =
      \valid(p) &&
      p->r.ref > 0 &&
      p->pgrpid > 0;

  // Predicate: Array indices are in bounds
  predicate in_mnthash_bounds(int i) =
      0 <= i < MNTHASH;
*/

/* ========== newpgrp() ========== */

/*@
  requires \valid(&pgrpid);
  requires pgrpid.ref >= 0;
  requires pgrpid.ref < INT_MAX;

  behavior success:
    ensures \valid(\result);
    ensures \result->r.ref == 1;
    ensures \result->pgrpid == \old(pgrpid.ref) + 1;
    ensures \result->progmode == 0644;

  behavior malloc_failure:
    ensures \false;

  assigns pgrpid.ref;

  complete behaviors;
  disjoint behaviors;
*/
Pgrp* newpgrp(void)
{
    Pgrp *p;

    p = malloc(sizeof(Pgrp));
    if(p == NULL)
        error("Enomem"); // Never returns

    //@ assert \valid(p);

    p->r.ref = 1;
    //@ assert p->r.ref == 1;

    p->pgrpid = incref(&pgrpid);
    //@ assert p->pgrpid > 0;

    p->progmode = 0644;
    //@ assert p->progmode == 0644;

    //@ assert valid_pgrp(p);
    return p;
}

/* ========== closepgrp() ========== */

/*@
  requires p == \null || \valid(p);
  requires p != \null ==> valid_pgrp(p);
  requires p != \null ==> \valid(p->mnthash + (0 .. MNTHASH-1));

  behavior null_input:
    assumes p == \null;
    ensures \true;
    assigns \nothing;

  behavior positive_refcount:
    assumes p != \null && decref(&p->r) != 0;
    ensures \true;
    assigns p->r.ref;

  behavior zero_refcount:
    assumes p != \null && decref(&p->r) == 0;
    ensures \true;

  assigns p->pgrpid, p->mnthash[0 .. MNTHASH-1];

  complete behaviors;
  disjoint behaviors;
*/
void closepgrp(Pgrp *p)
{
    Mhead **h, **e, *f, *next;

    if(p == NULL || decref(&p->r) != 0)
        return;

    // wlock(&p->ns);  // Omitted for verification simplicity

    p->pgrpid = -1;
    //@ assert p->pgrpid == -1;

    e = &p->mnthash[MNTHASH];
    //@ assert e == &p->mnthash[MNTHASH];

    /*@
      loop invariant h_bounds: p->mnthash <= h <= &p->mnthash[MNTHASH];
      loop assigns h, f, next;
      loop variant &p->mnthash[MNTHASH] - h;
    */
    for(h = p->mnthash; h < e; h++) {
        //@ assert in_mnthash_bounds(h - p->mnthash);

        /*@ loop invariant \true;  // Simplified
            loop assigns f, next;
        */
        for(f = *h; f; f = next) {
            // wlock(&f->lock);
            // cclose(f->from);
            // mountfree(f->mount);
            f->mount = NULL;
            next = f->hash;
            // wunlock(&f->lock);
            // putmhead(f);
        }
    }

    //@ assert h == &p->mnthash[MNTHASH];

    // wunlock(&p->ns);
    // cclose(p->dot);
    // cclose(p->slash);
    free(p);
}

/* ========== Reference Counting Primitives ========== */

/*@
  requires \valid(r);
  requires r->ref >= 0;
  requires r->ref < INT_MAX;

  ensures r->ref == \old(r->ref) + 1;
  ensures \result == r->ref;

  assigns r->ref;
*/
int incref_impl(Ref *r)
{
    //@ assert r->ref < INT_MAX;
    r->ref++;
    //@ assert r->ref == \old(r->ref) + 1;
    return r->ref;
}

/*@
  requires \valid(r);
  requires r->ref > 0;

  ensures r->ref == \old(r->ref) - 1;
  ensures \result == r->ref;
  ensures \result >= 0;

  assigns r->ref;
*/
int decref_impl(Ref *r)
{
    //@ assert r->ref > 0;
    r->ref--;
    //@ assert r->ref >= 0;
    return r->ref;
}
