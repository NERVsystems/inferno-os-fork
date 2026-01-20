/*
 * ACSL Specifications for Reference Counting
 *
 * Defines formal contracts for incref/decref operations.
 */

#ifndef REFCOUNT_ACSL_H
#define REFCOUNT_ACSL_H

#include <limits.h>

typedef struct Lock {
    int dummy;
} Lock;

typedef struct Ref {
    int ref;
    Lock lk;
} Ref;

/*@
  predicate valid_refcount(Ref *r) =
      \valid(r) && r->ref >= 0 && r->ref < INT_MAX;
*/

/*@
  requires valid_refcount(r);
  requires r->ref < INT_MAX;

  ensures r->ref == \old(r->ref) + 1;
  ensures \result == r->ref;
  ensures \result > 0;
  ensures \result <= INT_MAX;

  assigns r->ref;
*/
int incref(Ref *r);

/*@
  requires valid_refcount(r);
  requires r->ref > 0;

  ensures r->ref == \old(r->ref) - 1;
  ensures \result == r->ref;
  ensures \result >= 0;

  assigns r->ref;
*/
int decref(Ref *r);

/*@
  axiomatic Refcount {
    // Refcount never goes negative
    axiom refcount_non_negative:
        \forall Ref *r; valid_refcount(r) ==> r->ref >= 0;

    // Incref increases refcount by exactly 1
    axiom incref_increments:
        \forall Ref *r; valid_refcount(r) && r->ref < INT_MAX ==>
            incref(r) == \old(r->ref) + 1;

    // Decref decreases refcount by exactly 1
    axiom decref_decrements:
        \forall Ref *r; valid_refcount(r) && r->ref > 0 ==>
            decref(r) == \old(r->ref) - 1;

    // Refcount of 0 means object should be freed
    predicate should_be_freed(Ref *r) = r->ref == 0;
  }
*/

#endif /* REFCOUNT_ACSL_H */
