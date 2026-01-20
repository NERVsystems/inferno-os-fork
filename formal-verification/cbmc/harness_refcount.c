/*
 * CBMC Harness for Reference Counting Verification
 *
 * Verifies incref/decref operations don't overflow/underflow.
 */

#include <limits.h>
#include <stddef.h>

typedef struct Lock {
    int dummy;
} Lock;

typedef struct Ref {
    int ref;
    Lock lk;
} Ref;

/*
 * Model incref operation
 */
int incref_checked(Ref *r) {
    /* Preconditions */
    __CPROVER_assert(r != NULL, "incref: pointer non-NULL");
    __CPROVER_assert(r->ref >= 0, "incref: refcount non-negative before increment");
    __CPROVER_assert(r->ref < INT_MAX, "incref: no overflow on increment");

    r->ref++;

    /* Postconditions */
    __CPROVER_assert(r->ref > 0, "incref: refcount positive after increment");

    return r->ref;
}

/*
 * Model decref operation
 */
int decref_checked(Ref *r) {
    /* Preconditions */
    __CPROVER_assert(r != NULL, "decref: pointer non-NULL");
    __CPROVER_assert(r->ref > 0, "decref: refcount positive before decrement");

    r->ref--;

    /* Postconditions */
    __CPROVER_assert(r->ref >= 0, "decref: refcount non-negative after decrement");

    return r->ref;
}

/*
 * Test incref with various starting values
 */
void harness_incref(void) {
    Ref r;
    int initial_ref;

    /* Symbolic initial refcount */
    r.ref = initial_ref;

    /* Reasonable bounds on refcount */
    __CPROVER_assume(initial_ref >= 0);
    __CPROVER_assume(initial_ref < 1000000); /* Upper bound for verification */

    /* Perform incref */
    int new_ref = incref_checked(&r);

    /* Verify result */
    __CPROVER_assert(new_ref == initial_ref + 1, "incref increments by 1");
    __CPROVER_assert(new_ref > initial_ref, "incref increases value");
}

/*
 * Test decref with various starting values
 */
void harness_decref(void) {
    Ref r;
    int initial_ref;

    /* Symbolic initial refcount */
    r.ref = initial_ref;

    /* Reasonable bounds - must be positive for decref */
    __CPROVER_assume(initial_ref > 0);
    __CPROVER_assume(initial_ref < 1000000);

    /* Perform decref */
    int new_ref = decref_checked(&r);

    /* Verify result */
    __CPROVER_assert(new_ref == initial_ref - 1, "decref decrements by 1");
    __CPROVER_assert(new_ref < initial_ref, "decref decreases value");
    __CPROVER_assert(new_ref >= 0, "decref doesn't underflow");
}

/*
 * Test sequence of incref/decref operations
 */
void harness_refcount_sequence(void) {
    Ref r;

    /* Start with refcount 1 (typical initialization) */
    r.ref = 1;

    /* Increment */
    incref_checked(&r);
    __CPROVER_assert(r.ref == 2, "after incref: ref=2");

    incref_checked(&r);
    __CPROVER_assert(r.ref == 3, "after 2nd incref: ref=3");

    /* Decrement */
    decref_checked(&r);
    __CPROVER_assert(r.ref == 2, "after decref: ref=2");

    decref_checked(&r);
    __CPROVER_assert(r.ref == 1, "after 2nd decref: ref=1");

    decref_checked(&r);
    __CPROVER_assert(r.ref == 0, "after 3rd decref: ref=0");

    /* Cannot decref when ref=0 (would violate precondition) */
}

/*
 * Main harness
 */
void harness(void) {
    harness_incref();
    harness_decref();
    harness_refcount_sequence();
}
