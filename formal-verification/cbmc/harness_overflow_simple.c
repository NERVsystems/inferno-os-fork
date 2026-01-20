/*
 * CBMC Harness for Integer Overflow (Simplified)
 *
 * Checks overflow properties without large loops.
 */

#include <limits.h>

#define DELTAFD 20
#define MAXNFD 4000

/*
 * Verify fd allocation calculation doesn't overflow
 * given realistic constraints
 */
void harness(void) {
    int maxfd;
    int n;

    /* Constrain maxfd to reasonable values */
    __CPROVER_assume(maxfd >= 0);
    __CPROVER_assume(maxfd <= MAXNFD);

    /* Verify the calculation is overflow-safe for ALL valid maxfd values */
    if(maxfd >= DELTAFD) {
        /* Step-by-step calculation from pgrp.c:146 */
        n = (maxfd + 1 + DELTAFD - 1) / DELTAFD * DELTAFD;

        /* Post-conditions that MUST hold */
        __CPROVER_assert(n > 0, "allocation size positive");
        __CPROVER_assert(n >= maxfd + 1, "allocation size sufficient");
        __CPROVER_assert(n % DELTAFD == 0, "allocation size aligned");
        __CPROVER_assert(n <= (MAXNFD / DELTAFD + 1) * DELTAFD, "allocation size bounded");
    } else {
        n = DELTAFD;
        __CPROVER_assert(n == DELTAFD, "small allocation is DELTAFD");
    }

    /* Global postcondition */
    __CPROVER_assert(n > 0 && n <= 5000, "allocation size in valid range");
}
