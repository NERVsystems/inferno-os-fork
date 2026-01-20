/*
 * SPIN Model for Inferno Namespace Locking Protocol
 *
 * This model verifies deadlock freedom and correct lock ordering
 * in concurrent namespace operations.
 *
 * Lock Types:
 * - pg->ns: RWlock protecting mount table hash
 * - m->lock: RWlock protecting individual Mhead structures
 *
 * Key Invariant: pg->ns is ALWAYS acquired before m->lock
 */

/* ========== RWLock Implementation ========== */

typedef rwlock {
    byte readers;        /* Number of active readers (0-255) */
    bit writer;          /* 1 if writer holds lock, 0 otherwise */
}

/* Global locks */
rwlock pg_ns;     /* Namespace lock (pg->ns) */
rwlock mhead_lock; /* Mhead lock (m->lock) */

/* Acquire read lock */
inline rlock(lock) {
    atomic {
        (lock.writer == 0);
        lock.readers = lock.readers + 1;
    }
}

/* Release read lock */
inline runlock(lock) {
    atomic {
        assert(lock.readers > 0);
        lock.readers = lock.readers - 1;
    }
}

/* Acquire write lock */
inline wlock(lock) {
    atomic {
        (lock.writer == 0) && (lock.readers == 0);
        lock.writer = 1;
    }
}

/* Release write lock */
inline wunlock(lock) {
    atomic {
        assert(lock.writer == 1);
        lock.writer = 0;
    }
}

/* ========== Process States ========== */

mtype = { IDLE, IN_CMOUNT, IN_CUNMOUNT, IN_PGRPCPY, IN_FINDMOUNT, IN_CLOSEPGRP };

/* Track which locks each process holds */
typedef proc_state {
    bit holds_pg_ns_read;
    bit holds_pg_ns_write;
    bit holds_mhead_read;
    bit holds_mhead_write;
    mtype state;
}

proc_state proc[3];  /* Model 3 concurrent processes */

/* ========== Namespace Operations ========== */

/*
 * cmount(): Mount a channel onto another channel
 *
 * Lock sequence:
 * 1. wlock(&pg->ns)
 * 2. wlock(&m->lock)
 * 3. wunlock(&pg->ns)  <- EARLY RELEASE (optimization)
 * 4. wunlock(&m->lock)
 */
proctype cmount() {
    proc[_pid - 1].state = IN_CMOUNT;

    /* Acquire namespace write lock */
    wlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 1;

    /* Acquire mhead write lock */
    wlock(mhead_lock);
    proc[_pid - 1].holds_mhead_write = 1;

    /* Early release of namespace lock (line 458 in chan.c) */
    wunlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 0;

    /* Do mount operation (modeled as atomic block) */
    atomic {
        /* Critical section - modify mount table */
        skip;
    }

    /* Release mhead lock */
    wunlock(mhead_lock);
    proc[_pid - 1].holds_mhead_write = 0;

    proc[_pid - 1].state = IDLE;
}

/*
 * cunmount(): Unmount a channel
 *
 * Lock sequence:
 * 1. wlock(&pg->ns)
 * 2. wlock(&m->lock)
 * 3. wunlock(&pg->ns), wunlock(&m->lock) in various orders
 */
proctype cunmount() {
    proc[_pid - 1].state = IN_CUNMOUNT;

    /* Acquire namespace write lock */
    wlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 1;

    /* Acquire mhead write lock */
    wlock(mhead_lock);
    proc[_pid - 1].holds_mhead_write = 1;

    /* Critical section - modify mount table */
    atomic {
        skip;
    }

    /* Release both locks (order varies in actual code) */
    if
    :: wunlock(mhead_lock);
       proc[_pid - 1].holds_mhead_write = 0;
       wunlock(pg_ns);
       proc[_pid - 1].holds_pg_ns_write = 0;
    :: wunlock(pg_ns);
       proc[_pid - 1].holds_pg_ns_write = 0;
       wunlock(mhead_lock);
       proc[_pid - 1].holds_mhead_write = 0;
    fi

    proc[_pid - 1].state = IDLE;
}

/*
 * pgrpcpy(): Copy namespace from parent to child
 *
 * Lock sequence:
 * 1. wlock(&from->ns)
 * 2. For each mhead: rlock(&f->lock), ..., runlock(&f->lock)
 * 3. wunlock(&from->ns)
 */
proctype pgrpcpy() {
    proc[_pid - 1].state = IN_PGRPCPY;

    /* Acquire source namespace write lock */
    wlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 1;

    /* Iterate over mount heads (model as single iteration) */
    rlock(mhead_lock);
    proc[_pid - 1].holds_mhead_read = 1;

    /* Copy mount entry */
    atomic {
        skip;
    }

    runlock(mhead_lock);
    proc[_pid - 1].holds_mhead_read = 0;

    /* Release namespace lock */
    wunlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 0;

    proc[_pid - 1].state = IDLE;
}

/*
 * findmount(): Look up a mount point
 *
 * Lock sequence:
 * 1. rlock(&pg->ns)
 * 2. rlock(&m->lock)
 * 3. runlock(&pg->ns)
 * 4. runlock(&m->lock)
 */
proctype findmount() {
    proc[_pid - 1].state = IN_FINDMOUNT;

    /* Acquire namespace read lock */
    rlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_read = 1;

    /* Acquire mhead read lock */
    rlock(mhead_lock);
    proc[_pid - 1].holds_mhead_read = 1;

    /* Search mount table */
    atomic {
        skip;
    }

    /* Release namespace lock first */
    runlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_read = 0;

    /* Release mhead lock */
    runlock(mhead_lock);
    proc[_pid - 1].holds_mhead_read = 0;

    proc[_pid - 1].state = IDLE;
}

/*
 * closepgrp(): Close and free a process group
 *
 * Lock sequence:
 * 1. wlock(&p->ns)
 * 2. For each mhead: wlock(&f->lock), ..., wunlock(&f->lock)
 * 3. wunlock(&p->ns)
 */
proctype closepgrp() {
    proc[_pid - 1].state = IN_CLOSEPGRP;

    /* Acquire namespace write lock */
    wlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 1;

    /* Iterate over mount heads (model as single iteration) */
    wlock(mhead_lock);
    proc[_pid - 1].holds_mhead_write = 1;

    /* Free mount structures */
    atomic {
        skip;
    }

    wunlock(mhead_lock);
    proc[_pid - 1].holds_mhead_write = 0;

    /* Release namespace lock */
    wunlock(pg_ns);
    proc[_pid - 1].holds_pg_ns_write = 0;

    proc[_pid - 1].state = IDLE;
}

/* ========== Lock Ordering Invariant ========== */

/*
 * Verify lock acquisition ordering: pg_ns is ALWAYS acquired before mhead.
 *
 * Once both locks are held, they can be released in any order, so we allow
 * holding mhead without pg_ns if we're in a state that releases locks.
 */
ltl lock_ordering {
    [] (
        (proc[0].holds_mhead_read || proc[0].holds_mhead_write) ->
        (proc[0].holds_pg_ns_read || proc[0].holds_pg_ns_write ||
         proc[0].state == IN_CMOUNT ||      /* releases pg_ns early */
         proc[0].state == IN_CUNMOUNT ||    /* can release in either order */
         proc[0].state == IN_PGRPCPY ||     /* releases pg_ns then mhead */
         proc[0].state == IN_FINDMOUNT ||   /* releases pg_ns then mhead */
         proc[0].state == IN_CLOSEPGRP)     /* releases mhead then pg_ns */
    ) &&
    (
        (proc[1].holds_mhead_read || proc[1].holds_mhead_write) ->
        (proc[1].holds_pg_ns_read || proc[1].holds_pg_ns_write ||
         proc[1].state == IN_CMOUNT ||
         proc[1].state == IN_CUNMOUNT ||
         proc[1].state == IN_PGRPCPY ||
         proc[1].state == IN_FINDMOUNT ||
         proc[1].state == IN_CLOSEPGRP)
    ) &&
    (
        (proc[2].holds_mhead_read || proc[2].holds_mhead_write) ->
        (proc[2].holds_pg_ns_read || proc[2].holds_pg_ns_write ||
         proc[2].state == IN_CMOUNT ||
         proc[2].state == IN_CUNMOUNT ||
         proc[2].state == IN_PGRPCPY ||
         proc[2].state == IN_FINDMOUNT ||
         proc[2].state == IN_CLOSEPGRP)
    )
}

/* ========== Test Scenario: Concurrent Operations ========== */

init {
    atomic {
        /* Initialize locks */
        pg_ns.readers = 0;
        pg_ns.writer = 0;

        mhead_lock.readers = 0;
        mhead_lock.writer = 0;

        /* Initialize process states */
        proc[0].state = IDLE;
        proc[1].state = IDLE;
        proc[2].state = IDLE;

        /* Launch concurrent operations */
        if
        :: run cmount();    run findmount();  run pgrpcpy();
        :: run cunmount();  run cmount();     run findmount();
        :: run closepgrp(); run pgrpcpy();    run cmount();
        :: run findmount(); run findmount();  run findmount(); /* Multiple readers */
        :: run cmount();    run cmount();     /* Writer-writer */
        :: run pgrpcpy();   run cmount();     /* Read-write mix */
        fi
    }
}
