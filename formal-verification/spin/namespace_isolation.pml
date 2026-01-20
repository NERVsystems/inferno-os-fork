/*
 * Promela Model: Inferno Kernel Namespace Isolation
 *
 * This model verifies that per-process namespaces provide proper isolation.
 * After pgrpcpy() creates a child namespace, modifications to either
 * the parent or child namespace do NOT affect the other.
 *
 * Corresponds to: emu/port/pgrp.c (pgrpcpy, cmount, cunmount)
 *
 * Run with:
 *   spin -a namespace_isolation.pml
 *   gcc -o pan pan.c -DSAFETY
 *   ./pan
 */

/* ========================================================================
 * CONSTANTS
 * ======================================================================== */

#define MAX_PGRPS    3      /* Maximum number of process groups */
#define MAX_PATHS    2      /* Maximum number of paths */
#define MAX_CHANS    3      /* Maximum number of channels */

/* Special values */
#define NONE         255    /* No value / invalid */
#define NO_PARENT    255    /* Pgrp has no parent */

/* ========================================================================
 * STATE VARIABLES
 * ======================================================================== */

/* Process group state */
bool pgrp_exists[MAX_PGRPS];           /* Is pgrp allocated? */
byte pgrp_refcount[MAX_PGRPS];         /* Reference count */
byte pgrp_parent[MAX_PGRPS];           /* Parent pgrp (for tracking copies) */

/* Mount tables: mount_table[pgrp][path] = set of channels (as bitmask) */
/* Each byte represents which channels are mounted at that path */
byte mount_table[MAX_PGRPS * MAX_PATHS];

/* Channel state */
bool chan_exists[MAX_CHANS];           /* Is channel allocated? */
byte chan_refcount[MAX_CHANS];         /* Reference count */

/* Global ID counters */
byte next_pgrp_id = 0;
byte next_chan_id = 0;

/* ========================================================================
 * HELPER MACROS
 * ======================================================================== */

/* Index into mount_table array */
#define MT_IDX(pg, path)  ((pg) * MAX_PATHS + (path))

/* Check if channel c is mounted at (pgrp, path) */
#define IS_MOUNTED(pg, path, c)  ((mount_table[MT_IDX(pg, path)] >> (c)) & 1)

/* Add channel c to mount at (pgrp, path) */
#define DO_MOUNT(pg, path, c)    mount_table[MT_IDX(pg, path)] = mount_table[MT_IDX(pg, path)] | (1 << (c))

/* Remove channel c from mount at (pgrp, path) */
#define DO_UNMOUNT(pg, path, c)  mount_table[MT_IDX(pg, path)] = mount_table[MT_IDX(pg, path)] & ~(1 << (c))

/* ========================================================================
 * OPERATIONS
 * ======================================================================== */

/*
 * Allocate a new channel (models newchan())
 */
inline alloc_channel(cid) {
    atomic {
        if
        :: (next_chan_id < MAX_CHANS) ->
            cid = next_chan_id;
            chan_exists[cid] = true;
            chan_refcount[cid] = 1;
            next_chan_id++;
        :: else ->
            cid = NONE;
        fi
    }
}

/*
 * Create a new process group (models newpgrp())
 */
inline new_pgrp(pgid) {
    atomic {
        if
        :: (next_pgrp_id < MAX_PGRPS) ->
            pgid = next_pgrp_id;
            pgrp_exists[pgid] = true;
            pgrp_refcount[pgid] = 1;
            pgrp_parent[pgid] = NO_PARENT;
            /* Initialize empty mount table */
            byte p;
            for (p : 0 .. (MAX_PATHS - 1)) {
                mount_table[MT_IDX(pgid, p)] = 0;
            }
            next_pgrp_id++;
        :: else ->
            pgid = NONE;
        fi
    }
}

/*
 * Copy a process group (models pgrpcpy())
 * This is the CRITICAL operation for namespace isolation.
 * Creates a DEEP COPY of the mount table.
 */
inline pgrp_copy(from_pgid, to_pgid) {
    atomic {
        /* Preconditions */
        assert(from_pgid < MAX_PGRPS);
        assert(pgrp_exists[from_pgid]);
        assert(to_pgid < MAX_PGRPS);
        assert(pgrp_exists[to_pgid]);

        /* Copy mount table - VALUE COPY, not pointer copy */
        byte p;
        for (p : 0 .. (MAX_PATHS - 1)) {
            mount_table[MT_IDX(to_pgid, p)] = mount_table[MT_IDX(from_pgid, p)];
        }

        /* Record parent relationship */
        pgrp_parent[to_pgid] = from_pgid;
    }
}

/*
 * Mount a channel at a path (models cmount())
 * ONLY modifies the target pgrp's mount table.
 */
inline mount_chan(pgid, path, cid) {
    atomic {
        assert(pgid < MAX_PGRPS && pgrp_exists[pgid]);
        assert(path < MAX_PATHS);
        assert(cid < MAX_CHANS && chan_exists[cid]);

        DO_MOUNT(pgid, path, cid);
    }
}

/*
 * Unmount a channel from a path (models cunmount())
 */
inline unmount_chan(pgid, path, cid) {
    atomic {
        assert(pgid < MAX_PGRPS && pgrp_exists[pgid]);
        assert(path < MAX_PATHS);
        assert(cid < MAX_CHANS);

        DO_UNMOUNT(pgid, path, cid);
    }
}

/* ========================================================================
 * MAIN VERIFICATION PROCESS
 * ======================================================================== */

/*
 * This process models a scenario where:
 * 1. Parent process creates a pgrp with some mounts
 * 2. Child process is forked with pgrpcpy (KPDUPPG)
 * 3. Parent and child make independent mount changes
 * 4. We verify that changes don't cross namespace boundaries
 */

byte parent_pgrp;
byte child_pgrp;
byte parent_chan;
byte child_chan;
byte shared_chan;

proctype ParentProcess() {
    byte path;

    /* Parent mounts a new channel AFTER the fork */
    alloc_channel(parent_chan);
    if
    :: (parent_chan != NONE) ->
        path = 0;  /* Mount at path 0 */
        mount_chan(parent_pgrp, path, parent_chan);

        /* ISOLATION CHECK: child should NOT see this mount */
        assert(!IS_MOUNTED(child_pgrp, path, parent_chan));
    :: else -> skip
    fi
}

proctype ChildProcess() {
    byte path;

    /* Child mounts a new channel AFTER the fork */
    alloc_channel(child_chan);
    if
    :: (child_chan != NONE) ->
        path = 1;  /* Mount at path 1 */
        mount_chan(child_pgrp, path, child_chan);

        /* ISOLATION CHECK: parent should NOT see this mount */
        assert(!IS_MOUNTED(parent_pgrp, path, child_chan));
    :: else -> skip
    fi
}

init {
    /* Phase 1: Create parent pgrp and initial channel */
    new_pgrp(parent_pgrp);
    assert(parent_pgrp != NONE);

    alloc_channel(shared_chan);
    assert(shared_chan != NONE);

    /* Parent mounts the shared channel */
    mount_chan(parent_pgrp, 0, shared_chan);

    /* Phase 2: Fork - create child pgrp with COPIED namespace */
    new_pgrp(child_pgrp);
    assert(child_pgrp != NONE);

    pgrp_copy(parent_pgrp, child_pgrp);

    /* At this point, child should see the shared mount */
    assert(IS_MOUNTED(child_pgrp, 0, shared_chan));

    /* Phase 3: Run parent and child processes concurrently */
    /* They will make independent mount changes */
    run ParentProcess();
    run ChildProcess();
}

/* ========================================================================
 * LTL PROPERTIES
 * ======================================================================== */

/*
 * Property: Namespace Isolation
 * After pgrpcpy, any mount in parent does NOT appear in child (unless
 * it was there before the copy), and vice versa.
 *
 * This is verified by the assertions in ParentProcess and ChildProcess.
 * SPIN will explore all interleavings and check that the assertions hold.
 */

/* Additional safety property: reference counts are non-negative */
/* (automatically satisfied by using unsigned bytes) */
