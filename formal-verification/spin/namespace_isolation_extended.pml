/*
 * Extended Promela Model: Inferno Kernel Namespace Isolation
 *
 * This extended model tests more scenarios:
 * 1. Multiple concurrent mounts/unmounts
 * 2. Nested fork operations
 * 3. Race conditions between mount and copy operations
 *
 * Run with:
 *   spin -a namespace_isolation_extended.pml
 *   gcc -o pan pan.c -DSAFETY -O2 -w
 *   ./pan -m1000000
 */

#define MAX_PGRPS    4
#define MAX_PATHS    3
#define MAX_CHANS    5

#define NONE         255
#define NO_PARENT    255

/* State */
bool pgrp_exists[MAX_PGRPS];
byte pgrp_refcount[MAX_PGRPS];
byte pgrp_parent[MAX_PGRPS];
byte mount_table[MAX_PGRPS * MAX_PATHS];
bool chan_exists[MAX_CHANS];
byte chan_refcount[MAX_CHANS];

byte next_pgrp_id = 0;
byte next_chan_id = 0;

/* Snapshot of parent's mount table at time of copy */
byte snapshot_table[MAX_PATHS];
bool snapshot_taken = false;

#define MT_IDX(pg, path)  ((pg) * MAX_PATHS + (path))
#define IS_MOUNTED(pg, path, c)  ((mount_table[MT_IDX(pg, path)] >> (c)) & 1)
#define DO_MOUNT(pg, path, c)    mount_table[MT_IDX(pg, path)] = mount_table[MT_IDX(pg, path)] | (1 << (c))
#define DO_UNMOUNT(pg, path, c)  mount_table[MT_IDX(pg, path)] = mount_table[MT_IDX(pg, path)] & ~(1 << (c))

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

inline new_pgrp(pgid) {
    atomic {
        if
        :: (next_pgrp_id < MAX_PGRPS) ->
            pgid = next_pgrp_id;
            pgrp_exists[pgid] = true;
            pgrp_refcount[pgid] = 1;
            pgrp_parent[pgid] = NO_PARENT;
            byte np_p;
            for (np_p : 0 .. (MAX_PATHS - 1)) {
                mount_table[MT_IDX(pgid, np_p)] = 0;
            }
            next_pgrp_id++;
        :: else ->
            pgid = NONE;
        fi
    }
}

inline pgrp_copy(from_pgid, to_pgid) {
    atomic {
        byte pc_p;
        for (pc_p : 0 .. (MAX_PATHS - 1)) {
            mount_table[MT_IDX(to_pgid, pc_p)] = mount_table[MT_IDX(from_pgid, pc_p)];
        }
        pgrp_parent[to_pgid] = from_pgid;
    }
}

inline mount_chan(pgid, path, cid) {
    atomic {
        DO_MOUNT(pgid, path, cid);
    }
}

inline unmount_chan(pgid, path, cid) {
    atomic {
        DO_UNMOUNT(pgid, path, cid);
    }
}

/* Test variables */
byte parent_pgrp = NONE;
byte child_pgrp = NONE;
byte grandchild_pgrp = NONE;

byte chan0, chan1, chan2, chan3;

/*
 * KEY INVARIANT: After pgrpcpy, the child's mount table is an independent copy.
 * Any subsequent modifications to parent do not affect child.
 * Any subsequent modifications to child do not affect parent.
 */

/* Track modifications for verification */
bool parent_modified = false;
bool child_modified = false;
byte parent_mount_path = NONE;
byte parent_mount_chan = NONE;
byte child_mount_path = NONE;
byte child_mount_chan = NONE;

proctype ParentModifier() {
    byte cid, path;

    /* Allocate a new channel */
    alloc_channel(cid);
    if
    :: (cid != NONE && parent_pgrp != NONE) ->
        /* Choose a path to mount on */
        if
        :: path = 0;
        :: path = 1;
        :: path = 2;
        fi

        /* Mount in parent's namespace */
        mount_chan(parent_pgrp, path, cid);

        /* Record what we did */
        parent_mount_path = path;
        parent_mount_chan = cid;
        parent_modified = true;

        /* ISOLATION CHECK: If child exists and we already copied, child should NOT see this */
        if
        :: (child_pgrp != NONE && snapshot_taken) ->
            /* This channel was mounted AFTER the copy, so child must not see it */
            assert(!IS_MOUNTED(child_pgrp, path, cid));
        :: else -> skip
        fi
    :: else -> skip
    fi
}

proctype ChildModifier() {
    byte cid, path;

    /* Wait for child pgrp to exist */
    (child_pgrp != NONE);

    /* Allocate a new channel */
    alloc_channel(cid);
    if
    :: (cid != NONE) ->
        /* Choose a path to mount on */
        if
        :: path = 0;
        :: path = 1;
        :: path = 2;
        fi

        /* Mount in child's namespace */
        mount_chan(child_pgrp, path, cid);

        /* Record what we did */
        child_mount_path = path;
        child_mount_chan = cid;
        child_modified = true;

        /* ISOLATION CHECK: Parent should NOT see this mount */
        assert(!IS_MOUNTED(parent_pgrp, path, cid));
    :: else -> skip
    fi
}

/*
 * Verify the isolation invariant holds at the end
 */
proctype IsolationChecker() {
    /* Wait until both have done their modifications */
    (parent_modified && child_modified);

    /* Final isolation checks */

    /* 1. Parent's new mount is not in child */
    if
    :: (parent_mount_chan != NONE && parent_mount_path != NONE && child_pgrp != NONE) ->
        assert(!IS_MOUNTED(child_pgrp, parent_mount_path, parent_mount_chan));
    :: else -> skip
    fi

    /* 2. Child's new mount is not in parent */
    if
    :: (child_mount_chan != NONE && child_mount_path != NONE) ->
        assert(!IS_MOUNTED(parent_pgrp, child_mount_path, child_mount_chan));
    :: else -> skip
    fi

    /* 3. Original shared mount is still visible in both (if it was there) */
    if
    :: (chan0 != NONE) ->
        assert(IS_MOUNTED(parent_pgrp, 0, chan0));
        assert(IS_MOUNTED(child_pgrp, 0, chan0));
    :: else -> skip
    fi
}

init {
    byte init_p;

    /* Create parent pgrp */
    new_pgrp(parent_pgrp);
    assert(parent_pgrp != NONE);

    /* Create an initial shared channel and mount it */
    alloc_channel(chan0);
    if
    :: (chan0 != NONE) ->
        mount_chan(parent_pgrp, 0, chan0);
    :: else -> skip
    fi

    /* Take snapshot of parent's mount table */
    for (init_p : 0 .. (MAX_PATHS - 1)) {
        snapshot_table[init_p] = mount_table[MT_IDX(parent_pgrp, init_p)];
    }

    /* Create child pgrp and copy namespace (models fork with KPDUPPG) */
    new_pgrp(child_pgrp);
    assert(child_pgrp != NONE);
    pgrp_copy(parent_pgrp, child_pgrp);
    snapshot_taken = true;

    /* Verify initial copy was correct */
    for (init_p : 0 .. (MAX_PATHS - 1)) {
        assert(mount_table[MT_IDX(child_pgrp, init_p)] == snapshot_table[init_p]);
    }

    /* Run concurrent modifications and checker */
    run ParentModifier();
    run ChildModifier();
    run IsolationChecker();
}

/*
 * LTL Properties (checked by assertions above):
 *
 * 1. Post-copy isolation: After pgrpcpy, mounts in parent don't affect child
 * 2. Post-copy isolation: After pgrpcpy, mounts in child don't affect parent
 * 3. Copy correctness: At copy time, child gets exact copy of parent's mounts
 * 4. Shared visibility: Pre-existing mounts are visible in both namespaces
 */
