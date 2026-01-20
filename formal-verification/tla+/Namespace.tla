---------------------------- MODULE Namespace ----------------------------
(***************************************************************************
 * Formal Specification of Inferno Kernel Namespace Isolation
 *
 * This module defines the core data structures and state for modeling
 * the Inferno kernel's process-specific namespace mechanism.
 *
 * Based on: emu/port/pgrp.c, emu/port/chan.c
 *
 * Key abstractions:
 *   - Pgrp: Process group containing a namespace (mount table)
 *   - Mount: Mount point entry mapping paths to channels
 *   - Chan: Channel (file handle) abstraction
 *   - RefCount: Reference counting for resource management
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

\* =========================================================================
\* CONSTANTS - Model parameters
\* =========================================================================

CONSTANTS
    MaxProcesses,       \* Maximum number of processes (e.g., 3)
    MaxPgrps,           \* Maximum number of process groups (e.g., 4)
    MaxChannels,        \* Maximum number of channels (e.g., 6)
    MaxPaths,           \* Maximum number of distinct paths (e.g., 4)
    MaxMountId          \* Maximum mount ID for bounded checking

\* Type aliases for readability
ProcessId == 1..MaxProcesses
PgrpId == 1..MaxPgrps
ChannelId == 1..MaxChannels
PathId == 1..MaxPaths
MountId == 1..MaxMountId
RefCountVal == 0..MaxProcesses + MaxPgrps

\* =========================================================================
\* STATE VARIABLES
\* =========================================================================

VARIABLES
    \* Process state
    processes,          \* Set of active process IDs
    process_pgrp,       \* ProcessId -> PgrpId (which pgrp a process uses)

    \* Pgrp (namespace) state
    pgrp_exists,        \* PgrpId -> BOOLEAN (is this pgrp allocated)
    pgrp_refcount,      \* PgrpId -> Nat (reference count)
    pgrp_parent,        \* PgrpId -> PgrpId \cup {0} (parent pgrp, 0 = none)

    \* Namespace (mount table) state - the core abstraction
    \* Each pgrp has its own mount table: PgrpId -> (PathId -> Set of ChannelId)
    mount_table,        \* PgrpId -> [PathId -> SUBSET ChannelId]

    \* Channel state
    chan_exists,        \* ChannelId -> BOOLEAN
    chan_refcount,      \* ChannelId -> Nat

    \* Global counters
    next_pgrp_id,       \* Next available pgrp ID
    next_mount_id,      \* Next available mount ID
    next_chan_id        \* Next available channel ID

\* Tuple of all variables for temporal formulas
vars == <<processes, process_pgrp, pgrp_exists, pgrp_refcount, pgrp_parent,
          mount_table, chan_exists, chan_refcount,
          next_pgrp_id, next_mount_id, next_chan_id>>

\* =========================================================================
\* TYPE INVARIANT
\* =========================================================================

TypeOK ==
    /\ processes \subseteq ProcessId
    /\ process_pgrp \in [ProcessId -> PgrpId \cup {0}]
    /\ pgrp_exists \in [PgrpId -> BOOLEAN]
    /\ pgrp_refcount \in [PgrpId -> RefCountVal]
    /\ pgrp_parent \in [PgrpId -> PgrpId \cup {0}]
    /\ mount_table \in [PgrpId -> [PathId -> SUBSET ChannelId]]
    /\ chan_exists \in [ChannelId -> BOOLEAN]
    /\ chan_refcount \in [ChannelId -> RefCountVal]
    /\ next_pgrp_id \in PgrpId \cup {MaxPgrps + 1}
    /\ next_mount_id \in MountId \cup {MaxMountId + 1}
    /\ next_chan_id \in ChannelId \cup {MaxChannels + 1}

\* =========================================================================
\* HELPER FUNCTIONS
\* =========================================================================

\* Check if a pgrp is in use (has positive refcount)
PgrpInUse(pgid) == pgrp_exists[pgid] /\ pgrp_refcount[pgid] > 0

\* Check if a channel is in use
ChanInUse(cid) == chan_exists[cid] /\ chan_refcount[cid] > 0

\* Get the mount table for a specific pgrp and path
MountsAt(pgid, path) ==
    IF pgrp_exists[pgid] THEN mount_table[pgid][path] ELSE {}

\* Get all channels mounted anywhere in a pgrp's namespace
AllMountedChannels(pgid) ==
    UNION {mount_table[pgid][p] : p \in PathId}

\* Check if two pgrps share any mount structure (shallow equality)
\* This would indicate a violation after copy
SharesMountStructure(pg1, pg2) ==
    \E p \in PathId :
        mount_table[pg1][p] \cap mount_table[pg2][p] # {}

\* Check if pg_child was copied from pg_parent
\* (tracked via pgrp_parent relationship)
IsCopyOf(pg_child, pg_parent) ==
    pgrp_parent[pg_child] = pg_parent

\* =========================================================================
\* INITIAL STATE
\* =========================================================================

Init ==
    \* No processes initially
    /\ processes = {}
    /\ process_pgrp = [p \in ProcessId |-> 0]

    \* No pgrps allocated
    /\ pgrp_exists = [pg \in PgrpId |-> FALSE]
    /\ pgrp_refcount = [pg \in PgrpId |-> 0]
    /\ pgrp_parent = [pg \in PgrpId |-> 0]

    \* Empty mount tables
    /\ mount_table = [pg \in PgrpId |-> [p \in PathId |-> {}]]

    \* No channels allocated
    /\ chan_exists = [c \in ChannelId |-> FALSE]
    /\ chan_refcount = [c \in ChannelId |-> 0]

    \* IDs start at 1
    /\ next_pgrp_id = 1
    /\ next_mount_id = 1
    /\ next_chan_id = 1

\* =========================================================================
\* CHANNEL OPERATIONS
\* =========================================================================

\* Allocate a new channel (models newchan())
AllocChannel ==
    /\ next_chan_id <= MaxChannels
    /\ LET cid == next_chan_id IN
        /\ chan_exists' = [chan_exists EXCEPT ![cid] = TRUE]
        /\ chan_refcount' = [chan_refcount EXCEPT ![cid] = 1]
        /\ next_chan_id' = next_chan_id + 1
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_refcount,
                   pgrp_parent, mount_table, next_pgrp_id, next_mount_id>>

\* Increment channel reference (models incref(&c->r))
IncRefChannel(cid) ==
    /\ ChanInUse(cid)
    /\ chan_refcount' = [chan_refcount EXCEPT ![cid] = @ + 1]
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_refcount,
                   pgrp_parent, mount_table, chan_exists,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* Decrement channel reference (models decref(&c->r) / cclose())
DecRefChannel(cid) ==
    /\ ChanInUse(cid)
    /\ chan_refcount' = [chan_refcount EXCEPT ![cid] = @ - 1]
    \* When refcount hits 0, channel becomes "freed" (exists but refcount=0)
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_refcount,
                   pgrp_parent, mount_table, chan_exists,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* =========================================================================
\* PGRP OPERATIONS
\* =========================================================================

\* Create a new process group (models newpgrp())
NewPgrp ==
    /\ next_pgrp_id <= MaxPgrps
    /\ LET pgid == next_pgrp_id IN
        /\ pgrp_exists' = [pgrp_exists EXCEPT ![pgid] = TRUE]
        /\ pgrp_refcount' = [pgrp_refcount EXCEPT ![pgid] = 1]
        /\ pgrp_parent' = [pgrp_parent EXCEPT ![pgid] = 0]
        /\ mount_table' = [mount_table EXCEPT ![pgid] = [p \in PathId |-> {}]]
        /\ next_pgrp_id' = next_pgrp_id + 1
    /\ UNCHANGED <<processes, process_pgrp, chan_exists, chan_refcount,
                   next_mount_id, next_chan_id>>

\* Increment pgrp reference count
IncRefPgrp(pgid) ==
    /\ PgrpInUse(pgid)
    /\ pgrp_refcount' = [pgrp_refcount EXCEPT ![pgid] = @ + 1]
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_parent,
                   mount_table, chan_exists, chan_refcount,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* Close/decrement pgrp reference (models closepgrp())
\* When refcount hits 0, frees all mounts and channels
ClosePgrp(pgid) ==
    /\ PgrpInUse(pgid)
    /\ pgrp_refcount' = [pgrp_refcount EXCEPT ![pgid] = @ - 1]
    \* If refcount becomes 0, clear the mount table
    /\ IF pgrp_refcount[pgid] = 1  \* will become 0
       THEN
         \* Clear mount table (models mountfree() calls)
         /\ mount_table' = [mount_table EXCEPT ![pgid] = [p \in PathId |-> {}]]
         \* Note: In real impl, this would also decref all mounted channels
         \* We model this abstractly
       ELSE
         /\ mount_table' = mount_table
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_parent,
                   chan_exists, chan_refcount,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* =========================================================================
\* NAMESPACE COPY OPERATION (The critical operation for isolation)
\* =========================================================================

(*
 * Models pgrpcpy(to, from) from pgrp.c
 *
 * Key property: Creates a DEEP COPY of the namespace.
 * The new pgrp gets its own mount table that is initially
 * identical to the parent but is independent thereafter.
 *
 * In the actual implementation:
 *   - New Mhead structures are allocated for each mount point
 *   - New Mount structures are allocated for each mount entry
 *   - Channels are SHARED (incref'd) but mount structures are copied
 *
 * For our abstraction:
 *   - We model this as copying the mount table contents
 *   - The key insight is that subsequent mounts to either pgrp
 *     should NOT affect the other
 *)
PgrpCopy(from_pgid, to_pgid) ==
    /\ PgrpInUse(from_pgid)
    /\ pgrp_exists[to_pgid]
    /\ pgrp_refcount[to_pgid] > 0
    \* Copy mount table from 'from' to 'to'
    /\ mount_table' = [mount_table EXCEPT
                       ![to_pgid] = mount_table[from_pgid]]
    \* Record parent relationship for tracking
    /\ pgrp_parent' = [pgrp_parent EXCEPT ![to_pgid] = from_pgid]
    \* In real impl, channels get incref'd - we abstract this
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_refcount,
                   chan_exists, chan_refcount,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* =========================================================================
\* MOUNT OPERATIONS
\* =========================================================================

(*
 * Models cmount(new, old, flag, spec) from chan.c
 *
 * Adds channel 'cid' to the mount table at 'path' for pgrp 'pgid'
 * This is the operation that MUST NOT cross namespace boundaries
 *)
Mount(pgid, path, cid) ==
    /\ PgrpInUse(pgid)
    /\ ChanInUse(cid)
    /\ path \in PathId
    \* Add channel to mount table at path
    /\ mount_table' = [mount_table EXCEPT
                       ![pgid][path] = @ \cup {cid}]
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_refcount,
                   pgrp_parent, chan_exists, chan_refcount,
                   next_pgrp_id, next_mount_id, next_chan_id>>

(*
 * Models cunmount(mnt, mounted) from chan.c
 *
 * Removes channel 'cid' from mount table at 'path' for pgrp 'pgid'
 *)
Unmount(pgid, path, cid) ==
    /\ PgrpInUse(pgid)
    /\ cid \in mount_table[pgid][path]
    \* Remove channel from mount table
    /\ mount_table' = [mount_table EXCEPT
                       ![pgid][path] = @ \ {cid}]
    /\ UNCHANGED <<processes, process_pgrp, pgrp_exists, pgrp_refcount,
                   pgrp_parent, chan_exists, chan_refcount,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* =========================================================================
\* PROCESS OPERATIONS
\* =========================================================================

\* Create a new process with a new pgrp
CreateProcess ==
    /\ \E pid \in ProcessId :
        /\ pid \notin processes
        /\ next_pgrp_id <= MaxPgrps
        /\ LET pgid == next_pgrp_id IN
            /\ processes' = processes \cup {pid}
            /\ process_pgrp' = [process_pgrp EXCEPT ![pid] = pgid]
            /\ pgrp_exists' = [pgrp_exists EXCEPT ![pgid] = TRUE]
            /\ pgrp_refcount' = [pgrp_refcount EXCEPT ![pgid] = 1]
            /\ pgrp_parent' = [pgrp_parent EXCEPT ![pgid] = 0]
            /\ mount_table' = [mount_table EXCEPT ![pgid] = [p \in PathId |-> {}]]
            /\ next_pgrp_id' = next_pgrp_id + 1
    /\ UNCHANGED <<chan_exists, chan_refcount, next_mount_id, next_chan_id>>

\* Fork a process with KPDUPPG flag (duplicate pgrp)
\* This is the critical operation for namespace isolation
ForkWithDupPgrp(parent_pid) ==
    /\ parent_pid \in processes
    /\ \E child_pid \in ProcessId :
        /\ child_pid \notin processes
        /\ next_pgrp_id <= MaxPgrps
        /\ LET parent_pgid == process_pgrp[parent_pid]
               child_pgid == next_pgrp_id
           IN
            \* Create child process
            /\ processes' = processes \cup {child_pid}
            /\ process_pgrp' = [process_pgrp EXCEPT ![child_pid] = child_pgid]
            \* Create new pgrp for child
            /\ pgrp_exists' = [pgrp_exists EXCEPT ![child_pgid] = TRUE]
            /\ pgrp_refcount' = [pgrp_refcount EXCEPT ![child_pgid] = 1]
            /\ pgrp_parent' = [pgrp_parent EXCEPT ![child_pgid] = parent_pgid]
            \* COPY the mount table (deep copy semantics)
            /\ mount_table' = [mount_table EXCEPT
                               ![child_pgid] = mount_table[parent_pgid]]
            /\ next_pgrp_id' = next_pgrp_id + 1
    /\ UNCHANGED <<chan_exists, chan_refcount, next_mount_id, next_chan_id>>

\* Terminate a process
TerminateProcess(pid) ==
    /\ pid \in processes
    /\ LET pgid == process_pgrp[pid] IN
        /\ processes' = processes \ {pid}
        /\ process_pgrp' = [process_pgrp EXCEPT ![pid] = 0]
        \* Decrement pgrp refcount
        /\ pgrp_refcount' = [pgrp_refcount EXCEPT ![pgid] = @ - 1]
        \* If refcount becomes 0, clear mount table
        /\ IF pgrp_refcount[pgid] = 1
           THEN mount_table' = [mount_table EXCEPT ![pgid] = [p \in PathId |-> {}]]
           ELSE mount_table' = mount_table
    /\ UNCHANGED <<pgrp_exists, pgrp_parent, chan_exists, chan_refcount,
                   next_pgrp_id, next_mount_id, next_chan_id>>

\* =========================================================================
\* NEXT STATE RELATION
\* =========================================================================

Next ==
    \/ CreateProcess
    \/ \E pid \in processes : ForkWithDupPgrp(pid)
    \/ \E pid \in processes : TerminateProcess(pid)
    \/ AllocChannel
    \/ \E cid \in ChannelId : ChanInUse(cid) /\ IncRefChannel(cid)
    \/ \E cid \in ChannelId : ChanInUse(cid) /\ DecRefChannel(cid)
    \/ \E pgid \in PgrpId, path \in PathId, cid \in ChannelId :
        PgrpInUse(pgid) /\ ChanInUse(cid) /\ Mount(pgid, path, cid)
    \/ \E pgid \in PgrpId, path \in PathId, cid \in ChannelId :
        PgrpInUse(pgid) /\ cid \in mount_table[pgid][path] /\ Unmount(pgid, path, cid)

\* Fairness: Eventually some action happens
Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
