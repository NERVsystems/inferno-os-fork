--------------------------- MODULE MC_Namespace ---------------------------
(***************************************************************************
 * Model Checking Configuration for Namespace Specification
 *
 * This module configures the TLC model checker with appropriate
 * constants and properties to verify.
 *
 * Usage:
 *   tlc MC_Namespace.tla -config MC_Namespace.cfg
 *
 * Or with the TLA+ Toolbox, select this module as the model.
 ***************************************************************************)

EXTENDS Namespace, NamespaceProperties, TLC

\* =========================================================================
\* MODEL CONSTANTS
\* =========================================================================

\* Small values for tractable model checking
\* These can be increased for more thorough checking at cost of time

CONSTANTS
    MC_MaxProcesses,
    MC_MaxPgrps,
    MC_MaxChannels,
    MC_MaxPaths,
    MC_MaxMountId

\* Bind the model constants to the specification constants
MaxProcesses == MC_MaxProcesses
MaxPgrps == MC_MaxPgrps
MaxChannels == MC_MaxChannels
MaxPaths == MC_MaxPaths
MaxMountId == MC_MaxMountId

\* =========================================================================
\* STATE CONSTRAINT
\* =========================================================================

\* Limit state space for finite model checking
StateConstraint ==
    /\ Cardinality(processes) <= MC_MaxProcesses
    /\ next_pgrp_id <= MC_MaxPgrps + 1
    /\ next_chan_id <= MC_MaxChannels + 1

\* =========================================================================
\* ACTION CONSTRAINT
\* =========================================================================

\* Limit the number of objects to bound state space
ActionConstraint ==
    /\ next_pgrp_id' <= MC_MaxPgrps + 1
    /\ next_chan_id' <= MC_MaxChannels + 1

\* =========================================================================
\* INVARIANTS TO CHECK
\* =========================================================================

\* Primary safety invariant
INVARIANT_Safety == SafetyInvariant

\* Full correctness invariant
INVARIANT_Full == FullCorrectness

\* =========================================================================
\* PROPERTIES TO CHECK
\* =========================================================================

\* Type correctness (should always hold)
PROPERTY_TypeOK == []TypeOK

\* Namespace isolation (the main security property)
PROPERTY_Isolation == []NamespaceIsolation

\* Reference counting (memory safety)
PROPERTY_RefCount == []RefCountNonNegative

\* =========================================================================
\* SYMMETRY OPTIMIZATION
\* =========================================================================

\* Process IDs are symmetric (any permutation is equivalent)
ProcessSymmetry == Permutations(1..MC_MaxProcesses)

\* Channel IDs are symmetric
ChannelSymmetry == Permutations(1..MC_MaxChannels)

\* Path IDs are symmetric
PathSymmetry == Permutations(1..MC_MaxPaths)

\* =========================================================================
\* DEBUG HELPERS
\* =========================================================================

\* Alias for printing state in error traces
Alias == [
    procs |-> processes,
    proc_pgrp |-> process_pgrp,
    pgrps |-> {pg \in PgrpId : pgrp_exists[pg]},
    pgrp_refs |-> [pg \in {p \in PgrpId : pgrp_exists[p]} |-> pgrp_refcount[pg]],
    mounts |-> [pg \in {p \in PgrpId : pgrp_exists[p]} |->
                    [path \in PathId |-> mount_table[pg][path]]],
    chans |-> {c \in ChannelId : chan_exists[c]},
    chan_refs |-> [c \in {ch \in ChannelId : chan_exists[ch]} |-> chan_refcount[c]]
]

=============================================================================
