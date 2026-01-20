# Phase 4: ACSL Annotations and Frama-C Verification

**Status**: In Progress
**Created**: 2026-01-13
**Tool**: Frama-C with WP (Weakest Precondition) plugin

## Overview

Phase 4 adds **ACSL (ANSI/ISO C Specification Language) annotations** to critical Inferno functions and uses **Frama-C** for deductive verification. This provides the strongest formal guarantees by proving function contracts hold for all possible inputs.

## Objectives

Add machine-checkable function contracts to:
1. **newpgrp()** - Pgrp creation
2. **closepgrp()** - Pgrp cleanup
3. **pgrpcpy()** - Namespace copying
4. **newmount()** - Mount creation
5. **mountfree()** - Mount cleanup

## Installation

### macOS/Linux via OPAM

```bash
# Install OPAM (OCaml package manager)
brew install opam  # macOS
# OR
apt-get install opam  # Linux

# Initialize OPAM
opam init

# Install Frama-C
opam install frama-c

# Verify installation
frama-c -version
```

### Alternative: Docker

```bash
docker pull framac/frama-c:latest

# Run verification
docker run --rm -v $(pwd):/data framac/frama-c \
    -wp -wp-rte /data/emu/port/pgrp.c
```

## ACSL Annotations

### Example: newpgrp()

**File**: `emu/port/pgrp.c:8`

```c
/*@
  requires \valid(&pgrpid);
  requires pgrpid.ref >= 0;
  requires pgrpid.ref < INT_MAX;

  ensures \result != \null;
  ensures \result->r.ref == 1;
  ensures \result->pgrpid > \old(pgrpid.ref);
  ensures \result->progmode == 0644;

  assigns pgrpid.ref;
  assigns \result->r, \result->pgrpid, \result->progmode;
*/
Pgrp* newpgrp(void)
{
    Pgrp *p;

    p = malloc(sizeof(Pgrp));
    //@ assert p != \null || (\false && "malloc failed");
    if(p == nil)
        error(Enomem);

    p->r.ref = 1;
    p->pgrpid = incref(&pgrpid);
    p->progmode = 0644;

    return p;
}
```

### Example: closepgrp()

```c
/*@
  requires p == \null || \valid(p);
  requires p != \null ==> p->r.ref >= 0;
  requires p != \null ==> \valid(p->mnthash + (0 .. MNTHASH-1));

  behavior null_or_positive_refcount:
    assumes p == \null || decref(&p->r) != 0;
    ensures \true;  // Returns without freeing
    assigns \nothing;

  behavior free_pgrp:
    assumes p != \null && decref(&p->r) == 0;
    ensures \true;  // Frees pgrp
    assigns p->pgrpid;
    // Complex assigns clause for mount table iteration

  complete behaviors;
  disjoint behaviors;
*/
void closepgrp(Pgrp *p)
```

### Example: incref()

```c
/*@
  requires \valid(r);
  requires r->ref >= 0;
  requires r->ref < INT_MAX;

  ensures r->ref == \old(r->ref) + 1;
  ensures \result == r->ref;
  ensures \result > 0;

  assigns r->ref;
*/
int incref(Ref *r)
{
    //@ assert r->ref < INT_MAX;
    r->ref++;
    return r->ref;
}
```

### Example: decref()

```c
/*@
  requires \valid(r);
  requires r->ref > 0;

  ensures r->ref == \old(r->ref) - 1;
  ensures \result == r->ref;
  ensures \result >= 0;

  assigns r->ref;
*/
int decref(Ref *r)
{
    //@ assert r->ref > 0;
    r->ref--;
    return r->ref;
}
```

## Verification Strategy

### Step 1: Annotate Critical Functions

Add ACSL contracts to:
- Resource management functions (newpgrp, closepgrp, newmount, mountfree)
- Reference counting primitives (incref, decref)
- Locking operations (for ACSL ghost state tracking)

### Step 2: Add Runtime Checks (RTE Plugin)

```bash
frama-c -rte -rte-all emu/port/pgrp.c -print
```

Frama-C RTE plugin automatically generates assertions for:
- Division by zero
- Null pointer dereferences
- Array bounds
- Integer overflow

### Step 3: Run WP Plugin

```bash
frama-c -wp -wp-rte \
    -wp-prover alt-ergo,cvc4 \
    -wp-timeout 30 \
    emu/port/pgrp.c
```

### Step 4: Generate Proof Reports

```bash
frama-c -wp -wp-rte -wp-report-json report.json emu/port/pgrp.c
```

## Expected Results

### Properties to Prove

| Function | Property | Status |
|----------|----------|--------|
| `newpgrp` | Returns non-NULL | TBD |
| `newpgrp` | Refcount initialized to 1 | TBD |
| `closepgrp` | Null-safe | TBD |
| `closepgrp` | Array bounds safe | TBD |
| `pgrpcpy` | Array bounds safe | TBD |
| `incref` | No overflow | TBD |
| `decref` | No underflow | TBD |

### Proof Obligations

Frama-C WP will generate **proof obligations** for each assertion and function contract. These are sent to automatic theorem provers (Alt-Ergo, CVC4, Z3).

**Expected**: 80-90% proofs automatically discharged
**Manual**: Remaining proofs may require lemmas or simplification

## Challenges

1. **Complexity**: ACSL learning curve is steep
2. **Pointer Aliasing**: Requires separation logic annotations
3. **Side Effects**: Complex `assigns` clauses for pointer updates
4. **Exception Handling**: waserror/poperror needs modeling
5. **Proof Automation**: Not all properties auto-provable

## Advantages over CBMC

| Aspect | CBMC (Phase 3) | Frama-C (Phase 4) |
|--------|----------------|-------------------|
| **Verification** | Bounded model checking | Deductive verification |
| **Completeness** | Bounded execution paths | All possible inputs (unbounded) |
| **Proof Strength** | Counterexample finding | Mathematical proof |
| **Automation** | Fully automated | Semi-automated (manual lemmas) |
| **Complexity** | Medium | High |

## Files to Create

- [ ] `formal-verification/acsl/pgrp_annotated.c` - ACSL-annotated pgrp.c
- [ ] `formal-verification/acsl/refcount_spec.h` - ACSL spec for refcounting
- [ ] `formal-verification/acsl/verify.sh` - Frama-C verification script
- [ ] `formal-verification/results/PHASE4-ACSL-RESULTS.md` - Results

## Success Criteria

- [ ] All annotated functions have complete contracts
- [ ] WP plugin proves 80%+ proof obligations
- [ ] Remaining obligations documented with manual proofs or explanations
- [ ] Integration script for automated verification

## References

1. [ACSL Manual](https://frama-c.com/html/acsl.html)
2. [Frama-C Tutorial](https://frama-c.com/html/get-started.html)
3. [ACSL by Example](https://github.com/fraunhoferfokus/acsl-by-example)
4. [Frama-C WP Plugin](https://frama-c.com/html/wp-manual.html)

---

*Document Version: 1.0*
*Status: Installation and annotation phase*
