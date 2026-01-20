# Phase 3: CBMC Bounded Model Checking

**Status**: In Progress
**Created**: 2026-01-13
**Tool**: CBMC 6.7.1

## Overview

Phase 3 verifies the **actual C implementation** using CBMC (C Bounded Model Checker). While Phase 1-2 verified high-level properties on abstract models, Phase 3 checks the real code for implementation bugs.

## Objectives

Verify the following properties directly in the C code:

1. **Buffer Bounds Safety** - Array accesses within bounds
2. **Null Pointer Safety** - No null pointer dereferences
3. **Reference Count Safety** - No overflow, always non-negative
4. **Integer Overflow** - Arithmetic operations don't overflow
5. **Pointer Safety** - Valid pointer arithmetic

## Target Functions

### High Priority (pgrp.c)

| Function | Lines | Properties to Verify |
|----------|-------|----------------------|
| `newpgrp()` | 8-20 | Null check after malloc, refcount init |
| `closepgrp()` | 22-48 | Array bounds (mnthash), null checks, refcount |
| `pgrpcpy()` | 74-130 | Array bounds (MNTHASH loop), pointer safety |
| `newfgrp()` | 132-157 | Integer overflow in allocation, array bounds |
| `dupfgrp()` | 159-193 | Array bounds (fd array), integer overflow |
| `newmount()` | 210-227 | Refcount increment, null checks |

### Medium Priority (chan.c)

| Function | Lines | Properties to Verify |
|----------|-------|----------------------|
| `cmount()` | 388-502 | MOUNTH macro bounds, pointer safety |
| `cunmount()` | 503-573 | MOUNTH macro bounds, null checks |

## Key Verification Targets

### 1. Array Bounds (mnthash)

**File**: `emu/port/pgrp.c:32`

```c
e = &p->mnthash[MNTHASH];  // MNTHASH = 32
for(h = p->mnthash; h < e; h++)
```

**CBMC Assertion**:
```c
__CPROVER_assert(h >= p->mnthash && h < &p->mnthash[MNTHASH],
                 "mnthash pointer within bounds");
```

### 2. Array Bounds (MOUNTH macro)

**File**: `emu/port/dat.h:257`

```c
#define MOUNTH(p,qid)	((p)->mnthash[(qid).path&((1<<MNTLOG)-1)])
```

The macro masks to ensure `(qid).path & 31` is always [0, 31]. **Already bounds-safe by design.**

### 3. Integer Overflow in Allocation

**File**: `emu/port/pgrp.c:146`

```c
n = (old->maxfd+1 + DELTAFD-1)/DELTAFD * DELTAFD;
```

**Potential Issue**: `old->maxfd + 1` could overflow if maxfd = INT_MAX

**CBMC Assertion**:
```c
__CPROVER_assert(old->maxfd < INT_MAX - DELTAFD,
                 "no integer overflow in fd allocation");
```

### 4. Array Bounds (fd array)

**File**: `emu/port/pgrp.c:184`

```c
for(i = 0; i <= f->maxfd; i++) {
    if(c = f->fd[i])
        incref(&c->r);
        new->fd[i] = c;
}
```

**Verification**: Ensure `maxfd < nfd` so `i` doesn't exceed array bounds

**CBMC Assertion**:
```c
__CPROVER_assert(i < new->nfd, "fd array access within bounds");
__CPROVER_assert(i < f->nfd, "fd array access within bounds");
```

### 5. Reference Count Operations

**Files**: Multiple locations

**Concern**: Integer overflow in `incref()`, underflow in `decref()`

**CBMC Strategy**: Stub out `incref`/`decref` with assertions:
```c
#ifdef CBMC
int incref(Ref *r) {
    __CPROVER_assert(r->ref < INT_MAX, "refcount no overflow");
    return ++r->ref;
}

int decref(Ref *r) {
    __CPROVER_assert(r->ref > 0, "refcount positive before decref");
    return --r->ref;
}
#endif
```

## CBMC Verification Strategy

### Approach 1: Function-Level Bounded Verification

Verify individual functions with bounded inputs:

```bash
cbmc --function newpgrp \
     --bounds-check \
     --pointer-check \
     --signed-overflow-check \
     --unsigned-overflow-check \
     --unwinding-assertions \
     emu/port/pgrp.c
```

### Approach 2: Harness-Based Verification

Create test harnesses that set up realistic scenarios:

**Example Harness** (`formal-verification/cbmc/harness_pgrpcpy.c`):
```c
#include "dat.h"
#include "fns.h"

void harness_pgrpcpy(void) {
    Pgrp from, to;
    int i;

    // Symbolic initialization
    __CPROVER_assume(from.pgrpid > 0);
    __CPROVER_assume(to.pgrpid > 0);

    // Initialize arrays
    for(i = 0; i < MNTHASH; i++) {
        from.mnthash[i] = NULL; // or symbolic Mhead*
        to.mnthash[i] = NULL;
    }

    // Run the function
    pgrpcpy(&to, &from);

    // Post-conditions
    __CPROVER_assert(to.progmode == from.progmode,
                     "progmode copied correctly");
}
```

### Approach 3: Loop Unwinding

For loops with bounded iterations:

```bash
cbmc --unwind 32 \  # MNTHASH iterations
     --unwinding-assertions \
     emu/port/pgrp.c
```

## Expected Results

### Properties That Should Hold

✅ **Array bounds**: All array accesses within declared bounds
✅ **Pointer safety**: No invalid pointer arithmetic
✅ **Null safety**: All pointers checked before dereference
✅ **Refcount safety**: No overflow/underflow in reference counts
✅ **Integer arithmetic**: No signed/unsigned overflow

### Potential Issues to Find

- Off-by-one errors in loops
- Missing null checks
- Uninitialized variables
- Integer overflows in size calculations

## Limitations

1. **Bounded Verification**: CBMC checks finite execution depths
2. **Stub Dependencies**: External functions (malloc, error, etc.) need stubs
3. **Scalability**: Large functions may not complete in reasonable time
4. **Assumptions**: Must assume reasonable input constraints

## Files to Create

- [ ] `formal-verification/cbmc/README.md` - CBMC verification guide
- [ ] `formal-verification/cbmc/harness_*.c` - Test harnesses
- [ ] `formal-verification/cbmc/stubs.c` - Function stubs
- [ ] `formal-verification/cbmc/verify.sh` - Verification script
- [ ] `formal-verification/results/PHASE3-CBMC-RESULTS.md` - Results

## Integration with C Code

**Option A**: Add assertions with `#ifdef CBMC` guards (non-invasive)

```c
#ifdef CBMC
    __CPROVER_assert(h >= p->mnthash && h < &p->mnthash[MNTHASH],
                     "mnthash bounds");
#endif
```

**Option B**: Separate annotated copies for verification (cleaner)

Keep original code pristine, create `emu/port/pgrp.cbmc.c` with assertions.

## Success Criteria

- [ ] All buffer bounds checks pass
- [ ] All null pointer checks pass
- [ ] All reference count operations verified safe
- [ ] No integer overflows detected
- [ ] Documentation complete with reproducible verification

## References

1. [CBMC User Manual](https://www.cprover.org/cbmc/)
2. [CBMC Tutorial](https://www.cprover.org/cbmc/tutorial/)
3. Target files: `emu/port/pgrp.c`, `emu/port/chan.c`

---

*Document Version: 1.0*
*Status: In Progress*
