# ARM64 JIT Exit Crash Investigation

**Date:** January 18, 2026
**Branch:** feature/jit-64bit
**Status:** Root cause identified, fix not yet implemented

## Summary

Investigation into why ARM64 JIT-compiled programs crash on exit. The JIT works correctly for most operations (echo, cat, sh all function properly) but crashes with SEGV when the program attempts to exit.

## Problem Description

When running programs with JIT enabled (`-c4` flag), the emulator crashes with:
```
[Emuinit] Broken: "invalid mframe"
```

The crash occurs in `mframe()` function in `libinterp/xec.c` at line 390, where `t->size` is accessed but `t` contains garbage (a frame pointer instead of a Type pointer).

## What Was Tried

### 1. Debug Output Enhancement
Added extensive debug output to trace the problem:

**In `comp-arm64.c`:**
- Added IMFRAME debug to show source/destination addressing modes
- Added IFRAME debug to show destination operand details
- Added punt THREOP debug to show middle operand addressing

```c
// IMFRAME debug
if(cflag > 2 && pass)
    print("IMFRAME: src add=0x%x UXSRC=0x%x s.ind=%lld add&ARM=0x%x reg=%d d.ind=%lld\n",
        i->add, UXSRC(i->add), (vlong)i->s.ind, i->add & ARM, i->reg, (vlong)i->d.ind);

// IFRAME debug
if(cflag > 2 && pass)
    print("IFRAME: dst add=0x%x UXDST=0x%x d.ind=%lld d.i.f=%d d.i.s=%d\n",
        i->add, UXDST(i->add), (vlong)i->d.ind, i->d.i.f, i->d.i.s);

// punt THREOP debug
if(cflag > 3 && pass && (m & THREOP))
    print("punt THREOP: add&ARM=0x%x reg=%d\n", i->add & ARM, i->reg);
```

### 2. Register Save Order Investigation
Reordered the register save/restore in `punt()` to happen before debug output. This ensures X9-X12 (RFP, RMP, RREG, RM) are preserved across debug function calls.

### 3. Type Map Offset Fix
Fixed potential issue in `comd()` and `comi()` where pointer map iteration used `i << 5` (multiply by 32) but should use `i * 8 * sizeof(WORD)` (64 bytes per map byte on 64-bit).

## What Worked

1. **Debug output** successfully captured the crash sequence
2. **JIT compilation** itself is correct - instructions are generated properly
3. **Most program execution** works fine (echo, cat, sh all function)

## What Didn't Work

1. The exit crash persists despite the fixes attempted
2. The type map offset fix didn't resolve the crash (it may be unrelated)

## Root Cause Analysis

### The Crash Sequence

From debug output (`/tmp/jit_debug2.out`):

```
JIT punt: R.s=104d95f20 *R.s=104d95f28 R.m=104cbca40 R.t=4 &R.t=104cbca40
  &R=104cbc9e0 R.FP=104d95e48 R.MP=104e30cb0
JIT punt: R.s=104d95f20 *R.s=104d95f28 R.m=104cbca40 R.t=4376956848 &R.t=104cbca40
  &R=104cbc9e0 R.FP=104d95e48 R.MP=104e30cb0
mframe: R.s=104d95f20 *R.s=104d95f28 ml=104d95f28 o=81989552
  R.MP=104e30cb0 R.M=104e30c30 R.M->MP=104e30cb0
  R.s-R.MP=-634256 ml->nlinks=320
[Emuinit] Broken: "invalid mframe"
```

### Key Observations

1. **Two consecutive punts** with same R.s address (104d95f20)
2. **First punt:** R.t=4 (valid small index)
3. **Second punt:** R.t=4376956848 (garbage - looks like an address)
4. **R.s offset:** R.s = FP + 216 (since R.s - R.FP = 104d95f20 - 104d95e48 = 216 + 56 = 0xD8)

### The Problem

The memory location at FP+216 is being used for two incompatible purposes:

1. **IFRAME** writes a `Frame*` to FP+216:
   ```
   IFRAME: dst add=0x11 UXDST=0x1 d.ind=216 d.i.f=216 d.i.s=0
   ```

2. **IMFRAME** (or mframe) later reads from FP+216 expecting a `Modlink**`:
   - When mframe() executes `ml = T(s)` (i.e., `ml = *(Modlink**)R.s`)
   - It gets the Frame* that IFRAME stored, not a Modlink*
   - `ml->nlinks` returns garbage (320 = 0x140, likely reading frame data)

### Why This Happens

The Dis VM has two frame-related instructions:

- **IFRAME** - Allocates a new frame and stores Frame* to destination
- **IMFRAME** - Allocates a module frame, reads Modlink** from source

These instructions can use the same stack slot (FP+offset) for different purposes at different points in execution. The interpreter handles this because it processes instructions sequentially. However, the JIT may be:

1. Processing instructions from multiple modules
2. Not capturing the full instruction sequence that shows the conflict
3. Or there's a register corruption issue where R.s gets set incorrectly

## Addressing Mode Reference

From `include/isa.h`:
```c
#define ARM     0xC0    /* Mask for middle operand addressing */
#define AXNON   0x00    /* No middle operand */
#define AXIMM   0x40    /* Immediate value in reg field */
#define AXINF   0x80    /* Indirect FP-relative */
#define AXINM   0xC0    /* Indirect MP-relative */
```

Source/Destination addressing (UXSRC/UXDST):
- 0x0 = MP-relative
- 0x1 = FP-relative
- 0x2 = Immediate (for source)

## REG Structure Offsets

```c
struct REG {
    void*    PC;   // 0
    uchar*   MP;   // 8
    uchar*   FP;   // 16
    uchar*   SP;   // 24
    uchar*   TS;   // 32
    uchar*   EX;   // 40
    Modlink* M;    // 48
    int      IC;   // 56
    WORD*    xpc;  // 64
    WORD*    s;    // 72
    WORD*    d;    // 80
    WORD*    m;    // 88
    WORD     t;    // 96
    void*    st;   // 104
    void*    dt;   // 112
};
```

## Files Modified

1. **libinterp/comp-arm64.c**
   - Added debug output for IMFRAME, IFRAME, punt THREOP
   - Reordered register save to happen before debug calls
   - Fixed type map offset calculation in comd()/comi()

## Next Steps to Fix

1. **Investigate R.s assignment** - Find where R.s is being set to FP+216 for an IMFRAME
2. **Check for cross-module issues** - The debug only shows Emuinit compilation, but crash may involve another module
3. **Add more tracing** - Trace which instruction sets R.s immediately before mframe() crash
4. **Consider alternative fix** - May need to validate R.s contents before mframe() executes

## Lessons Learned

1. **Stack slot reuse** - The same frame slot can hold different pointer types at different execution points
2. **Multi-module complexity** - JIT compilation traces may not show all relevant modules
3. **Caller-saved registers** - Debug functions can corrupt X9-X12 unless saved first
4. **Debug output is essential** - The detailed punt/mframe traces were crucial for understanding the crash

## Related Documentation

- `docs/ARM64-JIT-ANALYSIS.md` - Overall JIT architecture analysis
- `docs/DEBUGGING-NOTES.md` - General debugging notes
- Commit `1c2eb2a` - Previous analysis of C code corrupting caller-saved registers
