# ACSL Annotations for Inferno Kernel

This directory contains ACSL (ANSI/ISO C Specification Language) annotations for formal verification of the Inferno kernel using Frama-C.

## Prerequisites

### Install Frama-C

**Via OPAM (recommended)**:
```bash
# Install OPAM
brew install opam  # macOS
# OR: apt-get install opam  # Linux

# Initialize
opam init
eval $(opam env)

# Install Frama-C
opam install frama-c
opam install frama-c-wp  # Weakest precondition plugin

# Verify
frama-c -version
```

**Via Docker**:
```bash
docker pull framac/frama-c:latest
```

## Files

- `refcount.h` - ACSL specifications for reference counting
- `pgrp_annotated.c` - ACSL-annotated excerpt from pgrp.c
- `verify.sh` - Automated verification script (requires Frama-C)

## Running Verification

### Using Local Installation

```bash
./verify.sh
```

### Using Docker

```bash
docker run --rm -v $(pwd)/../../:/code framac/frama-c:latest \
    -wp -wp-rte /code/formal-verification/acsl/pgrp_annotated.c
```

## ACSL Annotation Guide

### Function Contracts

```c
/*@
  requires <preconditions>;   // What must be true before call
  ensures <postconditions>;    // What must be true after call
  assigns <modified memory>;   // What memory can be changed
*/
```

### Loop Invariants

```c
/*@
  loop invariant <property>;   // True at loop entry and after each iteration
  loop variant <expression>;   // Decreasing value proving termination
  loop assigns <memory>;       // Memory modified by loop
*/
for(...) { ... }
```

### Assertions

```c
//@ assert <condition>;  // Must be provable at this program point
```

### Ghost Code

```c
/*@  ghost int counter = 0; */  // Variables only for specification
```

## Verification Workflow

1. Add ACSL contracts to function
2. Run WP plugin: `frama-c -wp -wp-rte file.c`
3. Check proof results
4. Add lemmas/assertions for failed proofs
5. Repeat until all obligations proved or documented

## Expected Results

Frama-C will generate proof obligations and attempt to prove them using SMT solvers (Alt-Ergo, Z3, CVC4).

Results appear as:
- **Proved**: Obligation successfully verified
- **Unknown**: Prover timeout or gave up
- **Failed**: Counter-example found (bug or annotation error)

## Limitations

- Complex pointer aliasing may require separation logic
- Exception handling (waserror/poperror) needs modeling
- Some obligations may require manual proof sketches
- Whole-program verification is computationally intensive

## Status

**Phase 4**: Annotations created, awaiting Frama-C installation for verification.

To complete:
```bash
# Install Frama-C (user must run - requires opam)
brew install opam
opam init
opam install frama-c

# Run verification
cd formal-verification/acsl
./verify.sh
```

## References

- [ACSL Reference Manual](https://frama-c.com/html/acsl.html)
- [Frama-C Tutorial](https://frama-c.com/html/tutorial.html)
- [ACSL Examples](https://github.com/fraunhoferfokus/acsl-by-example)
