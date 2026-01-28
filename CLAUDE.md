# Infernode - Development Guide for Claude

This guide ensures Claude Code works correctly with the Infernode (Inferno OS) codebase.

## Building Limbo Code

**Always use Inferno's native build tools from macOS**, not Plan 9 Port or commands inside Inferno. This ensures the build environment is compatible with the target Inferno system - the same compiler and mk that ship with Inferno are used to build code that runs on Inferno.

### Environment Setup

From the project root, set these environment variables:
```sh
export ROOT=$PWD
export PATH=$PWD/MacOSX/arm64/bin:$PATH
```

The native tools are located at:
- `MacOSX/arm64/bin/mk` - Plan 9 mk (Inferno's build tool)
- `MacOSX/arm64/bin/limbo` - Limbo compiler

### Build Commands

Build from macOS terminal (not inside Inferno):

```sh
# Build tests
cd tests
mk install

# Clean and rebuild
mk nuke
mk install

# Build a specific directory
cd appl/lib
mk testing.dis
```

### Why Native Tools?

Using Inferno's native mk and limbo ensures:
1. **Compatibility** - Same toolchain that built Inferno builds your code
2. **Correct SHELLTYPE** - mkconfig uses `SHELLTYPE=sh` for macOS /bin/sh
3. **No PATH conflicts** - Avoids mixing Plan 9 Port tools with Inferno tools

Do NOT:
- Run `mk` inside Inferno (SHELLTYPE mismatch)
- Use Plan 9 Port's mk (may have subtle incompatibilities)
- Use bash-isms like `&&` to chain commands (use `;` or separate commands)

## Inferno Shell Differences

The Inferno shell is rc-style, not POSIX sh:
- No `&&` operator - use `;` or separate commands
- `for` loops: `for i in $list { commands }` not `for i in $list; do ... done`
- Different quoting rules

## Test Files

All Limbo tests use the testing framework with clickable error addresses:
- Add `SRCFILE: con "/tests/mytest.b";` after global counters
- Use `testing->newTsrc(name, SRCFILE)` in the run() helper
- See `tests/example_test.b` as the reference template

## Project Structure

```
infernode/
├── MacOSX/arm64/bin/    # Native build tools (mk, limbo, emu)
├── appl/                # Limbo application source
├── module/              # Limbo module interfaces (.m files)
├── tests/               # Limbo unit tests
├── dis/                 # Compiled Dis bytecode
├── mkfiles/             # Shared mk rules
└── mkconfig             # Build configuration
```
