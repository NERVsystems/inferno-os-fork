#!/bin/bash
#
# Build InferNode for macOS ARM64 (Headless mode)
#

set -e

ROOT="$(cd "$(dirname "$0")" && pwd)"
export ROOT

echo "=== InferNode macOS ARM64 Build (Headless) ==="
echo "ROOT=$ROOT"
echo ""

# Set up environment for macOS ARM64
export SYSHOST=MacOSX
export OBJTYPE=arm64
export PATH="$ROOT/MacOSX/arm64/bin:$PATH"
export AWK=awk
export SHELLNAME=sh

echo "Building for: SYSHOST=$SYSHOST OBJTYPE=$OBJTYPE"
echo "GUI Backend: headless (no display)"
echo ""

# Rebuild libinterp if any source files changed
LIBINTERP="$ROOT/MacOSX/arm64/lib/libinterp.a"
NEED_REBUILD=0

# Check if library exists and compare timestamps
if [ ! -f "$LIBINTERP" ]; then
    NEED_REBUILD=1
else
    for src in "$ROOT/libinterp"/*.c; do
        if [ "$src" -nt "$LIBINTERP" ]; then
            NEED_REBUILD=1
            break
        fi
    done
fi

if [ "$NEED_REBUILD" = "1" ]; then
    echo "Rebuilding libinterp..."
    cd "$ROOT/libinterp"

    # Clean old objects
    rm -f *.o

    # Compile files for ARM64 (matching mkfile OFILES)
    CFLAGS="-g -O2 -fno-strict-aliasing -fno-omit-frame-pointer -Wuninitialized -Wunused-variable -Wreturn-type -Wimplicit -I../MacOSX/arm64/include -I../include -fcommon"

    # These are the files in OFILES from mkfile with $OBJTYPE=arm64
    SOURCES="alt.c comp-arm64.c conv.c crypt.c dec.c draw.c gc.c geom.c heap.c heapaudit.c ipint.c link.c load.c math.c raise.c readmod.c runt.c sign.c stack.c validstk.c xec.c das-arm64.c keyring.c string.c"

    for src in $SOURCES; do
        if [ -f "$src" ]; then
            obj="${src%.c}.o"
            echo "  CC $src"
            gcc -c $CFLAGS "$src" -o "$obj" || exit 1
        fi
    done

    # Update the library archive
    echo "  AR libinterp.a"
    ar rv "$LIBINTERP" *.o >/dev/null
    rm -f *.o

    echo "libinterp rebuilt."
    echo ""
fi

# Build emulator
cd "$ROOT/emu/MacOSX"

echo "Cleaning previous build..."
mk clean 2>/dev/null || true

echo "Building headless emulator..."
mk GUIBACK=headless

if [ -f o.emu ]; then
    echo ""
    echo "=== Build Successful ==="
    ls -lh o.emu
    file o.emu
    echo ""
    echo "Checking for SDL dependencies..."
    otool -L o.emu | grep -i sdl || echo "  ✓ No SDL dependencies (correct for headless)"
    echo ""
    echo "Emulator: $ROOT/emu/MacOSX/o.emu"
    echo "Run with: ./o.emu -r../.."
else
    echo "Build failed!"
    exit 1
fi
