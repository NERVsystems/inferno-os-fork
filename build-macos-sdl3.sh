#!/bin/bash
#
# Build InferNode for macOS ARM64 (SDL3 GUI mode)
#

set -e

ROOT="$(cd "$(dirname "$0")" && pwd)"
export ROOT

echo "=== InferNode macOS ARM64 Build (SDL3 GUI) ==="
echo "ROOT=$ROOT"
echo ""

# Check SDL3 is installed
if ! pkg-config --exists sdl3 2>/dev/null; then
    echo "Error: SDL3 not found!"
    echo "Install with: brew install sdl3 sdl3_ttf"
    exit 1
fi

SDL3_VERSION=$(pkg-config --modversion sdl3)
echo "Found SDL3 version: $SDL3_VERSION"

# Set up environment for macOS ARM64
export SYSHOST=MacOSX
export OBJTYPE=arm64
export PATH="$ROOT/MacOSX/arm64/bin:$PATH"
export AWK=awk
export SHELLNAME=sh

echo "Building for: SYSHOST=$SYSHOST OBJTYPE=$OBJTYPE"
echo "GUI Backend: SDL3"
echo ""

# Build emulator
cd "$ROOT/emu/MacOSX"

echo "Cleaning previous build..."
mk clean 2>/dev/null || true

echo "Building SDL3 GUI emulator..."
mk GUIBACK=sdl3

if [ -f o.emu ]; then
    echo ""
    echo "=== Build Successful ==="
    ls -lh o.emu
    file o.emu
    echo ""
    echo "Checking SDL3 dependencies..."
    otool -L o.emu | grep -i sdl
    echo ""
    echo "Emulator: $ROOT/emu/MacOSX/o.emu"
    echo ""
    echo "Test with:"
    echo "  ./o.emu -r../.. wm/wm     # Window manager"
    echo "  ./o.emu -r../.. acme      # Acme editor"
else
    echo "Build failed!"
    exit 1
fi
