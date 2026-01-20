#!/bin/bash
#
# Frama-C ACSL Verification Script
#
# Runs Frama-C WP plugin on ACSL-annotated code.
#

set -e

echo "=== Inferno Kernel ACSL Verification ==="

# Check if Frama-C is installed
if ! command -v frama-c &> /dev/null; then
    echo "❌ Frama-C not installed"
    echo ""
    echo "To install:"
    echo "  brew install opam"
    echo "  opam init"
    echo "  eval \$(opam env)"
    echo "  opam install frama-c"
    echo ""
    exit 1
fi

echo "Frama-C Version: $(frama-c -version | head -1)"
echo ""

cd "$(dirname "$0")"

echo "----------------------------------------"
echo "Verifying: pgrp_annotated.c"
echo "----------------------------------------"

# Run Frama-C WP plugin
frama-c -wp -wp-rte \
    -wp-prover alt-ergo,why3 \
    -wp-timeout 30 \
    -wp-verbose 0 \
    -wp-report wp-report.txt \
    pgrp_annotated.c \
    2>&1 | tee frama-c-output.log

echo ""
echo "----------------------------------------"
echo "Verification Report"
echo "----------------------------------------"

# Parse results
if grep -q "Everything (.*) Valid" wp-report.txt 2>/dev/null; then
    echo "✅ ALL PROOF OBLIGATIONS VERIFIED"
elif grep -q "Proved" wp-report.txt 2>/dev/null; then
    PROVED=$(grep -c "Proved" wp-report.txt || echo 0)
    TOTAL=$(grep -c "Goal" wp-report.txt || echo 0)
    echo "✅ Proved: $PROVED / $TOTAL obligations"
    echo ""
    echo "See wp-report.txt for details"
else
    echo "⚠️  Verification results unclear"
    echo "See wp-report.txt and frama-c-output.log"
fi

echo ""
echo "Detailed report: wp-report.txt"
echo "Full output: frama-c-output.log"
