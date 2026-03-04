#!/bin/bash
# Run a single assembly test comparing AS execution against Kraken's eval
# Usage: ./run_asm_test.sh <test.S>
#
# Flow:
#   1. Assemble and link the test with GNU as/ld
#   2. Run to capture final register state (136 bytes)
#   3. Call krakentest to compare AS result against Kraken's eval
#   4. Report PASS/FAIL

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
KRAKEN_ROOT="$SCRIPT_DIR/.."
KRAKENTEST="$KRAKEN_ROOT/.lake/build/bin/krakentest"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <test.S>"
    exit 1
fi

ASM_FILE="$1"
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# Check krakentest exists
if [ ! -x "$KRAKENTEST" ]; then
    echo "Error: krakentest not found. Run 'lake build krakentest' first."
    exit 1
fi

# Step 1: Assemble and link
as -o "$TMPDIR/test.o" "$ASM_FILE" 2>/dev/null || {
    echo "FAIL: Assembly failed for $ASM_FILE"
    exit 1
}

ld -o "$TMPDIR/test" "$TMPDIR/test.o" 2>/dev/null || {
    echo "FAIL: Linking failed for $ASM_FILE"
    exit 1
}

# Step 2: Run and capture output (136 bytes: registers + flags)
"$TMPDIR/test" > "$TMPDIR/output.bin" 2>/dev/null || true

# Check we got enough output
if [ ! -f "$TMPDIR/output.bin" ] || [ $(stat -c%s "$TMPDIR/output.bin") -lt 136 ]; then
    echo "FAIL: Test execution didn't produce expected output"
    exit 1
fi

# Step 3: Run krakentest to compare AS vs Kraken
"$KRAKENTEST" "$ASM_FILE" "$TMPDIR/output.bin"
