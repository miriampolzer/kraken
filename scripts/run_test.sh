#!/bin/bash
# Kraken Test Harness Runner
# Usage: ./run_test.sh <test.S> [--hex]
#
# This script assembles, links, executes an assembly file and captures
# the final register/flag state (136 bytes written to stdout).
#
# The assembly file should be wrapped with Kraken's capture infrastructure
# (using TestHarness.wrapAssembly or TestHarness.makeTestProgram).
#
# Prerequisites: GNU assembler (as), linker (ld)

set -e

if [ $# -lt 1 ]; then
    echo "Usage: $0 <test.S> [--hex]"
    echo ""
    echo "Options:"
    echo "  --hex     Show output as hex dump (default: raw binary to stdout)"
    echo ""
    echo "The assembly should end by jumping to _kraken_capture (or falling"
    echo "through to it) to trigger state capture and output."
    exit 1
fi

ASM_FILE="$1"
HEX_MODE="${2:-}"
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

OBJ_FILE="$TMPDIR/test.o"
EXE_FILE="$TMPDIR/test"
OUT_FILE="$TMPDIR/output.bin"

# Assemble
echo "Assembling $ASM_FILE..." >&2
as -o "$OBJ_FILE" "$ASM_FILE"

# Link
echo "Linking..." >&2
ld -o "$EXE_FILE" "$OBJ_FILE"

# Run and capture stdout (136 bytes of binary data)
echo "Running test..." >&2
"$EXE_FILE" > "$OUT_FILE"

# Display output
if [ "$HEX_MODE" == "--hex" ]; then
    echo "" >&2
    echo "Final state (hex dump):" >&2
    echo "Offset   0-7: rax,  8-15: rbx, 16-23: rcx, 24-31: rdx" >&2
    echo "Offset 32-39: rsi, 40-47: rdi, 48-55: rsp, 56-63: rbp" >&2
    echo "Offset 64-71: r8,  72-79: r9,  80-87: r10, 88-95: r11" >&2
    echo "Offset 96-103: r12, 104-111: r13, 112-119: r14, 120-127: r15" >&2
    echo "Offset 128-135: flags (RFLAGS)" >&2
    echo "" >&2
    xxd "$OUT_FILE"
else
    # Output raw binary (can be piped to parser)
    cat "$OUT_FILE"
fi

echo "" >&2
echo "Success! Output size: $(stat -c%s "$OUT_FILE") bytes" >&2
