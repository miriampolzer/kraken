#!/bin/bash
# Run all assembly tests and display results
# Usage: ./run_all_asm_tests.sh [--verbose]

set -e
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR/../asm-tests"

VERBOSE="${1:-}"
PASSED=0
FAILED=0

echo "========================================"
echo "Kraken Assembly Test Suite"
echo "========================================"
echo ""

for test_file in test_*.S; do
    name="${test_file%.S}"
    echo -n "Running $name... "

    # Run the test
    if "$SCRIPT_DIR/run_asm_test.sh" "$test_file" > "/tmp/${name}.bin" 2>/tmp/test_err.txt; then
        size=$(stat -c%s "/tmp/${name}.bin")
        echo "✓ ($size bytes)"
        PASSED=$((PASSED + 1))

        if [ "$VERBOSE" == "--verbose" ]; then
            echo "  Output:"
            xxd "/tmp/${name}.bin" | head -10 | sed 's/^/    /'
            echo ""
        fi
    else
        echo "✗ FAILED"
        FAILED=$((FAILED + 1))
        cat /tmp/test_err.txt | sed 's/^/  /'
    fi
done

echo ""
echo "========================================"
echo "Results: $PASSED passed, $FAILED failed"
echo "========================================"

if [ $FAILED -gt 0 ]; then
    exit 1
fi
