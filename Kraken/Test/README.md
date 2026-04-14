# Kraken Assembly Test Suite

This directory contains assembly tests that compare Kraken's x86 semantics
against real execution using GNU assembler.

## Running Tests

```bash
# Run all tests in the asm directory.
python3 Kraken/Test/asm_tests.py Kraken/Test/asm

# Run a single test file.
python3 Kraken/Test/asm_tests.py Kraken/Test/asm/test_arithmetic.S

# Manually inspect Kraken output on an asm file.
./.lake/build/bin/krakenrunner Kraken/Test/asm/arithmetic_test.S 
```
