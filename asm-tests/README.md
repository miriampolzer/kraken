# Kraken Assembly Test Suite

This directory contains assembly tests that compare Kraken's x86 semantics
against real execution using GNU assembler.

## Running Tests

```bash
# Run all tests
../scripts/run_all_asm_tests.sh

# Run a single test
../scripts/run_asm_test.sh test_arithmetic.S --hex
```

## Test Coverage

| File | Instructions Tested |
|------|---------------------|
| test_arithmetic.S | add, sub, adc, sbb, neg, dec |
| test_multiply.S | mul, imul, mulx |
| test_logic.S | xor, and, or |
| test_move.S | mov, movl, lea |
| test_memory.S | memory operands with displacement/index/scale |
| test_flags.S | flag-setting behaviors (ZF, CF, OF) |
| test_jumps.S | jmp, conditional jumps |

## Output Format

Each test outputs 136+ bytes:
- Bytes 0-127: 16 registers (8 bytes each)
- Bytes 128-135: Flags (RFLAGS)
- Bytes 136+: Memory regions (if any)
