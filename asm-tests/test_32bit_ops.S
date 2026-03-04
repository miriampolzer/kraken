# Test 32-bit arithmetic and bitwise operations
# Tests: addl, subl, negl, notl, decl, xorl, andl, orl, cmpl

.text
.globl _start

_start:
    # ----- 32-bit addition (addl) -----
    movl $0x7FFFFFFF, %eax           # Max positive int32
    movl $0x00000001, %ebx
    addl %ebx, %eax
    # Expected: eax = 0x80000000 (wraps)

    # Test zero-extension
    movq $0xFFFFFFFFFFFFFFFF, %rax
    movl $0x00000001, %eax           # Clears upper 32 bits
    addl $1, %eax
    # Expected: rax = 0x0000000000000002

    # ----- 32-bit subtraction (subl) -----
    movl $100, %eax
    movl $50, %ebx
    subl %ebx, %eax
    # Expected: eax = 50

    # ----- 32-bit negate (negl) -----
    movl $42, %eax
    negl %eax
    # Expected: eax = -42 (0xFFFFFFD6)

    # ----- 32-bit NOT (notl) -----
    movl $0xFF00FF00, %eax
    notl %eax
    # Expected: eax = 0x00FF00FF

    # ----- 32-bit decrement (decl) -----
    movl $10, %eax
    decl %eax
    # Expected: eax = 9

    # ----- 32-bit XOR (xorl) -----
    movl $0xAAAAAAAA, %eax
    movl $0x55555555, %ebx
    xorl %ebx, %eax
    # Expected: eax = 0xFFFFFFFF

    # Common pattern: xorl %eax, %eax clears register
    xorl %eax, %eax
    # Expected: eax = 0

    # ----- 32-bit AND (andl) -----
    movl $0xFFFF0000, %eax
    movl $0x0000FFFF, %ebx
    andl %ebx, %eax
    # Expected: eax = 0x00000000

    # ----- 32-bit OR (orl) -----
    movl $0xFF00FF00, %eax
    movl $0x00FF00FF, %ebx
    orl %ebx, %eax
    # Expected: eax = 0xFFFFFFFF

    # ----- 32-bit compare (cmpl) -----
    movl $100, %eax
    movl $100, %ebx
    cmpl %ebx, %eax
    # ZF should be set (equal)

    movl $50, %eax
    cmpl %ebx, %eax
    # CF should be set (below), ZF clear

    # Done
    movq $60, %rax                   # sys_exit
    xorq %rdi, %rdi                  # exit code 0
    syscall
