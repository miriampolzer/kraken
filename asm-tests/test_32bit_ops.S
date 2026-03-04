# Test 32-bit arithmetic and bitwise operations
# Tests: addl, subl, negl, xorl, andl, orl
#
# Expected final values:
#   rax: result of xorl %eax, %eax = 0
#   rbx: result of 32-bit ops
#   rcx: 50 (from subl test)

.data
.align 8
final_rax: .quad 0
final_rbx: .quad 0
final_rcx: .quad 0
final_rdx: .quad 0
final_rsi: .quad 0
final_rdi: .quad 0
final_rsp: .quad 0
final_rbp: .quad 0
final_r8: .quad 0
final_r9: .quad 0
final_r10: .quad 0
final_r11: .quad 0
final_r12: .quad 0
final_r13: .quad 0
final_r14: .quad 0
final_r15: .quad 0
final_flags: .quad 0

.text
.globl _start

_start:
    # ----- 32-bit addition (addl) -----
    movl $10, %eax
    movl $5, %ebx
    addl %ebx, %eax
    # Expected: eax = 15

    # Test zero-extension
    movq $0xFFFFFFFFFFFFFFFF, %rcx
    movl $1, %ecx           # Clears upper 32 bits
    addl $1, %ecx
    # Expected: rcx = 2 (zero-extended)

    # ----- 32-bit subtraction (subl) -----
    movl $100, %edx
    subl $50, %edx
    # Expected: edx = 50

    # ----- 32-bit XOR (xorl) -----
    movl $0xAAAAAAAA, %esi
    xorl $0x55555555, %esi
    # Expected: esi = 0xFFFFFFFF

    # Common pattern: xorl %eax, %eax clears register
    xorl %eax, %eax
    # Expected: eax = 0

    # ----- 32-bit AND (andl) -----
    movl $0xFFFF0000, %edi
    andl $0x0000FFFF, %edi
    # Expected: edi = 0

    # ----- 32-bit OR (orl) -----
    movl $0xFF00FF00, %r8d
    orl $0x00FF00FF, %r8d
    # Expected: r8 = 0xFFFFFFFF

    # ----- 32-bit negate (negl) -----
    movl $42, %r9d
    negl %r9d
    # Expected: r9d = -42 (two's complement, zero-extended)

    # ----- 32-bit NOT (notl) -----
    movl $0xAAAAAAAA, %r10d
    notl %r10d
    # Expected: r10d = 0x55555555

    # ----- 32-bit decrement (decl) -----
    movl $100, %r11d
    decl %r11d
    # Expected: r11d = 99

    # ----- 32-bit LEA (leal) -----
    movq $10, %r12
    leal 5(%r12), %r13d
    # Expected: r13 = 15 (zero-extended)

    # ----- 32-bit compare (cmpl) -----
    movl $50, %r14d
    cmpl $50, %r14d
    # Expected: ZF=1

    # ----- 32-bit shift left (shll) -----
    movl $1, %r15d
    shll $4, %r15d
    # Expected: r15d = 16

    jmp _kraken_capture

# ====== KRAKEN CAPTURE EPILOGUE ======
_kraken_capture:
    movq %rax, final_rax(%rip)
    movq %rbx, final_rbx(%rip)
    movq %rcx, final_rcx(%rip)
    movq %rdx, final_rdx(%rip)
    movq %rsi, final_rsi(%rip)
    movq %rdi, final_rdi(%rip)
    movq %rsp, final_rsp(%rip)
    movq %rbp, final_rbp(%rip)
    movq %r8,  final_r8(%rip)
    movq %r9,  final_r9(%rip)
    movq %r10, final_r10(%rip)
    movq %r11, final_r11(%rip)
    movq %r12, final_r12(%rip)
    movq %r13, final_r13(%rip)
    movq %r14, final_r14(%rip)
    movq %r15, final_r15(%rip)
    pushfq
    popq %rax
    movq %rax, final_flags(%rip)

    movq $1, %rax
    movq $1, %rdi
    leaq final_rax(%rip), %rsi
    movq $136, %rdx
    syscall

    movq $60, %rax
    xorq %rdi, %rdi
    syscall
