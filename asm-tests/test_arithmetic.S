# Test: Arithmetic Operations
# Tests: addq, subq, adcq, sbbq, negq, decq
#
# Expected results (in rax, rbx, rcx, rdx):
#   rax: 10 + 5 = 15
#   rbx: 20 - 7 = 13
#   rcx: 3 + 2 + CF(0) = 5, then + 1 + CF = 7
#   rdx: result of negq

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
    # Test addq
    movq $10, %rax
    addq $5, %rax           # rax = 15

    # Test subq
    movq $20, %rbx
    subq $7, %rbx           # rbx = 13

    # Test adcq (add with carry)
    xorq %rcx, %rcx         # Clear rcx and CF
    movq $3, %rcx
    addq $2, %rcx           # rcx = 5, CF = 0
    adcq $1, %rcx           # rcx = 5 + 1 + 0 = 6

    # Test negq
    movq $42, %rdx
    negq %rdx               # rdx = -42 (two's complement)

    # Test decq
    movq $100, %rsi
    decq %rsi               # rsi = 99

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
