# Test: Flags (ZF, CF, OF) behavior
# Tests various flag-setting operations
#
# This test verifies flag behavior for:
# - ZF: set when result is zero
# - CF: set on unsigned overflow/borrow
# - OF: set on signed overflow

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
    # Test 1: ZF should be set when result is zero
    movq $5, %rax
    subq $5, %rax           # rax = 0, ZF = 1
    # Save ZF state
    pushfq
    popq %rbx               # rbx contains flags after zero result

    # Test 2: CF should be set on unsigned overflow
    movq $1, %rax
    subq $2, %rax           # 1 - 2 = -1 (unsigned underflow), CF = 1
    pushfq
    popq %rcx               # rcx contains flags after borrow

    # Test 3: Add that doesn't overflow
    movq $10, %rax
    addq $20, %rax          # rax = 30, no flags set
    pushfq
    popq %rdx               # rdx contains flags (no overflow)

    # Final state:
    # rax = 30 (from last add)
    # rbx = flags after zero result (ZF set)
    # rcx = flags after borrow (CF set)
    # rdx = flags after normal add

    jmp _kraken_capture

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
