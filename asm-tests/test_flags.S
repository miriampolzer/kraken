# Test: Flags (ZF, CF, OF) behavior
# Tests various flag-setting operations without pushfq/popq
#
# This test verifies flag behavior for:
# - ZF: set when result is zero
# - CF: set on unsigned overflow/borrow
# - OF: set on signed overflow
#
# Instead of saving flags to registers (which needs pushfq),
# we test flag effects via the final flag state and register values.

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
    # Test 1: ZF set when result is zero
    movq $5, %rax
    subq $5, %rax           # rax = 0, ZF = 1

    # Test 2: Store a value to rbx
    movq $42, %rbx

    # Test 3: CF set on unsigned underflow (borrow)
    movq $1, %rcx
    subq $2, %rcx           # rcx = -1 (0xFFFF...), CF = 1

    # Test 4: Add that doesn't overflow
    movq $10, %rdx
    addq $20, %rdx          # rdx = 30, no special flags

    # Test 5: OF set on signed overflow (positive + positive = negative)
    movq $0x7FFFFFFFFFFFFFFF, %rsi  # MAX_INT64
    addq $1, %rsi           # rsi = MIN_INT64 (0x8000...), OF = 1

    # Final state:
    # rax = 0 (from sub)
    # rbx = 42
    # rcx = 0xFFFFFFFFFFFFFFFF (-1)
    # rdx = 30
    # rsi = 0x8000000000000000 (MIN_INT64)
    # Flags from last instruction: OF = 1

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
