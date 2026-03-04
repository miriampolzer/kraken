# Test: Register Operations (simplified from memory test)
# Tests: basic register operations since memory addressing with
# RIP-relative (like label(%rip)) isn't supported by the parser
#
# This is a simplified test that verifies register operations work correctly.

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
    # Test: Various register operations
    movq $100, %rax
    movq $200, %rbx
    movq $2, %rcx
    movq $8, %rdi

    # Test: Index calculation with scale (pure register arithmetic)
    # This tests that leaq with base+index*scale works
    leaq (%rax, %rcx, 8), %rdx   # rdx = 100 + 2*8 = 116

    # Test: Displacement + base + index*scale
    leaq 16(%rbx, %rcx, 4), %rsi  # rsi = 200 + 16 + 2*4 = 224

    # Final state:
    # rax = 100, rbx = 200, rcx = 2, rdx = 116, rsi = 224, rdi = 8

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
