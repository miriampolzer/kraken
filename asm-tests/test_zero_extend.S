# Test zero-extension move instructions
# Tests: movzbl, movzwl, movzbq with register sources
#
# Note: movz* require register sources in AT&T syntax, not immediates

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
    # ----- movzbl with register source -----
    # Load a value into al, then zero-extend to 32/64-bit
    movq $0x00000000000000AB, %rax   # al = 0xAB
    movq $0xFFFFFFFFFFFFFFFF, %rbx   # Fill rbx with 1s
    movzbl %al, %ebx                 # ebx = 0x000000AB, clears upper 32 bits
    # Expected: rbx = 0x00000000000000AB

    # ----- movzwl with register source -----
    movq $0x000000000000CDEF, %rcx   # cx = 0xCDEF
    movq $0xFFFFFFFFFFFFFFFF, %rdx
    movzwl %cx, %edx                 # edx = 0x0000CDEF, clears upper 32 bits
    # Expected: rdx = 0x000000000000CDEF

    # ----- movzbq with register source -----
    movq $0x00000000000000FF, %rsi   # sil = 0xFF
    movq $0xFFFFFFFFFFFFFFFF, %rdi
    movzbq %sil, %rdi                # rdi = 0x00000000000000FF
    # Expected: rdi = 0x00000000000000FF

    # ----- Test that zero-extend properly clears high bits -----
    movq $0xFFFFFFFFFFFF0042, %r8    # r8b = 0x42
    movq $0xDEADBEEFDEADBEEF, %r9
    movzbl %r8b, %r9d                # r9 = 0x0000000000000042
    # Expected: r9 = 0x42

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
