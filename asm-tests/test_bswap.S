# Test byte swap instructions
# Tests: bswapq (64-bit), bswapl (32-bit)
#
# Expected final values:
#   rax: 0x0807060504030201 (bswap of 0x0102030405060708)
#   rbx: 0xBEBAFECAEFBEADDE (bswap of 0xDEADBEEFCAFEBABE)
#   rcx: 0x00000000EFBEADDE (bswapl of 0xDEADBEEF)

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
    # ----- 64-bit byte swap -----
    movq $0x0102030405060708, %rax
    bswapq %rax
    # Expected: rax = 0x0807060504030201

    # Another 64-bit test
    movq $0xDEADBEEFCAFEBABE, %rbx
    bswapq %rbx
    # Expected: rbx = 0xBEBAFECAEFBEADDE

    # ----- 32-bit byte swap -----
    movl $0xDEADBEEF, %ecx
    bswapl %ecx
    # Expected: ecx = 0xEFBEADDE (upper 32 bits cleared)

    # Test that 32-bit bswap properly zero-extends
    movq $0xFFFFFFFF00000000, %rdx
    movl $0x01020304, %edx           # Clears upper 32 bits
    bswapl %edx
    # Expected: rdx = 0x0000000004030201

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
