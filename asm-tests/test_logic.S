# Test: Logical Operations
# Tests: xorq, andq, orq
#
# Expected results:
#   rax: 0xFF00 XOR 0x0F0F = 0xF00F
#   rbx: 0xFF00 AND 0x0F0F = 0x0F00
#   rcx: 0xFF00 OR 0x0F0F = 0xFF0F
#   rdx: XOR with self = 0

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
    # Test xorq
    movq $0xFF00, %rax
    xorq $0x0F0F, %rax      # rax = 0xF00F

    # Test andq
    movq $0xFF00, %rbx
    andq $0x0F0F, %rbx      # rbx = 0x0F00

    # Test orq
    movq $0xFF00, %rcx
    orq $0x0F0F, %rcx       # rcx = 0xFF0F

    # Test xorq for zeroing (common idiom)
    movq $12345, %rdx
    xorq %rdx, %rdx         # rdx = 0, ZF = 1

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
