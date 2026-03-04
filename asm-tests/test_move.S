# Test: Move and LEA Operations
# Tests: movq, movl (32-bit move with zero-extend), leaq
#
# Expected results:
#   rax: 42
#   rbx: leaq 8(%rax, %rcx, 4) = 42 + 10*4 + 8 = 90
#   rcx: 10
#   rdx: 0x00000000FFFFFFFF (movl zero-extends to 64-bit)

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
    # Test movq (64-bit immediate)
    movq $42, %rax          # rax = 42

    # Test movq (register to register)
    movq $10, %rcx          # rcx = 10

    # Test leaq (address calculation without memory access)
    leaq 8(%rax, %rcx, 4), %rbx  # rbx = 42 + 10*4 + 8 = 90

    # Test movl (32-bit move, zero-extends upper 32 bits)
    movq $0xFFFFFFFFFFFFFFFF, %rdx  # Fill with all 1s
    movl $0xFFFFFFFF, %edx         # movl zeros upper 32 bits

    # Test leaq with just displacement
    leaq 100(%rax), %rsi    # rsi = 42 + 100 = 142

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
