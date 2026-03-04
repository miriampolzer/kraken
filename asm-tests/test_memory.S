# Test: Memory Operands
# Tests: memory load/store with displacement, index, scale
#
# Uses a test buffer and verifies memory reads/writes

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

# Memory region tracking
mem_region_count: .quad 1
mem_region_0_base: .quad test_buffer
mem_region_0_size: .quad 4
mem_region_0_data: .space 32

# Test buffer for memory operations
test_buffer:
.quad 0
.quad 0
.quad 0
.quad 0

.text
.globl _start
_start:
    # Get address of test buffer
    leaq test_buffer(%rip), %rdi

    # Test: store with just base register
    movq $100, (%rdi)           # buffer[0] = 100

    # Test: store with displacement
    movq $200, 8(%rdi)          # buffer[1] = 200

    # Test: store with index and scale
    movq $2, %rcx               # index = 2
    movq $300, (%rdi, %rcx, 8)  # buffer[2] = 300

    # Test: store with base + index + scale + displacement
    movq $1, %rcx
    movq $400, 8(%rdi, %rcx, 8)  # buffer[1+1] = buffer[2] (wait, this overwrites)
    # Actually: 8 + 1*8 = 16, so buffer[2] = 400
    # Let's fix: use index 0 with disp 24
    movq $3, %rcx
    movq $400, (%rdi, %rcx, 8)   # buffer[3] = 400

    # Test: load from memory
    movq (%rdi), %rax           # rax = 100
    movq 8(%rdi), %rbx          # rbx = 200

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

    # Copy memory region
    movq mem_region_0_base(%rip), %rsi
    leaq mem_region_0_data(%rip), %rdi
    movq $4, %rcx
    rep movsq

    # Write registers (136 bytes)
    movq $1, %rax
    movq $1, %rdi
    leaq final_rax(%rip), %rsi
    movq $136, %rdx
    syscall

    # Write memory region (8 + 16 + 32 = 56 bytes)
    movq $1, %rax
    movq $1, %rdi
    leaq mem_region_count(%rip), %rsi
    movq $56, %rdx
    syscall

    movq $60, %rax
    xorq %rdi, %rdi
    syscall
