# Test shift and rotate instructions
# Tests: shlq, shrq, sarq, rolq, rorq (64-bit)
#
# Avoiding shld/shrd and 32-bit variants for now (parser may not support)

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
    # ----- Logical left shift (SHL) -----
    movq $0x00FF00FF00FF00FF, %rax
    shlq $4, %rax                    # rax << 4
    # Expected: rax = 0x0FF00FF00FF00FF0

    # ----- Logical right shift (SHR) -----
    movq $0xFF00FF00FF00FF00, %rbx
    shrq $4, %rbx                    # rbx >> 4
    # Expected: rbx = 0x0FF00FF00FF00FF0

    # ----- Arithmetic right shift (SAR) -----
    movq $0xF000000000000010, %rcx   # Negative number (MSB set)
    sarq $4, %rcx                    # Sign-extend shift
    # Expected: rcx = 0xFF00000000000001 (sign bit propagates)

    # ----- Rotate left (ROL) -----
    movq $0x8000000000000001, %rdx
    rolq $1, %rdx
    # Expected: rdx = 0x0000000000000003 (MSB wraps to LSB)

    # ----- Rotate right (ROR) -----
    movq $0x8000000000000001, %rsi
    rorq $1, %rsi
    # Expected: rsi = 0xC000000000000000 (LSB wraps to MSB)

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
