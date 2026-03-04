# Test 8-bit and 16-bit operations
# Tests: setc, setnc, cmpb, movw, 8-bit register reads via setc/setnc
#
# Per Intel SDM:
# - setc/setnc write a byte (0 or 1) to 8-bit register
# - 16-bit writes (movw) preserve upper 48 bits

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
    # ----- 16-bit register writes preserve upper bits (movw) -----
    movq $0xFFFFFFFFFFFF0000, %rax
    movw $0x1234, %ax
    # Expected: rax = 0xFFFFFFFFFFFF1234 (upper bits preserved)

    # ----- setc: set byte based on carry flag -----
    # First clear rbx completely
    xorq %rbx, %rbx
    # Create carry by overflow
    movq $0xFFFFFFFFFFFFFFFF, %rcx
    addq $1, %rcx                    # Sets CF=1
    setc %bl                         # bl = 1
    # Expected: rbx = 1

    # ----- setnc: set byte based on NOT carry flag -----
    xorq %rdx, %rdx                  # Clear rdx
    xorq %rsi, %rsi
    addq $1, %rsi                    # No carry (0+1=1), CF=0
    setnc %dl                        # dl = 1 (CF=0)
    # Expected: rdx = 1

    # ----- cmpb: 8-bit compare -----
    # Use setc to load 8-bit values first
    movq $100, %rdi
    movq $100, %r8
    cmpb %r8b, %dil                  # Compare low bytes: 100 - 100 = 0, ZF=1
    # ZF should be set

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
