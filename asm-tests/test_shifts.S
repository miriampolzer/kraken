# Test shift and rotate instructions
# Tests: shl, shr, sar, shld, shrd, rol, ror (64-bit and 32-bit variants)

.text
.globl _start

_start:
    # Setup initial values
    movq $0xFF00FF00FF00FF00, %rax
    movq $0x0000000100000001, %rbx
    movq $4, %rcx                    # Shift count

    # ----- Logical left shift (SHL) -----
    movq %rax, %rdx
    shlq $4, %rdx                    # rax << 4
    # Expected: rdx = 0xF00FF00FF00FF000

    # SHL with register count
    movq %rax, %rdx
    shlq %cl, %rdx                   # rax << 4 (using cl)

    # ----- Logical right shift (SHR) -----
    movq %rax, %rdx
    shrq $4, %rdx                    # rax >> 4
    # Expected: rdx = 0x0FF00FF00FF00FF0

    # ----- Arithmetic right shift (SAR) -----
    movq $0xF000000000000001, %rdx   # Negative number
    sarq $4, %rdx                    # Sign-extend shift
    # Expected: rdx = 0xFF00000000000000 (sign bit propagates)

    # ----- Rotate left (ROL) -----
    movq $0x8000000000000001, %rdx
    rolq $1, %rdx
    # Expected: rdx = 0x0000000000000003 (MSB wraps to LSB)

    # ----- Rotate right (ROR) -----
    movq $0x8000000000000001, %rdx
    rorq $1, %rdx
    # Expected: rdx = 0xC000000000000000 (LSB wraps to MSB)

    # ----- Double-precision shift left (SHLD) -----
    movq $0xAAAAAAAAAAAAAAAA, %rax
    movq $0x5555555555555555, %rbx
    shldq $4, %rbx, %rax
    # Expected: rax = (rax << 4) | (rbx >> 60)

    # ----- Double-precision shift right (SHRD) -----
    movq $0xAAAAAAAAAAAAAAAA, %rax
    movq $0x5555555555555555, %rbx
    shrdq $4, %rbx, %rax
    # Expected: rax = (rax >> 4) | (rbx << 60)

    # ----- 32-bit shift variants -----
    movl $0xFF00FF00, %eax
    shll $4, %eax                    # 32-bit shift left
    # Expected: eax = 0xF00FF000

    movl $0xFF00FF00, %eax
    shrl $4, %eax                    # 32-bit logical shift right
    # Expected: eax = 0x0FF00FF0

    # ----- 32-bit rotate variants -----
    movl $0x80000001, %eax
    roll $1, %eax                    # 32-bit rotate left
    # Expected: eax = 0x00000003

    movl $0x80000001, %eax
    rorl $1, %eax                    # 32-bit rotate right
    # Expected: eax = 0xC0000000

    # Done
    movq $60, %rax                   # sys_exit
    xorq %rdi, %rdi                  # exit code 0
    syscall
