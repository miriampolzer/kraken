# Test byte swap instructions
# Tests: bswap (64-bit), bswapl (32-bit)

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
    movl $0x01020304, %eax
    bswapl %eax
    # Expected: eax = 0x04030201 (upper 32 bits cleared)

    movl $0xDEADBEEF, %ecx
    bswapl %ecx
    # Expected: ecx = 0xEFBEADDE

    # Test that 32-bit bswap properly zero-extends
    movq $0xFFFFFFFF00000000, %rdx
    movl $0x01020304, %edx           # Clears upper 32 bits
    bswapl %edx
    # Expected: rdx = 0x0000000004030201

    # Done
    movq $60, %rax                   # sys_exit
    xorq %rdi, %rdi                  # exit code 0
    syscall
