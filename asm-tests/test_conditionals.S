# Test conditional and stack operations
# Tests: setc, setnc, cmovc, cmove, test, push, pop

.text
.globl _start

_start:
    # ----- TEST instruction -----
    movq $0xFF, %rax
    testq %rax, %rax                 # Sets ZF=0 (non-zero)

    xorq %rax, %rax
    testq %rax, %rax                 # Sets ZF=1 (zero)

    # ----- SETC / SETNC (set byte on carry) -----
    # First, create carry condition
    movq $0xFFFFFFFFFFFFFFFF, %rax
    addq $1, %rax                    # Overflow sets CF
    setc %cl                         # cl = 1 (CF was set)

    xorq %rax, %rax
    addq $1, %rax                    # No overflow
    setc %dl                         # dl = 0 (CF not set)
    setnc %bl                        # bl = 1 (CF not set)

    # ----- CMOVE (conditional move on equal/zero) -----
    movq $100, %rax
    movq $200, %rbx
    cmpq %rax, %rax                  # Sets ZF (equal)
    cmovzq %rbx, %rax                # rax = 200 (because ZF=1)

    movq $100, %rax
    movq $200, %rbx
    cmpq $50, %rax                   # Clears ZF (not equal)
    cmoveq %rbx, %rax                # rax unchanged (ZF=0)
    # Expected: rax = 100

    # ----- CMOVC (conditional move on carry) -----
    movq $0xFFFFFFFFFFFFFFFF, %rax
    movq $999, %rbx
    addq $1, %rax                    # Sets CF
    cmovcq %rbx, %rax                # rax = 999 (because CF=1)

    # ----- PUSH / POP -----
    movq $0xDEADBEEF, %rax
    pushq %rax                       # Push value to stack
    movq $0, %rax                    # Clear rax
    popq %rax                        # Restore from stack
    # Expected: rax = 0xDEADBEEF

    # Multiple push/pop
    pushq $100
    pushq $200
    pushq $300
    popq %rax                        # rax = 300
    popq %rbx                        # rbx = 200
    popq %rcx                        # rcx = 100

    # Done
    movq $60, %rax                   # sys_exit
    xorq %rdi, %rdi                  # exit code 0
    syscall
