/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
.option norvc
.option norelax
.section .text.init,"ax",@progbits
.globl _start
_start:
    csrr t0, mhartid
    la sp, __stack_top
    mv t1, t0
1:  beq t1, zero, 2f
    la t3, __stack_stride
    ld t2, 0(t3)
    add sp, sp, t2
    addi t1, t1, -1
    j 1b
2:  la t1, __trap
    csrw mtvec, t1
    la t1, __boot_ready
    beq t0, zero, 4f
3:  ld t2, 0(t1)
    beq t2, zero, 3b
    fence rw, rw
    j 6f
4:  la t2, __bss_start
    la t3, __bss_end
5:  beq t2, t3, 7f
    sd zero, 0(t2)
    addi t2, t2, 8
    j 5b
7:  fence rw, rw
    li t2, 1
    sd t2, 0(t1)
6:  call main
    j __exit
__trap:
    csrr a0, mcause
    addi a0, a0, 2
__exit:
    la t1, __test_results
    csrr t0, mhartid
    add t0, t0, t0
    add t0, t0, t0
    add t0, t0, t0
    add t1, t1, t0
    addi a0, a0, 1
    sd a0, 0(t1)
    fence rw, rw
.globl __test_halt
__test_halt:
    j __test_halt
.section .data,"aw",@progbits
.balign 8
__boot_ready:
    .dword 0
