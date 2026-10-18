/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
.option norvc
.option norelax
.section .text,"ax",@progbits
.globl console_putc
console_putc:
    csrr t0, mhartid
    la t1, __console_base
    add t0, t0, t0
    add t0, t0, t0
    add t1, t1, t0
    sw a0, 0(t1)
    ret
.globl console_put_words
console_put_words:
    addi sp, sp, -16
    sd ra, 8(sp)
    sd s0, 0(sp)
    mv s0, a0
3:  lw a0, 0(s0)
    beq a0, zero, 4f
    call console_putc
    addi s0, s0, 4
    j 3b
4:  ld s0, 0(sp)
    ld ra, 8(sp)
    addi sp, sp, 16
    ret
