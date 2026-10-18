/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
.option norvc
.option norelax
.section .text,"ax",@progbits
.globl main
main:
    la t0, __console_bss_probe
    ld t0, 0(t0)
    beq t0, zero, .Lbody
    li a0, 1
    ret
.Lbody:
    addi sp, sp, -16
    sd ra, 8(sp)
    la a0, prefix
    call console_put_words
    csrr a0, mhartid
    li t0, 0
    li t1, 10
1:  beq a0, t0, 2f
    addi t0, t0, 1
    beq t0, t1, 3f
    j 1b
2:  addi a0, a0, 48
    j 4f
3:  addi a0, a0, 87
4:  call console_putc
    la a0, suffix
    call console_put_words
    li a0, 0
    ld ra, 8(sp)
    addi sp, sp, 16
    ret
.section .rodata,"a",@progbits
.balign 4
prefix:
    .word 104, 97, 114, 116, 32, 0
suffix:
    .word 32, 111, 110, 108, 105, 110, 101, 10, 0
.section .bss,"aw",@nobits
.balign 8
.globl __console_bss_probe
__console_bss_probe:
    .zero 8
