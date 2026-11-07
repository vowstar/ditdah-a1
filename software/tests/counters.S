/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
.option norvc
.option norelax
.section .text,"ax",@progbits
.globl main
main:
    addi sp, sp, -32
    sd ra, 0(sp)
    sd s1, 8(sp)
    sd s2, 16(sp)
    sd s3, 24(sp)
    csrw mscratch, sp
    csrr s2, mtvec
    la t0, .Lmachine_trap
    csrw mtvec, t0
    li t0, -1
    csrw pmpaddr0, t0
    li t0, 15
    csrw pmpcfg0, t0
    li t0, 13
    csrw 0x320, t0
    li t0, 17
    csrw 0xb00, t0
    csrr t1, cycle
    bne t0, t1, .Lfailed
    csrw 0xb02, zero
    li t0, 1
    csrw 0x320, t0
.globl counter_measure_begin
counter_measure_begin:
    addi t1, zero, 11
    addi t2, zero, 12
    addi t3, zero, 13
    csrr t4, instret
    li t5, 3
    bne t4, t5, .Lfailed
    csrw 0x320, zero
    li t0, 15
    csrw 0x306, t0
    csrw 0x106, t0
    li t0, 1
    slli t0, t0, 63
    csrw 0x30a, t0
    li t0, 1
    slli t0, t0, 62
    ori t0, t0, 1
    csrw 0x323, t0
    li t0, 0x100000001
    csrw 0xb03, t0
    csrr t1, 0xb03
    bne t0, t1, .Lfailed
    li t0, -16
    csrw 0xb03, t0
    li t0, 0x2020
    csrw mideleg, t0
    la t0, .Lsupervisor_trap
    csrw stvec, t0
    li s1, 0
    li s3, 0
    li a2, 0
    la t0, .Lsupervisor
    csrw mepc, t0
    li t0, 0x1800
    csrc mstatus, t0
    li t0, 0x800
    csrs mstatus, t0
    mret
.Lsupervisor:
    csrr t0, time
    li t1, 4096
    add t0, t0, t1
    csrw 0x14d, t0
    li t0, 0x2020
    csrw sie, t0
    csrsi sstatus, 2
.globl counter_wait
counter_wait:
    csrci sstatus, 2
    bne a2, zero, .Lchecked
    beq s3, zero, .Lchecked
    li a2, 1
    li a0, 2
    ecall
.Lchecked:
    li t0, 2
    bne s1, t0, .Lwait
    bne s3, t0, .Lwait
    li a0, 0
    ecall
.Lwait:
    wfi
    csrsi sstatus, 2
    j counter_wait
.Lsupervisor_trap:
    addi sp, sp, -16
    sd t0, 0(sp)
    sd t1, 8(sp)
    csrr t0, scause
    li t1, 0x8000000000000005
    beq t0, t1, .Ltimer
    li t1, 0x800000000000000d
    bne t0, t1, .Lsupervisor_failed
    csrr t0, 0xda0
    andi t0, t0, 8
    beq t0, zero, .Lsupervisor_failed
    li t0, 0x2000
    csrc sip, t0
    addi s3, s3, 1
    j .Lsupervisor_return
.Ltimer:
    li t0, 2
    bgeu s1, t0, .Lsupervisor_return
    addi s1, s1, 1
    li t0, -1
    li t1, 2
    bgeu s1, t1, .Larm_timer
    csrr t0, time
    li t1, 4096
    add t0, t0, t1
.Larm_timer:
    csrw 0x14d, t0
.Lsupervisor_return:
    ld t0, 0(sp)
    ld t1, 8(sp)
    addi sp, sp, 16
    sret
.Lsupervisor_failed:
    li a0, 1
    ecall
.Lmachine_trap:
    csrr t0, mcause
    li t1, 9
    bne t0, t1, .Lfailed
    li t1, 2
    bne a0, t1, .Lfinish
.globl counter_overflow_rearm
counter_overflow_rearm:
    li t0, -16
    csrw 0xb03, t0
    li t0, 1
    slli t0, t0, 63
    csrc 0x323, t0
    csrr t0, mepc
    addi t0, t0, 4
    csrw mepc, t0
    mret
.Lfailed:
    li a0, 1
.Lfinish:
    csrr sp, mscratch
    csrw mie, zero
    csrw mideleg, zero
    csrw pmpcfg0, zero
    csrw mtvec, s2
    bne a0, zero, .Lrestore
    la a0, .Lprefix
    call console_put_words
    csrr a0, mhartid
    li t0, 10
    bltu a0, t0, .Ldecimal
    addi a0, a0, 87
    j .Ldigit
.Ldecimal:
    addi a0, a0, 48
.Ldigit:
    call console_putc
    la a0, .Lsuffix
    call console_put_words
    li a0, 0
.Lrestore:
    ld ra, 0(sp)
    ld s1, 8(sp)
    ld s2, 16(sp)
    ld s3, 24(sp)
    addi sp, sp, 32
    ret
.section .rodata,"a",@progbits
.balign 4
.Lprefix:
    .word 104, 97, 114, 116, 32, 0
.Lsuffix:
    .word 32, 111, 110, 108, 105, 110, 101, 10, 0
