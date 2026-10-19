/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
.option norvc
.option norelax
.section .text,"ax",@progbits
.globl main
main:
    addi sp, sp, -64
    sd ra, 0(sp)
    sd s0, 8(sp)
    sd s1, 16(sp)
    sd s2, 24(sp)
    sd s3, 32(sp)
    sd s4, 40(sp)
    sd s5, 48(sp)
    mv s5, sp
    csrr s0, mhartid
    csrr s2, mtvec
    csrr s3, mstatus
    li s4, 1
    la t0, .Lmachine_trap
    csrw mtvec, t0
    la t0, __console_base
    srli t0, t0, 2
    csrw pmpaddr0, t0
    addi t0, t0, 1024
    csrw pmpaddr1, t0
    la t0, __ram_base
    srli t0, t0, 2
    csrw pmpaddr2, t0
    la t0, __stack_top
    srli t0, t0, 2
    csrw pmpaddr3, t0
    li t0, 0x0f000b00
    csrw pmpcfg0, t0
    li t0, 256
    csrw medeleg, t0
    li t0, 2
    csrw mideleg, t0
    la t0, .Lsupervisor_trap
    csrw stvec, t0
    li s1, 0
    la t0, .Lsupervisor
    j .Lenter_supervisor
.Lmachine_irq:
    li s1, 3
    li t0, 2
    csrw mie, t0
    csrw mip, t0
    la t0, .Lsupervisor_irq
.Lenter_supervisor:
    csrw mepc, t0
    li t0, 0x1800
    csrc mstatus, t0
    li t0, 0x800
    csrs mstatus, t0
    mret
.Lsupervisor:
    la t0, .Luser
    csrw sepc, t0
    csrw sstatus, zero
    sret
.Luser:
    ecall
    j .Luser
.Lsupervisor_resume:
    li t0, 1
    bne s1, t0, .Lsupervisor_fail
    li s1, 2
.Lsupervisor_exit:
    ecall
    j .Lsupervisor_fail
.Lsupervisor_irq:
    li t0, 2
    csrs sstatus, t0
    li t0, 4
    bne s1, t0, .Lsupervisor_fail
    slli a1, s0, 2
    la t0, __console_base
    add a1, a1, t0
    la a0, .Lprefix
    call .Lprint
    sltiu t0, s0, 10
    li t1, 87
    beq t0, zero, 1f
    li t1, 48
1:  add t1, t1, s0
    sw t1, 0(a1)
    la a0, .Lsuffix
    call .Lprint
.Lsupervisor_done:
    ecall
    j .Lsupervisor_fail
.Lprint:
    lw t0, 0(a0)
    beq t0, zero, 2f
    sw t0, 0(a1)
    addi a0, a0, 4
    j .Lprint
2:  ret
.Lsupervisor_trap:
    addi sp, sp, -16
    sd t0, 0(sp)
    sd t1, 8(sp)
    csrr t0, scause
    li t1, 8
    bne t0, t1, .Lsupervisor_interrupt
    bne s1, zero, .Lsupervisor_trap_fail
    csrr t0, sepc
    la t1, .Luser
    bne t0, t1, .Lsupervisor_trap_fail
    csrr t0, sstatus
    andi t0, t0, 256
    bne t0, zero, .Lsupervisor_trap_fail
    li s1, 1
    la t0, .Lsupervisor_resume
    csrw sepc, t0
    li t0, 256
    csrs sstatus, t0
    j .Lsupervisor_return
.Lsupervisor_interrupt:
    li t1, 0x8000000000000001
    bne t0, t1, .Lsupervisor_trap_fail
    li t0, 3
    bne s1, t0, .Lsupervisor_trap_fail
    csrr t0, sstatus
    andi t0, t0, 256
    beq t0, zero, .Lsupervisor_trap_fail
    csrw sip, zero
    li s1, 4
.Lsupervisor_return:
    ld t0, 0(sp)
    ld t1, 8(sp)
    addi sp, sp, 16
    sret
.Lsupervisor_trap_fail:
    addi sp, sp, 16
.Lsupervisor_fail:
    li s1, -1
    ecall
    j .Lsupervisor_fail
.Lmachine_trap:
    csrr t0, mcause
    li t1, 9
    bne t0, t1, .Lfailure
    csrr t0, mstatus
    li t1, 0x1800
    and t0, t0, t1
    li t1, 0x800
    bne t0, t1, .Lfailure
    csrr t0, mepc
    li t1, 2
    bne s1, t1, 3f
    la t1, .Lsupervisor_exit
    bne t0, t1, .Lfailure
    la t0, .Lmachine_irq
    j .Lreturn_machine
3:  li t1, 4
    bne s1, t1, .Lfailure
    la t1, .Lsupervisor_done
    bne t0, t1, .Lfailure
    li s4, 0
.Lfailure:
    la t0, .Lfinish
.Lreturn_machine:
    csrw mepc, t0
    li t0, 0x1800
    csrs mstatus, t0
    mret
.Lfinish:
    mv sp, s5
    csrw mie, zero
    csrw mip, zero
    csrw medeleg, zero
    csrw mideleg, zero
    csrw pmpcfg0, zero
    csrw mtvec, s2
    csrw mstatus, s3
    mv a0, s4
    ld ra, 0(sp)
    ld s0, 8(sp)
    ld s1, 16(sp)
    ld s2, 24(sp)
    ld s3, 32(sp)
    ld s4, 40(sp)
    ld s5, 48(sp)
    addi sp, sp, 64
    ret
.section .rodata,"a",@progbits
.balign 4
.Lprefix:
    .word 104, 97, 114, 116, 32, 0
.Lsuffix:
    .word 32, 111, 110, 108, 105, 110, 101, 10, 0
