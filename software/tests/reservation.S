/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#if DITDAH_HART_COUNT != 2
#error "Reservation test requires two harts"
#endif
.option norvc
.option norelax
.section .text,"ax",@progbits
.globl main
main:
    addi sp, sp, -32
    sd ra, 0(sp)
    sd s0, 8(sp)
    sd s1, 16(sp)
    sd s2, 24(sp)
    csrr s0, mhartid
    csrr s1, mtvec
    csrr s2, mstatus
    la t0, .Lroot
    slli t1, s0, 12
    add t0, t0, t1
    li t1, 0xc7
    sd t1, 0(t0)
    li t1, 0x200000cf
    sd t1, 16(t0)
#if DITDAH_PMP_ENTRIES
    li t2, -1
    csrw pmpaddr0, t2
    li t2, 0x1f
    csrw pmpcfg0, t2
#endif
    srli t0, t0, 12
    li t1, 0x8000000000000000
    or t0, t0, t1
    csrw satp, t0
    sfence.vma
    la t0, .Ltrap
    csrw mtvec, t0
    la t0, .Lsupervisor
    csrw mepc, t0
    li t0, 0x200800
    csrw mstatus, t0
    mret
.Lsupervisor:
    la t0, .Lword
    bnez s0, .Lwriter
    lr.d a2, (t0)
    la t1, .Lready
    li a2, 1
    sd a2, 0(t1)
    la t1, .Lprepared
.Lprepare_wait:
    ld a2, 0(t1)
    beqz a2, .Lprepare_wait
    la t1, .Lgo
    li a2, 1
    sd a2, 0(t1)
    li a3, 4
.Ldelay:
    addi a3, a3, -1
    bnez a3, .Ldelay
.globl target_wait
target_wait:
    wrs.nto
.Lwritten_wait:
    ld a2, 0(t0)
    beqz a2, .Lwritten_wait
    j .Ldone
.Lwriter:
    la t1, .Lready
.Lready_wait:
    ld a2, 0(t1)
    beqz a2, .Lready_wait
    ld a2, 0(t0)
    la t1, .Lprepared
    li a2, 1
    sd a2, 0(t1)
    la t1, .Lgo
.Lgo_wait:
    ld a2, 0(t1)
    beqz a2, .Lgo_wait
    li a2, 1
    sd a2, 0(t0)
    lr.d a2, (t1)
    wrs.sto
.Ldone:
    ecall
.Ltrap:
    csrr t3, mcause
    li t4, 9
    beq t3, t4, .Lreturn_machine
    li t4, 2
    bne t3, t4, .Lfail
    csrr t3, mepc
    la t4, target_wait
    bne t3, t4, .Lfail
    addi t3, t3, 4
    csrw mepc, t3
    mret
.Lreturn_machine:
    la t3, .Lreturn
    csrw mepc, t3
    li t3, 0x1800
    csrs mstatus, t3
    mret
.Lreturn:
    la a0, .Lprefix
    call console_put_words
    addi a0, s0, 48
    call console_putc
    la a0, .Lsuffix
    call console_put_words
    li a0, 0
    j .Lrestore
.Lfail:
    li a0, 1
.Lrestore:
    csrw mtvec, s1
    csrw mstatus, s2
    ld ra, 0(sp)
    ld s0, 8(sp)
    ld s1, 16(sp)
    ld s2, 24(sp)
    addi sp, sp, 32
    ret
.section .rodata,"a",@progbits
.Lprefix: .word 104, 97, 114, 116, 32, 0
.Lsuffix: .word 32, 111, 110, 108, 105, 110, 101, 10, 0
.section .bss,"aw",@nobits
.balign 64
.Lword: .zero 64
.Lready: .zero 64
.Lprepared: .zero 64
.Lgo: .zero 64
.balign 4096
.Lroot: .zero 8192
