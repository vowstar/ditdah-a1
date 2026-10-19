/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#if DITDAH_RAM_BASE < 0x80000000 || DITDAH_RAM_BASE + DITDAH_RAM_BYTES > 0xc0000000 || DITDAH_CONSOLE_BASE + 64 > 0x40000000
#error "Virtual memory test requires RAM in [2 GiB, 3 GiB) and console below 1 GiB"
#endif
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
    csrr s0, mhartid
    csrr s2, mtvec
    csrr s3, mstatus
    mv s5, sp
    li s4, 1
    la t0, .Ltrap
    csrw mtvec, t0
    la s1, .Lspaces
    slli t0, s0, 14
    slli t1, s0, 12
    add t0, t0, t1
    add s1, s1, t0
    li t0, 0x200000cf
    sd t0, 16(s1)
    li t0, 0xc7
    sd t0, 0(s1)
    li t0, 4096
    add t1, s1, t0
    srli t2, t1, 2
    ori t2, t2, 1
    sd t2, 8(s1)
    add t1, t1, t0
    srli t2, t1, 2
    ori t2, t2, 1
    add t3, s1, t0
    sd t2, 0(t3)
    add t3, t3, t0
    add t1, t1, t0
    srli t2, t1, 2
    ori t2, t2, 0xcf
    sd t2, 0(t3)
    li t4, 2
.Lcopy_page:
    la t0, .Lvirtual
    la t2, .Lvirtual_end
    mv t3, t1
.Lcopy:
    lw t5, 0(t0)
    sw t5, 0(t3)
    addi t0, t0, 4
    addi t3, t3, 4
    bne t0, t2, .Lcopy
    slli t5, t4, 5
    add t5, t5, s0
    sd t5, 512(t1)
    li t0, 4096
    add t1, t1, t0
    addi t4, t4, -1
    bne t4, zero, .Lcopy_page
    li t0, 16384
    add t0, s1, t0
    la t1, .Lvirtual_value
    la t2, .Lvirtual
    sub t1, t1, t2
    add t0, t0, t1
    li t1, 0x00200513
    sw t1, 0(t0)
    fence.i
    la t0, __ram_base
    srli t0, t0, 2
    csrw pmpaddr0, t0
    la t0, __stack_top
    srli t0, t0, 2
    csrw pmpaddr1, t0
    la t0, __console_base
    srli t0, t0, 2
    csrw pmpaddr2, t0
    la t0, __console_base
    addi t0, t0, 64
    srli t0, t0, 2
    csrw pmpaddr3, t0
    li t0, 0x0b000f00
    csrw pmpcfg0, t0
    srli t0, s1, 12
    li t1, 0x8000000000000000
    or t0, t0, t1
    csrw satp, t0
    sfence.vma
    la t0, .Lsupervisor
    csrw mepc, t0
    li t0, 0x1800
    csrc mstatus, t0
    li t0, 0x800
    csrs mstatus, t0
    mret
.Lsupervisor:
    addi a2, s0, 64
    li t0, 0x40000000
    jalr ra, t0, 0
    li t0, 1
    bne a0, t0, .Lfail_supervisor
    li t0, 16384
    add t0, s1, t0
    srli t1, t0, 2
    ori t1, t1, 0xcf
    li t0, 8192
    add t0, s1, t0
    sd t1, 0(t0)
    sfence.vma
    addi a2, s0, 32
    li t0, 0x40000000
    jalr ra, t0, 0
    li t0, 2
    bne a0, t0, .Lfail_supervisor
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
.Ldone:
    ecall
.Lfail_supervisor:
    ecall
    j .Lfail_supervisor
.Lprint:
    lw t0, 0(a0)
    beq t0, zero, 2f
    sw t0, 0(a1)
    addi a0, a0, 4
    j .Lprint
2:  ret
.Ltrap:
    csrr t0, mcause
    li t1, 9
    bne t0, t1, .Lfailure
    csrr t0, mepc
    la t1, .Ldone
    bne t0, t1, .Lfailure
    li t0, 12288
    add t0, s1, t0
    ld t1, 512(t0)
    addi t2, s0, 65
    bne t1, t2, .Lfailure
    li t0, 16384
    add t0, s1, t0
    ld t1, 512(t0)
    addi t2, s0, 33
    bne t1, t2, .Lfailure
    li s4, 0
.Lfailure:
    la t0, .Lfinish
    csrw mepc, t0
    li t0, 0x1800
    csrs mstatus, t0
    mret
.Lfinish:
    mv sp, s5
    csrw satp, zero
    sfence.vma
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
.balign 4
.Lvirtual:
    li t0, 0x40000200
    ld t1, 0(t0)
    bne t1, a2, .Lvirtual_fail
    addi t1, t1, 1
    sd t1, 0(t0)
.Lvirtual_value:
    li a0, 1
    ret
.Lvirtual_fail:
    li a0, -1
    ret
.Lvirtual_end:
.section .rodata,"a",@progbits
.balign 4
.Lprefix:
    .word 104, 97, 114, 116, 32, 0
.Lsuffix:
    .word 32, 111, 110, 108, 105, 110, 101, 10, 0
.section .data,"aw",@progbits
.balign 4096
.Lspaces:
    .zero 16 * 20480
