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
    sd s6, 56(sp)
    la s6, .Lhart_count
    ld s6, 0(s6)
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
#if DITDAH_ASID_BITS
    li t0, 0x200000ef
#else
    li t0, 0x200000cf
#endif
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
#if DITDAH_ASID_BITS
    la t0, .Lcontexts
    slli t1, s0, 12
    add t0, t0, t1
    li t1, 0x200000cf
    sd t1, 8(t0)
    ori t1, t1, 32
    sd t1, 16(t0)
    li t1, 0xc7
    sd t1, 0(t0)
#endif
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
#ifdef DITDAH_SUPERVISOR_MEMORY
    la t0, __local_interrupt_base
    srli t0, t0, 2
    csrw pmpaddr4, t0
    li t1, 16384
    add t0, t0, t1
    csrw pmpaddr5, t0
    li t0, 0x0b000b000f00
#else
    li t0, 0x0b000f00
#endif
    csrw pmpcfg0, t0
#if defined(__riscv_zicbom) || defined(__riscv_zicboz)
    li t0, 0xf0
    csrs menvcfg, t0
#endif
#ifdef DITDAH_SUPERVISOR_MEMORY
    call .Lmemory_attributes
#endif
    srli t0, s1, 12
    li t1, 0x8000000000000000
    or t0, t0, t1
    csrw satp, t0
    sfence.vma
    li t0, 8
    csrw mie, t0
    la t0, .Lsupervisor
    csrw mepc, t0
    li t0, 0x1800
    csrc mstatus, t0
    li t0, 0x800
    csrs mstatus, t0
    mret
.Lsupervisor:
#if defined(__riscv_zicbom) || defined(__riscv_zicboz) || defined(__riscv_zawrs)
    la t0, .Lblocks
    slli t1, s0, 6
    add t0, t0, t1
    ld t1, 0(t0)
    addi t3, s0, 1
    mv t2, t0
    li t1, 8
.Lblock_fill:
    sd t3, 0(t2)
    addi t2, t2, 8
    addi t1, t1, -1
    bnez t1, .Lblock_fill
#if defined(__riscv_zicbom)
    cbo.clean 0(t0)
    cbo.inval 0(t0)
    cbo.flush 0(t0)
    ld t1, 0(t0)
    bne t1, t3, .Lfail_supervisor
#endif
#if defined(__riscv_zicboz)
    cbo.zero 0(t0)
    mv t2, t0
    li t1, 8
.Lblock_zero_check:
    ld t3, 0(t2)
    bnez t3, .Lfail_supervisor
    addi t2, t2, 8
    addi t1, t1, -1
    bnez t1, .Lblock_zero_check
#endif
#if defined(__riscv_zawrs)
    lr.d t1, (t0)
    wrs.sto
    lr.d t1, (t0)
    wrs.nto
#endif
#endif
#ifdef __riscv_compressed
    .option rvc
    c.nop
    .option norvc
#endif
#if defined(__riscv_flen) && __riscv_flen == 64
    li t0, 0x2000
    csrs sstatus, t0
    fcvt.s.lu ft0, s0
    fcvt.d.s ft0, ft0
    fadd.d ft1, ft0, ft0
    fcvt.lu.d t0, ft1, rtz
    slli t1, s0, 1
    bne t0, t1, .Lfail_supervisor
#endif
#if defined(__riscv_zba) && defined(__riscv_zbb) && defined(__riscv_zbs)
    sh1add t0, s0, s0
    andn t1, t0, zero
    bseti t1, t1, 8
    addi t0, t0, 256
    bne t0, t1, .Lfail_supervisor
#endif
    addi a2, s0, 64
    li t0, 0x40000000
    jalr ra, t0, 0
    li t0, 1
    bne a0, t0, .Lfail_supervisor
#if DITDAH_ASID_BITS
    csrr t5, satp
    la t0, .Lcontexts
    slli t1, s0, 12
    add t0, t0, t1
    srli t0, t0, 12
    li t1, 0x8000100000000000
    or t0, t0, t1
    li t1, 1
    sfence.vma zero, t1
    csrw satp, t0
    li t0, 0x40000200
    ld t1, 0(t0)
    li t2, 0x80000200
    ld t2, 0(t2)
    bne t1, t2, .Lfail_supervisor
    csrw satp, t5
    ld t1, 0(t0)
    addi t2, s0, 65
    bne t1, t2, .Lfail_supervisor
#endif
#ifdef DITDAH_SUPERVISOR_MEMORY
    li t0, 0x40000
    csrs sstatus, t0
    li t2, 0x40021020
    slli t0, s0, 6
    add t2, t2, t0
    fence iorw, iorw
    cbo.flush 0(t2)
    fence iorw, iorw
    la t0, .Lblocks
    slli t1, s0, 6
#else
    la t0, .Lready
    slli t1, s0, 3
#endif
    add t0, t0, t1
#ifdef DITDAH_SUPERVISOR_MEMORY
    ld t4, 0(t0)
    addi t1, s0, 0x100
    sd t1, 0(t0)
    fence o, o
    li t1, 1
    sd t1, 0(t2)
#else
    li t1, 1
    sd t1, 0(t0)
    fence rw, rw
#endif
    bne s0, zero, .Lwait_remap
#ifdef DITDAH_SUPERVISOR_MEMORY
    li t0, 0x40021020
#else
    la t0, .Lready
#endif
    li t1, 0
.Lwait_ready:
    ld t2, 0(t0)
    beq t2, zero, .Lwait_ready
#ifdef DITDAH_SUPERVISOR_MEMORY
    fence i, i
    la t3, .Lblocks
    slli t4, t1, 6
    add t3, t3, t4
    ld t4, 0(t3)
    addi t5, t1, 0x100
    bne t4, t5, .Lfail_supervisor
    addi t0, t0, 64
#else
    addi t0, t0, 8
#endif
    addi t1, t1, 1
    bltu t1, s6, .Lwait_ready
.Lrequest_remap:
    ecall
.Lwait_remap:
#ifdef DITDAH_SUPERVISOR_MEMORY
    li t0, 0x40000
    csrc sstatus, t0
#endif
    la t0, .Lacknowledged
    li t1, 0
.Lwait_ack:
    ld t2, 0(t0)
    beq t2, zero, .Lwait_ack
    addi t0, t0, 8
    addi t1, t1, 1
    bltu t1, s6, .Lwait_ack
    fence rw, rw
    addi a2, s0, 32
    li t0, 0x40000000
    jalr ra, t0, 0
    li t0, 2
    bne a0, t0, .Lfail_supervisor
#ifdef __riscv_atomic
    la t0, __atomic_count
.Latomic_retry:
    lr.d t1, (t0)
    addi t1, t1, 1
    sc.d t2, t1, (t0)
    bnez t2, .Latomic_retry
.Latomic_wait:
    ld t1, 0(t0)
    bne t1, s6, .Latomic_wait
#endif
    la t0, .Lconsole_turn
.Lconsole_wait:
    ld t1, 0(t0)
    bne t1, s0, .Lconsole_wait
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
    fence iorw, iorw
    la t0, .Lconsole_turn
    addi t1, s0, 1
    sd t1, 0(t0)
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
#ifdef DITDAH_SUPERVISOR_MEMORY
.Lmemory_attributes:
    la a4, .Lwide
    srli t1, a4, 2
    li t2, 0x80000000000020d7
    or t1, t1, t2
    li t0, 8320
    add t0, s1, t0
    li t2, 16
.Lnapot_pte:
    sd t1, 0(t0)
    addi t0, t0, 8
    addi t2, t2, -1
    bnez t2, .Lnapot_pte
    srli t1, a4, 2
    li t2, 0x20000000000000d7
    or t1, t1, t2
    sd t1, 0(t0)
    li t2, 0x6000000000000000
    xor t1, t1, t2
    sd t1, 8(t0)
    la t1, __local_interrupt_base
    srli t1, t1, 2
    li t2, 0x20000000000000d7
    or t1, t1, t2
    sd t1, 16(t0)
    li t0, 0x4000000000000001
    csrs menvcfg, t0
    csrw senvcfg, zero
    csrr t0, senvcfg
    bnez t0, .Lfailure
    li t0, 0x200000001
    csrw senvcfg, t0
    csrr t1, senvcfg
    bne t0, t1, .Lfailure
    srli t0, s1, 12
    li t1, 0x8000000000000000
    or t0, t0, t1
    csrw satp, t0
    .word 0x18000073
    .word 0x16000073
    .word 0x18100073
    slli t0, s0, 6
    add a4, a4, t0
    li a3, 0xaa00000040010000
    add a3, a3, t0
    mv a5, a3
    li t0, 0x1800
    csrc mstatus, t0
    li t0, 0x22000
    csrs mstatus, t0
    addi t1, s0, 0x123
    li t5, 16
    li t6, 4096
.Lnapot_data:
    sd t1, 0(a3)
    ld t2, 0(a3)
    bne t1, t2, .Lattribute_failure
    add a3, a3, t6
    addi t5, t5, -1
    bnez t5, .Lnapot_data
    mv a3, a5
#if defined(__riscv_flen) && __riscv_flen == 64
    fld ft0, 0(a3)
    fsd ft0, 8(a3)
    ld t2, 8(a3)
    bne t1, t2, .Lattribute_failure
#endif
#ifdef __riscv_atomic
    lr.d.aq t2, (a3)
    sc.d.rl t3, t1, (a3)
    bnez t3, .Lattribute_failure
    bne t1, t2, .Lattribute_failure
#endif
    li t0, 65536
    add a6, a3, t0
    fence iorw, iorw
    cbo.flush 0(a6)
    fence iorw, iorw
    ld t2, 0(a6)
    bne t1, t2, .Lattribute_failure
    add a6, a6, t6
    ld t2, 0(a3)
    addi t1, t1, 1
    sd t1, 0(a3)
    fence iorw, iorw
    cbo.flush 0(a6)
    fence iorw, iorw
    ld t2, 0(a6)
    bne t1, t2, .Lattribute_failure
    addi t1, t1, 1
    sd t1, 0(a6)
    fence o, o
#ifdef __riscv_atomic
    amoadd.d.aqrl t2, zero, (a6)
    bne t1, t2, .Lattribute_failure
#endif
    fence iorw, iorw
    cbo.flush 0(a6)
    fence iorw, iorw
    ld t2, 0(a3)
    bne t1, t2, .Lattribute_failure
    slli a7, s0, 2
    li t0, 0xaa00000040022000
    add a7, a7, t0
    li t0, 1
    sw t0, 0(a7)
    lw t1, 0(a7)
    bne t0, t1, .Lattribute_failure
    sw zero, 0(a7)
    lw t1, 0(a7)
    bnez t1, .Lattribute_failure
    li t0, 0x0b000f00
    csrw pmpcfg0, t0
    li a2, 0
.Llocal_denied:
    lw t1, 0(a7)
    beqz a2, .Lattribute_failure
    li t0, 0x0b000b000f00
    csrw pmpcfg0, t0
    csrw mstatus, s3
    ret
.Lattribute_failure:
    csrw mstatus, s3
    j .Lfailure
#endif
.balign 4
.Ltrap:
    addi sp, sp, -64
    sd t0, 0(sp)
    sd t1, 8(sp)
    sd t2, 16(sp)
    sd t3, 24(sp)
    sd t4, 32(sp)
    sd t5, 40(sp)
    sd t6, 48(sp)
    csrr t0, mcause
    li t1, 0x8000000000000003
    beq t0, t1, .Linterrupt
#ifdef DITDAH_SUPERVISOR_MEMORY
    li t1, 5
    beq t0, t1, .Llocal_fault
#endif
    li t1, 9
    bne t0, t1, .Lfailure
    csrr t0, mepc
    la t1, .Lrequest_remap
    beq t0, t1, .Lremap
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
#ifdef DITDAH_SUPERVISOR_MEMORY
.Llocal_fault:
    csrr t0, mepc
    la t1, .Llocal_denied
    bne t0, t1, .Lfailure
    csrr t1, mtval
    li t2, 0x40022000
    slli t3, s0, 2
    add t2, t2, t3
    bne t1, t2, .Lfailure
    li a2, 1
    addi t0, t0, 4
    csrw mepc, t0
    j .Lreturn
#endif
.Lremap:
    la t0, .Lspaces
    li t1, 0
.Lupdate:
    li t2, 16384
    add t2, t0, t2
    srli t2, t2, 2
    ori t2, t2, 0xcf
    li t3, 8192
    add t3, t0, t3
    sd t2, 0(t3)
    li t2, 20480
    add t0, t0, t2
    addi t1, t1, 1
    bltu t1, s6, .Lupdate
    fence rw, rw
    la t0, __local_interrupt_base
    mv t1, s6
    li t2, 1
.Lnotify:
    sw t2, 0(t0)
    addi t0, t0, 4
    addi t1, t1, -1
    bne t1, zero, .Lnotify
    csrr t0, mepc
    addi t0, t0, 4
    csrw mepc, t0
    j .Lreturn
.Linterrupt:
    la t0, __local_interrupt_base
    slli t1, s0, 2
    add t0, t0, t1
    sw zero, 0(t0)
#ifdef DITDAH_SUPERVISOR_MEMORY
    .word 0x18000073
    .word 0x16000073
    .word 0x18100073
#else
    sfence.vma
#endif
    fence rw, rw
    la t0, .Lacknowledged
    slli t1, s0, 3
    add t0, t0, t1
    li t1, 1
    sd t1, 0(t0)
    fence rw, rw
.Lreturn:
    ld t0, 0(sp)
    ld t1, 8(sp)
    ld t2, 16(sp)
    ld t3, 24(sp)
    ld t4, 32(sp)
    ld t5, 40(sp)
    ld t6, 48(sp)
    addi sp, sp, 64
    mret
.Lfinish:
    mv sp, s5
    csrw mie, zero
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
    ld s6, 56(sp)
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
.balign 8
.Lhart_count:
    .dword __hart_count
.section .bss,"aw",@nobits
#if defined(__riscv_zicbom) || defined(__riscv_zicboz) || defined(__riscv_zawrs)
.balign 64
.Lblocks:
    .zero 64 * DITDAH_HART_COUNT
#endif
.balign 8
.Lready:
    .zero 128
.Lacknowledged:
    .zero 128
#ifdef __riscv_atomic
.balign 64
.globl __atomic_count
__atomic_count:
    .zero 8
#endif
.balign 64
.Lconsole_turn:
    .zero 8
#ifndef DITDAH_ZERO_PAGE_TABLES
.section .data,"aw",@progbits
#endif
.balign 4096
.Lspaces:
    .zero DITDAH_HART_COUNT * 20480
#ifdef DITDAH_SUPERVISOR_MEMORY
.balign 65536
.Lwide:
    .zero 65536
#endif
#if DITDAH_ASID_BITS
.Lcontexts:
    .zero DITDAH_HART_COUNT * 4096
#endif
