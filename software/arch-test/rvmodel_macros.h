// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
#ifndef DITDAH_A1_TEST_PLATFORM
#define DITDAH_A1_TEST_PLATFORM
#define RVMODEL_DATA_SECTION \
  .pushsection .bss,"aw",@nobits; \
  .balign 8; .global __test_results; __test_results: .zero 8; \
  .popsection
#define RVMODEL_BOOT_TO_MMODE \
  la t0, rvmodel_halt_fail; csrw mtvec, t0
#define RVMODEL_HALT_PASS \
  li t0, 1; la t1, __test_results; sd t0, 0(t1); \
  .global __test_halt; __test_halt: j __test_halt
#define RVMODEL_HALT_FAIL \
  li t0, 2; la t1, __test_results; sd t0, 0(t1); j __test_halt
#define RVMODEL_IO_WRITE_STR(_R1, _R2, _R3, _STR_PTR) \
  la _R2, __console_base; \
  1: lbu _R1, 0(_STR_PTR); beqz _R1, 2f; \
  sw _R1, 0(_R2); addi _STR_PTR, _STR_PTR, 1; j 1b; 2:
#define RVMODEL_INTERRUPT_LATENCY 1
#define RVMODEL_TIMER_INT_SOON_DELAY 100
#define RVMODEL_SET_MEXT_INT(_R1, _R2) .error "External interrupts are outside this test selection"
#define RVMODEL_CLR_MEXT_INT(_R1, _R2) .error "External interrupts are outside this test selection"
#define RVMODEL_SET_MSW_INT(_R1, _R2) .error "Software interrupts are outside this test selection"
#define RVMODEL_CLR_MSW_INT(_R1, _R2) .error "Software interrupts are outside this test selection"
#define RVMODEL_SET_SEXT_INT(_R1, _R2) .error "Supervisor interrupts are outside this test selection"
#define RVMODEL_CLR_SEXT_INT(_R1, _R2) .error "Supervisor interrupts are outside this test selection"
#define RVMODEL_SET_SSW_INT(_R1, _R2) .error "Supervisor interrupts are outside this test selection"
#define RVMODEL_CLR_SSW_INT(_R1, _R2) .error "Supervisor interrupts are outside this test selection"
#endif
