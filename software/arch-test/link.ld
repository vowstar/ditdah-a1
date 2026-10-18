/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
OUTPUT_ARCH(riscv)
ENTRY(rvtest_entry_point)
MEMORY { ram (rwx) : ORIGIN = __ram_base, LENGTH = __ram_bytes }
__hart_count = 1;
__stack_bytes = 0x20000;
SECTIONS {
  .text.init : { KEEP(*(.text.init)) } > ram
  _start = rvtest_entry_point;
  .text.rvtest : { *(.text.rvtest .text.rvtest.*) } > ram
  . = ALIGN(0x4000);
  .rodata . : { *(.rodata .rodata.* .srodata .srodata.*) } > ram
  .data . : { *(.data .data.* .sdata .sdata.* .tohost) } > ram
  .bss . (NOLOAD) : {
    . = ALIGN(8);
    __bss_start = .;
    *(.bss .bss.* .sbss .sbss.* COMMON)
    . = ALIGN(16);
    __bss_end = .;
  } > ram
  __stack_bottom = .;
  . += __stack_bytes;
  __stack_top = .;
  . = ALIGN(0x1000);
  .text.rvmodel . : { *(.text.rvmodel .text.rvmodel.* .text .text.*) } > ram
  ASSERT(. <= ORIGIN(ram) + LENGTH(ram), "Test image exceeds RAM")
}
