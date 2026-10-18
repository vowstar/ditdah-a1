/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
OUTPUT_ARCH(riscv)
ENTRY(_start)
MEMORY { ram (rwx) : ORIGIN = __ram_base, LENGTH = __ram_bytes }
SECTIONS {
  .text : { KEEP(*(.text.init)) *(.text .text.*) } > ram
  .rodata : {
    . = ALIGN(8);
    __stack_stride = .;
    QUAD(-__stack_bytes)
    *(.rodata .rodata.*)
  } > ram
  .data : { *(.data .data.* .sdata .sdata.*) } > ram
  .bss (NOLOAD) : {
    . = ALIGN(8);
    __bss_start = .;
    __test_results = .;
    . += __hart_count * 8;
    *(.bss .bss.* .sbss .sbss.* COMMON)
    . = ALIGN(8);
    __bss_end = .;
  } > ram
  __stack_top = (ORIGIN(ram) + LENGTH(ram)) & ~15;
  ASSERT(__hart_count * __stack_bytes <= LENGTH(ram), "Software stacks exceed RAM")
  __stack_bottom = __stack_top - __hart_count * __stack_bytes;
  ASSERT(__bss_end <= __stack_bottom, "Software data and stacks overlap")
}
