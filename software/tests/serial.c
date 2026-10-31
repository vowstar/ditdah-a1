/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#include <stdint.h>

extern void console_putc(int character);
static volatile uint64_t turn;

int main(void)
{
    unsigned long hart;
    __asm__ volatile ("csrr %0, mhartid" : "=r"(hart));
    while (__atomic_load_n(&turn, __ATOMIC_ACQUIRE) != hart) {}
    const char *prefix = "hart ";
    const char *suffix = " online\n";
    while (*prefix) console_putc(*prefix++);
    console_putc("0123456789abcdef"[hart]);
    while (*suffix) console_putc(*suffix++);
    __asm__ volatile ("fence iorw, iorw" ::: "memory");
#if defined(__riscv_atomic)
    return __atomic_fetch_add(&turn, 1, __ATOMIC_RELEASE) != hart;
#else
    __atomic_store_n(&turn, hart + 1, __ATOMIC_RELEASE);
    return 0;
#endif
}
