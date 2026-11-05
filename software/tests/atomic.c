/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#include <stdint.h>

extern void console_putc(int character);
static struct { uint32_t neighbor; uint32_t counter; } state
    __attribute__((aligned(64))) = {0x6badcafe, 0};
static uint32_t lock __attribute__((aligned(64)));
static uint32_t done __attribute__((aligned(64)));
static uint32_t seen[16] __attribute__((aligned(64)));
static const uint64_t products[16] = {
    15, 24, 35, 48, 63, 80, 99, 120, 143, 168, 195, 224, 255, 288, 323, 360
};

static void put_text(const char *text)
{
    while (*text) console_putc(*text++);
}

int main(void)
{
    unsigned long hart;
    __asm__ volatile ("csrr %0, mhartid" : "=r"(hart));
    volatile uint64_t product = (hart + 3) * (hart + 5);
    if (product != products[hart] || product / (hart + 3) != hart + 5 || product % (hart + 3))
        return 1;
#if defined(__riscv_zba) && defined(__riscv_zbb) && defined(__riscv_zbs)
    uint64_t address, rotated, toggled;
    __asm__ volatile ("sh3add %0, %1, %2" : "=r"(address) : "r"(hart), "r"(0x8000000000000001UL));
    __asm__ volatile ("rori %0, %1, 63" : "=r"(rotated) : "r"(address));
    __asm__ volatile ("binvi %0, %1, 63" : "=r"(toggled) : "r"(rotated));
    if (address != 0x8000000000000001UL + 8 * hart ||
        rotated != 3 + 16 * hart || toggled != (0x8000000000000003UL + 16 * hart)) return 5;
#endif
#if defined(__riscv_flen)
    __asm__ volatile ("csrs mstatus, %0" :: "r"(0x2000UL));
    uint64_t floating;
    __asm__ volatile ("fcvt.s.lu ft0, %1; fadd.s ft1, ft0, ft0; fcvt.lu.s %0, ft1, rtz"
                      : "=r"(floating) : "r"(hart + 3) : "ft0", "ft1");
    if (floating != 2 * (hart + 3)) return 6;
#if __riscv_flen == 64
    __asm__ volatile ("fcvt.d.lu ft0, %1; fadd.d ft1, ft0, ft0; fcvt.lu.d %0, ft1, rtz"
                      : "=r"(floating) : "r"(hart + 5) : "ft0", "ft1");
    if (floating != 2 * (hart + 5)) return 7;
#endif
#endif
#if defined(__riscv_zicond)
    uint64_t conditional;
    __asm__ volatile ("czero.eqz %0, %1, zero" : "=r"(conditional) : "r"(hart + 17));
    if (conditional) return 8;
    __asm__ volatile ("czero.nez %0, %1, zero" : "=r"(conditional) : "r"(hart + 17));
    if (conditional != hart + 17) return 8;
    __asm__ volatile (".word 0x0100000f; .word 0x00200033");
#endif
#if defined(__riscv_zimop)
    uint64_t ignored;
    __asm__ volatile ("mop.r.0 %0, %1" : "=r"(ignored) : "r"(hart + 17));
    if (ignored) return 9;
    __asm__ volatile ("mop.rr.0 %0, %1, %2" : "=r"(ignored) : "r"(hart), "r"(hart + 1));
    if (ignored) return 9;
#endif
#if defined(__riscv_zcb)
    uint64_t compact;
    __asm__ volatile ("mv a0, %1; c.zext.b a0; mv %0, a0"
                      : "=r"(compact) : "r"(hart + 0x100) : "a0");
    if (compact != hart) return 10;
    __asm__ volatile ("mv a0, %1; mv a1, %2; c.mul a0, a1; mv %0, a0"
                      : "=r"(compact) : "r"(hart + 3), "r"(hart + 5) : "a0", "a1");
    if (compact != products[hart]) return 10;
#endif
#if defined(__riscv_zcmop)
    register uint64_t kept __asm__("t2") = hart + 17;
    __asm__ volatile ("c.mop.7" : "+r"(kept));
    if (kept != hart + 17) return 11;
#endif
#if defined(__riscv_zfa)
    uint64_t rounded, flags;
    __asm__ volatile ("csrw fflags, zero; fli.s ft0, 1.5; froundnx.s ft1, ft0, rne; "
                      "fmv.x.w %0, ft1; csrr %1, fflags"
                      : "=r"(rounded), "=r"(flags) :: "ft0", "ft1");
    if (rounded != 0x40000000 || flags != 1) return 12;
#if __riscv_flen == 64
    __asm__ volatile ("csrw fflags, zero; fmv.d.x ft0, %2; fcvtmod.w.d %0, ft0, rtz; csrr %1, fflags"
                      : "=r"(rounded), "=r"(flags) : "r"(0x41f0000000100000UL) : "ft0");
    if (rounded != 1 || flags != 16) return 12;
#endif
#endif
#if defined(__riscv_zfhmin)
    uint16_t half = 0x7d01 + hart, saved;
    uint64_t moved;
    __asm__ volatile ("flh ft0, %2; fsh ft0, %1; fmv.x.h %0, ft0"
                      : "=r"(moved), "=m"(saved) : "m"(half) : "ft0");
    if (moved != half || saved != half) return 13;
    __asm__ volatile ("fmv.h.x ft0, %1; fmv.x.h %0, ft0"
                      : "=r"(moved) : "r"(0x3c00UL + hart) : "ft0");
    if (moved != 0x3c00 + hart) return 13;
#if __riscv_flen == 64
    uint64_t narrowed, half_flags;
    __asm__ volatile ("csrw fflags, zero; fmv.d.x ft0, %3; fcvt.h.d ft1, ft0, rne; "
                      "fmv.x.h %0, ft1; fcvt.d.h ft2, ft1; fmv.x.d %1, ft2; csrr %2, fflags"
                      : "=r"(narrowed), "=r"(moved), "=r"(half_flags)
                      : "r"(0x3ff0020000000001UL) : "ft0", "ft1", "ft2");
    if (narrowed != 0x3c01 || moved != 0x3ff0040000000000UL || half_flags != 1) return 13;
#endif
#endif
    uint32_t old = __atomic_fetch_add(&state.counter, 1, __ATOMIC_ACQ_REL);
    if (old >= DITDAH_HART_COUNT) return 2;
    uint32_t expected = 0;
    while (!__atomic_compare_exchange_n(&lock, &expected, 1, 1,
                                        __ATOMIC_ACQUIRE, __ATOMIC_RELAXED))
        expected = 0;
    seen[old]++;
    __atomic_store_n(&lock, 0, __ATOMIC_RELEASE);
    __atomic_fetch_add(&done, 1, __ATOMIC_RELEASE);
    while (__atomic_load_n(&done, __ATOMIC_ACQUIRE) != DITDAH_HART_COUNT) {}
    if (state.neighbor != 0x6badcafe || state.counter != DITDAH_HART_COUNT) return 3;
    for (unsigned i = 0; i < DITDAH_HART_COUNT; ++i)
        if (seen[i] != 1) return 4;
    put_text("hart ");
    console_putc("0123456789abcdef"[hart]);
    put_text(" online\n");
    return 0;
}
