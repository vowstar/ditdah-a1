/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#include <stdint.h>

extern void console_putc(int character);
static volatile uint64_t zeroed;
static volatile uint64_t inputs[] = {0, 1, UINT64_MAX, UINT64_C(0x80000000ffffffff)};
static const uint64_t expected[] = {
    UINT64_C(0x0000000000001234), UINT64_C(0x0000000000001231), UINT64_C(0x01ffffffffffedcb), UINT64_C(0x8100000f01ffedcc),
    UINT64_C(0x0000000000001234), UINT64_C(0x0000000000001275), UINT64_C(0x01ffffffffffedcb), UINT64_C(0x810000ff01ffedb4),
    UINT64_C(0x0000000000001234), UINT64_C(0x0000000000001635), UINT64_C(0x01ffffffffffedcb), UINT64_C(0x81000fff01ffea34),
    UINT64_C(0x0000000000001234), UINT64_C(0x0000000000005235), UINT64_C(0x01ffffffffffedcb), UINT64_C(0x8100ffff01ff9234),
};

__attribute__((noinline)) static uint64_t mix(uint64_t value, unsigned shift)
{
    return ((value << shift) | (value >> (64 - shift))) ^ ((value ^ (value >> 7)) + 0x1234);
}

static void put_text(const char *text)
{
    while (*text) console_putc(*text++);
}

int main(void)
{
    unsigned long hart;
    __asm__ volatile ("csrr %0, mhartid" : "=r"(hart));
    volatile int8_t byte = -128;
    volatile uint8_t ubyte = 255;
    volatile int16_t half = -32768;
    volatile uint16_t uhalf = 65535;
    volatile uint32_t word = UINT32_MAX;
    word = word + 2;
    if (zeroed || byte != -128 || ubyte != 255 || half != -32768 || uhalf != 65535 || word != 1)
        return 1;
    if (mix(inputs[hart & 3], hart + 1) != expected[hart]) return 2;
    put_text("hart ");
    console_putc("0123456789abcdef"[hart]);
    put_text(" online\n");
    return 0;
}
