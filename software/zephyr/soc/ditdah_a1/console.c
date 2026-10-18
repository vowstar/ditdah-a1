/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#include <zephyr/arch/cpu.h>
#include <zephyr/devicetree.h>
#include <zephyr/init.h>
#include <zephyr/sys/libc-hooks.h>
#include <zephyr/sys/printk-hooks.h>
#include <zephyr/sys/sys_io.h>

static int transmit(int character)
{
	sys_write32((uint8_t)character,
		DT_REG_ADDR(DT_NODELABEL(console_tx)) + 4 * arch_proc_id());
	return character;
}

static int initialize(void)
{
	__printk_hook_install(transmit);
	__stdout_hook_install(transmit);
	return 0;
}

SYS_INIT(initialize, PRE_KERNEL_1, 0);
