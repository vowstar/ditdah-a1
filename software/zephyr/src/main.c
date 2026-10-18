/* SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> */
/* SPDX-License-Identifier: MIT */
#include <zephyr/drivers/timer/system_timer.h>
#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>
#include <zephyr/sys/sys_io.h>

#define HARTS CONFIG_MP_MAX_NUM_CPUS
BUILD_ASSERT(HARTS <= 16);
volatile uint64_t __test_results[HARTS];
static struct k_thread workers[HARTS];
K_THREAD_STACK_ARRAY_DEFINE(worker_stacks, HARTS, 2048);
static atomic_t completed;

struct notice {
	struct k_ipi_work work;
	volatile unsigned int cpu;
};

void __attribute__((noreturn)) __test_halt(void)
{
	for (;;) {
		__asm__ volatile("j __test_halt");
	}
}

static void notified(struct k_ipi_work *work)
{
	CONTAINER_OF(work, struct notice, work)->cpu = arch_curr_cpu()->id;
}

static void run(void *argument, void *unused1, void *unused2)
{
	unsigned int hart = (uintptr_t)argument;
	bool success = arch_curr_cpu()->id == hart && arch_proc_id() == hart;
	if (HARTS > 1) {
		unsigned int target = (hart + 1) % HARTS;
		struct notice notice = {.cpu = HARTS};
		k_ipi_work_init(&notice.work);
		success &= k_ipi_work_add(&notice.work, BIT(target), notified) == 0;
		k_ipi_work_signal();
		success &= k_ipi_work_wait(&notice.work, K_FOREVER) == 0;
		success &= notice.cpu == target;
	} else {
		uintptr_t msip = DT_REG_ADDR(DT_NODELABEL(clint));
		sys_write32(1, msip);
		while (sys_read32(msip)) {
			k_yield();
		}
	}
	k_spinlock_key_t key = sys_clock_lock();
	sys_clock_set_timeout(1, false);
	sys_clock_unlock(key);
	k_busy_wait(2 * USEC_PER_SEC / CONFIG_SYS_CLOCK_TICKS_PER_SEC);
	int64_t began = k_uptime_ticks();
	k_sleep(K_TICKS(2));
	success &= k_uptime_ticks() - began >= 2;
	printk("hart %x online\n", hart);
	atomic_inc(&completed);
	while (atomic_get(&completed) != HARTS) {
		k_yield();
	}
	arch_irq_lock();
	__test_results[hart] = success ? 1 : 2;
	__asm__ volatile("fence rw, rw" ::: "memory");
	__test_halt();
}

int main(void)
{
	for (unsigned int hart = 0; hart < HARTS; hart++) {
		k_tid_t thread = k_thread_create(&workers[hart], worker_stacks[hart],
			K_THREAD_STACK_SIZEOF(worker_stacks[hart]), run,
			(void *)(uintptr_t)hart, NULL, NULL, 1, 0, K_FOREVER);
		__ASSERT_NO_MSG(k_thread_cpu_pin(thread, hart) == 0);
		k_thread_start(thread);
	}
	return 0;
}
