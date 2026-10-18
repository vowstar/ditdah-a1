# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT

.PHONY: config check rtl verify-signoff verify-simulation verify-production verify-cache verify-platform verify-formal clean

HART_COUNTS ?= 2 3 15 16
ICACHE_CASES := pipeline_reuse cache_replacement fence_ordering fence_i_prefetch synchronization atomic_ordering atomic_denied atomic_retry bus_fetch pipeline_redirect pmp_fetch pmp_update interrupt_fence interrupt_fence_i interrupt_fetch_fault

config:
	configure-ditdah-a1 --output result/ditdah_a1_config.json

check:
	configure-ditdah-a1 --check

rtl:
	build-ditdah-a1

verify-signoff: verify-formal

verify-simulation: config check
	python3 test/verify.py $(VERIFY_ARGS)
	python3 test/verify.py --multicore-only --output result/multicore $(foreach count,$(filter-out 15,$(HART_COUNTS)),--harts $(count))

verify-production: verify-simulation
	build-ditdah-a1 --output result/production
	build-ditdah-a1 --top DitDahA1Core --output result/core
	build-ditdah-a1 --top DitDahA1Frontend --config result/frontend-input.json --output result/frontend
	build-ditdah-a1 --top DitDahA1MemoryFabric --config result/fabric-input.json --output result/fabric
	build-ditdah-a1 --top DitDahA1Backend --config result/backend-input.json --output result/backend
	build-ditdah-a1 --config result/verify/pmp16-axi512/input.json --output result/production-pmp16
	build-ditdah-a1 --top DitDahA1Core --config result/verify/pmp16-axi512/input.json --output result/core-pmp16
	build-ditdah-a1 --top DitDahA1Frontend --config result/verify/pmp16-axi512/input.json --output result/frontend-pmp16
	build-ditdah-a1 --top DitDahA1Backend --config result/verify/pmp16-axi512/input.json --output result/backend-pmp16
	build-ditdah-a1 --config result/verify/irq-pmp16-axi512/input.json --output result/production-irq
	build-ditdah-a1 --top DitDahA1Core --config result/verify/irq-pmp16-axi512/input.json --output result/core-irq
	build-ditdah-a1 --top DitDahA1Backend --config result/verify/irq-pmp16-axi512/input.json --output result/backend-irq
	for count in $(HART_COUNTS); do build-ditdah-a1 --config result/harts$$count-input.json --output result/production-harts$$count || exit $$?; done
	python3 test/check_production.py --harts $(HART_COUNTS)

verify-cache: verify-production
	python3 test/verify.py --icache-bytes 8192 --width 64 --width 512 --output result/icache --traffic-baseline result/verify/summary.json $(foreach name,$(ICACHE_CASES),--case $(name))
	python3 test/verify.py --icache-bytes 8192 --multicore-only --output result/icache-multicore $(foreach count,$(filter-out 15,$(HART_COUNTS)),--harts $(count)) --case synchronization --case atomic --case atomic_interrupt --case protection --case interrupt
	python3 test/verify.py --icache-bytes 65536 --width 64 --pmp-entries 0 --output result/icache-large --case pipeline_reuse --case synchronization --case fence_i_prefetch

verify-platform: verify-cache
	python3 test/verify.py --platform-only --output result/platform
	for profile in 2:64 16:512; do \
		count=$${profile%:*}; width=$${profile#*:}; config=result/platform/harts$$count-axi$$width/input.json; \
		for program in software/tests/console.S software/tests/integer.c; do \
			name=$${program##*/}; name=$${name%.*}-harts$$count; \
			python3 scripts/build_software.py --config $$config --program $$program --stack-bytes 512 --output result/software/$$name && \
			python3 test/verify.py --elf result/software/$$name/software.elf --config $$config --output result/software-verify/$$name || exit $$?; \
		done; \
	done
	python3 test/verify.py --elf result/software/integer-harts2/software.elf --config result/platform/harts2-axi64/input.json --output result/software-verify/initialization --poison-bss

verify-formal: verify-platform
	python3 test/formal.py
	python3 test/formal.py --rtl result/production-pmp16 --output result/formal/pmp16
	python3 test/formal.py --rtl result/verify/pmp16-axi64/rtl --output result/formal/pmp16-pa32 --modules Pmp Axi
	python3 test/formal.py --rtl result/production-irq --output result/formal/irq --modules InterruptCsr InterruptBackend WfiBackend
	python3 test/formal.py --rtl result/verify/irq-axi64/rtl --output result/formal/irq-pa32 --modules InterruptCsr InterruptBackend WfiBackend
	python3 test/formal.py --rtl result/icache/axi64/rtl --output result/formal/icache-pa32 --modules InstructionCache SynchronizationBackend WfiFrontend WfiBackend
	python3 test/formal.py --rtl result/icache/irq-pmp16-axi512/rtl --output result/formal/icache --modules InstructionCache SynchronizationBackend WfiFrontend WfiBackend
	python3 test/formal.py --rtl result/platform/harts2-axi64/rtl --output result/formal/platform --modules LocalInterrupts
	python3 test/formal.py --rtl result/platform/harts16-axi512/rtl --output result/formal/platform-harts16 --modules LocalInterrupts Lsu WfiBackend
	for count in $(HART_COUNTS); do python3 test/formal.py --rtl result/production-harts$$count --output result/formal/harts$$count --modules MemoryArbiter || exit $$?; done

clean:
	rm -rf result
