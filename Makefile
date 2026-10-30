# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT

.PHONY: config check rtl software verify-software verify-data-software verify-supervisor-software zephyr verify-zephyr verify-zephyr-long verify-signoff verify-simulation verify-production verify-cache verify-platform verify-user verify-data-cache verify-supervisor verify-formal verify-scalar-formal verify-user-formal verify-data-formal verify-supervisor-formal verify-translation verify-translation-formal verify-translation-software verify-translation-cache verify-translation-cache-formal verify-translation-cache-software clean
.PHONY: verify-burst verify-burst-formal verify-burst-software verify-widths verify-width-software
.PHONY: verify-data-line verify-data-line-software verify-read-capacity verify-read-software
.PHONY: verify-writeback verify-writeback-software verify-scalar-isa verify-compressed-isa

HART_COUNTS ?= 2 3 15 16
SCALAR_OUTPUT ?= result/scalar-isa/gate
COMPRESSED_OUTPUT ?= result/compressed-isa
COMPRESSED_CASES := $(addprefix compressed_,integer boundary illegal breakpoint groups control)
COMPRESSED_ARGS = $(foreach name,$(COMPRESSED_CASES),--case $(name))
MULDIV_CASES := $(addprefix muldiv_,0 1 2 3 4 5 6 7 0w 4w 5w 6w 7w)
ATOMIC_CASES := $(foreach size,2 3,$(addsuffix _$(size),$(addprefix atomic_,0 1 4 8 12 16 20 24 28) atomic_reservation))
SCALAR_CASES := $(MULDIV_CASES) $(ATOMIC_CASES) integer_reserved integer_breakpoint
SCALAR_CACHE := --icache-bytes 8192 --dcache-bytes 8192 --dcache-writeback --l2-cache-bytes 131072
ICACHE_CASES := pipeline_reuse pipeline_integer_stream pipeline_dependency_stream pipeline_dependency_chain cache_replacement fence_ordering fence_i_prefetch synchronization atomic_ordering atomic_denied atomic_retry bus_fetch pipeline_redirect pmp_fetch pmp_update interrupt_fence interrupt_fence_i interrupt_fetch_fault
PIPELINE_CASES := memory_groups memory_group_alignment memory_group_bus_read memory_group_bus_write pipeline_recovery pipeline_recovery_fault
USER_CASES := user_access user_system user_wait user_protection user_fetch user_mprv
SUPERVISOR_CASES := supervisor_traps supervisor_csr supervisor_mprv
TRANSLATION_CASES := sv39_data sv39_reuse sv39_protection sv39_large sv39_gigantic sv39_accessed sv39_dirty sv39_user_denied sv39_sum sv39_mxr sv39_canonical sv39_context
SOFTWARE_HARTS ?= 2
SOFTWARE_CONFIG ?= software/platform.json
SOFTWARE_OUTPUT ?= result/software
SOFTWARE_JOBS ?= 1
SOFTWARE_ICACHE_BYTES ?= $(if $(filter 16,$(SOFTWARE_HARTS)),8192,0)
SOFTWARE_DCACHE_BYTES ?= 0
SOFTWARE_PROFILE = --config $(SOFTWARE_CONFIG) --harts $(SOFTWARE_HARTS) --icache-bytes $(SOFTWARE_ICACHE_BYTES) --dcache-bytes $(SOFTWARE_DCACHE_BYTES) --console-base 0x10000000
ZEPHYR_TRANSACTIONS_1 := 280000
ZEPHYR_TRANSACTIONS_2 := 480000
ZEPHYR_TRANSACTIONS_16 := 2500000
ZEPHYR_TIMEOUT_1 := 600
ZEPHYR_TIMEOUT_2 := 600
ZEPHYR_TIMEOUT_16 := 5400

config:
	configure-ditdah-a1 --output result/ditdah_a1_config.json

check:
	configure-ditdah-a1 --check

rtl:
	build-ditdah-a1

software:
	for program in software/tests/console.S software/tests/integer.c; do \
		name=$${program##*/}; name=$${name%.*}; \
		python3 scripts/build_software.py $(SOFTWARE_PROFILE) --program $$program --stack-bytes 512 --output $(SOFTWARE_OUTPUT)/harts$(SOFTWARE_HARTS)/$$name || exit $$?; \
	done

verify-software: software
	for name in console integer; do \
		image=$(SOFTWARE_OUTPUT)/harts$(SOFTWARE_HARTS)/$$name; \
		python3 test/verify.py --elf $$image/software.elf --config $$image/input.json --output $$image/verification --jobs $(SOFTWARE_JOBS) || exit $$?; \
	done

verify-data-software:
	for count in 1 2 16; do $(MAKE) verify-software SOFTWARE_HARTS=$$count SOFTWARE_DCACHE_BYTES=8192 SOFTWARE_OUTPUT=$(SOFTWARE_OUTPUT)/data-cache || exit $$?; done

verify-supervisor-software:
	for count in 1 2 16; do for cache in 0 8192; do \
		image=$(SOFTWARE_OUTPUT)/supervisor/harts$$count-cache$$cache; \
		python3 scripts/build_software.py --config $(SOFTWARE_CONFIG) --supervisor-mode --expected-interrupt 1 --harts $$count --icache-bytes $$cache --dcache-bytes $$cache --console-base 0x10000000 --program software/tests/supervisor.S --stack-bytes 512 --output $$image && \
		python3 test/verify.py --elf $$image/software.elf --config $$image/input.json --output $$image/verification --jobs $(SOFTWARE_JOBS) || exit $$?; \
	done; done

zephyr:
	@test -n "$(ZEPHYR_TRANSACTIONS_$(SOFTWARE_HARTS))" || { echo 'Select SOFTWARE_HARTS=1, 2 or 16'; exit 1; }
	python3 scripts/build_zephyr.py $(SOFTWARE_PROFILE) --timebase-hz 10000000 --output $(SOFTWARE_OUTPUT)/zephyr-harts$(SOFTWARE_HARTS)

verify-zephyr: zephyr
	python3 test/verify.py --elf $(SOFTWARE_OUTPUT)/zephyr-harts$(SOFTWARE_HARTS)/software.elf --config $(SOFTWARE_OUTPUT)/zephyr-harts$(SOFTWARE_HARTS)/input.json --output $(SOFTWARE_OUTPUT)/zephyr-harts$(SOFTWARE_HARTS)/verification --software-transactions $(ZEPHYR_TRANSACTIONS_$(SOFTWARE_HARTS)) --software-timeout $(ZEPHYR_TIMEOUT_$(SOFTWARE_HARTS)) --jobs $(SOFTWARE_JOBS)

verify-zephyr-long:
	for count in 1 2 16; do $(MAKE) verify-zephyr SOFTWARE_HARTS=$$count || exit $$?; done

verify-signoff: verify-writeback verify-formal
	$(MAKE) verify-scalar-isa
	$(MAKE) verify-compressed-isa
	$(MAKE) verify-widths
	$(MAKE) verify-data-line
	$(MAKE) verify-read-capacity
	$(MAKE) verify-memory-concurrency
	$(MAKE) verify-prediction
	$(MAKE) verify-cache-configuration
	$(MAKE) verify-shared-cache
	$(MAKE) verify-translation-context SOFTWARE_CONFIG=$(SHARED_OUTPUT)/software/w3-h16/input.json

.PHONY: verify-shared-cache
SHARED_OUTPUT ?= result/shared-cache-signoff
SHARED_ARGS = --load-queue-entries 2 --fabric-read-slots 4 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-ways 2 --dcache-refill-bytes 64 --dcache-writeback
verify-shared-cache:
	python3 test/verify.py --shared-cache-arrays --output $(SHARED_OUTPUT)/arrays
	for bus in 256 512; do python3 test/formal.py --rtl $(SHARED_OUTPUT)/arrays/axi$$bus/rtl --output $(SHARED_OUTPUT)/formal$$bus --modules SharedCache || exit $$?; done
	for profile in 2:128:2 16:512:3; do \
		count=$${profile%%:*}; rest=$${profile#*:}; bus=$${rest%%:*}; width=$${rest#*:}; \
		python3 test/verify.py $(SHARED_ARGS) --l2-cache-bytes 131072 --multicore-only --harts $$count --width $$bus --issue-width $$width --output $(SHARED_OUTPUT)/harts$$count --case data_coherence --case writeback_retry --case synchronization --case cache_reservation --case atomic_lrsc_shared --case atomic_interrupt || exit $$?; \
	done
	python3 test/verify.py $(SHARED_ARGS) --fabric-read-slots 3 --l2-cache-bytes 131072 --user-mode --interrupts --width 512 --issue-width 3 --output $(SHARED_OUTPUT)/protected --case user_mprv --case pmp_update --case pmp_permissions --case interrupt_read_pending --case synchronization --case fence_i_prefetch --case fence_ordering
	python3 test/verify.py $(SHARED_ARGS) --fabric-read-slots 3 --l2-cache-bytes 131072 --sv39 --tlb-entries 4 --width 256 --issue-width 3 --output $(SHARED_OUTPUT)/translation --case sv39_context --case sv39_reuse --case sv39_accessed --case sv39_protection --case sv39_sum --case sv39_mxr
	python3 test/verify.py $(SHARED_ARGS) --dcache-ways 1 --multicore-only --harts 2 --width 128 --issue-width 2 --output $(SHARED_OUTPUT)/conflict0 --case cache_conflict
	python3 test/verify.py $(SHARED_ARGS) --dcache-ways 1 --l2-cache-bytes 131072 --multicore-only --harts 2 --width 128 --issue-width 2 --output $(SHARED_OUTPUT)/conflict1 --case cache_conflict --shared-cache-baseline $(SHARED_OUTPUT)/conflict0/summary.json
	python3 test/verify.py --software-matrix --config $(SOFTWARE_CONFIG) --l2-cache-bytes 131072 --load-queue-entries 2 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-ways 2 --dcache-refill-bytes 64 --dcache-writeback --output $(SHARED_OUTPUT)/software --jobs $(SOFTWARE_JOBS)

.PHONY: verify-cache-configuration
CACHE_OUTPUT ?= result/cache-configuration
verify-cache-configuration:
	for ways in 1 2; do \
		python3 test/verify.py --cache-matrix --dcache-ways $$ways --output $(CACHE_OUTPUT)/ways$$ways || exit $$?; \
	done
	for profile in 8192:8:0 8192:8:1 65536:64:1; do \
		bytes=$${profile%%:*}; rest=$${profile#*:}; refill=$${rest%%:*}; writeback=$${rest#*:}; \
		python3 test/formal.py --rtl $(CACHE_OUTPUT)/ways2/c$$bytes-r$$refill-w$$writeback/rtl --output $(CACHE_OUTPUT)/formal-c$$bytes-r$$refill-w$$writeback --modules DataCacheAssociativity || exit $$?; \
	done
	for bytes in 8192 65536; do \
		python3 test/verify.py --cache-matrix --dcache-bytes $$bytes --dcache-ways 2 --load-queue-entries 2 --output $(CACHE_OUTPUT)/dual$$bytes || exit $$?; \
	done
	for profile in 8192:8 65536:64; do \
		bytes=$${profile%:*}; refill=$${profile#*:}; \
		python3 test/formal.py --rtl $(CACHE_OUTPUT)/dual$$bytes/c$$bytes-r$$refill-w1/rtl --output $(CACHE_OUTPUT)/formal-dual$$bytes --modules DataCacheAssociativity --jobs $(FORMAL_JOBS) || exit $$?; \
	done
	for profile in 2:8192:64:1:8 2:16384:128:2:64 16:65536:512:3:64; do \
		count=$${profile%%:*}; rest=$${profile#*:}; bytes=$${rest%%:*}; rest=$${rest#*:}; bus=$${rest%%:*}; rest=$${rest#*:}; width=$${rest%%:*}; refill=$${rest#*:}; \
		python3 test/verify.py --multicore-only --harts $$count --width $$bus --issue-width $$width --load-queue-entries 2 --fabric-read-slots 4 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes $$bytes --dcache-ways 2 --dcache-refill-bytes $$refill --dcache-writeback --output $(CACHE_OUTPUT)/harts$$count-c$$bytes --case data_coherence --case synchronization --case cache_reservation --case atomic_lrsc_shared --case atomic_interrupt || exit $$?; \
	done
	python3 test/verify.py --user-mode --interrupts --width 512 --issue-width 3 --load-queue-entries 2 --fabric-read-slots 3 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 65536 --dcache-ways 2 --dcache-refill-bytes 64 --dcache-writeback --output $(CACHE_OUTPUT)/protected --case user_mprv --case pmp_update --case pmp_permissions --case interrupt_read_pending --case synchronization --case fence_i_prefetch --case fence_ordering
	python3 test/verify.py --sv39 --tlb-entries 4 --width 256 --issue-width 3 --load-queue-entries 2 --fabric-read-slots 3 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 65536 --dcache-ways 2 --dcache-refill-bytes 64 --dcache-writeback --output $(CACHE_OUTPUT)/translation --case sv39_context --case sv39_reuse --case sv39_accessed --case sv39_protection --case sv39_sum --case sv39_mxr
	for ways in 1 2; do \
		comparison=""; if test $$ways = 2; then comparison="--cache-baseline $(CACHE_OUTPUT)/conflict1/summary.json"; fi; \
		python3 test/verify.py --width 128 --pmp-entries 0 --dcache-bytes 8192 --dcache-ways $$ways $$comparison --output $(CACHE_OUTPUT)/conflict$$ways --case cache_conflict || exit $$?; \
	done
	python3 test/verify.py --software-matrix --config $(SOFTWARE_CONFIG) --load-queue-entries 2 --branch-prediction --branch-predictor-entries 8 --icache-bytes 8192 --burst-refill --dcache-bytes 65536 --dcache-ways 2 --dcache-refill-bytes 64 --dcache-writeback --output $(CACHE_OUTPUT)/software --jobs $(SOFTWARE_JOBS)
	$(MAKE) verify-translation-software SOFTWARE_CONFIG=$(CACHE_OUTPUT)/software/w3-h16/input.json SOFTWARE_OUTPUT=$(CACHE_OUTPUT)/software SOFTWARE_TLB_ENTRIES=4 SOFTWARE_CACHE_SIZES=65536 SOFTWARE_BURST_REFILL=--burst-refill TRANSLATION_SOFTWARE_DIR=translation

.PHONY: verify-prediction
PREDICTION_OUTPUT ?= result/prediction
FORMAL_JOBS ?= 1
verify-prediction:
	for mode in disabled 0 8 16; do \
		prediction=""; comparison=""; \
		if test $$mode != disabled; then prediction="--branch-prediction --branch-predictor-entries $$mode"; fi; \
		if test $$mode = 8; then comparison="--prediction-baseline $(PREDICTION_OUTPUT)/0/summary.json"; fi; \
		python3 test/verify.py --width 128 --issue-width 3 --pmp-entries 0 --icache-bytes 8192 --burst-refill $$prediction $$comparison --output $(PREDICTION_OUTPUT)/$$mode --case branch_window --case return_window --case return_switch --case pipeline_recovery --case pipeline_recovery_fault --case pipeline_redirect --case pipeline_older_fault --case pipeline_reuse || exit $$?; \
	done
	python3 test/verify.py --user-mode --interrupts --width 512 --issue-width 3 --load-queue-entries 2 --fabric-read-slots 3 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --dcache-writeback --branch-prediction --branch-predictor-entries 8 --output $(PREDICTION_OUTPUT)/protected --case user_mprv --case pmp_update --case pmp_permissions --case interrupt_read_pending --case synchronization --case fence_i_prefetch --case fence_ordering --case pipeline_recovery --case pipeline_recovery_fault --case pipeline_redirect --case pipeline_older_fault --case return_switch
	python3 test/verify.py --sv39 --tlb-entries 4 --width 256 --issue-width 2 --load-queue-entries 2 --fabric-read-slots 3 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --dcache-writeback --branch-prediction --branch-predictor-entries 16 --output $(PREDICTION_OUTPUT)/translation --case sv39_context --case sv39_reuse --case sv39_accessed --case sv39_protection --case sv39_sum --case sv39_mxr
	python3 test/verify.py --software-matrix --config $(SOFTWARE_CONFIG) --load-queue-entries 2 --branch-prediction --branch-predictor-entries 8 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --dcache-writeback --output $(PREDICTION_OUTPUT)/software --jobs $(SOFTWARE_JOBS)
	python3 test/formal.py --rtl $(PREDICTION_OUTPUT)/8/axi128/rtl --output $(PREDICTION_OUTPUT)/formal --modules WfiFrontend PipelineBackend --jobs $(FORMAL_JOBS)
	python3 test/formal.py --rtl $(PREDICTION_OUTPUT)/16/axi128/rtl --output $(PREDICTION_OUTPUT)/formal16 --modules WfiFrontend --jobs $(FORMAL_JOBS)

.PHONY: verify-memory-concurrency
verify-memory-concurrency:
	python3 test/verify.py --multicore-only --harts 1 --width 64 --pmp-entries 0 --load-queue-entries 2 --fabric-read-slots 1 --dcache-bytes 8192 --output result/dual-load-serial --case load_window --case load_cancel
	for profile in 1:2 2:4; do \
		count=$${profile%:*}; slots=$${profile#*:}; \
		python3 test/verify.py --multicore-only --harts $$count --width 128 --pmp-entries 0 --load-queue-entries 2 --fabric-read-slots $$slots --dcache-bytes 8192 --output result/dual-load --case load_window --case load_cancel || exit $$?; \
	done
	python3 test/formal.py --rtl result/dual-load/harts1-axi128/rtl --output result/formal/dual-load --modules LsuReads ReadQueue PipelineBackend
	python3 test/verify.py --multicore-only --harts 1 --width 256 --issue-width 2 --pmp-entries 0 --load-queue-entries 2 --fabric-read-slots 2 --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/dual-load-line --case load_window --case load_cancel
	python3 test/verify.py --multicore-only --interrupts --harts 2 --width 64 --issue-width 2 --load-queue-entries 2 --pmp-entries 0 --dcache-bytes 8192 --dcache-writeback --output result/dual-load-writeback --case data_coherence --case synchronization --case atomic_interrupt --case cache_reservation --case interrupt
	python3 test/verify.py --user-mode --interrupts --width 512 --issue-width 3 --load-queue-entries 2 --fabric-read-slots 3 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --dcache-writeback --output result/dual-load-protection --case user_mprv --case pmp_update --case pmp_permissions --case interrupt_read_pending --case synchronization --case fence_i_prefetch --case fence_ordering
	python3 test/verify.py --sv39 --tlb-entries 2 --width 512 --issue-width 3 --load-queue-entries 2 --fabric-read-slots 3 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/dual-load-translation --case sv39_context --case sv39_reuse --case sv39_accessed
	python3 test/verify.py --software-matrix --load-queue-entries 2 --config $(SOFTWARE_CONFIG) --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --output $(SOFTWARE_OUTPUT)/dual-load --jobs $(SOFTWARE_JOBS)
	$(MAKE) verify-translation-software SOFTWARE_CONFIG=$(SOFTWARE_OUTPUT)/dual-load/w3-h16/input.json SOFTWARE_TLB_ENTRIES=4 SOFTWARE_CACHE_SIZES=8192 SOFTWARE_BURST_REFILL=--burst-refill TRANSLATION_SOFTWARE_DIR=dual-load-translation

verify-writeback:
	for profile in 2:64:1:8 2:128:2:64 16:512:3:64; do \
		count=$${profile%%:*}; rest=$${profile#*:}; bus=$${rest%%:*}; rest=$${rest#*:}; width=$${rest%%:*}; span=$${rest#*:}; \
		python3 test/verify.py --multicore-only --harts $$count --width $$bus --issue-width $$width --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes $$span --dcache-writeback --output result/writeback-harts$$count-axi$$bus --case data_coherence --case synchronization --case cache_reservation --case atomic_lrsc_shared --case atomic_interrupt || exit $$?; \
		python3 test/formal.py --rtl result/writeback-harts$$count-axi$$bus/harts$$count-axi$$bus/rtl --output result/formal/writeback-harts$$count-axi$$bus --modules DataCacheWriteback Coherence MemoryArbiter MemoryFabric || exit $$?; \
	done
	python3 test/verify.py --sv39 --tlb-entries 4 --width 256 --issue-width 2 --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --dcache-writeback --output result/writeback-translation --case sv39_context --case sv39_reuse --case sv39_protection --case sv39_sum --case sv39_mxr
	python3 test/verify.py --user-mode --interrupts --width 512 --pmp-entries 16 --dcache-bytes 8192 --dcache-writeback --output result/writeback-protection --case user_mprv --case pmp_update --case pmp_permissions --case interrupt_read_pending --case synchronization
	$(MAKE) verify-writeback-software

verify-writeback-software:
	python3 test/verify.py --software-refill-matrix --config $(SOFTWARE_CONFIG) --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-writeback --issue-width 3 --output $(SOFTWARE_OUTPUT)/writeback --jobs $(SOFTWARE_JOBS)
	$(MAKE) verify-translation-software SOFTWARE_CONFIG=$(SOFTWARE_OUTPUT)/writeback/r64-h16/input.json SOFTWARE_TLB_ENTRIES=4 SOFTWARE_CACHE_SIZES=8192 SOFTWARE_BURST_REFILL=--burst-refill TRANSLATION_SOFTWARE_DIR=writeback-sv39

verify-read-capacity:
	for profile in 1:1:64:1 1:2:512:2 2:1:64:1 2:2:64:1 2:4:64:2 3:3:128:2 16:4:256:2 16:4:512:3; do \
		count=$${profile%%:*}; rest=$${profile#*:}; slots=$${rest%%:*}; rest=$${rest#*:}; bus=$${rest%%:*}; width=$${rest#*:}; \
		cases="--case data_coherence --case synchronization"; \
		if test $$count -gt 1; then cases="$$cases --case atomic_lrsc_shared --case atomic_interrupt"; fi; \
		python3 test/verify.py --multicore-only --harts $$count --fabric-read-slots $$slots --width $$bus --issue-width $$width --pmp-entries 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/read-slots-harts$$count-$$slots-$$bus $$cases || exit $$?; \
		python3 test/formal.py --rtl result/read-slots-harts$$count-$$slots-$$bus/harts$$count-axi$$bus/rtl --output result/formal/read-slots-harts$$count-$$slots-$$bus --modules ReadQueue MemoryFabric || exit $$?; \
	done
	$(MAKE) verify-read-software

verify-read-software:
	python3 test/verify.py --software-read-matrix --config $(SOFTWARE_CONFIG) --harts 16 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --output $(SOFTWARE_OUTPUT)/read-slots --jobs $(SOFTWARE_JOBS)

verify-data-line:
	for span in 8 64; do \
		python3 test/verify.py --interrupts --width 64 --pmp-entries 0 --dcache-bytes 8192 --dcache-refill-bytes $$span --output result/data-line-work-$$span --case data_cache_cold --case data_cache_warm --case data_cache_sparse || exit $$?; \
	done
	python3 test/verify.py --user-mode --interrupts --width 512 --pmp-entries 16 --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/data-line-protected --case data_cache_word_boundary --case data_cache_boundary --case data_cache_narrow --case data_cache_retry --case pmp_update --case user_mprv --case interrupt_read_pending
	python3 test/verify.py --width 128 --width 256 --width 512 --pmp-entries 0 --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/data-line-wide --case data_cache_cold --case data_cache_narrow --case data_cache_retry
	for profile in 0:64:1 2:128:2 4:512:3; do \
		entries=$${profile%%:*}; rest=$${profile#*:}; bus=$${rest%%:*}; width=$${rest#*:}; \
		python3 test/verify.py --sv39 --tlb-entries $$entries --width $$bus --pmp-entries 16 --issue-width $$width --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/data-line-translation-$$entries --case sv39_reuse --case sv39_protection --case sv39_sum --case sv39_mxr --case sv39_context || exit $$?; \
	done
	for profile in 2:64:1 2:128:2 2:256:3 2:512:2 16:512:3; do \
		count=$${profile%%:*}; rest=$${profile#*:}; bus=$${rest%%:*}; width=$${rest#*:}; \
		python3 test/verify.py --multicore-only --harts $$count --width $$bus --pmp-entries 16 --issue-width $$width --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --output result/data-line-harts$$count-axi$$bus --case data_coherence --case synchronization --case atomic_lrsc_shared --case atomic_lrsc_private --case atomic_interrupt || exit $$?; \
	done
	python3 test/formal.py --rtl result/data-line-work-64/irq-axi64/rtl --output result/formal/data-line --modules DataCache Memory Axi
	python3 test/formal.py --rtl result/data-line-protected/irq-pmp16-axi512/rtl --output result/formal/data-line-protected --modules Pmp Lsu DataCache Memory Axi
	python3 test/formal.py --rtl result/data-line-translation-4/irq-pmp16-axi512/rtl --output result/formal/data-line-translation --modules Translation Lsu Coherence WfiFrontend
	for profile in 2:64 2:512 16:512; do \
		count=$${profile%:*}; bus=$${profile#*:}; \
		python3 test/formal.py --rtl result/data-line-harts$$count-axi$$bus/harts$$count-axi$$bus/rtl --output result/formal/data-line-fabric-$$count-$$bus --modules ReadQueue MemoryFabric || exit $$?; \
	done
	build-ditdah-a1 --no-trace --config result/data-line-protected/irq-pmp16-axi512/input.json --output result/production-data-line
	build-ditdah-a1 --no-trace --config result/data-line-harts16-axi512/harts16-axi512/input.json --output result/production-data-line-burst
	python3 test/check_production.py --dcache-refill-bytes 64
	$(MAKE) verify-data-line-software

verify-data-line-software:
	python3 test/verify.py --software-refill-matrix --config $(SOFTWARE_CONFIG) --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --issue-width 3 --output $(SOFTWARE_OUTPUT)/data-line --jobs $(SOFTWARE_JOBS)

verify-widths:
	for width in 1 2 3; do \
		python3 test/verify.py --issue-width $$width --width 64 --pmp-entries 0 --icache-bytes 8192 --dcache-bytes 8192 --output result/widths/w$$width \
			--case pipeline_integer_stream --case pipeline_dependency_stream --case pipeline_dependency_chain --case pipeline_redirect --case memory_word --case data_cache --case data_cache_narrow --case data_cache_retry $(foreach name,$(PIPELINE_CASES),--case $(name)) || exit $$?; \
	done
	python3 test/verify.py --issue-width 3 --branch-prediction --width 64 --pmp-entries 0 --icache-bytes 8192 --output result/widths/prediction $(foreach name,$(PIPELINE_CASES),--case $(name)) --case pipeline_redirect --case pipeline_older_fault --case pipeline_integer_stream
	python3 test/verify.py --issue-width 3 --width 64 --pmp-entries 0 --output result/widths/uncached --case pipeline_redirect --case memory_word
	python3 test/verify.py --issue-width 1 --branch-prediction --width 64 --pmp-entries 0 --output result/widths/prediction-uncached --case pipeline_recovery --case pipeline_redirect
	for profile in 2:64:2 3:512:4; do \
		width=$${profile%%:*}; rest=$${profile#*:}; bus=$${rest%%:*}; entries=$${rest#*:}; \
		python3 test/verify.py --issue-width $$width --sv39 --tlb-entries $$entries --width $$bus --pmp-entries 16 --icache-bytes 8192 --dcache-bytes 8192 --output result/widths/translation-w$$width \
			--case sv39_integer_stream --case sv39_reuse --case sv39_protection --case sv39_sum --case sv39_mxr --case sv39_context --case data_cache_boundary --case memory_group_pmp --case memory_group_page --case memory_group_interrupt || exit $$?; \
	done
	python3 test/formal.py --rtl result/widths/translation-w2/irq-pmp16-axi64/rtl --output result/formal/pipeline-w2 --modules PipelineBackend WfiFrontend
	python3 test/formal.py --rtl result/widths/prediction/irq-axi64/rtl --output result/formal/pipeline-prediction --modules PipelineBackend WfiFrontend
	build-ditdah-a1 --no-trace --config result/widths/w2/irq-axi64/input.json --output result/production-width2
	build-ditdah-a1 --no-trace --config result/widths/prediction/irq-axi64/input.json --output result/production-prediction
	python3 test/check_production.py --pipeline
	$(MAKE) verify-width-software

verify-width-software:
	python3 test/verify.py --software-matrix --config $(SOFTWARE_CONFIG) --icache-bytes 8192 --dcache-bytes 8192 --output $(SOFTWARE_OUTPUT)/widths --jobs $(SOFTWARE_JOBS)

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

verify-user: verify-platform
	python3 test/verify.py --user-mode --width 64 --pmp-entries 16 --output result/user $(foreach name,$(USER_CASES),--case $(name))
	python3 test/verify.py --user-mode --width 512 --pmp-entries 16 --interrupts --icache-bytes 8192 --output result/user-cache $(foreach name,$(USER_CASES),--case $(name)) --case user_interrupt
	python3 test/verify.py --user-mode --width 64 --pmp-entries 0 --interrupts --output result/user-pmp0 --case user_access --case user_system --case user_wait --case user_interrupt
	python3 test/verify.py --user-mode --platform-only --harts 16 --width 512 --pmp-entries 16 --icache-bytes 8192 --output result/user-multicore --case user_isolation --case user_device

verify-data-cache: verify-user
	python3 test/verify.py --dcache-bytes 8192 --width 64 --pmp-entries 0 --output result/data-cache --case data_cache --case memory_word --case atomic_ordering --case bus_read --case bus_write
	python3 test/verify.py --dcache-bytes 8192 --icache-bytes 8192 --user-mode --interrupts --width 512 --pmp-entries 16 --output result/data-cache-user --case data_cache --case pmp_update --case user_access --case user_protection --case user_mprv --case user_interrupt
	python3 test/verify.py --dcache-bytes 8192 --multicore-only --output result/data-coherence --harts 2 --harts 3 --harts 16 --case data_coherence --case synchronization --case atomic_lrsc_shared --case atomic_lrsc_private
	python3 test/verify.py --dcache-bytes 8192 --user-mode --platform-only --harts 16 --width 512 --pmp-entries 16 --icache-bytes 8192 --output result/data-platform --case user_isolation --case user_device
	build-ditdah-a1 --no-trace --config result/data-cache-user/irq-pmp16-axi512/input.json --output result/production-dcache
	build-ditdah-a1 --no-trace --config result/data-coherence/harts16-axi512/input.json --output result/production-dcache-harts16
	build-ditdah-a1 --no-trace --top DitDahA1MemoryFabric --config result/data-coherence/harts16-axi512/input.json --output result/fabric-dcache
	python3 test/check_production.py --data-cache
	$(MAKE) verify-data-software

verify-formal: verify-burst-formal
	python3 test/formal.py --rtl result/multicore/harts2-axi64/rtl --output result/formal/read-fabric --modules ReadQueue MemoryFabric
	python3 test/formal.py --rtl result/multicore/harts16-axi512/rtl --output result/formal/read-queue-wide --modules ReadQueue

verify-burst: verify-translation-cache-formal
	python3 test/verify.py --burst-refill --icache-bytes 8192 --user-mode --width 64 --pmp-entries 16 --output result/burst
	python3 test/verify.py --burst-refill --icache-bytes 8192 --width 128 --width 256 --width 512 --pmp-entries 0 --output result/burst-wide
	python3 test/verify.py --burst-refill --icache-bytes 8192 --multicore-only --harts 2 --width 64 --pmp-entries 0 --output result/burst-harts2 --case synchronization --case data_coherence --case atomic_lrsc_shared --case exchange
	python3 test/verify.py --burst-refill --icache-bytes 8192 --dcache-bytes 8192 --multicore-only --harts 16 --width 512 --pmp-entries 16 --interrupts --output result/burst-harts16
	python3 test/verify.py --burst-refill --sv39 --tlb-entries 4 --icache-bytes 8192 --dcache-bytes 8192 --width 512 --pmp-entries 16 --output result/burst-translation --case sv39_reuse --case sv39_protection --case sv39_sum --case sv39_mxr --case sv39_context
	$(MAKE) verify-burst-software
	build-ditdah-a1 --no-trace --config $(SOFTWARE_OUTPUT)/burst/harts16-cache8192/input.json --output result/production-burst
	python3 test/check_production.py --sv39 --tlb-entries 4 --burst-refill

verify-burst-formal: verify-burst
	python3 test/formal.py --rtl result/burst/pmp16-axi64/rtl --output result/formal/burst --modules Pmp Fetch InstructionCache Memory MemoryArbiter Axi WfiFrontend
	python3 test/formal.py --rtl result/burst-translation/irq-pmp16-axi512/rtl --output result/formal/burst-wide --modules Pmp SupervisorFetch InstructionCache Memory MemoryArbiter Axi Coherence WfiFrontend

.PHONY: verify-translation-context
TRANSLATION_OUTPUT ?= result/translation-context-signoff
TRANSLATION_ARGS = --sv39 --i-tlb-entries 2 --d-tlb-entries 2 --pmp-entries 16 --issue-width 3
verify-translation-context:
	for entries in 0 4; do \
		comparison=""; if test $$entries = 4; then comparison="--translation-baseline $(TRANSLATION_OUTPUT)/shared0/summary.json"; fi; \
		python3 test/verify.py $(TRANSLATION_ARGS) --tlb-entries $$entries --width 64 --output $(TRANSLATION_OUTPUT)/shared$$entries --case sv39_working_set --case sv39_asid $$comparison || exit $$?; \
	done
	python3 test/verify.py $(TRANSLATION_ARGS) --asid-bits 4 --tlb-entries 4 --width 256 --load-queue-entries 2 --fabric-read-slots 3 --icache-bytes 8192 --burst-refill --dcache-bytes 8192 --dcache-refill-bytes 64 --dcache-writeback --l2-cache-bytes 131072 --output $(TRANSLATION_OUTPUT)/coherent --case sv39_asid --case sv39_context --case sv39_protection --case sv39_accessed --case sv39_sum --case sv39_mxr
	for profile in shared0:64 shared4:64 coherent:256; do \
		name=$${profile%:*}; bus=$${profile#*:}; \
		python3 test/formal.py --rtl $(TRANSLATION_OUTPUT)/$$name/irq-pmp16-axi$$bus/rtl --output $(TRANSLATION_OUTPUT)/formal-$$name --modules Translation --jobs $(FORMAL_JOBS) || exit $$?; \
	done
	python3 test/formal.py --rtl $(TRANSLATION_OUTPUT)/coherent/irq-pmp16-axi256/rtl --output $(TRANSLATION_OUTPUT)/formal-scalar --modules SupervisorCsr SupervisorExecute IntegerDecode --jobs $(FORMAL_JOBS)
	$(MAKE) verify-translation-software SOFTWARE_OUTPUT=$(TRANSLATION_OUTPUT)/software SOFTWARE_TLB_ENTRIES=4 SOFTWARE_CACHE_SIZES=8192 SOFTWARE_BURST_REFILL=--burst-refill SOFTWARE_TRANSLATION_ARGS="--asid-bits 4 --i-tlb-entries 2 --d-tlb-entries 2 --dcache-refill-bytes 64" TRANSLATION_SOFTWARE_DIR=context
	build-ditdah-a1 --no-trace --config $(TRANSLATION_OUTPUT)/software/context/harts16-cache8192/input.json --output $(TRANSLATION_OUTPUT)/production-context
	python3 test/check_production.py --root $(TRANSLATION_OUTPUT) --translation-context --sv39 --tlb-entries 4 --i-tlb-entries 2 --d-tlb-entries 2 --asid-bits 4 --burst-refill --dcache-refill-bytes 64

verify-translation-cache: verify-translation-formal
	python3 test/verify.py --sv39 --tlb-entries 2 --width 64 --pmp-entries 16 --output result/translation-cache-small $(foreach name,$(TRANSLATION_CASES),--case $(name))
	python3 test/verify.py --sv39 --tlb-entries 2 --width 64 --pmp-entries 0 --output result/translation-cache-pmp0 --case sv39_reuse --case sv39_context
	python3 test/verify.py --sv39 --tlb-entries 4 --width 512 --pmp-entries 16 --icache-bytes 8192 --dcache-bytes 8192 --output result/translation-tlb --case sv39_reuse --case sv39_protection --case sv39_sum --case sv39_mxr --case sv39_context
	$(MAKE) verify-translation-cache-software
	build-ditdah-a1 --no-trace --config $(SOFTWARE_OUTPUT)/translation-cache/harts16-cache8192/input.json --output result/production-sv39-tlb4
	python3 test/check_production.py --sv39 --tlb-entries 4

verify-translation-cache-formal: verify-translation-cache
	python3 test/formal.py --rtl result/translation-cache-small/irq-pmp16-axi64/rtl --output result/formal/translation-cache-small --modules Translation
	python3 test/formal.py --rtl result/translation-cache-pmp0/irq-axi64/rtl --output result/formal/translation-cache-pmp0 --modules Translation
	python3 test/formal.py --rtl result/translation-tlb/irq-pmp16-axi512/rtl --output result/formal/translation-tlb --modules Translation

verify-translation-cache-software:
	$(MAKE) verify-translation-software SOFTWARE_TLB_ENTRIES=4 TRANSLATION_SOFTWARE_DIR=translation-cache

SOFTWARE_TLB_ENTRIES ?= 0
SOFTWARE_TRANSLATION_ARGS ?=
TRANSLATION_SOFTWARE_DIR ?= translation
SOFTWARE_CACHE_SIZES ?= 0 8192
SOFTWARE_BURST_REFILL ?=

verify-burst-software:
	$(MAKE) verify-translation-software SOFTWARE_TLB_ENTRIES=4 SOFTWARE_CACHE_SIZES=8192 SOFTWARE_BURST_REFILL=--burst-refill TRANSLATION_SOFTWARE_DIR=burst

verify-translation-software:
	for count in 1 2 16; do for cache in $(SOFTWARE_CACHE_SIZES); do \
		image=$(SOFTWARE_OUTPUT)/$(TRANSLATION_SOFTWARE_DIR)/harts$$count-cache$$cache; \
		python3 scripts/build_software.py --config $(SOFTWARE_CONFIG) --sv39 --tlb-entries $(SOFTWARE_TLB_ENTRIES) $(SOFTWARE_TRANSLATION_ARGS) $(SOFTWARE_BURST_REFILL) --expected-interrupt 3 --harts $$count --icache-bytes $$cache --dcache-bytes $$cache --console-base 0x10000000 --program software/tests/virtual_memory.S --stack-bytes 512 --output $$image && \
		python3 test/verify.py --elf $$image/software.elf --config $$image/input.json --output $$image/verification --software-transactions $$((4096 * count)) --jobs $(SOFTWARE_JOBS) || exit $$?; \
	done; done

verify-translation: verify-supervisor-formal
	python3 test/verify.py --sv39 --width 64 --pmp-entries 16 --output result/translation $(foreach name,$(TRANSLATION_CASES),--case $(name))
	python3 test/verify.py --sv39 --width 512 --pmp-entries 16 --icache-bytes 8192 --dcache-bytes 8192 --output result/translation-cache --case sv39_data --case sv39_sum --case sv39_mxr --case sv39_context
	$(MAKE) verify-translation-software
	build-ditdah-a1 --no-trace --config $(SOFTWARE_OUTPUT)/translation/harts16-cache8192/input.json --output result/production-sv39
	python3 test/check_production.py --sv39

verify-translation-formal: verify-translation
	python3 test/formal.py --rtl result/translation/irq-pmp16-axi64/rtl --output result/formal/translation --modules Translation SupervisorCsr SupervisorExecute IntegerDecode
	python3 test/formal.py --rtl result/translation-cache/irq-pmp16-axi512/rtl --output result/formal/translation-cache --modules Translation SupervisorCsr SupervisorExecute Lsu

verify-supervisor: verify-data-formal
	python3 test/verify.py --supervisor-mode --width 64 --pmp-entries 16 --output result/supervisor $(foreach name,$(SUPERVISOR_CASES),--case $(name))
	python3 test/verify.py --supervisor-mode --width 512 --pmp-entries 16 --icache-bytes 8192 --dcache-bytes 8192 --output result/supervisor-cache $(foreach name,$(SUPERVISOR_CASES),--case $(name)) --case data_cache
	$(MAKE) verify-supervisor-software
	build-ditdah-a1 --no-trace --config $(SOFTWARE_OUTPUT)/supervisor/harts16-cache8192/input.json --output result/production-supervisor
	python3 test/check_production.py --supervisor

verify-supervisor-formal: verify-supervisor
	python3 test/formal.py --rtl result/supervisor/irq-pmp16-axi64/rtl --output result/formal/supervisor --modules SupervisorCsr SupervisorExecute SupervisorFetch Pmp Fetch Lsu Axi IntegerDecode
	python3 test/formal.py --rtl result/supervisor-cache/irq-pmp16-axi512/rtl --output result/formal/supervisor-cache --modules SupervisorCsr SupervisorExecute SupervisorFetch InstructionCache DataCache

verify-scalar-formal: verify-data-cache
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

verify-user-formal: verify-scalar-formal
	python3 test/formal.py --rtl result/user/pmp16-axi64/rtl --output result/formal/user --modules UserCsr UserExecute Csr Pmp Fetch Lsu Axi
	python3 test/formal.py --rtl result/user-cache/irq-pmp16-axi512/rtl --output result/formal/user-cache --modules UserCsr UserExecute Pmp InstructionCache Axi InterruptCsr

verify-data-formal: verify-user-formal
	python3 test/formal.py --rtl result/data-cache/axi64/rtl --output result/formal/data-cache --modules DataCache Coherence
	python3 test/formal.py --rtl result/data-cache-user/irq-pmp16-axi512/rtl --output result/formal/data-cache-user --modules DataCache Lsu
	for profile in 2:64 3:64 16:512; do \
		count=$${profile%:*}; width=$${profile#*:}; \
		python3 test/formal.py --rtl result/data-coherence/harts$$count-axi$$width/rtl --output result/formal/coherence-harts$$count --modules Coherence || exit $$?; \
	done

clean:
	rm -rf result

verify-scalar-isa:
	python3 test/verify.py --interrupts --issue-width 3 --width 64 --pmp-entries 0 $(foreach name,$(SCALAR_CASES) interrupt_divide,--case $(name)) --output $(SCALAR_OUTPUT)/enabled
	python3 test/formal.py --rtl $(SCALAR_OUTPUT)/enabled/irq-axi64/rtl --output $(SCALAR_OUTPUT)/formal --modules MulDiv IntegerDecode WordExecute Lsu Memory Axi InterruptBackend --jobs 2
	python3 test/verify.py --no-m --no-a --issue-width 2 --width 64 --pmp-entries 0 $(foreach name,$(SCALAR_CASES),--case $(name)) --output $(SCALAR_OUTPUT)/disabled
	python3 test/formal.py --rtl $(SCALAR_OUTPUT)/disabled/axi64/rtl --output $(SCALAR_OUTPUT)/disabled-formal --modules IntegerDecode Memory --jobs 2
	python3 test/verify.py $(SCALAR_CACHE) --issue-width 3 --load-queue-entries 2 --fabric-read-slots 4 --multicore-only --harts 2 --width 64 --pmp-entries 0 --case atomic_lrsc_shared_word --case atomic_lrsc_private_word --case atomic_lrsc_shared --case atomic_lrsc_private --case atomic --output $(SCALAR_OUTPUT)/coherent
	python3 test/verify.py $(SCALAR_CACHE) --sv39 --issue-width 2 --load-queue-entries 2 --width 512 --pmp-entries 16 --tlb-entries 4 --i-tlb-entries 4 --d-tlb-entries 4 --asid-bits 4 --case sv39_atomic --case sv39_protection --output $(SCALAR_OUTPUT)/translated
	for count in 1 2 16; do \
		python3 scripts/build_software.py --config $(SOFTWARE_CONFIG) --isa rv64ima --program software/tests/atomic.c --harts $$count --issue-width $$((count < 3 ? count : 3)) --icache-bytes 8192 --dcache-bytes 8192 --stack-bytes 512 --console-base 0x10000000 --output $(SCALAR_OUTPUT)/software/harts$$count || exit $$?; \
		python3 test/verify.py --elf $(SCALAR_OUTPUT)/software/harts$$count/software.elf --config $(SCALAR_OUTPUT)/software/harts$$count/input.json --output $(SCALAR_OUTPUT)/software/harts$$count/verification || exit $$?; \
	done

verify-compressed-isa:
	python3 test/verify.py --compressed --width 64 --pmp-entries 0 $(COMPRESSED_ARGS) --output $(COMPRESSED_OUTPUT)/bare
	python3 test/formal.py --rtl $(COMPRESSED_OUTPUT)/bare/axi64/rtl --output $(COMPRESSED_OUTPUT)/formal --modules CompressedFetch
	python3 test/verify.py --compressed --width 128 --pmp-entries 0 --issue-width 3 --icache-bytes 8192 --branch-prediction --branch-predictor-entries 8 $(COMPRESSED_ARGS) --output $(COMPRESSED_OUTPUT)/cached
	python3 test/formal.py --rtl $(COMPRESSED_OUTPUT)/cached/axi128/rtl --output $(COMPRESSED_OUTPUT)/cache-formal --modules InstructionCache
	python3 test/verify.py --compressed $(SCALAR_CACHE) --burst-refill --sv39 --tlb-entries 4 --i-tlb-entries 4 --d-tlb-entries 2 --width 512 --pmp-entries 16 --issue-width 2 $(foreach kind,page success pma pmp,--case compressed_page_$(kind)) --output $(COMPRESSED_OUTPUT)/translated
	python3 test/formal.py --rtl $(COMPRESSED_OUTPUT)/translated/irq-pmp16-axi512/rtl --output $(COMPRESSED_OUTPUT)/burst-formal --modules InstructionCache
	python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); d=d.get("parameters",d); d["enableC"]=True; json.dump(d,open(sys.argv[2],"w"))' "$(SOFTWARE_CONFIG)" "$(COMPRESSED_OUTPUT)/software.json"
	for count in 1 2 16; do \
		image=$(COMPRESSED_OUTPUT)/software/harts$$count; \
		python3 scripts/build_software.py --config $(COMPRESSED_OUTPUT)/software.json --isa rv64imac --program software/tests/atomic.c --harts $$count --issue-width $$((count < 3 ? count : 3)) --icache-bytes 8192 --dcache-bytes 8192 --stack-bytes 512 --console-base 0x10000000 --output $$image && \
		python3 test/verify.py --elf $$image/software.elf --config $$image/input.json --output $$image/verification --jobs $(SOFTWARE_JOBS) || exit $$?; \
	done
