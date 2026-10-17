# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT

.PHONY: config check rtl verify-signoff clean

config:
	configure-ditdah-a1 --output result/ditdah_a1_config.json

check:
	configure-ditdah-a1 --check

rtl:
	build-ditdah-a1

verify-signoff: config check
	python3 test/verify.py $(VERIFY_ARGS)
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
	python3 test/check_production.py
	python3 test/formal.py
	python3 test/formal.py --rtl result/production-pmp16 --output result/formal/pmp16
	python3 test/formal.py --rtl result/verify/pmp16-axi64/rtl --output result/formal/pmp16-pa32 --modules Pmp
	python3 test/formal.py --rtl result/production-irq --output result/formal/irq --modules InterruptCsr InterruptBackend
	python3 test/formal.py --rtl result/verify/irq-axi64/rtl --output result/formal/irq-pa32 --modules InterruptCsr InterruptBackend

clean:
	rm -rf result
