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
	python3 test/verify.py
	build-ditdah-a1 --output result/production
	build-ditdah-a1 --top DitDahA1Core --output result/core
	build-ditdah-a1 --top DitDahA1Frontend --config result/frontend-input.json --output result/frontend
	build-ditdah-a1 --top DitDahA1MemoryFabric --config result/fabric-input.json --output result/fabric
	build-ditdah-a1 --top DitDahA1Backend --config result/backend-input.json --output result/backend
	python3 test/check_production.py

clean:
	rm -rf result
