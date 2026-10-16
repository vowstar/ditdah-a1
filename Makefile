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
	build-ditdah-a1 --top DitDahA1Frontend --output result/frontend
	python3 test/check_production.py

clean:
	rm -rf result
