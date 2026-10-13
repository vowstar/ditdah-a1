# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT

.PHONY: config check clean

config:
	configure-ditdah-a1 --output result/ditdah_a1_config.json

check:
	configure-ditdah-a1 --check

clean:
	rm -rf result
