# Verification

<!-- SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> -->
<!-- SPDX-License-Identifier: MIT -->

Run commands from the repository root inside `nix develop`.
The shell provides RTL generation, Verilator, Icarus Verilog, formal tools, Python test dependencies and RISC-V GDB.
It does not provide every software or external-debug dependency below.

## Dependencies

| Consumer | Additional requirements |
| --- | --- |
| Freestanding software | RISC-V GCC/binutils; `RISCV_PREFIX` defaults to `riscv64-unknown-elf-` |
| External debug and full signoff | OpenOCD and RISC-V GDB; Makefile variables `OPENOCD` and `RISCV_GDB` select executables |
| Debug probe compilation | `riscv64-unknown-elf-gcc` is also required explicitly; this probe does not use `RISCV_PREFIX` |
| RTOS software | `ZEPHYR_BASE` checkout and its build dependencies, including CMake and Ninja |
| External architectural tests | `ARCH_TEST_DIR` checkout and the Python/tool dependencies used by [the builder](../scripts/build_arch_tests.py) |

The RTOS builder requires revision `dccb09599635bdff17633fa7e9dab014b91dce90` and rejects tracked changes.
See [the RTOS builder](../scripts/build_zephyr.py) for its toolchain and SDK requirements.
The architectural-test builder requires ACT 0.3.0, Sail 0.13.1, pyjson5 and ruamel.yaml, with its pinned clean source checkout.
External software and model runs record their actual versions and inputs; unavailable tools do not count as passing evidence.

## Test selection

| Command | Scope | Output |
| --- | --- | --- |
| `make config` | Generate the default configuration | `result/ditdah_a1_config.json` |
| `make check` | Parameter, region and serialization contracts | Command status and diagnostics |
| `make verify-simulation` | Scalar and multicore RTL simulation | `result/verify`, `result/multicore` |
| `make verify-software` | Freestanding console and integer programs | `result/software` |
| `make verify-supervisor-memory` | Page attributes, maintenance, pointer masking and 1/2/16-hart software | `result/supervisor-memory` |
| `make verify-jtag` | JTAG transport and DMI crossing simulation/formal | `result/jtag-signoff` |
| `make verify-signoff` | Complete hardware campaign, including external debug and platform software | `result/` |
| `make verify-width-software` | Same loaded software across 1–3 issue and 1/2/16 harts | `result/software/widths` |
| `make verify-zephyr-long` | Long RTOS workloads on 1/2/16 harts | `result/software` |

Full campaigns and software matrices are separate from the initial RTL build and can take hours.
Use [Makefile](../Makefile) for component gates, output overrides and prerequisites.
`FORMAL_JOBS` controls independent proof partitions; `SOFTWARE_JOBS` controls software schedules.
These settings do not automatically parallelize one simulated processor.

## Coverage and acceptance

Simulation checks standalone Core and AXI integration with the instruction model, independent memory checks and parameter contracts.
ISA and software checks cover selected integer/FP operations, compressed fetch, counters, interrupts, memory maintenance and translation.
Multicore checks retain per-hart instruction state and memory ordering from actual bus service.
Software acceptance requires target-generated console bytes and per-hart result publication, with interrupt/atomic witnesses where required.

Formal properties check authorization, ownership, cancellation, retirement and error routing under their declared abstractions and assumptions.
Cache control proofs abstract array values; native-array and content tests check storage behavior separately.
Arithmetic simulation and selected RVFI instruction models supplement control proofs.
Unbounded safety, bounded checks, reachability and mutation rejection are distinct results.

Read each runner's summaries, configuration manifests and raw logs together.
A successful build alone does not establish execution or checker acceptance.
Reports apply to their recorded source, configuration, software and executed cases.
Failures, timeouts, SKIP and unavailable tests are separate from successful checks.

These campaigns do not establish complete ISA/Profile compliance or physical signoff.
RTL console/SMP results do not establish Linux startup or FPGA operation.
