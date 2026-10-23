# DitDah-A1

DitDah-A1 targets a 64-bit RISC-V application processor with scalar execution.

## Architecture target

| Component | Target |
| --- | --- |
| Scalar ISA | RV64GCB |
| Scalar execution | Fixed eight-stage, configurable one to three issue, in-order |
| Privilege and translation | M/S/U, Sv39 and Sv48 |
| Memory | Private instruction/data caches, optional shared L2 |
| Multiprocessing | One to sixteen harts with hardware cache coherence |
| Integration | Burst-capable AXI4 and JTAG debug |

The executable RTL supports one to sixteen RV64 harts, M or optional M/U and M/S/U modes, shared AXI4 and precise synchronous exceptions.
`issueWidth` selects one to three lanes in a fixed eight-stage pipeline; independent integer ALUs may follow one ordinary load/store, while other resources execute alone.
PMP is configurable to zero or sixteen entries per hart; the default uncached configuration omits it.
MUL uses an iterative resource; accepted operations retain their instruction owner through completion or cancellation draining.
Branches recover in EX while retaining older work; `enableBranchPrediction` enables static backward-branch and direct-jump prediction.
The manifest lists implemented instructions; Sv48, writeback caches and shared L2 remain design targets.
Core composes Frontend and Backend; Frontend owns PC sequencing and Backend owns execution and retirement.
Non-fault Backend packets contain four-byte instructions and word-aligned PCs; producers supply fetch faults.
Core exposes separate instruction/data memory ports; the physical fabric owns shared arbitration and AXI.
Instruction permissions apply before cache lookup and to the complete refill request; region checks also protect external accesses.
The multicore fabric permits two ordinary reads or enabled 64-byte refills from distinct harts; writes, atomics and devices wait for all response fragments and execute exclusively.
An unexpected read ID blocks new fabric transactions until reset while known in-flight reads drain.
AXI data width is configurable to 64/128/256/512 bits; scalar requests remain at most eight bytes.
AMOADD.D, AMOOR.D and AMOSWAP.D use AXI exclusive retry and return the old value.
LR.D/SC.D use per-hart reservations; ordered data completion covers all aq/rl combinations. This does not implement the complete A or Zaamo extension.
FENCE preserves ordered data completion; FENCE.I restarts local instruction fetching and invalidates the optional private instruction cache.

## Development

```bash
nix develop
make config
make check
make rtl
make verify-signoff
```

`make config` writes the uncached configuration to `result/ditdah_a1_config.json`; `make check` validates configuration, memory-region, and serialization contracts.
`configure-ditdah-a1 --config input.json --output result/config.json` validates a supplied configuration.
`build-ditdah-a1 --config input.json --output result/rtl` generates supported RTL configurations.
Use `--top DitDahA1Core`, `DitDahA1Frontend`, `DitDahA1Backend`, or `DitDahA1MemoryFabric` for independent generation.
Component builds validate their own domain; whole-system generation rejects unimplemented features.
The manifest records the selected top and validation scope; unrelated parameters do not enable hardware features.
Add `--trace` to retain the separate DV bind files.
The default physical map is 64 KiB of RAM at zero; configure regions for the intended system.
Set a region's `atomic` flag only for readable, writable, non-device memory with end-to-end exclusive monitoring of every competing writer.
The flag defaults to false; unsupported exclusive reads and bus errors fault without rollback guarantees.
Failed AMO writes retry; SC returns a status without retry.
AMO completion requires eventual bus responses and successful exclusive access; contention can delay all harts on the shared fabric.
Set `iCacheBytes` to zero for bypass or a power of two from 8 to 64 KiB for a blocking, direct-mapped instruction cache with 64-byte lines.
Instruction refills use individually authorized four-byte requests; non-demand refill faults fall back to the original demand.
Set `enableBurstRefill` with an instruction cache for protected 64-byte INCR refills; denial or line errors retry the original scalar demand without installing a line.
Set `dCacheBytes` to 8192 for private read caches on `dataCacheable` non-device regions; zero bypasses them.
Ordinary loads use eight-byte sectors; narrow refills require full-word permission. CPU writes invalidate private copies before forwarding.
`dCacheRefillBytes` defaults to 8; set it to 64 for protected whole-line refills independent of I-cache. Expanded-read errors drain and retry the original demand without installing a partial line.
External writers require platform coordination; no DMA coherence is implemented.
Set `pmpEntries` to 16 to enable protection; successful PMP writes restart younger execution while accepted fetches drain.
Set `enableUserMode` for Bare M/U execution and effective data privilege via MPRV.
Set `enableSupervisorMode` with user mode and interrupts for M/S/U, standard trap delegation and SRET.
Set `virtualAddressBits` to 39 for Sv39/Svade with 4 KiB/2 MiB/1 GiB pages and ASIDLEN=0; zero selects Bare. PTE reads share the data path under S-mode PMP/PMA.
Set `tlbEntries` to 0/2/4 for a shared per-hart TLB with independent I/D hit service and one walker; SFENCE.VMA, satp and PMP maintenance exclude stale refills while accepted reads drain.
Set `enableInterrupts` for precise entry and return from synchronous machine software/timer/external interrupt levels; platform logic owns the sources.
System interrupt inputs are indexed by hart; each hart has independent CSR and PMP state.
An optional `localInterruptBase` maps protected software-interrupt and 64-bit timer registers; `timeTick` supplies the synchronous timebase.
All harts share the reset vector and read their index from `mhartid`; standalone Core and Backend integrations must hold `hartId` constant.

`make verify-signoff` checks standalone Core and AXI integration against the same instruction model,
tests interface and component-configuration contracts, lints the five production tops, and proves execution/transaction safety.
Formal checks cover Fetch cancellation, multiply ownership and zero/unit operands, and Backend ownership with an abstract resource.
Enabled configurations additionally check PMP decisions, CSR locks, and cancellation/ownership with abstract authorization.
Interrupt checks cover CSR eligibility, saved PC, transaction ownership, and independently modeled architectural events.
Multicore checks use per-hart instruction models and shared memory ordered by bus service; arbiter proofs check ownership and bounded overtaking.
Atomic checks include independent interference, failed-write suppression, returned old values, publication ordering, and AXI retry/error safety.
Instruction-cache control proofs abstract memory read values; array geometry, storage behavior and instruction publication are checked separately.
Data-cache checks separate architectural samples from physical service, test native arrays, and prove invalidation and ownership control with abstract array values.
Translation checks cover page permissions, faults, context changes, protected implicit reads, and virtual software on 1/2/16 harts.
Burst checks cover all bus widths, retained ownership through last, beat data, full-line protection, invalidation and paired 1/2/16-hart software.
Platform checks execute shared work, software interrupts and timer interrupts on 1/2/3/16 harts.
ELF checks build freestanding software with `RISCV_PREFIX` (default `riscv64-unknown-elf-`) and validate actual console writes and per-hart results.
`make verify-width-software` checks identical loaded software across 1/2/3 issue for each of 1/2/16 harts; `make verify-zephyr-long SOFTWARE_JOBS=3` uses the pinned `ZEPHYR_BASE` checkout.
Reachability and mutation checks exercise the properties; general multiply results are checked by simulation.
This checks the implemented instruction subset, not full ISA compliance or physical signoff.
Use `make verify-signoff VERIFY_ARGS=--use-generated` to reuse RTL whose recorded sources and configuration still match.

## Credits

- [CHIPS Alliance Rocket](https://github.com/chipsalliance/rocket-chip): processor architecture and configurable hardware design.
- [CHIPS Alliance T1](https://github.com/chipsalliance/t1): hardware generation and verification workflows.
- [DitDah-E1](https://github.com/vowstar/ditdah-e1): project structure and reproducible configuration workflow.
- [Zaozi](https://github.com/xinpian-tech/zaozi): hardware description framework and pinned development tools.
- [RISC-V specifications](https://riscv.org/specifications/ratified/): instruction and privilege contracts.
- [LLVM](https://github.com/llvm/llvm-project) and [CIRCT](https://github.com/llvm/circt): compiler toolchain.
- [YosysHQ](https://github.com/YosysHQ): synthesis and formal verification tools.
- [RISC-V architectural tests](https://github.com/riscv-non-isa/riscv-arch-test) and [Sail](https://github.com/riscv/sail-riscv): executable architectural checks.
- [Zephyr](https://github.com/zephyrproject-rtos/zephyr): multicore software tests.
