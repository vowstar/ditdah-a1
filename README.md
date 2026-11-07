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
Optional M uses shared iterative multiplication and division with retained instruction ownership through completion or cancellation draining. Multiplication takes 64 iterations, or 32 for MULW.
Branches recover in EX while retaining older work; `enableBranchPrediction` enables static backward-branch and direct-jump prediction.
`branchPredictorEntries` selects 0/8/16 direct-mapped entries with two-bit direction counters and last indirect targets; nonzero requires prediction enabled. This does not implement a return stack.
The manifest lists I/Zicsr/Zifencei, Zihintpause/Zihintntl/Zkt and optional M/A/C, F/D, Zba/Zbb/Zbs, Zicond/Zimop/Zcb/Zcmop, Zfa/Zfhmin and counter/timer extensions. `floatingPointBits` selects 0/32/64. FPRs and FCSR/FS update at retirement. Sv48 remains a target.
Core composes Frontend and Backend; Frontend owns PC sequencing and Backend owns execution and retirement. `enableC` adds serial halfword fetch and two/four-byte packets with halfword-aligned PCs; raw encodings survive retirement and each parcel receives its own translation and permission check.
Core exposes separate instruction/data memory ports; the physical fabric owns shared arbitration and AXI.
Instruction permissions apply before cache lookup and to the complete refill request; region checks also protect external accesses.
`loadQueueEntries` selects one or two ordinary data-read contexts per hart; replies retain their instruction owner and complete in order.
The fabric permits one instruction read and the configured data-read count per hart through 1–4 `fabricReadSlots` (at most `hartCount * (1 + loadQueueEntries)`; default two for multiple harts, zero for the single-hart bridge); writes, atomics and devices wait for all response fragments and execute exclusively.
Queued AXI read IDs identify transaction slots; serialized accesses retain hart IDs. An unexpected read ID blocks new fabric transactions until reset while known in-flight reads drain.
AXI data width is configurable to 64/128/256/512 bits; scalar requests remain at most eight bytes.
The nine standard W/D AMOs use AXI exclusive retry and return the old value.
W/D LR/SC pair the full physical address and width per hart; ordered data completion covers all aq/rl combinations.
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
Use `--top DitDahA1Core`, `DitDahA1Frontend`, `DitDahA1Backend`, or `DitDahA1MemoryFabric` for independent generation; `--trace` retains the separate DV bind files.
Component builds validate their domain; system builds reject unimplemented features, and the manifest records the selected top and scope.
The default physical map is 64 KiB of RAM at zero; configure regions for the intended system.
`python3 scripts/build_platform.py --clock-hz "$CLOCK_HZ" --jtag-idcode "$JTAG_IDCODE" --output result/platform` generates a boot-ROM, RAM and UART-TX platform from `software/platform.json`.
Set a region's `atomic` flag only for readable, writable, non-device memory with end-to-end exclusive monitoring of every competing writer.
The flag defaults to false; unsupported exclusive reads and bus errors fault without rollback guarantees.
Failed AMO writes retry; SC returns a status without retry. AMO completion requires eventual bus responses and successful exclusive access; contention can delay all harts on the shared fabric.
Set `iCacheBytes` to zero for bypass or a power of two from 8 to 64 KiB for a blocking, direct-mapped instruction cache with 64-byte lines.
Instruction refills use individually authorized four-byte requests; non-demand refill faults fall back to the original demand.
Set `enableBurstRefill` with an instruction cache for protected 64-byte INCR refills; denial or line errors retry the original scalar demand without installing a line.
Set `dCacheBytes` to 8192/16384/32768/65536 total data bytes per hart on `dataCacheable` non-device regions; zero bypasses them. `dCacheWays` selects one or two ways; two ways use one LRU bit per set.
Ordinary loads use eight-byte sectors; narrow refills require full-word permission. Write-through stores update existing bytes after successful completion; store misses do not allocate.
`dCacheRefillBytes` defaults to 8; set it to 64 for protected whole-line refills independent of I-cache. Expanded-read errors drain and retry the original demand without installing a partial line.
Set `dCacheWriteback` for dirty-byte tracking, ownership probes and masked writeback; errors retain dirty data and retry. Ordinary writes invalidate peer copies, and atomic operations invalidate all copies.
Writeback cacheable service is serialized and uses privileged maintenance writes for previously authorized dirty bytes; new demands retain their protection checks. External writers require platform coordination; no DMA coherence is implemented.
Set `l2CacheBytes` to zero for bypass or 131072 for a shared, direct-mapped 128 KiB cache with 64-byte lines and one read transaction at a time.
The shared cache is non-inclusive and write-through without write allocation; private caches retain dirty ownership. Writes invalidate shared copies, while exclusive and device accesses bypass it; cache hits retain upstream protection checks.
Set `pmpEntries` to 16 to enable protection; successful PMP writes restart younger execution while accepted fetches drain.
Set `enableUserMode` for Bare M/U execution and effective data privilege via MPRV.
Set `enableSupervisorMode` with user mode and interrupts for M/S/U, standard trap delegation and SRET.
Set `virtualAddressBits` to 39 for Sv39/Svade with 4 KiB/2 MiB/1 GiB pages; zero selects Bare. `asidBits` selects zero or four implemented ASID bits. PTE reads share the data path under S-mode PMP/PMA.
`iTlbEntries`, `dTlbEntries` and shared `tlbEntries` independently select 0/2/4 entries per hart with one walker. Local entries clear on satp writes; ASID-tagged shared entries survive context changes. With local banks or ASIDs, SFENCE.VMA selects VA/ASID ranges and handles global mappings; PMP maintenance clears all layers, and maintenance excludes stale refills while accepted reads drain.
`enableCounters` adds 64-bit cycle/time/instret, counter access/inhibit controls and Zicntr/Zihpm; supervisor mode also adds Sscounterenw. `hpmCounters` selects 0–29 actual HPM counters; nonzero enables Sscofpmf, privilege filters and IRQ13. Events 0/1/2 select none/cycles/successful retirements. `enableSstc` adds stimecmp and STCE.
`enableInterrupts` enables per-hart interrupt levels. An optional `localInterruptBase` maps protected software-interrupt and 64-bit timer registers; `timeTick` supplies the synchronous timebase. Enabled counters share that time or a coherent external `timeValue`; enabled standalone Core/Backend counters require `timeValue`.
`enableJtag` adds precise per-hart external debugging; system builds require `jtagIdcode` and a dedicated `debugBase`.
All harts share the reset vector and read their index from `mhartid`; standalone Core and Backend integrations must hold `hartId` constant.

`make verify-signoff` checks standalone Core and AXI integration against the same instruction model, tests interface and component-configuration contracts, lints the five production tops, and proves execution/transaction safety.
Formal checks cover Fetch cancellation, arithmetic ownership and Backend ownership with an abstract resource. Paired execution-control proofs and selected RVFI instruction models supplement numeric simulation.
Enabled configurations additionally check PMP decisions, CSR locks, and cancellation/ownership with abstract authorization.
Interrupt checks cover eligibility, saved PC and ownership; counter checks cover retirement-time CSR updates, 64-bit counting, access, overflow and S timers with 1/2/16-hart console software.
Multicore checks use per-hart instruction models and shared memory ordered by bus service; arbiter proofs check ownership and bounded overtaking.
Atomic checks include independent interference, failed-write suppression, returned old values, publication ordering, and AXI retry/error safety.
Instruction-cache control proofs abstract memory read values; array geometry, storage behavior and instruction publication are checked separately.
Data-cache checks separate architectural samples from physical service, test native arrays, and prove invalidation and ownership control with abstract array values.
Translation checks cover page permissions, faults, context changes, protected implicit reads, and virtual software on 1/2/16 harts.
Burst checks cover all bus widths, retained ownership through last, beat data, full-line protection, invalidation and paired 1/2/16-hart software.
Platform checks execute shared work, software interrupts and timer interrupts on 1/2/3/16 harts.
ELF checks build freestanding software with `RISCV_PREFIX` (default `riscv64-unknown-elf-`) and validate actual console writes and per-hart results.
`make verify-width-software` checks identical loaded software across 1/2/3 issue for each of 1/2/16 harts; `make verify-zephyr-long SOFTWARE_JOBS=3` uses the pinned `ZEPHYR_BASE` checkout.
Reachability and mutation checks exercise properties; simulation checks general multiplication. These checks do not establish full ISA compliance or physical signoff.
`make verify-memory-concurrency`, `make verify-prediction` and `make verify-cache-configuration` cover overlapped reads, prediction and cache geometry/coherence. `FORMAL_JOBS` controls independent proof partitions.

## Credits

- [CHIPS Alliance Rocket](https://github.com/chipsalliance/rocket-chip): processor architecture and configurable hardware design.
- [CHIPS Alliance T1](https://github.com/chipsalliance/t1): hardware generation and verification workflows.
- [DitDah-E1](https://github.com/vowstar/ditdah-e1): project structure and reproducible configuration workflow.
- [Zaozi](https://github.com/xinpian-tech/zaozi): hardware description framework and pinned development tools.
- [RISC-V specifications](https://riscv.org/specifications/ratified/): instruction and privilege contracts.
- [LLVM](https://github.com/llvm/llvm-project), [CIRCT](https://github.com/llvm/circt) and [YosysHQ](https://github.com/YosysHQ): compiler and verification tools.
- [Berkeley HardFloat](https://www.jhauser.us/arithmetic/HardFloat.html): IEEE 754 arithmetic.
- [RISC-V architectural tests](https://github.com/riscv-non-isa/riscv-arch-test), [Sail](https://github.com/riscv/sail-riscv) and [RVFI instruction models](https://github.com/YosysHQ/riscv-formal): executable architectural checks.
- [Zephyr](https://github.com/zephyrproject-rtos/zephyr): multicore software tests.
