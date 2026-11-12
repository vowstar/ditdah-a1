# Configuration and integration

<!-- SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com> -->
<!-- SPDX-License-Identifier: MIT -->

## Configuration inputs

Generate a complete configuration with `make config`, then edit its `parameters` object.
The `implementation` and `target` sections are regenerated from those parameters.
Partial JSON inputs inherit constructor defaults, which differ from the generated uncached configuration.
Some constructor defaults describe targets rejected by current RTL.
`configure-ditdah-a1 --rtl` checks system RTL constraints; `build-ditdah-a1` validates the selected component's domain.
See [the parameter definitions](../ditdah_a1/src/DitDahA1Parameter.scala) for complete constraints.

Generate an independent component with:

```bash
build-ditdah-a1 --top DitDahA1Core --config result/checked.json --output result/core
```

Other production components include `DitDahA1Frontend`, `DitDahA1Backend` and `DitDahA1MemoryFabric`.
Add `--trace` to retain separate DV bind files; `--no-trace` omits them.

| Parameter | Supported RTL values |
| --- | --- |
| `hartCount`, `issueWidth` | 1–16 harts, 1–3 issue lanes |
| `physicalAddressBits`, `axiDataBits` | 32–56 address bits; 64/128/256/512 data bits |
| `pmpEntries`, `virtualAddressBits` | 0/16 PMP entries; 0 for Bare or 39 for Sv39 |
| `iCacheBytes`, `dCacheBytes` | 0 or 8192/16384/32768/65536 bytes per hart |
| `dCacheWays`, `dCacheRefillBytes` | 1/2 ways; 8/64-byte refills |
| `l2CacheBytes` | 0 or 131072 bytes |
| `loadQueueEntries`, `fabricReadSlots` | 1/2 data-read contexts; 0–4 fabric read slots, subject to client count |
| `tlbEntries`, `iTlbEntries`, `dTlbEntries`, `asidBits` | 0/2/4 entries per bank; 0/4 ASID bits |
| `branchPredictorEntries` | 0/8/16; nonzero requires `enableBranchPrediction` |
| `floatingPointBits`, `hpmCounters` | 0/32/64 FP bits; 0–29 implemented HPM counters |
| `enableSvnapot`, `enableSvpbmt` | Optional 64 KiB mappings and page memory types; both require Sv39 |
| `enableSvinval`, `enableSsnpm` | Optional supervisor invalidation and host U-mode pointer masking; both require supervisor mode |

The generated default has one M-mode hart, M/A enabled, Bare addressing and AXI128.
Caches, PMP, interrupts, prediction and JTAG are disabled; RAM is 64 KiB at zero with `atomic=false`.
`enableSupervisorMode` requires user mode and interrupts. Sv39 requires supervisor mode.
Translation banks require Sv39; multiple harts require at least one fabric read slot.
Fabric slots cannot exceed `hartCount * (1 + loadQueueEntries)`; automatic selection uses zero for one hart and two otherwise.

## ISA and execution

The manifest records the selected extensions and instructions; it is not a full-ISA compliance certificate.
M/A, C, F/D, Zba/Zbb/Zbs, Zicond/Zimop/Zcb/Zcmop, Zfa/Zfhmin, Zawrs/Zicbom/Zicboz and counters/timers are configurable.
Zihintpause, Zihintntl, Zicbop and Zkt appear in every core manifest.
Zcb/Zcmop require C; Zfa/Zfhmin require F; Zawrs requires A.
Zfhmin supplies half-precision transfers and conversions, not general FP16 arithmetic.
Shared iterative multiplication takes 64 iterations, or 32 for MULW; long operations retain ownership through completion or cancellation draining.
Floating-point registers, FCSR and FS update at retirement.
Branches recover in EX. Prediction provides static backward/direct-jump prediction and optional two-bit direction/indirect-target entries, without a return stack.
Compressed instructions retain raw encodings. Word-aligned 32-bit instructions use one authorized word snapshot; other 32-bit instructions use separately checked halfword parcels.

## Memory, protection and ordering

Regions define readable, writable, executable, device, atomic and data-cacheable properties.
Normal internal-memory and device accesses retain applicable privilege, translation and protection checks.
Demand instruction permissions apply before cache lookup. Each refill request also requires authorization.
Set `atomic=true` only for readable, writable, non-device memory with exclusive monitoring of every competing writer.
The nine W/D AMOs use AXI exclusive retries and return the old value; SC returns success/failure without retrying.
LR/SC reservations match the physical address and width per hart. Ordered data completion covers all aq/rl combinations.
AMO progress requires eventual bus responses and successful exclusive access; contention can delay all harts.
Bus errors fault; earlier externally visible writes have no rollback guarantee.
FENCE preserves ordered data completion; FENCE.I restarts local instruction fetching and invalidates the private instruction cache.

Ordinary reads retain their instruction owner and complete in order.
Queued AXI read IDs identify transaction slots; serialized accesses retain hart IDs.
Writes, atomics and devices execute exclusively after outstanding response fragments drain.
Unexpected read IDs block new fabric transactions until reset while known reads drain.
Scalar requests remain at most eight bytes across all AXI widths.

`enableMisaligned` defaults to false and splits ordinary integer/FP accesses into separately authorized fragments.
Devices and atomics remain aligned. Fault addresses identify the failing fragment; already completed store bytes can remain visible.
`enableZawrs` defaults to false and uses bounded waits with committed-byte reservation invalidation.
`enableZicbom` flushes 64-byte blocks; `enableZicboz` clears blocks through eight ordinary writes. Both default to false.
Cache management assumes uniform block attributes and that write permission implies read permission; behavior outside those preconditions is UNSPECIFIED.
Cache-management enable checks use execution privilege; memory authorization uses effective data privilege, read-or-write permission and PTE A without requiring D.
`cbo.zero` uses ordinary store authorization, including PTE W/A/D in paged mode.
Cache-management memory faults are store-class faults at the original effective address. Block zeroing is not atomic.

## Caches and translation

The instruction cache is blocking and direct-mapped, with 64-byte lines.
Default refills use authorized four-byte requests. `enableBurstRefill` selects protected 64-byte INCR refills.
Expanded-refill denial or errors fall back to the original demand; accepted error beats drain without installing a partial line.
Data caches use eight-byte sectors and optional 64-byte refills; narrow refills require whole-word permission.
Two-way data caches use one LRU bit per set. Write-through stores update hits after completion and do not allocate misses.
`dCacheWriteback` adds dirty-byte ownership, probes and masked writeback; errors retain dirty data and retry.
Ordinary writes invalidate peer copies; atomic service invalidates target-line copies.
Writeback cacheable service is serialized; maintenance completes previously authorized dirty bytes while new demands retain protection checks.
External writers require platform coordination; DMA coherence and persistence across global cold reset are not provided.
The shared cache is direct-mapped, non-inclusive and write-through without write allocation, with one active read.
Private caches retain dirty ownership. Writes invalidate shared copies; exclusive and device traffic bypass shared storage.

Sv39/Svade supports 4 KiB/2 MiB/1 GiB pages and one walker per hart, with S-mode PMP/PMA checks on PTE reads.
Local I/D translation entries clear on satp writes; ASID-tagged shared entries can survive context changes.
Where configured, selective SFENCE.VMA handles VA/ASID/global mappings; other configurations invalidate more entries.
Maintenance excludes stale refills while accepted requests drain.
Sv39/A retains one atomic translation when the private data TLB is absent; it also participates in maintenance.
Svnapot, Svpbmt, Svinval and Ssnpm default to false. Svpbmt uses `menvcfg.PBMTE` and preserves leaf attributes through memory service.
NC/IO accesses bypass cache allocation and use exact demands; IO also requires architectural authorization before issuing.
PMP and static access permissions remain independent of page memory types.
Cacheable/noncacheable aliases require `fence iorw,iorw; cbo.flush; fence iorw,iorw` when switching attributes.
SINVAL.VMA uses the existing maintenance service; both invalidation-ordering instructions serialize execution.
Host `senvcfg.PMM` supports encodings 00/10 for PMLEN 0/7; unsupported encodings select zero.
Masking covers effective U-mode explicit data accesses, including MPRV, and is disabled by MXR in Bare and Sv39.
Instruction fetch, page-table reads and translation-maintenance operands retain their original addresses. Hypervisor controls are not implemented.
Successful PMP writes restart younger execution and clear translation layers while accepted fetches drain.

## Time and interrupts

`enableInterrupts` exposes per-hart software, timer and external interrupt levels.
`localInterruptBase` maps protected software/timer registers; `timeTick` supplies their synchronous timebase.
`enableCounters` adds cycle/time/instret and counter controls; supervisor mode adds Sscounterenw.
HPM events 0/1/2 select none/cycles/successful retirements; nonzero `hpmCounters` requires counters and interrupts and adds Sscofpmf/IRQ13.
`enableSstc` requires counters, supervisor mode and interrupts and adds stimecmp/STCE.
Without local timer registers, enabled system counters require coherent external `timeValue`; enabled standalone Core/Backend counters always require it.
All system harts share the reset vector and receive their index through `mhartid`; standalone integrations must hold `hartId` constant.

## Debug and platform

System `enableJtag` adds TAP/DTM, DMI clock crossing and an execution-based Debug 1.0 subset shared across harts.
It requires an explicit odd unsigned 32-bit `jtagIdcode` and a dedicated aligned, non-overlapping `debugBase` page.
The uncached debug window is reachable only in Debug Mode; ordinary memory retains protection and coherence.
The module supports halt/resume, single-step, abstract register commands and an eight-word Program Buffer.
Authentication, triggers, system bus access, hart groups and independent hart reset are not implemented.
With `enableJtag`, Core and Backend builds expose `DebugHartPort`; they do not instantiate a complete JTAG transport.
`reset` resets debug and processor state. `systemReset` and `ndmreset` reset processor/fabric state while preserving the debug transport/module.
Reset attached AXI peers with `systemResetActive`, the same non-debug reset domain.

[The platform builder](../scripts/build_platform.py) uses [software/platform.json](../software/platform.json) for boot storage, RAM and UART TX.
Supply `--clock-hz` and an explicit `--jtag-idcode`; the default timebase is 1 MHz and baud rate is 115200.
Clock frequency must be divisible by the timebase, and rounded serial timing must satisfy the builder's baud-error check.
The default platform has 512 KiB RAM at `0x80000000`; its UART TX is not a general-purpose serial controller.

Set `JTAG_IDCODE` to the integration's explicit IDCODE before running:

```bash
: "${JTAG_IDCODE:?Set the integration IDCODE}"
python3 scripts/build_platform.py --clock-hz 10000000 --jtag-idcode "$JTAG_IDCODE" --output result/platform
```

`result/platform` contains the processor/platform RTL, `filelist.f`, processor configuration and platform `manifest.json`.
