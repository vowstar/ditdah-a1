# DitDah-A1

DitDah-A1 targets a 64-bit RISC-V application processor with scalar execution.
A denotes application processing; 1 identifies the architecture generation.
Hart count and cache sizes describe configurations of the same model.

## Architecture target

| Component | Target |
| --- | --- |
| Scalar ISA | RV64GCB |
| Scalar execution | Eight-stage, dual-issue, in-order |
| Privilege and translation | M/S/U, Sv39 and Sv48 |
| Memory | Private instruction/data caches, optional shared L2 |
| Multiprocessing | One to eight harts with hardware cache coherence |
| Integration | Burst-capable AXI4 and JTAG debug |

The executable RTL has one RV64 hart, M mode, an overlapped single-issue pipeline, uncached AXI4,
and precise synchronous exceptions. The generated configuration manifest lists the 13 implemented instructions.
The complete target ISA is not implemented.
Caches, MMU, dual issue, and coherence remain design targets.
Core composes Frontend and Backend; Frontend owns PC sequencing and Backend owns execution and retirement.
Non-fault Backend packets contain four-byte instructions and word-aligned PCs; producers supply fetch faults.
Core exposes separate instruction/data memory ports; the physical fabric owns arbitration, region checks, and AXI.
AXI data width is configurable to 64/128/256/512 bits; scalar requests remain at most eight bytes.

## Development

```bash
nix develop
make config
make check
make rtl
make verify-signoff
```

`make config` writes the uncached execution configuration to `result/ditdah_a1_config.json`.
`make check` validates configuration, memory-region, and serialization contracts.
`nix build` produces a validated configuration package.
`configure-ditdah-a1 --config input.json --output result/config.json` validates a supplied configuration.
`build-ditdah-a1 --config input.json --output result/rtl` generates supported RTL configurations.
Use `--top DitDahA1Core`, `DitDahA1Frontend`, `DitDahA1Backend`, or `DitDahA1MemoryFabric`
for independent generation.
Component builds validate their own domain; whole-system generation rejects unimplemented features.
The manifest records the selected top and validation scope; unrelated parameters do not enable hardware features.
Add `--trace` to retain the separate DV bind files.
The default physical map is 64 KiB of RAM at zero; configure regions for the intended system.

`make verify-signoff` checks standalone Core and AXI integration against the same instruction model,
tests interface and component-configuration contracts, and lints the five production tops.
This checks the implemented instruction subset, not full ISA compliance or physical signoff.

Pipeline depth, issue width, and cache sizes are specifications rather than model-number fields.
Major architecture generations use 1, 2, and 3. Release versions track maintenance separately.
E, R, A, and P identify embedded, real-time, application, and performance-oriented designs.

## Credits

- [CHIPS Alliance Rocket](https://github.com/chipsalliance/rocket-chip): processor architecture and configurable hardware design.
- [CHIPS Alliance T1](https://github.com/chipsalliance/t1): hardware generation and verification workflows.
- [DitDah-E1](https://github.com/vowstar/ditdah-e1): project structure and reproducible configuration workflow.
- [Zaozi](https://github.com/xinpian-tech/zaozi): hardware description framework and pinned development tools.
- [RISC-V specifications](https://riscv.org/specifications/ratified/): instruction and privilege contracts.
- [LLVM](https://github.com/llvm/llvm-project) and [CIRCT](https://github.com/llvm/circt): compiler toolchain.
