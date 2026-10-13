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

The configuration generator is implemented. CPU RTL, caches, MMU, and coherence are design targets.

## Development

```bash
nix develop
make config
make check
```

`make config` writes `result/ditdah_a1_config.json`.
`make check` validates address, cache, hart-count, and serialization contracts.
`nix build` produces a validated configuration package.
`configure-ditdah-a1 --config input.json --output result/config.json` validates a supplied configuration.

Pipeline depth, issue width, and cache sizes are specifications rather than model-number fields.
Major architecture generations use 1, 2, and 3. Release versions track maintenance separately.
E, R, A, and P identify embedded, real-time, application, and performance-oriented designs.

## Credits

- [DitDah-E1](https://github.com/vowstar/ditdah-e1): project structure and reproducible configuration workflow.
- [Zaozi](https://github.com/xinpian-tech/zaozi): hardware description framework and pinned development tools.
- [RISC-V specifications](https://riscv.org/specifications/ratified/): instruction and privilege contracts.
- [LLVM](https://github.com/llvm/llvm-project) and [CIRCT](https://github.com/llvm/circt): compiler toolchain.
