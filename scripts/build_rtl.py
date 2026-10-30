# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Generate a validated processor configuration and its RTL."""

import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import tempfile


def source_hashes():
    paths = sorted(Path("ditdah_a1/src").glob("*.scala")) + sorted(p for p in Path("rtl").rglob("*") if p.is_file()) + [
        Path(name) for name in ("flake.nix", "flake.lock", "nix/stable-toolchain.nix", "scripts/build_rtl.py")]
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path)
    parser.add_argument("--output", type=Path, default=Path("result/rtl"))
    trace_options = parser.add_mutually_exclusive_group()
    trace_options.add_argument("--trace", action="store_true", default=None)
    trace_options.add_argument("--no-trace", action="store_false", dest="trace")
    parser.add_argument("--top", choices=["DitDahA1", "DitDahA1Core", "DitDahA1Backend", "DitDahA1Gpr", "DitDahA1Frontend", "DitDahA1MemoryFabric", "DitDahA1ReadQueue", "DitDahA1Fetch", "DitDahA1Lsu", "DitDahA1Translation", "DitDahA1LocalInterrupts", "DitDahA1DataCache", "DitDahA1Coherence", "DitDahA1SharedCache"], default="DitDahA1")
    args = parser.parse_args()
    hashes = source_hashes()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scratch = Path("/data/tmp")
    scratch = scratch if scratch.is_dir() and os.access(scratch, os.W_OK) else None
    with tempfile.TemporaryDirectory(prefix="ditdah-a1-", dir=scratch) as directory:
        work = Path(directory)
        scope = {"DitDahA1Core": "core", "DitDahA1Backend": "backend", "DitDahA1Gpr": "gpr", "DitDahA1Frontend": "frontend", "DitDahA1MemoryFabric": "fabric", "DitDahA1ReadQueue": "fabric", "DitDahA1LocalInterrupts": "localInterrupts", "DitDahA1DataCache": "dataCache", "DitDahA1Coherence": "coherence", "DitDahA1SharedCache": "sharedCache"}.get(args.top, "system")
        command = ["configure-ditdah-a1", "--output", str(work / "manifest.json")]
        if scope == "system":
            command += ["--rtl"]
        if args.config:
            command += ["--config", str(args.config.resolve())]
        subprocess.run(command, check=True)
        manifest = json.loads((work / "manifest.json").read_text())
        trace = manifest["parameters"]["enableTrace"] if args.trace is None else args.trace
        manifest["parameters"]["enableTrace"] = trace
        manifest["top"] = args.top
        manifest["validationScope"] = scope
        manifest["implementation"]["hartCount"] = manifest["parameters"]["hartCount"] if args.top == "DitDahA1" else int(args.top == "DitDahA1Core")
        manifest["implementation"]["fabricRequesters"] = 2 * manifest["parameters"]["hartCount"] if args.top in ("DitDahA1", "DitDahA1MemoryFabric", "DitDahA1ReadQueue") else 0
        if args.top not in ("DitDahA1", "DitDahA1MemoryFabric", "DitDahA1ReadQueue"):
            manifest["implementation"]["fabricReadSlots"] = 0
        manifest["implementation"]["enableBranchPrediction"] = bool(manifest["parameters"]["enableBranchPrediction"] and args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Frontend"))
        manifest["implementation"]["branchPredictorEntries"] = manifest["parameters"]["branchPredictorEntries"] if args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Frontend") else 0
        manifest["implementation"]["pmpEntries"] = 0 if scope in ("fabric", "localInterrupts", "gpr", "sharedCache") else manifest["parameters"]["pmpEntries"]
        manifest["implementation"]["pmpState"] = bool(manifest["implementation"]["pmpEntries"] and args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Backend"))
        manifest["implementation"]["machineInterrupts"] = bool(manifest["parameters"]["enableInterrupts"] and args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Backend"))
        manifest["implementation"]["localInterrupts"] = bool(manifest["parameters"]["localInterruptBase"] and args.top in ("DitDahA1", "DitDahA1MemoryFabric", "DitDahA1LocalInterrupts"))
        manifest["implementation"]["iCacheBytes"] = manifest["parameters"]["iCacheBytes"] if args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Frontend", "DitDahA1Fetch") else 0
        manifest["implementation"]["tlbEntries"] = manifest["parameters"]["tlbEntries"] if args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Translation") else 0
        for key in ("iTlbEntries", "dTlbEntries"):
            manifest["implementation"][key] = manifest["parameters"][key] if args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Translation") else 0
        manifest["implementation"]["asidBits"] = manifest["parameters"]["asidBits"] if args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Backend", "DitDahA1Csr", "DitDahA1Translation") else 0
        manifest["implementation"]["enableBurstRefill"] = bool(manifest["parameters"]["enableBurstRefill"] and args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Frontend", "DitDahA1Fetch", "DitDahA1InstructionCache", "DitDahA1MemoryFabric", "DitDahA1Memory", "DitDahA1Axi"))
        manifest["implementation"]["dCacheBytes"] = manifest["parameters"]["dCacheBytes"] if args.top in ("DitDahA1", "DitDahA1DataCache") else 0
        manifest["implementation"]["dCacheWays"] = manifest["parameters"]["dCacheWays"] if manifest["implementation"]["dCacheBytes"] else 0
        manifest["implementation"]["l2CacheBytes"] = manifest["parameters"]["l2CacheBytes"] if args.top in ("DitDahA1", "DitDahA1SharedCache") else 0
        manifest["implementation"]["dCacheRefillBytes"] = manifest["parameters"]["dCacheRefillBytes"] if manifest["implementation"]["dCacheBytes"] else 0
        manifest["implementation"]["dataCoherence"] = args.top == "DitDahA1Coherence" or bool(manifest["parameters"]["dCacheBytes"] and args.top in ("DitDahA1", "DitDahA1MemoryFabric"))
        has_gpr = args.top in ("DitDahA1", "DitDahA1Core", "DitDahA1Backend", "DitDahA1Gpr")
        manifest["implementation"]["gprReadPorts"] = 2 * manifest["parameters"]["issueWidth"] if has_gpr else 0
        manifest["implementation"]["gprWritePorts"] = manifest["parameters"]["issueWidth"] if has_gpr else 0
        manifest["sourceHashes"] = hashes
        parameter = work / "parameter.json"
        parameter.write_text(json.dumps(manifest["parameters"]))
        env = dict(os.environ, DITDAH_A1_SOURCE=str(Path("ditdah_a1/src").resolve()),
                   DITDAH_A1_GENERATOR="DitDahA1Module" if args.top == "DitDahA1" else args.top)
        subprocess.run(["elaborate-ditdah-a1", "design", str(parameter)], cwd=work, env=env, check=True)
        subprocess.run(["firld", *map(str, sorted(work.glob("*.mlirbc"))), "--base-circuit", args.top,
                        "--no-mangle", "--emit-bytecode", "-o", str(work / "linked.mlirbc")], check=True)
        subprocess.run(["firtool", str(work / "linked.mlirbc"), "--split-verilog",
                        "-disable-all-randomization", "--lowering-options=noAlwaysComb,disallowLocalVariables,locationInfoStyle=none",
                        "-o", str(work / "rtl")], check=True)
        if source_hashes() != hashes:
            raise RuntimeError("Sources changed during RTL generation")
        manifest["firtoolVersion"] = subprocess.check_output(["firtool", "--version"], text=True).strip()
        generated = work / "rtl"
        if not trace:
            for path in generated.iterdir():
                if "DV" in path.name or path.name.startswith("ref_"):
                    path.unlink()
        if manifest["parameters"]["floatingPointBits"] and (generated / "DitDahA1Backend.sv").exists():
            library = Path("rtl/ieee754")
            def inline(path):
                def header(match):
                    include = next((folder / match[1] for folder in (library / "RISCV", library) if (folder / match[1]).is_file()), None)
                    assert include is not None, "Missing arithmetic header"
                    return inline(include)
                return re.sub(r'`include "([^"]+)"', header, path.read_text())
            (generated / "DitDahA1Fpu.sv").write_bytes(Path("rtl/DitDahA1Fpu.sv").read_bytes())
            (generated / "DitDahA1FloatLibrary.sv").write_text("\n".join(inline(path) for path in sorted(library.rglob("*.v"))))
        files = sorted(path.name for path in generated.glob("*.sv"))
        # Remove only files owned by the previous generated manifest.
        previous = output / "filelist.f"
        if previous.exists():
            for name in previous.read_text().splitlines():
                if Path(name).name == name and name.endswith(".sv"):
                    (output / name).unlink(missing_ok=True)
        if not trace:
            for path in output.glob("ref_*.sv"):
                path.unlink()
        for path in generated.iterdir():
            if path.is_file() and path.name != "filelist.f":
                (output / path.name).write_bytes(path.read_bytes())
        previous.write_text("\n".join(files) + "\n")
        (output / "ditdah_a1_config.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(output)


if __name__ == "__main__":
    main()
