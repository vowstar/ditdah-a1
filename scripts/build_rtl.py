# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Generate a validated processor configuration and its RTL."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def source_hashes():
    paths = sorted(Path("ditdah_a1/src").glob("*.scala")) + [
        Path(name) for name in ("flake.nix", "flake.lock", "nix/stable-toolchain.nix", "scripts/build_rtl.py")]
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path)
    parser.add_argument("--output", type=Path, default=Path("result/rtl"))
    trace_options = parser.add_mutually_exclusive_group()
    trace_options.add_argument("--trace", action="store_true", default=None)
    trace_options.add_argument("--no-trace", action="store_false", dest="trace")
    parser.add_argument("--top", choices=["DitDahA1", "DitDahA1Core", "DitDahA1Frontend", "DitDahA1Fetch", "DitDahA1Lsu"], default="DitDahA1")
    args = parser.parse_args()
    hashes = source_hashes()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scratch = Path("/data/tmp")
    scratch = scratch if scratch.is_dir() and os.access(scratch, os.W_OK) else None
    with tempfile.TemporaryDirectory(prefix="ditdah-a1-", dir=scratch) as directory:
        work = Path(directory)
        command = ["configure-ditdah-a1", "--rtl", "--output", str(work / "manifest.json")]
        if args.config:
            command += ["--config", str(args.config.resolve())]
        subprocess.run(command, check=True)
        manifest = json.loads((work / "manifest.json").read_text())
        trace = manifest["parameters"]["enableTrace"] if args.trace is None else args.trace
        manifest["parameters"]["enableTrace"] = trace
        manifest["top"] = args.top
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
