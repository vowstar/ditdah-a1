# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Check that the production artifact is self-contained and has no DV layer."""

from pathlib import Path
import subprocess

rtl = Path("result/production")
files = (rtl / "filelist.f").read_text().splitlines()
assert files and all("DV" not in name and not name.startswith("ref_") for name in files)
assert not list(rtl.glob("*DV*.sv")) and not list(rtl.glob("ref_*.sv"))
header = (rtl / "DitDahA1.sv").read_text().split(");", 1)[0]
assert "trace" not in header.lower()
subprocess.run(["verilator", "--lint-only", "--top-module", "DitDahA1",
                *[str(rtl / name) for name in files]], check=True)
print("Production RTL interface and lint passed")
