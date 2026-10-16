# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
"""Check self-contained production artifacts and their external interfaces."""

from pathlib import Path
import subprocess

for directory, top in (("production", "DitDahA1"), ("core", "DitDahA1Core"),
                       ("frontend", "DitDahA1Frontend")):
    rtl = Path("result") / directory
    files = (rtl / "filelist.f").read_text().splitlines()
    assert files and all("DV" not in name and not name.startswith("ref_") for name in files)
    assert not list(rtl.glob("*DV*.sv")) and not list(rtl.glob("ref_*.sv"))
    header = (rtl / (top + ".sv")).read_text().split(");", 1)[0]
    assert "trace" not in header.lower()
    if top != "DitDahA1":
        assert "axi_" not in header
    subprocess.run(["verilator", "--lint-only", "--top-module", top,
                    *[str(rtl / name) for name in files]], check=True)
    print(f"{top} production interface and lint passed")
