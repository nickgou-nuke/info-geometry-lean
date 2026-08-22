#!/usr/bin/env python3
"""Check the GAP flag-orbit lists against the frozen Lean `flagCells` table.

The GAP script numbers left cosets from 1, while Lean's `Fin 189` table is
zero-based.  This verifier performs only that explicit normalization and set
comparison; it does not promote GAP output to a Lean theorem.
"""

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean/InfoGeometry/Algebra/Zorn/G2FlagWordCertificate.lean"
GAP = ROOT / "scripts/verify_g2_true_bruhat_cover.g"

out = subprocess.run(
    ["/home/goutev/miniforge3/envs/sage/bin/gap", "-q"],
    input=GAP.read_text(), text=True, capture_output=True, check=True,
).stdout

cas_cells = []
for k in range(12):
    match = re.search(rf"^CORRECTED_FLAG_ORBIT_{k}=\[([^\]]*)\]", out, re.M | re.S)
    if match is None:
        raise SystemExit(f"missing GAP orbit {k}")
    cas_cells.append(sorted(int(x) - 1 for x in re.findall(r"\d+", match.group(1))))

lean_block = LEAN.read_text().split("def flagCells", 1)[1].split("]\n\nend ", 1)[0]
lean_cells = [
    sorted(int(x) for x in re.findall(r"\d+", raw))
    for raw in re.findall(r"\{([^{}]*)\}", lean_block)
]
if len(lean_cells) != 12:
    raise SystemExit(f"expected 12 Lean cells, got {len(lean_cells)}")
if cas_cells != lean_cells:
    raise SystemExit("GAP/Lean flag-cell mismatch")

sizes = [len(cell) for cell in cas_cells]
assert sum(sizes) == 189
print("FLAG_CELLS_CAS_LEAN_ALIGNMENT=PASS")
print(f"FLAG_CELL_SIZES={sizes}")
print("FLAG_CELL_TOTAL=189")
