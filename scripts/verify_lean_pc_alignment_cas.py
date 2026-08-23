#!/usr/bin/env python3
"""CAS-only alignment check: Lean PC coordinate formulas == GAP PC rows.

The parser is deliberately narrow: it accepts only the six explicit
coordinate definitions in G2TwoSylowPCGenerators.lean and interprets `^^`
as addition in GF(2).  It does not enumerate carrier elements or words.
"""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
lean_file = ROOT / "lean/InfoGeometry/Algebra/Zorn/G2LeanCarrierMatrixAlignment.lean"
source = lean_file.read_text()

def lean_rows(index):
    pattern = rf"def pc{index}Matrix :.*?:=\s*\n(.*?)(?=\n\ntheorem|\n\ndef)"
    match = re.search(pattern, source, re.S)
    if match is None:
        raise AssertionError(f"missing pc{index}Fun")
    rows = []
    for line in match.group(1).splitlines():
        supports = re.search(r"!\[([^]]*)\]", line)
        if supports:
            entries = [x.strip() for x in supports.group(1).split(",")]
            rows.append(tuple(i + 1 for i, x in enumerate(entries) if x not in {"0", ""}))
    if len(rows) != 8:
        raise AssertionError(f"pc{index}Matrix has {len(rows)} rows")
    return tuple(rows)

gap = subprocess.run(["gap", "-q", str(ROOT / "scripts/export_carrier_pc_rows.g")],
                     cwd=ROOT, check=True, capture_output=True, text=True)
gap_rows = {}
for line in gap.stdout.splitlines():
    match = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if match:
        gap_rows[int(match.group(1))] = tuple(
            tuple(int(x) for x in row.split(",") if x)
            for row in match.group(2).split(";")
        )

assert set(gap_rows) == set(range(1, 7))
for index in range(1, 7):
    lean = lean_rows(index)
    gap = gap_rows[index]
    assert lean == gap, (
        f"PC alignment mismatch at generator {index}: "
        f"Lean-rows={lean} GAP-rows={gap}"
    )

print("LEAN_PC_FORMULAS_EQUAL_GAP_PC_ROWS=PASS")
print("All six Lean PC generators have exact CAS-derived GAP matrix support")
