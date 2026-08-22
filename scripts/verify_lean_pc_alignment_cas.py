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
lean_file = ROOT / "lean/InfoGeometry/Algebra/Zorn/G2TwoSylowPCGenerators.lean"
source = lean_file.read_text()

def lean_rows(index):
    pattern = rf"def pc{index}Fun \(X : SplitOctF2\) : SplitOctF2 :=\s*⟨(.*?)⟩"
    match = re.search(pattern, source, re.S)
    if match is None:
        raise AssertionError(f"missing pc{index}Fun")
    fields = [field.strip() for field in match.group(1).split(",")]
    if len(fields) != 8:
        raise AssertionError(f"pc{index}Fun has {len(fields)} coordinates")
    names = ("a", "b", "x0", "x1", "x2", "y0", "y1", "y2")
    rows = []
    for field in fields:
        terms = [term.strip() for term in field.split("^^")]
        parity = {name: terms.count(f"X.{name}") % 2 for name in names}
        if any(term not in {f"X.{name}" for name in names} for term in terms):
            raise AssertionError(f"unsupported GF(2) expression: {field}")
        rows.append(tuple(i + 1 for i, name in enumerate(names) if parity[name]))
    # Lean's `autMatrix` stores the image of basis `j` in column `j`:
    # autMatrix f i j = (f (basis8 j))_i.  The GAP exporter prints row
    # supports, so transpose the parsed coordinate table before comparing.
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
    gap_columns = tuple(
        tuple(row + 1 for row, support in enumerate(gap) if col + 1 in support)
        for col in range(8)
    )
    assert lean == gap_columns, (
        f"PC alignment mismatch at generator {index}: "
        f"Lean-output-rows={lean} GAP-transposed-columns={gap_columns}"
    )

print("LEAN_PC_FORMULAS_EQUAL_GAP_PC_ROWS=PASS")
print("All six Lean PC generators have exact CAS-derived GAP matrix support")
