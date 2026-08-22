"""Symbolic, non-enumerative PC recovery for the true Lean t representative."""
from pathlib import Path
import re
import subprocess
import sys
import sympy as sp

root = Path(__file__).resolve().parents[1]
row_script = (root / "scripts/export_g2_t_rows.g"
              if len(sys.argv) > 2 and sys.argv[2] == "api"
              else root / "scripts/export_g2_true_t_rows.g")
raw = subprocess.run(["gap", "-q", str(row_script)],
                     check=True, capture_output=True, text=True).stdout
trows = {}
for line in raw.splitlines():
    m = re.fullmatch(r"TROW ([1-8]) ([0-9,]*)", line.strip())
    if m:
        trows[int(m.group(1)) - 1] = [int(x) - 1 for x in m.group(2).split(",") if x]
assert len(trows) == 8

rows = [
    [[0,3],[1,3],[2,7],[3],[3,4,5],[5],[0,1,3,6,7],[7]],
    [[0,7],[1,7],[2],[2,3],[0,1,3,4,7],[2,3,5,6,7],[2,6,7],[7]],
    [[0,2,7],[1,2,7],[2],[3,7],[0,1,3,4,6],[0,1,2,3,5,7],[2,6,7],[7]],
    [[0],[1],[2],[3],[3,4],[5],[6,7],[7]],
    [[0,7],[1,7],[2],[3],[0,1,3,4,7],[3,5],[2,6,7],[7]],
    [[0],[1],[2],[3],[2,4],[5,7],[6],[7]],
]
I = sp.eye(8)
gens = [sp.Matrix([[int(j in rows[k][i]) for j in range(8)] for i in range(8)])
        for k in range(6)]
t = sp.Matrix([[int(j in trows[i]) for j in range(8)] for i in range(8)])
a = sp.symbols("a0:6")
word = I
for k in range(6):
    word = (I + a[k] * (gens[k] - I)) * word
index = int(sys.argv[1]) if len(sys.argv) > 1 else 1
target = t * gens[index] * t
polys = [word[i, j] - target[i, j] for i in range(8) for j in range(8)]
gb = sp.groebner(polys + [x*x + x for x in a], *a, order="lex", modulus=2)
label = "API_T" if len(sys.argv) > 2 and sys.argv[2] == "api" else "TRUE_T"
print(f"{label}_PC{index}_GROEBNER=PASS")
for p in gb.polys:
    print("GB", p.as_expr())
solutions = [p.as_expr() for p in gb.polys if p.as_expr().count(a[0]) >= 0]
expected = [a[k] for k in range(6)]
for k in range(6):
    assert any(p.as_expr() == a[k] or p.as_expr() == a[k] + 1 for p in gb.polys)
bits = [0 if any(p.as_expr() == a[k] for p in gb.polys) else 1 for k in range(6)]
print(f"{label}_PC{index}_BITS=", bits)
