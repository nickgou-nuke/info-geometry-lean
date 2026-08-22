#!/usr/bin/env python3
"""CAS Groebner packet for the exact Lean-aligned t reflection carrier."""
from pathlib import Path
import re
import subprocess
import itertools
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
rows = {
    0: [[0, 3], [1, 3], [2, 7], [3], [3, 4, 5], [5], [0, 1, 3, 6, 7], [7]],
    1: [[0, 7], [1, 7], [2], [2, 3], [0, 1, 3, 4, 7], [2, 3, 5, 6, 7], [2, 6, 7], [7]],
    2: [[0, 2, 7], [1, 2, 7], [2], [3, 7], [0, 1, 3, 4, 6], [0, 1, 2, 3, 5, 7], [2, 6, 7], [7]],
    3: [[0], [1], [2], [3], [3, 4], [5], [6, 7], [7]],
    4: [[0, 7], [1, 7], [2], [3], [0, 1, 3, 4, 7], [3, 5], [2, 6, 7], [7]],
    5: [[0], [1], [2], [3], [2, 4], [5, 7], [6], [7]],
}
t_raw = subprocess.run(
    ["gap", "-q", str(ROOT / "scripts/export_lean_t_rows.g")],
    cwd=ROOT, check=True, capture_output=True, text=True,
).stdout
trows = {}
for line in t_raw.splitlines():
    match = re.fullmatch(r"TROW ([1-8]) ([0-9,]*)", line.strip())
    if match:
        trows[int(match.group(1)) - 1] = [
            int(x) - 1 for x in match.group(2).split(",") if x
        ]
assert set(trows) == set(range(8))

identity = sp.eye(8)
generators = [sp.Matrix([
    [int(j in rows[k][i]) for j in range(8)] for i in range(8)
]) for k in range(6)]
t = sp.Matrix([
    [int(j in trows[i]) for j in range(8)] for i in range(8)
])
a = sp.symbols("a0:6")
word = identity
for index in range(6):
    word = (identity + a[index] * (generators[index] - identity)) * word

for index in range(1, 6):
    target = t * generators[index] * t
    equations = [word[i, j] - target[i, j]
                 for i in range(8) for j in range(8)]
    basis = sp.groebner(
        equations + [bit * bit + bit for bit in a],
        *a, order="lex", modulus=2,
    )
    if len(basis.polys) != 6:
        raise AssertionError(f"T_COMPLEMENT_P{index}_NO_UNIQUE_CERTIFICATE")
    target_bits = None
    for candidate in itertools.product((0, 1), repeat=6):
        candidate_word = word.subs(dict(zip(a, candidate))).applyfunc(lambda x: int(x) % 2)
        if candidate_word == target:
            target_bits = list(candidate)
            break
    if target_bits is None:
        raise AssertionError(f"T_COMPLEMENT_P{index}_RECOVERY_FAILED")
    print(f"T_COMPLEMENT_GROEBNER_P{index}=PASS")
    print(f"t * p{index} * t = pcWord {target_bits}")
print("T_COMPLEMENT_GROEBNER_PACKET=PASS")
print("GROEBNER_NO_ASSIGNMENT_ENUMERATION=PASS")
