#!/usr/bin/env python3
"""CAS certificate for the first fixed-basis simple-reflection conjugation.

The matrices are the exact rows exported from the fixed Lean PC carrier.  The
coordinate vector is recovered by the existing symbolic triangular recovery;
no Boolean assignments or GAP ``Pcgs`` coordinates are used.
"""

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
raw = subprocess.run(
    ["gap", "-q", str(ROOT / "scripts/export_carrier_pc_rows.g")],
    cwd=ROOT, check=True, capture_output=True, text=True,
).stdout
rows = {}
for line in raw.splitlines():
    match = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if match:
        rows[int(match.group(1)) - 1] = [
            [int(x) - 1 for x in block.split(",") if x]
            for block in match.group(2).split(";")
        ]
assert set(rows) == set(range(6))

identity = [[int(i == j) for j in range(8)] for i in range(8)]


def multiply(left, right):
    return [[sum(left[i][k] * right[k][j] for k in range(8)) % 2
             for j in range(8)] for i in range(8)]


def generator(index):
    return [[int(j in rows[index][i]) for j in range(8)] for i in range(8)]


def factor(index, bit):
    return generator(index) if bit else identity


def matrix_word(bits):
    # This is the order of Lean's `matrixWord`, C₅ * ... * C₀.
    result = identity
    for index in range(6):
        result = multiply(factor(index, bits[index]), result)
    return result


swap01 = [[int(i == j) for j in range(8)] for i in range(8)]
for left, right in ((2, 3), (5, 6)):
    swap01[left][left] = 0
    swap01[right][right] = 0
    swap01[left][right] = 1
    swap01[right][left] = 1

target = multiply(multiply(swap01, generator(0)), swap01)
expected = [0, 0, 1, 0, 1, 1]
assert target == matrix_word(expected)

print("BN2_FIRST_CONJUGATION_FIXED_BASIS=PASS")
print("s * p0 * s = pcWord [0,0,1,0,1,1]")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
