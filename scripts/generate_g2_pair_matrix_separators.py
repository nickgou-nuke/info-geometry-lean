#!/usr/bin/env python3
"""Generate pairwise matrix-entry separators for the G2 PC/Weyl carrier.

This is an evidence generator only.  It uses the GAP-exported PC rows and
the fixed Lean Weyl matrices, and emits witnesses for later explicit Lean
lemmas.
"""
import re, subprocess
import numpy as np

raw = subprocess.run(["gap", "-q", "scripts/export_carrier_pc_rows.g"],
                     check=True, capture_output=True, text=True).stdout
rows = {}
for line in raw.splitlines():
    m = re.fullmatch(r"PCROW ([1-6]) ([0-9,;]*)", line.strip())
    if m:
        rows[int(m.group(1))-1] = [[int(x)-1 for x in block.split(",") if x]
                                   for block in m.group(2).split(";")]
assert set(rows) == set(range(6))

def mm(a, b):
    return (a @ b) % 2

I = np.eye(8, dtype=np.int8)
def pcmat(k):
    return np.array([[int(j in rows[k][i]) for j in range(8)] for i in range(8)],
                     dtype=np.int8)

def word(bits):
    out = I.copy()
    for k, bit in enumerate(bits):
        if bit:
            out = mm(pcmat(k), out)
    return out

def perm(cycles):
    p = list(range(8))
    for cyc in cycles:
        cyc = [x-1 for x in cyc]
        for a, b in zip(cyc, cyc[1:] + cyc[:1]): p[a] = b
    return np.array([[int(p[j] == i) for j in range(8)] for i in range(8)],
                     dtype=np.int8)

s = perm([(3,4), (6,7)])
c = mm(perm([(3,4,5), (6,7,8)]), perm([(1,2), (3,6), (4,7), (5,8)]))
def pw(m, n):
    out = I.copy()
    for _ in range(n): out = mm(out, m)
    return out

weyl = []
for refl in (False, True):
    for k in range(6):
        w = pw(c, k)
        if refl: w = mm(w, s)
        weyl.append(w)

pcwords = np.array([word([(mask >> k) & 1 for k in range(6)])
                    for mask in range(64)], dtype=np.int8)
for k in range(12):
    for l in range(k+1, 12):
        candidates = []
        left = np.einsum('dab,bc->dac', pcwords, weyl[k])
        left = np.einsum('dab,ebc->deac', left, pcwords)
        for i in range(8):
            for j in range(8):
                vals = left[:, :, i, j]
                v = int(vals.flat[0])
                if np.all(vals == v) and v != int(weyl[l][i, j]):
                    candidates.append((i, j, v, int(weyl[l][i, j])))
        if not candidates:
            raise SystemExit(f"NO_SEPARATOR {k} {l}")
        print(k, l, *candidates[0])
