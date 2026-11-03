#!/usr/bin/env python3
"""polarity_determines_form census (strict).

Arbitrates the W3 owner theorem before Lean transcription:

    For eta = diag(1, 1, 1, -1) (time slot last) and an ARBITRARY (not
    presumed symmetric) bilinear form m on R^4 with

        (H)  for all x y : eta(x, y) = 0  ->  m(x, y) = 0,

    the functional-pair hypothesis forces m = (m 0 0) * eta, i.e.

        m_ij = 0          (i != j),
        m_00 = m_11 = m_22,   m_33 = -m_00.

Certificate strategy (ring-general, not just characteristic zero):

1. Spike pairs.  The 12 pairs (e_i, e_j), i != j, are eta-orthogonal
   (eta diagonal), and their constraint rows are the corresponding unit
   vectors in the 16 entry-slot space: off-diagonals die individually,
   with no 2-inversion.

2. The three null self-pairs x = (1,0,0,1), (0,1,0,1), (0,0,1,1)
   satisfy eta(x, x) = 0, so (H) on (x, x) forces
   m_00 + m_33 = 0, m_11 + m_33 = 0, m_22 + m_33 = 0 respectively
   (off-diagonals already zero).  The 15 spike rows have rank 15.

3. Ring-generality certificate: for each of the four DIAGONAL columns
   dropped, the resulting 15x15 integer minor has determinant +-1
   (dropping an off-diagonal column zeroes its own unit-pair row, so
   only diagonal drops are the certificate).  A unit minor forces rank
   15 over EVERY commutative ring: no characteristic degenerates the
   spike system.

4. Finite-field confirmation: F_p ranks p in {2, 3, 5, 101} computed
   with DomainMatrix over GF(p), all equal 15.

5. Nullspace isolation: over Q the aggregate constraint matrix
   (spikes + a large random orth-pair sweep, sampled through nullspace
   bases of x^perp) has a one-dimensional nullspace spanned by
   vec(eta); normalizing by the (0,0) entry reproduces eta exactly.

The census exits nonzero on any failure (all checks are strict).
"""

import random
import sys

import sympy as sp
from sympy import Matrix, Rational
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import GF
from sympy import ilcm

random.seed(0x1E7)

DIM = 4
SLOT = 16
d = (1, 1, 1, -1)


def eta_pair(x, y):
    return sum(d[i] * x[i] * y[i] for i in range(DIM))


def pair_row(x, y):
    """Constraint row: m(x, y) = sum_ij m_ij x_i y_j."""
    return [x[i] * y[j] for i in range(DIM) for j in range(DIM)]


def eta_vec():
    return [d[i] if i == 4 * k + k else 0 for k in range(DIM) for i in [k, k]
            for _ in [i]][0:0] or [d[a] if a == b else 0
                                   for a in range(DIM) for b in range(DIM)]


def nullspace_basis_of_orthogonal_complement(x):
    """Integer basis of { y : eta(x, y) = 0 }.  x must be eta-nondegenerate."""
    row = Matrix(1, DIM, [d[i] * x[i] for i in range(DIM)])
    ns = row.nullspace()
    assert len(ns) == DIM - 1, "x must be eta-nondegenerate"
    out = []
    for v in ns:
        lcm = 1
        for t in v:
            lcm = ilcm(lcm, Rational(t).q)
        out.append([int(Rational(t) * lcm) for t in v])
    return out


def make_orth_y(x):
    """Random integer y in x^perp (eta-orthogonal to x)."""
    rows = nullspace_basis_of_orthogonal_complement(x)
    coeffs = [random.randint(-3, 3) for _ in rows]
    y = [sum(c * rows[k][i] for k, c in enumerate(coeffs)) for i in range(DIM)]
    if eta_pair(x, y) != 0:
        raise AssertionError("sampled y is not eta-orthogonal to x")
    return y


def build_rows():
    rows = []
    # 12 off-diagonal unit pairs
    evecs = [[1 if i == k else 0 for k in range(DIM)] for i in range(DIM)]
    for i in range(DIM):
        for j in range(DIM):
            if i == j:
                continue
            assert eta_pair(evecs[i], evecs[j]) == 0
            rows.append(pair_row(evecs[i], evecs[j]))
    # 3 null self-pairs
    nulls = [(1, 0, 0, 1), (0, 1, 0, 1), (0, 0, 1, 1)]
    for x in nulls:
        assert eta_pair(x, x) == 0, f"{x} must lie on the null cone"
        rows.append(pair_row(x, x))
    return rows


def diagonal_minor_certs(spike):
    """For each diagonal column drop, the 15x15 minor has det +-1."""
    diag_cols = [4 * k + k for k in range(DIM)]  # 0, 5, 10, 15
    dets = []
    for col in diag_cols:
        keep = [c for c in range(SLOT) if c != col]
        minor = Matrix(spike).extract(list(range(15)), keep)
        det = int(minor.det())
        dets.append(det)
        if abs(det) != 1:
            raise AssertionError(
                f"spike minor (drop diagonal col {col}) has det {det}")
    return dets


def gf_rank(entries, p):
    dm = DomainMatrix([[sp.Integer(t) % p for t in row] for row in entries],
                      (len(entries), SLOT), GF(p))
    return dm.rank()


def main():
    failures = []
    total = 9

    def ok(label, cond):
        print(f"  [{'OK' if cond else 'FAIL'}]      {label}")
        if not cond:
            failures.append(label)

    print("polarity_determines_form census (strict):")

    eta_v = eta_vec()
    assert sum(eta_v) == 1 + 1 + 1 + (-1), "eta_vec main-diagonal sanity"

    rows = build_rows()
    ok("(P0) spike pairs: 12 orth unit pairs + 3 null self pairs, rows built",
       len(rows) == 15)
    spike = rows

    diagonal_minor_certs(spike)
    ok("(P1) ring certificate: det = +-1 for every DIAGONAL-column-drop minor",
       True)

    ok("(P2) spike system rank 15 over Q", Matrix(spike).rank() == 15)

    for idx, p in enumerate((2, 3, 5, 101)):
        ok(f"(P{3 + idx}) spike system rank 15 over F_{p}", gf_rank(spike, p) == 15)

    # random orth-pair sweep on top of the spikes
    sweep = []
    for _ in range(60):
        x = [random.randint(-6, 6) for _ in range(DIM)]
        while eta_pair(x, x) == 0:
            x = [random.randint(-6, 6) for _ in range(DIM)]
        sweep.append(pair_row(x, make_orth_y(x)))
    full = spike + sweep
    ok("(P7) sweep: aggregate constraint matrix rank stays 15",
       Matrix(full).rank() == 15)

    ns = Matrix(full).nullspace()
    ok("(P8) nullspace one-dimensional", len(ns) == 1)
    if len(ns) == 1:
        v = ns[0]
        pivot = v[0]
        if pivot == 0:
            ok("(P9) nullspace vector normalized by (0,0) entry equals vec(eta)",
               False)
        else:
            norm = [Rational(t) / pivot for t in v]
            ok("(P9) nullspace vector normalized by (0,0) entry equals vec(eta)",
               norm == eta_v)

    print()
    if failures:
        print(f"{total - len(failures)}/{total} checks passed; "
              f"failures: {failures}")
        sys.exit(1)
    print(f"{total}/{total} checks passed; failures: none")
    sys.exit(0)


if __name__ == "__main__":
    main()
