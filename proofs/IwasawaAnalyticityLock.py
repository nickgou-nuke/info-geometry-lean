#!/usr/bin/env python3
"""SymPy mirror of the conservative Iwasawa analyticity lock.

This script checks the finite algebra behind `IwasawaAnalyticityLock.lean`:

  traceDefect_n = log(det(K_n A_n N_n)) - sum_i log(lambda_i)

for the concrete Primon/Cuntz KAN model where K and N are identity matrices and
A is the positive diagonal matrix diag(1, ..., n+1).

It also mirrors the colimit-transport shape: if a global defect is represented
by a finite defect and every finite defect is zero, the represented global defect
is zero.  This is a symbolic sanity check, not an analytic determinant theorem.
"""

from __future__ import annotations

import sympy as sp


def kan_factor(n: int) -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    """Concrete finite Primon/Cuntz KAN factor at stage n."""
    size = n + 1
    K = sp.eye(size)
    A = sp.diag(*[sp.Integer(i + 1) for i in range(size)])
    N = sp.eye(size)
    return K, A, N


def total(K: sp.Matrix, A: sp.Matrix, N: sp.Matrix) -> sp.Matrix:
    return K * A * N


def spectral_log_scale(n: int) -> sp.Expr:
    return sum(sp.log(sp.Integer(i + 1)) for i in range(n + 1))


def logcombine_zero(expr: sp.Expr) -> sp.Expr:
    """Canonicalize positive log products into one logarithm."""
    return sp.simplify(sp.logcombine(expr, force=True))


def trace_defect(n: int) -> sp.Expr:
    K, A, N = kan_factor(n)
    det_total = sp.det(total(K, A, N))
    return logcombine_zero(sp.log(det_total) - spectral_log_scale(n))


def represented_colimit_defect(stage: int) -> sp.Expr:
    """Colimit shadow: the global defect is represented by one finite stage."""
    return trace_defect(stage)


for n in range(0, 8):
    K, A, N = kan_factor(n)
    T = total(K, A, N)

    expected_det = sp.prod(sp.Integer(i + 1) for i in range(n + 1))
    assert sp.det(K) == 1, f"K determinant failed at n={n}"
    assert sp.det(N) == 1, f"N determinant failed at n={n}"
    assert sp.det(T) == expected_det, f"det total failed at n={n}"
    assert trace_defect(n) == 0, f"trace defect failed at n={n}: {trace_defect(n)}"

print("OK  finite K/N determinants are one")
print("OK  finite total determinant is the product of spectral weights")
print("OK  finite log-det trace defects vanish")

for stage in range(0, 8):
    assert represented_colimit_defect(stage) == 0, (
        f"represented colimit defect failed at stage={stage}"
    )

print("OK  represented colimit defects vanish when pulled back to finite stages")
print("All checks passed: Iwasawa analyticity lock finite/colimit shadow is exact.")

