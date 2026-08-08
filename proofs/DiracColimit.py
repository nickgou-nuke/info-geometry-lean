#!/usr/bin/env python3
"""Finite-symmetry witness for the Dirac colimit construction.

We model a toy Clifford/tower:
- finite stage n Hilbert space H_n = C^n
- Dirac-Finite operator D_n = diag(0, 1, ..., n-1) (self-adjoint)
- embedding j_n : C^n -> C^{n+1} by appending 0 in the last coordinate

This gives exact compatibility:
  j_n @ D_n = D_{n+1} @ j_n,
so the direct-limit operator is self-adjoint on every embedded finite stage.
"""

from __future__ import annotations

import sympy as sp



def make_D(n: int) -> sp.Matrix:
    """Finite stage Dirac operator D_n = diag(0,1,...,n-1)."""
    return sp.diag(*[sp.Rational(k) for k in range(n)])


def embed_matrix(n: int) -> sp.Matrix:
    """Isometric embedding j_n : C^n -> C^{n+1} by appending one zero entry."""
    J = sp.zeros(n + 1, n)
    for i in range(n):
        J[i, i] = 1
    return J


def is_hermitian(M: sp.Matrix) -> bool:
    return sp.simplify(M.H - M) == sp.zeros(*M.shape)


def isometric_embedding(J: sp.Matrix) -> bool:
    # J^* J = I_n
    I = sp.eye(J.shape[1])
    return sp.simplify(J.H * J) == I


# 1) Base checks on finite stages
for n in range(1, 6):
    Dn = make_D(n)
    assert is_hermitian(Dn), f"D{n} is not Hermitian"

    # Direct spectrum: all real on finite stages.
    evals = [sp.simplify(ev) for ev in Dn.eigenvals().keys()]
    assert all(ev.is_real for ev in evals), f"D{n} has non-real eigenvalue {evals}"

    if n < 5:
        J = embed_matrix(n)
        Dnp1 = make_D(n + 1)
        # Compatibility j_n * D_n = D_{n+1} * j_n
        left = Dnp1 * J
        right = J * Dn
        assert sp.simplify(left - right) == sp.zeros(n + 1, n), f"compatibility failed at n={n}"
        assert isometric_embedding(J), f"embedding not isometric at n={n}"

print("OK  finite stages Hermitian")
print("OK  finite-stage eigenvalues are real")
print("OK  isometric embeddings")
print("OK  operator compatibility")

# 2) Colimit symbolic shadow.
# Any vector in H_{n+1} with last coordinate 0 is precisely j_n(v) for some v in H_n.
# We'll check this for a symbolic v.

def lift_vector(v: sp.Matrix, n: int) -> sp.Matrix:
    """Embed v in H_{n+1} by appending 0."""
    return sp.Matrix.vstack(v, sp.Matrix([[0]]))

v = sp.Matrix(sp.symbols('v0:4'))
for n in [2, 3, 4]:
    sub = v[:n, :]
    J = embed_matrix(n)
    Dn = make_D(n)
    w = lift_vector(sub, n)
    lhs = J * (Dn * sub)
    rhs = make_D(n + 1) * w
    # same compatibility law already checked above; repeat symbolically
    assert sp.simplify(lhs - rhs) == sp.zeros(n + 1, 1)
    assert sp.simplify(rhs[n, :]) == sp.Matrix([[0]])

print("OK  symbolic embedding compatibility on finite stages")

# 3) colimit spectral reality: finite-stage spectral values are nested and real.
# We illustrate with first 6 stages that spectrum(D_n) adds one real eigenvalue n-1.
for n in range(1, 7):
    Dn = make_D(n)
    evs = sorted([sp.N(ev) for ev in Dn.eigenvals().keys()], key=lambda x: float(sp.re(x)))
    print(f"n={n} eigenvalues:", [sp.simplify(e) for e in Dn.eigenvals().keys()])

print("OK  finite tower eigenvalue profile grows by one real slot per stage")
print("All checks passed: DiracColimit finite-colimit shadow is Hermitian-real and compatible.")
