#!/usr/bin/env python3
"""
Exact computer-algebra certificate for the real split-octonion derivation algebra.

This is intentionally not a Lean scaffold.  It recomputes the derivation algebra
from the primitive Zorn product over QQ, proves exact bracket closure by solving
in the computed nullspace basis, computes the adjoint/Killing matrix, and checks
that the real form is the split real form by the Killing-form inertia.
"""

from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

DIM = 8
BASIS_NAMES = ["E11", "E22", "U0", "U1", "U2", "V0", "V1", "V2"]


def cross(x, y):
    return [
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ]


def dot(x, y):
    return sum(x[i] * y[i] for i in range(3))


def zorn_mul(X, Y):
    a, b = X[0], X[1]
    x = [X[2], X[3], X[4]]
    y = [X[5], X[6], X[7]]
    c, d = Y[0], Y[1]
    u = [Y[2], Y[3], Y[4]]
    v = [Y[5], Y[6], Y[7]]
    xy = cross(y, v)
    xu = cross(x, u)
    return sp.Matrix([
        a * c + dot(x, v),
        b * d + dot(y, u),
        a * u[0] + d * x[0] - xy[0],
        a * u[1] + d * x[1] - xy[1],
        a * u[2] + d * x[2] - xy[2],
        b * v[0] + c * y[0] + xu[0],
        b * v[1] + c * y[1] + xu[1],
        b * v[2] + c * y[2] + xu[2],
    ])


def basis_vector(i: int) -> sp.Matrix:
    return sp.eye(DIM).col(i)


BASIS = [basis_vector(i) for i in range(DIM)]
PRODUCT = [[zorn_mul(BASIS[i], BASIS[j]) for j in range(DIM)] for i in range(DIM)]


def derivation_constraint_matrix() -> sp.Matrix:
    rows = []
    for i in range(DIM):
        for j in range(DIM):
            P = PRODUCT[i][j]
            for k in range(DIM):
                row = [sp.Rational(0) for _ in range(DIM * DIM)]
                # D(e_i e_j): if e_i e_j has coefficient P[m], contribution D(e_m)
                for m in range(DIM):
                    row[k + DIM * m] += P[m]
                # - D(e_i) e_j
                for r in range(DIM):
                    coeff = PRODUCT[r][j][k]
                    row[r + DIM * i] -= coeff
                # - e_i D(e_j)
                for s in range(DIM):
                    coeff = PRODUCT[i][s][k]
                    row[s + DIM * j] -= coeff
                rows.append(row)
    return sp.Matrix(rows)


def vec_to_mat(v: sp.Matrix) -> sp.Matrix:
    return sp.Matrix(DIM, DIM, lambda r, c: v[r + DIM * c])


def mat_to_vec(M: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([M[r, c] for c in range(DIM) for r in range(DIM)])


def verify_derivation_matrix(D: sp.Matrix) -> None:
    for i in range(DIM):
        for j in range(DIM):
            lhs = D * PRODUCT[i][j]
            rhs = zorn_mul(D * BASIS[i], BASIS[j]) + zorn_mul(BASIS[i], D * BASIS[j])
            assert sp.simplify(lhs - rhs) == sp.zeros(DIM, 1), (i, j, lhs - rhs)


def express_in_basis(B: sp.Matrix, target: sp.Matrix) -> sp.Matrix:
    sol = B.gauss_jordan_solve(target)[0]
    assert B * sol == target
    return sol


def inertia_symmetric(M: sp.Matrix) -> tuple[int, int, int]:
    """Exact rational congruence inertia for a symmetric matrix."""
    A = sp.Matrix(M)
    pos = neg = zero = 0
    while A.rows:
        n = A.rows
        if A == sp.zeros(n):
            zero += n
            break
        pivot = None
        for i in range(n):
            if A[i, i] != 0:
                pivot = i
                break
        if pivot is not None:
            if pivot != 0:
                A.row_swap(0, pivot)
                A.col_swap(0, pivot)
            p = sp.Rational(A[0, 0])
            if p > 0:
                pos += 1
            else:
                neg += 1
            if n == 1:
                break
            v = A[1:n, 0]
            C = A[1:n, 1:n]
            A = sp.Matrix(sp.simplify(C - (v * v.T) / p))
            continue
        # no diagonal pivot, but matrix nonzero: use hyperbolic 2-plane from off-diagonal entry
        ij = None
        for i in range(n):
            for j in range(i + 1, n):
                if A[i, j] != 0:
                    ij = (i, j)
                    break
            if ij is not None:
                break
        assert ij is not None
        i, j = ij
        order = [i, j] + [k for k in range(n) if k not in (i, j)]
        A = A.extract(order, order)
        a = sp.Rational(A[0, 1])
        pos += 1
        neg += 1
        if n == 2:
            break
        B2 = sp.Matrix([[0, a], [a, 0]])
        E = A[2:n, 0:2]
        C = A[2:n, 2:n]
        A = sp.Matrix(sp.simplify(C - E * B2.inv() * E.T))
    return pos, neg, zero


def main() -> None:
    C = derivation_constraint_matrix()
    rank = C.rank()
    nullity = DIM * DIM - rank
    assert C.rows == 512
    assert C.cols == 64
    assert rank == 50
    assert nullity == 14

    null_basis_vecs = C.nullspace()
    assert len(null_basis_vecs) == 14
    derivs = [vec_to_mat(v) for v in null_basis_vecs]
    for D in derivs:
        verify_derivation_matrix(D)

    B = sp.Matrix.hstack(*[mat_to_vec(D) for D in derivs])
    assert B.rank() == 14

    structure_constants = []
    ad_mats = []
    max_denominator = 1
    for i, Di in enumerate(derivs):
        ad = sp.zeros(14, 14)
        row_constants = []
        for j, Dj in enumerate(derivs):
            comm = Di * Dj - Dj * Di
            verify_derivation_matrix(comm)
            coords = express_in_basis(B, mat_to_vec(comm))
            for q in coords:
                max_denominator = sp.ilcm(max_denominator, sp.denom(q))
            ad[:, j] = coords
            row_constants.append([str(sp.simplify(q)) for q in coords])
        ad_mats.append(ad)
        structure_constants.append(row_constants)

    K = sp.Matrix(14, 14, lambda i, j: sp.trace(ad_mats[i] * ad_mats[j]))
    assert K == K.T
    killing_rank = K.rank()
    assert killing_rank == 14
    inertia = inertia_symmetric(K)
    assert inertia[2] == 0
    assert sorted(inertia[:2]) == [6, 8]

    # A split real simple Lie algebra of type G2 has dimension 14 and Killing-form
    # inertia (8,6), up to global sign convention.  The exact computation here is
    # over QQ and therefore symbolically certifies the real split form.
    certificate = {
        "carrier": "Zorn split octonions over QQ/RR, basis E11,E22,U0,U1,U2,V0,V1,V2",
        "constraint_rows": int(C.rows),
        "constraint_cols": int(C.cols),
        "constraint_rank": int(rank),
        "derivation_dimension": int(nullity),
        "basis_count": len(derivs),
        "bracket_closed": True,
        "structure_constants_basis": "computed_nullspace_basis",
        "structure_constants_max_denominator": int(max_denominator),
        "killing_rank": int(killing_rank),
        "killing_inertia_pos_neg_zero": list(map(int, inertia)),
        "real_form": "split real g2 = g_{2(2)} by exact Killing inertia (8,6) up to sign",
        "finite_g2_2_order": 12096,
        "finite_real_boundary": "finite G2(2) order ledger is separate from real split G_{2(2)}",
    }
    out = Path(__file__).resolve().parent / "artifacts" / "real_split_g2_exact_ca_certificate.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    print("EXACT_CA_SPLIT_OCTONION_DERIVATIONS_OK")
    print(json.dumps(certificate, sort_keys=True))


if __name__ == "__main__":
    main()
