#!/usr/bin/env python3
"""Exact rational CAS verification for the 8D split-octonion Cayley-Dickson
1+3+1+3 anatomy, chiral Zorn nullspace decomposition, Cl(3,3) CAR, and SL_3
stabilizer action.

Uses pure Python stdlib (fractions.Fraction) so it runs in any Python 3.11+
environment without external CAS dependencies.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable


F = Fraction


def q_add(a: tuple[F, F, F, F], b: tuple[F, F, F, F]) -> tuple[F, F, F, F]:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3])


def q_sub(a: tuple[F, F, F, F], b: tuple[F, F, F, F]) -> tuple[F, F, F, F]:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3])


def q_neg(a: tuple[F, F, F, F]) -> tuple[F, F, F, F]:
    return (-a[0], -a[1], -a[2], -a[3])


def q_smul(c: F, a: tuple[F, F, F, F]) -> tuple[F, F, F, F]:
    return (c * a[0], c * a[1], c * a[2], c * a[3])


def q_star(a: tuple[F, F, F, F]) -> tuple[F, F, F, F]:
    return (a[0], -a[1], -a[2], -a[3])


def q_mul(a: tuple[F, F, F, F], b: tuple[F, F, F, F]) -> tuple[F, F, F, F]:
    r0 = a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3]
    r1 = a[0] * b[1] + a[1] * b[0] + a[2] * b[3] - a[3] * b[2]
    r2 = a[0] * b[2] - a[1] * b[3] + a[2] * b[0] + a[3] * b[1]
    r3 = a[0] * b[3] + a[1] * b[2] - a[2] * b[1] + a[3] * b[0]
    return (r0, r1, r2, r3)


def q_norm_sq(a: tuple[F, F, F, F]) -> F:
    return a[0] ** 2 + a[1] ** 2 + a[2] ** 2 + a[3] ** 2


SplitOct = tuple[tuple[F, F, F, F], tuple[F, F, F, F]]


def cd_zero() -> SplitOct:
    z = (F(0), F(0), F(0), F(0))
    return (z, z)


def cd_one() -> SplitOct:
    return ((F(1), F(0), F(0), F(0)), (F(0), F(0), F(0), F(0)))


def cd_add(x: SplitOct, y: SplitOct) -> SplitOct:
    return (q_add(x[0], y[0]), q_add(x[1], y[1]))


def cd_sub(x: SplitOct, y: SplitOct) -> SplitOct:
    return (q_sub(x[0], y[0]), q_sub(x[1], y[1]))


def cd_neg(x: SplitOct) -> SplitOct:
    return (q_neg(x[0]), q_neg(x[1]))


def cd_smul(c: F, x: SplitOct) -> SplitOct:
    return (q_smul(c, x[0]), q_smul(c, x[1]))


def cd_mul(x: SplitOct, y: SplitOct) -> SplitOct:
    a, b = x
    c, d = y
    return (q_add(q_mul(a, c), q_mul(q_star(d), b)),
            q_add(q_mul(d, a), q_mul(b, q_star(c))))


def cd_conj(x: SplitOct) -> SplitOct:
    return (q_star(x[0]), q_neg(x[1]))


def cd_norm(x: SplitOct) -> F:
    return q_norm_sq(x[0]) - q_norm_sq(x[1])


def cd_krein_bilinear(x: SplitOct, y: SplitOct) -> F:
    return (cd_norm(cd_add(x, y)) - cd_norm(x) - cd_norm(y)) / F(2)


# 1 + 3 + 1 + 3 basis elements
Q0 = (F(0), F(0), F(0), F(0))
Q_BASIS = [
    (F(0), F(1), F(0), F(0)),
    (F(0), F(0), F(1), F(0)),
    (F(0), F(0), F(0), F(1)),
]
ONE_CD: SplitOct = cd_one()
I_CD: list[SplitOct] = [(q, Q0) for q in Q_BASIS]
ELL_CD: SplitOct = (Q0, (F(1), F(0), F(0), F(0)))
S_CD: list[SplitOct] = [cd_mul(ELL_CD, ik) for ik in I_CD]

BASIS_1313: list[SplitOct] = [ONE_CD, *I_CD, ELL_CD, *S_CD]


def cd_to_coord8(x: SplitOct) -> list[F]:
    q, r = x
    return [q[0], q[1], q[2], q[3], r[0], -r[1], -r[2], -r[3]]


def coord8_to_cd(c: Iterable[F]) -> SplitOct:
    vals = list(c)
    return (
        (vals[0], vals[1], vals[2], vals[3]),
        (vals[4], -vals[5], -vals[6], -vals[7]),
    )


def vec3_dot(u: list[F], v: list[F]) -> F:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def vec3_cross(u: list[F], v: list[F]) -> list[F]:
    return [
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    ]


ZornMatrix = tuple[F, F, list[F], list[F]]


def to_zorn_matrix(x: SplitOct) -> ZornMatrix:
    q, r = x
    return (
        q[0] + r[0],
        q[0] - r[0],
        [r[1] - q[1], r[2] - q[2], r[3] - q[3]],
        [q[1] + r[1], q[2] + r[2], q[3] + r[3]],
    )


def from_zorn_matrix(z: ZornMatrix) -> SplitOct:
    a, b, x, y = z
    return (
        ((a + b) / 2, (y[0] - x[0]) / 2, (y[1] - x[1]) / 2, (y[2] - x[2]) / 2),
        ((a - b) / 2, (x[0] + y[0]) / 2, (x[1] + y[1]) / 2, (x[2] + y[2]) / 2),
    )


def zorn_mul(z1: ZornMatrix, z2: ZornMatrix) -> ZornMatrix:
    a1, b1, x1, y1 = z1
    a2, b2, x2, y2 = z2
    c12 = vec3_cross(y1, y2)
    d12 = vec3_cross(x1, x2)
    return (
        a1 * a2 + vec3_dot(x1, y2),
        b1 * b2 + vec3_dot(y1, x2),
        [a1 * x2[i] + b2 * x1[i] - c12[i] for i in range(3)],
        [b1 * y2[i] + a2 * y1[i] + d12[i] for i in range(3)],
    )


def zorn_conj(z: ZornMatrix) -> ZornMatrix:
    a, b, x, y = z
    return (b, a, [-v for v in x], [-v for v in y])


def zorn_det(z: ZornMatrix) -> F:
    a, b, x, y = z
    return a * b - vec3_dot(x, y)


def zorn_to_fin8(z: ZornMatrix) -> list[F]:
    # ZornSplitOctonion has a := z.a, u := z.x, v := z.y, b := z.b
    # zornToFin8 := ![z.a, z.u 2, z.u 1, z.v 0, z.u 0, -z.v 1, z.v 2, z.b]
    a, b, u, v = z
    return [a, u[2], u[1], v[0], u[0], -v[1], v[2], b]


def fin8_to_zorn(psi: list[F]) -> ZornMatrix:
    return (
        psi[0],
        psi[7],
        [psi[4], psi[2], psi[1]],
        [psi[3], -psi[5], psi[6]],
    )


def mat_zero(n: int = 8) -> list[list[F]]:
    return [[F(0) for _ in range(n)] for _ in range(n)]


def mat_eye(n: int = 8) -> list[list[F]]:
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]


def mat_add(A: list[list[F]], B: list[list[F]]) -> list[list[F]]:
    n = len(A)
    return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]


def mat_smul(c: F, A: list[list[F]]) -> list[list[F]]:
    return [[c * x for x in row] for row in A]


def mat_mul(A: list[list[F]], B: list[list[F]]) -> list[list[F]]:
    n = len(A)
    return [
        [sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)]
        for i in range(n)
    ]


def mat_vec(A: list[list[F]], v: list[F]) -> list[F]:
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def mat_det(M: list[list[F]]) -> F:
    n = len(M)
    A = [row[:] for row in M]
    det = F(1)
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if A[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            return F(0)
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            det = -det
        piv = A[col][col]
        det *= piv
        for r in range(col + 1, n):
            factor = A[r][col] / piv
            if factor != 0:
                for k in range(col, n):
                    A[r][k] -= factor * A[col][k]
    return det


def mat_inv(M: list[list[F]]) -> list[list[F]]:
    n = len(M)
    A = [M[i][:] + [F(1) if i == j else F(0) for j in range(n)] for i in range(n)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if A[r][col] != 0), None)
        assert pivot is not None, "Singular matrix"
        A[col], A[pivot] = A[pivot], A[col]
        piv = A[col][col]
        A[col] = [x / piv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                factor = A[r][col]
                A[r] = [A[r][k] - factor * A[col][k] for k in range(2 * n)]
    return [row[n:] for row in A]


def mat_transpose(M: list[list[F]]) -> list[list[F]]:
    return [[M[j][i] for j in range(len(M))] for i in range(len(M[0]))]


def left_mul_mat(x: SplitOct) -> list[list[F]]:
    cols = [cd_to_coord8(cd_mul(x, b)) for b in BASIS_1313]
    return [[cols[j][i] for j in range(8)] for i in range(8)]


def zorn_left_act_mat(z: ZornMatrix) -> list[list[F]]:
    cols = []
    for j in range(8):
        e = [F(1) if k == j else F(0) for k in range(8)]
        cols.append(zorn_to_fin8(zorn_mul(z, fin8_to_zorn(e))))
    return [[cols[j][i] for j in range(8)] for i in range(8)]


def frac_str(x: F) -> str:
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)


def serialize_split_oct(x: SplitOct) -> dict[str, list[str]]:
    return {
        "q": [frac_str(v) for v in x[0]],
        "r": [frac_str(v) for v in x[1]],
    }


def serialize_zorn(z: ZornMatrix) -> dict[str, object]:
    return {
        "a": frac_str(z[0]),
        "b": frac_str(z[1]),
        "x": [frac_str(v) for v in z[2]],
        "y": [frac_str(v) for v in z[3]],
    }


def run_verification() -> dict[str, object]:
    # Test elements with non-trivial rational coordinates
    X: SplitOct = (
        (F(1, 2), F(-2, 3), F(3, 4), F(1, 5)),
        (F(-1, 3), F(5, 2), F(-1, 4), F(2, 7)),
    )
    Y: SplitOct = (
        (F(3, 5), F(1, 2), F(-4, 3), F(2, 5)),
        (F(2, 3), F(-1, 6), F(3, 2), F(-1, 2)),
    )
    Z: SplitOct = (
        (F(-2, 5), F(1, 7), F(1, 3), F(-3, 4)),
        (F(1, 2), F(2, 3), F(-3, 5), F(1, 4)),
    )

    # 1. cdA algebra, conjugation, norm & multiplicativity
    assert cd_mul(ONE_CD, X) == X
    assert cd_mul(X, ONE_CD) == X
    assert cd_mul(X, cd_conj(X)) == cd_smul(cd_norm(X), ONE_CD)
    assert cd_mul(cd_conj(X), X) == cd_smul(cd_norm(X), ONE_CD)
    assert cd_conj(cd_mul(X, Y)) == cd_mul(cd_conj(Y), cd_conj(X))
    assert cd_norm(cd_mul(X, Y)) == cd_norm(X) * cd_norm(Y)

    # 2. 1+3+1+3 basis identities and (4,4) Krein signature
    for k in range(3):
        assert cd_mul(I_CD[k], I_CD[k]) == cd_neg(ONE_CD)
        assert S_CD[k] == (Q0, q_neg(Q_BASIS[k]))
        assert cd_mul(S_CD[k], S_CD[k]) == ONE_CD
        assert cd_add(cd_mul(ELL_CD, I_CD[k]), cd_mul(I_CD[k], ELL_CD)) == cd_zero()
    assert cd_mul(ELL_CD, ELL_CD) == ONE_CD
    for k in range(3):
        nxt = (k + 1) % 3
        thd = (k + 2) % 3
        assert cd_mul(I_CD[k], I_CD[nxt]) == I_CD[thd]
        assert cd_mul(I_CD[nxt], I_CD[k]) == cd_neg(I_CD[thd])
    krein_diag = [cd_krein_bilinear(b, b) for b in BASIS_1313]
    assert krein_diag == [F(1), F(1), F(1), F(1), F(-1), F(-1), F(-1), F(-1)]
    for i in range(8):
        for j in range(i + 1, 8):
            assert cd_krein_bilinear(BASIS_1313[i], BASIS_1313[j]) == F(0)
    assert coord8_to_cd(cd_to_coord8(X)) == X

    # 3. toZornMatrix isomorphism & ZornSplitOctonion alignment
    assert from_zorn_matrix(to_zorn_matrix(X)) == X
    assert to_zorn_matrix(ONE_CD) == (F(1), F(1), [F(0)] * 3, [F(0)] * 3)
    assert to_zorn_matrix(cd_mul(X, Y)) == zorn_mul(to_zorn_matrix(X), to_zorn_matrix(Y))
    assert to_zorn_matrix(cd_conj(X)) == zorn_conj(to_zorn_matrix(X))
    assert zorn_det(to_zorn_matrix(X)) == cd_norm(X)

    # Explicit 8x8 change of basis T between cd_to_coord8 and zorn_to_fin8
    T_cols = [zorn_to_fin8(to_zorn_matrix(b)) for b in BASIS_1313]
    T_mat = [[T_cols[j][i] for j in range(8)] for i in range(8)]
    assert mat_det(T_mat) == F(-16)
    P_mat = mat_inv(T_mat)
    assert mat_mul(P_mat, T_mat) == mat_eye(8)
    assert mat_mul(T_mat, P_mat) == mat_eye(8)
    assert mat_mul(T_mat, left_mul_mat(X)) == mat_mul(zorn_left_act_mat(to_zorn_matrix(X)), T_mat)

    # 4. Polarized left-alternative law on 8x8 matrices + non-associativity
    L_X = left_mul_mat(X)
    L_Y = left_mul_mat(Y)
    L_XY_YX = left_mul_mat(cd_add(cd_mul(X, Y), cd_mul(Y, X)))
    assert mat_add(mat_mul(L_X, L_Y), mat_mul(L_Y, L_X)) == L_XY_YX
    assert mat_vec(L_X, cd_to_coord8(Z)) == cd_to_coord8(cd_mul(X, Z))
    assert cd_mul(cd_mul(I_CD[0], I_CD[1]), ELL_CD) != cd_mul(I_CD[0], cd_mul(I_CD[1], ELL_CD))
    assert mat_mul(left_mul_mat(I_CD[0]), left_mul_mat(ELL_CD)) != left_mul_mat(cd_mul(I_CD[0], ELL_CD))

    # 5. Seven anticommuting 8x8 operators
    seven_gens = [*I_CD, ELL_CD, *S_CD]
    seven_mats = [left_mul_mat(g) for g in seven_gens]
    expected_sqs = [-1, -1, -1, 1, 1, 1, 1]
    anticomm_pairs = 0
    for j in range(7):
        assert mat_mul(seven_mats[j], seven_mats[j]) == mat_smul(F(expected_sqs[j]), mat_eye(8))
        for k in range(j + 1, 7):
            assert mat_add(mat_mul(seven_mats[j], seven_mats[k]),
                           mat_mul(seven_mats[k], seven_mats[j])) == mat_zero(8)
            anticomm_pairs += 1
    assert anticomm_pairs == 21

    # 6. Chiral nullspace laws & spin-frame rotation vs ambient
    u_plus = cd_smul(F(1, 2), cd_add(ONE_CD, ELL_CD))
    u_minus = cd_smul(F(1, 2), cd_sub(ONE_CD, ELL_CD))
    assert cd_mul(u_plus, u_plus) == u_plus
    assert cd_mul(u_minus, u_minus) == u_minus
    assert cd_mul(u_plus, u_minus) == cd_zero()
    assert cd_mul(u_minus, u_plus) == cd_zero()
    assert cd_add(u_plus, u_minus) == ONE_CD

    e_plus = [cd_mul(u_plus, ik) for ik in I_CD]
    e_minus = [cd_mul(u_minus, ik) for ik in I_CD]
    for k in range(3):
        assert e_plus[k] == cd_smul(F(1, 2), cd_add(I_CD[k], S_CD[k]))
        assert e_plus[k] == cd_mul(I_CD[k], u_minus)
        assert e_minus[k] == cd_smul(F(1, 2), cd_sub(I_CD[k], S_CD[k]))
        assert e_minus[k] == cd_mul(I_CD[k], u_plus)

    # N_± = u_± O~ = {(q, ±q*)} has cdNorm ≡ 0
    q_test = (F(3, 2), F(-5, 3), F(1, 4), F(7, 5))
    n_plus_elem = (q_test, q_star(q_test))
    n_minus_elem = (q_test, q_neg(q_star(q_test)))
    assert cd_mul(u_plus, (q_smul(F(2), q_test), Q0)) == n_plus_elem
    assert cd_mul(u_minus, (q_smul(F(2), q_test), Q0)) == n_minus_elem
    assert cd_norm(cd_mul(u_plus, X)) == F(0)
    assert cd_norm(cd_mul(u_minus, Y)) == F(0)
    assert cd_norm(n_plus_elem) == F(0)
    assert cd_norm(n_minus_elem) == F(0)

    # Spin-frame right H-action vs ambient product
    assert cd_mul(u_plus, (q_mul(Q_BASIS[0], Q_BASIS[2]), Q0)) == cd_neg(e_plus[1])
    assert cd_mul(u_plus, (q_mul(Q_BASIS[1], Q_BASIS[2]), Q0)) == e_plus[0]
    assert cd_mul(u_minus, (q_mul(Q_BASIS[0], Q_BASIS[2]), Q0)) == cd_neg(e_minus[1])
    assert cd_mul(u_minus, (q_mul(Q_BASIS[1], Q_BASIS[2]), Q0)) == e_minus[0]
    assert cd_mul(cd_mul(u_plus, I_CD[0]), I_CD[2]) == cd_neg(e_minus[1])

    # Zorn cross-pairing norm identity
    alpha_p, alpha_m = F(3, 2), F(-5, 4)
    a_vec = [F(1, 2), F(-2, 3), F(3, 5)]
    b_vec = [F(4, 3), F(1, 5), F(-1, 2)]
    chiral_X = cd_add(cd_smul(alpha_p, u_plus), cd_smul(alpha_m, u_minus))
    for k in range(3):
        chiral_X = cd_add(chiral_X, cd_add(cd_smul(a_vec[k], e_plus[k]), cd_smul(b_vec[k], e_minus[k])))
    assert cd_norm(chiral_X) == alpha_p * alpha_m + vec3_dot(a_vec, b_vec)
    assert to_zorn_matrix(chiral_X) == (alpha_p, alpha_m, [-v for v in a_vec], b_vec)

    # 7. Fermionic CAR and 8x8 matrix CAR for {L_{e_j^+}, -L_{e_k^-}}
    for j in range(3):
        assert cd_mul(e_plus[j], e_plus[j]) == cd_zero()
        assert cd_mul(e_minus[j], e_minus[j]) == cd_zero()
        for k in range(3):
            delta = F(1) if j == k else F(0)
            assert cd_mul(e_plus[j], e_minus[k]) == cd_smul(-delta, u_plus)
            assert cd_mul(e_minus[k], e_plus[j]) == cd_smul(-delta, u_minus)
            assert cd_add(cd_mul(e_plus[j], e_plus[k]), cd_mul(e_plus[k], e_plus[j])) == cd_zero()
            assert cd_add(cd_mul(e_minus[j], e_minus[k]), cd_mul(e_minus[k], e_minus[j])) == cd_zero()
            assert cd_add(cd_mul(e_plus[j], e_minus[k]), cd_mul(e_minus[k], e_plus[j])) == cd_smul(-delta, ONE_CD)

    L_ep = [left_mul_mat(ep) for ep in e_plus]
    neg_L_em = [mat_smul(F(-1), left_mul_mat(em)) for em in e_minus]
    for j in range(3):
        for k in range(3):
            delta = F(1) if j == k else F(0)
            assert mat_add(mat_mul(L_ep[j], L_ep[k]), mat_mul(L_ep[k], L_ep[j])) == mat_zero(8)
            assert mat_add(mat_mul(neg_L_em[j], neg_L_em[k]), mat_mul(neg_L_em[k], neg_L_em[j])) == mat_zero(8)
            assert mat_add(mat_mul(L_ep[j], neg_L_em[k]), mat_mul(neg_L_em[k], L_ep[j])) == mat_smul(delta, mat_eye(8))

    # 8. Cross products & singlet
    eps = {
        (0, 1, 2): 1, (1, 2, 0): 1, (2, 0, 1): 1,
        (1, 0, 2): -1, (2, 1, 0): -1, (0, 2, 1): -1,
    }
    for j in range(3):
        for k in range(3):
            rhs_m = cd_zero()
            rhs_p = cd_zero()
            for m in range(3):
                c = F(eps.get((j, k, m), 0))
                if c != 0:
                    rhs_m = cd_add(rhs_m, cd_smul(c, e_minus[m]))
                    rhs_p = cd_add(rhs_p, cd_smul(c, e_plus[m]))
            assert cd_mul(e_plus[j], e_plus[k]) == rhs_m
            assert cd_mul(e_minus[j], e_minus[k]) == rhs_p
    assert cd_mul(cd_mul(e_plus[0], e_plus[1]), e_plus[2]) == cd_neg(u_minus)

    # 9. SL_3(R) det-1 action preserving cdMul and cdNorm (and det != 1 failure)
    g_sl3 = [
        [F(1), F(2), F(-1)],
        [F(0), F(1), F(3)],
        [F(1), F(2), F(0)],
    ]
    assert mat_det(g_sl3) == F(1)
    g_inv_T = mat_transpose(mat_inv(g_sl3))

    def sl3_act(g: list[list[F]], g_dual: list[list[F]], elem: SplitOct) -> SplitOct:
        ap, am, neg_a, b = to_zorn_matrix(elem)
        a = [-v for v in neg_a]
        ga = mat_vec(g, a)
        gb = mat_vec(g_dual, b)
        return from_zorn_matrix((ap, am, [-v for v in ga], gb))

    assert sl3_act(g_sl3, g_inv_T, cd_mul(X, Y)) == cd_mul(
        sl3_act(g_sl3, g_inv_T, X), sl3_act(g_sl3, g_inv_T, Y)
    )
    assert cd_norm(sl3_act(g_sl3, g_inv_T, X)) == cd_norm(X)

    g_bad = [
        [F(2), F(0), F(0)],
        [F(0), F(1), F(0)],
        [F(0), F(0), F(1)],
    ]
    assert mat_det(g_bad) == F(2)
    g_bad_inv_T = mat_transpose(mat_inv(g_bad))
    assert sl3_act(g_bad, g_bad_inv_T, cd_mul(e_plus[1], e_plus[2])) != cd_mul(
        sl3_act(g_bad, g_bad_inv_T, e_plus[1]),
        sl3_act(g_bad, g_bad_inv_T, e_plus[2]),
    )

    script_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    round_trip_prod = cd_mul(X, Y)
    payload: dict[str, object] = {
        "schema": "info_geometry.cas_witness.v1",
        "object": "split_octonion_1313_chiral_zorn_cl33_sl3",
        "lean_owner": "InfoGeometry.Canonical.SplitOctonionCayleyDickson",
        "cas_source": "scripts/verify_split_octonion_chiral_zorn.py",
        "script_sha256": script_sha256,
        "arithmetic_domain": "exact_fractions_Fraction_over_Q",
        "basis_order": ["1", "i1", "i2", "i3", "ell", "s1", "s2", "s3"],
        "chiral_basis_order": [
            "u_plus", "u_minus",
            "e1_plus", "e2_plus", "e3_plus",
            "e1_minus", "e2_minus", "e3_minus",
        ],
        "multiplication_convention": (
            "cdA: (a,b)*(c,d) = (a*c + star(d)*b, d*a + b*star(c)); "
            "Phi(alpha_+, alpha_-, a, b) = ZornMatrix(alpha_+, alpha_-, -a, b)"
        ),
        "anti_hom": False,
        "krein_signature_diagonal": [1, 1, 1, 1, -1, -1, -1, -1],
        "seven_operator_squares": expected_sqs,
        "change_of_basis_det_T": frac_str(mat_det(T_mat)),
        "checked": {
            "cdA_1313_basis_identities": True,
            "krein_signature_4_4_and_multiplicativity": True,
            "toZornMatrix_algebra_isomorphism": True,
            "polarized_left_alternative_8x8": True,
            "seven_anticommuting_8x8_operators": True,
            "chiral_nullspace_isotropic_and_spin_frame": True,
            "fermionic_car_and_mat8_cl33": True,
            "chiral_cross_products_and_singlet": True,
            "sl3_det1_automorphism_action": True,
        },
        "round_trip_verified": True,
        "round_trip_element": {
            "input": {
                "X": serialize_split_oct(X),
                "Y": serialize_split_oct(Y),
            },
            "expected_output": {
                "cd_product": serialize_split_oct(round_trip_prod),
                "ZornMatrix_product": serialize_zorn(to_zorn_matrix(round_trip_prod)),
                "cdNorm_product": frac_str(cd_norm(round_trip_prod)),
            },
            "lean_theorem": "splitOctCDEquivZornMatrix_mul",
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    payload["artifact_hash"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify split-octonion 1+3+1+3 / chiral Zorn / Cl(3,3) / SL3 identities."
    )
    parser.add_argument(
        "--out",
        "--output",
        dest="output",
        type=Path,
        default=Path("scratch/verify_split_octonion_chiral_zorn.json"),
        help="Output JSON path (default: scratch/verify_split_octonion_chiral_zorn.json).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print generated JSON payload to stdout.",
    )
    args = parser.parse_args()
    payload = run_verification()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    args.output.write_text(text, encoding="utf-8")
    if args.json:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
