#!/usr/bin/env python3
"""Multilingual 5-CAS Verification Suite for Isospin in the 5-Graded Cl(5,5) / Pin+-(5,5) / so(5,5) Framework.

Verifies the exact mathematical dictionary across five independent computer algebra engines:
  1. SymPy     — Explicit 32x32 real Jordan-Wigner matrices of Cl(5,5) (`MatStage 5`),
                 4-projector resolution (Pi_+, Pi_-, Pi_pair^+, Pi_pair^-),
                 grade-0 isospin sl(2)_iso vs. grade-+-2 pairing quasispin sl(2)_pair,
                 and Pin_+(5,5) / Pin_-(5,5) reflection squares and chirality intertwining.
  2. SageMath  — Lie algebra D_5 = so(5,5) (dim 45 = 10 + 25 + 10), parabolic 5-grading,
                 and commuting sl(2)_iso (+) sl(2)_pair root subalgebras.
  3. GAP       — SimpleLieAlgebra("D", 5, Rationals), Chevalley basis brackets for
                 the commuting A_1 (isospin) x A_1 (pairing quasispin) subalgebra.
  4. Macaulay2 — Groebner basis reduction in QQ[Np, Nn]/(Np^2 - Np, Nn^2 - Nn)
                 certifying the 4-projector orthogonal decomposition and Cartan eigenvalues.
  5. Singular  — Polynomial ideal membership (reduce / std) certifying the spectral
                 idempotent and Casimir identities of tau_3 = Np - Nn and 2*K_0 = Np + Nn - 1.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
import sympy as sp
from sympy.physics.quantum import TensorProduct


def run_sympy_verification() -> dict:
    """1. SymPy 32x32 exact matrix verification on Cl(5,5) (`MatStage 5`)."""
    I2 = sp.eye(2)
    # Single-mode CAR creation e = [[0, 1], [0, 0]], annihilation f = [[0, 0], [1, 0]], parity Z = [[1, 0], [0, -1]]
    e1 = sp.Matrix([[0, 1], [0, 0]])
    f1 = sp.Matrix([[0, 0], [1, 0]])
    z1 = sp.Matrix([[1, 0], [0, -1]])

    def kron_list(mats):
        out = mats[0]
        for m in mats[1:]:
            out = TensorProduct(out, m)
        return out

    # 5 Witt creation/annihilation operators in M_32(Q)
    e = []
    f = []
    for a in range(5):
        factors_e = [z1 if k < a else (e1 if k == a else I2) for k in range(5)]
        factors_f = [z1 if k < a else (f1 if k == a else I2) for k in range(5)]
        e.append(kron_list(factors_e))
        f.append(kron_list(factors_f))

    I32 = sp.eye(32)
    Z32 = sp.zeros(32, 32)
    gamma_chiral = kron_list([z1, z1, z1, z1, z1])

    # Check Pin_+(5,5) and Pin_-(5,5) generators
    for a in range(5):
        gp = e[a] + f[a]
        gm = e[a] - f[a]
        assert gp * gp == I32, f"Gamma_+({a})^2 != I32"
        assert gm * gm == -I32, f"Gamma_-({a})^2 != -I32"
        assert gamma_chiral * e[a] + e[a] * gamma_chiral == Z32
        assert gamma_chiral * f[a] + f[a] * gamma_chiral == Z32

    # Number projectors N_a = e_a f_a and Cartan generators H_a = N_a - 1/2 I
    N = [e[a] * f[a] for a in range(5)]
    H = [N[a] - sp.Rational(1, 2) * I32 for a in range(5)]
    N_tot = sum(H, Z32)

    def bracket(X, Y):
        return X * Y - Y * X

    # Choose modes p = 3, n = 4 as the nucleon isospin doublet, modes {0, 1, 2} as spatial/orbital
    p, n = 3, 4
    # Grade-0 Isospin sl(2)_iso generators:
    tau_plus = e[p] * f[n]
    tau_minus = e[n] * f[p]
    tau_3 = H[p] - H[n]  # = N_p - N_n

    # Grade-+-2 Pairing Quasispin sl(2)_pair generators:
    K_plus = e[p] * e[n]
    K_minus = f[n] * f[p]
    two_K_0 = H[p] + H[n]  # = N_p + N_n - I32

    # 1. Verify 5-grading eigenvalues under ad(N_tot):
    assert bracket(N_tot, tau_plus) == Z32
    assert bracket(N_tot, tau_minus) == Z32
    assert bracket(N_tot, tau_3) == Z32
    assert bracket(N_tot, K_plus) == 2 * K_plus
    assert bracket(N_tot, K_minus) == -2 * K_minus
    assert bracket(N_tot, two_K_0) == Z32

    # 2. Verify sl(2)_iso and sl(2)_pair commutation relations:
    assert bracket(tau_3, tau_plus) == 2 * tau_plus
    assert bracket(tau_3, tau_minus) == -2 * tau_minus
    assert bracket(tau_plus, tau_minus) == tau_3

    assert bracket(two_K_0, K_plus) == 2 * K_plus
    assert bracket(two_K_0, K_minus) == -2 * K_minus
    assert bracket(K_plus, K_minus) == two_K_0

    # 3. Verify mutual commutation [sl(2)_iso, sl(2)_pair] = 0:
    for X in (tau_plus, tau_minus, tau_3):
        for Y in (K_plus, K_minus, two_K_0):
            assert bracket(X, Y) == Z32

    # 4. Verify 4-sector orthogonal Peirce projector decomposition:
    Pi_plus = N[p] * (I32 - N[n])
    Pi_minus = (I32 - N[p]) * N[n]
    Pi_pair_plus = N[p] * N[n]
    Pi_pair_minus = (I32 - N[p]) * (I32 - N[n])

    projs = [Pi_plus, Pi_minus, Pi_pair_plus, Pi_pair_minus]
    assert sum(projs, Z32) == I32
    for i, P in enumerate(projs):
        assert P * P == P
        for j, Q in enumerate(projs):
            if i != j:
                assert P * Q == Z32

    # 5. Verify Cartan-Projector Spectral Decomposition and Eigenvalue Laws:
    assert tau_3 == Pi_plus - Pi_minus
    assert two_K_0 == Pi_pair_plus - Pi_pair_minus
    assert tau_3 * Pi_plus == Pi_plus
    assert tau_3 * Pi_minus == -Pi_minus
    assert tau_3 * Pi_pair_plus == Z32
    assert tau_3 * Pi_pair_minus == Z32
    assert two_K_0 * Pi_pair_plus == Pi_pair_plus
    assert two_K_0 * Pi_pair_minus == -Pi_pair_minus
    assert two_K_0 * Pi_plus == Z32
    assert two_K_0 * Pi_minus == Z32

    # 6. Verify Peirce Ladder Factorizations & Reflexive Identities:
    assert tau_plus * tau_minus == Pi_plus
    assert tau_minus * tau_plus == Pi_minus
    assert tau_plus * tau_minus * tau_plus == tau_plus
    assert tau_minus * tau_plus * tau_minus == tau_minus
    assert K_plus * K_minus == Pi_pair_plus
    assert K_minus * K_plus == Pi_pair_minus
    assert K_plus * K_minus * K_plus == K_plus
    assert K_minus * K_plus * K_minus == K_minus

    # 7. Verify Associative Cross-Sector Annihilation & Full Quadratic Casimir Partition:
    Delta_iso = Pi_plus + Pi_minus
    Delta_pair = Pi_pair_plus + Pi_pair_minus
    assert Delta_iso + Delta_pair == I32
    assert Delta_iso * Delta_pair == Z32
    assert Delta_pair * Delta_iso == Z32
    for X in (tau_plus, tau_minus, tau_3):
        for Y in (K_plus, K_minus, two_K_0):
            assert X * Y == Z32
            assert Y * X == Z32

    C2_iso = tau_3 * tau_3 + 2 * (tau_plus * tau_minus + tau_minus * tau_plus)
    C2_pair = two_K_0 * two_K_0 + 2 * (K_plus * K_minus + K_minus * K_plus)
    assert C2_iso == 3 * Delta_iso
    assert C2_pair == 3 * Delta_pair
    assert C2_iso + C2_pair == 3 * I32

    # 8. Verify Pin_+(5,5) & Pin_-(5,5) Majorana Particle-Hole Duality and Spin-Connection Factorization:
    for a in range(5):
        gp_a = e[a] + f[a]
        gm_a = e[a] - f[a]
        assert gm_a * gp_a == 2 * H[a]
        assert gp_a * gm_a == -2 * H[a]

    Gamma_n = e[n] + f[n]
    Gamma_minus_n = e[n] - f[n]
    assert Gamma_n * Gamma_n == I32
    assert Gamma_minus_n * Gamma_minus_n == -I32
    assert Gamma_n * tau_plus * Gamma_n == -K_plus
    assert Gamma_n * tau_minus * Gamma_n == -K_minus
    assert Gamma_n * tau_3 * Gamma_n == two_K_0
    assert Gamma_n * Pi_plus * Gamma_n == Pi_pair_plus
    assert Gamma_n * Pi_minus * Gamma_n == Pi_pair_minus
    assert Gamma_n * Delta_iso * Gamma_n == Delta_pair
    assert Gamma_minus_n * tau_plus * (-Gamma_minus_n) == K_plus
    assert Gamma_minus_n * tau_minus * (-Gamma_minus_n) == K_minus
    assert Gamma_minus_n * tau_3 * Gamma_minus_n == -two_K_0

    # 8b. Verify Spin-Connection Carrier Parity (2 H_p)(2 H_n) = Delta_pair - Delta_iso
    #     and Global SO(4)_{pn} Dirac & Kahler Factorization:
    two_Hp = 2 * N[p] - I32
    two_Hn = 2 * N[n] - I32
    assert tau_3 + two_K_0 == two_Hp
    assert two_K_0 - tau_3 == two_Hn
    assert two_Hp * two_Hn == Delta_pair - Delta_iso
    Q_tot = (tau_plus + tau_minus) + (K_plus + K_minus)
    J_tot = (tau_plus - tau_minus) + (K_plus - K_minus)
    assert Q_tot * Q_tot == I32
    assert J_tot * J_tot == -I32
    assert J_tot * Q_tot == two_Hp
    Gamma_color = (2 * H[0]) * (2 * H[1]) * (2 * H[2])
    Gamma_10D = (2 * H[0]) * (2 * H[1]) * (2 * H[2]) * (2 * H[3]) * (2 * H[4])
    assert Gamma_10D == Gamma_color * (Delta_pair - Delta_iso)
    V = [I32 - N[a] for a in range(3)]
    Pi_baryon = N[0] * N[1] * N[2]
    Pi_vac = V[0] * V[1] * V[2]
    Pi_quark = N[0] * V[1] * V[2] + V[0] * N[1] * V[2] + V[0] * V[1] * N[2]
    Pi_diquark = V[0] * N[1] * N[2] + N[0] * V[1] * N[2] + N[0] * N[1] * V[2]
    Pi_pos_company = Pi_baryon + Pi_quark
    Pi_neg_company = Pi_vac + Pi_diquark
    assert Pi_baryon + Pi_quark + Pi_diquark + Pi_vac == I32
    assert Gamma_color == Pi_pos_company - Pi_neg_company
    assert Gamma_10D == (Pi_pos_company - Pi_neg_company) * (Delta_pair - Delta_iso)
    Pi_16_plus = Pi_pos_company * Delta_pair + Pi_neg_company * Delta_iso
    Pi_16_minus = Pi_pos_company * Delta_iso + Pi_neg_company * Delta_pair
    assert Pi_16_plus + Pi_16_minus == I32
    assert Gamma_10D == Pi_16_plus - Pi_16_minus
    assert Pi_16_minus == (
        Pi_baryon * Delta_iso + Pi_quark * Delta_iso + Pi_vac * Delta_pair + Pi_diquark * Delta_pair
    )
    assert int(Pi_16_plus.trace()) == 16
    assert int(Pi_16_minus.trace()) == 16
    T3_color = N[0] - N[1]
    three_Y_color = N[0] + N[1] - 2 * N[2]
    N_color = N[0] + N[1] + N[2]
    assert 2 * N_color + three_Y_color + 3 * T3_color == 6 * N[0]
    assert 2 * N_color + three_Y_color - 3 * T3_color == 6 * N[1]
    assert N_color - three_Y_color == 3 * N[2]
    assert 3 * (T3_color * T3_color) + (three_Y_color * three_Y_color) == 4 * (Pi_quark + Pi_diquark)
    assert T3_color * Pi_baryon == Z32
    assert three_Y_color * Pi_baryon == Z32
    assert T3_color * Pi_vac == Z32
    assert three_Y_color * Pi_vac == Z32
    assert N_color == Pi_quark + 2 * Pi_diquark + 3 * Pi_baryon
    six_Q_EM = N_color + 3 * (Pi_plus - Pi_minus)
    assert six_Q_EM == (
        4 * (Pi_quark * Pi_plus)
        - 2 * (Pi_quark * Pi_minus)
        + 1 * (Pi_quark * Delta_pair)
        + 5 * (Pi_diquark * Pi_plus)
        - 1 * (Pi_diquark * Pi_minus)
        + 2 * (Pi_diquark * Delta_pair)
        + 6 * (Pi_baryon * Pi_plus)
        + 3 * (Pi_baryon * Delta_pair)
        + 3 * (Pi_vac * Pi_plus)
        - 3 * (Pi_vac * Pi_minus)
    )

    # 9. Verify Erlangen 2.0 Cartan-Peirce Emergence & Gauge Invariance on SplitQuaternion:
    x00, x01, x10, x11, y00, y01, y10, y11, u = sp.symbols(
        "x00 x01 x10 x11 y00 y01 y10 y11 u"
    )
    P_plus = sp.Matrix([[1, 0], [0, 0]])
    P_minus = sp.Matrix([[0, 0], [0, 1]])
    seed_d = sp.Matrix([[0, 1], [0, 0]])
    seed_B = sp.Matrix([[0, 0], [1, 0]])
    vel_Q = seed_d + seed_B
    wheel_J = seed_d - seed_B
    pol_Gamma = P_plus - P_minus
    assert wheel_J * vel_Q == pol_Gamma
    assert vel_Q * wheel_J == -pol_Gamma

    X = sp.Matrix([[x00, x01], [x10, x11]])
    Y = sp.Matrix([[y00, y01], [y10, y11]])
    omega_X = P_plus * X * P_plus + P_minus * X * P_minus
    frame_X = P_plus * X * P_minus + P_minus * X * P_plus
    frame_Y = P_plus * Y * P_minus + P_minus * Y * P_plus
    assert omega_X + frame_X == X
    assert pol_Gamma * omega_X * pol_Gamma == omega_X
    assert pol_Gamma * frame_X * pol_Gamma == -frame_X
    g_XY = x01 * y10 + x10 * y01
    R_XY = x01 * y10 - x10 * y01
    assert sp.simplify(frame_X * frame_Y + frame_Y * frame_X - g_XY * I2) == sp.zeros(2, 2)
    assert sp.simplify(frame_X * frame_Y - frame_Y * frame_X - R_XY * pol_Gamma) == sp.zeros(2, 2)
    torsion = omega_X * frame_Y - frame_Y * omega_X
    assert P_plus * torsion * P_plus + P_minus * torsion * P_minus == sp.zeros(2, 2)
    K_L = u * P_plus + (1 / u) * P_minus
    K_R = (1 / u) * P_plus + u * P_minus
    X_boost = sp.simplify(K_L * X * K_R)
    Y_boost = sp.simplify(K_L * Y * K_R)
    assert sp.simplify((X_boost[0, 1] * Y_boost[1, 0] + X_boost[1, 0] * Y_boost[0, 1]) - g_XY) == 0
    assert sp.simplify((X_boost[0, 1] * Y_boost[1, 0] - X_boost[1, 0] * Y_boost[0, 1]) - R_XY) == 0

    # 10. Verify 3-Color Zorn Vector-Matrix Channel Embeddings & Cross-Channel Diquark/Baryon Laws:
    def zvm_mul(m1, m2):
        a1, u1, v1, b1 = m1
        a2, u2, v2, b2 = m2
        return (
            a1 * a2 + u1.dot(v2),
            a1 * u2 + b2 * u1 - v1.cross(v2),
            a2 * v1 + b1 * v2 + u1.cross(u2),
            b1 * b2 + v1.dot(u2),
        )

    def color_embed(k, M):
        ek = sp.Matrix([1 if i == k else 0 for i in range(3)])
        return (M[0, 0], M[0, 1] * ek, M[1, 0] * ek, M[1, 1])

    for k in range(3):
        lhs = color_embed(k, X * Y)
        rhs = zvm_mul(color_embed(k, X), color_embed(k, Y))
        assert sp.simplify(lhs[0] - rhs[0]) == 0
        assert sp.simplify(lhs[1] - rhs[1]) == sp.zeros(3, 1)
        assert sp.simplify(lhs[2] - rhs[2]) == sp.zeros(3, 1)
        assert sp.simplify(lhs[3] - rhs[3]) == 0

    assert zvm_mul(color_embed(0, seed_d), color_embed(1, seed_d)) == color_embed(2, seed_B)
    assert zvm_mul(
        zvm_mul(color_embed(0, seed_d), color_embed(1, seed_d)),
        color_embed(2, seed_d),
    ) == color_embed(2, P_minus)
    assert zvm_mul(
        color_embed(0, seed_d),
        zvm_mul(color_embed(1, seed_d), color_embed(2, seed_d)),
    ) == color_embed(0, P_plus)

    # 11. Verify Zorn 6D Frame Anticommutator Metric & Cross-Channel Color Torsion Trichotomy:
    def zvm_add(m1, m2):
        return (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2], m1[3] + m2[3])

    def zvm_sub(m1, m2):
        return (m1[0] - m2[0], m1[1] - m2[1], m1[2] - m2[2], m1[3] - m2[3])

    def zvm_frame(m):
        return (0, m[1], m[2], 0)

    e_X0 = zvm_frame(color_embed(0, X))
    e_Y1 = zvm_frame(color_embed(1, Y))
    comm_01 = zvm_sub(zvm_mul(e_X0, e_Y1), zvm_mul(e_Y1, e_X0))
    expected_torsion = color_embed(
        2, sp.Matrix([[0, -2 * x10 * y10], [2 * x01 * y01, 0]])
    )
    assert sp.simplify(comm_01[0] - expected_torsion[0]) == 0
    assert sp.simplify(comm_01[1] - expected_torsion[1]) == sp.zeros(3, 1)
    assert sp.simplify(comm_01[2] - expected_torsion[2]) == sp.zeros(3, 1)
    assert sp.simplify(comm_01[3] - expected_torsion[3]) == 0

    # 12. Verify the Nambu-Bianchi Frame Jacobiator Law on 3 Colored Frame Elements:
    z01, z10 = sp.symbols("z01 z10")
    Z_mat = sp.Matrix([[0, z01], [z10, 0]])
    e_Z2 = zvm_frame(color_embed(2, Z_mat))

    def zvm_comm(m1, m2):
        return zvm_sub(zvm_mul(m1, m2), zvm_mul(m2, m1))

    jac_012 = zvm_add(
        zvm_add(
            zvm_comm(e_X0, zvm_comm(e_Y1, e_Z2)),
            zvm_comm(e_Y1, zvm_comm(e_Z2, e_X0)),
        ),
        zvm_comm(e_Z2, zvm_comm(e_X0, e_Y1)),
    )
    nambu_sum = x01 * y01 * z01 + x10 * y10 * z10
    assert sp.simplify(jac_012[0] - 6 * nambu_sum) == 0
    assert sp.simplify(jac_012[3] - (-6 * nambu_sum)) == 0

    # 13. Verify Tamm-Dancoff Singlet-Triplet Binet-Cauchy-Zorn Norm Conservation & Nambu Extraction:
    def zvm_norm(m):
        return m[0] * m[3] - m[1].dot(m[2])

    def zvm_singlet(m):
        return (m[0], sp.zeros(3, 1), sp.zeros(3, 1), m[3])

    prod_01 = zvm_mul(e_X0, e_Y1)
    assert sp.simplify(
        (zvm_norm(zvm_singlet(prod_01)) + zvm_norm(zvm_frame(prod_01)))
        - zvm_norm(e_X0) * zvm_norm(e_Y1)
    ) == 0
    td_nambu = zvm_singlet(zvm_mul(zvm_frame(prod_01), e_Z2))
    assert sp.simplify(td_nambu[0] - (-x10 * y10 * z10)) == 0
    assert sp.simplify(td_nambu[3] - (x01 * y01 * z01)) == 0

    # 14. Verify SplitQuaternion 1 (+) 3 Tamm-Dancoff & Three-Triplet Nambu Singlet Closure:
    T_X = 2 * X - X.trace() * I2
    T_Y = 2 * Y - Y.trace() * I2
    T_Z = 2 * Z_mat - Z_mat.trace() * I2
    C_XY = T_X * T_Y - T_Y * T_X
    assert sp.simplify((T_X * T_Y + T_Y * T_X) - (T_X * T_Y).trace() * I2) == sp.zeros(2, 2)
    assert sp.simplify(C_XY.trace()) == 0
    assert sp.simplify((C_XY * T_Z + T_Z * C_XY) - (C_XY * T_Z).trace() * I2) == sp.zeros(2, 2)

    # 15. Verify Tomita Modular Conjugation & KMS u^(+-6) Nambu Volume Casimir Invariance:
    def zvm_tomita(m):
        return (m[0], m[2], m[1], m[3])

    def zvm_swap(m):
        return (m[3], -m[2], -m[1], m[0])

    lhs_tomita = zvm_tomita(zvm_mul(e_X0, e_Y1))
    rhs_tomita = zvm_mul(zvm_tomita(e_Y1), zvm_tomita(e_X0))
    assert sp.simplify(lhs_tomita[0] - rhs_tomita[0]) == 0
    assert sp.simplify(lhs_tomita[1] - rhs_tomita[1]) == sp.zeros(3, 1)
    assert sp.simplify(lhs_tomita[2] - rhs_tomita[2]) == sp.zeros(3, 1)
    assert sp.simplify(lhs_tomita[3] - rhs_tomita[3]) == 0

    lhs_swap = zvm_swap(zvm_mul(e_X0, e_Y1))
    rhs_swap = zvm_mul(zvm_swap(e_X0), zvm_swap(e_Y1))
    assert sp.simplify(lhs_swap[0] - rhs_swap[0]) == 0
    assert sp.simplify(lhs_swap[1] - rhs_swap[1]) == sp.zeros(3, 1)
    assert sp.simplify(lhs_swap[2] - rhs_swap[2]) == sp.zeros(3, 1)
    assert sp.simplify(lhs_swap[3] - rhs_swap[3]) == 0

    # 16. Verify Universal Malcev-Zorn S_3 Identity J(X,Y,Z) == -6 * [X,Y,Z], Associator-Nambu,
    #     and Tomita +1 Ternary Homomorphism:
    assoc_012 = zvm_sub(zvm_mul(zvm_mul(e_X0, e_Y1), e_Z2), zvm_mul(e_X0, zvm_mul(e_Y1, e_Z2)))
    assert sp.simplify(jac_012[0] - (-6 * assoc_012[0])) == 0
    assert sp.simplify(jac_012[1] - (-6 * assoc_012[1])) == sp.zeros(3, 1)
    assert sp.simplify(jac_012[2] - (-6 * assoc_012[2])) == sp.zeros(3, 1)
    assert sp.simplify(jac_012[3] - (-6 * assoc_012[3])) == 0
    assert sp.simplify(assoc_012[0] - (-nambu_sum)) == 0
    assert sp.simplify(assoc_012[3] - nambu_sum) == 0
    t_X0, t_Y1, t_Z2 = zvm_tomita(e_X0), zvm_tomita(e_Y1), zvm_tomita(e_Z2)
    t_assoc = zvm_tomita(assoc_012)
    assoc_t = zvm_sub(zvm_mul(zvm_mul(t_X0, t_Y1), t_Z2), zvm_mul(t_X0, zvm_mul(t_Y1, t_Z2)))
    assert sp.simplify(t_assoc[0] - assoc_t[0]) == 0
    assert sp.simplify(t_assoc[1] - assoc_t[1]) == sp.zeros(3, 1)
    assert sp.simplify(t_assoc[2] - assoc_t[2]) == sp.zeros(3, 1)
    assert sp.simplify(t_assoc[3] - assoc_t[3]) == 0

    # 17. Verify Chiral Maxwell / GEM (1 (+) 3) Four-Potential & Tomita Stress-Energy-Poynting Laws:
    d0, dx, dy, dz, phi, ax, ay, az = sp.symbols("d0 dx dy dz phi ax ay az")
    d_vec = sp.Matrix([dx, dy, dz])
    a_vec = sp.Matrix([ax, ay, az])
    D_pot = (d0, d_vec, -d_vec, -d0)
    A_pot = (phi, a_vec, -a_vec, -phi)
    DA_prod = zvm_mul(D_pot, A_pot)
    DD_prod = zvm_mul(D_pot, D_pot)
    E_vec = d0 * a_vec - phi * d_vec
    B_vec = d_vec.cross(a_vec)
    G_lorenz = d0 * phi - d_vec.dot(a_vec)
    assert sp.simplify(DA_prod[0] - G_lorenz) == 0
    assert sp.simplify(DA_prod[3] - G_lorenz) == 0
    assert sp.simplify(DA_prod[1] - (E_vec - B_vec)) == sp.zeros(3, 1)
    assert sp.simplify(DA_prod[2] - (E_vec + B_vec)) == sp.zeros(3, 1)
    assert sp.simplify(DD_prod[1]) == sp.zeros(3, 1)
    assert sp.simplify(DD_prod[2]) == sp.zeros(3, 1)

    F_gem = (0, E_vec - B_vec, E_vec + B_vec, 0)
    assert sp.simplify(zvm_norm(F_gem) - (B_vec.dot(B_vec) - E_vec.dot(E_vec))) == 0
    T_gem = zvm_mul(F_gem, zvm_tomita(F_gem))
    E2_plus_B2 = E_vec.dot(E_vec) + B_vec.dot(B_vec)
    EdotB = E_vec.dot(B_vec)
    ExB = E_vec.cross(B_vec)
    assert sp.simplify(T_gem[0] - (E2_plus_B2 - 2 * EdotB)) == 0
    assert sp.simplify(T_gem[3] - (E2_plus_B2 + 2 * EdotB)) == 0
    assert sp.simplify(T_gem[1] - 2 * ExB) == sp.zeros(3, 1)
    assert sp.simplify(T_gem[2] - 2 * ExB) == sp.zeros(3, 1)
    assert (
        sp.simplify(
            E2_plus_B2**2
            - 4 * EdotB**2
            - 4 * ExB.dot(ExB)
            - (E_vec.dot(E_vec) - B_vec.dot(B_vec)) ** 2
        )
        == 0
    )

    # 18. Verify Non-Abelian Gluon Self-Interaction & Vectorlike vs. Chiral Bianchi Anomaly:
    DA_comm = zvm_comm(D_pot, A_pot)
    assert sp.simplify(DA_comm[0]) == 0
    assert sp.simplify(DA_comm[3]) == 0
    assert sp.simplify(DA_comm[1] - 2 * (E_vec - B_vec)) == sp.zeros(3, 1)
    assert sp.simplify(DA_comm[2] - 2 * (E_vec + B_vec)) == sp.zeros(3, 1)

    phi3, bx, by, bz = sp.symbols("phi3 bx by bz")
    b_vec = sp.Matrix([bx, by, bz])
    B_pot = (phi3, b_vec, -b_vec, -phi3)
    jac_vec = zvm_add(
        zvm_add(
            zvm_comm(D_pot, zvm_comm(A_pot, B_pot)),
            zvm_comm(A_pot, zvm_comm(B_pot, D_pot)),
        ),
        zvm_comm(B_pot, zvm_comm(D_pot, A_pot)),
    )
    assert sp.simplify(jac_vec[0]) == 0
    assert sp.simplify(jac_vec[3]) == 0

    C1 = (d0, d_vec, sp.zeros(3, 1), -d0)
    C2 = (phi, a_vec, sp.zeros(3, 1), -phi)
    C3 = (phi3, b_vec, sp.zeros(3, 1), -phi3)
    jac_chiral = zvm_add(
        zvm_add(
            zvm_comm(C1, zvm_comm(C2, C3)),
            zvm_comm(C2, zvm_comm(C3, C1)),
        ),
        zvm_comm(C3, zvm_comm(C1, C2)),
    )
    det_dab = d_vec.dot(a_vec.cross(b_vec))
    assert sp.simplify(jac_chiral[0] - 6 * det_dab) == 0
    assert sp.simplify(jac_chiral[3] - (-6 * det_dab)) == 0

    # 19. Verify Machian Collinear Degeneracy & Sciama Relational Inertial Induction:
    c_scale, Phi_bg = sp.symbols("c_scale Phi_bg")
    assert sp.simplify(a_vec.cross(c_scale * a_vec)) == sp.zeros(3, 1)
    assert sp.simplify(d_vec.dot(a_vec.cross(c_scale * a_vec))) == 0
    A_scaled = (c_scale * phi, c_scale * a_vec, -c_scale * a_vec, -c_scale * phi)
    comm_comoving = zvm_comm(A_pot, A_scaled)
    assert sp.simplify(comm_comoving[0]) == 0
    assert sp.simplify(comm_comoving[1]) == sp.zeros(3, 1)
    assert sp.simplify(comm_comoving[2]) == sp.zeros(3, 1)
    assert sp.simplify(comm_comoving[3]) == 0
    P_bg = (Phi_bg, sp.zeros(3, 1), sp.zeros(3, 1), -Phi_bg)
    sciama_prod = zvm_frame(zvm_mul(D_pot, P_bg))
    assert sp.simplify(sciama_prod[1] - (-Phi_bg * d_vec)) == sp.zeros(3, 1)
    assert sp.simplify(sciama_prod[2] - (-Phi_bg * d_vec)) == sp.zeros(3, 1)

    # 20. Nucleus-vs-Periphery Nambu Anomaly & Tomita-GEM Frame-Dragging Associator
    # (`zornAssociator_nucleus_zero_vs_periphery_torsion`,
    #  `zornAssociator_charge_mul_frame_eq_nambu`,
    #  `zornFieldStrength_tomita_stress_and_frame_dragging`)
    def zvm_assoc(m1, m2, m3):
        return zvm_sub(zvm_mul(zvm_mul(m1, m2), m3), zvm_mul(m1, zvm_mul(m2, m3)))

    h_sym, h_plus, h_minus = sp.symbols("h h_plus h_minus", commutative=True)
    H_nuc = (h_sym, sp.zeros(3, 1), sp.zeros(3, 1), h_sym)
    H_per = (h_plus, sp.zeros(3, 1), sp.zeros(3, 1), h_minus)
    assoc_nuc = zvm_assoc(D_pot, A_pot, H_nuc)
    assert sp.simplify(assoc_nuc[0]) == 0
    assert sp.simplify(assoc_nuc[1]) == sp.zeros(3, 1)
    assert sp.simplify(assoc_nuc[2]) == sp.zeros(3, 1)
    assert sp.simplify(assoc_nuc[3]) == 0
    xv, xw = d_vec, a_vec
    yv, yw = a_vec, b_vec
    zv, zw = b_vec, E_vec
    eX = (0, xv, xw, 0)
    eY = (0, yv, yw, 0)
    eZ = (0, zv, zw, 0)
    assoc_per = zvm_assoc(eX, eY, H_per)
    assert sp.simplify(assoc_per[0]) == 0
    assert sp.simplify(assoc_per[1] - (h_plus - h_minus) * xw.cross(yw)) == sp.zeros(3, 1)
    assert sp.simplify(assoc_per[2] - (h_plus - h_minus) * xv.cross(yv)) == sp.zeros(3, 1)
    assert sp.simplify(assoc_per[3]) == 0
    nambu_per = zvm_singlet(zvm_mul(assoc_per, eZ))
    assert sp.simplify(nambu_per[0] - (h_plus - h_minus) * xw.dot(yw.cross(zw))) == 0
    assert sp.simplify(nambu_per[3] - (h_plus - h_minus) * xv.dot(yv.cross(zv))) == 0
    F_eb = (0, E_vec + B_vec, -E_vec + B_vec, 0)
    assoc_frame_drag = zvm_assoc(F_eb, zvm_tomita(F_eb), H_per)
    assert sp.simplify(assoc_frame_drag[0]) == 0
    assert sp.simplify(assoc_frame_drag[1] - (-2 * (h_plus - h_minus) * ExB)) == sp.zeros(3, 1)
    assert sp.simplify(assoc_frame_drag[2] - (2 * (h_plus - h_minus) * ExB)) == sp.zeros(3, 1)
    assert sp.simplify(assoc_frame_drag[3]) == 0

    # 21. Sciama-Lense-Thirring Transverse Frame Dragging, Scalar Readouts (§IX),
    #     Supertrace-Curvature Bridge, & Coplanar Nambu Degeneracy
    # (`zorn_sciama_lense_thirring_transverse_frame_dragging`,
    #  `zorn_scalar_readout_associator_and_supertrace_curvature`,
    #  `zorn_machian_two_body_collinear_degeneracy`,
    #  `zorn_machian_three_body_coplanar_degeneracy`)
    E_g = -Phi_bg * a_vec
    B_g = a_vec.cross(b_vec)
    assert sp.simplify(E_g.dot(B_g)) == 0
    F_slt = (0, E_g - B_g, E_g + B_g, 0)
    T_slt = zvm_singlet(zvm_mul(F_slt, zvm_tomita(F_slt)))
    assert sp.simplify(T_slt[0] - (Phi_bg**2 * a_vec.dot(a_vec) + B_g.dot(B_g))) == 0
    assert sp.simplify(T_slt[3] - (Phi_bg**2 * a_vec.dot(a_vec) + B_g.dot(B_g))) == 0
    helmholtz_flux = E_g.cross(B_g)
    assert (
        sp.simplify(
            helmholtz_flux - Phi_bg * (a_vec.dot(a_vec) * b_vec - a_vec.dot(b_vec) * a_vec)
        )
        == sp.zeros(3, 1)
    )
    assert sp.simplify(a_vec.dot(helmholtz_flux)) == 0

    def zvm_str(m):
        return m[0] - m[3]

    def zvm_curv(m1, m2):
        return m1[1].dot(m2[2]) - m1[2].dot(m2[1])

    assert sp.simplify(zvm_str(zvm_comm(D_pot, A_pot)) - 2 * zvm_curv(D_pot, A_pot)) == 0
    assoc_eXYZ = zvm_assoc(eX, eY, eZ)
    nambu_eXYZ = xv.dot(yv.cross(zv)) + xw.dot(yw.cross(zw))
    assert sp.simplify(assoc_eXYZ[0] - (-nambu_eXYZ)) == 0
    assert sp.simplify(zvm_str(assoc_eXYZ) - (-2 * nambu_eXYZ)) == 0
    chiral_1 = (0, d_vec, sp.zeros(3, 1), 0)
    chiral_2 = (0, a_vec, sp.zeros(3, 1), 0)
    chiral_3 = (0, b_vec, sp.zeros(3, 1), 0)
    assert sp.simplify(zvm_assoc(chiral_1, chiral_2, chiral_3)[0] - (-d_vec.dot(a_vec.cross(b_vec)))) == 0
    c1_sym, c2_sym = sp.symbols("c1 c2", commutative=True)
    chiral_coplanar = (0, c1_sym * d_vec + c2_sym * a_vec, sp.zeros(3, 1), 0)
    assoc_coplanar = zvm_assoc(chiral_1, chiral_2, chiral_coplanar)
    assert sp.simplify(assoc_coplanar[0]) == 0
    assert sp.simplify(assoc_coplanar[1]) == sp.zeros(3, 1)
    assert sp.simplify(assoc_coplanar[2]) == sp.zeros(3, 1)
    assert sp.simplify(assoc_coplanar[3]) == 0

    return {
        "engine": "SymPy",
        "status": "PASSED",
        "carrier": "M_32(Q) = Cl(5,5) (MatStage 5), SplitQuaternion, ZornVectorMatrix",
        "bi_peirce_cross_annihilation": True,
        "casimir_partition": "C2_iso + C2_pair == 3 * I32",
        "pin_plus_minus_duality": True,
        "erlangen_2_0_metric_curvature_gauge_invariance": True,
        "zorn_3_color_diquark_baryon_fusion": True,
        "traces": {
            "tr(Pi_plus)": int(Pi_plus.trace()),
            "tr(Pi_minus)": int(Pi_minus.trace()),
            "tr(Pi_pair_plus)": int(Pi_pair_plus.trace()),
            "tr(Pi_pair_minus)": int(Pi_pair_minus.trace()),
        },
    }


def run_sage_verification() -> dict:
    """2. SageMath verification of D_5 = so(5,5) 5-grading, Erlangen 2.0, and 3-color Zorn algebra."""
    from sage.all import QQ, Matrix, RootSystem, vector

    R = RootSystem(["D", 5])
    ambient = R.ambient_space()
    roots = list(ambient.roots())
    # 5-grading weight is the sum of all 5 ambient coordinates (1,1,1,1,1)
    grade_counts = {-2: 0, -1: 0, 0: 0, 1: 0, 2: 0}
    for alpha in roots:
        v = alpha.to_vector()
        g = int(sum(v))
        grade_counts[g] += 1
    # Add 5 Cartan generators to grade 0
    grade_counts[0] += 5
    assert grade_counts[-2] == 10
    assert grade_counts[0] == 25
    assert grade_counts[2] == 10
    assert sum(grade_counts.values()) == 45

    # Isospin root alpha_iso = e_3 - e_4 (grade 0) and Pairing root alpha_pair = e_3 + e_4 (grade +2)
    e = ambient.basis()
    alpha_iso = e[3] - e[4]
    alpha_pair = e[3] + e[4]
    assert alpha_iso in roots
    assert alpha_pair in roots
    assert int(sum(alpha_iso.to_vector())) == 0
    assert int(sum(alpha_pair.to_vector())) == 2
    assert int(alpha_iso.to_vector().dot_product(alpha_pair.to_vector())) == 0

    # Verify Erlangen 2.0 Pin_- * Pin_+ = polarizationGamma in MatrixSpace(QQ, 2, 2):
    d = Matrix(QQ, [[0, 1], [0, 0]])
    B = Matrix(QQ, [[0, 0], [1, 0]])
    Q = d + B
    J = d - B
    Gamma = Matrix(QQ, [[1, 0], [0, -1]])
    assert J * Q == Gamma and Q * J == -Gamma

    # Verify 3-color Zorn cross-product seed fusion in QQ^3:
    e0 = vector(QQ, [1, 0, 0])
    e1 = vector(QQ, [0, 1, 0])
    e2 = vector(QQ, [0, 0, 1])
    assert e0.cross_product(e1) == e2

    return {
        "engine": "SageMath",
        "status": "PASSED",
        "grade_counts": {str(k): v for k, v in grade_counts.items()},
        "dim_so55": sum(grade_counts.values()),
        "iso_dot_pair": 0,
        "erlangen_and_zorn_verified": True,
    }


def run_gap_verification() -> dict:
    """3. GAP verification of SimpleLieAlgebra("D", 5, Rationals) and SplitQuaternion Erlangen 2.0."""
    gap_bin = "/home/goutev/miniforge3/envs/sage/bin/gap"
    code = """
L := SimpleLieAlgebra("D", 5, Rationals);;
dimL := Dimension(L);;
chevalley := ChevalleyBasis(L);;
pos := chevalley[1];;
neg := chevalley[2];;
cartan := chevalley[3];;
e_iso := pos[4];; f_iso := neg[4];; h_iso := cartan[4];;
e_pair := pos[5];; f_pair := neg[5];; h_pair := cartan[5];;
d := [[0, 1], [0, 0]];; B := [[0, 0], [1, 0]];;
Q := d + B;; J := d - B;; polGamma := [[1, 0], [0, -1]];;
ok := (dimL = 45)
  and (e_iso * f_iso = h_iso)
  and (e_pair * f_pair = h_pair)
  and (IsZero(e_iso * e_pair))
  and (IsZero(e_iso * f_pair))
  and (IsZero(h_iso * e_pair))
  and (IsZero(h_pair * e_iso))
  and (J * Q = polGamma)
  and (Q * J = -polGamma);;
if ok then
  Print("GAP_D5_OK:", dimL, "\\n");
else
  Print("GAP_D5_FAIL\\n");
fi;
QUIT;
"""
    res = subprocess.run([gap_bin, "-q"], input=code, capture_output=True, text=True, check=True)
    assert "GAP_D5_OK:45" in res.stdout, f"GAP failed: {res.stdout}"
    return {
        "engine": "GAP",
        "status": "PASSED",
        "lie_algebra": "D5 (dim 45)",
        "commuting_A1xA1": True,
        "erlangen_pin_factorization": True,
    }


def run_macaulay2_verification() -> dict:
    """4. Macaulay2 Groebner-basis certification of the 4-projector ideal & Erlangen gauge invariance."""
    m2_bin = "/usr/bin/M2"
    code = """
R = QQ[Np, Nn, u, uinv, x01, x10, y01, y10];
I = ideal(Np^2 - Np, Nn^2 - Nn, u * uinv - 1);
A = R / I;
use A;
PiPlus = Np * (1 - Nn);
PiMinus = (1 - Np) * Nn;
PiPairPlus = Np * Nn;
PiPairMinus = (1 - Np) * (1 - Nn);
tau3 = Np - Nn;
twoK0 = Np + Nn - 1;
assert(PiPlus^2 == PiPlus);
assert(PiMinus^2 == PiMinus);
assert(PiPairPlus^2 == PiPairPlus);
assert(PiPairMinus^2 == PiPairMinus);
assert(PiPlus * PiMinus == 0);
assert(PiPlus * PiPairPlus == 0);
assert(PiPlus + PiMinus + PiPairPlus + PiPairMinus == 1);
assert(tau3 == PiPlus - PiMinus);
assert(twoK0 == PiPairPlus - PiPairMinus);
assert(tau3 * PiPlus == PiPlus);
assert(tau3 * PiMinus == -PiMinus);
assert(tau3 * PiPairPlus == 0);
assert(twoK0 * PiPairPlus == PiPairPlus);
assert(twoK0 * PiPairMinus == -PiPairMinus);
assert(tau3^2 + twoK0^2 == 1);
x01b = u^2 * x01; x10b = uinv^2 * x10;
y01b = u^2 * y01; y10b = uinv^2 * y10;
assert(x01b * y10b + x10b * y01b == x01 * y10 + x10 * y01);
assert(x01b * y10b - x10b * y01b == x01 * y10 - x10 * y01);
print "M2_PROJECTOR_IDEAL_OK";
exit 0;
"""
    res = subprocess.run([m2_bin, "--silent"], input=code, capture_output=True, text=True, check=True)
    assert "M2_PROJECTOR_IDEAL_OK" in res.stdout, f"M2 failed: {res.stdout} {res.stderr}"
    return {
        "engine": "Macaulay2",
        "status": "PASSED",
        "ring": "QQ[Np,Nn,u,uinv,...]/(Np^2-Np, Nn^2-Nn, u*uinv-1)",
        "casimir_sum": "tau3^2 + twoK0^2 == 1",
        "erlangen_gauge_invariance": True,
    }


def run_singular_verification() -> dict:
    """5. Singular Groebner-basis reduction certifying projector, Casimir, and Erlangen gauge identities."""
    singular_bin = "/home/goutev/miniforge3/envs/sage/bin/Singular"
    code = """
ring R = 0, (Np, Nn, u, uinv, x01, x10, y01, y10), dp;
ideal I = std(ideal(Np^2 - Np, Nn^2 - Nn, u * uinv - 1));
poly PiPlus = Np * (1 - Nn);
poly PiMinus = (1 - Np) * Nn;
poly PiPairPlus = Np * Nn;
poly PiPairMinus = (1 - Np) * (1 - Nn);
poly tau3 = Np - Nn;
poly twoK0 = Np + Nn - 1;
poly g_diff = (u^2 * x01) * (uinv^2 * y10) + (uinv^2 * x10) * (u^2 * y01) - (x01 * y10 + x10 * y01);
poly R_diff = (u^2 * x01) * (uinv^2 * y10) - (uinv^2 * x10) * (u^2 * y01) - (x01 * y10 - x10 * y01);
int ok = (reduce(PiPlus^2 - PiPlus, I) == 0)
  && (reduce(PiMinus^2 - PiMinus, I) == 0)
  && (reduce(PiPlus * PiMinus, I) == 0)
  && (reduce(PiPlus + PiMinus + PiPairPlus + PiPairMinus - 1, I) == 0)
  && (reduce(tau3 * PiPlus - PiPlus, I) == 0)
  && (reduce(tau3 * PiMinus + PiMinus, I) == 0)
  && (reduce(twoK0 * PiPairPlus - PiPairPlus, I) == 0)
  && (reduce(twoK0 * PiPairMinus + PiPairMinus, I) == 0)
  && (reduce(tau3^2 + twoK0^2 - 1, I) == 0)
  && (reduce(g_diff, I) == 0)
  && (reduce(R_diff, I) == 0);
if (ok) {
  print("SINGULAR_PROJECTOR_IDEAL_OK");
} else {
  print("SINGULAR_PROJECTOR_IDEAL_FAIL");
}
quit;
"""
    res = subprocess.run([singular_bin, "-q"], input=code, capture_output=True, text=True, check=True)
    assert "SINGULAR_PROJECTOR_IDEAL_OK" in res.stdout, f"Singular failed: {res.stdout} {res.stderr}"
    return {
        "engine": "Singular",
        "status": "PASSED",
        "std_basis_reduction": "0 remainder on all 11 projector, Casimir, and Erlangen gauge identities",
    }


def main() -> int:
    results = [
        run_sympy_verification(),
        run_sage_verification(),
        run_gap_verification(),
        run_macaulay2_verification(),
        run_singular_verification(),
    ]
    print(json.dumps({"multilingual_cas_verification": results}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
