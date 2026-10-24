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
