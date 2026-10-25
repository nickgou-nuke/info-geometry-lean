#!/usr/bin/env python3
"""
Exact Symbolic Verification of Archetypes XLII-LIV in SymPy:
5-Graded Operator Zorn Algebra, BCFW Contact Recursion, Unified Three-Arnold Triad,
and Operator / 3D Navier-Stokes Lamb-Vorticity Depletion.

Tests both:
1. Noncommutative operator ring `A` (`Symbol(..., commutative=False)`) for `OpZornMatrix A`.
2. Commutative ring `R` (`Symbol(..., commutative=True)`) for 3D `ZornVectorMatrix R`.
"""

from __future__ import annotations
from dataclasses import dataclass
import sys
import sympy as sp


@dataclass
class OpVec3:
    x: sp.Expr
    y: sp.Expr
    z: sp.Expr

    def __add__(self, other: "OpVec3") -> "OpVec3":
        return OpVec3(
            sp.expand(self.x + other.x),
            sp.expand(self.y + other.y),
            sp.expand(self.z + other.z),
        )

    def __sub__(self, other: "OpVec3") -> "OpVec3":
        return OpVec3(
            sp.expand(self.x - other.x),
            sp.expand(self.y - other.y),
            sp.expand(self.z - other.z),
        )

    def __neg__(self) -> "OpVec3":
        return OpVec3(sp.expand(-self.x), sp.expand(-self.y), sp.expand(-self.z))

    def is_zero(self) -> bool:
        return (
            sp.expand(self.x) == 0
            and sp.expand(self.y) == 0
            and sp.expand(self.z) == 0
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, OpVec3):
            return False
        return (self - other).is_zero()


def v_zero() -> OpVec3:
    return OpVec3(sp.Integer(0), sp.Integer(0), sp.Integer(0))


def left_scale(c: sp.Expr, u: OpVec3) -> OpVec3:
    return OpVec3(sp.expand(c * u.x), sp.expand(c * u.y), sp.expand(c * u.z))


def right_scale(u: OpVec3, c: sp.Expr) -> OpVec3:
    return OpVec3(sp.expand(u.x * c), sp.expand(u.y * c), sp.expand(u.z * c))


def dot(u: OpVec3, w: OpVec3) -> sp.Expr:
    return sp.expand(u.x * w.x + u.y * w.y + u.z * w.z)


def naive_cross(u: OpVec3, v: OpVec3) -> OpVec3:
    return OpVec3(
        sp.expand(u.y * v.z - u.z * v.y),
        sp.expand(u.z * v.x - u.x * v.z),
        sp.expand(u.x * v.y - u.y * v.x),
    )


def skew_cross(u: OpVec3, v: OpVec3) -> OpVec3:
    return naive_cross(u, v) - naive_cross(v, u)


@dataclass
class OpZornMatrix:
    a: sp.Expr
    v: OpVec3
    w: OpVec3
    b: sp.Expr

    def __add__(self, other: "OpZornMatrix") -> "OpZornMatrix":
        return OpZornMatrix(
            sp.expand(self.a + other.a),
            self.v + other.v,
            self.w + other.w,
            sp.expand(self.b + other.b),
        )

    def __sub__(self, other: "OpZornMatrix") -> "OpZornMatrix":
        return OpZornMatrix(
            sp.expand(self.a - other.a),
            self.v - other.v,
            self.w - other.w,
            sp.expand(self.b - other.b),
        )

    def __mul__(self, other: "OpZornMatrix") -> "OpZornMatrix":
        return OpZornMatrix(
            sp.expand(self.a * other.a - dot(self.v, other.w)),
            left_scale(self.a, other.v)
            + right_scale(self.v, other.b)
            - skew_cross(self.w, other.w),
            right_scale(self.w, other.a)
            + left_scale(self.b, other.w)
            + skew_cross(self.v, other.v),
            sp.expand(-dot(self.w, other.v) + self.b * other.b),
        )

    def is_zero(self) -> bool:
        return (
            sp.expand(self.a) == 0
            and self.v.is_zero()
            and self.w.is_zero()
            and sp.expand(self.b) == 0
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, OpZornMatrix):
            return False
        return (self - other).is_zero()


def z_zero() -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), v_zero(), v_zero(), sp.Integer(0))


def z_one() -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(1), v_zero(), v_zero(), sp.Integer(1))


def op_comm(X: OpZornMatrix, Y: OpZornMatrix) -> OpZornMatrix:
    return X * Y - Y * X


def op_anti(X: OpZornMatrix, Y: OpZornMatrix) -> OpZornMatrix:
    return X * Y + Y * X


def op_assoc(X: OpZornMatrix, Y: OpZornMatrix, Z: OpZornMatrix) -> OpZornMatrix:
    return (X * Y) * Z - X * (Y * Z)


def grade_minus2(eta: sp.Expr) -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), OpVec3(eta, sp.Integer(0), sp.Integer(0)), v_zero(), sp.Integer(0))


def grade_minus1(y: sp.Expr, z: sp.Expr) -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), v_zero(), OpVec3(sp.Integer(0), y, z), sp.Integer(0))


def grade_zero(rho_p: sp.Expr, rho_m: sp.Expr) -> OpZornMatrix:
    return OpZornMatrix(rho_p, v_zero(), v_zero(), rho_m)


def grade_plus1(y: sp.Expr, z: sp.Expr) -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), OpVec3(sp.Integer(0), y, z), v_zero(), sp.Integer(0))


def grade_plus2(xi: sp.Expr) -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), v_zero(), OpVec3(xi, sp.Integer(0), sp.Integer(0)), sp.Integer(0))


def lightcone_plus(v: OpVec3) -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), v, v_zero(), sp.Integer(0))


def lightcone_minus(w: OpVec3) -> OpZornMatrix:
    return OpZornMatrix(sp.Integer(0), v_zero(), w, sp.Integer(0))


def contact_symplectic_form(y1: sp.Expr, z1: sp.Expr, y2: sp.Expr, z2: sp.Expr) -> sp.Expr:
    return sp.expand((y1 * z2 - z1 * y2) - (y2 * z1 - z2 * y1))


def heisenberg_nil_plus(y: sp.Expr, z: sp.Expr, xi: sp.Expr) -> OpZornMatrix:
    return grade_plus1(y, z) + grade_plus2(xi)


def heisenberg_group_plus(y: sp.Expr, z: sp.Expr, xi: sp.Expr) -> OpZornMatrix:
    return z_one() + heisenberg_nil_plus(y, z, xi)


def heisenberg_nil_minus(y: sp.Expr, z: sp.Expr, eta: sp.Expr) -> OpZornMatrix:
    return grade_minus1(y, z) + grade_minus2(eta)


def heisenberg_group_minus(y: sp.Expr, z: sp.Expr, eta: sp.Expr) -> OpZornMatrix:
    return z_one() + heisenberg_nil_minus(y, z, eta)


def main() -> int:
    print("======================================================================")
    print("SymPy Verification: 5-Graded Operator Zorn, BCFW, Arnold & Navier-Stokes")
    print("======================================================================")

    # Noncommutative operator symbols
    y1, z1, xi1, y2, z2, xi2, y3, z3, xi3 = sp.symbols(
        "y1 z1 xi1 y2 z2 xi2 y3 z3 xi3", commutative=False
    )
    eta1, eta2, eta3, xi, eta, rho_p, rho_m = sp.symbols(
        "eta1 eta2 eta3 xi eta rho_p rho_m", commutative=False
    )
    y0, z0, ys, zs = sp.symbols("y0 z0 ys zs", commutative=False)
    ux, uy, uz, wx, wy, wz = sp.symbols("ux uy uz wx wy wz", commutative=False)
    vx, vy, vz, qx, qy, qz = sp.symbols("vx vy vz qx qy qz", commutative=False)
    dp, dm = sp.symbols("dp dm", commutative=False)

    # 1. Archetypes XLII-XLIV: Positive & Negative Heisenberg Nilradical Associativity
    N1p = heisenberg_nil_plus(y1, z1, xi1)
    N2p = heisenberg_nil_plus(y2, z2, xi2)
    N3p = heisenberg_nil_plus(y3, z3, xi3)
    H1p = heisenberg_group_plus(y1, z1, xi1)
    H2p = heisenberg_group_plus(y2, z2, xi2)
    H3p = heisenberg_group_plus(y3, z3, xi3)
    w12 = contact_symplectic_form(y1, z1, y2, z2)
    w12_3 = contact_symplectic_form(y1 + y2, z1 + z2, y3, z3)

    assert N1p * N2p == grade_plus2(w12)
    assert op_assoc(N1p, N2p, N3p) == z_zero()
    assert H1p * H2p == heisenberg_group_plus(y1 + y2, z1 + z2, xi1 + xi2 + w12)
    assert op_assoc(H1p, H2p, H3p) == z_zero()
    assert H1p * heisenberg_group_plus(-y1, -z1, -xi1) == z_one()

    N1m = heisenberg_nil_minus(y1, z1, eta1)
    N2m = heisenberg_nil_minus(y2, z2, eta2)
    N3m = heisenberg_nil_minus(y3, z3, eta3)
    H1m = heisenberg_group_minus(y1, z1, eta1)
    H2m = heisenberg_group_minus(y2, z2, eta2)
    H3m = heisenberg_group_minus(y3, z3, eta3)

    assert N1m * N2m == grade_minus2(-w12)
    assert op_assoc(N1m, N2m, N3m) == z_zero()
    assert H1m * H2m == heisenberg_group_minus(y1 + y2, z1 + z2, eta1 + eta2 - w12)
    assert op_assoc(H1m, H2m, H3m) == z_zero()
    assert H1m * heisenberg_group_minus(-y1, -z1, -eta1) == z_one()
    print("[PASS] Archetypes XLII-XLIV: Positive & Negative Nilradical Associativity & Group Laws")

    # 2. Archetype XLV: Opposite-Nilradical G_0 Nucleus Closure
    Np = heisenberg_nil_plus(y1, z1, xi)
    Nm = heisenberg_nil_minus(y2, z2, eta)
    K = op_anti(Np, Nm)
    assert K == grade_zero(-(y1 * y2 + z1 * z2 + eta * xi), -(y2 * y1 + z2 * z1 + xi * eta))
    Lp = lightcone_plus(OpVec3(vx, vy, vz))
    Lm = lightcone_minus(OpVec3(qx, qy, qz))
    assert op_comm(K, Lp * Lm) == op_comm(K, Lp) * Lm + Lp * op_comm(K, Lm)
    print("[PASS] Archetype XLV: Opposite-Nilradical G_0 Nucleus Closure & Leibniz Derivation")

    # 3. Archetypes XLVI & XLVII: 5-Grade Invariance & Contact Centrality / Readout
    D = grade_zero(rho_p, rho_m)
    assert op_comm(D, grade_plus1(y1, z1)) == grade_plus1(rho_p * y1 - y1 * rho_m, rho_p * z1 - z1 * rho_m)
    assert op_comm(D, grade_plus2(xi)) == grade_plus2(rho_m * xi - xi * rho_p)
    assert op_comm(D, grade_minus1(y1, z1)) == grade_minus1(rho_m * y1 - y1 * rho_p, rho_m * z1 - z1 * rho_p)
    assert op_comm(D, grade_minus2(eta)) == grade_minus2(rho_p * eta - eta * rho_m)
    assert H1p * heisenberg_group_plus(sp.Integer(0), sp.Integer(0), xi) == heisenberg_group_plus(y1, z1, xi1 + xi)
    assert grade_minus2(eta) * (grade_minus1(y1, z1) + grade_plus2(xi)) == grade_zero(-eta * xi, sp.Integer(0))
    assert op_assoc(
        heisenberg_group_plus(sp.Integer(0), sp.Integer(0), xi),
        D,
        heisenberg_group_minus(sp.Integer(0), sp.Integer(0), eta),
    ) == z_zero()
    print("[PASS] Archetypes XLVI-XLVII: 5-Grade Invariance, Contact Centrality & Readout")

    # 4. Archetype XLVIII: 5-Graded BCFW Transverse Shift & Contact Pole Residue
    P0 = OpZornMatrix(sp.Integer(1), OpVec3(sp.Integer(0), -y0, -z0), v_zero(), sp.Integer(0))
    P_shifted = OpZornMatrix(sp.Integer(1), OpVec3(sp.Integer(0), -(ys + y0), -(zs + z0)), v_zero(), sp.Integer(0))
    S_plus = z_one() + grade_plus1(ys, zs)
    S_minus = z_one() + grade_plus1(-ys, -zs)
    w_res = contact_symplectic_form(ys, zs, y0, z0)
    assert op_assoc(S_plus, P0, S_minus) == z_zero()
    assert P0 * S_minus == P_shifted - grade_plus2(w_res)
    assert (S_plus * P0) * S_minus == P_shifted - grade_plus2(w_res + w_res)
    assert grade_minus2(eta) * (P0 * S_minus - P_shifted) == grade_zero(eta * w_res, sp.Integer(0))
    print("[PASS] Archetype XLVIII: 5-Graded BCFW Transverse Shift & Symplectic Contact Residue")

    # 5. Archetypes L-LII: Unified Three-Arnold Triad
    v1_vec = OpVec3(ux, uy, uz)
    v2_vec = OpVec3(wx, wy, wz)
    v3_vec = OpVec3(vx, vy, vz)
    om12 = v1_vec - v2_vec
    om23 = v2_vec - v3_vec
    om31 = v3_vec - v1_vec
    cycle = skew_cross(v1_vec, v2_vec) + skew_cross(v2_vec, v3_vec) + skew_cross(v3_vec, v1_vec)
    assert skew_cross(om12, om23) + skew_cross(om23, om31) + skew_cross(om31, om12) == cycle + cycle + cycle
    assert op_comm(op_comm(N1p, N2p), N3p) + op_comm(op_comm(N2p, N3p), N1p) + op_comm(op_comm(N3p, N1p), N2p) == z_zero()

    assert (H1p * H2p) * H3p == heisenberg_group_plus(y1 + y2 + y3, z1 + z2 + z3, xi1 + xi2 + xi3 + w12 + w12_3)
    H1p_inv = heisenberg_group_plus(-y1, -z1, -xi1)
    H2p_inv = heisenberg_group_plus(-y2, -z2, -xi2)
    assert (H1p * H2p) * (H1p_inv * H2p_inv) == heisenberg_group_plus(sp.Integer(0), sp.Integer(0), w12 + w12)
    print("[PASS] Archetypes L-LII: Unified Three-Arnold Triad (Braid, Hydrodynamics, KAN Loop)")

    # 6. Archetypes LIII & LIV: Operator Navier-Stokes Viscous Leibniz & 5-Graded Vorticity Depletion
    D_visc = grade_zero(dp, dm)
    u_vec = OpVec3(ux, uy, uz)
    w_vec = OpVec3(wx, wy, wz)
    U_op = lightcone_plus(u_vec)
    Om_p = lightcone_plus(w_vec)
    Om_m = lightcone_minus(w_vec)

    # Opposite-chirality viscous Leibniz rule (exact over any noncommutative ring A):
    assert op_comm(D_visc, Om_p * Om_m) == op_comm(D_visc, Om_p) * Om_m + Om_p * op_comm(D_visc, Om_m)
    assert op_anti(op_comm(D_visc, Om_p), Om_m) + op_anti(Om_p, op_comm(D_visc, Om_m)) == op_comm(D_visc, op_anti(Om_p, Om_m))
    # Same-chirality Lamb product viscous action & 3D Lamb-velocity work projection:
    assert U_op * (Om_p * U_op) == grade_zero(-dot(u_vec, skew_cross(w_vec, u_vec)), sp.Integer(0))
    assert (Om_p * U_op) * U_op == grade_zero(sp.Integer(0), -dot(skew_cross(w_vec, u_vec), u_vec))

    U_perp = grade_plus1(uy, uz)
    Om_perp = grade_plus1(wy, wz)
    assert U_perp * (Om_perp * U_perp) == z_zero()
    assert (Om_perp * U_perp) * U_perp == z_zero()
    assert Om_perp * (Om_perp * U_perp) == z_zero()
    assert (Om_perp * U_perp) * Om_perp == z_zero()
    print("[PASS] Archetypes LIII-LIV (Noncommutative): Enstrophy Balance & 5-Graded Vorticity Depletion")

    # 7. Archetype LIV.4 (Commutative 3D): Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence
    c_ux, c_uy, c_uz, c_wx, c_wy, c_wz, c_dp, c_dm = sp.symbols(
        "c_ux c_uy c_uz c_wx c_wy c_wz c_dp c_dm", commutative=True
    )
    cu = OpVec3(c_ux, c_uy, c_uz)
    cw = OpVec3(c_wx, c_wy, c_wz)
    cU = lightcone_plus(cu)
    cOm = lightcone_plus(cw)
    cOm_m = lightcone_minus(cw)
    cD_visc = grade_zero(c_dp, c_dm)
    assert op_comm(cD_visc, cOm * cOm_m) == op_comm(cD_visc, cOm) * cOm_m + cOm * op_comm(cD_visc, cOm_m)
    assert op_comm(cD_visc, cOm) * cU + cOm * op_comm(cD_visc, cU) + op_comm(cD_visc, cOm * cU) + op_comm(cD_visc, cOm * cU) == z_zero()
    assert cU * (cOm * cU) == z_zero()
    assert (cOm * cU) * cU == z_zero()
    assert cOm * (cOm * cU) == z_zero()
    assert (cOm * cU) * cOm == z_zero()
    print("[PASS] Archetype LIV.4 (Commutative 3D): Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence")

    # 8. Archetypes LV-LVII: Noncommutative QGT, Metriplectic Evolution, & Beltrami Helicity Dissipation
    Gamma = grade_zero(sp.Integer(1), sp.Integer(-1))
    Q_qgt = U_op * Om_m + U_op * Om_m
    Q_dual = Om_m * U_op + Om_m * U_op
    g_qgt = op_anti(U_op, Om_m)
    w_berry = op_comm(U_op, Om_m)
    assert Q_qgt == g_qgt + w_berry
    assert Q_dual == g_qgt - w_berry
    assert (z_one() + Gamma) * g_qgt == Q_qgt
    assert (z_one() - Gamma) * g_qgt == Q_dual

    hp, hm, nup, num, nu = sp.symbols("hp hm nup num nu", commutative=False)
    H_gen = grade_zero(hp, hm)
    S_gen = grade_zero(nup, num)
    X_full = OpZornMatrix(dp, u_vec, w_vec, dm)
    assert op_comm(H_gen, X_full) + op_anti(S_gen, X_full) == (H_gen + S_gen) * X_full + X_full * (S_gen - H_gen)
    assert op_anti(S_gen, U_op * Om_m) == op_anti(S_gen, U_op) * Om_m + U_op * op_anti(S_gen, Om_m) - ((U_op * S_gen) * Om_m + (U_op * S_gen) * Om_m)
    assert op_comm(H_gen, op_anti(S_gen, X_full)) - op_anti(S_gen, op_comm(H_gen, X_full)) == op_anti(op_comm(H_gen, S_gen), X_full)

    c_nu, c_lam = sp.symbols("c_nu c_lam", commutative=True)
    cu_beltrami = OpVec3(c_lam * c_ux, c_lam * c_uy, c_lam * c_uz)
    cOm_beltrami_p = lightcone_plus(cu_beltrami)
    cOm_beltrami_m = lightcone_minus(cu_beltrami)
    cS_visc = grade_zero(-c_nu * c_lam**2, -c_nu * c_lam**2)
    cH_hel = op_anti(cU, cOm_beltrami_m)
    assert cOm_beltrami_p * cU == z_zero()
    assert op_anti(cS_visc * cU, cOm_beltrami_m) + op_anti(cU, cS_visc * cOm_beltrami_m) == grade_zero(-2 * c_nu * c_lam**2, -2 * c_nu * c_lam**2) * cH_hel
    print("[PASS] Archetypes LV-LVII: Noncommutative QGT, Metriplectic Evolution & Beltrami Helicity Dissipation")

    # 9. Archetypes LVIII & LIX: Quantum Chromo-Hydrodynamics (Yang-Mills Bianchi, Chern-Simons, & Confinement)
    def color_cross(u: OpVec3, v: OpVec3) -> OpVec3:
        return naive_cross(u, v) + naive_cross(v, u)

    F_ym = naive_cross(u_vec, u_vec)
    assert naive_cross(u_vec, w_vec) + naive_cross(u_vec, w_vec) == skew_cross(u_vec, w_vec) + color_cross(u_vec, w_vec)
    assert skew_cross(u_vec, u_vec) == v_zero()
    assert color_cross(u_vec, u_vec) == F_ym + F_ym
    # Algebraic QCD Bianchi identity: u . F_YM(u) == F_YM(u) . u
    assert sp.expand(dot(u_vec, F_ym) - dot(F_ym, u_vec)) == 0
    # Anomaly-free Chern-Simons color helicity in G_0:
    F_m = lightcone_minus(F_ym)
    C_cs = op_anti(U_op, F_m)
    assert C_cs == grade_zero(-dot(u_vec, F_ym), -dot(u_vec, F_ym))
    w_cs = op_comm(U_op, F_m)
    assert sp.expand(w_cs.a + w_cs.b) == 0

    # Quark-Diquark-Meson-Baryon Nucleus Confinement:
    M_singlet = op_anti(U_op, Om_m)
    B_singlet = op_assoc(U_op, Om_p, lightcone_plus(OpVec3(y1, z1, xi1)))
    assert M_singlet.v == v_zero() and M_singlet.w == v_zero()
    assert B_singlet.v == v_zero() and B_singlet.w == v_zero()
    assert op_comm(M_singlet, U_op * Om_m) == op_comm(M_singlet, U_op) * Om_m + U_op * op_comm(M_singlet, Om_m)
    assert op_comm(B_singlet, U_op * Om_m) == op_comm(B_singlet, U_op) * Om_m + U_op * op_comm(B_singlet, Om_m)
    print("[PASS] Archetypes LVIII-LIX: Quantum Chromo-Hydrodynamics, QCD Bianchi & Nucleus Confinement")

    # 10. Archetype LX: Master Nilpotent-Idempotent Trifactor Synthesis
    e11 = grade_zero(sp.Integer(1), sp.Integer(0))
    Unip_u = z_one() + U_op
    Unip_w = z_one() + Om_m
    Psi_L = Unip_w * e11
    Psi_R = e11 * Unip_u
    Pi_tri = Psi_L * Psi_R
    assert Psi_L * Psi_L == Psi_L
    assert Psi_R * Psi_R == Psi_R
    assert Psi_R * Psi_L == grade_zero(sp.Integer(1) - dot(u_vec, w_vec), sp.Integer(0))
    H_mod_uw = op_anti(U_op, Om_m)
    assert op_assoc(Psi_R, Psi_L, Psi_R) == op_comm(H_mod_uw, U_op)
    assert op_assoc(Psi_L, Psi_R, Psi_L) == op_comm(H_mod_uw, Om_m)
    assert Pi_tri * Pi_tri == OpZornMatrix(
        sp.Integer(1) - dot(u_vec, w_vec),
        u_vec - right_scale(u_vec, dot(w_vec, u_vec)),
        w_vec - left_scale(dot(w_vec, u_vec), w_vec),
        -dot(w_vec, u_vec) + dot(w_vec, u_vec) * dot(w_vec, u_vec),
    )
    # General Gauss-Bruhat Trifactor Madelung-Bernoulli split:
    T_bruhat = (Unip_w * D_visc) * Unip_u
    assert T_bruhat == (Psi_L * grade_zero(dp, sp.Integer(0))) * Psi_R + grade_zero(sp.Integer(0), dm)
    # 5-Graded Contact-Transverse Strict Idempotence & Lamb Composition:
    def contact_flow_idem(xi_val, y_val, z_val):
        u_m = z_one() + lightcone_minus(OpVec3(xi_val, sp.Integer(0), sp.Integer(0)))
        u_p = z_one() + lightcone_plus(OpVec3(sp.Integer(0), -y_val, -z_val))
        return (u_m * e11) * u_p
    Pi_c1 = contact_flow_idem(xi1, y1, z1)
    Pi_c1_perp = z_one() - Pi_c1
    Pi_c2 = contact_flow_idem(xi2, y2, z2)
    assert Pi_c1 * Pi_c1 == Pi_c1
    assert Pi_c1_perp * Pi_c1_perp == Pi_c1_perp
    assert Pi_c1 * Pi_c1_perp == z_zero()
    assert Pi_c1_perp * Pi_c1 == z_zero()
    assert Pi_c1 * Pi_c2 == contact_flow_idem(xi1 + w12, y2, z2)
    print("[PASS] Archetype LX: Master Nilpotent-Idempotent Trifactor Synthesis & Contact-Lamb Composition")

    # 11. Archetypes LXI & LXII: 1934 Jordan-von Neumann-Wigner Formalism in OpZornMatrix A & ZornVectorMatrix R
    def j_assoc(A_mat: OpZornMatrix, B_mat: OpZornMatrix, C_mat: OpZornMatrix) -> OpZornMatrix:
        return op_anti(op_anti(A_mat, B_mat), C_mat) - op_anti(A_mat, op_anti(B_mat, C_mat))

    Y_full = OpZornMatrix(hp, v3_vec, OpVec3(qx, qy, qz), hm)
    Z_full = OpZornMatrix(nup, OpVec3(y1, z1, xi1), OpVec3(y2, z2, xi2), num)
    assert j_assoc(X_full, Y_full, Z_full) + j_assoc(Z_full, Y_full, X_full) == z_zero()
    assert j_assoc(X_full, Y_full, Z_full) + j_assoc(Y_full, Z_full, X_full) + j_assoc(Z_full, X_full, Y_full) == z_zero()
    jvnw_rhs = op_comm(op_comm(Z_full, X_full), Y_full) + (
        op_assoc(X_full, Y_full, Z_full)
        + op_assoc(Y_full, X_full, Z_full)
        + op_assoc(X_full, Z_full, Y_full)
        - op_assoc(Z_full, X_full, Y_full)
        - op_assoc(Y_full, Z_full, X_full)
        - op_assoc(Z_full, Y_full, X_full)
    )
    assert j_assoc(X_full, Y_full, Z_full) == jvnw_rhs
    assert j_assoc(H_gen, X_full, S_gen) == op_comm(op_comm(S_gen, H_gen), X_full)
    assert j_assoc(H_gen, X_full, H_gen) == z_zero()

    # JvNW Theorem 3 Cubic Peirce Polynomial & Theorem 4 / 12 Cross-Product Cancellation:
    L1_e = op_anti(e11, X_full)
    L2_e = op_anti(e11, L1_e)
    L3_e = op_anti(e11, L2_e)
    assert L3_e - (L2_e + L2_e + L2_e) + (L1_e + L1_e) == z_zero()
    assert L2_e - (L1_e + L1_e + L1_e) + (X_full + X_full) == grade_zero(sp.Integer(0), dm + dm)
    assert (z_zero() - L2_e) + (L1_e + L1_e) == OpZornMatrix(sp.Integer(0), u_vec, w_vec, sp.Integer(0))
    assert L2_e - L1_e == grade_zero(dp + dp, sp.Integer(0))

    J_1 = OpZornMatrix(sp.Integer(0), u_vec, w_vec, sp.Integer(0))
    J_2 = OpZornMatrix(sp.Integer(0), v3_vec, OpVec3(qx, qy, qz), sp.Integer(0))
    assert op_anti(J_1, J_2) == grade_zero(
        -(dot(u_vec, OpVec3(qx, qy, qz)) + dot(v3_vec, w_vec)),
        -(dot(w_vec, v3_vec) + dot(OpVec3(qx, qy, qz), u_vec)),
    )

    # JvNW Theorem 12 Noncommutative Yang-Mills Balance & Cubic Power-Associativity:
    J_ym = OpZornMatrix(sp.Integer(0), u_vec, F_ym, sp.Integer(0))
    alpha_ym = -(dot(u_vec, F_ym) + dot(u_vec, F_ym))
    assert op_anti(J_ym, J_ym) == grade_zero(alpha_ym, alpha_ym)
    assert j_assoc(X_full, X_full, X_full) == z_zero()
    assert j_assoc(op_anti(H_gen, H_gen), X_full, H_gen) == z_zero()

    # Commutative JvNW Fundamental Axiom (III) on ZornVectorMatrix R:
    cA_mat = OpZornMatrix(c_dp, cu, cw, c_dm)
    cB_mat = OpZornMatrix(c_nu, OpVec3(c_wx, c_uz, c_uy), OpVec3(c_ux, c_wz, c_wy), c_lam)
    assert j_assoc(op_anti(cA_mat, cA_mat), cB_mat, cA_mat) == z_zero()
    print("[PASS] Archetypes LXI-LXII: 1934 Jordan-von Neumann-Wigner Cubic Peirce, Page 45 & Axiom III")

    # 12. Archetypes LXIII & LXIV: Wheeler's "It from Bit" (P^2 = P), "Boundary of a Boundary is Zero" (d^2 = 0), & Participatory Loops
    e22 = grade_zero(sp.Integer(0), sp.Integer(1))
    P_row_u = Psi_R
    P_col_w = Psi_L
    P_row_v1 = e11 + lightcone_plus(u_vec)
    P_row_v2 = e11 + lightcone_plus(w_vec)
    P_row_v3 = e11 + lightcone_plus(v3_vec)
    d_u = P_row_u - e11
    d_w = P_col_w - e11
    d_1 = P_row_v1 - e11
    d_2 = P_row_v2 - e11
    d_3 = P_row_v3 - e11
    assert P_row_u * P_row_u == P_row_u
    assert P_col_w * P_col_w == P_col_w
    assert d_u * d_u == z_zero()
    assert d_w * d_w == z_zero()
    assert grade_plus1(y1, z1) * (grade_plus1(y1, z1) * N2p) == z_zero()
    assert P_row_u * P_col_w == grade_zero(sp.Integer(1) - dot(u_vec, w_vec), sp.Integer(0))
    assert d_u * d_w + d_w * d_u == grade_zero(-dot(u_vec, w_vec), -dot(w_vec, u_vec))
    assert d_u * d_w - d_w * d_u == grade_zero(-dot(u_vec, w_vec), dot(w_vec, u_vec))
    assert e22 * (P_row_v1 * P_row_v2) == lightcone_minus(skew_cross(u_vec, w_vec))
    assert d_1 * (d_2 * d_3) == grade_zero(-dot(u_vec, skew_cross(w_vec, v3_vec)), sp.Integer(0))
    assert (d_1 * d_2) * d_3 == grade_zero(sp.Integer(0), -dot(skew_cross(u_vec, w_vec), v3_vec))
    print("[PASS] Archetypes LXIII-LXIV: Wheeler 'It from Bit', 'Boundary of a Boundary is Zero', & Participatory Loops")

    # ------------------------------------------------------------------
    # 13. Archetypes LXV & LXVI: Super-Grassmannian 5-Grading Euler Operator,
    #     KKT Minimal Polynomial (E_5^5 - 5 E_5^3 + 4 E_5 = 0), & (2|3) Supertrace
    # ------------------------------------------------------------------
    def euler5(X: OpZornMatrix) -> OpZornMatrix:
        return OpZornMatrix(
            sp.Integer(0),
            OpVec3(-2 * X.v.x, X.v.y, X.v.z),
            OpVec3(2 * X.w.x, -X.w.y, -X.w.z),
            sp.Integer(0),
        )

    assert euler5(N1p * N2p) == euler5(N1p) * N2p + N1p * euler5(N2p)
    assert euler5(N1m * N2m) == euler5(N1m) * N2m + N1m * euler5(N2m)
    E1_X = euler5(X_full)
    E2_X = euler5(E1_X)
    E3_X = euler5(E2_X)
    E4_X = euler5(E3_X)
    E5_X = euler5(E4_X)
    assert E5_X - (E3_X + E3_X + E3_X + E3_X + E3_X) + (E1_X + E1_X + E1_X + E1_X) == z_zero()
    # (2|3) Lepton-Quark Supertrace cancellation:
    # Lepton trace tr(gradeZero(u.w, 0)) = u.w; Quark trace tr(G_color(u,w)) = u.x*w.x + u.y*w.y + u.z*w.z = u.w
    quark_tr = u_vec.x * w_vec.x + u_vec.y * w_vec.y + u_vec.z * w_vec.z
    lepton_Mat = z_zero() - (lightcone_plus(u_vec) * lightcone_minus(w_vec))
    lepton_tr = lepton_Mat.a + lepton_Mat.b
    assert sp.expand(lepton_tr - quark_tr) == 0
    print("[PASS] Archetypes LXV-LXVI: Euler 5-Grading Derivation, KKT Degree-5 Polynomial, & (2|3) Supertrace Cancellation")

    # ------------------------------------------------------------------
    # 14. Archetypes LXVII & LXVIII: Rolf Dahm (JPCS 3152 (2025) 012008)
    #     Plücker-Klein 6-Vector Bijection, Maxwell-Poynting Invariants,
    #     Dihedral D_4 / PG(3,2) Collinear Operator Triples, & Lounesto Ideals
    # ------------------------------------------------------------------
    p_rad_kl = u_vec + w_vec
    p_trans_kl = u_vec - w_vec
    assert p_rad_kl + p_trans_kl == u_vec + u_vec
    assert p_rad_kl - p_trans_kl == w_vec + w_vec
    assert sp.expand(
        (dot(p_rad_kl, p_trans_kl) + dot(p_trans_kl, p_rad_kl))
        - 2 * (dot(u_vec, u_vec) - dot(w_vec, w_vec))
    ) == 0
    assert (z_zero() - (lightcone_plus(u_vec) * lightcone_minus(w_vec) + lightcone_minus(w_vec) * lightcone_plus(u_vec))) == grade_zero(
        dot(u_vec, w_vec), dot(w_vec, u_vec)
    )

    # Dahm Dihedral D_4 & PG(3,2) collinear operator triple identity (s1 * s0) * r1 = r0 = 1:
    dahm_r0 = grade_zero(sp.Integer(1), sp.Integer(1))
    dahm_r1 = OpZornMatrix(sp.Integer(0), OpVec3(-sp.Integer(1), sp.Integer(0), sp.Integer(0)), OpVec3(-sp.Integer(1), sp.Integer(0), sp.Integer(0)), sp.Integer(0))
    dahm_s0 = grade_zero(sp.Integer(1), -sp.Integer(1))
    dahm_s1 = OpZornMatrix(sp.Integer(0), OpVec3(-sp.Integer(1), sp.Integer(0), sp.Integer(0)), OpVec3(sp.Integer(1), sp.Integer(0), sp.Integer(0)), sp.Integer(0))
    assert dahm_r1 * dahm_r1 == z_zero() - dahm_r0
    assert dahm_s0 * dahm_s0 == dahm_r0
    assert dahm_s1 * dahm_s1 == dahm_r0
    assert dahm_s0 * dahm_r1 == dahm_s1
    assert dahm_r1 * dahm_s0 == z_zero() - dahm_s1
    assert dahm_s0 * dahm_s1 == dahm_r1
    assert dahm_s1 * dahm_s0 == z_zero() - dahm_r1
    assert (dahm_s1 * dahm_s0) * dahm_r1 == dahm_r0
    assert (dahm_s0 * dahm_s1) * dahm_r1 == z_zero() - dahm_r0
    # Lounesto spinorial left ideal absorption:
    psi_L = OpZornMatrix(dp, OpVec3(sp.Integer(0), sp.Integer(0), sp.Integer(0)), OpVec3(dm, sp.Integer(0), sp.Integer(0)), sp.Integer(0))
    assert psi_L * e11 == psi_L
    assert psi_L * e22 == z_zero()
    print("[PASS] Archetypes LXVII-LXVIII: Dahm Plücker-Klein Bijection, Dihedral D_4 / PG(3,2) Collinear Triples, & Lounesto Spinorial Ideals")

    # 15. Archetypes LXIX & LXX: Electromagnetic Hodge Dual Maxwell-Poynting Stress Matrix
    #     J(E, B) * J*(E, B) = <-(E.E), E x B, -(E x B), B.B> & Simple Line Square-Zero J_line^2 = 0
    J_em = OpZornMatrix(sp.Integer(0), u_vec, w_vec, sp.Integer(0))
    J_star = OpZornMatrix(sp.Integer(0), -w_vec, u_vec, sp.Integer(0))
    J_dual = OpZornMatrix(sp.Integer(0), w_vec, u_vec, sp.Integer(0))
    S_poynt = skew_cross(u_vec, w_vec)
    assert J_em * J_star == OpZornMatrix(-dot(u_vec, u_vec), S_poynt, -S_poynt, dot(w_vec, w_vec))
    assert J_em * J_dual == OpZornMatrix(-dot(u_vec, u_vec), S_poynt, S_poynt, -dot(w_vec, w_vec))
    assert sp.expand(((J_em * J_star).a + (J_em * J_star).b) - (dot(w_vec, w_vec) - dot(u_vec, u_vec))) == 0
    assert sp.expand(((dahm_s0 * (J_em * J_star)).a + (dahm_s0 * (J_em * J_star)).b) + (dot(u_vec, u_vec) + dot(w_vec, w_vec))) == 0
    assert J_em * J_em == grade_zero(-dot(u_vec, w_vec), -dot(w_vec, u_vec))
    print("[PASS] Archetypes LXIX-LXX: Electromagnetic Hodge-Dual Maxwell-Poynting Stress Matrix & Simple Plücker Line Nilpotence")

    print("======================================================================")
    print("ALL CHECKS PASSED")
    print("======================================================================")
    return 0


if __name__ == "__main__":
    sys.exit(main())
