/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset

/-!
# Finite Real $\mathrm{Cl}(3,1)$, Four-Dimensional Peirce-Corner Translation Module, and Corner-Preserving Lorentz Action from the DeWitt Tetractys

This module bridges the two-bit DeWitt Split Tetractys owner
(`InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset`) to:
1. A concrete real `Cl(3,1)` Dirac family `gamma0, gamma1, gamma2, gamma3` in `Matrix (Fin 4) (Fin 4) ℤ`,
   its faithful 4-dimensional Dirac translation module `diracVector p0 p1 p2 p3`, its Minkowski
   quadratic form `(-p0^2 + p1^2 + p2^2 + p3^2) • 1`, and the 6-generator $\mathfrak{so}(3,1)$
   Lorentz bivector action (`sigma12, sigma23, sigma31, boost01, boost02, boost03`) preserving
   `diracVector` and lifting into any commuting Peirce corner.
2. A general `[Ring B]` corner-preserving Lorentz action theorem (`upperCorner_lorentz_conjugation_and_commutator`)
   proving that block-diagonal / even-grade operators preserve `upperCorner P` under both group
   conjugation $T \mapsto G T G_{\mathrm{inv}}$ and Lie commutation $[L_{\mathrm{even}}, T]$, and satisfy
   the unipotent Poincaré semidirect product relation $G(1 + T)G_{\mathrm{inv}} = 1 + G T G_{\mathrm{inv}}$.
3. A concrete faithful 4-dimensional upper Peirce-corner translation module
   `cornerTranslation p0 p1 p2 p3` inside `upperCorner dtMatP1` in `Matrix (Fin 4) (Fin 4) ℤ`,
   together with its abelian nilpotent corner law, unipotent translation group law
   `(1 + cornerTranslation p) * (1 + cornerTranslation q) = 1 + cornerTranslation (p + q)`,
   quadratic determinant pairing `cornerTranslation p * dualCornerTranslation p = (p0^2 - p1^2 - p2^2 + p3^2) • dtMatP1`,
   and corner-preserving spinor Lorentz actions (`dtMatJ2`, `dtMatS2`, `dtMatPhi2`).
4. Real two-spinor null and massive determinant identities (`rankOneMomentum_det_zero`,
   `twoSpinorDet_eq_pairing_sq`, `twoSpinorDet_nonneg`).

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `gamma_clifford_relations`: concrete `Cl(3,1)` Clifford relations in `Matrix (Fin 4) (Fin 4) ℤ`.
- `gamma0_mul_gamma1_ne_comm`: explicit non-commutativity witness for `Matrix (Fin 4) (Fin 4) ℤ`.
- `diracVector_square` & `diracVector_eq_zero_iff`: Minkowski quadratic square and faithfulness of the 4D Dirac module over `ℤ`.
- `so31_bivector_squares_and_diracVector_action`: all 6 $\mathfrak{so}(3,1)$ Lorentz bivectors preserve the 4D `diracVector` module under commutation with the exact $(1,3)$ boost and rotation laws.
- `cornerTranslation_mem_upperCorner_and_faithful`: `cornerTranslation p0 p1 p2 p3` lies strictly in `upperCorner dtMatP1`, is a faithful 4-dimensional `ℤ`-module, is abelian square-zero, and satisfies the unipotent group law `(1 + T(p))(1 + T(q)) = 1 + T(p + q)`.
- `cornerTranslation_lorentz_action_and_quadratic_norm`: the block-diagonal Lorentz generators `dtMatJ2`, `dtMatS2`, `dtMatPhi2` commute with `dtMatP1`, preserve the 4D upper-corner translation module under commutation and conjugation, and preserve the quadratic norm pairing `cornerTranslation p * dualCornerTranslation p = (p0^2 - p1^2 - p2^2 + p3^2) • dtMatP1`.
- `rankOneMomentum_det_zero`, `twoSpinorDet_eq_pairing_sq`, `twoSpinorDet_nonneg`: real two-spinor determinant identities.

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `upperCorner_mul_eq_zero`, `upperCorner_commute`: nilpotence and commutativity of `upperCorner P` for any idempotent `P * P = P` in `[Ring B]`.
- `upperCorner_lorentz_conjugation_and_commutator`: in any `[Ring B]` with `P * P = P`, any `G, G_inv` commuting with `P` preserve `upperCorner P` under conjugation `G * T * G_inv` and satisfy the semidirect product law `G * (1 + T) * G_inv = 1 + G * T * G_inv`, any `evenGrade P L` preserves `upperCorner P` under commutation, and any Lorentz generator commuting with `P` and corner seed `W` lifts its action on a translation module `V` directly into `upperCorner P (W * V)`.

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`, `0 structure wrappers`).
-/

namespace InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge

open Matrix
open InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset

/-! ## §1. Concrete Real $\mathrm{Cl}(3,1)$ Family & 6-Generator $\mathfrak{so}(3,1)$ Lorentz Action on the 4D Dirac Module -/

/-- Alias for the 2-bit integer matrix carrier `Matrix (Fin 4) (Fin 4) ℤ`. -/
abbrev Mat4Z := Matrix (Fin 4) (Fin 4) ℤ

/-- Timelike generator $\gamma_0 = J_1 = J_0 \otimes I_2$ ($\gamma_0^2 = -I_4$). -/
def gamma0 : Mat4Z := dtMatJ1

/-- First spacelike generator $\gamma_1 = S_1 = S_0 \otimes I_2$ ($\gamma_1^2 = +I_4$). -/
def gamma1 : Mat4Z := dtMatS1

/-- Second spacelike generator $\gamma_2 = \Phi_1 S_2 = \Phi_0 \otimes S_0$ ($\gamma_2^2 = +I_4$). -/
def gamma2 : Mat4Z := dtMatPhi1 * dtMatS2

/-- Third spacelike generator $\gamma_3 = \Phi_1 \Phi_2 = \Phi_0 \otimes \Phi_0$ ($\gamma_3^2 = +I_4$). -/
def gamma3 : Mat4Z := dtMatPhi1 * dtMatPhi2

/-- Explicit non-commutativity witness for `Matrix (Fin 4) (Fin 4) ℤ`: `gamma0 * gamma1 ≠ gamma1 * gamma0`. -/
lemma gamma0_mul_gamma1_ne_comm :
    gamma0 * gamma1 ≠ gamma1 * gamma0 := by
  intro h
  have h02 := congr_fun (congr_fun h 0) 2
  revert h02
  decide

/-- The four displayed matrices satisfy the `(-,+,+,+)` Clifford relations in `Matrix (Fin 4) (Fin 4) ℤ`. -/
theorem gamma_clifford_relations :
    gamma0 * gamma0 = -1 ∧
    gamma1 * gamma1 = 1 ∧
    gamma2 * gamma2 = 1 ∧
    gamma3 * gamma3 = 1 ∧
    gamma0 * gamma1 + gamma1 * gamma0 = 0 ∧
    gamma0 * gamma2 + gamma2 * gamma0 = 0 ∧
    gamma0 * gamma3 + gamma3 * gamma0 = 0 ∧
    gamma1 * gamma2 + gamma2 * gamma1 = 0 ∧
    gamma1 * gamma3 + gamma3 * gamma1 = 0 ∧
    gamma2 * gamma3 + gamma3 * gamma2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    decide

/-- Integer-coefficient Dirac 4-vector $V(p) = p_0 \gamma_0 + p_1 \gamma_1 + p_2 \gamma_2 + p_3 \gamma_3$ in `[Ring B]`. -/
def diracVector {B : Type*} [Ring B] (g0 g1 g2 g3 : B) (p0 p1 p2 p3 : ℤ) : B :=
  p0 • g0 + p1 • g1 + p2 • g2 + p3 • g3

theorem gamma2_eq :
    gamma2 = !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem gamma3_eq :
    gamma3 = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem diracVector_eq (p0 p1 p2 p3 : ℤ) :
    diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 =
      !![p1, 0, p0 + p2, p3;
         0, p1, p3, p0 - p2;
         -p0 + p2, p3, -p1, 0;
         p3, -p0 - p2, 0, -p1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracVector, gamma0, gamma1, gamma2_eq, gamma3_eq, dtMatJ1, dtMatS1] <;> ring

/-- The square of the concrete Dirac vector is its `(-,+,+,+)` Minkowski quadratic form. -/
theorem diracVector_square (p0 p1 p2 p3 : ℤ) :
    diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 *
      diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : Mat4Z) := by
  rw [diracVector_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> ring

/-- **Faithfulness of the 4-Dimensional Dirac Translation Module (`diracVector_eq_zero_iff`)**:
The four generators `gamma0, gamma1, gamma2, gamma3` are $\mathbb{Z}$-linearly independent, so
`diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 = 0` if and only if `p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0`. -/
theorem diracVector_eq_zero_iff (p0 p1 p2 p3 : ℤ) :
    diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 = 0 ↔
      p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 := by
  constructor
  · intro h
    have h00 : diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 0 0 = 0 := by rw [h]; rfl
    have h02 : diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 0 2 = 0 := by rw [h]; rfl
    have h13 : diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 1 3 = 0 := by rw [h]; rfl
    have h03 : diracVector gamma0 gamma1 gamma2 gamma3 p0 p1 p2 p3 0 3 = 0 := by rw [h]; rfl
    simp [diracVector_eq] at h00 h02 h13 h03
    refine ⟨by omega, h00, by omega, h03⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- Spatial rotation bivector $\Sigma_{12} = \gamma_1 \gamma_2$ in `[Ring B]`. -/
def sigma12 {B : Type*} [Ring B] (g1 g2 : B) : B := g1 * g2

/-- Spatial rotation bivector $\Sigma_{23} = \gamma_2 \gamma_3$ in `[Ring B]`. -/
def sigma23 {B : Type*} [Ring B] (g2 g3 : B) : B := g2 * g3

/-- Spatial rotation bivector $\Sigma_{31} = \gamma_3 \gamma_1$ in `[Ring B]`. -/
def sigma31 {B : Type*} [Ring B] (g3 g1 : B) : B := g3 * g1

/-- Lorentz boost bivector $K_{01} = \gamma_0 \gamma_1$ in `[Ring B]`. -/
def boost01 {B : Type*} [Ring B] (g0 g1 : B) : B := g0 * g1

/-- Lorentz boost bivector $K_{02} = \gamma_0 \gamma_2$ in `[Ring B]`. -/
def boost02 {B : Type*} [Ring B] (g0 g2 : B) : B := g0 * g2

/-- Lorentz boost bivector $K_{03} = \gamma_0 \gamma_3$ in `[Ring B]`. -/
def boost03 {B : Type*} [Ring B] (g0 g3 : B) : B := g0 * g3

/-- For any anticommuting `a, b` in `[Ring B]`, `(a * b)^2 = -(a^2 * b^2)`. -/
theorem clifford_bivector_sq {B : Type*} [Ring B] (a b : B)
    (hab : a * b + b * a = 0) :
    (a * b) * (a * b) = -((a * a) * (b * b)) := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
  calc
    (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (-(a * b)) * b := by rw [hba]
    _ = -((a * a) * (b * b)) := by noncomm_ring

/-- Any bivector `a * b` in `[Ring B]` commutes with any `c` that anticommutes with both `a` and `b`. -/
theorem clifford_bivector_comm_orth {B : Type*} [Ring B] (a b c : B)
    (hac : a * c + c * a = 0) (hbc : b * c + c * b = 0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (a * b) c = 0 := by
  have hac' : a * c = -(c * a) := eq_neg_of_add_eq_zero_left hac
  have hbc' : b * c = -(c * b) := eq_neg_of_add_eq_zero_left hbc
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  calc
    (a * b) * c - c * (a * b) = a * (b * c) - c * (a * b) := by simp only [mul_assoc]
    _ = a * (-(c * b)) - c * (a * b) := by rw [hbc']
    _ = -((a * c) * b) - c * (a * b) := by noncomm_ring
    _ = -(-(c * a) * b) - c * (a * b) := by rw [hac']
    _ = 0 := by noncomm_ring

/-- Commutator of a bivector `a * b` with its left factor `a` when `a * b + b * a = 0`. -/
theorem clifford_bivector_comm_left {B : Type*} [Ring B] (a b : B)
    (hab : a * b + b * a = 0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (a * b) a = -((2 : ℤ) • ((a * a) * b)) := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  calc
    (a * b) * a - a * (a * b) = a * (b * a) - a * (a * b) := by simp only [mul_assoc]
    _ = a * (-(a * b)) - a * (a * b) := by rw [hba]
    _ = -((2 : ℤ) • ((a * a) * b)) := by
      rw [two_zsmul]
      noncomm_ring

/-- Commutator of a bivector `a * b` with its right factor `b` when `a * b + b * a = 0`. -/
theorem clifford_bivector_comm_right {B : Type*} [Ring B] (a b : B)
    (hab : a * b + b * a = 0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (a * b) b = (2 : ℤ) • (a * (b * b)) := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  calc
    (a * b) * b - b * (a * b) = a * (b * b) - (b * a) * b := by simp only [mul_assoc]
    _ = a * (b * b) - (-(a * b)) * b := by rw [hba]
    _ = (2 : ℤ) • (a * (b * b)) := by
      rw [two_zsmul]
      noncomm_ring

/-- Linearity of the commutator in the 4-component Dirac vector `diracVector`. -/
theorem comm_diracVector {B : Type*} [Ring B] (X g0 g1 g2 g3 : B) (p0 p1 p2 p3 : ℤ) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm X (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      p0 • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X g0 +
      p1 • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X g1 +
      p2 • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X g2 +
      p3 • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X g3 := by
  dsimp [diracVector, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
  abel

/-- **6-Generator $\mathfrak{so}(3,1)$ Lorentz Bivector Action on the 4D Dirac Translation Module in `[Ring B]` (`so31_bivector_squares_and_diracVector_action`)**:
For any `g0, g1, g2, g3` in `[Ring B]` satisfying the `Cl(3,1)` relations
`g0^2 = -1`, `g1^2 = g2^2 = g3^2 = 1`, and pairwise anticommutation `gi * gj + gj * gi = 0`:
1. The three spatial rotation bivectors satisfy $\Sigma_{12}^2 = \Sigma_{23}^2 = \Sigma_{31}^2 = -1$,
   and the three boost bivectors satisfy $K_{01}^2 = K_{02}^2 = K_{03}^2 = +1$.
2. Under the commutator action $[B, V] = B V - V B$, all six $\mathfrak{so}(3,1)$ bivectors preserve
   the 4-dimensional module `diracVector g0 g1 g2 g3 p0 p1 p2 p3` with the exact $(1,3)$ Minkowski Lorentz
   rotation and boost laws. -/
theorem so31_bivector_squares_and_diracVector_action {B : Type*} [Ring B]
    (g0 g1 g2 g3 : B) (p0 p1 p2 p3 : ℤ)
    (h0 : g0 * g0 = -1) (h1 : g1 * g1 = 1) (h2 : g2 * g2 = 1) (h3 : g3 * g3 = 1)
    (h01 : g0 * g1 + g1 * g0 = 0) (h02 : g0 * g2 + g2 * g0 = 0) (h03 : g0 * g3 + g3 * g0 = 0)
    (h12 : g1 * g2 + g2 * g1 = 0) (h13 : g1 * g3 + g3 * g1 = 0) (h23 : g2 * g3 + g3 * g2 = 0) :
    (sigma12 g1 g2 * sigma12 g1 g2 = -1 ∧
     sigma23 g2 g3 * sigma23 g2 g3 = -1 ∧
     sigma31 g3 g1 * sigma31 g3 g1 = -1 ∧
     boost01 g0 g1 * boost01 g0 g1 = 1 ∧
     boost02 g0 g2 * boost02 g0 g2 = 1 ∧
     boost03 g0 g3 * boost03 g0 g3 = 1) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (sigma12 g1 g2) (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      (2 : ℤ) • diracVector g0 g1 g2 g3 0 p2 (-p1) 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (sigma23 g2 g3) (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      (2 : ℤ) • diracVector g0 g1 g2 g3 0 0 p3 (-p2) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (sigma31 g3 g1) (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      (2 : ℤ) • diracVector g0 g1 g2 g3 0 (-p3) 0 p1 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (boost01 g0 g1) (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      (2 : ℤ) • diracVector g0 g1 g2 g3 p1 p0 0 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (boost02 g0 g2) (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      (2 : ℤ) • diracVector g0 g1 g2 g3 p2 0 p0 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (boost03 g0 g3) (diracVector g0 g1 g2 g3 p0 p1 p2 p3) =
      (2 : ℤ) • diracVector g0 g1 g2 g3 p3 0 0 p0 := by
  have h10 : g1 * g0 + g0 * g1 = 0 := by simpa [add_comm] using h01
  have h20 : g2 * g0 + g0 * g2 = 0 := by simpa [add_comm] using h02
  have h30 : g3 * g0 + g0 * g3 = 0 := by simpa [add_comm] using h03
  have h21 : g2 * g1 + g1 * g2 = 0 := by simpa [add_comm] using h12
  have h31 : g3 * g1 + g1 * g3 = 0 := by simpa [add_comm] using h13
  have h32 : g3 * g2 + g2 * g3 = 0 := by simpa [add_comm] using h23
  have h_pos : ∀ (p : ℤ) (x : B), p • ((2 : ℤ) • x) = (2 : ℤ) • (p • x) := by
    intro p x
    rw [← mul_smul, ← mul_smul, mul_comm]
  have h_neg : ∀ (p : ℤ) (x : B), p • -((2 : ℤ) • x) = (2 : ℤ) • ((-p) • x) := by
    intro p x
    rw [smul_neg, neg_smul, smul_neg, h_pos]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [sigma12]; rw [clifford_bivector_sq g1 g2 h12, h1, h2]; simp
  · dsimp [sigma23]; rw [clifford_bivector_sq g2 g3 h23, h2, h3]; simp
  · dsimp [sigma31]; rw [clifford_bivector_sq g3 g1 h31, h3, h1]; simp
  · dsimp [boost01]; rw [clifford_bivector_sq g0 g1 h01, h0, h1]; simp
  · dsimp [boost02]; rw [clifford_bivector_sq g0 g2 h02, h0, h2]; simp
  · dsimp [boost03]; rw [clifford_bivector_sq g0 g3 h03, h0, h3]; simp
  · dsimp [sigma12]
    rw [comm_diracVector,
      clifford_bivector_comm_orth g1 g2 g0 h10 h20,
      clifford_bivector_comm_left g1 g2 h12,
      clifford_bivector_comm_right g1 g2 h12,
      clifford_bivector_comm_orth g1 g2 g3 h13 h23,
      h1, h2]
    simp only [one_mul, mul_one, diracVector, zero_smul, smul_zero, add_zero, zero_add,
      h_pos, h_neg, smul_add]
    abel
  · dsimp [sigma23]
    rw [comm_diracVector,
      clifford_bivector_comm_orth g2 g3 g0 h20 h30,
      clifford_bivector_comm_orth g2 g3 g1 h21 h31,
      clifford_bivector_comm_left g2 g3 h23,
      clifford_bivector_comm_right g2 g3 h23,
      h2, h3]
    simp only [one_mul, mul_one, diracVector, zero_smul, smul_zero, add_zero, zero_add,
      h_pos, h_neg, smul_add]
    abel
  · dsimp [sigma31]
    rw [comm_diracVector,
      clifford_bivector_comm_orth g3 g1 g0 h30 h10,
      clifford_bivector_comm_right g3 g1 h31,
      clifford_bivector_comm_orth g3 g1 g2 h32 h12,
      clifford_bivector_comm_left g3 g1 h31,
      h3, h1]
    simp only [one_mul, mul_one, diracVector, zero_smul, smul_zero, add_zero, zero_add,
      h_pos, h_neg, smul_add]
    abel
  · dsimp [boost01]
    rw [comm_diracVector,
      clifford_bivector_comm_left g0 g1 h01,
      clifford_bivector_comm_right g0 g1 h01,
      clifford_bivector_comm_orth g0 g1 g2 h02 h12,
      clifford_bivector_comm_orth g0 g1 g3 h03 h13,
      h0, h1]
    simp only [neg_mul, one_mul, mul_one, smul_neg, neg_neg, diracVector,
      zero_smul, smul_zero, add_zero, h_pos, smul_add]
    abel
  · dsimp [boost02]
    rw [comm_diracVector,
      clifford_bivector_comm_left g0 g2 h02,
      clifford_bivector_comm_orth g0 g2 g1 h01 h21,
      clifford_bivector_comm_right g0 g2 h02,
      clifford_bivector_comm_orth g0 g2 g3 h03 h23,
      h0, h2]
    simp only [neg_mul, one_mul, mul_one, smul_neg, neg_neg, diracVector,
      zero_smul, smul_zero, add_zero, h_pos, smul_add]
    abel
  · dsimp [boost03]
    rw [comm_diracVector,
      clifford_bivector_comm_left g0 g3 h03,
      clifford_bivector_comm_orth g0 g3 g1 h01 h31,
      clifford_bivector_comm_orth g0 g3 g2 h02 h32,
      clifford_bivector_comm_right g0 g3 h03,
      h0, h3]
    simp only [neg_mul, one_mul, mul_one, smul_neg, neg_neg, diracVector,
      zero_smul, smul_zero, add_zero, h_pos, smul_add]
    abel

/-! ## §2. General `[Ring B]` Peirce-Corner Nilpotence and Corner-Preserving Lorentz Action -/

/-- The upper Peirce corner $P x (1 - P)$ associated to an idempotent `P`. -/
def upperCorner {B : Type*} [Ring B] (P x : B) : B := P * x * (1 - P)

/-- The even-grade (block-diagonal) projection $P L P + (1 - P) L (1 - P)$ associated to `P`. -/
def evenBlock {B : Type*} [Ring B] (P L : B) : B := P * L * P + (1 - P) * L * (1 - P)

/-- Two elements of the same upper Peirce corner have zero product. -/
theorem upperCorner_mul_eq_zero {B : Type*} [Ring B]
    (P x y : B) (hP : P * P = P) :
    upperCorner P x * upperCorner P y = 0 := by
  have hP_assoc : ∀ z : B, P * (P * z) = P * z :=
    fun z => by rw [← mul_assoc, hP]
  dsimp [upperCorner]
  simp only [sub_mul, mul_sub, mul_one, mul_assoc, hP_assoc]
  abel

/-- The commutator of any two upper-corner elements vanishes. -/
theorem upperCorner_commute {B : Type*} [Ring B]
    (P x y : B) (hP : P * P = P) :
    upperCorner P x * upperCorner P y -
      upperCorner P y * upperCorner P x = 0 := by
  rw [upperCorner_mul_eq_zero P x y hP,
    upperCorner_mul_eq_zero P y x hP]
  simp

/-- **General Corner-Preserving Lorentz Action & Semidirect Poincaré Law (`upperCorner_lorentz_conjugation_and_commutator`)**:
In any associative ring `[Ring B]` with idempotent `P * P = P`:
1. **Idempotence of `upperCorner P`**: `upperCorner P (upperCorner P x) = upperCorner P x`.
2. **Group Conjugation Preserving `upperCorner P`**:
   For any `G, G_inv : B` commuting with `P` (`P * G = G * P` and `P * G_inv = G_inv * P`),
   conjugation `G * upperCorner P x * G_inv` equals `upperCorner P (G * x * G_inv)` and therefore
   lies strictly inside `upperCorner P`.
3. **Unipotent Poincaré Semidirect Product Law**:
   If in addition `G * G_inv = 1`, then `G * (1 + upperCorner P x) * G_inv = 1 + upperCorner P (G * x * G_inv)`.
4. **Even-Grade Lie Algebra Action Preserving `upperCorner P`**:
   For any `L : B`, the commutator `evenBlock P L * upperCorner P x - upperCorner P x * evenBlock P L`
   lies strictly inside `upperCorner P`.
5. **Lifting a Lorentz Representation into `upperCorner P`**:
   For any `L, W, V : B` where `L` commutes with `P` and `W` (`P * L = L * P`, `W * L = L * W`),
   the commutator with the corner-embedded translation `upperCorner P (W * V)` satisfies
   `L * upperCorner P (W * V) - upperCorner P (W * V) * L = upperCorner P (W * (L * V - V * L))`. -/
theorem upperCorner_lorentz_conjugation_and_commutator {B : Type*} [Ring B]
    (P x G G_inv L W V : B) (hP : P * P = P)
    (hPG : P * G = G * P) (hPGinv : P * G_inv = G_inv * P)
    (hGGinv : G * G_inv = 1)
    (hPL : P * L = L * P) (hWL : W * L = L * W) :
    upperCorner P (upperCorner P x) = upperCorner P x ∧
    G * upperCorner P x * G_inv = upperCorner P (G * x * G_inv) ∧
    upperCorner P (G * upperCorner P x * G_inv) = G * upperCorner P x * G_inv ∧
    G * (1 + upperCorner P x) * G_inv = 1 + upperCorner P (G * x * G_inv) ∧
    upperCorner P (evenBlock P L * upperCorner P x - upperCorner P x * evenBlock P L) =
      evenBlock P L * upperCorner P x - upperCorner P x * evenBlock P L ∧
    L * upperCorner P (W * V) - upperCorner P (W * V) * L =
      upperCorner P (W * (L * V - V * L)) := by
  have hP_assoc : ∀ z : B, P * (P * z) = P * z :=
    fun z => by rw [← mul_assoc, hP]
  have hGinv_sub : (1 - P) * G_inv = G_inv * (1 - P) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPGinv]
  have hL_sub : (1 - P) * L = L * (1 - P) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPL]
  have h_idem : ∀ y : B, upperCorner P (upperCorner P y) = upperCorner P y := by
    intro y
    dsimp [upperCorner]
    simp only [sub_mul, mul_sub, mul_one, mul_assoc, hP, hP_assoc]
    abel
  have h_conj : G * upperCorner P x * G_inv = upperCorner P (G * x * G_inv) := by
    dsimp [upperCorner]
    calc
      G * (P * x * (1 - P)) * G_inv = (G * P) * x * ((1 - P) * G_inv) := by
        simp only [mul_assoc]
      _ = (P * G) * x * (G_inv * (1 - P)) := by rw [← hPG, hGinv_sub]
      _ = P * (G * x * G_inv) * (1 - P) := by simp only [mul_assoc]
  refine ⟨h_idem x, h_conj, ?_, ?_, ?_, ?_⟩
  · rw [h_conj, h_idem]
  · calc
      G * (1 + upperCorner P x) * G_inv = G * G_inv + G * upperCorner P x * G_inv := by
        simp only [mul_add, add_mul, mul_one]
      _ = 1 + upperCorner P (G * x * G_inv) := by rw [hGGinv, h_conj]
  · dsimp [upperCorner, evenBlock]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, hP_assoc]
    abel
  · dsimp [upperCorner]
    calc
      L * (P * (W * V) * (1 - P)) - P * (W * V) * (1 - P) * L
        = (L * P) * (W * V) * (1 - P) - P * (W * V) * ((1 - P) * L) := by
          simp only [mul_assoc]
      _ = (P * L) * (W * V) * (1 - P) - P * (W * V) * (L * (1 - P)) := by
          rw [← hPL, hL_sub]
      _ = P * ((L * W) * V) * (1 - P) - P * (W * (V * L)) * (1 - P) := by
          simp only [mul_assoc]
      _ = P * ((W * L) * V) * (1 - P) - P * (W * (V * L)) * (1 - P) := by
          rw [← hWL]
      _ = P * (W * (L * V - V * L)) * (1 - P) := by
          noncomm_ring

/-! ## §3. Concrete 4-Dimensional Translation Module in `upperCorner dtMatP1` and Corner-Preserving Spinorial Lorentz Action -/

/-- First basis matrix $T_0 = P_1 \Phi_1 (1 - P_1) = E_{01} \otimes I_2$ of `upperCorner dtMatP1`. -/
def cornerBasis0 : Mat4Z := upperCorner dtMatP1 dtMatPhi1

/-- Second basis matrix $T_1 = P_1 (\Phi_1 S_2) (1 - P_1) = E_{01} \otimes S_0$ of `upperCorner dtMatP1`. -/
def cornerBasis1 : Mat4Z := upperCorner dtMatP1 (dtMatPhi1 * dtMatS2)

/-- Third basis matrix $T_2 = P_1 (\Phi_1 \Phi_2) (1 - P_1) = E_{01} \otimes \Phi_0$ of `upperCorner dtMatP1`. -/
def cornerBasis2 : Mat4Z := upperCorner dtMatP1 (dtMatPhi1 * dtMatPhi2)

/-- Fourth basis matrix $T_3 = P_1 (\Phi_1 J_2) (1 - P_1) = E_{01} \otimes J_0$ of `upperCorner dtMatP1`. -/
def cornerBasis3 : Mat4Z := upperCorner dtMatP1 (dtMatPhi1 * dtMatJ2)

/-- **The 4-Dimensional Upper Peirce-Corner Translation Element (`cornerTranslation`)**:
Embeds a 4-momentum $(p_0, p_1, p_2, p_3) \in \mathbb{Z}^4$ into the upper Peirce corner
`upperCorner dtMatP1` as $\begin{pmatrix} 0 & p_0 I_0 + p_1 S_0 + p_2 \Phi_0 + p_3 J_0 \\ 0 & 0 \end{pmatrix}$. -/
def cornerTranslation (p0 p1 p2 p3 : ℤ) : Mat4Z :=
  p0 • cornerBasis0 + p1 • cornerBasis1 + p2 • cornerBasis2 + p3 • cornerBasis3

/-- **The Dual Lower Peirce-Corner Adjugate Translation (`dualCornerTranslation`)**:
Embeds $(p_0, p_1, p_2, p_3) \in \mathbb{Z}^4$ into the lower Peirce corner
$(1 - P_1) \mathrm{Mat}_4(\mathbb{Z}) P_1$ as $\begin{pmatrix} 0 & 0 \\ p_0 I_0 - p_1 S_0 - p_2 \Phi_0 - p_3 J_0 & 0 \end{pmatrix}$. -/
def dualCornerTranslation (p0 p1 p2 p3 : ℤ) : Mat4Z :=
  (1 - dtMatP1) *
    (p0 • dtMatPhi1 - p1 • (dtMatPhi1 * dtMatS2) -
     p2 • (dtMatPhi1 * dtMatPhi2) - p3 • (dtMatPhi1 * dtMatJ2)) * dtMatP1

def dtMatQ1 : Mat4Z := 1 - dtMatP1

theorem one_sub_dtMatP1 :
    (1 : Mat4Z) - dtMatP1 = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem cornerBasis0_eq :
    cornerBasis0 = !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem cornerBasis1_eq :
    cornerBasis1 = !![0, 0, 1, 0; 0, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem cornerBasis2_eq :
    cornerBasis2 = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem cornerBasis3_eq :
    cornerBasis3 = !![0, 0, 0, 1; 0, 0, -1, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem lowerBasis0_eq :
    dtMatQ1 * dtMatPhi1 * dtMatP1 =
      !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem lowerBasis1_eq :
    dtMatQ1 * (dtMatPhi1 * dtMatS2) * dtMatP1 =
      !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, -1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem lowerBasis2_eq :
    dtMatQ1 * (dtMatPhi1 * dtMatPhi2) * dtMatP1 =
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem lowerBasis3_eq :
    dtMatQ1 * (dtMatPhi1 * dtMatJ2) * dtMatP1 =
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; -1, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem cornerTranslation_eq (p0 p1 p2 p3 : ℤ) :
    cornerTranslation p0 p1 p2 p3 =
      !![0, 0, p0 + p1, p2 + p3;
         0, 0, p2 - p3, p0 - p1;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cornerTranslation, cornerBasis0_eq, cornerBasis1_eq, cornerBasis2_eq, cornerBasis3_eq] <;>
    ring

theorem dualCornerTranslation_eq (p0 p1 p2 p3 : ℤ) :
    dualCornerTranslation p0 p1 p2 p3 =
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         p0 - p1, -p2 - p3, 0, 0;
         -p2 + p3, p0 + p1, 0, 0] := by
  change dtMatQ1 *
      (p0 • dtMatPhi1 - p1 • (dtMatPhi1 * dtMatS2) -
       p2 • (dtMatPhi1 * dtMatPhi2) - p3 • (dtMatPhi1 * dtMatJ2)) * dtMatP1 = _
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    lowerBasis0_eq, lowerBasis1_eq, lowerBasis2_eq, lowerBasis3_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Faithful 4-Dimensional Translation Module Inside `upperCorner dtMatP1` (`cornerTranslation_mem_upperCorner_and_faithful`)**:
1. **Strict Upper-Corner Membership**:
   `upperCorner dtMatP1 (cornerTranslation p0 p1 p2 p3) = cornerTranslation p0 p1 p2 p3`.
2. **4D Additivity**:
   `cornerTranslation (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) = cornerTranslation p0 p1 p2 p3 + cornerTranslation q0 q1 q2 q3`.
3. **Faithfulness (4-Dimensional $\mathbb{Z}$-Linear Independence)**:
   `cornerTranslation p0 p1 p2 p3 = 0 ↔ p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0`.
4. **Abelian Nilpotent Corner Product & Unipotent Translation Group Law**:
   `cornerTranslation p0 p1 p2 p3 * cornerTranslation q0 q1 q2 q3 = 0` and
   `(1 + cornerTranslation p0 p1 p2 p3) * (1 + cornerTranslation q0 q1 q2 q3) = 1 + cornerTranslation (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3)`. -/
theorem cornerTranslation_mem_upperCorner_and_faithful (p0 p1 p2 p3 q0 q1 q2 q3 : ℤ) :
    upperCorner dtMatP1 (cornerTranslation p0 p1 p2 p3) = cornerTranslation p0 p1 p2 p3 ∧
    cornerTranslation (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) =
      cornerTranslation p0 p1 p2 p3 + cornerTranslation q0 q1 q2 q3 ∧
    (cornerTranslation p0 p1 p2 p3 = 0 ↔ p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0) ∧
    cornerTranslation p0 p1 p2 p3 * cornerTranslation q0 q1 q2 q3 = 0 ∧
    (1 + cornerTranslation p0 p1 p2 p3) * (1 + cornerTranslation q0 q1 q2 q3) =
      1 + cornerTranslation (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) := by
  have h_add :
      cornerTranslation (p0 + q0) (p1 + q1) (p2 + q2) (p3 + q3) =
        cornerTranslation p0 p1 p2 p3 + cornerTranslation q0 q1 q2 q3 := by
    rw [cornerTranslation_eq, cornerTranslation_eq, cornerTranslation_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have h_mul : cornerTranslation p0 p1 p2 p3 * cornerTranslation q0 q1 q2 q3 = 0 := by
    rw [cornerTranslation_eq, cornerTranslation_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨?_, h_add, ?_, h_mul, ?_⟩
  · dsimp [upperCorner]
    rw [one_sub_dtMatP1, cornerTranslation_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dtMatP1]
  · constructor
    · intro h
      have h02 : cornerTranslation p0 p1 p2 p3 0 2 = 0 := by rw [h]; rfl
      have h13 : cornerTranslation p0 p1 p2 p3 1 3 = 0 := by rw [h]; rfl
      have h03 : cornerTranslation p0 p1 p2 p3 0 3 = 0 := by rw [h]; rfl
      have h12 : cornerTranslation p0 p1 p2 p3 1 2 = 0 := by rw [h]; rfl
      simp [cornerTranslation_eq] at h02 h13 h03 h12
      refine ⟨by omega, by omega, by omega, by omega⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      ext i j
      fin_cases i <;> fin_cases j <;> decide
  · simp only [add_mul, mul_add, one_mul, mul_one, h_mul, add_zero, h_add, add_assoc]

set_option maxHeartbeats 800000 in
/-- **Corner-Preserving Spinorial Lorentz Action & Quadratic Norm on `cornerTranslation` (`cornerTranslation_lorentz_action_and_quadratic_norm`)**:
1. **Block-Diagonal Commutation with `dtMatP1`**:
   The Bit-2 $\mathfrak{sl}_2(\mathbb{R})$ generators `dtMatJ2`, `dtMatS2`, `dtMatPhi2` all commute
   with the Peirce idempotent `dtMatP1`.
2. **Lie Algebra Action Preserving `cornerTranslation`**:
   - `[dtMatJ2, cornerTranslation p0 p1 p2 p3] = 2 • cornerTranslation 0 p2 (-p1) 0` (rotation in the $(p_1, p_2)$ plane),
   - `[dtMatS2, cornerTranslation p0 p1 p2 p3] = 2 • cornerTranslation 0 0 p3 p2` (boost in the $(p_2, p_3)$ plane),
   - `[dtMatPhi2, cornerTranslation p0 p1 p2 p3] = 2 • cornerTranslation 0 (-p3) 0 (-p1)` (boost in the $(p_1, p_3)$ plane).
3. **Group Conjugation & Chiral Spinor Action Preserving `cornerTranslation`**:
   - Conjugation by `dtMatJ2` ($J_2^{-1} = -J_2$):
     `dtMatJ2 * cornerTranslation p0 p1 p2 p3 * (-dtMatJ2) = cornerTranslation p0 (-p1) (-p2) p3`,
   - Left chiral spinor rotation by `dtMatJ2`:
     `dtMatJ2 * cornerTranslation p0 p1 p2 p3 = cornerTranslation (-p3) p2 (-p1) p0`.
4. **Quadratic Norm Pairing on the Upper Corner**:
   `cornerTranslation p0 p1 p2 p3 * dualCornerTranslation p0 p1 p2 p3 = (p0 ^ 2 - p1 ^ 2 - p2 ^ 2 + p3 ^ 2) • dtMatP1`,
   which is strictly preserved under the Lorentz conjugation `p1 ↦ -p1, p2 ↦ -p2` and chiral rotation `(p0, p1, p2, p3) ↦ (-p3, p2, -p1, p0)`. -/
theorem cornerTranslation_lorentz_action_and_quadratic_norm (p0 p1 p2 p3 : ℤ) :
    (dtMatP1 * dtMatJ2 = dtMatJ2 * dtMatP1 ∧
     dtMatP1 * dtMatS2 = dtMatS2 * dtMatP1 ∧
     dtMatP1 * dtMatPhi2 = dtMatPhi2 * dtMatP1) ∧
    dtMatJ2 * cornerTranslation p0 p1 p2 p3 - cornerTranslation p0 p1 p2 p3 * dtMatJ2 =
      2 • cornerTranslation 0 p2 (-p1) 0 ∧
    dtMatS2 * cornerTranslation p0 p1 p2 p3 - cornerTranslation p0 p1 p2 p3 * dtMatS2 =
      2 • cornerTranslation 0 0 p3 p2 ∧
    dtMatPhi2 * cornerTranslation p0 p1 p2 p3 - cornerTranslation p0 p1 p2 p3 * dtMatPhi2 =
      2 • cornerTranslation 0 (-p3) 0 (-p1) ∧
    dtMatJ2 * cornerTranslation p0 p1 p2 p3 * (-dtMatJ2) =
      cornerTranslation p0 (-p1) (-p2) p3 ∧
    dtMatJ2 * cornerTranslation p0 p1 p2 p3 =
      cornerTranslation (-p3) p2 (-p1) p0 ∧
    cornerTranslation p0 p1 p2 p3 * dualCornerTranslation p0 p1 p2 p3 =
      (p0 ^ 2 - p1 ^ 2 - p2 ^ 2 + p3 ^ 2) • dtMatP1 ∧
    cornerTranslation (-p3) p2 (-p1) p0 * dualCornerTranslation (-p3) p2 (-p1) p0 =
      cornerTranslation p0 p1 p2 p3 * dualCornerTranslation p0 p1 p2 p3 := by
  have h_norm :
      ∀ q0 q1 q2 q3 : ℤ,
        cornerTranslation q0 q1 q2 q3 * dualCornerTranslation q0 q1 q2 q3 =
          (q0 ^ 2 - q1 ^ 2 - q2 ^ 2 + q3 ^ 2) • dtMatP1 := by
    intro q0 q1 q2 q3
    rw [cornerTranslation_eq, dualCornerTranslation_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatP1] <;> ring
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, h_norm p0 p1 p2 p3, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · rw [cornerTranslation_eq, cornerTranslation_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatJ2] <;> ring
  · rw [cornerTranslation_eq, cornerTranslation_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatS2] <;> ring
  · rw [cornerTranslation_eq, cornerTranslation_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatPhi2] <;> ring
  · rw [cornerTranslation_eq, cornerTranslation_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatJ2] <;> ring
  · rw [cornerTranslation_eq, cornerTranslation_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatJ2] <;> ring
  · rw [h_norm, h_norm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dtMatP1] <;> ring

/-! ## §4. Real Two-Spinor Null and Massive Determinant Identities -/

/-- The symmetric rank-one momentum matrix $\lambda \lambda^\top$ in `Matrix (Fin 2) (Fin 2) ℝ`. -/
def rankOneMomentum (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a ^ 2, a * b; a * b, b ^ 2]

/-- The determinant of the sum of two real rank-one momenta. -/
def twoSpinorDet (a b c d : ℝ) : ℝ :=
  (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2

/-- The alternating real two-spinor pairing $\langle \lambda, \tilde\lambda \rangle = a d - b c$. -/
def spinorPairing (a b c d : ℝ) : ℝ := a * d - b * c

/-- A single real spinor gives a rank-one, hence null, symmetric momentum matrix. -/
theorem rankOneMomentum_det_zero (a b : ℝ) :
    (rankOneMomentum a b).det = 0 := by
  simp [rankOneMomentum, Matrix.det_fin_two]
  ring

/-- Two real rank-one momentum matrices have determinant equal to the square of
the alternating spinor pairing. -/
theorem twoSpinorDet_eq_pairing_sq (a b c d : ℝ) :
    twoSpinorDet a b c d = spinorPairing a b c d ^ 2 := by
  simp [twoSpinorDet, spinorPairing]
  ring

/-- The two-spinor determinant is nonnegative over `ℝ`. -/
theorem twoSpinorDet_nonneg (a b c d : ℝ) :
    0 ≤ twoSpinorDet a b c d := by
  rw [twoSpinorDet_eq_pairing_sq]
  exact sq_nonneg _

end InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge
