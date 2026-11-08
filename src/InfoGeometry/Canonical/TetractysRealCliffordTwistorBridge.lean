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

/-- Integer-coefficient Dirac 4-vector $V(p) = p_0 \gamma_0 + p_1 \gamma_1 + p_2 \gamma_2 + p_3 \gamma_3$. -/
def diracVector (p0 p1 p2 p3 : ℤ) : Mat4Z :=
  p0 • gamma0 + p1 • gamma1 + p2 • gamma2 + p3 • gamma3

/-- The square of the concrete Dirac vector is its `(-,+,+,+)` Minkowski quadratic form. -/
theorem diracVector_square (p0 p1 p2 p3 : ℤ) :
    diracVector p0 p1 p2 p3 * diracVector p0 p1 p2 p3 =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : Mat4Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracVector, gamma0, gamma1, gamma2, gamma3,
      dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
      Matrix.mul_apply, Matrix.smul_apply] <;> ring

/-- **Faithfulness of the 4-Dimensional Dirac Translation Module (`diracVector_eq_zero_iff`)**:
The four generators `gamma0, gamma1, gamma2, gamma3` are $\mathbb{Z}$-linearly independent, so
`diracVector p0 p1 p2 p3 = 0` if and only if `p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0`. -/
theorem diracVector_eq_zero_iff (p0 p1 p2 p3 : ℤ) :
    diracVector p0 p1 p2 p3 = 0 ↔ p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 := by
  constructor
  · intro h
    have h00 : diracVector p0 p1 p2 p3 0 0 = 0 := by rw [h]; rfl
    have h02 : diracVector p0 p1 p2 p3 0 2 = 0 := by rw [h]; rfl
    have h13 : diracVector p0 p1 p2 p3 1 3 = 0 := by rw [h]; rfl
    have h03 : diracVector p0 p1 p2 p3 0 3 = 0 := by rw [h]; rfl
    change p1 = 0 at h00
    change p0 + p2 = 0 at h02
    change p0 - p2 = 0 at h13
    change p3 = 0 at h03
    refine ⟨by omega, h00, by omega, h03⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- Spatial rotation bivector $\Sigma_{12} = \gamma_1 \gamma_2$ ($\Sigma_{12}^2 = -I_4$). -/
def sigma12 : Mat4Z := gamma1 * gamma2

/-- Spatial rotation bivector $\Sigma_{23} = \gamma_2 \gamma_3$ ($\Sigma_{23}^2 = -I_4$). -/
def sigma23 : Mat4Z := gamma2 * gamma3

/-- Spatial rotation bivector $\Sigma_{31} = \gamma_3 \gamma_1$ ($\Sigma_{31}^2 = -I_4$). -/
def sigma31 : Mat4Z := gamma3 * gamma1

/-- Lorentz boost bivector $K_{01} = \gamma_0 \gamma_1$ ($K_{01}^2 = +I_4$). -/
def boost01 : Mat4Z := gamma0 * gamma1

/-- Lorentz boost bivector $K_{02} = \gamma_0 \gamma_2$ ($K_{02}^2 = +I_4$). -/
def boost02 : Mat4Z := gamma0 * gamma2

/-- Lorentz boost bivector $K_{03} = \gamma_0 \gamma_3$ ($K_{03}^2 = +I_4$). -/
def boost03 : Mat4Z := gamma0 * gamma3

/-- **6-Generator $\mathfrak{so}(3,1)$ Lorentz Bivector Action on the 4D Dirac Translation Module (`so31_bivector_squares_and_diracVector_action`)**:
1. The three spatial rotation bivectors satisfy $\Sigma_{12}^2 = \Sigma_{23}^2 = \Sigma_{31}^2 = -I_4$,
   and the three boost bivectors satisfy $K_{01}^2 = K_{02}^2 = K_{03}^2 = +I_4$.
2. Under the commutator action $[B, V] = B V - V B$, all six $\mathfrak{so}(3,1)$ bivectors preserve
   the 4-dimensional module `diracVector p0 p1 p2 p3` with the exact $(1,3)$ Minkowski Lorentz
   rotation and boost laws:
   - $[\Sigma_{12}, V(p_0, p_1, p_2, p_3)] = 2 \cdot V(0, p_2, -p_1, 0)$,
   - $[\Sigma_{23}, V(p_0, p_1, p_2, p_3)] = 2 \cdot V(0, 0, p_3, -p_2)$,
   - $[\Sigma_{31}, V(p_0, p_1, p_2, p_3)] = 2 \cdot V(0, -p_3, 0, p_1)$,
   - $[K_{01}, V(p_0, p_1, p_2, p_3)] = 2 \cdot V(p_1, p_0, 0, 0)$,
   - $[K_{02}, V(p_0, p_1, p_2, p_3)] = 2 \cdot V(p_2, 0, p_0, 0)$,
   - $[K_{03}, V(p_0, p_1, p_2, p_3)] = 2 \cdot V(p_3, 0, 0, p_0)$. -/
theorem so31_bivector_squares_and_diracVector_action (p0 p1 p2 p3 : ℤ) :
    (sigma12 * sigma12 = -1 ∧ sigma23 * sigma23 = -1 ∧ sigma31 * sigma31 = -1 ∧
     boost01 * boost01 = 1 ∧ boost02 * boost02 = 1 ∧ boost03 * boost03 = 1) ∧
    sigma12 * diracVector p0 p1 p2 p3 - diracVector p0 p1 p2 p3 * sigma12 =
      2 • diracVector 0 p2 (-p1) 0 ∧
    sigma23 * diracVector p0 p1 p2 p3 - diracVector p0 p1 p2 p3 * sigma23 =
      2 • diracVector 0 0 p3 (-p2) ∧
    sigma31 * diracVector p0 p1 p2 p3 - diracVector p0 p1 p2 p3 * sigma31 =
      2 • diracVector 0 (-p3) 0 p1 ∧
    boost01 * diracVector p0 p1 p2 p3 - diracVector p0 p1 p2 p3 * boost01 =
      2 • diracVector p1 p0 0 0 ∧
    boost02 * diracVector p0 p1 p2 p3 - diracVector p0 p1 p2 p3 * boost02 =
      2 • diracVector p2 0 p0 0 ∧
    boost03 * diracVector p0 p1 p2 p3 - diracVector p0 p1 p2 p3 * boost03 =
      2 • diracVector p3 0 0 p0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigma12, diracVector, gamma0, gamma1, gamma2, gamma3,
        dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigma23, diracVector, gamma0, gamma1, gamma2, gamma3,
        dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigma31, diracVector, gamma0, gamma1, gamma2, gamma3,
        dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boost01, diracVector, gamma0, gamma1, gamma2, gamma3,
        dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boost02, diracVector, gamma0, gamma1, gamma2, gamma3,
        dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boost03, diracVector, gamma0, gamma1, gamma2, gamma3,
        dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring

/-! ## §2. General `[Ring B]` Peirce-Corner Nilpotence and Corner-Preserving Lorentz Action -/

/-- The upper Peirce corner $P x (1 - P)$ associated to an idempotent `P`. -/
def upperCorner {B : Type*} [Ring B] (P x : B) : B := P * x * (1 - P)

/-- The even-grade (block-diagonal) projection $P L P + (1 - P) L (1 - P)$ associated to `P`. -/
def evenBlock {B : Type*} [Ring B] (P L : B) : B := P * L * P + (1 - P) * L * (1 - P)

/-- Two elements of the same upper Peirce corner have zero product. -/
theorem upperCorner_mul_eq_zero {B : Type*} [Ring B]
    (P x y : B) (hP : P * P = P) :
    upperCorner P x * upperCorner P y = 0 := by
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP]
    abel
  dsimp [upperCorner]
  rw [mul_assoc, mul_assoc, ← mul_assoc (P * x), hQP]
  simp

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
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hP, hP_assoc]
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
          simp only [mul_sub, sub_mul, mul_assoc]

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
  have h_mul : cornerTranslation p0 p1 p2 p3 * cornerTranslation q0 q1 q2 q3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply]
  refine ⟨?_, ?_, ?_, h_mul, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · constructor
    · intro h
      have h02 : cornerTranslation p0 p1 p2 p3 0 2 = 0 := by rw [h]; rfl
      have h13 : cornerTranslation p0 p1 p2 p3 1 3 = 0 := by rw [h]; rfl
      have h03 : cornerTranslation p0 p1 p2 p3 0 3 = 0 := by rw [h]; rfl
      have h12 : cornerTranslation p0 p1 p2 p3 1 2 = 0 := by rw [h]; rfl
      change p0 + p1 = 0 at h02
      change p0 - p1 = 0 at h13
      change p2 + p3 = 0 at h03
      change p2 - p3 = 0 at h12
      refine ⟨by omega, by omega, by omega, by omega⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      ext i j
      fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring

/-- **Corner-Preserving Spinorial Lorentz Action & Quadratic Norm on `cornerTranslation` (`cornerTranslation_lorentz_action_and_quadratic_norm`)**:
1. **Block-Diagonal Commutation with `dtMatP1`**:
   The Bit-2 $\mathfrak{sl}_2(\mathbb{R})$ generators `dtMatJ2`, `dtMatS2`, `dtMatPhi2` all commute
   with the Peirce idempotent `dtMatP1`.
2. **Lie Algebra Action Preserving `cornerTranslation`**:
   - `[dtMatJ2, cornerTranslation p0 p1 p2 p3] = 2 • cornerTranslation 0 (-p2) p1 0` (rotation in the $(p_1, p_2)$ plane),
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
      2 • cornerTranslation 0 (-p2) p1 0 ∧
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
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j; fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, dualCornerTranslation,
        cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cornerTranslation, dualCornerTranslation,
        cornerBasis0, cornerBasis1, cornerBasis2, cornerBasis3,
        upperCorner, dtMatP1, dtMatPhi1, dtMatS2, dtMatPhi2, dtMatJ2,
        Matrix.mul_apply, Matrix.smul_apply] <;> ring

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
