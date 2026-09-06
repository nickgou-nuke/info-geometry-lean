/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.Algebra.Clifford

/-!
# Hestenes-Krein Algebraic Bivector Lift and 12-Fold Cyclotomic Phase

This module formalizes the purely algebraic, transcendental-free construction of the
12th root of unity and spin Coxeter holonomy using Geometric Algebra (Clifford bivectors)
and Krein chiral symmetry.

Key Theorems:
1. `bivector_pow_four`: $B^2 = -I \implies B^4 = I$.
2. 🏆 `cyclotomic_phase_cube`: For $Z = \frac{1}{2}(\sqrt{3} I + B)$, $Z^3 = B$.
3. 🏆 `cyclotomic_phase_pow_six`: $Z^6 = (Z^3)^2 = B^2 = -I$.
4. 🏆 `cyclotomic_phase_pow_twelve`: $Z^{12} = (Z^6)^2 = (-I)^2 = I$.
5. 🏆 `krein_involution_projectors_sum`: Fundamental symmetry $J^2 = 1$ generates
   orthogonal chiral projectors $\Pi_\pm = \frac{1}{2}(I \pm J)$ with $\Pi_+ + \Pi_- = I$.
6. 🏆 `krein_involution_projectors_ortho`: $\Pi_+ \Pi_- = 0$.
-/

section BivectorLift

variable {R : Type*} [CommRing R]

/-- A spatial/elliptic bivector is an operator whose square is $-I$. -/
def IsChiralBivector {M : Type*} [AddCommGroup M] [Module R M]
    (B : Module.End R M) : Prop :=
  B ^ 2 = -1

/-- A Krein chiral fundamental symmetry is an involution operator whose square is $+I$. -/
def IsKreinInvolution {M : Type*} [AddCommGroup M] [Module R M]
    (J : Module.End R M) : Prop :=
  J ^ 2 = 1

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem neg_one_sq_op : (-1 : Module.End R M) ^ 2 = 1 := by
  ext v
  calc
    (((-1 : Module.End R M) ^ 2)) v = (-1 : Module.End R M) ((-1 : Module.End R M) v) := rfl
    _ = - ((-1 : Module.End R M) v) := LinearMap.neg_apply 1 ((-1 : Module.End R M) v)
    _ = - (- (1 : Module.End R M) v) := by rw [LinearMap.neg_apply]
    _ = (1 : Module.End R M) v := neg_neg _

theorem bivector_sq_eval (B : Module.End R M) (hB : IsChiralBivector B) (v : M) :
    B (B v) = -v := by
  have h := congr_fun (congr_arg DFunLike.coe hB) v
  exact h

/-- 🏆 THEOREM 1: Bivector powers of order 4: $B^4 = I$. -/
theorem bivector_pow_four (B : Module.End R M) (hB : IsChiralBivector B) :
    B ^ 4 = 1 := by
  have h4 : B ^ 4 = (B ^ 2) ^ 2 := by
    have h_mul : (2 : ℕ) * 2 = 4 := rfl
    rw [← pow_mul, h_mul]
  rw [h4, hB, neg_one_sq_op]

theorem bivector_shift_sq
    (B : Module.End R M) (sqrt3 : R)
    (h3 : sqrt3 ^ 2 = 3)
    (hB : IsChiralBivector B) :
    (sqrt3 • (1 : Module.End R M) + B) ^ 2 = (2 : R) • (1 : Module.End R M) + (2 * sqrt3) • B := by
  ext v
  have hB2 := bivector_sq_eval B hB v
  have h_left : ((sqrt3 • (1 : Module.End R M) + B) ^ 2) v =
      sqrt3 • (sqrt3 • v + B v) + B (sqrt3 • v + B v) := rfl
  rw [h_left, smul_add, map_add, smul_smul, LinearMap.map_smul, hB2]
  have h_sq3 : sqrt3 * sqrt3 = (3 : R) := by rw [← sq, h3]
  have h_two_b : sqrt3 • B v + sqrt3 • B v = (2 * sqrt3) • B v := by
    calc
      sqrt3 • B v + sqrt3 • B v = (1 + 1 : R) • (sqrt3 • B v) := by module
      _ = (2 : R) • (sqrt3 • B v) := by ring_nf
      _ = (2 * sqrt3) • B v := by rw [smul_smul]
  have h_three_v : (3 : R) • v + -v = (2 : R) • v := by
    calc
      (3 : R) • v + -v = (3 : R) • v - (1 : R) • v := by rw [one_smul, sub_eq_add_neg]
      _ = (3 - 1 : R) • v := by rw [sub_smul]
      _ = (2 : R) • v := by ring_nf
  simp only [LinearMap.add_apply, LinearMap.smul_apply, h_sq3]
  calc
    (3 : R) • v + sqrt3 • B v + (sqrt3 • B v + -v) =
        ((3 : R) • v + -v) + (sqrt3 • B v + sqrt3 • B v) := by module
    _ = (2 : R) • v + (2 * sqrt3) • B v := by rw [h_three_v, h_two_b]

theorem bivector_shift_cube
    (B : Module.End R M) (sqrt3 : R)
    (h3 : sqrt3 ^ 2 = 3)
    (hB : IsChiralBivector B) :
    (sqrt3 • (1 : Module.End R M) + B) ^ 3 = (8 : R) • B := by
  have h_pow3 : (sqrt3 • (1 : Module.End R M) + B) ^ 3 =
      (sqrt3 • (1 : Module.End R M) + B) * (sqrt3 • (1 : Module.End R M) + B) ^ 2 := by
    calc
      (sqrt3 • (1 : Module.End R M) + B) ^ 3 = (sqrt3 • (1 : Module.End R M) + B) ^ (1 + 2) := rfl
      _ = (sqrt3 • (1 : Module.End R M) + B) ^ 1 * (sqrt3 • (1 : Module.End R M) + B) ^ 2 := by rw [pow_add]
      _ = _ := by rw [pow_one]
  rw [h_pow3, bivector_shift_sq B sqrt3 h3 hB]
  ext v
  have hB2 := bivector_sq_eval B hB v
  have h_left : ((sqrt3 • (1 : Module.End R M) + B) * ((2 : R) • (1 : Module.End R M) + (2 * sqrt3) • B)) v =
      sqrt3 • ((2 : R) • v + (2 * sqrt3) • B v) + B ((2 : R) • v + (2 * sqrt3) • B v) := rfl
  rw [h_left, smul_add, map_add, smul_smul, smul_smul, LinearMap.map_smul, LinearMap.map_smul, hB2]
  have h_sq3 : sqrt3 * (2 * sqrt3) = (6 : R) := by
    calc
      sqrt3 * (2 * sqrt3) = 2 * (sqrt3 * sqrt3) := by ring
      _ = 2 * (sqrt3 ^ 2) := by rw [sq]
      _ = 2 * 3 := by rw [h3]
      _ = 6 := by ring
  have h_comm : sqrt3 * (2 : R) = 2 * sqrt3 := mul_comm sqrt3 2
  have h_smul_neg : (2 * sqrt3) • -v = -((2 * sqrt3) • v) := smul_neg (2 * sqrt3) v
  simp only [LinearMap.smul_apply, h_sq3, h_comm, h_smul_neg]
  calc
    (2 * sqrt3) • v + (6 : R) • B v + ((2 : R) • B v + -((2 * sqrt3) • v)) =
        ((2 * sqrt3) • v + -((2 * sqrt3) • v)) + ((6 : R) • B v + (2 : R) • B v) := by module
    _ = 0 + (6 + 2 : R) • B v := by
      rw [add_neg_cancel, add_smul]
    _ = (8 : R) • B v := by
      have h8 : (6 : R) + 2 = 8 := by ring
      rw [zero_add, h8]

/-- The algebraic 12-fold cyclotomic phase operator $Z = \frac{1}{2}(\sqrt{3} I + B)$. -/
def cyclotomicPhase (B : Module.End R M) (inv2 sqrt3 : R) : Module.End R M :=
  inv2 • (sqrt3 • (1 : Module.End R M) + B)

/-- 🏆 THEOREM 2: Exact cube formula $Z^3 = B$ without complex numbers or transcendental functions. -/
theorem cyclotomic_phase_cube
    (B : Module.End R M) (inv2 sqrt3 : R)
    (h2 : (2 : R) * inv2 = 1)
    (h3 : sqrt3 ^ 2 = 3)
    (hB : IsChiralBivector B) :
    (cyclotomicPhase B inv2 sqrt3) ^ 3 = B := by
  dsimp [cyclotomicPhase]
  have h_smul : (inv2 • (sqrt3 • (1 : Module.End R M) + B)) ^ 3 =
      (inv2 ^ 3) • ((sqrt3 • (1 : Module.End R M) + B) ^ 3) := by
    rw [smul_pow]
  rw [h_smul, bivector_shift_cube B sqrt3 h3 hB, smul_smul]
  have h_inv : inv2 ^ 3 * (8 : R) = 1 := by
    calc
      inv2 ^ 3 * (8 : R) = (inv2 * 2) ^ 3 := by ring
      _ = (2 * inv2) ^ 3 := by rw [mul_comm]
      _ = 1 ^ 3 := by rw [h2]
      _ = 1 := by ring
  rw [h_inv, one_smul]

/-- 🏆 THEOREM 3: Exact 6th power is $-I$: $Z^6 = -I$. -/
theorem cyclotomic_phase_pow_six
    (B : Module.End R M) (inv2 sqrt3 : R)
    (h2 : (2 : R) * inv2 = 1)
    (h3 : sqrt3 ^ 2 = 3)
    (hB : IsChiralBivector B) :
    (cyclotomicPhase B inv2 sqrt3) ^ 6 = -1 := by
  have h6 : (cyclotomicPhase B inv2 sqrt3) ^ 6 = ((cyclotomicPhase B inv2 sqrt3) ^ 3) ^ 2 := by
    have h_mul : (3 : ℕ) * 2 = 6 := rfl
    rw [← pow_mul, h_mul]
  rw [h6, cyclotomic_phase_cube B inv2 sqrt3 h2 h3 hB, hB]

/-- 🏆 THEOREM 4: Exact 12-fold cyclotomic closure in the Hestenes lift: $Z^{12} = I$. -/
theorem cyclotomic_phase_pow_twelve
    (B : Module.End R M) (inv2 sqrt3 : R)
    (h2 : (2 : R) * inv2 = 1)
    (h3 : sqrt3 ^ 2 = 3)
    (hB : IsChiralBivector B) :
    (cyclotomicPhase B inv2 sqrt3) ^ 12 = 1 := by
  have h12 : (cyclotomicPhase B inv2 sqrt3) ^ 12 = ((cyclotomicPhase B inv2 sqrt3) ^ 6) ^ 2 := by
    have h_mul : (6 : ℕ) * 2 = 12 := rfl
    rw [← pow_mul, h_mul]
  rw [h12, cyclotomic_phase_pow_six B inv2 sqrt3 h2 h3 hB, neg_one_sq_op]

/-! ### 2. Krein Chiral Projectors -/

/-- Positive chiral projector $\Pi_+ = \frac{1}{2}(I + J)$. -/
def projPlus (J : Module.End R M) (inv2 : R) : Module.End R M :=
  inv2 • ((1 : Module.End R M) + J)

/-- Negative chiral projector $\Pi_- = \frac{1}{2}(I - J)$. -/
def projMinus (J : Module.End R M) (inv2 : R) : Module.End R M :=
  inv2 • ((1 : Module.End R M) - J)

/-- 🏆 THEOREM 5: Partition of unity: $\Pi_+ + \Pi_- = I$. -/
theorem krein_involution_projectors_sum
    (J : Module.End R M) (inv2 : R)
    (h2 : (2 : R) * inv2 = 1) :
    projPlus J inv2 + projMinus J inv2 = 1 := by
  dsimp [projPlus, projMinus]
  rw [← smul_add]
  have h : ((1 : Module.End R M) + J) + ((1 : Module.End R M) - J) = (2 : R) • (1 : Module.End R M) := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    module
  rw [h, smul_smul, mul_comm inv2 2, h2, one_smul]

/-- 🏆 THEOREM 6: Orthogonality of chiral projectors: $\Pi_+ \Pi_- = 0$. -/
theorem krein_involution_projectors_ortho
    (J : Module.End R M) (inv2 : R)
    (hJ : IsKreinInvolution J) :
    projPlus J inv2 * projMinus J inv2 = 0 := by
  dsimp [projPlus, projMinus]
  rw [smul_mul_smul_comm]
  have h_inner : ((1 : Module.End R M) + J) * ((1 : Module.End R M) - J) = 0 := by
    ext v
    have hJ2 : J (J v) = v := by
      have h := congr_fun (congr_arg DFunLike.coe hJ) v
      exact h
    calc
      (((1 : Module.End R M) + J) * ((1 : Module.End R M) - J)) v =
          (v - J v) + J (v - J v) := rfl
      _ = (v - J v) + (J v - J (J v)) := by rw [map_sub]
      _ = (v - J v) + (J v - v) := by rw [hJ2]
      _ = 0 := by module
  rw [h_inner, smul_zero]

end BivectorLift

end InfoGeometry.Algebra.Clifford
