/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset

/-!
# Finite real Clifford and two-spinor identities from the DeWitt tetractys

This file adds a finite matrix bridge to the existing DeWitt and twistor owners.
It proves a concrete real `Cl(3,1)` matrix family on `Fin 4`, its quadratic
Minkowski square identity over integer coefficients, Peirce-corner nilpotence,
and the real two-spinor determinant identity.

These statements do not construct the Poincare group or super-Poincare algebra.
Those require, among other data, a Lorentz action on a four-dimensional
translation module and a specified representation of odd supercharges.
-/

namespace InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge

open Matrix
open InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset

/-! ## A concrete real `Cl(3,1)` family -/

abbrev Mat4Z := Matrix (Fin 4) (Fin 4) ℤ

/-- Timelike generator `γ₀ = J₁`. -/
def gamma0 : Mat4Z := dtMatJ1

/-- First spacelike generator `γ₁ = S₁`. -/
def gamma1 : Mat4Z := dtMatS1

/-- Second spacelike generator `γ₂ = Φ₁ S₂`. -/
def gamma2 : Mat4Z := dtMatPhi1 * dtMatS2

/-- Third spacelike generator `γ₃ = Φ₁ Φ₂`. -/
def gamma3 : Mat4Z := dtMatPhi1 * dtMatPhi2

/-- The four displayed matrices satisfy the `(-,+,+,+)` Clifford relations.
This is a concrete integer-matrix statement, using the basis order of the
imported two-bit DeWitt matrices. -/
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

/-- Integer-coefficient Dirac vector in the concrete four-dimensional module. -/
def diracVector (p0 p1 p2 p3 : ℤ) : Mat4Z :=
  p0 • gamma0 + p1 • gamma1 + p2 • gamma2 + p3 • gamma3

/-- The square of the concrete Dirac vector is its Minkowski quadratic form.
Scalars and matrices are both over `ℤ`; no analytic or continuum operator is
being asserted here. -/
theorem diracVector_square (p0 p1 p2 p3 : ℤ) :
    diracVector p0 p1 p2 p3 * diracVector p0 p1 p2 p3 =
      (-p0 ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : Mat4Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracVector, gamma0, gamma1, gamma2, gamma3,
      dtMatJ1, dtMatS1, dtMatPhi1, dtMatS2, dtMatPhi2,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ] <;> ring

/-! ## Peirce translation corner: nilpotence without a Poincare action -/

/-- The upper Peirce corner associated to an idempotent `P`. -/
def upperCorner {B : Type*} [Ring B] (P x : B) : B := P * x * (1 - P)

/-- Two elements of the same upper Peirce corner have zero product. -/
theorem upperCorner_mul_eq_zero {B : Type*} [Ring B]
    (P x y : B) (hP : P * P = P) :
    upperCorner P x * upperCorner P y = 0 := by
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP]
    abel
  have hmiddle : (1 - P) * (P * (y * (1 - P))) = 0 := by
    rw [← mul_assoc, hQP, zero_mul]
  simp [upperCorner, mul_assoc, hmiddle]

/-- The commutator of any two upper-corner elements vanishes. This establishes
an abelian nilpotent corner, not a four-dimensional translation representation. -/
theorem upperCorner_commute {B : Type*} [Ring B]
    (P x y : B) (hP : P * P = P) :
    upperCorner P x * upperCorner P y -
      upperCorner P y * upperCorner P x = 0 := by
  rw [upperCorner_mul_eq_zero P x y hP,
    upperCorner_mul_eq_zero P y x hP]
  simp

/-! ## Real two-spinor null and massive determinant identities -/

/-- The symmetric rank-one momentum matrix `λ λᵀ`. -/
def rankOneMomentum (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a ^ 2, a * b; a * b, b ^ 2]

/-- The determinant of the sum of two real rank-one momenta. -/
def twoSpinorDet (a b c d : ℝ) : ℝ :=
  (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2

/-- The alternating real two-spinor pairing. -/
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
