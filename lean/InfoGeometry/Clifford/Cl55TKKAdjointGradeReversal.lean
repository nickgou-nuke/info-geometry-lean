/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl55SuperTKK

set_option autoImplicit false

/-!
# Grade reversal from adjoint anti-commutation

This file constructs the induced endomorphism-algebra action of the
transported modular involution, proves its anti-commutation with the concrete
Cl(5,5) TKK adjoint, and derives the general eigenspace consequence.
-/

namespace InfoGeometry.Clifford.Cl55SuperTKK

/-- Conjugation by the transported modular involution on the endomorphism
algebra of the vacuum ideal. -/
noncomputable def idealModularConjugationAction : EndV →ₗ[ℝ] EndV where
  toFun X := idealModularConjugation * X * idealModularConjugation
  map_add' X Y := by
    simp only [mul_add, add_mul]
  map_smul' c X := by
    simp only [smul_mul_assoc, mul_smul_comm]
    rfl

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Conjugation by a square-one element preserves multiplication in any
associative ring. -/
theorem conjugation_mul_of_sq_one
    {A : Type*} [Ring A] (J X Y : A) (hJ : J * J = 1) :
    J * (X * Y) * J = (J * X * J) * (J * Y * J) := by
  calc
    J * (X * Y) * J = J * X * 1 * Y * J := by noncomm_ring
    _ = J * X * (J * J) * Y * J := by rw [hJ]
    _ = (J * X * J) * (J * Y * J) := by noncomm_ring

/-- Conjugation by a square-one element preserves the commutator in any
associative ring. -/
theorem conjugation_preserves_commutator
    {A : Type*} [Ring A] (J X Y : A) (hJ : J * J = 1) :
    J * (X * Y - Y * X) * J =
      (J * X * J) * (J * Y * J) - (J * Y * J) * (J * X * J) := by
  have hxy := conjugation_mul_of_sq_one J X Y hJ
  have hyx := conjugation_mul_of_sq_one J Y X hJ
  calc
    J * (X * Y - Y * X) * J =
        J * (X * Y) * J - J * (Y * X) * J := by noncomm_ring
    _ = (J * X * J) * (J * Y * J) -
        (J * Y * J) * (J * X * J) := by rw [hxy, hyx]

/-- Conjugation by the square-one ideal modular element preserves the
associative product on `EndV`. -/
theorem idealModularConjugationAction_mul (X Y : EndV) :
    idealModularConjugationAction (X * Y) =
      idealModularConjugationAction X * idealModularConjugationAction Y := by
  change idealModularConjugation * (X * Y) * idealModularConjugation =
    (idealModularConjugation * X * idealModularConjugation) *
      (idealModularConjugation * Y * idealModularConjugation)
  exact conjugation_mul_of_sq_one
    idealModularConjugation X Y idealModularConjugation_sq

/-- Conjugation by the ideal modular involution preserves the concrete
associative commutator defining the TKK bracket on `EndV`. -/
theorem idealModularConjugationAction_preserves_tkkBracket
    (X Y : EndV) :
    idealModularConjugationAction (tkkBracket X Y) =
      tkkBracket (idealModularConjugationAction X)
        (idealModularConjugationAction Y) := by
  change idealModularConjugation * (X * Y - Y * X) *
      idealModularConjugation =
    (idealModularConjugation * X * idealModularConjugation) *
        (idealModularConjugation * Y * idealModularConjugation) -
      (idealModularConjugation * Y * idealModularConjugation) *
        (idealModularConjugation * X * idealModularConjugation)
  exact conjugation_preserves_commutator
    idealModularConjugation X Y idealModularConjugation_sq

/-- In any associative ring, conjugation by an involution that sends the
commutator generator to its negative reverses the corresponding adjoint map. -/
theorem conjugation_anticommutes_commutator
    {A : Type*} [Ring A] (J P X : A)
    (hJ : J * J = 1) (hP : J * P * J = -P) :
    J * (P * X - X * P) * J =
      -(P * (J * X * J) - (J * X * J) * P) := by
  have hleft : J * P * X * J = (J * P * J) * (J * X * J) := by
    calc
      J * P * X * J = J * P * 1 * X * J := by simp
      _ = J * P * (J * J) * X * J := by rw [hJ]
      _ = (J * P * J) * (J * X * J) := by noncomm_ring
  have hright : J * X * P * J = (J * X * J) * (J * P * J) := by
    calc
      J * X * P * J = J * X * 1 * P * J := by simp
      _ = J * X * (J * J) * P * J := by rw [hJ]
      _ = (J * X * J) * (J * P * J) := by noncomm_ring
  calc
    J * (P * X - X * P) * J = J * P * X * J - J * X * P * J := by
      noncomm_ring
    _ = (J * P * J) * (J * X * J) -
        (J * X * J) * (J * P * J) := by rw [hleft, hright]
    _ = -(P * (J * X * J) - (J * X * J) * P) := by
      rw [hP]
      noncomm_ring

/-- Conjugation by the ideal modular involution anticommutes with the
concrete TKK adjoint action. -/
theorem idealModularConjugationAction_anticommutes_tkkAdjoint (X : EndV) :
    idealModularConjugationAction (tkkAdjoint X) =
      -tkkAdjoint (idealModularConjugationAction X) := by
  have hJ := idealModularConjugation_sq
  have hP := idealModularConjugation_conjugates_tkkGradingElement
  change idealModularConjugation *
      (tkkGradingElement * X - X * tkkGradingElement) *
        idealModularConjugation =
    -(tkkGradingElement *
        (idealModularConjugation * X * idealModularConjugation) -
      (idealModularConjugation * X * idealModularConjugation) *
        tkkGradingElement)
  exact conjugation_anticommutes_commutator
    idealModularConjugation tkkGradingElement X hJ hP

/-- The vacuum-ideal endomorphism algebra is genuinely noncommutative:
the indicated matrix units compose in opposite orders to a nonzero unit and
zero, respectively. -/
theorem idealEndV_noncommutative_witness :
    matrixUnit 0 1 * matrixUnit 1 2 ≠ matrixUnit 1 2 * matrixUnit 0 1 := by
  let e := coordinates.conjAlgEquiv ℝ
  intro h
  have h' := congrArg e h
  have hmul : coordinateMatrixUnit 0 1 * coordinateMatrixUnit 1 2 =
      coordinateMatrixUnit 0 2 := by
    ext f i
    simp [coordinateMatrixUnit, Module.End.mul_apply, Pi.single_apply]
  have hzero : coordinateMatrixUnit 1 2 * coordinateMatrixUnit 0 1 = 0 := by
    ext f i
    simp [coordinateMatrixUnit, Module.End.mul_apply, Pi.single_apply]
  have hcontradiction : coordinateMatrixUnit 0 2 = 0 := by
    simpa [e, matrixUnit, hmul, hzero] using h'
  exact coordinateMatrixUnit_ne_zero 0 2 hcontradiction

/-- A real-linear map that anti-commutes with the concrete TKK adjoint
operator sends its integer grade `k` eigenspace into grade `-k`. -/
theorem linearMap_anti_commuting_with_tkk_adjoint_reverses_grade
    (theta : EndV →ₗ[ℝ] EndV)
    (hθ : ∀ X, theta (tkkAdjoint X) = -tkkAdjoint (theta X))
    (k : ℤ) {X : EndV} (hX : X ∈ tkkGrade k) :
    theta X ∈ tkkGrade (-k) := by
  change tkkAdjoint X = (k : ℝ) • X at hX
  change tkkAdjoint (theta X) = ((-k : ℤ) : ℝ) • theta X
  calc
    tkkAdjoint (theta X) = -theta (tkkAdjoint X) := by
      calc
        tkkAdjoint (theta X) = -(-tkkAdjoint (theta X)) := by
          exact (neg_neg (tkkAdjoint (theta X))).symm
        _ = -theta (tkkAdjoint X) := by rw [hθ X]
    _ = -((k : ℝ) • theta X) := by
      rw [hX, map_smul]
    _ = ((-k : ℤ) : ℝ) • theta X := by
      rw [Int.cast_neg]
      exact (neg_smul (k : ℝ) (theta X)).symm

/-- The concrete modular-conjugation action reverses each integer TKK grade. -/
theorem idealModularConjugationAction_maps_grade_neg
    (k : ℤ) {X : EndV} (hX : X ∈ tkkGrade k) :
    idealModularConjugationAction X ∈ tkkGrade (-k) :=
  linearMap_anti_commuting_with_tkk_adjoint_reverses_grade
    idealModularConjugationAction
    idealModularConjugationAction_anticommutes_tkkAdjoint k hX

end InfoGeometry.Clifford.Cl55SuperTKK
