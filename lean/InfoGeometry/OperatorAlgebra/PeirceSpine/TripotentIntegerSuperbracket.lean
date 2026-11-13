/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentIntegerGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentSuperbracket

/-!
# Homogeneous super-Jacobi with an unrestricted integer index

Every intermediate bracket has its true sum degree. There are no hypotheses
requiring intermediate sums to stay in a five-element label type. Zero
components outside the support are handled by the native integer grading.
This associative superbracket is not automatically a bracket on an ordinary
skew-adjoint Lie subalgebra.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Algebra.SupergradedBracket

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The parity of any integer degree, including negative degrees. -/
def integerParity (k : ℤ) : Bool := decide (k % 2 = 1)

/-- Parity respects all integer sums. -/
theorem integerParity_add (i j : ℤ) :
    integerParity (i + j) = Bool.xor (integerParity i) (integerParity j) := by
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [integerParity, Int.add_emod, hi, hj]

/-- The unrestricted parity agrees with the existing five-label parity. -/
theorem integerParity_fiveGradeValue (k : FiveGrade) :
    integerParity (fiveGradeValue k) = fiveGradeParity k :=
  (fiveGradeParity_eq_mod_two k).symm

/-- The integer parity is realized by the existing middle-projector involution. -/
theorem parityConj_projZero_eq_integerParity {S X : A}
    (hS : S * S * S = S) {k : ℤ} (hX : X ∈ adGrade S k) :
    parityConj (projZero S) X = if integerParity k then -X else X := by
  by_cases hk : k ∈ Set.range fiveGradeValue
  · obtain ⟨i, rfl⟩ := hk
    rw [integerParity_fiveGradeValue]
    exact parityConj_projZero_eq_fiveGradeParity hS i
      (by rwa [← adGrade_fiveGradeValue hS])
  · have hz : X = 0 := by
      rw [adGrade_eq_bot_of_not_mem hS hk] at hX
      exact hX
    simp [hz, parityConj]

/-- Signed brackets have their actual integer sum degree. -/
theorem superBracket_mem_adGrade {S X Y : A} {i j : ℤ}
    (hX : X ∈ adGrade S i) (hY : Y ∈ adGrade S j) :
    superBracket (integerParity i) (integerParity j) X Y ∈ adGrade S (i + j) := by
  have hXY := mul_mem_adGrade_add hX hY
  have hYX : Y * X ∈ adGrade S (i + j) := by
    simpa only [add_comm j i] using mul_mem_adGrade_add hY hX
  unfold superBracket anticommutator InfoGeometry.Algebra.SupergradedBracket.commutator
  split_ifs
  · exact add_mem hXY hYX
  · exact sub_mem hXY hYX

/-- The homogeneous bracket in a specified, provably equal sum degree. -/
def integerSuperBracket {S : A} {i j k : ℤ} (hk : i + j = k)
    (X : adGrade S i) (Y : adGrade S j) : adGrade S k :=
  ⟨superBracket (integerParity i) (integerParity j) (X : A) (Y : A),
    hk ▸ superBracket_mem_adGrade X.property Y.property⟩

/-- Super-Jacobi is a single equality in the total integer homogeneous
component, valid even when any pair sum is outside `[-2,2]`. -/
theorem integerSuperBracket_jacobi {S : A} {i j k : ℤ}
    (X : adGrade S i) (Y : adGrade S j) (Z : adGrade S k) :
    gradedSign (R := ℝ) (integerParity i) (integerParity k) •
          integerSuperBracket (show i + (j + k) = i + j + k by omega)
            X (integerSuperBracket rfl Y Z) +
        gradedSign (R := ℝ) (integerParity j) (integerParity i) •
          integerSuperBracket (show j + (k + i) = i + j + k by omega)
            Y (integerSuperBracket rfl Z X) +
        gradedSign (R := ℝ) (integerParity k) (integerParity j) •
          integerSuperBracket (show k + (i + j) = i + j + k by omega)
            Z (integerSuperBracket rfl X Y) = 0 := by
  apply Subtype.ext
  change gradedSign (R := ℝ) (integerParity i) (integerParity k) •
        superBracket (integerParity i) (integerParity (j + k)) (X : A)
          (superBracket (integerParity j) (integerParity k) (Y : A) (Z : A)) +
      gradedSign (R := ℝ) (integerParity j) (integerParity i) •
        superBracket (integerParity j) (integerParity (k + i)) (Y : A)
          (superBracket (integerParity k) (integerParity i) (Z : A) (X : A)) +
      gradedSign (R := ℝ) (integerParity k) (integerParity j) •
        superBracket (integerParity k) (integerParity (i + j)) (Z : A)
          (superBracket (integerParity i) (integerParity j) (X : A) (Y : A)) = (0 : A)
  simp only [integerParity_add]
  exact superBracket_superJacobi (R := ℝ)
    (integerParity i) (integerParity j) (integerParity k) (X : A) (Y : A) (Z : A)

end InfoGeometry.OperatorAlgebra.PeirceSpine
