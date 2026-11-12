/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity
import InfoGeometry.Algebra.SupergradedJordanLieSplit

/-!
# Signed brackets on the native tripotent five ranges

The middle Peirce projector already determines the parity of the five
adjoint-weight ranges. This owner connects that parity to the existing
associative superbracket. Multiplication closure of the actual ranges gives
signed bracket closure, and weights outside the five labels give zero.

The homogeneous bracket below takes values in the proved output submodule.
Its Jacobi identity is an equality in a common output grade; the inner
brackets use their actual summed grade labels, whose parity is proved to be
the XOR of the input parities. The universal signed identity is reused.

The carrier remains an arbitrary associative real algebra. Some grades may
vanish. These statements do not construct a Jordan/Kantor TKK realization,
identify a physical superalgebra, or make the middle projector a vacuum.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Algebra.SupergradedBracket

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Parity of the actual five weights for the middle-projector cut. -/
def fiveGradeParity : FiveGrade → Bool
  | .negOne => true
  | .posOne => true
  | _ => false

/-- The middle-projector parity is the integer weight modulo two. -/
theorem fiveGradeParity_eq_mod_two (k : FiveGrade) :
    fiveGradeParity k = decide (fiveGradeValue k % 2 = 1) := by
  cases k <;> decide

/-- Whenever a sum stays in the five labels, its parity is the XOR. -/
theorem fiveGradeParity_add {i j k : FiveGrade}
    (hk : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k) :
    fiveGradeParity k = Bool.xor (fiveGradeParity i) (fiveGradeParity j) := by
  cases i <;> cases j <;> cases k <;>
    first
    | rfl
    | norm_num [fiveGradeValue] at hk

/-- The bracket's parity label agrees with the existing Peirce involution. -/
theorem parityConj_projZero_eq_fiveGradeParity {T X : A}
    (hT : T * T * T = T) (k : FiveGrade)
    (hX : X ∈ fiveGradeRange T k) :
    parityConj (projZero T) X = if fiveGradeParity k then -X else X := by
  have h := parityConj_projZero_of_mem_fiveGradeRange hT k hX
  cases k <;> simpa [fiveGradeParity] using h

/-- The signed bracket adds the weights of the actual homogeneous inputs. -/
theorem superBracket_mem_fiveGradeRange {T X Y : A} {i j k : FiveGrade}
    (hT : T * T * T = T)
    (hk : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k)
    (hX : X ∈ fiveGradeRange T i) (hY : Y ∈ fiveGradeRange T j) :
    superBracket (fiveGradeParity i) (fiveGradeParity j) X Y ∈
      fiveGradeRange T k := by
  have hXY := mul_mem_fiveGradeRange hT hk hX hY
  have hYX : Y * X ∈ fiveGradeRange T k :=
    mul_mem_fiveGradeRange hT (by simpa only [add_comm] using hk) hY hX
  unfold superBracket anticommutator InfoGeometry.Algebra.SupergradedBracket.commutator
  split_ifs
  · exact (fiveGradeRange T k).add_mem hXY hYX
  · exact (fiveGradeRange T k).sub_mem hXY hYX

/-- A signed bracket is zero when its summed weight is outside the support. -/
theorem superBracket_eq_zero_of_fiveGrade_sum_not_mem
    {T X Y : A} {i j : FiveGrade}
    (hT : T * T * T = T)
    (hX : X ∈ fiveGradeRange T i) (hY : Y ∈ fiveGradeRange T j)
    (hout : fiveGradeValue i + fiveGradeValue j ∉ Set.range fiveGradeValue) :
    superBracket (fiveGradeParity i) (fiveGradeParity j) X Y = 0 := by
  have houtR : (fiveGradeValue i : ℝ) + (fiveGradeValue j : ℝ) ∉
      Set.range (fun k : FiveGrade => (fiveGradeValue k : ℝ)) := by
    rintro ⟨k, hk⟩
    change (fiveGradeValue k : ℝ) =
      (fiveGradeValue i : ℝ) + (fiveGradeValue j : ℝ) at hk
    apply hout
    refine ⟨k, ?_⟩
    exact_mod_cast hk
  rw [fiveGradeRange_eq_eigenspace hT] at hX hY
  have hXY := mul_eq_zero_of_weight_not_mem hT hX hY houtR
  have hYX : Y * X = 0 :=
    mul_eq_zero_of_weight_not_mem hT hY hX
      (by simpa only [add_comm] using houtR)
  simp [superBracket, anticommutator,
    InfoGeometry.Algebra.SupergradedBracket.commutator, hXY, hYX]

/-- The signed bracket with its codomain restricted to the proved sum grade. -/
def fiveGradeSuperBracket {T : A} (hT : T * T * T = T)
    {i j k : FiveGrade}
    (hk : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k)
    (X : fiveGradeRange T i) (Y : fiveGradeRange T j) : fiveGradeRange T k :=
  ⟨superBracket (fiveGradeParity i) (fiveGradeParity j) (X : A) (Y : A),
    superBracket_mem_fiveGradeRange hT hk X.property Y.property⟩

@[simp] theorem coe_fiveGradeSuperBracket {T : A}
    (hT : T * T * T = T) {i j k : FiveGrade}
    (hk : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k)
    (X : fiveGradeRange T i) (Y : fiveGradeRange T j) :
    (fiveGradeSuperBracket hT hk X Y : A) =
      superBracket (fiveGradeParity i) (fiveGradeParity j) (X : A) (Y : A) :=
  rfl

/-- Homogeneous Jacobi inside the common output range, with the inner
brackets carrying their proved sum grades. If a pair sum is outside the
five labels, its bracket is instead zero by the preceding support theorem. -/
theorem fiveGradeSuperBracket_jacobi {T : A} (hT : T * T * T = T)
    {i j k ij jk ki total : FiveGrade}
    (hij : fiveGradeValue i + fiveGradeValue j = fiveGradeValue ij)
    (hjk : fiveGradeValue j + fiveGradeValue k = fiveGradeValue jk)
    (hki : fiveGradeValue k + fiveGradeValue i = fiveGradeValue ki)
    (htotal : fiveGradeValue i + fiveGradeValue jk = fiveGradeValue total)
    (X : fiveGradeRange T i) (Y : fiveGradeRange T j) (Z : fiveGradeRange T k) :
    gradedSign (R := ℝ) (fiveGradeParity i) (fiveGradeParity k) •
          fiveGradeSuperBracket hT htotal X (fiveGradeSuperBracket hT hjk Y Z) +
        gradedSign (R := ℝ) (fiveGradeParity j) (fiveGradeParity i) •
          fiveGradeSuperBracket hT
            (show fiveGradeValue j + fiveGradeValue ki = fiveGradeValue total
              from by omega)
            Y (fiveGradeSuperBracket hT hki Z X) +
        gradedSign (R := ℝ) (fiveGradeParity k) (fiveGradeParity j) •
          fiveGradeSuperBracket hT
            (show fiveGradeValue k + fiveGradeValue ij = fiveGradeValue total
              from by omega)
            Z (fiveGradeSuperBracket hT hij X Y) = 0 := by
  apply Subtype.ext
  change
    gradedSign (R := ℝ) (fiveGradeParity i) (fiveGradeParity k) •
          superBracket (fiveGradeParity i) (fiveGradeParity jk) (X : A)
            (superBracket (fiveGradeParity j) (fiveGradeParity k) (Y : A) (Z : A)) +
        gradedSign (R := ℝ) (fiveGradeParity j) (fiveGradeParity i) •
          superBracket (fiveGradeParity j) (fiveGradeParity ki) (Y : A)
            (superBracket (fiveGradeParity k) (fiveGradeParity i) (Z : A) (X : A)) +
        gradedSign (R := ℝ) (fiveGradeParity k) (fiveGradeParity j) •
          superBracket (fiveGradeParity k) (fiveGradeParity ij) (Z : A)
            (superBracket (fiveGradeParity i) (fiveGradeParity j) (X : A) (Y : A)) =
      (0 : A)
  rw [fiveGradeParity_add hjk, fiveGradeParity_add hki, fiveGradeParity_add hij]
  exact superBracket_superJacobi (R := ℝ)
    (fiveGradeParity i) (fiveGradeParity j) (fiveGradeParity k) (X : A) (Y : A) (Z : A)

end InfoGeometry.OperatorAlgebra.PeirceSpine
