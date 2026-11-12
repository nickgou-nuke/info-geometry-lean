/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.FreeAlgebra
import InfoGeometry.Algebra.CyclicQuotient
import InfoGeometry.LinearAlgebra.OrderedQuotientBasis
import InfoGeometry.OperatorAlgebra.OperatorGeometryExamples

/-!
# Noncommutative examples for ordered operator bases

The words `x * y` and `y * x` belong to the native free associative algebra on two generators.
Evaluation at the existing full nondiagonal matrix projections proves that these words differ.
Their cyclic classes agree and are nonzero. The actual ordered selector therefore retains the
first of their two labels, and reversing the priority order changes the retained label.

The same matrices give an explicit failure of sequential constraint preservation: `P` is fixed
by left multiplication by `P`, but left multiplication by `Q` moves it outside that fixed space.
The existing Cartan reflections square to the identity, and their half-averages are exactly
`P` and `Q`. Each reflection has finite order dividing two; no finiteness of the group generated
by both reflections is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorBasisExamples

open InfoGeometry.Algebra.CyclicQuotient
open InfoGeometry.LinearAlgebra.OrderedQuotientBasis
open InfoGeometry.OperatorAlgebra.OperatorGeometryExamples
open InfoGeometry.Core.IdempotentCartan

/-- The native free associative complex algebra on two generator labels. -/
abbrev WordAlgebra := FreeAlgebra ℂ Bool

/-- The first free generator. -/
def x : WordAlgebra := FreeAlgebra.ι ℂ false

/-- The second free generator. -/
def y : WordAlgebra := FreeAlgebra.ι ℂ true

local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- Evaluate the two free generators at the existing noncommuting matrix projections. -/
def matrixEvaluation : WordAlgebra →ₐ[ℂ] Mat :=
  FreeAlgebra.lift ℂ (fun b : Bool => if b then Q else P)

@[simp]
theorem matrixEvaluation_x : matrixEvaluation x = P := by
  simp [matrixEvaluation, x]

@[simp]
theorem matrixEvaluation_y : matrixEvaluation y = Q := by
  simp [matrixEvaluation, y]

/-- Distinct word order is witnessed in the full matrix algebra. -/
theorem xy_ne_yx : x * y ≠ y * x := by
  intro h
  apply projections_not_commute
  change P * Q = Q * P
  simpa only [map_mul, matrixEvaluation_x, matrixEvaluation_y] using
    congrArg matrixEvaluation h

/-- Evaluation sending every free generator to one. -/
def augmentation : WordAlgebra →ₐ[ℂ] ℂ :=
  FreeAlgebra.lift ℂ (fun _ : Bool => 1)

/-- Evaluation at all generators equal to one descends as a complex-linear cyclic functional. -/
def cyclicEvaluation : CyclicModule ℂ WordAlgebra →ₗ[ℂ] ℂ :=
  descLinear augmentation.toLinearMap (fun a b => by
    change augmentation (a * b) = augmentation (b * a)
    simp only [map_mul]
    exact mul_comm _ _)

@[simp]
theorem cyclicEvaluation_class (a : WordAlgebra) :
    cyclicEvaluation (cyclicClass ℂ WordAlgebra a) = augmentation a := by
  simp only [cyclicEvaluation, descLinear_class, AlgHom.toLinearMap_apply]

theorem cyclicEvaluation_xy :
    cyclicEvaluation (cyclicClass ℂ WordAlgebra (x * y)) = 1 := by
  simp [augmentation, x, y]

/-- The cyclic equality does not collapse these word classes to zero. -/
theorem cyclic_xy_ne_zero : cyclicClass ℂ WordAlgebra (x * y) ≠ 0 := by
  intro h
  have hone : (1 : ℂ) = 0 := by
    simpa only [cyclicEvaluation_xy, map_zero] using congrArg cyclicEvaluation h
  exact one_ne_zero hone

/-- The native cyclic module quotient identifies the two cyclic word orders. -/
theorem cyclic_xy_eq_yx :
    cyclicClass ℂ WordAlgebra (x * y) = cyclicClass ℂ WordAlgebra (y * x) :=
  cyclicClass_mul_comm ℂ WordAlgebra x y

/-- Candidate labels retain the distinction between the original words. -/
def words : Bool → WordAlgebra
  | false => x * y
  | true => y * x

/-- The same candidate family after the native relation quotient. -/
def quotientWords : Bool → CyclicModule ℂ WordAlgebra :=
  cyclicClass ℂ WordAlgebra ∘ words

theorem quotientWords_true_eq_false : quotientWords true = quotientWords false :=
  cyclic_xy_eq_yx.symm

theorem quotientWords_ne_zero (b : Bool) : quotientWords b ≠ 0 := by
  cases b with
  | false => exact cyclic_xy_ne_zero
  | true =>
      rw [quotientWords_true_eq_false]
      exact cyclic_xy_ne_zero

/-- In the forward priority order, the genuine greedy selector retains the first label. -/
theorem select_false_true : select ℂ quotientWords ∅ [false, true] = {false} := by
  have hfirst : quotientWords false ∉ candidateSpan ℂ quotientWords ∅ := by
    simpa only [candidateSpan_empty, Submodule.mem_bot] using quotientWords_ne_zero false
  have hsecond : quotientWords true ∈ candidateSpan ℂ quotientWords {false} := by
    rw [quotientWords_true_eq_false]
    exact mem_candidateSpan ℂ quotientWords (Finset.mem_singleton_self false)
  rw [select_cons, ite_eq_right hfirst, Finset.insert_empty, select_cons, ite_eq_left hsecond,
    select_nil]

/-- Reversing priority retains the other original word label in the same quotient. -/
theorem select_true_false : select ℂ quotientWords ∅ [true, false] = {true} := by
  have hfirst : quotientWords true ∉ candidateSpan ℂ quotientWords ∅ := by
    simpa only [candidateSpan_empty, Submodule.mem_bot] using quotientWords_ne_zero true
  have hsecond : quotientWords false ∈ candidateSpan ℂ quotientWords {true} := by
    rw [← quotientWords_true_eq_false]
    exact mem_candidateSpan ℂ quotientWords (Finset.mem_singleton_self true)
  rw [select_cons, ite_eq_right hfirst, Finset.insert_empty, select_cons, ite_eq_left hsecond,
    select_nil]

theorem priority_changes_survivors :
    select ℂ quotientWords ∅ [false, true] ≠ select ℂ quotientWords ∅ [true, false] := by
  rw [select_false_true, select_true_false]
  decide

/-- The initial matrix satisfies the earlier left-projection constraint. -/
theorem initial_matrix_fixed : P * P = P :=
  P_isStarProjection.isIdempotentElem.eq

/-- The later projection enforces its own constraint. -/
theorem later_matrix_fixed : Q * (Q * P) = Q * P := by
  rw [← mul_assoc, Q_isStarProjection.isIdempotentElem.eq]

/-- An exact matrix entry records failure to preserve the earlier fixed space. -/
theorem later_projection_defect_entry :
    (P * (Q * P) - Q * P) 0 0 = (-3 / 25 : ℂ) := by
  norm_num [P, Q, Matrix.mul_apply, Fin.sum_univ_two]

/-- A later, noncommuting projection can destroy an earlier fixed-space condition. -/
theorem later_projection_not_fixed : P * (Q * P) ≠ Q * P := by
  intro h
  have hz : (P * (Q * P) - Q * P) 0 0 = 0 := by
    rw [h, sub_self]
    rfl
  rw [later_projection_defect_entry] at hz
  norm_num at hz

/-- The existing division-free reflection of the first projection. -/
def symmetryP : Mat := reflection P

/-- The existing division-free reflection of the second projection. -/
def symmetryQ : Mat := reflection Q

theorem symmetryP_sq : symmetryP * symmetryP = 1 :=
  reflection_sq P_isStarProjection.isIdempotentElem.eq

theorem symmetryQ_sq : symmetryQ * symmetryQ = 1 :=
  reflection_sq Q_isStarProjection.isIdempotentElem.eq

/-- The two-element average of the first involution is the original projection. -/
theorem half_average_symmetryP : (1 / 2 : ℂ) • (1 + symmetryP) = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetryP, reflection, two_nsmul, P, Matrix.one_apply]

/-- The two-element average of the second involution is the original projection. -/
theorem half_average_symmetryQ : (1 / 2 : ℂ) • (1 + symmetryQ) = Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetryQ, reflection, two_nsmul, Q, Matrix.one_apply]

/-- The loss of the earlier constraint occurs for these actual involution averages. -/
theorem consecutive_half_averages_not_fixed :
    ((1 / 2 : ℂ) • (1 + symmetryP)) * (((1 / 2 : ℂ) • (1 + symmetryQ)) * P) ≠
      ((1 / 2 : ℂ) • (1 + symmetryQ)) * P := by
  rw [half_average_symmetryP, half_average_symmetryQ]
  exact later_projection_not_fixed

end InfoGeometry.Canonical.OperatorBasisExamples

end
