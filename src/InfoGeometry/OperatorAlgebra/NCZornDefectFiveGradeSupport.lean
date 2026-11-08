/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Five-grade support of noncommutative operator defects

The carrier, five-grade components, and associator defect are owned by
NCZornTripotentFiveGrading. This module proves the support consequence
needed by downstream defect transport: a nonzero operator defect has a
nonzero component in one of the five grades. It also transports the existing
noncommuting-coefficient witness to that statement.
-/

namespace InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport

open InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading
open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorZornRealModule
open InfoGeometry.Canonical.NCZorn
open scoped Matrix

/-- The two coefficient matrix units used by the explicit Zorn associator
example. -/
def coefficientE01 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

def coefficientE10 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- The coefficient carrier in the associator example is genuinely
noncommutative. -/
theorem coefficientMatrix_noncommutative_witness :
    coefficientE01 * coefficientE10 ≠ coefficientE10 * coefficientE01 := by
  decide

variable {A : Type*} [Ring A]

/-- A nonzero operator has a nonzero component among all five native grades. -/
theorem exists_nonzero_five_grade_component
    (K : Module.End ℤ (OperatorZornMatrix A)) (hK : K ≠ 0) :
    ∃ d : Fin 5, ncZornFiveComponent K d ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum : ∑ d : Fin 5, ncZornFiveComponent K d = 0 :=
    Finset.sum_eq_zero fun d _ => h d
  rw [ncZornFiveComponent_sum] at hsum
  exact hK hsum

/-- A nonvanishing Zorn associator defect is supported in at least one of
the five operator grades. -/
theorem ncZornMulDefect_has_nonzero_five_grade_component
    (X Y : OperatorZornMatrix A)
    (hD : ncZornMulDefect X Y ≠ 0) :
    ∃ d : Fin 5, ncZornFiveComponent (ncZornMulDefect X Y) d ≠ 0 :=
  exists_nonzero_five_grade_component (ncZornMulDefect X Y) hD

/-- The Zorn associator anomaly is the sum of its five graded operator
components, evaluated on the third argument. This keeps the defect itself
visible instead of replacing it by the weaker fact that some grade is nonzero. -/
theorem ncZornMulDefect_associator_five_grade_expansion
    (X Y Z : OperatorZornMatrix A) :
    ncZornMulDefect X Y Z =
      ∑ d : Fin 5, ncZornFiveComponent (ncZornMulDefect X Y) d Z := by
  have h := congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) => K Z)
    (ncZornFiveComponent_sum (ncZornMulDefect X Y))
  simpa only [LinearMap.sum_apply] using h.symm

/-- A nonzero associator value at a specified third input is detected by at
least one evaluated five-grade contribution. -/
theorem ncZornMulDefect_apply_has_nonzero_five_grade_component
    (X Y Z : OperatorZornMatrix A)
    (hD : ncZornMulDefect X Y Z ≠ 0) :
    ∃ d : Fin 5, ncZornFiveComponent (ncZornMulDefect X Y) d Z ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum :
      ∑ d : Fin 5, ncZornFiveComponent (ncZornMulDefect X Y) d Z = 0 :=
    Finset.sum_eq_zero fun d _ => h d
  rw [← ncZornMulDefect_associator_five_grade_expansion X Y Z] at hsum
  exact hD hsum

/-- Noncommuting coefficient data that produces the owner-level associator
defect also produces a nonzero component in one of the five grades. -/
theorem upperTwo_noncommuting_defect_has_five_grade_support
    {a b d : A} (h : (a * b - b * a) * d ≠ 0) :
    ∃ k : Fin 5,
      ncZornFiveComponent
        (ncZornMulDefect (upperTwo a b) (upperTwo a b)) k ≠ 0 := by
  have hNotRange :
      ncZornMulDefect (upperTwo a b) (upperTwo a b) ∉
        LinearMap.range (ncZornLeftMulHom (A := A)) :=
    (ncZornMulDefect_upperTwo_not_mem_range h).2
  have hD : ncZornMulDefect (upperTwo a b) (upperTwo a b) ≠ 0 := by
    intro hZero
    apply hNotRange
    rw [hZero]
    exact Submodule.zero_mem _
  exact ncZornMulDefect_has_nonzero_five_grade_component
    (upperTwo a b) (upperTwo a b) hD

/-- Concrete noncommutative matrix coefficients give an actual Zorn
associator anomaly, and therefore force at least one of its five native
operator grades to be nonzero. The coefficient algebra is `M₂(ℤ)`, so this
is a matrix-operator witness rather than a scalar specialization. -/
theorem matrix_coefficient_associator_has_nonzero_five_grade :
    ncZornMulDefect
        (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
        (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
        (NCZornElement.pureNPlus (!![(0 : ℤ), 1; 0, 0])) ≠ 0 ∧
    ∃ k : Fin 5,
      ncZornFiveComponent
        (ncZornMulDefect
          (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
          (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))) k
        (NCZornElement.pureNPlus (!![(0 : ℤ), 1; 0, 0])) ≠ 0 := by
  have hCoeff :
      ((!![(0 : ℤ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) *
          (!![(0 : ℤ), 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) -
        (!![(0 : ℤ), 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) *
          (!![(0 : ℤ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ)) *
        (!![(0 : ℤ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0 := by
    intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hWitness := ncZornMulDefect_upperTwo_not_mem_range hCoeff
  have hAssoc :
      ncZornMulDefect
        (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
        (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
        (NCZornElement.pureNPlus (!![(0 : ℤ), 1; 0, 0])) ≠ 0 := by
    intro hZero
    have hCoord := congrArg
      (fun X : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℤ) => X.sigma_minus 2) hZero
    rw [hWitness.1] at hCoord
    have hEntry := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hCoord
    norm_num at hEntry
  exact ⟨hAssoc,
    ncZornMulDefect_apply_has_nonzero_five_grade_component
      (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
      (upperTwo (!![(0 : ℤ), 1; 0, 0]) (!![(0 : ℤ), 0; 1, 0]))
      (NCZornElement.pureNPlus (!![(0 : ℤ), 1; 0, 0])) hAssoc⟩

end InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport
