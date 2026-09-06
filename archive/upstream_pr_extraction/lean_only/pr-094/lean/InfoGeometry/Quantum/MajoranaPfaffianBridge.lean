import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Native finite Majorana Pfaffian bridge

Mathlib does not currently expose a general `Matrix.pfaffian` name.  This
owner therefore formalizes the complete two-mode Pfaffian surface directly
with native matrices and determinants.  It is the finite `2N = 2` instance:
the general matching/Pfaffian construction remains a separate extension.
-/

namespace InfoGeometry.Quantum.MajoranaPfaffianBridge

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The skewness predicate used by the finite Pfaffian surface. -/
def IsSkew (A : M2R) : Prop := A.transpose = -A

/-- Native two-mode Pfaffian: the single upper-triangular entry. -/
def pfaffian2 (A : M2R) : ℝ := A 0 1

theorem coupling_isSkew (m : ℝ) :
    IsSkew (InfoGeometry.MajoranaPfaffianNaturalClosure.twoMajoranaCoupling m) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.MajoranaPfaffianNaturalClosure.twoMajoranaCoupling]

theorem coupling_pfaffian (m : ℝ) :
    pfaffian2
        (InfoGeometry.MajoranaPfaffianNaturalClosure.twoMajoranaCoupling m) = m := by
  rfl

theorem det_eq_pfaffian2_sq {A : M2R} (hA : IsSkew A) :
    A.det = (pfaffian2 A)^2 := by
  have h00 : A 0 0 = -A 0 0 := by
    have h := congrArg (fun M : M2R => M 0 0) hA
    simpa [IsSkew] using h
  have h11 : A 1 1 = -A 1 1 := by
    have h := congrArg (fun M : M2R => M 1 1) hA
    simpa [IsSkew] using h
  have h10 : A 1 0 = -A 0 1 := by
    have h := congrArg (fun M : M2R => M 0 1) hA
    simpa [IsSkew] using h
  have hz00 : A 0 0 = 0 := by linarith
  have hz11 : A 1 1 = 0 := by linarith
  rw [Matrix.det_fin_two]
  simp [pfaffian2, hz00, hz11, h10]
  ring

theorem coupling_det_eq_pfaffian2_sq (m : ℝ) :
    (InfoGeometry.MajoranaPfaffianNaturalClosure.twoMajoranaCoupling m).det =
      (pfaffian2
        (InfoGeometry.MajoranaPfaffianNaturalClosure.twoMajoranaCoupling m))^2 := by
  exact det_eq_pfaffian2_sq (coupling_isSkew m)

/-- Pfaffian covariance under a two-dimensional congruence. -/
theorem pfaffian2_congr (O A : M2R) (hA : IsSkew A) :
    pfaffian2 (O * A * O.transpose) = O.det * pfaffian2 A := by
  have h00 : A 0 0 = -A 0 0 := by
    have h := congrArg (fun M : M2R => M 0 0) hA
    simpa [IsSkew] using h
  have h11 : A 1 1 = -A 1 1 := by
    have h := congrArg (fun M : M2R => M 1 1) hA
    simpa [IsSkew] using h
  have h10 : A 1 0 = -A 0 1 := by
    have h := congrArg (fun M : M2R => M 0 1) hA
    simpa [IsSkew] using h
  have hz00 : A 0 0 = 0 := by linarith
  have hz11 : A 1 1 = 0 := by linarith
  simp [pfaffian2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.det_fin_two, hz00, hz11, h10]
  ring

theorem pfaffian2_orientation_preserving (O A : M2R) (hA : IsSkew A)
    (hO : O.det = 1) :
    pfaffian2 (O * A * O.transpose) = pfaffian2 A := by
  rw [pfaffian2_congr O A hA, hO, one_mul]

theorem pfaffian2_orientation_reversing (O A : M2R) (hA : IsSkew A)
    (hO : O.det = -1) :
    pfaffian2 (O * A * O.transpose) = -pfaffian2 A := by
  rw [pfaffian2_congr O A hA, hO]
  ring

end InfoGeometry.Quantum.MajoranaPfaffianBridge
