import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OrientedPfaffianMatching

/-!
# The four-index Pfaffian matching polynomial

For the displayed skew matrix, the three monomials are the three perfect
matchings of four labelled vertices.  This is a finite polynomial identity;
no state, correlator, or physical interpretation is included in the carrier.
-/

namespace InfoGeometry.Canonical.MajoranaPfaffian4

open scoped Matrix
open InfoGeometry.Canonical.OrientedPfaffianMatching

variable {R : Type*} [CommRing R]

def skewMatrix4 (a b c d e f : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, a, b, c;
     -a, 0, d, e;
     -b, -d, 0, f;
     -c, -e, -f, 0]

/-- The signed matching polynomial for the ordering `01,02,03,12,13,23`. -/
def pfaffian4 (a b c d e f : R) : R := a * f - b * e + c * d

theorem pfaffian4_matching_expansion (a b c d e f : R) :
    pfaffian4 a b c d e f = a * f - b * e + c * d := by
  rfl

theorem skewMatrix4_transpose (a b c d e f : R) :
    (skewMatrix4 a b c d e f).transpose =
      -skewMatrix4 a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix4, Matrix.transpose_apply]

theorem skewMatrix4_pfaffian_sq_eq_det
    (a b c d e f : R) :
    pfaffian4 a b c d e f ^ 2 =
      (skewMatrix4 a b c d e f).det := by
  classical
  rw [pfaffian4]
  simp [skewMatrix4, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove, pow_two]
  ring

theorem pfaffian4_matching_terms
    (a b c d e f : R) :
    pfaffian4 a b c d e f =
      (a * f) + (-(b * e)) + (c * d) := by
  unfold pfaffian4
  ring

/-! The three perfect matchings of four labelled vertices.  Their partner
functions are the pairings `01|23`, `02|13`, and `03|12`. -/

def matching01_23 : @PerfectMatching (Fin 4) where
  partner := ![1, 0, 3, 2]
  involutive := by
    intro i
    fin_cases i <;> rfl
  fixed_free := by
    intro i
    fin_cases i <;> decide

def matching02_13 : @PerfectMatching (Fin 4) where
  partner := ![2, 3, 0, 1]
  involutive := by
    intro i
    fin_cases i <;> rfl
  fixed_free := by
    intro i
    fin_cases i <;> decide

def matching03_12 : @PerfectMatching (Fin 4) where
  partner := ![3, 2, 1, 0]
  involutive := by
    intro i
    fin_cases i <;> rfl
  fixed_free := by
    intro i
    fin_cases i <;> decide

theorem matching01_23_pairs :
    PerfectMatching.partner matching01_23 0 = 1 ∧
      PerfectMatching.partner matching01_23 2 = 3 := by
  constructor <;> rfl

theorem matching02_13_pairs :
    PerfectMatching.partner matching02_13 0 = 2 ∧
      PerfectMatching.partner matching02_13 1 = 3 := by
  constructor <;> rfl

theorem matching03_12_pairs :
    PerfectMatching.partner matching03_12 0 = 3 ∧
      PerfectMatching.partner matching03_12 1 = 2 := by
  constructor <;> rfl

end InfoGeometry.Canonical.MajoranaPfaffian4
