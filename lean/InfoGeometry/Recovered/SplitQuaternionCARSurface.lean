import Mathlib.Tactic
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered
import InfoGeometry.Algebra.Cl11OSp12

/-!
# Matrix CAR Surface for OSp(1|2)

This file constructs a concrete CAR pair directly in the checked
$2 \times 2$ real split-quaternion matrix representation. It does not assert
an algebra homomorphism from the abstract Clifford owner.

It provides a concrete `FermionicCARSurface` for use in the bounded 
operator representations of `OSp(1|2)`.
-/

namespace InfoGeometry.Recovered

open InfoGeometry.SplitQuaternion
open InfoGeometry.Algebra.Cl11OSp12
open InfoGeometry.Algebra.Cl11OSp12

noncomputable section

/-- A concrete nilpotent annihilation matrix. -/
def matrix_b : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (splitJ + splitI)

/-- A concrete nilpotent creation matrix. -/
def matrix_bdag : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (splitJ - splitI)

lemma matrix_b_sq : matrix_b * matrix_b = 0 := by
  simp [matrix_b, mul_add, add_mul]
  module

lemma matrix_bdag_sq : matrix_bdag * matrix_bdag = 0 := by
  simp [matrix_bdag, mul_sub, sub_mul]
  module

lemma matrix_anticomm : matrix_b * matrix_bdag + matrix_bdag * matrix_b = 1 := by
  simp [matrix_b, matrix_bdag, mul_add, add_mul, mul_sub, sub_mul, splitOne]
  module

/--
The concrete matrix realization of the fermionic CAR surface.
-/
def splitMatrixCARSurface : FermionicCARSurface (Matrix (Fin 2) (Fin 2) ℝ) where
  b := matrix_b
  bdag := matrix_bdag
  b_sq := matrix_b_sq
  bdag_sq := matrix_bdag_sq
  anticomm := matrix_anticomm

end

end InfoGeometry.Recovered
