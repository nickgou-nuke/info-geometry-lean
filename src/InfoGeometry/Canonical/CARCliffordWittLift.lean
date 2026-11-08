import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11SplitQuaternion

/-!
# CAR / Clifford Operator Realization of Chiral Lorentz Geometry

This file formally executes the exact conceptual chain mapping classical
relativistic chirality to an operator algebra lift:

1. **Cl(1,1) Sheet Atom**: We use the native `SplitQuaternion` basis
   (modeling the Weyl L/R block decomposition).
2. **Witt / Circular Basis**: We define the creation/annihilation operators
   $a, c$ algebraically directly from the split geometric generators $e, f$.
3. **Canonical Anticommutation Relations (CAR)**: We prove that this change
   of basis strictly obeys the CAR algebra structure $a^2=0, c^2=0, ac+ca=1$.
4. **Quadratic Operator Lie Algebra**: We construct the quadratic CAR operator
   $E = c a - \frac{1}{2}$ and prove that it identically recovers the classical
   bivector generator $ef$ of the Lorentz transformations (the boost).

This establishes the formal operator-algebraic lift (Level 2 quantization)
of the Lorentz spin representation.
-/

namespace InfoGeometry.Canonical.CARCliffordWittLift

set_option linter.unusedSectionVars false

open Matrix

variable {R : Type*} [Field R] [CharZero R]

-- 1. The Cl(1,1) Sheet Atom
def e_vec : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
def f_vec : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
def ef_vec : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

lemma e_sq : e_vec (R := R) * e_vec = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_vec]

lemma f_sq : f_vec (R := R) * f_vec = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [f_vec]

lemma ef_anti : e_vec (R := R) * f_vec + f_vec * e_vec = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_vec, f_vec]

-- 2. Witt / Circular Basis
def witt_a : Matrix (Fin 2) (Fin 2) R := (1/2 : R) • (e_vec + f_vec)
def witt_c : Matrix (Fin 2) (Fin 2) R := (1/2 : R) • (e_vec - f_vec)

-- 3. Canonical Anticommutation Relations (CAR)
theorem CAR_a_sq : witt_a (R := R) * witt_a = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [witt_a, e_vec, f_vec]

theorem CAR_c_sq : witt_c (R := R) * witt_c = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [witt_c, e_vec, f_vec]

theorem CAR_ac_anti : witt_a (R := R) * witt_c + witt_c * witt_a = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [witt_a, witt_c, e_vec, f_vec] <;> ring

-- 4. Quadratic Operator Lie Algebra
-- The geometric Lorentz bivector
def bivector_ef : Matrix (Fin 2) (Fin 2) R := e_vec * f_vec

-- The quadratic CAR operator
def quadratic_E : Matrix (Fin 2) (Fin 2) R :=
  witt_c * witt_a - (1/2 : R) • (1 : Matrix (Fin 2) (Fin 2) R)

-- 5. Noncommutative Symmetry Dynamics (Bivector Recovery)
theorem quadratic_Lie_generator_eq_lorentz_bivector :
    quadratic_E (R := R) = (1/2 : R) • bivector_ef := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quadratic_E, witt_c, witt_a, bivector_ef, e_vec, f_vec] <;> ring

end InfoGeometry.Canonical.CARCliffordWittLift
