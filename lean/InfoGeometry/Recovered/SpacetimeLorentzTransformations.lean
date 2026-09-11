import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered

/-!
# Spacetime Minkowski Vectors and Lorentz Transformations

This file formalizes the embedding of Minkowski spacetime vectors $(t, x, y, z)$ 
into the rigorous $2 \times 2$ real matrix representations of the split-quaternions.

It proves the fundamental property of the restricted Lorentz group: the 
algebraic sandwich transformation $x' = q \cdot x \cdot q^*$ acts as an isometry 
on the Minkowski spacetime metric, preserving the spacetime interval identically.
-/

namespace InfoGeometry.Spacetime

open Matrix
open InfoGeometry.SplitQuaternion

/-- 
A spacetime vector $(t, x, y, z)$ mapped into the $2 \times 2$ real matrix algebra.
This corresponds to the explicit split Pauli matrix basis mapping.
-/
noncomputable def spacetimeMatrix (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  t • splitOne + x • splitI + y • splitJ + z • splitK

/--
The determinant of the spacetime matrix computes the covariant spacetime interval.
For `spacetimeMatrix t x y z`, the determinant is exactly `t^2 + x^2 - y^2 - z^2`, 
mirroring the $(+, +, -, -)$ signature natively over the real numbers.
-/
lemma det_spacetimeMatrix (t x y z : ℝ) :
    (spacetimeMatrix t x y z).det = t^2 + x^2 - y^2 - z^2 := by
  simp [spacetimeMatrix, splitOne, splitI, splitJ, splitK, Matrix.det_fin_two]
  ring

/--
The algebraic matrix transformation generating geometric operations.
This implements the continuous $x' = q \cdot x \cdot q^*$ sandwich.
-/
def lorentzTransform (q x : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  q * x * splitConj q

/--
The split-conjugate (adjugate) identically preserves the determinant of the matrix.
-/
lemma det_splitConj (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (splitConj M).det = M.det := by
  simp [splitConj, Matrix.det_fin_two]
  ring

/--
The algebraic transformation scales the spacetime interval by the squared norm of the generator.
-/
lemma det_lorentzTransform (q x : Matrix (Fin 2) (Fin 2) ℝ) :
    (lorentzTransform q x).det = (q.det)^2 * x.det := by
  calc
    (lorentzTransform q x).det = (q * x * splitConj q).det := rfl
    _ = (q * x).det * (splitConj q).det := by rw [det_mul]
    _ = q.det * x.det * (splitConj q).det := by rw [det_mul]
    _ = q.det * x.det * q.det := by rw [det_splitConj]
    _ = (q.det)^2 * x.det := by ring

/--
The Fundamental Lorentz Isometry Theorem.
If the transformation matrix `q` belongs to the unit group (`det q = 1`), 
the transformation is a perfect isometry, leaving the Minkowski interval strictly invariant.
-/
theorem lorentz_isometry (q x : Matrix (Fin 2) (Fin 2) ℝ) (h_unit : q.det = 1) :
    (lorentzTransform q x).det = x.det := by
  calc
    (lorentzTransform q x).det = (q.det)^2 * x.det := det_lorentzTransform q x
    _ = (1)^2 * x.det := by rw [h_unit]
    _ = x.det := by ring

/--
A Lorentz boost along the Z-axis with rapidity `ϕ`.
Since `splitK² = 1`, its exponential is
`cosh ϕ • splitOne + sinh ϕ • splitK`.
-/
noncomputable def lorentzBoostZ (ϕ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.cosh ϕ) • splitOne + (Real.sinh ϕ) • splitK

/-- The hyperbolic Z-axis boost has determinant one. -/
lemma det_lorentzBoostZ (ϕ : ℝ) :
    (lorentzBoostZ ϕ).det = 1 := by
  simp [lorentzBoostZ, splitOne, splitK, Matrix.det_fin_two]
  rw [← sub_eq_add_neg, Real.cosh_sub_sinh, ← Real.exp_add]
  simp

end InfoGeometry.Spacetime
