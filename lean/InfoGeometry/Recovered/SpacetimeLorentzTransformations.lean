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
  have h00 : spacetimeMatrix t x y z 0 0 = t + z := by
    simp only [spacetimeMatrix, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitI, splitJ, splitK, smul_eq_mul]
  have h01 : spacetimeMatrix t x y z 0 1 = x + y := by
    simp only [spacetimeMatrix, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitI, splitJ, splitK, smul_eq_mul]
  have h10 : spacetimeMatrix t x y z 1 0 = -x + y := by
    simp only [spacetimeMatrix, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitI, splitJ, splitK, smul_eq_mul]
  have h11 : spacetimeMatrix t x y z 1 1 = t - z := by
    simp only [spacetimeMatrix, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitI, splitJ, splitK, smul_eq_mul,
      sub_eq_add_neg]
  rw [Matrix.det_fin_two, h00, h01, h10, h11]
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
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  change M 1 1 * M 0 0 - (-M 0 1) * (-M 1 0) = _
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
  have h00 : lorentzBoostZ ϕ 0 0 = Real.cosh ϕ + Real.sinh ϕ := by
    simp only [lorentzBoostZ, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitK, smul_eq_mul]
  have h01 : lorentzBoostZ ϕ 0 1 = 0 := by
    simp only [lorentzBoostZ, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitK, smul_eq_mul]
  have h10 : lorentzBoostZ ϕ 1 0 = 0 := by
    simp only [lorentzBoostZ, Matrix.add_apply, Matrix.smul_apply]
    simp [splitOne, splitK, smul_eq_mul]
  have h11 : lorentzBoostZ ϕ 1 1 = Real.cosh ϕ - Real.sinh ϕ := by
    change (Real.cosh ϕ • splitOne) 1 1 +
      (Real.sinh ϕ • splitK) 1 1 = _
    have hone : splitOne 1 1 = 1 := by simp [splitOne]
    have hK : splitK 1 1 = -1 := by simp [splitK]
    rw [Matrix.smul_apply, Matrix.smul_apply, hone, hK, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [Matrix.det_fin_two, h00, h01, h10]
  rw [h11]
  simp only [mul_zero, sub_zero]
  calc
    (Real.cosh ϕ + Real.sinh ϕ) *
        (Real.cosh ϕ - Real.sinh ϕ) =
        Real.cosh ϕ ^ 2 - Real.sinh ϕ ^ 2 := by ring
    _ = 1 := Real.cosh_sq_sub_sinh_sq ϕ

end InfoGeometry.Spacetime
