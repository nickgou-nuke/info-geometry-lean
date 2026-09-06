import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

namespace InfoGeometry.Canonical

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower

/-!
# Finite-stage obstruction for the Cuntz isometry relations

Two isometries with orthogonal ranges cannot exist in a nonzero finite square
matrix algebra.  This is the algebraic obstruction behind the need for the
infinite Hilbert/Cantor representation of the Cuntz shift.
-/

theorem no_two_finite_cuntz_isometries
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v w : Matrix ι ι ℝ)
    (hv : v.transpose * v = 1)
    (hw : w.transpose * w = 1)
    (hvw : v.transpose * w = 0) :
    False := by
  have hvdet : v.det ≠ 0 := by
    exact Matrix.det_ne_zero_of_left_inverse hv
  have hvunit : IsUnit v.det := isUnit_iff_ne_zero.mpr hvdet
  have hright : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v hvunit
  have hvt : v.transpose = v⁻¹ := by
    calc
      v.transpose = v.transpose * 1 := by simp
      _ = v.transpose * (v * v⁻¹) := by rw [hright]
      _ = (v.transpose * v) * v⁻¹ := by rw [Matrix.mul_assoc]
      _ = v⁻¹ := by rw [hv]; simp
  have hwzero : w = 0 := by
    have hleft : v⁻¹ * w = 0 := by simpa [hvt] using hvw
    calc
      w = 1 * w := by simp
      _ = (v * v⁻¹) * w := by rw [hright]
      _ = v * (v⁻¹ * w) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hleft, mul_zero]
  have hbad : (0 : Matrix ι ι ℝ) = 1 := by
    rw [hwzero] at hw
    simpa only [transpose_zero, zero_mul] using hw
  have hdiag := congrFun
    (congrFun hbad (Classical.choice (inferInstance : Nonempty ι)))
    (Classical.choice (inferInstance : Nonempty ι))
  simp at hdiag

theorem no_two_finite_stage_cuntz_isometries
    (n : ℕ)
    (v w : MatStage n)
    (hv : v.transpose * v = 1)
    (hw : w.transpose * w = 1)
    (hvw : v.transpose * w = 0) :
    False := by
  exact no_two_finite_cuntz_isometries v w hv hw hvw

end InfoGeometry.Canonical
