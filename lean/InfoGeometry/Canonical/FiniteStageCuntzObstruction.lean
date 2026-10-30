import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- In a finite square matrix algebra over a stably finite ring, a right
inverse also supplies cancellation on the left. The coefficient ring need
not be commutative. -/
theorem square_matrix_right_inverse_annihilator_iff
    {R ι : Type*} [Ring R] [IsStablyFiniteRing R]
    [Fintype ι] [DecidableEq ι]
    (a b x : Matrix ι ι R) (hab : a * b = 1) :
    a * x = 0 ↔ x = 0 := by
  have hba : b * a = 1 := mul_eq_one_comm.mp hab
  constructor
  · intro hx
    calc
      x = (b * a) * x := by rw [hba, one_mul]
      _ = b * (a * x) := mul_assoc _ _ _
      _ = 0 := by rw [hx, mul_zero]
  · rintro rfl
    exact mul_zero _

/-- Two left-invertible columns cannot have the indicated zero cross-product
in a nonzero finite square matrix algebra over a stably finite ring. This
obstruction is independent of characteristic and of a chosen involution. -/
theorem no_two_square_matrix_inverse_pairs
    {R ι : Type*} [Ring R] [IsStablyFiniteRing R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x₀ y₀ x₁ y₁ : Matrix ι ι R)
    (h₀ : y₀ * x₀ = 1) (h₁ : y₁ * x₁ = 1)
    (hcross : y₀ * x₁ = 0) : False := by
  have hx₁ := (square_matrix_right_inverse_annihilator_iff y₀ x₀ x₁ h₀).mp hcross
  rw [hx₁, mul_zero] at h₁
  exact zero_ne_one h₁

/-- On a finite square real-matrix carrier, an isometry's orthogonal
complementary isometry must vanish. The conclusion isolates the exact
finite-dimensional obstruction before using the second isometry law. -/
theorem orthogonal_isometry_forces_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v w : Matrix ι ι ℝ)
    (hv : v.transpose * v = 1)
    (hvw : v.transpose * w = 0) :
    w = 0 := by
  exact (square_matrix_right_inverse_annihilator_iff v.transpose v w hv).mp hvw

theorem no_two_finite_cuntz_isometries
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v w : Matrix ι ι ℝ)
    (hv : v.transpose * v = 1)
    (hw : w.transpose * w = 1)
    (hvw : v.transpose * w = 0) :
    False := by
  have hwzero := orthogonal_isometry_forces_zero v w hv hvw
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
