import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical re-export of the tripotent Peirce calculus

The proof-bearing owner lives in `InfoGeometry.Physics.Algebra`.  This file is
only a canonical namespace facade and does not duplicate the polynomial
projector implementation.
-/

namespace InfoGeometry.Canonical.TripotentPeirceProjectors

export InfoGeometry.Physics.Algebra (
  projPos
  projNeg
  projZero
  projPos_add_projNeg
  projPos_sub_projNeg
  proj_sum_eq_id
  projPos_idempotent
  projNeg_idempotent
  projZero_idempotent
  projPos_mul_projNeg_eq_zero
  projNeg_mul_projPos_eq_zero
  projPos_mul_projZero_eq_zero
  projZero_mul_projPos_eq_zero
  projNeg_mul_projZero_eq_zero
  projZero_mul_projNeg_eq_zero
  mul_projPos
  projPos_mul
  mul_projNeg
  projNeg_mul
  mul_projZero
  projZero_mul
)

/-! The canonical facade exposes the five-sector reconstruction without
duplicating the proof-bearing polynomial projector owner. -/

theorem peirce_five_grade_sum_decomposition
    {R : Type*} [Ring R] [Algebra ℝ R] (e x : R) :
    (projNeg e * x * projPos e) +
        (projZero e * x * projPos e + projNeg e * x * projZero e) +
        (projPos e * x * projPos e + projZero e * x * projZero e +
          projNeg e * x * projNeg e) +
        (projPos e * x * projZero e + projZero e * x * projNeg e) +
        (projPos e * x * projNeg e) = x := by
  calc
    (projNeg e * x * projPos e) +
          (projZero e * x * projPos e + projNeg e * x * projZero e) +
          (projPos e * x * projPos e + projZero e * x * projZero e +
            projNeg e * x * projNeg e) +
          (projPos e * x * projZero e + projZero e * x * projNeg e) +
          (projPos e * x * projNeg e) =
        (projPos e + projZero e + projNeg e) * x *
          (projPos e + projZero e + projNeg e) := by
            noncomm_ring
    _ = 1 * x * 1 := by rw [proj_sum_eq_id]
    _ = x := by simp

end InfoGeometry.Canonical.TripotentPeirceProjectors
