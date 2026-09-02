import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace InfoGeometry.Algebra.ZornFiniteSelfAdjoint

open scoped InnerProductSpace

abbrev V := EuclideanSpace ℝ (Fin 8)

/-- Native finite-dimensional self-adjointness criterion for the Zorn coordinate
carrier.  In finite dimension, the adjoint is everywhere defined. -/
theorem isSelfAdjoint_of_inner_symmetric
    (T : V →ₗ[ℝ] V)
    (hT : ∀ x y : V, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) :
    IsSelfAdjoint T := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint T).mp
  exact hT

/-- Skew-adjointness criterion for a finite-dimensional Lax generator. -/
theorem isSkewAdjoint_of_inner_skew
    (T : V →ₗ[ℝ] V)
    (hT : ∀ x y : V, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ) :
    T.adjoint = -T := by
  symm
  apply (LinearMap.eq_adjoint_iff (-T) T).mpr
  intro x y
  change ⟪-(T x), y⟫_ℝ = ⟪x, T y⟫_ℝ
  rw [inner_neg_left, hT]
  simp

end InfoGeometry.Algebra.ZornFiniteSelfAdjoint
