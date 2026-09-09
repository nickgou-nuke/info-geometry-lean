import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace InfoGeometry.Canonical.ZornFiniteSelfAdjoint

open scoped InnerProductSpace

abbrev V := EuclideanSpace ℝ (Fin 8)

theorem isSelfAdjoint_of_inner_symmetric
    (T : V →ₗ[ℝ] V)
    (hT : ∀ x y : V, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) :
    IsSelfAdjoint T := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint T).mp
  exact hT

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

end InfoGeometry.Canonical.ZornFiniteSelfAdjoint
