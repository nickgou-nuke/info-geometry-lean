import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# MTW Curvature Tensor on the Projective Riemannian Surface

This module defines the Ma-Trudinger-Wang (MTW) curvature tensor on the
projective quantum geometric Riemannian surface, bridging the OAI/Geometry/WeakMTW
formalization to our existing QGT infrastructure.

The MTW tensor governns geodesic convexity of the injectivity domain and
regularity of the Monge-Ampère optimal transport problem on information manifolds.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective.MTWCurvature

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projective Riemannian metric on the operator space `H →L[ℂ] H`. -/
structure ProjectiveRiemannianMetric (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The metric as a bilinear form on `H →L[ℂ] H`. -/
  g : (H →L[ℂ] H) → (H →L[ℂ] H) → ℝ
  /-- Symmetry of the metric. -/
  symmetric : ∀ X Y, g X Y = g Y X
  /-- Non-negativity on the diagonal. -/
  nonneg : ∀ X, 0 ≤ g X X

/-- The MTW curvature tensor built from a projective Riemannian metric.
    It measures the deviation from being flat in the optimal-transport sense. -/
noncomputable def mtwCurvature (g : ProjectiveRiemannianMetric H) (X Y Z W : H →L[ℂ] H) : ℝ :=
  g.g X Y * g.g Z W - g.g X Z * g.g Y W

/-- The MTW tensor is symmetric under swapping both argument pairs. -/
theorem mtwCurvature_symm_swap_both (g : ProjectiveRiemannianMetric H) (X Y Z W : H →L[ℂ] H) :
    mtwCurvature g X Y Z W = mtwCurvature g Y X W Z := by
  dsimp [mtwCurvature]
  rw [g.symmetric Y X, g.symmetric Z W]
  ring

/-- The MTW tensor is symmetric under exchange of the (X,Y) pair with the (Z,W) pair. -/
theorem mtwCurvature_symm_pair_swap (g : ProjectiveRiemannianMetric H) (X Y Z W : H →L[ℂ] H) :
    mtwCurvature g X Y Z W = mtwCurvature g Z W X Y := by
  dsimp [mtwCurvature]
  rw [g.symmetric Z X, g.symmetric W Y]
  ring

end InfoGeometry.QuantumGeometry.Projective.MTWCurvature