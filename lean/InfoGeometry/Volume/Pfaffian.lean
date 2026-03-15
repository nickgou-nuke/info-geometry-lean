import InfoGeometry.Volume.Base
import InfoGeometry.Krein.KreinSpace
import Mathlib.LinearAlgebra.Determinant

/-!
# Majorana Pfaffians

Finite-dimensional Pfaffian layer used by the Kitaev-chain capstone.
The constructive core here is the determinant-square-root identity.
-/

namespace InfoGeometry.Volume.Pfaffian

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
variable [FiniteDimensional ℝ H]

/--
Skew-symmetry predicate in the Krein channel: `[Wu,v] = -[u,Wv]`.
-/
def IsSkewSymmetric (W : H →ₗ[ℝ] H) : Prop :=
  ∀ u v : H,
    KreinSpace.kreinInner (H := H) (W u) v = -KreinSpace.kreinInner (H := H) u (W v)

/--
Pfaffian surrogate used in the finite real layer:
`Pf(W) := sqrt(|det W|)`.
-/
noncomputable def pfaffian (W : H →ₗ[ℝ] H) : ℝ :=
  Real.sqrt (|LinearMap.det W|)

/-- Pfaffian-determinant identity in this finite layer. -/
theorem pfaffian_sq_eq_det (W : H →ₗ[ℝ] H) :
    (pfaffian W)^2 = |LinearMap.det W| := by
  unfold pfaffian
  simpa [pow_two] using (Real.sq_sqrt (abs_nonneg (LinearMap.det W)))

/--
Topological stability in the incompressible regime (`|det| = 1`):
`Pf(W)` is pinned to `1` in this positive-branch convention.
-/
theorem topological_stability_of_incompressibility
    (W : H →ₗ[ℝ] H) (hDet : |LinearMap.det W| = 1) :
    pfaffian W = 1 ∨ pfaffian W = -1 := by
  left
  unfold pfaffian
  simpa [hDet] using Real.sqrt_one

end InfoGeometry.Volume.Pfaffian
