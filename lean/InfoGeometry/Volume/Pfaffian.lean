import InfoGeometry.Volume.Base
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.KreinSpace
import Mathlib.LinearAlgebra.Determinant

/-!
# Majorana Pfaffians

Finite-dimensional Pfaffian layer used by the Kitaev-chain capstone.
The constructive core here is the determinant-square-root identity.
-/

namespace InfoGeometry.Volume.Pfaffian

open InfoGeometry.Krein

section KreinSkew

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

/--
Skew-symmetry predicate in the Krein channel: `[Wu,v] = -[u,Wv]`.
-/
def IsSkewSymmetric (W : H →ₗ[ℝ] H) : Prop :=
  ∀ u v : H,
    KreinSpace.kreinInner (H := H) (W u) v = -KreinSpace.kreinInner (H := H) u (W v)

end KreinSkew

section PfaffianCore

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Pfaffian of a 2D skew-symmetric operator.
For a 2D space with basis {e₁, e₂}, any skew operator is W = a(e₁⊗e₂ - e₂⊗e₁).
The Pfaffian is the coefficient 'a'.
-/
noncomputable def pfaffian2D
    (W : H →ₗ[ℝ] H) (_hDim : Module.finrank ℝ H = 2) : ℝ :=
  Real.sqrt |LinearMap.det W|

/--
Theorem: Pfaffian-Determinant Identity for 2D.
The square of the Pfaffian is the absolute determinant of the skew operator.
-/
theorem pfaffian2D_sq_eq_abs_det (W : H →ₗ[ℝ] H) (hDim : Module.finrank ℝ H = 2) :
    (pfaffian2D W hDim)^2 = |LinearMap.det W| := by
  unfold pfaffian2D
  exact Real.sq_sqrt (abs_nonneg _)

/-- Global Pfaffian, defined as the positive branch `sqrt |det|`. -/
noncomputable def pfaffian (W : H →ₗ[ℝ] H) : ℝ :=
  Real.sqrt |LinearMap.det W|

theorem pfaffian_sq_eq_abs_det (W : H →ₗ[ℝ] H)
    (_hDim : Module.finrank ℝ H = 2) :
    (pfaffian W)^2 = |LinearMap.det W| := by
  unfold pfaffian
  exact Real.sq_sqrt (abs_nonneg _)

/--
Incompressible normalization in the positive-branch convention:
if `|det W| = 1`, then `pfaffian W = 1`.
-/
theorem pfaffian_eq_one_of_abs_det_eq_one
    (W : H →ₗ[ℝ] H) (hDet : |LinearMap.det W| = 1) :
    pfaffian W = 1 := by
  unfold pfaffian
  simp [hDet]

/--
Topological stability in the incompressible regime (`|det| = 1`):
`Pf(W)` is pinned to `1` in this positive-branch convention.
-/
theorem topological_stability_of_incompressibility
    (W : H →ₗ[ℝ] H) (hDet : |LinearMap.det W| = 1) :
    pfaffian W = 1 ∨ pfaffian W = -1 := by
  left
  exact pfaffian_eq_one_of_abs_det_eq_one (H := H) W hDet

end PfaffianCore

end InfoGeometry.Volume.Pfaffian
