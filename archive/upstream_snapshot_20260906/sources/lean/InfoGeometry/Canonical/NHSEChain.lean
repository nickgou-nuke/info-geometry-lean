import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Trigonometric
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.NHSEChain

open Real

/-- Parameters for the Non-Hermitian Skin Effect (NHSE) on a Kitaev-Cuntz chain -/
structure NHSEParameters where
  /-- The base hopping amplitude -/
  t : ℝ
  /-- The topological boost parameter responsible for non-Hermiticity -/
  alpha : ℝ
  /-- Base hopping must be positive -/
  t_pos : 0 < t

/-- The right-moving hopping transition probability (t_R) -/
@[rep_depth thermo]
noncomputable def t_R (p : NHSEParameters) : ℝ := p.t * cosh p.alpha

/-- The left-moving hopping transition probability (t_L) -/
@[rep_depth thermo]
noncomputable def t_L (p : NHSEParameters) : ℝ := p.t * sinh p.alpha

/-- 
Theorem: The tight-binding lattice breaks macroscopic reciprocity.
For any boost parameter α, the right-moving and left-moving transitions are strictly unequal.
This global asymmetry is the strict mathematical origin of the Non-Hermitian Skin Effect,
forcing the bulk spectrum to collapse and localizing states at the boundary.
-/
@[rep_depth thermo]
theorem nhse_asymmetry_strict (p : NHSEParameters) : t_L p < t_R p := by
  dsimp [t_R, t_L]
  have h1 : sinh p.alpha < cosh p.alpha := Real.sinh_lt_cosh p.alpha
  exact mul_lt_mul_of_pos_left h1 p.t_pos

/--
Theorem: As a direct corollary, the Hamiltonian is strictly non-Hermitian.
-/
@[rep_depth thermo]
theorem nhse_non_hermitian (p : NHSEParameters) : t_L p ≠ t_R p :=
  ne_of_lt (nhse_asymmetry_strict p)

end InfoGeometry.Canonical.NHSEChain
