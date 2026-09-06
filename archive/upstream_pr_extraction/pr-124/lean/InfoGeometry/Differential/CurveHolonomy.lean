import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

namespace InfoGeometry.Differential

open MeasureTheory
open UpperHalfPlane

/-- A continuous gauge connection 1-form on the Upper Half-Plane. -/
abbrev Connection1Form
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  UpperHalfPlane → (ℂ →L[ℝ] E)

/-- 
  The curve holonomy defined via Mathlib's native curve integral.
  `γ` is the parameterized boundary path, e.g., the edge of the truncated domain.
-/
noncomputable def pathIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Connection1Form E)
    (γ : ℝ → UpperHalfPlane)
    (a b : ℝ) : E :=
  ∫ t in a..b, A (γ t) (deriv (fun t => (γ t : ℂ)) t)

end InfoGeometry.Differential
