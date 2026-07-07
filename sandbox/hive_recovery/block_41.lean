import Mathlib.Analysis.Complex.CauchyIntegral
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.ComplexAnalyticBridge

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesComplexTranslation
open InfoGeometry.Krein

local notation "H₂_real" => DoubledSpace ℝ

/-- The map connecting ℂ to DoubledSpace ℝ -/
noncomputable def to_doubled_real (z : ℂ) : H₂_real :=
  to_doubled z.re z.im

/-- The canonical complex structure on H₂_real -/
noncomputable def H2_phaseStructure : PhaseStructure H₂_real where
  K := complex_i (E := ℝ)
  K_square := complex_i_sq (E := ℝ)

/-- Map a DoubledSpace R element back to C -/
noncomputable def from_doubled_real (v : H₂_real) : ℂ :=
  Complex.mk (WithLp.fst v) (WithLp.snd v)

/-- Complex analytic functions map to CauchyAnalyticAt -/
noncomputable def analyticAt_implies_cauchyAnalyticAt {f : ℂ → ℂ} {z : ℂ}
    (h_an : AnalyticAt ℂ f z) :
    CauchyAnalyticAt H2_phaseStructure H2_phaseStructure
      (fun v => to_doubled_real (f (from_doubled_real v)))
      (to_doubled_real z) := by
  sorry

end InfoGeometry.Canonical.ComplexAnalyticBridge