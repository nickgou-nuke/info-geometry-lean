import InfoGeometry.Analysis.LaplaceOperatorTransport

noncomputable section

namespace InfoGeometry.Analysis.LaplaceOperatorTransportTests

open MeasureTheory LaplaceTransform LaplaceOperatorTransport

variable {Space : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℂ Space] [CompleteSpace Space]
  {measure : Measure ℝ} {spectral : ℂ}

example {field : ℝ → Space} (converges : LaplaceConvergent measure field spectral) :
    laplaceIntegral measure (fun time => (ContinuousLinearMap.id ℂ Space) (field time))
      spectral = (ContinuousLinearMap.id ℂ Space) (laplaceIntegral measure field spectral) :=
  laplaceIntegral_map (ContinuousLinearMap.id ℂ Space) converges

example {operators : ℝ → Space →L[ℂ] Space}
    (converges : LaplaceConvergent measure operators spectral) (vector : Space) :
    (laplaceIntegral measure operators spectral) vector =
      laplaceIntegral measure (fun time => operators time vector) spectral :=
  laplaceIntegral_apply converges vector

example (symmetry : Space →L[ℂ] Space)
    {operators : ℝ → Space →L[ℂ] Space}
    (converges : LaplaceConvergent measure operators spectral)
    (commutes : ∀ time, symmetry.comp (operators time) = (operators time).comp symmetry) :
    symmetry.comp (laplaceIntegral measure operators spectral) =
      (laplaceIntegral measure operators spectral).comp symmetry :=
  laplaceIntegral_commutes symmetry converges commutes

#print axioms laplaceIntegral_intertwines
#print axioms laplaceIntegral_commutes
#print axioms mellin_logPullback_map

end InfoGeometry.Analysis.LaplaceOperatorTransportTests
