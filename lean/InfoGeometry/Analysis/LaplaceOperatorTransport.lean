import InfoGeometry.Analysis.LaplaceFourierComparison
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

namespace InfoGeometry.Analysis.LaplaceOperatorTransport

open MeasureTheory LaplaceTransform LaplaceFourierComparison

variable {Source Target : Type*}
  [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]
  {measure : Measure ℝ} {spectral : ℂ}

theorem laplaceConvergent_map (transport : Source →L[ℂ] Target)
    {field : ℝ → Source} (converges : LaplaceConvergent measure field spectral) :
    LaplaceConvergent measure (fun time => transport (field time)) spectral := by
  simpa only [LaplaceConvergent, map_smul] using transport.integrable_comp converges

theorem laplaceIntegral_map (transport : Source →L[ℂ] Target)
    {field : ℝ → Source} (converges : LaplaceConvergent measure field spectral) :
    laplaceIntegral measure (fun time => transport (field time)) spectral =
      transport (laplaceIntegral measure field spectral) := by
  simpa only [laplaceIntegral, map_smul] using transport.integral_comp_comm converges

theorem laplaceConvergent_apply {operators : ℝ → Source →L[ℂ] Target}
    (converges : LaplaceConvergent measure operators spectral) (vector : Source) :
    LaplaceConvergent measure (fun time => operators time vector) spectral := by
  exact laplaceConvergent_map (ContinuousLinearMap.apply ℂ Target vector) converges

theorem laplaceIntegral_apply {operators : ℝ → Source →L[ℂ] Target}
    (converges : LaplaceConvergent measure operators spectral) (vector : Source) :
    (laplaceIntegral measure operators spectral) vector =
      laplaceIntegral measure (fun time => operators time vector) spectral := by
  exact (laplaceIntegral_map (ContinuousLinearMap.apply ℂ Target vector) converges).symm

theorem laplaceIntegral_intertwines (transport : Source →L[ℂ] Target)
    {sourceFamily : ℝ → Source →L[ℂ] Source}
    {targetFamily : ℝ → Target →L[ℂ] Target}
    (sourceConverges : LaplaceConvergent measure sourceFamily spectral)
    (targetConverges : LaplaceConvergent measure targetFamily spectral)
    (intertwines : ∀ time, transport.comp (sourceFamily time) =
      (targetFamily time).comp transport) :
    transport.comp (laplaceIntegral measure sourceFamily spectral) =
      (laplaceIntegral measure targetFamily spectral).comp transport := by
  ext vector
  change transport ((laplaceIntegral measure sourceFamily spectral) vector) =
    (laplaceIntegral measure targetFamily spectral) (transport vector)
  rw [laplaceIntegral_apply sourceConverges, laplaceIntegral_apply targetConverges]
  rw [← laplaceIntegral_map transport (laplaceConvergent_apply sourceConverges vector)]
  apply congrArg (fun field : ℝ → Target => laplaceIntegral measure field spectral)
  funext time
  exact congrArg (fun operator : Source →L[ℂ] Target => operator vector) (intertwines time)

theorem laplaceIntegral_commutes (symmetry : Source →L[ℂ] Source)
    {operators : ℝ → Source →L[ℂ] Source}
    (converges : LaplaceConvergent measure operators spectral)
    (commutes : ∀ time, symmetry.comp (operators time) = (operators time).comp symmetry) :
    symmetry.comp (laplaceIntegral measure operators spectral) =
      (laplaceIntegral measure operators spectral).comp symmetry := by
  exact laplaceIntegral_intertwines symmetry converges converges commutes

theorem mellin_logPullback_map (transport : Source →L[ℂ] Target)
    {field : ℝ → Source} (converges : LaplaceConvergent volume field spectral) :
    mellin (fun time : ℝ => transport (field (-Real.log time))) spectral =
      transport (mellin (fun time : ℝ => field (-Real.log time)) spectral) := by
  change mellin (fun time : ℝ => (fun parameter => transport (field parameter))
    (-Real.log time)) spectral = _
  change mellin (fun time : ℝ => transport (field (-Real.log time))) spectral = _
  rw [mellin_logPullback_eq_laplaceTransform
    (f := fun parameter => transport (field parameter))]
  rw [← laplaceIntegral_map transport converges]
  exact laplaceIntegral_map transport converges

end InfoGeometry.Analysis.LaplaceOperatorTransport
