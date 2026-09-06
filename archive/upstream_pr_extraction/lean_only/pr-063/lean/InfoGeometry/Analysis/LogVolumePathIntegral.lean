import InfoGeometry.Analysis.LogVolumeExactDifferential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace InfoGeometry.Analysis.LogVolumePathIntegral

open MeasureTheory
open scoped Interval
open InfoGeometry.Analysis.LogVolumeEntropyRate
open InfoGeometry.Analysis.LogVolumeExactDifferential

/--
The integral of the exact logarithmic-volume differential is the endpoint
difference of its global potential.
-/
theorem integral_logVolumeDifferential_eq_sub
    {Q : ℝ → ℝ}
    {a b : ℝ}
    (hQ :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ Q t)
    (hQ₀ :
      ∀ t ∈ Set.uIcc a b,
        Q t ≠ 0)
    (hint :
      IntervalIntegrable
        (logVolumeDifferential Q)
        volume a b) :
    ∫ t in a..b, logVolumeDifferential Q t =
      logVolumePotential Q b -
        logVolumePotential Q a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    simpa [logVolumeDifferential, logVolumeRate] using
      (hasDerivAt_logVolumePotential
        (hQ t ht).hasDerivAt (hQ₀ t ht))
  · exact hint

/--
A globally defined logarithmic-volume differential has zero integral when its
volume path has equal endpoints.
-/
theorem integral_logVolumeDifferential_eq_zero_of_endpoints_eq
    {Q : ℝ → ℝ}
    {a b : ℝ}
    (hQ :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ Q t)
    (hQ₀ :
      ∀ t ∈ Set.uIcc a b,
        Q t ≠ 0)
    (hint :
      IntervalIntegrable
        (logVolumeDifferential Q)
        volume a b)
    (hloop : Q b = Q a) :
    ∫ t in a..b, logVolumeDifferential Q t = 0 := by
  rw [integral_logVolumeDifferential_eq_sub hQ hQ₀ hint]
  unfold logVolumePotential
  rw [hloop, sub_self]

/--
The integrated negative logarithmic-volume rate is the endpoint difference of
the compression potential.
-/
theorem integral_neg_logVolumeDifferential_eq_compressionPotential_sub
    {Q : ℝ → ℝ}
    {a b : ℝ}
    (hQ :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ Q t)
    (hQ₀ :
      ∀ t ∈ Set.uIcc a b,
        Q t ≠ 0)
    (hint :
      IntervalIntegrable
        (logVolumeDifferential Q)
        volume a b) :
    ∫ t in a..b, -logVolumeDifferential Q t =
      compressionPotential Q b -
        compressionPotential Q a := by
  rw [intervalIntegral.integral_neg]
  rw [integral_logVolumeDifferential_eq_sub hQ hQ₀ hint]
  unfold compressionPotential logVolumePotential
  ring

/-- A closed scalar volume path has zero integrated compression rate. -/
theorem integral_neg_logVolumeDifferential_eq_zero_of_endpoints_eq
    {Q : ℝ → ℝ}
    {a b : ℝ}
    (hQ :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ Q t)
    (hQ₀ :
      ∀ t ∈ Set.uIcc a b,
        Q t ≠ 0)
    (hint :
      IntervalIntegrable
        (logVolumeDifferential Q)
        volume a b)
    (hloop : Q b = Q a) :
    ∫ t in a..b, -logVolumeDifferential Q t = 0 := by
  rw [integral_neg_logVolumeDifferential_eq_compressionPotential_sub
    hQ hQ₀ hint]
  unfold compressionPotential
  rw [hloop, sub_self]

end InfoGeometry.Analysis.LogVolumePathIntegral
