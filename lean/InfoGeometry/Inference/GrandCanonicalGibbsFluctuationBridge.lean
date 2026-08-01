/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Inference.GibbsTemperatureResponse
import InfoGeometry.Inference.GibbsFluctuation
import InfoGeometry.Inference.GibbsTemperatureSusceptibility

/-!
# Grand-canonical variance and finite Gibbs dispersion

The grand-canonical finite-state variance and the generic Gibbs weighted
variance are the same finite object on the canonical energy slice.  This
bridge exposes that identity and transfers the pairwise coherence criterion
to the existing temperature-susceptibility API.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators
open InfoGeometry.GrandCanonical
open InfoGeometry.Inference

variable {Data : Type*} [Fintype Data] [Nonempty Data]

/-- Grand-canonical variance is the generic Gibbs weighted variance. -/
theorem grandCanonicalVariance_eq_weightedVariance
    (E : Data → ℝ) (β : ℝ) :
    variance E β =
      weightedVariance (gibbsWeight E β) E := by
  rfl

/-- Temperature susceptibility is the same pairwise Gibbs dispersion. -/
theorem temperatureSusceptibility_eq_weightedVariance
    (E : Data → ℝ) (ε : ℝ) :
    temperatureSusceptibility E ε =
      weightedVariance (gibbsWeight E ε⁻¹) E := by
  unfold temperatureSusceptibility
  exact grandCanonicalVariance_eq_weightedVariance E ε⁻¹

/-- Zero temperature susceptibility is exactly pairwise energy agreement. -/
theorem temperatureSusceptibility_eq_zero_iff_pairwise
    (E : Data → ℝ) (ε : ℝ) :
    temperatureSusceptibility E ε = 0 ↔ ∀ i j, E i = E j := by
  rw [temperatureSusceptibility_eq_weightedVariance]
  exact weightedVariance_eq_zero_iff_of_pos
    (gibbsWeight E ε⁻¹) E
    (gibbsWeight_sum_one E ε⁻¹)
    (fun i => gibbsWeight_pos E ε⁻¹ i)

/--
The temperature derivative of the finite Gibbs mean is susceptibility divided
by the inverse-temperature Jacobian `ε²`.
-/
theorem deriv_mean_at_temperature_eq_susceptibility_div_sq
    (params : GrandCanonicalParams Data) {ε : ℝ} (hε : 0 < ε) :
    deriv (fun t : ℝ => mean params t⁻¹) ε =
      temperatureSusceptibility params.energy ε / ε ^ (2 : ℕ) := by
  rw [InfoGeometry.GrandCanonical.deriv_mean_at_inverse_temperature params hε]
  rfl

end InfoGeometry.Inference.FiniteGibbs
