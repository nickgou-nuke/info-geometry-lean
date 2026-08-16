import InfoGeometry.Analysis.FiniteSpectralHeatMellin
import InfoGeometry.Analysis.FiniteSpectralMellinTaylor

/-!
# InfoGeometry.Analysis.SpectralTaylorMellinBridge

Finite spectral bridge between additive Taylor prefixes and multiplicative
Mellin/power moments.

This is the theorem-owned finite part of the slogan that spectral calculus can
be read in two compatible ways:

* as a Taylor prefix in the additive variable;
* as a Mellin/power moment in the multiplicative scaling variable.

No full spectral theorem.
No projection-valued measure.
No unbounded functional calculus.
No Mellin inversion.
-/

namespace InfoGeometry.Analysis.SpectralTaylorMellinBridge

open Finset
open InfoGeometry.Analysis.FiniteSpectralMellinTaylor
open InfoGeometry.Analysis.FiniteSpectralHeatMellin

namespace FiniteSpectralData

variable {ι : Type*} [Fintype ι]

/-- Taylor and Mellin are the same finite moment package on the spectral data. -/
theorem additiveTaylor_mellin_duality
    (D : FiniteSpectralData ι ℂ) (c : ℕ → ℂ) (N : ℕ) :
    InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix D c N =
      ∑ k ∈ Finset.range N,
        c k * InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.mellinMoment D k :=
  rfl

/-- The finite Taylor prefix recursion is the local additive closure law. -/
theorem additiveTaylor_prefix_succ
    (D : FiniteSpectralData ι ℂ) (c : ℕ → ℂ) (N : ℕ) :
    InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix D c (N + 1) =
      InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix D c N +
        c N * InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.mellinMoment D N :=
  InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix_succ D c N

/-- The finite spectral heat readout is a Taylor prefix weighted by the heat coefficients. -/
theorem heatTaylor_as_mellin_prefix
    (D : FiniteSpectralData ι ℂ) (t : ℂ) (N : ℕ) :
    InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorReadout D t N =
      InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix D
        (InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorCoeff t) N :=
  InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorReadout_eq_taylorMomentPrefix D t N

/-- Pointwise agreement of the scalar scaling law gives agreement of the finite readout. -/
theorem scaling_readout_eq_of_pointwise
    (D : FiniteSpectralData ι ℂ)
    (heatMellinScalar scaleScalar : ℂ → ℂ)
    (hpoint : ∀ i : ι, heatMellinScalar (D.spectralValue i) =
      scaleScalar (D.spectralValue i)) :
    InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatMellinReadout D heatMellinScalar =
      InfoGeometry.Analysis.FiniteSpectralHeatMellin.spectralScalingReadout D scaleScalar :=
  InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatMellinReadout_eq_spectralScalingReadout_of_pointwise
    D heatMellinScalar scaleScalar hpoint

/-- The one-term prefix recovers the zeroth Mellin moment with coefficient `c 0`. -/
theorem one_term_recovers_mellin_zero
    (D : FiniteSpectralData ι ℂ) (c : ℕ → ℂ) :
    InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix D c 1 =
      c 0 * InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.mellinMoment D 0 :=
  InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix_one D c

end FiniteSpectralData

/--
Finite spectral packet exposing the additive/Taylor and multiplicative/Mellin
readouts side by side.
-/
structure SpectralTaylorMellinData (ι : Type*) where
  /-- Finite spectral datum. -/
  data : FiniteSpectralData ι ℂ
  /-- Taylor coefficient family. -/
  coeff : ℕ → ℂ
  /-- Scalar heat/Mellin transform. -/
  heatMellinScalar : ℂ → ℂ
  /-- Scalar scaling readout. -/
  scaleScalar : ℂ → ℂ
  /-- Pointwise agreement on the finite spectrum. -/
  hpoint : ∀ i : ι, heatMellinScalar (data.spectralValue i) =
    scaleScalar (data.spectralValue i)

namespace SpectralTaylorMellinData

variable {ι : Type*} [Fintype ι]

/-- The finite heat readout is the finite Taylor/Mellin prefix. -/
theorem heat_readout_eq_prefix (P : SpectralTaylorMellinData ι) (t : ℂ) (N : ℕ) :
    InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorReadout P.data t N =
      InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix P.data
        (InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorCoeff t) N :=
  InfoGeometry.Analysis.SpectralTaylorMellinBridge.FiniteSpectralData.heatTaylor_as_mellin_prefix
    P.data t N

/-- The finite scalar Mellin readout equals the finite spectral scaling readout. -/
theorem scalar_readout_eq (P : SpectralTaylorMellinData ι) :
    InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatMellinReadout P.data P.heatMellinScalar =
      InfoGeometry.Analysis.FiniteSpectralHeatMellin.spectralScalingReadout P.data P.scaleScalar :=
  InfoGeometry.Analysis.SpectralTaylorMellinBridge.FiniteSpectralData.scaling_readout_eq_of_pointwise
    P.data P.heatMellinScalar P.scaleScalar P.hpoint

/-- The finite Taylor prefix recursion is preserved in the packet. -/
theorem prefix_succ (P : SpectralTaylorMellinData ι) (N : ℕ) :
    InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix P.data P.coeff
        (N + 1) =
      InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix P.data P.coeff
        N +
      P.coeff N *
        InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.mellinMoment P.data N :=
  InfoGeometry.Analysis.SpectralTaylorMellinBridge.FiniteSpectralData.additiveTaylor_prefix_succ
    P.data P.coeff N

end SpectralTaylorMellinData

end InfoGeometry.Analysis.SpectralTaylorMellinBridge
