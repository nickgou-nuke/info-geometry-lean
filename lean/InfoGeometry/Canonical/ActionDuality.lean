import Paperproof
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.HeatKernel
import InfoGeometry.Canonical.SpectralInference
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.ActionDuality

Compatibility bridge between the reduced spectral action proxy and
Legendre/Fenchel duality data.
-/

namespace ActionDuality

open InfoGeometry.Geometry
open InfoGeometry.Canonical.QFTTDFTLaunchpad
open InfoGeometry.Canonical.HeatKernel
open InfoGeometry.Canonical.SpectralInference

variable {Θ : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [FiniteDimensional ℝ Θ]

/--
Compatibility between the spectral basepoint log-volume scalar and the primal
potential evaluated at a chosen basepoint `θ₀`.
-/
def SpectralPrimalCompatibility
    (IST : InfoSpectralTriple Θ)
    (ψ : Θ → ℝ)
    (θ₀ : Θ) : Prop :=
  spectralLogVolume IST = ψ θ₀

/--
At a compatible basepoint `θ₀`, the reduced Einstein-Hilbert action proxy is
exactly `-6` times the dual pairing minus the dual potential along the
Hohenberg-Kohn witness covector.
-/
theorem einsteinHilbertAction_eq_neg_six_dual_pairing_sub_dual_of_compatible
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (IST : InfoSpectralTriple Θ)
    (θ₀ : Θ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hCompat : SpectralPrimalCompatibility IST ψ θ₀) :
    ∃ η : Θ →L[ℝ] ℝ,
      einsteinHilbertAction IST = -6 * (η θ₀ - ψStar η) := by
  rcases hHK with ⟨grad, gradStar, hConj, hLeft, hRight, hFY⟩
  clear gradStar hConj hLeft hRight
  refine ⟨grad θ₀, ?_⟩
  rw [einsteinHilbertAction_eq_neg_six_spectralLogVolume, hCompat]
  rw [primal_value_of_fenchelYoungEquality ψ ψStar θ₀ (grad θ₀) (hFY θ₀)]

/--
Compatible basepoint action rewrite together with zero Fenchel gap at the same
dual covector.
-/
theorem einsteinHilbertAction_and_zeroGap_of_compatible
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (IST : InfoSpectralTriple Θ)
    (θ₀ : Θ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hCompat : SpectralPrimalCompatibility IST ψ θ₀) :
    ∃ η : Θ →L[ℝ] ℝ,
      einsteinHilbertAction IST = -6 * (η θ₀ - ψStar η)
      ∧ fenchelGap ψ ψStar θ₀ η = 0 := by
  rcases hHK with ⟨grad, gradStar, hConj, hLeft, hRight, hFY⟩
  clear gradStar hConj hLeft hRight
  refine ⟨grad θ₀, ?_, ?_⟩
  · rw [einsteinHilbertAction_eq_neg_six_spectralLogVolume, hCompat]
    rw [primal_value_of_fenchelYoungEquality ψ ψStar θ₀ (grad θ₀) (hFY θ₀)]
  · exact (fenchelYoungEquality_iff_gap_eq_zero ψ ψStar θ₀ (grad θ₀)).1 (hFY θ₀)

end ActionDuality
