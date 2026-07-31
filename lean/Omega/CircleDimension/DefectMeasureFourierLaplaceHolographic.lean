import Mathlib.Data.Complex.Basic
import Omega.CircleDimension.ComovingHorizonScanFourierInversion
import Omega.TypedAddressBiaxialCompletion.ComovingFingerprint

namespace Omega.CircleDimension

open Omega.TypedAddressBiaxialCompletion
open scoped BigOperators

noncomputable section

/-- Concrete data for the finite-measure Fourier-Laplace fingerprint wrapper. The only external
input is an interval on which the underlying comoving Fourier-Laplace transform is already known
to be unique. -/
structure DefectMeasureFourierLaplaceData where
  κ : ℕ
  interval : Set ℝ
  hInterval : ComovingOpenIntervalInjective κ interval
  lorentzProfileModel : Prop
  explicitFourierFormulaInput : Prop
  positiveFrequencyRestriction : Prop
  integrableAnalyticProfile : Prop
  lorentzProfileModel_h : lorentzProfileModel
  explicitFourierFormulaInput_h : explicitFourierFormulaInput
  positiveFrequencyRestriction_h : positiveFrequencyRestriction
  integrableAnalyticProfile_h : integrableAnalyticProfile

/-- A bundled two-parameter Fourier-Laplace fingerprint attached to a finite atomic family. -/
structure TensorizedFingerprint (κ : ℕ) where
  family : ComovingFingerprintFamily κ
  eval : ℝ → ℝ → ℂ
  eval_eq : eval = comovingFingerprint family

namespace DefectMeasureFourierLaplaceData

/-- Every finite atomic defect family admits a bundled two-parameter Fourier-Laplace fingerprint
whose `ξ`-dependence is a finite exponential sum for each fixed Laplace parameter. -/
def tensorizedFingerprint (D : DefectMeasureFourierLaplaceData) : Prop :=
  ∀ ν : ComovingFingerprintFamily D.κ, ∀ s : ℝ,
    ∃ F : TensorizedFingerprint D.κ, F.family = ν ∧
      ∃ A : Fin D.κ → ℂ, ∃ z : Fin D.κ → ℂ,
        ∀ ξ : ℝ, F.eval ξ s = ∑ j, A j * Complex.exp (z j * (ξ : ℂ))

/-- Uniqueness of the finite-measure Fourier-Laplace fingerprint map. -/
def fingerprintInjective (D : DefectMeasureFourierLaplaceData) : Prop :=
  Function.Injective (fun ν : ComovingFingerprintFamily D.κ => comovingFingerprint ν)

end DefectMeasureFourierLaplaceData

/-- The comoving-horizon Fourier inversion package yields a bundled two-parameter fingerprint for
each finite atomic defect measure, and uniqueness on a nonempty open interval upgrades to global
injectivity of the Fourier-Laplace transform on this finite-measure class.
    prop:cdim-defect-measure-fourier-laplace-holographic -/
theorem paper_cdim_defect_measure_fourier_laplace_holographic
    (D : DefectMeasureFourierLaplaceData) : D.tensorizedFingerprint ∧ D.fingerprintInjective := by
  have hScan :
      D.integrableAnalyticProfile ∧ ComovingFiniteExponentialSpectrum D.κ ∧
        ComovingOpenIntervalInjective D.κ D.interval :=
    paper_cdim_comoving_horizon_scan_fourier_inversion
      D.integrableAnalyticProfile_h D.lorentzProfileModel_h
      D.explicitFourierFormulaInput_h D.positiveFrequencyRestriction_h D.hInterval
      (fun _ _ => comovingFingerprint_integral_representation D.κ)
      (fun _ _ => comovingFingerprint_finite_exponential_spectrum D.κ)
      (fun _ hI => hI)
      (fun _ => comovingFingerprint_finite_exponential_spectrum D.κ)
      (fun _ hI => hI)
  have hSpectrum : ComovingFiniteExponentialSpectrum D.κ := hScan.2.1
  refine ⟨?_, ?_⟩
  · intro ν s
    obtain ⟨A, z, hA⟩ := hSpectrum ν s
    refine ⟨⟨ν, comovingFingerprint ν, rfl⟩, rfl, A, z, ?_⟩
    intro ξ
    simpa using hA ξ
  · exact comovingFingerprintFamilyInjective_of_interval D.hInterval

end

end Omega.CircleDimension
