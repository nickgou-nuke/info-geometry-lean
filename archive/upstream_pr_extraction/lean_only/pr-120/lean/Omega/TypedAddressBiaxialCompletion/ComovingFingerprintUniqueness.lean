import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed
import Omega.TypedAddressBiaxialCompletion.ComovingHankel

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing typed-address wrapper for the comoving fingerprint uniqueness package: the
Fourier-Laplace representation is finite-atomic, finite-spectrum uniqueness makes the fingerprint
injective, and the kernel/Hankel package identifies `ν`, `H_ν`, `F_ν`, and `K_ν` on any nonempty
open interval.
    prop:unit-circle-comoving-fingerprint-uniqueness -/
theorem paper_typed_address_biaxial_completion_comoving_fingerprint_uniqueness
    {lorentzProfileModel explicitFourierFormulaInput positiveFrequencyRestriction
      intervalUniquenessPrinciple fourierClosedForm finiteExponentialSpectrum openIntervalInjective
      generalPosition hankelFactorization hankelRankCertificate
      fingerprintIntegralRepresentation fingerprintInjective intervalFingerprintKernelEquivalence : Prop}
    (hGeneralPosition : generalPosition)
    (hLorentzProfileModel : lorentzProfileModel)
    (hExplicitFourierFormulaInput : explicitFourierFormulaInput)
    (hPositiveFrequencyRestriction : positiveFrequencyRestriction)
    (hIntervalUniquenessPrinciple : intervalUniquenessPrinciple)
    (deriveFourierClosedForm :
      lorentzProfileModel → explicitFourierFormulaInput → fourierClosedForm)
    (deriveFiniteExponentialSpectrum :
      fourierClosedForm → positiveFrequencyRestriction → finiteExponentialSpectrum)
    (deriveOpenIntervalInjective :
      finiteExponentialSpectrum → intervalUniquenessPrinciple → openIntervalInjective)
    (deriveFingerprintIntegralRepresentation :
      fourierClosedForm → fingerprintIntegralRepresentation)
    (deriveFingerprintInjective :
      finiteExponentialSpectrum → openIntervalInjective → fingerprintInjective)
    (deriveHankelFactorization : generalPosition → hankelFactorization)
    (deriveHankelRankCertificate : hankelFactorization → hankelRankCertificate)
    (deriveIntervalFingerprintKernelEquivalence :
      fingerprintIntegralRepresentation →
      hankelFactorization →
      hankelRankCertificate →
      intervalFingerprintKernelEquivalence) :
    fingerprintIntegralRepresentation ∧ fingerprintInjective ∧
      intervalFingerprintKernelEquivalence := by
  have hFourier : fourierClosedForm ∧ finiteExponentialSpectrum ∧ openIntervalInjective :=
    paper_typed_address_biaxial_completion_comoving_fourier_closed
      hLorentzProfileModel hExplicitFourierFormulaInput
      hPositiveFrequencyRestriction hIntervalUniquenessPrinciple
      deriveFourierClosedForm deriveFiniteExponentialSpectrum deriveOpenIntervalInjective
  rcases hFourier with ⟨hClosed, hSpectrum, hOpenIntervalInjective⟩
  have hIntegral : fingerprintIntegralRepresentation :=
    deriveFingerprintIntegralRepresentation hClosed
  have hInjective : fingerprintInjective :=
    deriveFingerprintInjective hSpectrum hOpenIntervalInjective
  have hHankel : hankelFactorization ∧ hankelRankCertificate :=
    paper_typed_address_biaxial_completion_comoving_hankel
      hGeneralPosition deriveHankelFactorization deriveHankelRankCertificate
  rcases hHankel with ⟨hFactorization, hRank⟩
  exact ⟨hIntegral, hInjective,
    deriveIntervalFingerprintKernelEquivalence hIntegral hFactorization hRank⟩

/-- Unit-circle paper-label wrapper for the typed-address comoving fingerprint uniqueness package.
    prop:unit-circle-comoving-fingerprint-uniqueness -/
theorem paper_unit_circle_comoving_fingerprint_uniqueness
    {lorentzProfileModel explicitFourierFormulaInput positiveFrequencyRestriction
      intervalUniquenessPrinciple fourierClosedForm finiteExponentialSpectrum openIntervalInjective
      generalPosition hankelFactorization hankelRankCertificate
      fingerprintIntegralRepresentation fingerprintInjective intervalFingerprintKernelEquivalence : Prop}
    (hGeneralPosition : generalPosition)
    (hLorentzProfileModel : lorentzProfileModel)
    (hExplicitFourierFormulaInput : explicitFourierFormulaInput)
    (hPositiveFrequencyRestriction : positiveFrequencyRestriction)
    (hIntervalUniquenessPrinciple : intervalUniquenessPrinciple)
    (deriveFourierClosedForm :
      lorentzProfileModel → explicitFourierFormulaInput → fourierClosedForm)
    (deriveFiniteExponentialSpectrum :
      fourierClosedForm → positiveFrequencyRestriction → finiteExponentialSpectrum)
    (deriveOpenIntervalInjective :
      finiteExponentialSpectrum → intervalUniquenessPrinciple → openIntervalInjective)
    (deriveFingerprintIntegralRepresentation :
      fourierClosedForm → fingerprintIntegralRepresentation)
    (deriveFingerprintInjective :
      finiteExponentialSpectrum → openIntervalInjective → fingerprintInjective)
    (deriveHankelFactorization : generalPosition → hankelFactorization)
    (deriveHankelRankCertificate : hankelFactorization → hankelRankCertificate)
    (deriveIntervalFingerprintKernelEquivalence :
      fingerprintIntegralRepresentation →
      hankelFactorization →
      hankelRankCertificate →
      intervalFingerprintKernelEquivalence) :
    fingerprintIntegralRepresentation ∧ fingerprintInjective ∧
      intervalFingerprintKernelEquivalence := by
  exact paper_typed_address_biaxial_completion_comoving_fingerprint_uniqueness
    hGeneralPosition
    hLorentzProfileModel hExplicitFourierFormulaInput
    hPositiveFrequencyRestriction hIntervalUniquenessPrinciple
    deriveFourierClosedForm deriveFiniteExponentialSpectrum deriveOpenIntervalInjective
    deriveFingerprintIntegralRepresentation deriveFingerprintInjective
    deriveHankelFactorization deriveHankelRankCertificate
    deriveIntervalFingerprintKernelEquivalence

end Omega.TypedAddressBiaxialCompletion
