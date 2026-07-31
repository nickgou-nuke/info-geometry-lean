import Mathlib.Tactic
import Omega.POM.ResonanceHankelNullIntegralPrincipalization

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-resonance-gcd-recovers-minpoly`. -/
theorem paper_pom_resonance_gcd_recovers_minpoly
    {n : ℕ} (kernelEqualsMultiplesData : HankelSyndromeKernelEqualsMultiplesData)
    (nullModeKernel squareKernel multipleModule : Set (Fin n → ℤ))
    (nullMode_eq_squareKernel : nullModeKernel = squareKernel)
    (squareKernel_subset_multipleModule :
      kernelEqualsMultiplesData.kernelContainedInMultiples → squareKernel ⊆ multipleModule)
    (multipleModule_subset_squareKernel :
      kernelEqualsMultiplesData.multiplesContainedInKernel → multipleModule ⊆ squareKernel)
    (basisRank : ℕ) (basisVector : Fin basisRank → Fin n → ℤ)
    (annihilator : Fin basisRank → Polynomial ℤ)
    (minpoly commonDivisor : Polynomial ℤ)
    (bezoutCoeff : Fin basisRank → Polynomial ℤ)
    (basisVector_mem : ∀ j, basisVector j ∈ nullModeKernel)
    (basis_annihilator_of_multiple :
      ∀ j, basisVector j ∈ multipleModule → minpoly ∣ annihilator j)
    (commonDivisor_dvd_annihilator : ∀ j, commonDivisor ∣ annihilator j)
    (commonDivisor_greatest :
      ∀ C : Polynomial ℤ, (∀ j, C ∣ annihilator j) → C ∣ commonDivisor)
    (bezout_minpoly : (∑ j : Fin basisRank, bezoutCoeff j * annihilator j) = minpoly)
    (commonDivisor_eq_sign :
      minpoly ∣ commonDivisor → commonDivisor ∣ minpoly →
        commonDivisor = minpoly ∨ commonDivisor = -minpoly) :
    commonDivisor = minpoly ∨ commonDivisor = -minpoly := by
  have hPrincipal : nullModeKernel = multipleModule :=
    paper_pom_resonance_hankel_null_integral_principalization
      kernelEqualsMultiplesData nullModeKernel squareKernel multipleModule
      nullMode_eq_squareKernel squareKernel_subset_multipleModule
      multipleModule_subset_squareKernel
  have hMinpolyDvdAnnihilator : ∀ j, minpoly ∣ annihilator j := by
    intro j
    have hMultiple : basisVector j ∈ multipleModule := by
      simpa [hPrincipal] using basisVector_mem j
    exact basis_annihilator_of_multiple j hMultiple
  have hMinpolyDvdCommon : minpoly ∣ commonDivisor :=
    commonDivisor_greatest minpoly hMinpolyDvdAnnihilator
  have hCommonDvdMinpoly : commonDivisor ∣ minpoly := by
    rw [← bezout_minpoly]
    exact Finset.dvd_sum fun j _ =>
      dvd_mul_of_dvd_right (commonDivisor_dvd_annihilator j) (bezoutCoeff j)
  exact commonDivisor_eq_sign hMinpolyDvdCommon hCommonDvdMinpoly

end Omega.POM
