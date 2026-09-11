import InfoGeometry.External.Auto.PrimonFockTraceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.PrimonSuperThermodynamics
import InfoGeometry.External.Auto.RiemannHypothesis
open RiemannHypothesis

/-!
# Primon Hamiltonian vs Hilbert--Pólya operator: theorem-honest separation

This file formalizes the distinction:

* the primon/Fock Hamiltonian has arithmetic energies `log n` and generates
  finite zeta/Dirichlet heat traces;
* a Hilbert--Pólya operator, if realized, is a separate spectral datum whose
  real spectrum parametrizes nontrivial zeros as `1/2 + iγ`;
* prime logarithms can feed an auxiliary potential/scattering model as
  coefficients, but this is not an identification of spectra;
* zeros of the bosonic zeta partition are reciprocal/graded-sector singularities.
-/

noncomputable section

namespace PrimonHilbertPolyaSeparation

open PrimonFockTraceBridge
open PrimonSuperThermo

/-- The primon energy of an integer mode `n` is `log n`. -/
def primonIntegerEnergy (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

/-- The primon arithmetic spectrum: logarithms of nonzero natural numbers. -/
def PrimonLogIntegerSpectrum : Set ℝ :=
  { E : ℝ | ∃ n : ℕ, n ≠ 0 ∧ E = primonIntegerEnergy n }

/-- Single-particle prime energies are the prime-log coefficients. -/
def PrimonPrimeSpectrum : Set ℝ :=
  { E : ℝ | ∃ p : ℕ, Nat.Prime p ∧ E = primonIntegerEnergy p }

/-- Prime-crystal potential coefficients: primes enter an auxiliary scattering
model as locations/weights `log p`, not as Riemann-zero eigenvalues. -/
def primeCrystalPotentialCoeff (p : ℕ) : ℝ :=
  Real.log (p : ℝ)

/-- The prime-crystal coefficient agrees with the primon prime-mode energy. -/
theorem primeCrystalPotentialCoeff_eq_primeEnergy (p : ℕ) :
    primeCrystalPotentialCoeff p = primeEnergy p := rfl

/-- Finite primon heat trace is exactly the finite zeta/Dirichlet partial sum.
This is the finite theorem kernel for `Tr(exp(-β H_primon)) = ζ(β)`. -/
theorem primon_heat_trace_is_zeta_partial (β : ℝ) (N : ℕ) :
    finitePrimonFockTrace β N = finiteZetaPartial β N :=
  finitePrimonFockTrace_eq_zeta_partial β N

/-- Hilbert--Pólya spectral datum is intentionally separate from the primon
log-integer spectrum: its real spectrum parametrizes zeros as `1/2+iγ`. -/
structure HilbertPolyaSpectralDatum (Z : ℂ → ℂ) where
  gammaSpectrum : Set ℝ
  zeros_as_critical_spectrum :
    { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ Z s = 0 } =
      { s : ℂ | ∃ γ : ℝ, γ ∈ gammaSpectrum ∧
        s = (1 / 2 : ℂ) + γ * Complex.I }

/-- The Hilbert--Pólya datum is exactly the existing RH schema. -/
def HilbertPolyaSpectralDatum.toHamiltonian
    {Z : ℂ → ℂ} (H : HilbertPolyaSpectralDatum Z) : hilbert_polya_hamiltonian Z :=
  ⟨H.gammaSpectrum, H.zeros_as_critical_spectrum⟩

/-- If the separate Hilbert--Pólya datum is realized, RH follows for `Z`. -/
theorem hilbert_polya_datum_implies_RH
    {Z : ℂ → ℂ} (H : HilbertPolyaSpectralDatum Z) : RHStatement Z :=
  hilbert_polya_hamiltonian_implies_RH H.toHamiltonian


/-- Reciprocal/graded ghost-sector singularities are exactly denominator zeros
in the formal zeta dictionary.  This is not an eigenvalue claim for the primon
Hamiltonian. -/
theorem reciprocal_ghost_singularity_iff_zero
    {Z : ℂ → ℂ} {s : ℂ} :
    rhGradedIndexSingularity Z s ↔ rhDenominatorZero Z s :=
  rh_graded_index_singularity_iff_denominator_zero

/-- A zero of the bosonic partition gives a reciprocal/graded-sector singularity
in the formal algebraic dictionary. -/
theorem zeta_zero_gives_reciprocal_ghost_singularity
    (Z : ℂ → ℂ) (s : ℂ) (hzero : rhDenominatorZero Z s) :
    rhGradedIndexSingularity Z s :=
  rh_zeta_zero_implies_graded_index_pole Z s hzero


/-- Capstone synthesis of the theorem-honest separation. -/
theorem primon_hilbert_polya_separation_synthesis
    (Z : ℂ → ℂ) (β : ℝ) (N : ℕ) (s : ℂ)
    (H : HilbertPolyaSpectralDatum Z)
    (hzero : rhDenominatorZero Z s) :
    finitePrimonFockTrace β N = finiteZetaPartial β N ∧
    (∀ p : ℕ, primeCrystalPotentialCoeff p = primeEnergy p) ∧
    RHStatement Z ∧
    (rhGradedIndexSingularity Z s ↔ rhDenominatorZero Z s) ∧
    rhGradedIndexSingularity Z s := by
  exact ⟨primon_heat_trace_is_zeta_partial β N,
    primeCrystalPotentialCoeff_eq_primeEnergy,
    hilbert_polya_datum_implies_RH H,
    reciprocal_ghost_singularity_iff_zero (Z := Z) (s := s),
    zeta_zero_gives_reciprocal_ghost_singularity Z s hzero⟩

end PrimonHilbertPolyaSeparation

end noncomputable section
