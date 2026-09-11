import InfoGeometry.Quantum.PenroseOnsagerYangOccupationSpectrum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.PenroseOnsagerYangOrderParameter
import InfoGeometry.Quantum.PenroseOnsagerYangTwoModeCoherence

/-!
# Penrose--Onsager--Yang finite condensation chain

This capstone packages only the intrinsic finite mathematics:

* macroscopic occupation is linear-scale spectral occupation;
* simple and fragmented condensation are distinct predicates;
* `sqrt(N0) chi` has squared norm and rank-one-kernel trace `N0`;
* a global scalar phase disappears from the rank-one kernel;
* coherent and diagonal two-mode kernels can have identical diagonal
  occupations while differing in off-diagonal coherence.

It does not identify these facts with spontaneous `U(1)` breaking, a BdG
Hamiltonian, Majorana modes, an ODLRO spatial limit, or a transport law.
-/

noncomputable section

namespace InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain

open scoped BigOperators ComplexOrder
open InfoGeometry.Quantum.PenroseOnsagerYang

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Exact classification statement: a simply condensed occupation family is
not fragmented. -/
theorem pristine_simple_fragmented_separation
    {F : OccupationFamily κ}
    (hF : IsSimpleCondensate F) :
    ¬ IsFragmentedCondensate F :=
  simple_not_fragmented hF

/-- Exact finite order-parameter statement. -/
theorem pristine_orderParameter_kernel
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ)
    {u : ℂ} (hu : u * starRingEnd ℂ u = 1) :
    (rankOneKernel χ).PosSemidef ∧
      (rankOneKernel χ).IsHermitian ∧
      modeNormSq (orderParameter N0 χ) = N0 ∧
      Matrix.trace (rankOneKernel (orderParameter N0 χ)) = (N0 : ℂ) ∧
      rankOneKernel (scalarAction u χ) = rankOneKernel χ :=
  condensate_kernel_packet hN0 hχ hu

/-- Exact finite spectral-kernel statement. -/
theorem pristine_spectralKernel
    (occupation : κ → ℝ)
    (hoccupation : ∀ k, 0 ≤ occupation k)
    (mode : κ → Mode ι)
    (hmode : ∀ k, IsNormalizedMode (mode k)) :
    (spectralKernel occupation mode).PosSemidef ∧
      Matrix.trace (spectralKernel occupation mode) =
        ∑ k, (occupation k : ℂ) := by
  exact ⟨spectralKernel_posSemidef occupation mode,
    trace_spectralKernel occupation hoccupation mode hmode⟩

/-- Exact finite coherent/diagonal two-mode separation. -/
theorem pristine_twoMode_coherence
    {a b : ℂ} (hab : a * starRingEnd ℂ b ≠ 0) :
    Matrix.det (coherentTwoModeKernel a b) = 0 ∧
      (coherentTwoModeKernel a b).PosSemidef ∧
      (incoherentKernelOfAmplitudes a b).PosSemidef ∧
      coherentTwoModeKernel a b 0 0 =
        incoherentKernelOfAmplitudes a b 0 0 ∧
      coherentTwoModeKernel a b 1 1 =
        incoherentKernelOfAmplitudes a b 1 1 ∧
      coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b :=
  twoMode_coherence_packet hab

/-- Combined theorem-safe Penrose--Onsager--Yang packet. -/
theorem penrose_onsager_yang_condensation_pristine_chain
    {F : OccupationFamily κ}
    (hF : IsSimpleCondensate F)
    (occupation : κ → ℝ)
    (hoccupation : ∀ k, 0 ≤ occupation k)
    (mode : κ → Mode ι)
    (hmode : ∀ k, IsNormalizedMode (mode k))
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ)
    {u : ℂ} (hu : u * starRingEnd ℂ u = 1)
    {a b : ℂ} (hab : a * starRingEnd ℂ b ≠ 0) :
    (¬ IsFragmentedCondensate F) ∧
      (spectralKernel occupation mode).PosSemidef ∧
      Matrix.trace (spectralKernel occupation mode) =
        ∑ k, (occupation k : ℂ) ∧
      modeNormSq (orderParameter N0 χ) = N0 ∧
      Matrix.trace (rankOneKernel (orderParameter N0 χ)) = (N0 : ℂ) ∧
      rankOneKernel (scalarAction u χ) = rankOneKernel χ ∧
      (incoherentKernelOfAmplitudes a b).PosSemidef ∧
      coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b := by
  exact ⟨simple_not_fragmented hF,
    spectralKernel_posSemidef occupation mode,
    trace_spectralKernel occupation hoccupation mode hmode,
    modeNormSq_orderParameter hN0 hχ,
    trace_orderParameterKernel hN0 hχ,
    rankOneKernel_globalPhase_invariant hu χ,
    incoherentKernelOfAmplitudes_posSemidef a b,
    coherent_ne_incoherent_of_cross_ne_zero hab⟩

end InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain
