import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Meta.Architecture
import InfoGeometry.Thermodynamics.SouriauTemperature

/-!
# InfoGeometry.Arithmetic.PrimeInformationKMS

Finite information/KMS normalization layer for the prime thermodynamic lane.

This module keeps three calibrations separate and proof-backed:

* prime Boltzmann weights `w_p(β) = exp(-β log p)` and finite normalization;
* bosonic zeta gas versus fermionic square-free/Möbius gas;
* Massieu/Bregman and KMS strip readouts from the already-owned bridge layers.

The probability layer is finite and normalized by an explicit partition
function.  `log p` is treated as energy / log-volume / unnormalized surprisal
until that normalization is performed.

No infinite Euler product, analytic continuation, Lee--Yang theorem, or RH
claim is made in this file.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeInformationKMS

open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge
open InfoGeometry.Arithmetic.PrimeSuperalgebra
open InfoGeometry.LogPotential.LegendreModel
open InfoGeometry.Thermodynamics

/-! ## 1. Finite information normalization -/


/-- Prime Boltzmann weight `w_p(β) = exp(-β log p)`. -/
@[rep_depth thermo]
def boltzmannWeight (beta : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-beta * Real.log p)

/-- Finite prime information partition function. -/
@[rep_depth thermo]
def partition (modes : Finset ℕ) (beta : ℝ) : ℝ :=
  Finset.sum modes (fun p => boltzmannWeight beta p)

/-- The partition is positive on a nonempty finite prime cutoff. -/
@[rep_depth thermo]
theorem partition_pos (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    0 < partition modes beta := by
  unfold partition boltzmannWeight
  exact Finset.sum_pos
    (by
      intro p hp
      exact Real.exp_pos _)
    h_nonempty

/-- Normalized prime probability on the finite cutoff. -/
@[rep_depth thermo]
def normalizedProbability (modes : Finset ℕ) (beta : ℝ) (p : ℕ) : ℝ :=
  boltzmannWeight beta p / partition modes beta

/-- Information surprisal after finite normalization. -/
@[rep_depth thermo]
def informationSurprisal (modes : Finset ℕ) (beta : ℝ) (p : ℕ) : ℝ :=
  -Real.log (normalizedProbability modes beta p)

/-- The normalized finite probabilities sum to one. -/
@[rep_depth thermo]
theorem normalizedProbability_sum_eq_one (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    Finset.sum modes (fun p => normalizedProbability modes beta p) = 1 := by
  unfold normalizedProbability partition boltzmannWeight
  rw [← Finset.sum_div]
  exact div_self (partition_pos modes beta h_nonempty).ne'

/-- The normalized prime log-energy is the finite weighted-energy quotient. -/
@[rep_depth thermo]
theorem normalizedProbability_logEnergy_eq_weighted_quotient
    (modes : Finset ℕ) (beta : ℝ) :
    Finset.sum modes (fun p =>
      normalizedProbability modes beta p * Real.log p) =
      (Finset.sum modes (fun p => boltzmannWeight beta p * Real.log p)) /
        partition modes beta := by
  unfold normalizedProbability
  calc
    (∑ p ∈ modes, (boltzmannWeight beta p / partition modes beta) * Real.log p) =
        ∑ p ∈ modes, (boltzmannWeight beta p * Real.log p) /
          partition modes beta := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (∑ p ∈ modes, boltzmannWeight beta p * Real.log p) /
          partition modes beta := by
      rw [Finset.sum_div]

/-- The normalized finite mean of the prime log-energy. -/
@[rep_depth thermo]
def normalizedLogEnergyMean (modes : Finset ℕ) (beta : ℝ) : ℝ :=
  ∑ p ∈ modes, normalizedProbability modes beta p * Real.log p

/-- The normalized finite variance of the prime log-energy. -/
@[rep_depth thermo]
def normalizedLogEnergyVariance (modes : Finset ℕ) (beta : ℝ) : ℝ :=
  ∑ p ∈ modes,
    normalizedProbability modes beta p *
      (Real.log p - normalizedLogEnergyMean modes beta) ^ 2

/-- The normalized finite logarithmic score has zero expectation. -/
@[rep_depth thermo]
theorem normalizedLogEnergyScore_mean_zero
    (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    ∑ p ∈ modes,
      normalizedProbability modes beta p *
        (-(Real.log p - normalizedLogEnergyMean modes beta)) = 0 := by
  let μ := normalizedLogEnergyMean modes beta
  have hnorm :
      ∑ p ∈ modes, normalizedProbability modes beta p = 1 :=
    normalizedProbability_sum_eq_one modes beta h_nonempty
  have hcenter :
      ∑ p ∈ modes,
        normalizedProbability modes beta p * (Real.log p - μ) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    dsimp [μ, normalizedLogEnergyMean]
    rw [hnorm]
    ring
  calc
    (∑ p ∈ modes,
        normalizedProbability modes beta p *
          (-(Real.log p - μ))) =
        -(∑ p ∈ modes,
          normalizedProbability modes beta p * (Real.log p - μ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = 0 := by rw [hcenter]; ring

/-- Normalized finite probabilities are nonnegative on the active cutoff. -/
@[rep_depth thermo]
theorem normalizedProbability_nonneg
    (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty)
    (p : ℕ) (hp : p ∈ modes) :
    0 ≤ normalizedProbability modes beta p := by
  unfold normalizedProbability boltzmannWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (le_of_lt (partition_pos modes beta h_nonempty))

/-- The finite Fisher score-square readout is nonnegative. -/
@[rep_depth thermo]
theorem normalizedLogEnergyScoreSquare_nonneg
    (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    0 ≤ ∑ p ∈ modes,
      normalizedProbability modes beta p *
        (-(Real.log p - normalizedLogEnergyMean modes beta)) ^ 2 := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg
    (normalizedProbability_nonneg modes beta h_nonempty p hp)
    (sq_nonneg _)

/-- The finite score-square readout is exactly the normalized log-energy
    variance. -/
@[rep_depth thermo]
theorem normalizedLogEnergyScoreSquare_eq_variance
    (modes : Finset ℕ) (beta : ℝ) :
    (∑ p ∈ modes,
      normalizedProbability modes beta p *
        (-(Real.log p - normalizedLogEnergyMean modes beta)) ^ 2) =
      normalizedLogEnergyVariance modes beta := by
  unfold normalizedLogEnergyVariance
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_sq]

/-- The normalized finite log-energy variance is nonnegative. -/
@[rep_depth thermo]
theorem normalizedLogEnergyVariance_nonneg
    (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty) :
    0 ≤ normalizedLogEnergyVariance modes beta := by
  rw [← normalizedLogEnergyScoreSquare_eq_variance]
  exact normalizedLogEnergyScoreSquare_nonneg modes beta h_nonempty

/--
Normalized surprisal is `β log p + log Z` on the finite cutoff.

This is the calibrated information-theoretic version of the unnormalized
energy `log p`.
-/
@[rep_depth thermo]
theorem informationSurprisal_eq_beta_log_add_logPartition
    (modes : Finset ℕ) (beta : ℝ) (h_nonempty : modes.Nonempty)
    (p : ℕ) :
    informationSurprisal modes beta p =
      beta * Real.log p + Real.log (partition modes beta) := by
  unfold informationSurprisal normalizedProbability partition boltzmannWeight
  have hnum : 0 < Real.exp (-beta * Real.log p) := Real.exp_pos _
  change -Real.log
      (Real.exp (-beta * Real.log p) /
        partition modes beta) =
    beta * Real.log p +
      Real.log (partition modes beta)
  rw [Real.log_div hnum.ne' (partition_pos modes beta h_nonempty).ne']
  rw [Real.log_exp]
  ring

/--
Boltzmann weight equals the `p^{-β}` real power on prime modes.
-/
@[rep_depth thermo]
theorem boltzmannWeight_eq_rpow
    (modes : Finset ℕ) (beta : ℝ) (h_prime : ∀ p ∈ modes, Nat.Prime p)
    (p : ℕ) (hp : p ∈ modes) :
    boltzmannWeight beta p = (p : ℝ) ^ (-beta) := by
  have hprime : Nat.Prime p := h_prime p hp
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast Nat.Prime.pos hprime
  unfold boltzmannWeight
  rw [Real.rpow_def_of_pos hp0]
  congr 1
  ring

/-! ## 2. Sector separation: bosonic zeta gas vs fermionic square-free gas -/

/-- Bosonic prime gas partition, in the analytic half-plane. -/
@[rep_depth thermo]
def bosonicZetaPartition (s : ℂ) : ℂ :=
  infiniteComplexBosonicEulerProduct s

/-- Fermionic square-free prime partition. -/
@[rep_depth thermo]
abbrev PrimeCutoff := PrimeSuperalgebra.PrimeCutoff

/-- Fermionic square-free prime partition. -/
@[rep_depth thermo]
def fermionicSquarefreePartition (P : PrimeCutoff) (β : ℝ) : ℝ :=
  finiteFermionicSquarefreePartition P β

/-- Möbius supertrace of the fermionic square-free sector. -/
@[rep_depth thermo]
def mobiusSupertrace (P : PrimeCutoff) (β : ℝ) : ℝ :=
  finitePrimeSupertrace P β

@[rep_depth thermo]
theorem bosonicZetaPartition_eq_riemannZeta
    {s : ℂ}
    (hs : 1 < s.re) :
    bosonicZetaPartition s = riemannZeta s := by
  simpa [bosonicZetaPartition] using
    infiniteComplexBosonicEulerProduct_eq_riemannZeta (s := s) hs

@[rep_depth thermo]
theorem fermionicSquarefreePartition_eq_product
    (P : PrimeCutoff) (β : ℝ) :
    fermionicSquarefreePartition P β =
      Finset.prod P.primes (fun p => 1 + primeWeight β p) := by
  simpa [fermionicSquarefreePartition, primeWeight] using
    finiteFermionicSquarefreePartition_eq_product P β

@[rep_depth thermo]
theorem mobiusSupertrace_eq_denominator
    (P : PrimeCutoff) (β : ℝ) :
    mobiusSupertrace P β =
      Finset.prod P.primes (fun p => 1 - primeWeight β p) := by
  simpa [mobiusSupertrace, primeWeight, finitePrimeDenominator] using
    finitePrimeSupertrace_eq_denominator P β

@[rep_depth thermo]
theorem finiteFullSUSYProduct_eq_one
    (P : PrimeCutoff) (β : ℝ)
    (hdenom : finitePrimeDenominator P β ≠ 0) :
    finiteFullSUSYProduct P β = 1 := by
  exact PrimeSuperalgebra.finiteFullSUSYProduct_eq_one P β hdenom

/-- The named Möbius supertrace cancels the finite bosonic partition. -/
@[rep_depth thermo]
theorem mobiusSupertrace_mul_finiteBosonicPrimePartition_eq_one
    (P : PrimeCutoff) (β : ℝ)
    (hdenom : finitePrimeDenominator P β ≠ 0) :
    mobiusSupertrace P β * finiteBosonicPrimePartition P β = 1 := by
  simpa [mobiusSupertrace] using
    (PrimeSuperalgebra.finitePrimeSupertrace_mul_finiteBosonicPrimePartition_eq_one
      P β hdenom)

/-! ## 3. KMS normalization and Massieu/Bregman readouts -/

/-- The finite grand-canonical KMS strip is nonempty at positive inverse temperature. -/
@[rep_depth thermo]
theorem primeKMSAnalyticStrip_nonempty {β : ℝ} (hβ : 0 < β) :
    (Set.Ioo (0 : ℝ) β).Nonempty := by
  refine ⟨β / 2, ?_, ?_⟩ <;> linarith

/-- Grand-canonical KMS periodicity for a finite kernel. -/
@[rep_depth thermo]
theorem primeGrandKMS_periodicity_condition
    (β : ℝ) {ι : Type*} [DecidableEq ι]
    (energy mu : ι → ℝ)
    (K : Finset ι → Finset ι → ℝ)
    (S T : Finset ι) :
    Real.exp (-β * Finset.sum S (fun p => energy p - mu p)) * K S T =
      Real.exp (-β * Finset.sum T (fun p => energy p - mu p)) *
        (Real.exp (-β * (Finset.sum S (fun p => energy p - mu p) -
          Finset.sum T (fun p => energy p - mu p))) * K S T) := by
  have hExp :
      Real.exp (-β * Finset.sum S (fun p => energy p - mu p)) =
        Real.exp (-β * Finset.sum T (fun p => energy p - mu p)) *
          Real.exp (-β * (Finset.sum S (fun p => energy p - mu p) -
            Finset.sum T (fun p => energy p - mu p))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp]
  ring

/-- Souriau inverse temperature readout from the Massieu bridge. -/
@[rep_depth transport]
theorem beta_eq_realPart_of_massieuBridge
    (B : Bridge) :
    B.beta = B.temperature.s.re :=
  B.beta_eq_realPart_of_bridge

/-- The Massieu potential is already the finite grand-canonical potential. -/
@[rep_depth thermo]
theorem massieu_eq_potential_of_massieuBridge
    (B : Bridge) (θ : ℝ) :
    B.massieuModel.massieu θ =
      InfoGeometry.GrandCanonical.potentialGC
        (primeGrandCanonicalParams B.P B.energyWeight) θ B.chemicalPotential :=
  B.massieu_eq_potential θ

/-- The dual coordinate is the finite mean-shift readout. -/
@[rep_depth thermo]
theorem dualCoord_eq_meanShift_of_massieuBridge
    (B : Bridge) (θ : ℝ) :
    B.massieuModel.dualCoord θ =
      InfoGeometry.GrandCanonical.meanShift
        (primeGrandCanonicalParams B.P B.energyWeight) θ B.chemicalPotential :=
  B.dualCoord_eq_meanShift_of_bridge θ

/-- The temperature-regularized Hamiltonian defect is nonnegative. -/
@[rep_depth thermo]
theorem temperatureRegularizedHamiltonian_nonneg_of_massieuBridge
    (B : Bridge)
    (ε θ η : ℝ) (hε : 0 ≤ ε) :
    0 ≤ B.temperatureRegularizedHamiltonian ε θ η :=
  B.temperatureRegularizedHamiltonian_nonneg ε θ η hε

/-- The temperature-regularized Hamiltonian defect vanishes on contact. -/
@[rep_depth thermo]
theorem temperatureRegularizedHamiltonian_eq_zero_at_contact_of_massieuBridge
    (B : Bridge) (ε θ : ℝ) :
    B.temperatureRegularizedHamiltonian ε θ (B.massieuModel.dualCoord θ) = 0 :=
  B.temperatureRegularizedHamiltonian_eq_zero_at_contact ε θ

/-- The Fenchel gap is nonnegative. -/
@[rep_depth thermo]
theorem fenchelGap_nonneg_of_massieuBridge
    (B : Bridge) (θ η : ℝ) :
    0 ≤ B.massieuModel.fenchelGap θ η :=
  B.fenchelGap_nonneg θ η

/-- The Fenchel gap vanishes on contact. -/
@[rep_depth thermo]
theorem fenchelGap_eq_zero_at_contact_of_massieuBridge
    (B : Bridge) (θ : ℝ) :
    B.massieuModel.fenchelGap θ (B.massieuModel.dualCoord θ) = 0 :=
  B.fenchelGap_eq_zero_at_contact θ

/-- Canonical free energy expressed through the scaled entropy-energy contact form. -/
@[rep_depth thermo]
theorem canonicalFreeEnergy_eq_scaled_entropy_energy_of_massieuBridge
    (B : Bridge) (ε θ : ℝ) :
    B.massieuModel.canonicalFreeEnergy ε θ =
      -ε * (B.massieuModel.canonicalEntropy θ -
        θ * B.massieuModel.canonicalEnergy θ) :=
  B.massieuModel.canonicalFreeEnergy_eq_scaled_entropy_energy ε θ


end InfoGeometry.Arithmetic.PrimeInformationKMS
