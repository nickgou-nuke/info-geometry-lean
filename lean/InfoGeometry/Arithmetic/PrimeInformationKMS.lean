import Mathlib
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

namespace PrimeInformationKMS

open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge
open InfoGeometry.Arithmetic.PrimeSuperalgebra
open InfoGeometry.LogPotential.LegendreModel
open InfoGeometry.Thermodynamics

/-! ## 1. Finite information normalization -/

/--
Finite prime information calibration packet.

`modes` is a finite prime cutoff.  The packet keeps the inverse-temperature
coordinate `beta` and the Souriau coordinate `temperature.s` separate, with an
explicit proof that the real inverse temperature is the real part of the
complex Souriau coordinate.
-/
@[rep_depth thermo]
structure FinitePrimeInformationKMSPacket where
  modes : Finset ℕ
  prime_modes : ∀ p ∈ modes, Nat.Prime p
  modes_nonempty : modes.Nonempty
  beta : ℝ
  temperature : InfoGeometry.Thermodynamics.SouriauTemperature
  beta_eq_realPart_proof : beta = temperature.s.re

namespace FinitePrimeInformationKMSPacket

/-- Prime Boltzmann weight `w_p(β) = exp(-β log p)`. -/
@[rep_depth thermo]
def boltzmannWeight (β : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-β * Real.log p)

/-- Finite prime information partition function. -/
@[rep_depth thermo]
def partition (K : FinitePrimeInformationKMSPacket) : ℝ :=
  Finset.sum K.modes (fun p => boltzmannWeight K.beta p)

/-- The partition is positive on a nonempty finite prime cutoff. -/
@[rep_depth thermo]
theorem partition_pos (K : FinitePrimeInformationKMSPacket) :
    0 < partition K := by
  unfold partition boltzmannWeight
  exact Finset.sum_pos
    (by
      intro p hp
      exact Real.exp_pos _)
    K.modes_nonempty

/-- Normalized prime probability on the finite cutoff. -/
@[rep_depth thermo]
def normalizedProbability (K : FinitePrimeInformationKMSPacket) (p : ℕ) : ℝ :=
  boltzmannWeight K.beta p / partition K

/-- Information surprisal after finite normalization. -/
@[rep_depth thermo]
def informationSurprisal (K : FinitePrimeInformationKMSPacket) (p : ℕ) : ℝ :=
  -Real.log (normalizedProbability K p)

/-- The Souriau inverse-temperature readout is the real part of the complex coordinate. -/
@[rep_depth transport]
theorem beta_eq_realPart_of_packet (K : FinitePrimeInformationKMSPacket) :
    K.beta = K.temperature.s.re :=
  K.beta_eq_realPart_proof

/-- The normalized finite probabilities sum to one. -/
@[rep_depth thermo]
theorem normalizedProbability_sum_eq_one (K : FinitePrimeInformationKMSPacket) :
    Finset.sum K.modes (fun p => normalizedProbability K p) = 1 := by
  unfold normalizedProbability partition boltzmannWeight
  rw [← Finset.sum_div]
  exact div_self (partition_pos K).ne'

/--
Normalized surprisal is `β log p + log Z` on the finite cutoff.

This is the calibrated information-theoretic version of the unnormalized
energy `log p`.
-/
@[rep_depth thermo]
theorem informationSurprisal_eq_beta_log_add_logPartition
    (K : FinitePrimeInformationKMSPacket)
    (p : ℕ) :
    FinitePrimeInformationKMSPacket.informationSurprisal K p =
      K.beta * Real.log p + Real.log (FinitePrimeInformationKMSPacket.partition K) := by
  unfold FinitePrimeInformationKMSPacket.informationSurprisal
    FinitePrimeInformationKMSPacket.normalizedProbability
    FinitePrimeInformationKMSPacket.partition
    FinitePrimeInformationKMSPacket.boltzmannWeight
  have hnum : 0 < Real.exp (-K.beta * Real.log p) := Real.exp_pos _
  change -Real.log
      (Real.exp (-K.beta * Real.log p) /
        FinitePrimeInformationKMSPacket.partition K) =
    K.beta * Real.log p +
      Real.log (FinitePrimeInformationKMSPacket.partition K)
  rw [Real.log_div hnum.ne' (FinitePrimeInformationKMSPacket.partition_pos K).ne']
  rw [Real.log_exp]
  ring

/--
Boltzmann weight equals the `p^{-β}` real power on prime modes.
-/
@[rep_depth thermo]
theorem boltzmannWeight_eq_rpow
    (K : FinitePrimeInformationKMSPacket)
    (p : ℕ) (hp : p ∈ K.modes) :
    boltzmannWeight K.beta p = (p : ℝ) ^ (-K.beta) := by
  have hprime : Nat.Prime p := K.prime_modes p hp
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast Nat.Prime.pos hprime
  unfold boltzmannWeight
  rw [Real.rpow_def_of_pos hp0]
  congr 1
  ring

end FinitePrimeInformationKMSPacket

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
    B.massieuModel.massieu θ = B.packet.potential θ B.chemicalPotential :=
  B.massieu_eq_potential θ

/-- The dual coordinate is the finite mean-shift readout. -/
@[rep_depth thermo]
theorem dualCoord_eq_meanShift_of_massieuBridge
    (B : Bridge) (θ : ℝ) :
    B.massieuModel.dualCoord θ = B.packet.meanShift θ B.chemicalPotential :=
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


end PrimeInformationKMS
