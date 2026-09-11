import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Core.Entropy
import InfoGeometry.Thermo.FromBregman
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FreeEntropyDiffusionBridge

Explicit free-entropy diffusion bridge on the canonical Souriau and current
owner surfaces.

This file does not introduce a heuristic diffusion model or a bundled socket.
It names the free-entropy potential explicitly as the Souriau Massieu
potential, reads its score derivatives from the owner theorems, and packages
the finite Fisher/Onsager packet together with the completed current H²
anomaly theorem from the constructive CAR-to-current layer.
-/

namespace InfoGeometry.Canonical.FreeEntropyDiffusionBridge

open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Thermo

variable {α : Type*} [Fintype α] [Nonempty α]
variable {A : Type*} [Ring A]
variable {Ω : Type*} [Fintype Ω]

/-- Free entropy potential on the finite Souriau slice. -/
noncomputable def freeEntropyPotential
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  souriauMassieuPotential M T

/-- Pointwise Souriau surprisal: the negative logarithm of the Gibbs-Souriau weight. -/
noncomputable def souriauSurprisal
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
  -Real.log (souriauGibbsWeight M T x)

/-- Souriau Boltzmann entropy readout written as the weighted sum of pointwise surprisal. -/
noncomputable def souriauBoltzmannEntropy
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  -∑ x, souriauGibbsWeight M T x * Real.log (souriauGibbsWeight M T x)

/-- Normalized boundary/core probability law induced by the Souriau Gibbs weight. -/
noncomputable def souriauBoundaryProbability
    (M : SouriauMomentMap α) (T : GeometricTemperature) : InfoGeometry.FinProb α := by
  classical
  have hnonneg : ∀ x : α, 0 ≤ souriauGibbsWeight M T x := by
    intro x
    exact souriauGibbsWeight_nonneg M T x
  have hsum : ∑ x, ENNReal.ofReal (souriauGibbsWeight M T x) = 1 := by
    calc
      ∑ x, ENNReal.ofReal (souriauGibbsWeight M T x)
          = ENNReal.ofReal (∑ x, souriauGibbsWeight M T x) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset α))
                (f := fun x => souriauGibbsWeight M T x) (by
                  intro x hx
                  exact hnonneg x)
      _ = ENNReal.ofReal 1 := by
            simp [souriauGibbsWeight_sum_one]
      _ = 1 := by simp
  exact InfoGeometry.FinProb.of_fintype
    (fun x => ENNReal.ofReal (souriauGibbsWeight M T x)) hsum

/-- The boundary/core probability law evaluates pointwise to the Souriau Gibbs weight. -/
@[simp] theorem souriauBoundaryProbability_apply
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    (souriauBoundaryProbability M T x).toReal = souriauGibbsWeight M T x := by
  have hnonneg : 0 ≤ souriauGibbsWeight M T x := souriauGibbsWeight_nonneg M T x
  simp [souriauBoundaryProbability, InfoGeometry.FinProb.of_fintype, PMF.ofFintype_apply,
    hnonneg]

/-- Boundary/core surprisal operator induced by the Souriau Gibbs law. -/
noncomputable def souriauBoundarySurprisal
    (M : SouriauMomentMap α) (T : GeometricTemperature) : α → ℝ :=
  InfoGeometry.surprisal (souriauBoundaryProbability M T)

/-- The boundary/core surprisal operator is the negative logarithm of the Gibbs weight. -/
theorem souriauBoundarySurprisal_eq_neg_log_gibbsWeight
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    souriauBoundarySurprisal M T x = -Real.log (souriauGibbsWeight M T x) := by
  simp [souriauBoundarySurprisal, InfoGeometry.surprisal, souriauBoundaryProbability_apply]

/-- Boundary/core Boltzmann entropy readout as the expectation of surprisal. -/
noncomputable def souriauBoundaryEntropy
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  InfoGeometry.entropy (souriauBoundaryProbability M T)

/-- The boundary/core entropy is the expectation of boundary surprisal. -/
theorem souriauBoundaryEntropy_eq_expectation_surprisal
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauBoundaryEntropy M T =
      InfoGeometry.expectation (souriauBoundaryProbability M T)
        (souriauBoundarySurprisal M T) := by
  rfl

/-- The boundary/core Boltzmann entropy is the weighted surprisal sum. -/
theorem souriauBoundaryEntropy_eq_weighted_surprisal_sum
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauBoundaryEntropy M T =
      -∑ x, souriauGibbsWeight M T x * Real.log (souriauGibbsWeight M T x) := by
  simp [souriauBoundaryEntropy, InfoGeometry.entropy, InfoGeometry.expectation,
    souriauBoundaryProbability_apply]

/-- Bregman/KL penalty on the finite Souriau slice. -/
noncomputable def souriauBregmanPenalty
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) : ℝ :=
  L.bregman θ' θ

/-- Souriau free-entropy functional: Massieu potential minus Bregman penalty. -/
noncomputable def souriauFreeEntropyFunctional
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) : ℝ :=
  freeEntropyPotential M T - souriauBregmanPenalty L θ θ'

/-- The free entropy potential is the logarithm of the Souriau partition. -/
theorem freeEntropyPotential_eq_log_partition
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    freeEntropyPotential M T = Real.log (souriauPartition M T) := by
  simpa [freeEntropyPotential] using souriauMassieuPotential_eq_log_partition M T

/-- The pointwise Souriau surprisal is the negative logarithm of the Gibbs weight. -/
theorem souriauSurprisal_eq_neg_log_gibbsWeight
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    souriauSurprisal M T x = -Real.log (souriauGibbsWeight M T x) := by
  rfl

/-- The Souriau Boltzmann entropy is the weighted surprisal sum by definition. -/
theorem souriauBoltzmannEntropy_eq_weighted_surprisal_sum
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauBoltzmannEntropy M T =
      -∑ x, souriauGibbsWeight M T x * Real.log (souriauGibbsWeight M T x) := by
  rfl

/-- The Bregman penalty is exactly the KL parameterized divergence. -/
theorem souriauBregmanPenalty_eq_KL_param
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauBregmanPenalty L θ θ' = InfoGeometry.ConvexDuality.KL_param L.f θ θ' := by
  simpa [souriauBregmanPenalty] using
    (InfoGeometry.Thermo.KL_param_eq_bregman_energy (L := L) θ θ').symm

/-- The Souriau free-entropy functional is Massieu minus KL/Bregman penalty. -/
theorem souriauFreeEntropyFunctional_eq_massieu_sub_KL
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauFreeEntropyFunctional M T L θ θ' =
      freeEntropyPotential M T - InfoGeometry.ConvexDuality.KL_param L.f θ θ' := by
  rw [souriauFreeEntropyFunctional, souriauBregmanPenalty_eq_KL_param]

/-- The Souriau free-entropy functional is Massieu minus Bregman penalty. -/
theorem souriauFreeEntropyFunctional_eq_massieu_sub_bregman
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauFreeEntropyFunctional M T L θ θ' =
      freeEntropyPotential M T - L.bregman θ' θ := by
  rfl

/-- The Bregman-induced free energy readout is the canonical free-energy divergence. -/
theorem souriauFreeEnergyFromBregman_eq_freeEnergyDivergence
    [Nonempty Ω]
    (L : InfoGeometry.Convex.LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ) :
    freeEnergyFromBregman (L := L) θ0 θ ε =
      freeEnergyDivergence (L := L) θ0 θ ε := by
  exact freeEnergyDivergence_eq_freeEnergyFromBregman (L := L) θ0 θ ε

/-- The Bregman free energy is the internal-energy minus scale-entropy readout. -/
theorem souriauBregmanFreeEnergy_eq_internal_sub_scale_entropy
    [Nonempty Ω]
    (L : InfoGeometry.Convex.LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) :
    freeEnergyFromBregman (L := L) θ0 θ ε
      =
    internalEnergy (energyFromBregman (L := L) θ0 θ) ε
      - ε * shannonEntropy (energyFromBregman (L := L) θ0 θ) ε := by
  exact freeEnergyFromBregman_eq_internal_sub_scale_entropy
    (L := L) θ0 θ ε hε

/-- The boundary/core free entropy is entropy minus Bregman penalty. -/
noncomputable def souriauBoundaryFreeEntropy
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) : ℝ :=
  souriauBoundaryEntropy M T - souriauBregmanPenalty L θ θ'

/-- The boundary/core free entropy is entropy minus Bregman penalty. -/
theorem souriauBoundaryFreeEntropy_eq_entropy_sub_bregman
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauBoundaryFreeEntropy M T L θ θ' =
      souriauBoundaryEntropy M T - L.bregman θ' θ := by
  simp [souriauBoundaryFreeEntropy, souriauBregmanPenalty]

/-- The boundary/core free entropy is entropy minus KL penalty. -/
theorem souriauBoundaryFreeEntropy_eq_entropy_sub_KL
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauBoundaryFreeEntropy M T L θ θ' =
      souriauBoundaryEntropy M T - InfoGeometry.ConvexDuality.KL_param L.f θ θ' := by
  rw [souriauBoundaryFreeEntropy_eq_entropy_sub_bregman]
  simpa using (souriauBregmanPenalty_eq_KL_param (L := L) θ θ')

/-- The Souriau free-entropy functional is log-partition minus KL/Bregman penalty. -/
theorem souriauFreeEntropyFunctional_eq_log_partition_sub_bregman
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauFreeEntropyFunctional M T L θ θ' =
      Real.log (souriauPartition M T) - L.bregman θ' θ := by
  simp [souriauFreeEntropyFunctional, freeEntropyPotential_eq_log_partition,
    souriauBregmanPenalty]

/-- The Souriau free-entropy functional is log-partition minus KL/Bregman penalty. -/
theorem souriauFreeEntropyFunctional_eq_log_partition_sub_KL
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (L : InfoGeometry.Convex.LegendrePotential) (θ θ' : ℝ) :
    souriauFreeEntropyFunctional M T L θ θ' =
      Real.log (souriauPartition M T) - InfoGeometry.ConvexDuality.KL_param L.f θ θ' := by
  rw [souriauFreeEntropyFunctional_eq_log_partition_sub_bregman]
  simpa using (souriauBregmanPenalty_eq_KL_param (L := L) θ θ')

/-- The `β` score of the free entropy potential is the shifted mean readout. -/
theorem freeEntropy_beta_score
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun β => freeEntropyPotential M { T with beta := β }) T.beta =
      -souriauMeanShift M T := by
  simpa [freeEntropyPotential] using souriau_beta_conjugate_shifted_readout M T

/-- The `μ` score of the free entropy potential is the number readout. -/
theorem freeEntropy_mu_score
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun μ => freeEntropyPotential M { T with mu := μ }) T.mu =
      T.beta * souriauMeanNumber M T := by
  simpa [freeEntropyPotential] using souriau_mu_conjugate_number_readout M T

/--
Finite free-entropy diffusion packet:
the Massieu score readouts and the finite Souriau-Fisher/Onsager response
matrix are exposed together with the nonnegative entropy-production gate.
-/
theorem freeEntropy_fisherOnsager_packet
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPSD : (souriauFisherResponseMatrix M T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    deriv (fun β => freeEntropyPotential M { T with beta := β }) T.beta =
        -souriauMeanShift M T
      ∧ deriv (fun μ => freeEntropyPotential M { T with mu := μ }) T.mu =
        T.beta * souriauMeanNumber M T
      ∧ (souriauFisherResponseMatrix M T).PositiveSemidefinite
      ∧ 0 ≤ (souriauFisherResponseMatrix M T).entropyProduction xβ xμ := by
  rcases gibbsSouriau_massieu_fisher_onsager_secondLaw_packet M T hPSD xβ xμ with
    ⟨hβ, hμ, _hββ, _hμμ, _hβμ, _hμβ, _hSym, hσ⟩
  exact ⟨by simpa [freeEntropyPotential] using hβ,
    by simpa [freeEntropyPotential] using hμ,
    hPSD,
    hσ⟩

/-- H² anomaly owner theorem: completed current law from raw CAR modes. -/
theorem h2_current_anomaly_from_rawCAR
    (C : RawCARModeAlgebra A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 :=
  RawCARModeAlgebra.normalOrderedCurrent_heisenberg_from_matrixUnit C m n

end InfoGeometry.Canonical.FreeEntropyDiffusionBridge
