import Mathlib
import InfoGeometry.Physics.BiWaveRamanujanBridge
import InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge
import InfoGeometry.Physics.Thermodynamics.ChiralGrandCanonicalFiniteKMS

/-!
# A conservative formal bridge for nuclear chiral and quasiparticle models

The cited work on nuclear chirality and chirality--parity violation motivates
discrete symmetry operators, quartet labels, and electromagnetic selection
rules.  This file formalizes the algebraic core only: commuting involutions,
the existing finite five-grade CAR--BdG--Soloviev carrier, and the existing
two-wave/KMS readouts.  Phenomenological Hamiltonians, experimental claims,
and a general theorem about nuclear ChP violation are intentionally not
introduced without their physical hypotheses.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearChiralMengBridge

open InfoGeometry.Physics.BiWaveRamanujan
open InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure
open InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
open InfoGeometry.Physics.NuclearBdGSolovievCompression
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge
open InfoGeometry.Physics.Thermodynamics

/-! ## ChP symmetry algebra -/

structure ChPInvolutions (A : Type*) [Ring A] where
  chirality : A
  parity : A
  chirality_sq : chirality * chirality = 1
  parity_sq : parity * parity = 1
  commute : chirality * parity = parity * chirality

namespace ChPInvolutions

variable {A : Type*} [Ring A] (S : ChPInvolutions A)

def chiplex : A := S.chirality * S.parity

theorem chiplex_sq : S.chiplex * S.chiplex = 1 := by
  unfold chiplex
  calc
    S.chirality * S.parity * (S.chirality * S.parity) =
        (S.chirality * S.chirality) * (S.parity * S.parity) := by
          calc
            S.chirality * S.parity * (S.chirality * S.parity) =
                S.chirality * (S.parity * S.chirality) * S.parity := by
                  noncomm_ring
            _ = S.chirality * (S.chirality * S.parity) * S.parity := by
                  rw [S.commute]
            _ = (S.chirality * S.chirality) * (S.parity * S.parity) := by
                  noncomm_ring
    _ = 1 := by rw [S.chirality_sq, S.parity_sq]; simp

theorem chiplex_commutes_with_chirality :
    S.chiplex * S.chirality = S.chirality * S.chiplex := by
  unfold chiplex
  calc
    S.chirality * S.parity * S.chirality =
        S.chirality * (S.parity * S.chirality) := by
          exact mul_assoc S.chirality S.parity S.chirality
    _ = S.chirality * (S.chirality * S.parity) := by
          exact congrArg (fun z => S.chirality * z) S.commute.symm

theorem chiplex_commutes_with_parity :
    S.chiplex * S.parity = S.parity * S.chiplex := by
  unfold chiplex
  calc
    S.chirality * S.parity * S.parity =
        (S.chirality * S.parity) * S.parity := by rfl
    _ = (S.parity * S.chirality) * S.parity := by
          exact congrArg (fun z => z * S.parity) S.commute
    _ = S.parity * (S.chirality * S.parity) := by
          exact mul_assoc S.parity S.chirality S.parity

theorem conjugation_by_chiplex_involutive (x : A) :
    S.chiplex * (S.chiplex * x * S.chiplex) * S.chiplex = x := by
  calc
    S.chiplex * (S.chiplex * x * S.chiplex) * S.chiplex =
        (S.chiplex * S.chiplex) * x * (S.chiplex * S.chiplex) := by
          noncomm_ring
    _ = x := by rw [S.chiplex_sq]; simp

end ChPInvolutions

/-! ## Causal architecture -/

inductive Archetype
  | chpInvolutions
  | fiveGradeCarrier
  | quasiparticlePhonon
  | solovievCompression
  | twinWaveKMS
  | operatorZornReadout
  deriving DecidableEq, Fintype, Repr

def causalRank : Archetype → ℕ
  | .chpInvolutions => 0
  | .fiveGradeCarrier => 1
  | .quasiparticlePhonon => 2
  | .solovievCompression => 3
  | .twinWaveKMS => 4
  | .operatorZornReadout => 5

instance : LE Archetype where
  le a b := causalRank a ≤ causalRank b

theorem causal_refl (a : Archetype) : a ≤ a := by
  change causalRank a ≤ causalRank a
  exact Nat.le_refl _

theorem causal_trans (a b c : Archetype) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  change causalRank a ≤ causalRank b at hab
  change causalRank b ≤ causalRank c at hbc
  change causalRank a ≤ causalRank c
  exact Nat.le_trans hab hbc

theorem causal_antisymm (a b : Archetype) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  change causalRank a ≤ causalRank b at hab
  change causalRank b ≤ causalRank a at hba
  cases a <;> cases b <;> simp only [causalRank] at hab hba ⊢ <;> omega

instance : PartialOrder Archetype where
  le_refl := causal_refl
  le_trans := causal_trans
  le_antisymm := causal_antisymm

theorem causal_chain :
    Archetype.chpInvolutions ≤ Archetype.fiveGradeCarrier ∧
    Archetype.fiveGradeCarrier ≤ Archetype.quasiparticlePhonon ∧
    Archetype.quasiparticlePhonon ≤ Archetype.solovievCompression ∧
    Archetype.solovievCompression ≤ Archetype.twinWaveKMS ∧
    Archetype.twinWaveKMS ≤ Archetype.operatorZornReadout := by
  constructor
  · change causalRank Archetype.chpInvolutions ≤ causalRank Archetype.fiveGradeCarrier
    norm_num [causalRank]
  constructor
  · change causalRank Archetype.fiveGradeCarrier ≤ causalRank Archetype.quasiparticlePhonon
    norm_num [causalRank]
  constructor
  · change causalRank Archetype.quasiparticlePhonon ≤ causalRank Archetype.solovievCompression
    norm_num [causalRank]
  constructor
  · change causalRank Archetype.solovievCompression ≤ causalRank Archetype.twinWaveKMS
    norm_num [causalRank]
  · change causalRank Archetype.twinWaveKMS ≤ causalRank Archetype.operatorZornReadout
    norm_num [causalRank]

/-! ## Source-grounded exact packets -/

theorem five_grade_soloviev_packet (Eqp ω V ξ Δ : ℂ) :
    (∀ g : Generator,
      InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.HasGrade (degree g) (represent g)) ∧
    bdgBlock ξ Δ * bdgBlock ξ Δ =
      (ξ ^ 2 + Δ ^ 2) • (1 : Mat2) ∧
    solovievBlock Eqp ω V =
      (Eqp + ω / 2) • (1 : Mat2) + bdgBlock (ω / 2) V := by
  exact ⟨represent_hasGrade, bdgBlock_sq ξ Δ,
    solovievBlock_eq_center_add_bdg Eqp ω V⟩

theorem twin_wave_and_thermal_packet (μ t : ℝ) (X Y : BdGBlock ℝ) :
    (∀ σ : ℝ,
      Complex.normSq (psiFwd ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.normSq (psiBwd ((σ : ℂ) + (t : ℂ) * Complex.I)) ↔ σ = 1 / 2) ∧
    ‖boundaryIntertwiner t‖ = 1 ∧
    boundaryIntertwiner t * boundaryIntertwiner (-t) = 1 ∧
    chiralGibbsState μ (X * chiralSimilarityFlow μ Y) =
      chiralGibbsState μ (Y * X) := by
  exact ⟨fun σ => biwave_modular_balance σ t,
    boundaryIntertwiner_unitary t,
    boundaryIntertwiner_inversion t,
    chiralGibbsState_kms μ X Y⟩

theorem aharonov_readout_packet (overlap : ℂ) (h : overlap ≠ 0) :
    kreinSwapMatrix * kreinSwapMatrix = 1 ∧
    weakValue overlap overlap = 1 ∧
    weakValue overlap 0 = 0 := by
  exact ⟨kreinSwapMatrix_sq,
    weakValue_forward_projector overlap h,
    weakValue_backward_projector overlap⟩

theorem operator_zorn_super_soloviev_packet {A : Type*} [Ring A] [StarRing A]
    (Delta : A) :
    (operatorZornParity (A := A)).IsOdd
      (InfoGeometry.Physics.NCG.diracOperator Delta) ∧
    (operatorZornParity (A := A)).IsEven
      (InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta) ∧
    totalParity (operatorZornParity (A := A)) *
        diracSuperHamiltonian Delta *
        totalParity (operatorZornParity (A := A)) =
      diracSuperHamiltonian Delta := by
  exact ⟨dirac_internal_odd Delta,
    dirac_square_internal_even Delta,
    diracSuperHamiltonian_invariant Delta⟩

end InfoGeometry.Physics.NuclearChiralMengBridge
