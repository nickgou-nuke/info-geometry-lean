/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Physics.BiWaveRamanujanBridge
import InfoGeometry.Physics.NuclearFiveGradeBdGSolovievClosure
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge
import InfoGeometry.Physics.Thermodynamics.ChiralGrandCanonicalFiniteKMS
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.Physics.MengChPSelectionRules
import InfoGeometry.Nuclear.NuclearChiralPRMBridge
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization

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
  deriving DecidableEq, Repr

instance : Fintype Archetype :=
  Fintype.ofList
    [.chpInvolutions, .fiveGradeCarrier, .quasiparticlePhonon,
      .solovievCompression, .twinWaveKMS, .operatorZornReadout]
    (by intro x; cases x <;> simp)

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

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def nuclearChiralMengArchetypeOperator (P A C X : B) : Archetype → B
  | .chpInvolutions => invS P
  | .fiveGradeCarrier => evenGrade P X + oddGrade P X
  | .quasiparticlePhonon => conePlus P A
  | .solovievCompression => coneMinus P C
  | .twinWaveKMS => genPhi P A C
  | .operatorZornReadout => genV P A C

theorem nuclearChiralMengArchetype_operator_identities
    {P : B} (hP : P * P = P) (A C X : B) :
    nuclearChiralMengArchetypeOperator P A C X .chpInvolutions *
      nuclearChiralMengArchetypeOperator P A C X .chpInvolutions = (1 : B) ∧
    nuclearChiralMengArchetypeOperator P A C X .fiveGradeCarrier = X ∧
    nuclearChiralMengArchetypeOperator P A C X .quasiparticlePhonon *
      nuclearChiralMengArchetypeOperator P A C X .quasiparticlePhonon = 0 ∧
    nuclearChiralMengArchetypeOperator P A C X .solovievCompression *
      nuclearChiralMengArchetypeOperator P A C X .solovievCompression = 0 ∧
    nuclearChiralMengArchetypeOperator P A C X .twinWaveKMS *
      nuclearChiralMengArchetypeOperator P A C X .twinWaveKMS =
      nuclearChiralMengArchetypeOperator P A C X .operatorZornReadout := by
  dsimp only [nuclearChiralMengArchetypeOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

/-! ## Bridge to `MengChPSelectionRules` & concrete triaxial PRM ChP realization -/

namespace ChPInvolutions

/-- Generalized spectral invariance for any Hamiltonian commuting with both involutions in `ChPInvolutions`. -/
theorem chiplex_commutes_of_comm {A : Type*} [Ring A] (S : ChPInvolutions A) (H : A)
    (hCh : S.chirality * H = H * S.chirality) (hP : S.parity * H = H * S.parity) :
    S.chiplex * H = H * S.chiplex := by
  unfold ChPInvolutions.chiplex
  calc
    (S.chirality * S.parity) * H = S.chirality * (S.parity * H) := mul_assoc _ _ _
    _ = S.chirality * (H * S.parity) := by rw [hP]
    _ = (S.chirality * H) * S.parity := (mul_assoc _ _ _).symm
    _ = (H * S.chirality) * S.parity := by rw [hCh]
    _ = H * (S.chirality * S.parity) := mul_assoc _ _ _

/-- Construct a `ChPInvolutions` algebra directly from Meng's `chiture` and `parity` operators. -/
def ofMeng {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (rotation exchange intrinsicParity parity : Module.End ℂ Space)
    (hChiture : MengChPSelectionRules.chiture rotation exchange intrinsicParity *
      MengChPSelectionRules.chiture rotation exchange intrinsicParity = 1)
    (hParity : parity * parity = 1)
    (hComm : MengChPSelectionRules.chiture rotation exchange intrinsicParity * parity =
      parity * MengChPSelectionRules.chiture rotation exchange intrinsicParity) :
    ChPInvolutions (Module.End ℂ Space) where
  chirality := MengChPSelectionRules.chiture rotation exchange intrinsicParity
  parity := parity
  chirality_sq := hChiture
  parity_sq := hParity
  commute := hComm

theorem ofMeng_chiplex_eq {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (rotation exchange intrinsicParity parity : Module.End ℂ Space)
    (hChiture : MengChPSelectionRules.chiture rotation exchange intrinsicParity *
      MengChPSelectionRules.chiture rotation exchange intrinsicParity = 1)
    (hParity : parity * parity = 1)
    (hComm : MengChPSelectionRules.chiture rotation exchange intrinsicParity * parity =
      parity * MengChPSelectionRules.chiture rotation exchange intrinsicParity) :
    (ofMeng rotation exchange intrinsicParity parity hChiture hParity hComm).chiplex =
      MengChPSelectionRules.chiplex
        (MengChPSelectionRules.chiture rotation exchange intrinsicParity) parity := by
  unfold chiplex ofMeng MengChPSelectionRules.chiplex
  rfl

theorem same_chiplex_selection {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (m : MengChPSelectionRules.Multipole)
    (chitureOp parity transition : Module.End ℂ Space)
    (bra : Space →ₗ[ℂ] ℂ) (ket : Space) (value : ℂ) (value_ne : value ≠ 0)
    (hChitureSq : chitureOp * chitureOp = 1)
    (hParitySq : parity * parity = 1)
    (hComm : chitureOp * parity = parity * chitureOp)
    (ket_eigen : (⟨chitureOp, parity, hChitureSq, hParitySq, hComm⟩ :
      ChPInvolutions (Module.End ℂ Space)).chiplex ket = value • ket)
    (bra_eigen : ∀ s, bra ((⟨chitureOp, parity, hChitureSq, hParitySq, hComm⟩ :
      ChPInvolutions (Module.End ℂ Space)).chiplex s) = value * bra s)
    (hCovCh : chitureOp * transition =
      MengChPSelectionRules.chitureCharacter m • (transition * chitureOp))
    (hCovP : parity * transition =
      MengChPSelectionRules.parityCharacter m • (transition * parity)) :
    bra (transition ket) = 0 := by
  let S : ChPInvolutions (Module.End ℂ Space) :=
    ⟨chitureOp, parity, hChitureSq, hParitySq, hComm⟩
  have hket : MengChPSelectionRules.chiplex chitureOp parity ket = value • ket := by
    have hs := ket_eigen
    change S.chiplex ket = value • ket at hs
    simpa [S, ChPInvolutions.chiplex, MengChPSelectionRules.chiplex] using hs
  have hbra : ∀ s, bra (MengChPSelectionRules.chiplex chitureOp parity s) = value * bra s := by
    intro s
    have hs := bra_eigen s
    change bra (S.chiplex s) = value * bra s at hs
    simpa [S, ChPInvolutions.chiplex, MengChPSelectionRules.chiplex] using hs
  exact MengChPSelectionRules.same_chiplex_transition_vanishes
    m chitureOp parity transition bra ket value value_ne hket hbra hCovCh hCovP

end ChPInvolutions

section TriaxialChPRealization

open InfoGeometry.Nuclear

/-- Concrete 4D chiral-doublet × intrinsic-parity carrier `(c, p) ∈ Fin 2 × Fin 2`:
`c` indexes left/right triaxial orientation `{|L⟩, |R⟩}`, `p` indexes intrinsic parity `{|+⟩, |-⟩}`. -/
abbrev ChiralParitySpace := Fin 2 × Fin 2 → ℂ

/-- Triaxial `π`-rotation operator combining chiral orientation flip and intrinsic parity rotation sign. -/
def triaxialRotationOp : Module.End ℂ ChiralParitySpace where
  toFun ψ := fun cp => (if cp.2 = 0 then (1 : ℂ) else -1) * ψ (Equiv.swap 0 1 cp.1, cp.2)
  map_add' ψ φ := by ext ⟨c, p⟩; fin_cases p <;> (simp; try abel)
  map_smul' a ψ := by ext ⟨c, p⟩; fin_cases p <;> simp

/-- Exchange symmetry operator on the triaxial chiral-doublet carrier. -/
def triaxialExchangeOp : Module.End ℂ ChiralParitySpace := 1

/-- Intrinsic spatial parity operator `P` acting on the second index `p : Fin 2`. -/
def triaxialIntrinsicParityOp : Module.End ℂ ChiralParitySpace where
  toFun ψ := fun cp => (if cp.2 = 0 then (1 : ℂ) else -1) * ψ cp
  map_add' ψ φ := by ext ⟨c, p⟩; fin_cases p <;> (simp; try abel)
  map_smul' a ψ := by ext ⟨c, p⟩; fin_cases p <;> simp

/-- Meng chiture operator `A = R * X * P_int` on `ChiralParitySpace`. -/
def triaxialChitureOp : Module.End ℂ ChiralParitySpace :=
  MengChPSelectionRules.chiture triaxialRotationOp triaxialExchangeOp triaxialIntrinsicParityOp

/-- Meng spatial parity operator on `ChiralParitySpace`. -/
def triaxialParityOp : Module.End ℂ ChiralParitySpace := triaxialIntrinsicParityOp

/-- Meng chiplex operator `B = A * P` on `ChiralParitySpace`. -/
def triaxialChiplexOp : Module.End ℂ ChiralParitySpace :=
  MengChPSelectionRules.chiplex triaxialChitureOp triaxialParityOp

@[simp] theorem triaxialChitureOp_apply (ψ : ChiralParitySpace) (c p : Fin 2) :
    triaxialChitureOp ψ (c, p) = ψ (Equiv.swap 0 1 c, p) := by
  simp only [triaxialChitureOp, MengChPSelectionRules.chiture, triaxialExchangeOp, mul_one,
    Module.End.mul_apply, triaxialRotationOp, triaxialIntrinsicParityOp, LinearMap.coe_mk,
    AddHom.coe_mk]
  fin_cases p <;> simp

@[simp] theorem triaxialParityOp_apply (ψ : ChiralParitySpace) (c p : Fin 2) :
    triaxialParityOp ψ (c, p) = (if p = 0 then (1 : ℂ) else -1) * ψ (c, p) := rfl

@[simp] theorem triaxialChiplexOp_apply (ψ : ChiralParitySpace) (c p : Fin 2) :
    triaxialChiplexOp ψ (c, p) = (if p = 0 then (1 : ℂ) else -1) * ψ (Equiv.swap 0 1 c, p) := by
  simp [triaxialChiplexOp, MengChPSelectionRules.chiplex, Module.End.mul_apply]

theorem triaxialChitureOp_sq : triaxialChitureOp * triaxialChitureOp = 1 := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  fin_cases c <;> simp [Module.End.mul_apply]

theorem triaxialParityOp_sq : triaxialParityOp * triaxialParityOp = 1 := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  fin_cases p <;> simp [Module.End.mul_apply]

theorem triaxialChitureOp_comm_parity :
    triaxialChitureOp * triaxialParityOp = triaxialParityOp * triaxialChitureOp := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;> simp [Module.End.mul_apply]

/-- Concrete `ChPInvolutions` instance realizing `MengChPSelectionRules` on `ChiralParitySpace`. -/
def triaxialChPInvolutions : ChPInvolutions (Module.End ℂ ChiralParitySpace) :=
  ChPInvolutions.ofMeng triaxialRotationOp triaxialExchangeOp triaxialIntrinsicParityOp
    triaxialParityOp
    (by simpa [triaxialChitureOp] using triaxialChitureOp_sq)
    triaxialParityOp_sq
    (by simpa [triaxialChitureOp] using triaxialChitureOp_comm_parity)

theorem triaxialChPInvolutions_chiplex_eq :
    triaxialChPInvolutions.chiplex = triaxialChiplexOp := by
  unfold triaxialChPInvolutions triaxialChiplexOp triaxialChitureOp
  exact ChPInvolutions.ofMeng_chiplex_eq triaxialRotationOp triaxialExchangeOp
    triaxialIntrinsicParityOp triaxialParityOp
    (by simpa [triaxialChitureOp] using triaxialChitureOp_sq)
    triaxialParityOp_sq
    (by simpa [triaxialChitureOp] using triaxialChitureOp_comm_parity)

/-- Lift `ChiralPRM.prmMatrix` onto `ChiralParitySpace`. -/
def prmHamiltonianOp (state : ChiralPRM.ChiralDoubletState) :
    Module.End ℂ ChiralParitySpace where
  toFun ψ := fun cp =>
    (ChiralPRM.prmMatrix state cp.1 0 : ℂ) * ψ (0, cp.2) +
    (ChiralPRM.prmMatrix state cp.1 1 : ℂ) * ψ (1, cp.2)
  map_add' ψ φ := by ext ⟨c, p⟩; simp; ring
  map_smul' a ψ := by ext ⟨c, p⟩; simp; ring

theorem prmHamiltonianOp_comm_chiture (state : ChiralPRM.ChiralDoubletState) :
    triaxialChitureOp * prmHamiltonianOp state = prmHamiltonianOp state * triaxialChitureOp := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  fin_cases c <;>
    simp [Module.End.mul_apply, prmHamiltonianOp, ChiralPRM.prmMatrix, add_comm]

theorem prmHamiltonianOp_comm_parity (state : ChiralPRM.ChiralDoubletState) :
    triaxialParityOp * prmHamiltonianOp state = prmHamiltonianOp state * triaxialParityOp := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  fin_cases p <;> (simp [Module.End.mul_apply, prmHamiltonianOp]; try ring)

theorem prmHamiltonianOp_comm_chiplex (state : ChiralPRM.ChiralDoubletState) :
    triaxialChiplexOp * prmHamiltonianOp state = prmHamiltonianOp state * triaxialChiplexOp := by
  rw [← triaxialChPInvolutions_chiplex_eq]
  exact ChPInvolutions.chiplex_commutes_of_comm triaxialChPInvolutions (prmHamiltonianOp state)
    (by simpa [triaxialChPInvolutions, ChPInvolutions.ofMeng, triaxialChitureOp] using
      prmHamiltonianOp_comm_chiture state)
    (by simpa [triaxialChPInvolutions, ChPInvolutions.ofMeng] using
      prmHamiltonianOp_comm_parity state)

/-- Chiral-doublet simultaneous eigenstates indexed by chiture sign `χSign` and parity sign `πSign`. -/
def chiralBandKet (χSign πSign : Fin 2) : ChiralParitySpace :=
  fun cp => (if cp.2 = πSign then 1 else 0) * (if cp.1 = 0 then 1 else if χSign = 0 then 1 else -1)

/-- Dual eigenfunctional corresponding to `chiralBandKet χSign πSign`. -/
def chiralBandBra (χSign πSign : Fin 2) : ChiralParitySpace →ₗ[ℂ] ℂ where
  toFun ψ := ψ (0, πSign) + (if χSign = 0 then (1 : ℂ) else -1) * ψ (1, πSign)
  map_add' ψ φ := by fin_cases χSign <;> simp <;> ring
  map_smul' a ψ := by fin_cases χSign <;> simp <;> ring

theorem prmHamiltonianOp_eigen_plus (state : ChiralPRM.ChiralDoubletState) (πSign : Fin 2) :
    prmHamiltonianOp state (chiralBandKet 0 πSign) =
      (ChiralPRM.energyPlus state : ℂ) • chiralBandKet 0 πSign := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;> fin_cases πSign <;>
    (simp [prmHamiltonianOp, chiralBandKet, ChiralPRM.prmMatrix, ChiralPRM.energyPlus]; try ring)

theorem prmHamiltonianOp_eigen_minus (state : ChiralPRM.ChiralDoubletState) (πSign : Fin 2) :
    prmHamiltonianOp state (chiralBandKet 1 πSign) =
      (ChiralPRM.energyMinus state : ℂ) • chiralBandKet 1 πSign := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;> fin_cases πSign <;>
    (simp [prmHamiltonianOp, chiralBandKet, ChiralPRM.prmMatrix, ChiralPRM.energyMinus]; try ring)

theorem triaxialChitureOp_eigen (χSign πSign : Fin 2) :
    triaxialChitureOp (chiralBandKet χSign πSign) =
      (if χSign = 0 then (1 : ℂ) else -1) • chiralBandKet χSign πSign := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;> fin_cases χSign <;> fin_cases πSign <;>
    simp [chiralBandKet]

theorem triaxialParityOp_eigen (χSign πSign : Fin 2) :
    triaxialParityOp (chiralBandKet χSign πSign) =
      (if πSign = 0 then (1 : ℂ) else -1) • chiralBandKet χSign πSign := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;> fin_cases χSign <;> fin_cases πSign <;>
    simp [chiralBandKet]

theorem triaxialChiplexOp_eigen (χSign πSign : Fin 2) :
    triaxialChiplexOp (chiralBandKet χSign πSign) =
      ((if χSign = 0 then (1 : ℂ) else -1) * (if πSign = 0 then (1 : ℂ) else -1)) •
        chiralBandKet χSign πSign := by
  unfold triaxialChiplexOp
  exact MengChPSelectionRules.chiplex_eigenvector triaxialChitureOp triaxialParityOp
    (chiralBandKet χSign πSign) _ _
    (triaxialChitureOp_eigen χSign πSign) (triaxialParityOp_eigen χSign πSign)

theorem chiralBandBra_chiplex_eigen (χSign πSign : Fin 2) (ψ : ChiralParitySpace) :
    chiralBandBra χSign πSign (triaxialChiplexOp ψ) =
      ((if χSign = 0 then (1 : ℂ) else -1) * (if πSign = 0 then (1 : ℂ) else -1)) *
        chiralBandBra χSign πSign ψ := by
  fin_cases χSign <;> fin_cases πSign <;>
    (simp [chiralBandBra]; try ring)

/-- Concrete triaxial multipole transition operators for `E2`, `M1`, and `E3`. -/
def triaxialMultipoleOp : MengChPSelectionRules.Multipole → Module.End ℂ ChiralParitySpace
  | .electricTwo =>
      { toFun := fun ψ cp => (if cp.1 = 0 then (1 : ℂ) else -1) * ψ cp
        map_add' := fun ψ φ => by ext ⟨c, p⟩; fin_cases c <;> (simp; try abel)
        map_smul' := fun a ψ => by ext ⟨c, p⟩; fin_cases c <;> simp }
  | .magneticOne =>
      { toFun := fun ψ cp =>
          (if cp.1 = 0 then (1 : ℂ) else -1) * (if cp.2 = 0 then (1 : ℂ) else -1) * ψ cp
        map_add' := fun ψ φ => by ext ⟨c, p⟩; fin_cases c <;> fin_cases p <;> (simp; try abel)
        map_smul' := fun a ψ => by ext ⟨c, p⟩; fin_cases c <;> fin_cases p <;> simp }
  | .electricThree =>
      { toFun := fun ψ cp => ψ (cp.1, Equiv.swap 0 1 cp.2)
        map_add' := fun ψ φ => by ext ⟨c, p⟩; simp
        map_smul' := fun a ψ => by ext ⟨c, p⟩; simp }

theorem triaxialMultipoleOp_chiture_cov (m : MengChPSelectionRules.Multipole) :
    triaxialChitureOp * triaxialMultipoleOp m =
      MengChPSelectionRules.chitureCharacter m • (triaxialMultipoleOp m * triaxialChitureOp) := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  cases m <;> fin_cases c <;> fin_cases p <;>
    simp [triaxialMultipoleOp, MengChPSelectionRules.chitureCharacter, Module.End.mul_apply]

theorem triaxialMultipoleOp_parity_cov (m : MengChPSelectionRules.Multipole) :
    triaxialParityOp * triaxialMultipoleOp m =
      MengChPSelectionRules.parityCharacter m • (triaxialMultipoleOp m * triaxialParityOp) := by
  apply LinearMap.ext; intro ψ; ext ⟨c, p⟩
  cases m <;> fin_cases c <;> fin_cases p <;>
    simp [triaxialMultipoleOp, MengChPSelectionRules.parityCharacter, Module.End.mul_apply]

/-- Non-commutativity witness on `ChiralParitySpace`. -/
theorem triaxialChitureOp_e2_noncomm :
    triaxialChitureOp * triaxialMultipoleOp .electricTwo ≠
      triaxialMultipoleOp .electricTwo * triaxialChitureOp := by
  intro h
  have h1 := triaxialMultipoleOp_chiture_cov .electricTwo
  rw [h] at h1
  simp only [MengChPSelectionRules.chitureCharacter] at h1
  have hv := congrFun (congrArg (fun op : Module.End ℂ ChiralParitySpace =>
    op (Pi.single (0, 0) 1)) h1) (1, 0)
  simp [triaxialMultipoleOp, Module.End.mul_apply] at hv
  norm_num at hv

/-- Same-chiplex transitions vanish identically for all `E2`, `M1`, and `E3` multipoles. -/
theorem triaxial_same_chiplex_vanishes (m : MengChPSelectionRules.Multipole) :
    chiralBandBra 1 1 (triaxialMultipoleOp m (chiralBandKet 0 0)) = 0 := by
  apply MengChPSelectionRules.same_chiplex_transition_vanishes m triaxialChitureOp
    triaxialParityOp (triaxialMultipoleOp m) (chiralBandBra 1 1) (chiralBandKet 0 0) 1
    one_ne_zero
  · change triaxialChiplexOp (chiralBandKet 0 0) = (1 : ℂ) • chiralBandKet 0 0
    simpa using triaxialChiplexOp_eigen 0 0
  · intro s
    change chiralBandBra 1 1 (triaxialChiplexOp s) = (1 : ℂ) * chiralBandBra 1 1 s
    simpa using chiralBandBra_chiplex_eigen 1 1 s
  · exact triaxialMultipoleOp_chiture_cov m
  · exact triaxialMultipoleOp_parity_cov m

/-- Nonzero opposite-chiplex transition witnesses for `E2`, `M1`, and `E3`. -/
theorem triaxial_opposite_chiplex_allowed_nonzero :
    chiralBandBra 1 0 (triaxialMultipoleOp .electricTwo (chiralBandKet 0 0)) ≠ 0 ∧
    chiralBandBra 1 0 (triaxialMultipoleOp .magneticOne (chiralBandKet 0 0)) ≠ 0 ∧
    chiralBandBra 0 1 (triaxialMultipoleOp .electricThree (chiralBandKet 0 0)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [chiralBandBra, chiralBandKet, triaxialMultipoleOp]
  · simp [chiralBandBra, chiralBandKet, triaxialMultipoleOp]
  · simp [chiralBandBra, chiralBandKet, triaxialMultipoleOp]

/-- Obstruction-driven chiral shift: `E2` and `M1` anticommute with `triaxialChitureOp`,
shifting `chiture` eigenvalue `+1 ↔ -1` across the doublet partners, while `E3` commutes
with `triaxialChitureOp` and anticommutes with `triaxialParityOp`, shifting intrinsic parity. -/
theorem triaxialMultipoleOp_chiture_shift (m : MengChPSelectionRules.Multipole)
    (χSign πSign : Fin 2) :
    triaxialChitureOp (triaxialMultipoleOp m (chiralBandKet χSign πSign)) =
      (MengChPSelectionRules.chitureCharacter m * (if χSign = 0 then (1 : ℂ) else -1)) •
        triaxialMultipoleOp m (chiralBandKet χSign πSign) ∧
    triaxialParityOp (triaxialMultipoleOp m (chiralBandKet χSign πSign)) =
      (MengChPSelectionRules.parityCharacter m * (if πSign = 0 then (1 : ℂ) else -1)) •
        triaxialMultipoleOp m (chiralBandKet χSign πSign) := by
  constructor
  · have hc := congrArg (fun op : Module.End ℂ ChiralParitySpace => op (chiralBandKet χSign πSign))
      (triaxialMultipoleOp_chiture_cov m)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, triaxialChitureOp_eigen, map_smul] at hc
    rw [hc, smul_smul]
  · have hp := congrArg (fun op : Module.End ℂ ChiralParitySpace => op (chiralBandKet χSign πSign))
      (triaxialMultipoleOp_parity_cov m)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, triaxialParityOp_eigen, map_smul] at hp
    rw [hp, smul_smul]

theorem triaxialChitureOp_eq_chpChitureOp :
    triaxialChitureOp = InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpChitureOp := by
  ext ψ ⟨c, p⟩
  fin_cases c <;> fin_cases p <;>
    simp [triaxialChitureOp, MengChPSelectionRules.chiture, triaxialRotationOp,
      triaxialExchangeOp, triaxialIntrinsicParityOp,
      InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpChitureOp,
      InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpRotationOp,
      InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpExchangeOp,
      InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpIntrinsicParityOp,
      Module.End.mul_apply]

theorem triaxialIntrinsicParityOp_eq_chpIntrinsicParityOp :
    triaxialIntrinsicParityOp =
      InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpIntrinsicParityOp := by
  ext ψ ⟨c, p⟩
  fin_cases p <;>
    simp [triaxialIntrinsicParityOp,
      InfoGeometry.Physics.NuclearInternalExternalParityFactorization.chpIntrinsicParityOp]

end TriaxialChPRealization

end InfoGeometry.Physics.NuclearChiralMengBridge
