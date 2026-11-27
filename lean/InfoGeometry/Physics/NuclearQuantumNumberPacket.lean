/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.GammasphereZornMap
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Superalgebra.WittenMoebiusChiralParity

/-!
# Finite nuclear quantum-number packet

This file packages only quantum-number readouts already represented elsewhere
in the repository:

* `2J`, from the positive half-integer spin carrier in `GammasphereZornMap`;
* one-mode quasiparticle occupation `n ∈ {0,1}`;
* the Wigner isospin-doublet projection `2T₃ ∈ {-1,+1}`;
* the associated one-mode fermion-parity and centered-occupation weights.

The parity readout here is quasiparticle fermion parity.  It is not a
formalization of nuclear spatial/intrinsic parity, orbital angular momentum,
seniority, or a complete shell-model quantum-number scheme.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearQuantumNumberPacket

open InfoGeometry.Physics.Gammasphere
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.NuclearWignerSupermultiplet

/-- The two projections of the Wigner isospin-`1/2` doublet. -/
inductive IsospinDoubletProjection where
  | negative
  | positive
  deriving DecidableEq, Repr

namespace IsospinDoubletProjection

/-- Integer `2T₃` readout. -/
def twoT3 : IsospinDoubletProjection → ℤ
  | negative => -1
  | positive => 1

/-- Spectral projector for the selected `T₃` sector. -/
def projector : IsospinDoubletProjection → Matrix (Fin 2) (Fin 2) ℂ
  | negative => isospinNegativeProjector
  | positive => isospinPositiveProjector

@[simp] theorem twoT3_sq (q : IsospinDoubletProjection) :
    q.twoT3 ^ 2 = 1 := by
  cases q <;> norm_num [twoT3]

/-- Every isospin-doublet sector is represented by an idempotent projector. -/
theorem projector_idempotent (q : IsospinDoubletProjection) :
    q.projector * q.projector = q.projector := by
  cases q
  · exact isospinNegativeProjector_idempotent
  · exact isospinPositiveProjector_idempotent

/-- `2T₃` acts by eigenvalue `-1` on the negative sector. -/
theorem cartan_mul_negative_projector :
    isospinCartan * projector .negative =
      (-1 : ℂ) • projector .negative := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector,
      InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinCartan,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospin3,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3,
      InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinNegativeProjector]

/-- `2T₃` acts by eigenvalue `+1` on the positive sector. -/
theorem cartan_mul_positive_projector :
    isospinCartan * projector .positive =
      (1 : ℂ) • projector .positive := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector,
      InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinCartan,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospin3,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3,
      InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinPositiveProjector]

/-- Uniform eigenprojector statement for the Wigner doublet. -/
theorem cartan_mul_projector (q : IsospinDoubletProjection) :
    isospinCartan * q.projector = (q.twoT3 : ℂ) • q.projector := by
  cases q
  · simpa [twoT3] using cartan_mul_negative_projector
  · simpa [twoT3] using cartan_mul_positive_projector

end IsospinDoubletProjection

/-- A finite packet of nuclear quantum-number data already owned by the current
formalization. -/
structure QuantumNumbers where
  spin : NuclearSpin
  occupation : OccupationQuantumNumber
  isospinProjection : IsospinDoubletProjection
  deriving Repr

namespace QuantumNumbers

/-- Positive integer readout `2J`. -/
def twoJ (q : QuantumNumbers) : ℕ := q.spin.1

/-- `2J` is strictly positive by construction. -/
theorem twoJ_pos (q : QuantumNumbers) : 0 < q.twoJ := q.spin.2

/-- Quasiparticle occupation `n ∈ {0,1}`. -/
def occupationNumber (q : QuantumNumbers) : ℤ := q.occupation.value

/-- Centered occupation Cartan weight `2n-1`. -/
def occupationCartanWeight (q : QuantumNumbers) : ℤ :=
  q.occupation.cartanWeight

/-- One-mode quasiparticle fermion parity `(-1)^n`. -/
def quasiparticleParity (q : QuantumNumbers) : ℤ :=
  q.occupation.parityWeight

/-- Wigner isospin projection represented as `2T₃`. -/
def twoT3 (q : QuantumNumbers) : ℤ := q.isospinProjection.twoT3

@[simp] theorem occupationCartanWeight_formula (q : QuantumNumbers) :
    q.occupationCartanWeight = 2 * q.occupationNumber - 1 := by
  exact q.occupation.cartanWeight_eq_two_value_sub_one

@[simp] theorem quasiparticleParity_formula (q : QuantumNumbers) :
    q.quasiparticleParity = 1 - 2 * q.occupationNumber := by
  exact q.occupation.parityWeight_eq_one_sub_two_value

@[simp] theorem quasiparticleParity_sq (q : QuantumNumbers) :
    q.quasiparticleParity ^ 2 = 1 := by
  exact q.occupation.parityWeight_sq

@[simp] theorem twoT3_sq (q : QuantumNumbers) : q.twoT3 ^ 2 = 1 := by
  exact q.isospinProjection.twoT3_sq

/-- The isospin part of a quantum-number packet selects a genuine spectral
projector of the normalized Wigner Cartan operator. -/
theorem isospin_projector_eigenvalue (q : QuantumNumbers) :
    isospinCartan * q.isospinProjection.projector =
      (q.twoT3 : ℂ) • q.isospinProjection.projector := by
  exact q.isospinProjection.cartan_mul_projector

end QuantumNumbers

/-! ## Concrete inhabitant & 4-parity / (S, T) / K^π nuclear taxonomy packet -/

/-- Canonical constructive inhabitant of `QuantumNumbers` (`2J = 1`, vacant mode, proton `2T₃ = +1`). -/
def defaultQuantumNumbers : QuantumNumbers where
  spin := ⟨1, Nat.zero_lt_succ 0⟩
  occupation := .vacant
  isospinProjection := .positive

inductive WittenMoebiusSector
  | wmEven
  | wmOdd
  deriving DecidableEq, Repr

namespace WittenMoebiusSector

def sign : WittenMoebiusSector → ℤ
  | .wmEven => 1
  | .wmOdd => -1

def toBool : WittenMoebiusSector → Bool
  | .wmEven => true
  | .wmOdd => false

theorem sign_sq (w : WittenMoebiusSector) : w.sign ^ 2 = 1 := by
  cases w <;> norm_num [sign]

theorem sign_eq_bool (w : WittenMoebiusSector) :
    (w.sign : ℂ) = if w.toBool then (1 : ℂ) else -1 := by
  cases w <;> simp [sign, toBool]

end WittenMoebiusSector

inductive MengChitureSector
  | chiEven
  | chiOdd
  deriving DecidableEq, Repr

namespace MengChitureSector

def sign : MengChitureSector → ℤ
  | .chiEven => 1
  | .chiOdd => -1

def toBool : MengChitureSector → Bool
  | .chiEven => true
  | .chiOdd => false

theorem sign_sq (m : MengChitureSector) : m.sign ^ 2 = 1 := by
  cases m <;> norm_num [sign]

theorem sign_eq_bool (m : MengChitureSector) :
    (m.sign : ℂ) = if m.toBool then (1 : ℂ) else -1 := by
  cases m <;> simp [sign, toBool]

end MengChitureSector

inductive SpinPairingLabel
  | spinSinglet
  | spinTriplet
  deriving DecidableEq, Repr

inductive IsospinPairingLabel
  | isoSinglet
  | isoTriplet
  deriving DecidableEq, Repr

/-- Complete nuclear quantum-number taxonomy packet unifying:
1. spin `2J`, quasiparticle occupation, and isospin projection `2T₃` (`base`);
2. axial rotational bandhead `2K` and Nilsson single-particle `2Ω`;
3. spatial parity `π ∈ {±1}`, Witten–Möbius Zorn parity `wmSector`, and Meng chiture `chitureSector`;
4. Wigner `(S, T)` two-nucleon pairing sector labels. -/
structure NuclearTaxonomyPacket where
  base : QuantumNumbers
  twoK : ℕ
  twoOmega : ℕ
  spatialParitySign : ℤ
  spatial_parity_sq : spatialParitySign ^ 2 = 1
  wmSector : WittenMoebiusSector
  chitureSector : MengChitureSector
  spinPairing : SpinPairingLabel
  isospinPairing : IsospinPairingLabel

/-- Canonical constructive inhabitant of `NuclearTaxonomyPacket` (`2K = 0`, `π = +1`, `(S=0, T=1)`). -/
def defaultTaxonomyPacket : NuclearTaxonomyPacket where
  base := defaultQuantumNumbers
  twoK := 0
  twoOmega := 1
  spatialParitySign := 1
  spatial_parity_sq := by norm_num
  wmSector := .wmEven
  chitureSector := .chiEven
  spinPairing := .spinSinglet
  isospinPairing := .isoTriplet

namespace NuclearTaxonomyPacket

open InfoGeometry.Physics.NuclearInternalExternalParityFactorization

def spatialParityBool (p : NuclearTaxonomyPacket) : Bool :=
  decide (p.spatialParitySign = 1)

def fermionParityBool (p : NuclearTaxonomyPacket) : Bool :=
  decide (p.base.quasiparticleParity = 1)

theorem spatialParitySign_cases (p : NuclearTaxonomyPacket) :
    p.spatialParitySign = 1 ∨ p.spatialParitySign = -1 := by
  have h : (p.spatialParitySign - 1) * (p.spatialParitySign + 1) = 0 := by
    have hsq := p.spatial_parity_sq
    linarith
  rcases mul_eq_zero.mp h with h1 | h2
  · left; omega
  · right; omega

theorem spatialParitySign_eq_bool (p : NuclearTaxonomyPacket) :
    (p.spatialParitySign : ℂ) = if p.spatialParityBool then (1 : ℂ) else -1 := by
  unfold spatialParityBool
  rcases p.spatialParitySign_cases with h | h <;> simp [h]

theorem fermionParity_eq_bool (p : NuclearTaxonomyPacket) :
    (p.base.quasiparticleParity : ℂ) = if p.fermionParityBool then (1 : ℂ) else -1 := by
  unfold fermionParityBool QuantumNumbers.quasiparticleParity
  cases p.base.occupation <;> simp [OccupationQuantumNumber.parityWeight]

/-- Joint 4-tuple of parity bits `(π, (-1)^N, P_WM, P_Meng)` indexing the 16 commuting sectors. -/
def parityTuple (p : NuclearTaxonomyPacket) : Fin 4 → Bool :=
  ![p.spatialParityBool, p.fermionParityBool, p.wmSector.toBool, p.chitureSector.toBool]

/-- Joint four-parity spectral projector in `Module.End ℂ FourParityCarrier` selected by `p`. -/
def fourParityProj (p : NuclearTaxonomyPacket) : Module.End ℂ FourParityCarrier :=
  fourParityProjector p.parityTuple

theorem fourParityProj_idem (p : NuclearTaxonomyPacket) :
    p.fourParityProj * p.fourParityProj = p.fourParityProj := by
  unfold fourParityProj
  exact fourParityProjector_idem p.parityTuple

theorem fourParityProj_ne_zero (p : NuclearTaxonomyPacket) :
    p.fourParityProj ≠ 0 := by
  unfold fourParityProj
  exact fourParityProjector_ne_zero p.parityTuple

theorem fourParityProj_orth (p q : NuclearTaxonomyPacket)
    (hne : p.parityTuple ≠ q.parityTuple) :
    p.fourParityProj * q.fourParityProj = 0 := by
  unfold fourParityProj
  exact fourParityProjector_mul_ne p.parityTuple q.parityTuple hne

private theorem piOp_mul_fourParityProjector (b : Fin 4 → Bool) :
    piOp * fourParityProjector b =
      (if b 0 then (1 : ℂ) else -1) • fourParityProjector b := by
  unfold fourParityProjector
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
    mul_involutionProjector piOp piOp_sq (b 0), smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]

private theorem fermionOp_mul_fourParityProjector (b : Fin 4 → Bool) :
    fermionOp * fourParityProjector b =
      (if b 1 then (1 : ℂ) else -1) • fourParityProjector b := by
  have hc12 : fermionOp * involutionProjector (K := ℂ) piOp (b 0) =
      involutionProjector (K := ℂ) piOp (b 0) * fermionOp := by
    have hc : fermionOp * piOp = piOp * fermionOp := (liftSector_1_2_comm _ _).symm
    unfold involutionProjector
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, hc]
  unfold fourParityProjector
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hc12, mul_assoc _ fermionOp,
    mul_involutionProjector fermionOp fermionOp_sq (b 1), mul_smul_comm,
    smul_mul_assoc, smul_mul_assoc]

private theorem wmOp_mul_fourParityProjector (b : Fin 4 → Bool) :
    wmOp * fourParityProjector b =
      (if b 2 then (1 : ℂ) else -1) • fourParityProjector b := by
  have hc13 : wmOp * involutionProjector (K := ℂ) piOp (b 0) =
      involutionProjector (K := ℂ) piOp (b 0) * wmOp := by
    have hc : wmOp * piOp = piOp * wmOp := (liftSector_1_3_comm _ _).symm
    unfold involutionProjector
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, hc]
  have hc23 : wmOp * involutionProjector (K := ℂ) fermionOp (b 1) =
      involutionProjector (K := ℂ) fermionOp (b 1) * wmOp := by
    have hc : wmOp * fermionOp = fermionOp * wmOp := (liftSector_2_3_comm _ _).symm
    unfold involutionProjector
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, hc]
  unfold fourParityProjector
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hc13, mul_assoc _ wmOp, hc23, ← mul_assoc,
    mul_assoc _ wmOp, mul_involutionProjector wmOp wmOp_sq (b 2), mul_smul_comm,
    smul_mul_assoc]

private theorem mengParityOp_mul_fourParityProjector (b : Fin 4 → Bool) :
    mengParityOp * fourParityProjector b =
      (if b 3 then (1 : ℂ) else -1) • fourParityProjector b := by
  have hc14 : mengParityOp * involutionProjector (K := ℂ) piOp (b 0) =
      involutionProjector (K := ℂ) piOp (b 0) * mengParityOp := by
    have hc : mengParityOp * piOp = piOp * mengParityOp := (liftSector_1_4_comm _ _).symm
    unfold involutionProjector
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, hc]
  have hc24 : mengParityOp * involutionProjector (K := ℂ) fermionOp (b 1) =
      involutionProjector (K := ℂ) fermionOp (b 1) * mengParityOp := by
    have hc : mengParityOp * fermionOp = fermionOp * mengParityOp := (liftSector_2_4_comm _ _).symm
    unfold involutionProjector
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, hc]
  have hc34 : mengParityOp * involutionProjector (K := ℂ) wmOp (b 2) =
      involutionProjector (K := ℂ) wmOp (b 2) * mengParityOp := by
    have hc : mengParityOp * wmOp = wmOp * mengParityOp := (liftSector_3_4_comm _ _).symm
    unfold involutionProjector
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, hc]
  unfold fourParityProjector
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hc14, mul_assoc _ mengParityOp, hc24, ← mul_assoc,
    mul_assoc _ mengParityOp, hc34, ← mul_assoc, mul_assoc _ mengParityOp,
    mul_involutionProjector mengParityOp mengParityOp_sq (b 3), mul_smul_comm]

/-- Compatibility certificate uniting the Wigner isospin doublet projector, the four separated
parity eigenvalues `(π, (-1)^N, P_WM, P_Meng)` on `FourParityCarrier`, and nonvanishing sector
support `fourParityProj ≠ 0`. -/
theorem isospin_and_fourParity_compatibility (p : NuclearTaxonomyPacket) :
    (isospinCartan * p.base.isospinProjection.projector =
      (p.base.twoT3 : ℂ) • p.base.isospinProjection.projector) ∧
    (piOp * p.fourParityProj = (p.spatialParitySign : ℂ) • p.fourParityProj ∧
     fermionOp * p.fourParityProj = (p.base.quasiparticleParity : ℂ) • p.fourParityProj ∧
     wmOp * p.fourParityProj = (p.wmSector.sign : ℂ) • p.fourParityProj ∧
     mengParityOp * p.fourParityProj = (p.chitureSector.sign : ℂ) • p.fourParityProj) ∧
    (p.fourParityProj * p.fourParityProj = p.fourParityProj ∧ p.fourParityProj ≠ 0) ∧
    (piOp ≠ fermionOp ∧ fermionOp ≠ wmOp ∧ wmOp ≠ mengParityOp) := by
  have h1 : piOp * p.fourParityProj = (p.spatialParitySign : ℂ) • p.fourParityProj := by
    unfold fourParityProj
    rw [piOp_mul_fourParityProjector, p.spatialParitySign_eq_bool]
    rfl
  have h2 : fermionOp * p.fourParityProj = (p.base.quasiparticleParity : ℂ) • p.fourParityProj := by
    unfold fourParityProj
    rw [fermionOp_mul_fourParityProjector, p.fermionParity_eq_bool]
    rfl
  have h3 : wmOp * p.fourParityProj = (p.wmSector.sign : ℂ) • p.fourParityProj := by
    unfold fourParityProj
    rw [wmOp_mul_fourParityProjector, p.wmSector.sign_eq_bool]
    rfl
  have h4 : mengParityOp * p.fourParityProj = (p.chitureSector.sign : ℂ) • p.fourParityProj := by
    unfold fourParityProj
    rw [mengParityOp_mul_fourParityProjector, p.chitureSector.sign_eq_bool]
    rfl
  rcases four_parity_separation_and_compatibility with
    ⟨_, _, ⟨_, hpi_ferm, _, _, _, _, hferm_wm, _, _, _, hwm_meng, _⟩, _⟩
  refine ⟨QuantumNumbers.isospin_projector_eigenvalue p.base, ⟨h1, h2, h3, h4⟩,
    ⟨p.fourParityProj_idem, p.fourParityProj_ne_zero⟩,
    ⟨hpi_ferm, hferm_wm, hwm_meng⟩⟩

/-- Predicate encoding the `K = 0` rotational even-odd staggering rule `(-1)^I = π`
expressed in doubled spin `twoI = 2I`. -/
def kZeroStaggeringAllowed (twoI : ℕ) (piSign : ℤ) :
    Prop :=
  twoI % 2 = 0 ∧ ((twoI % 4 = 0 ∧ piSign = 1) ∨ (twoI % 4 = 2 ∧ piSign = -1))

/-- For any even integer `twoI = 2I` and parity `π ∈ {±1}`, `K = 0` staggering selects
`I` even iff `π = +1` and `I` odd iff `π = -1`. -/
theorem k_zero_parity_staggering_iff (twoI : ℕ) (hEven : twoI % 2 = 0)
    (piSign : ℤ) (hpi : piSign ^ 2 = 1) :
    (kZeroStaggeringAllowed twoI piSign ↔
      ((piSign = 1 ∧ twoI % 4 = 0) ∨ (piSign = -1 ∧ twoI % 4 = 2))) := by
  unfold kZeroStaggeringAllowed
  have _hcases : piSign = 1 ∨ piSign = -1 := by
    have hfac : (piSign - 1) * (piSign + 1) = 0 := by
      have hsq := hpi
      linarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left; omega
    · right; omega
  constructor
  · intro ⟨_, hst⟩
    rcases hst with ⟨h0, hp⟩ | ⟨h2, hp⟩
    · left; exact ⟨hp, h0⟩
    · right; exact ⟨hp, h2⟩
  · intro hst
    refine ⟨hEven, ?_⟩
    rcases hst with ⟨hp, h0⟩ | ⟨hp, h2⟩
    · left; exact ⟨h0, hp⟩
    · right; exact ⟨h2, hp⟩

/-- Whether the packet's `(S, T)` pairing label lies in Wigner's antisymmetric `6_A` multiplet
`(S=0, T=1) ⊕ (S=1, T=0)` (`Casimir = 5`) versus `10_S` (`Casimir = 9`). -/
def inWigner6AMultiplet (p : NuclearTaxonomyPacket) :
    Prop :=
  (p.spinPairing = .spinSinglet ∧ p.isospinPairing = .isoTriplet) ∨
  (p.spinPairing = .spinTriplet ∧ p.isospinPairing = .isoSinglet)

theorem inWigner6AMultiplet_iff_ne (p : NuclearTaxonomyPacket) :
    p.inWigner6AMultiplet ↔
      ((p.spinPairing = .spinSinglet) ↔ (p.isospinPairing = .isoTriplet)) := by
  unfold inWigner6AMultiplet
  cases p.spinPairing <;> cases p.isospinPairing <;> simp

end NuclearTaxonomyPacket

end InfoGeometry.Physics.NuclearQuantumNumberPacket
