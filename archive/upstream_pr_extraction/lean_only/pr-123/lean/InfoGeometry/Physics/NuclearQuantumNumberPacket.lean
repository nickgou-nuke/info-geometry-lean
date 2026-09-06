import Mathlib.Tactic
import InfoGeometry.Physics.GammasphereZornMap
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge

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

end InfoGeometry.Physics.NuclearQuantumNumberPacket
