import Mathlib
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem

/-!
# Exact compression of the common CAR--phonon Hamiltonian

The scalar Soloviev parameters are realized here as matrix elements of one
explicit operator on the common quasiparticle--phonon carrier. The two model
channels are the occupied quasiparticle state with zero and one phonon.

The theorem is a genuine section--retraction compression statement:

`readout (H_full (embed v)) = H_QPNM *ᵥ v`.

No identification of the full occupation carrier with the two-dimensional
model space is made.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSolovievCompression

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Physics.NuclearCARPhononCommonCarrier
open InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev ModelVector := Fin 2 → ℝ

/-- Scalar copy of the Zorn unit, written explicitly so the model-space
readout is definitionally transparent. -/
def scalarCoefficient (c : ℝ) : Coefficient where
  a := c
  v := fun _ => 0
  w := fun _ => 0
  b := c

/-- Occupied one-quasiparticle sheet with scalar coefficient `c`. -/
def occupiedKet (c : ℝ) : Sheet :=
  (0, scalarCoefficient c)

@[simp] theorem occupiedKet_second_a (c : ℝ) :
    (occupiedKet c).2.a = c := rfl

/-- Embed the two Soloviev channels as the zero- and one-phonon occupied
quasiparticle states. -/
def modelEmbed : ModelVector →ₗ[ℝ] Carrier where
  toFun v
    | 0 => occupiedKet (v 0)
    | Nat.succ 0 => occupiedKet (v 1)
    | Nat.succ (Nat.succ _) => 0
  map_add' v w := by
    funext n
    cases n with
    | zero => simp [occupiedKet, scalarCoefficient]
    | succ n =>
        cases n with
        | zero => simp [occupiedKet, scalarCoefficient]
        | succ n => simp
  map_smul' c v := by
    funext n
    cases n with
    | zero => simp [occupiedKet, scalarCoefficient]
    | succ n =>
        cases n with
        | zero => simp [occupiedKet, scalarCoefficient]
        | succ n => simp

@[simp] theorem modelEmbed_zero_level (v : ModelVector) :
    modelEmbed v 0 = occupiedKet (v 0) := rfl

@[simp] theorem modelEmbed_one_level (v : ModelVector) :
    modelEmbed v 1 = occupiedKet (v 1) := rfl

@[simp] theorem modelEmbed_high_level
    (v : ModelVector) (n : ℕ) :
    modelEmbed v (n + 2) = 0 := by
  rfl

/-- Read the scalar occupied-sheet coefficients in the zero- and one-phonon
channels. -/
def modelReadout : Carrier →ₗ[ℝ] ModelVector where
  toFun ψ := ![(ψ 0).2.a, (ψ 1).2.a]
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' c ψ := by
    ext i
    fin_cases i <;> simp

/-- The readout is a left inverse of the model embedding. -/
@[simp] theorem modelReadout_modelEmbed (v : ModelVector) :
    modelReadout (modelEmbed v) = v := by
  ext i
  fin_cases i <;> rfl

/-- Quasiparticle occupation projection on the common carrier. -/
def qpNumber : Operator :=
  qpCreation * qpAnnihilation

/-- Phonon number operator on the polynomial occupation basis. -/
def phononNumber : Operator :=
  phononCreation * phononAnnihilation

@[simp] theorem qpNumber_apply (ψ : Carrier) (n : ℕ) :
    qpNumber ψ n = (0, (ψ n).2) := by
  rcases ψ n with ⟨x₀, x₁⟩
  rfl

@[simp] theorem phononNumber_zero (ψ : Carrier) :
    phononNumber ψ 0 = 0 := rfl

@[simp] theorem phononNumber_succ (ψ : Carrier) (n : ℕ) :
    phononNumber ψ (n + 1) = ((n + 1 : ℕ) : ℝ) • ψ (n + 1) := rfl

/-- Full one-quasiparticle harmonic-phonon Hamiltonian with linear channel
coupling. Its model compression is the Soloviev QPNM matrix. -/
def fullQPNMHamiltonian (Eqp omega V : ℝ) : Operator :=
  Eqp • qpNumber + omega • phononNumber +
    V • (phononCreation + phononAnnihilation)

/-- Compression through the explicit section and retraction. -/
def compressedAction (Eqp omega V : ℝ) : ModelVector →ₗ[ℝ] ModelVector :=
  modelReadout.comp ((fullQPNMHamiltonian Eqp omega V).comp modelEmbed)

/-- Zero-phonon component of the compressed Hamiltonian. -/
theorem compressedAction_zero
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 0 = Eqp * C + V * D := by
  simp [compressedAction, fullQPNMHamiltonian, qpNumber, phononNumber,
    modelReadout, modelEmbed, occupiedKet, scalarCoefficient,
    qpAnnihilation, qpCreation, pointwiseSheetLift,
    phononCreation, phononAnnihilation, Module.End.mul_apply]
  ring

/-- One-phonon component of the compressed Hamiltonian. -/
theorem compressedAction_one
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 1 =
      V * C + (Eqp + omega) * D := by
  simp [compressedAction, fullQPNMHamiltonian, qpNumber, phononNumber,
    modelReadout, modelEmbed, occupiedKet, scalarCoefficient,
    qpAnnihilation, qpCreation, pointwiseSheetLift,
    phononCreation, phononAnnihilation, Module.End.mul_apply]
  ring

/-- Main compression theorem: the common-carrier Hamiltonian restricts and
projects exactly to the finite Soloviev QPNM action. -/
theorem compressedAction_eq_qpnm_mulVec
    (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] =
      mulVec (qpnmMatrix Eqp omega V) ![C, D] := by
  ext i
  fin_cases i
  · rw [compressedAction_zero]
    simp [qpnmMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  · rw [compressedAction_one]
    simp [qpnmMatrix, mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The matrix eigenvalue system is therefore exactly the compressed full
operator eigenvalue system on the two selected channels. -/
theorem compressed_eigenvalue_system
    (Eqp omega V E C D : ℝ) :
    compressedAction Eqp omega V ![C, D] = E • ![C, D] ↔
      ((Eqp - E) * C + V * D = 0 ∧
        V * C + (Eqp + omega - E) * D = 0) := by
  rw [compressedAction_eq_qpnm_mulVec]
  exact qpnm_eigenvalue_system Eqp omega V E C D

/-- Complete finite compression packet. -/
theorem soloviev_compression_packet
    (Eqp omega V C D : ℝ) :
    modelReadout (modelEmbed ![C, D]) = ![C, D] ∧
      compressedAction Eqp omega V ![C, D] =
        mulVec (qpnmMatrix Eqp omega V) ![C, D] ∧
      compressedAction Eqp omega V ![C, D] 0 = Eqp * C + V * D ∧
      compressedAction Eqp omega V ![C, D] 1 =
        V * C + (Eqp + omega) * D := by
  exact ⟨modelReadout_modelEmbed _,
    compressedAction_eq_qpnm_mulVec Eqp omega V C D,
    compressedAction_zero Eqp omega V C D,
    compressedAction_one Eqp omega V C D⟩

end InfoGeometry.Physics.NuclearSolovievCompression
