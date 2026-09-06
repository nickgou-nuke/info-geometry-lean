import Mathlib.Tactic
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.Cl55SpinorCartanFock

/-!
# Nuclear CAR ↔ Cl(5,5) Cartan/parity dictionary

The nuclear one-mode CAR Cartan `2N-1` and the five-mode Witt-CAR Cartan
`H_a = e_a f_a - 1/2` live in different representations and are not identified.
This file records the exact normalization and relation-shape dictionary:
`2 H_a` has the same `±2` root weights as the centered nuclear occupation
Cartan.  It also places the nuclear fermion-parity involution beside the
independent `Cl(5,5)` global chirality involution and its complementary
projectors.

No physical identification of a nuclear mode with a `Cl(5,5)` spinor mode is
asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearCl55CartanParityDictionary

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge.QuasiparticleCAR
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.Cl55WittLieRouting

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- `Cl(5,5)` Cartan generator in the same `±2` normalization as the nuclear
centered occupation Cartan. -/
def normalizedCl55Cartan (a : Fin 5) : MatStage 5 :=
  (2 : ℝ) • H a

/-- The normalized `Cl(5,5)` Cartan gives creation weight `+2`. -/
theorem normalizedCl55Cartan_creation (a : Fin 5) :
    bracket (normalizedCl55Cartan a) (e a) = (2 : ℝ) • e a := by
  calc
    bracket (normalizedCl55Cartan a) (e a) =
        (2 : ℝ) • bracket (H a) (e a) := by
      unfold normalizedCl55Cartan bracket
      simp [smul_mul_assoc, mul_smul_comm, smul_sub]
    _ = (2 : ℝ) • e a := by rw [H_creation]; simp

/-- The normalized `Cl(5,5)` Cartan gives annihilation weight `-2`. -/
theorem normalizedCl55Cartan_annihilation (a : Fin 5) :
    bracket (normalizedCl55Cartan a) (f a) = (-2 : ℝ) • f a := by
  calc
    bracket (normalizedCl55Cartan a) (f a) =
        (2 : ℝ) • bracket (H a) (f a) := by
      unfold normalizedCl55Cartan bracket
      simp [smul_mul_assoc, mul_smul_comm, smul_sub]
    _ = (2 : ℝ) • (-f a) := by rw [H_annihilation]; simp
    _ = (-2 : ℝ) • f a := by simp

/-- The `Cl(5,5)` chirality and chiral projectors form a complementary parity
packet. -/
theorem cl55_chiral_projector_packet :
    gammaChiral * gammaChiral = 1 ∧
      PPlus * PPlus = PPlus ∧
      PMinus * PMinus = PMinus ∧
      PPlus * PMinus = 0 ∧
      PPlus + PMinus = 1 :=
  ⟨gammaChiral_sq, PPlus_sq, PMinus_sq, PPlus_mul_PMinus, P_sum⟩

/-- Nuclear one-mode fermion parity and `Cl(5,5)` chirality are both
involutions in their respective native carriers. -/
theorem nuclear_cl55_parity_shape_packet
    (car : QuasiparticleCAR ι A) (i : ι) :
    car.fermionParity i * car.fermionParity i = 1 ∧
      gammaChiral * gammaChiral = 1 :=
  ⟨car.fermionParity_sq i, gammaChiral_sq⟩

/-- Cartan relation-shape comparison at the common `±2` normalization. -/
theorem nuclear_cl55_cartan_shape_packet
    (car : QuasiparticleCAR ι A) (i : ι) (a : Fin 5) :
    (QuasiparticleCAR.comm (car.centeredOccupationCartan i) (car.adag i) =
        car.adag i + car.adag i ∧
      QuasiparticleCAR.comm (car.centeredOccupationCartan i) (car.a i) =
        -(car.a i + car.a i)) ∧
    (bracket (normalizedCl55Cartan a) (e a) = (2 : ℝ) • e a ∧
      bracket (normalizedCl55Cartan a) (f a) = (-2 : ℝ) • f a) :=
  ⟨⟨car.comm_centeredOccupationCartan_adag i,
      car.comm_centeredOccupationCartan_a i⟩,
    ⟨normalizedCl55Cartan_creation a,
      normalizedCl55Cartan_annihilation a⟩⟩

end InfoGeometry.Physics.NuclearCl55CartanParityDictionary
