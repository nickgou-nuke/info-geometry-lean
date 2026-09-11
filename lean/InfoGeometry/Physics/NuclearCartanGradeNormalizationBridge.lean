import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearGradedBathCommutant
import InfoGeometry.Physics.Cl55SpinorCartanFock

/-!
# Nuclear Cartan normalization and graded-bath bridge

Two useful Cartan normalizations coexist in the nuclear lane:

* `2N-1`, with the standard `sl₂` root weights `±2`;
* `N-1/2`, with occupation/root weights `±1`.

The second normalization matches both the integer grading convention used by
`NuclearGradedBathCommutant` and the Witt-CAR Cartan convention used by
`Cl55SpinorCartanFock`.

A grading is not automatically assumed to arise from an inner Cartan action.
The predicate `CartanRealizesGrade` records that additional statement
explicitly; all thermal consequences below require it as a hypothesis.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearCartanGradeNormalizationBridge

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.NuclearGradedBathCommutant
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.Cl55WittLieRouting

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Balanced occupation Cartan `Kᵢ = Nᵢ - 1/2`. -/
def balancedOccupationCartan
    (car : QuasiparticleCAR ι A) (i : ι) : A :=
  car.numberOp i - (1 / 2 : ℝ) • (1 : A)

/-- Creation has balanced Cartan weight `+1`. -/
theorem comm_balancedOccupationCartan_adag
    (car : QuasiparticleCAR ι A) (i : ι) :
    QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.adag i) =
      car.adag i := by
  unfold balancedOccupationCartan QuasiparticleCAR.comm
  calc
    (car.numberOp i - (1 / 2 : ℝ) • (1 : A)) * car.adag i -
        car.adag i * (car.numberOp i - (1 / 2 : ℝ) • (1 : A)) =
      QuasiparticleCAR.comm (car.numberOp i) (car.adag i) := by
        simp [QuasiparticleCAR.comm, sub_mul, mul_sub,
          Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    _ = car.adag i := car.comm_numberOp_adag_same i

/-- Annihilation has balanced Cartan weight `-1`. -/
theorem comm_balancedOccupationCartan_a
    (car : QuasiparticleCAR ι A) (i : ι) :
    QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.a i) =
      -car.a i := by
  unfold balancedOccupationCartan QuasiparticleCAR.comm
  calc
    (car.numberOp i - (1 / 2 : ℝ) • (1 : A)) * car.a i -
        car.a i * (car.numberOp i - (1 / 2 : ℝ) • (1 : A)) =
      QuasiparticleCAR.comm (car.numberOp i) (car.a i) := by
        simp [QuasiparticleCAR.comm, sub_mul, mul_sub,
          Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    _ = -car.a i := car.comm_numberOp_a_same i

/-- The `sl₂`-normalized centered Cartan is twice the balanced Cartan. -/
theorem centeredOccupationCartan_eq_two_smul_balanced
    (car : QuasiparticleCAR ι A) (i : ι) :
    car.centeredOccupationCartan i =
      (2 : ℝ) • balancedOccupationCartan car i := by
  unfold InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR.centeredOccupationCartan
    balancedOccupationCartan
  rw [smul_sub, smul_smul]
  norm_num
  rw [two_smul]

/-- Explicit statement that an integer grading is realized by an inner Cartan
commutator.  This is additional structure, not a consequence of `LieGrading`. -/
def CartanRealizesGrade
    (H : A) (grade : ℤ → Submodule ℝ A) : Prop :=
  ∀ (k : ℤ) (x : A), x ∈ grade k →
    H * x - x * H = (k : ℝ) • x

/-- Grade zero is the Cartan centralizer whenever a Cartan realizes the grading. -/
theorem cartan_comm_grade_zero
    {H : A} {grade : ℤ → Submodule ℝ A}
    (hCartan : CartanRealizesGrade H grade)
    {x : A} (hx : x ∈ grade 0) :
    H * x - x * H = 0 := by
  simpa using hCartan 0 x hx

/-- A thermal quasiparticle creation operator has Cartan weight `+1` when the
thermal grading is Cartan-realized. -/
theorem quasiparticleCreation_cartan_weight_one
    {H : A} {grade : ℤ → Submodule ℝ A}
    (hCartan : CartanRealizesGrade H grade)
    {M : ThermalQuasiparticleModel grade}
    (q : QuasiparticleCreation grade M) :
    H * q.op - q.op * H = q.op := by
  simpa using hCartan 1 q.op q.grade_one

/-- The negative interaction channel has Cartan weight `-1`. -/
theorem interactionMinus_cartan_weight_neg_one
    {H : A} {grade : ℤ → Submodule ℝ A}
    (hCartan : CartanRealizesGrade H grade)
    (M : ThermalQuasiparticleModel grade) :
    H * M.H_int_minus - M.H_int_minus * H = -M.H_int_minus := by
  have h := hCartan (-1) M.H_int_minus M.h_int_minus_grade
  simpa using h

/-- The positive interaction channel has Cartan weight `+1`. -/
theorem interactionPlus_cartan_weight_one
    {H : A} {grade : ℤ → Submodule ℝ A}
    (hCartan : CartanRealizesGrade H grade)
    (M : ThermalQuasiparticleModel grade) :
    H * M.H_int_plus - M.H_int_plus * H = M.H_int_plus := by
  simpa using hCartan 1 M.H_int_plus M.h_int_plus_grade

/-- The free quasiparticle Hamiltonian is Cartan-neutral. -/
theorem freeHamiltonian_cartan_weight_zero
    {H : A} {grade : ℤ → Submodule ℝ A}
    (hCartan : CartanRealizesGrade H grade)
    (M : ThermalQuasiparticleModel grade) :
    H * M.H_qp - M.H_qp * H = 0 := by
  exact cartan_comm_grade_zero hCartan M.h_qp_grade

/-- `Cl(5,5)` Witt-CAR Cartan uses the same balanced `±1` normalization. -/
theorem cl55_balanced_cartan_packet (a : Fin 5) :
    bracket (H a) (e a) = e a ∧
      bracket (H a) (f a) = -f a := by
  constructor
  · simpa using H_creation a a
  · simpa using H_annihilation a a

/-- Relation-shape dictionary at balanced normalization. -/
theorem nuclear_cl55_balanced_cartan_shape_packet
    (car : QuasiparticleCAR ι A) (i : ι) (a : Fin 5) :
    (QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.adag i) =
        car.adag i ∧
      QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.a i) =
        -car.a i) ∧
    (bracket (H a) (e a) = e a ∧
      bracket (H a) (f a) = -f a) :=
  ⟨⟨comm_balancedOccupationCartan_adag car i,
      comm_balancedOccupationCartan_a car i⟩,
    cl55_balanced_cartan_packet a⟩

end InfoGeometry.Physics.NuclearCartanGradeNormalizationBridge
