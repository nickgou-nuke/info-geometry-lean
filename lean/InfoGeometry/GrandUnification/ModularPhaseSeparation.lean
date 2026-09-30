import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace InfoGeometry.GrandUnification.ModularPhaseSeparation

open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-! ### 1. Krein Symmetry and Chiral Gradings -/

/-- An operator is a Krein-Chiral symmetry if it acts as an involution on the space. -/
def IsKreinSymmetry (Γ : Module.End R M) : Prop :=
  Γ * Γ = 1

/-- An operator is 'odd' relative to the Krein grading if it perfectly anti-commutes with Γ. -/
def IsOddOperator (Γ A : Module.End R M) : Prop :=
  Γ * A = - (A * Γ)

/-- The Graded Krein Supertrace over the endomorphism algebra. -/
noncomputable def supertrace (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

/-! ### 2. The Triviality Bounds -/

lemma odd_operator_zero_of_grading_one (Γ A : Module.End R M) 
    (h_odd : IsOddOperator Γ A) (h_one : Γ = 1) : A = 0 := by
  unfold IsOddOperator at h_odd
  rw [h_one, mul_one, one_mul] at h_odd
  have h_add : A + A = 0 := by
    calc A + A = -A + A := by nth_rw 1 [h_odd]
         _ = 0 := neg_add_cancel A
  have h_two : (2 : R) • A = 0 := by
    calc (2 : R) • A = (1 + 1 : R) • A := by norm_num
         _ = (1 : R) • A + (1 : R) • A := add_smul 1 1 A
         _ = A + A := by simp only [one_smul]
         _ = 0 := h_add
  calc A = (1 : R) • A := by rw [one_smul]
       _ = (⅟(2 : R) * 2) • A := by rw [invOf_mul_self]
       _ = ⅟(2 : R) • ((2 : R) • A) := by rw [mul_smul]
       _ = ⅟(2 : R) • (0 : Module.End R M) := by rw [h_two]
       _ = 0 := smul_zero _

lemma odd_operator_zero_of_grading_neg_one (Γ A : Module.End R M) 
    (h_odd : IsOddOperator Γ A) (h_neg_one : Γ = -1) : A = 0 := by
  unfold IsOddOperator at h_odd
  rw [h_neg_one, neg_mul, mul_neg, one_mul, mul_one, neg_neg] at h_odd
  have h_add : A + A = 0 := by
    calc A + A = -A + A := by nth_rw 1 [← h_odd]
         _ = 0 := neg_add_cancel A
  have h_two : (2 : R) • A = 0 := by
    calc (2 : R) • A = (1 + 1 : R) • A := by norm_num
         _ = (1 : R) • A + (1 : R) • A := add_smul 1 1 A
         _ = A + A := by simp only [one_smul]
         _ = 0 := h_add
  calc A = (1 : R) • A := by rw [one_smul]
       _ = (⅟(2 : R) * 2) • A := by rw [invOf_mul_self]
       _ = ⅟(2 : R) • ((2 : R) • A) := by rw [mul_smul]
       _ = ⅟(2 : R) • (0 : Module.End R M) := by rw [h_two]
       _ = 0 := smul_zero _

/-! ### 3. Algebra (Ego) & Commutant (Anima) Modular Partition -/

/-- The Commutant (Anima) of an operator algebra block.
    Defines the set of all endomorphisms that commute with a given target operator. -/
def ModularCommutant (A : Module.End R M) : Submodule R (Module.End R M) where
  carrier := {X | X * A = A * X}
  zero_mem' := by dsimp; rw [zero_mul, mul_zero]
  add_mem' := by
    intro X Y hX hY; dsimp at *
    rw [add_mul, mul_add, hX, hY]
  smul_mem' := by
    intro c X hX; dsimp at *
    ext v
    simp only [LinearMap.mul_apply, LinearMap.smul_apply, LinearMap.map_smul]
    have h_eval : (X * A) v = (A * X) v := by rw [hX]
    simp only [LinearMap.mul_apply] at h_eval
    rw [h_eval]

/-! ### 4. The Modular Phase Separation Theorem -/

/-- Theorem: The presence of a non-trivial local spinning anomaly breaks the 
    ambient vacuum symmetry, separating the architecture into an algebra and its commutant. -/
theorem modular_phase_separation
    (Γ A B : Module.End R M)
    (h_odd_A : IsOddOperator Γ A)
    (h_anomaly : supertrace Γ (A * B - B * A) ≠ 0) :
    Γ ≠ 1 ∧ Γ ≠ -1 ∧ (B ∈ ModularCommutant A → False) := by
  constructor
  · intro h_one
    have hA_zero := odd_operator_zero_of_grading_one Γ A h_odd_A h_one
    rw [hA_zero, zero_mul, mul_zero, sub_zero] at h_anomaly
    have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
      unfold supertrace; rw [mul_zero, map_zero]
    exact h_anomaly h_str_zero
  · constructor
    · intro h_neg_one
      have hA_zero := odd_operator_zero_of_grading_neg_one Γ A h_odd_A h_neg_one
      rw [hA_zero, zero_mul, mul_zero, sub_zero] at h_anomaly
      have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
        unfold supertrace; rw [mul_zero, map_zero]
      exact h_anomaly h_str_zero
    · intro h_comm
      dsimp [ModularCommutant] at h_comm
      have h_sub_zero : A * B - B * A = 0 := by rw [h_comm, sub_self]
      rw [h_sub_zero] at h_anomaly
      have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
        unfold supertrace; rw [mul_zero, map_zero]
      exact h_anomaly h_str_zero

/-! ### 5. Grand Unification Modular Packet -/

/-- The Tomita-Takesaki-inspired Unification Packet structurally binding 
    the Krein spatial grading to the generation of the Algebra and Commutant sheets. -/
structure TomitaModularSeparationPacket (R M : Type*) [CommRing R] [Invertible (2 : R)] 
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] where
  /-- The Fundamental Krein Chiral Symmetry (The Grading operator). -/
  KreinSymmetry : Module.End R M
  
  /-- The Local Physical Algebra Generator (Ego Component). -/
  EgoOperator : Module.End R M
  
  /-- The Hidden Mirror Sector Operator (Anima Component). -/
  AnimaOperator : Module.End R M
  
  /-- Witness that the Krein framework is structurally sound (is an involution). -/
  krein_is_symmetry : IsKreinSymmetry KreinSymmetry
  
  /-- Witness that the local physical generator acts as a vortex anomaly (is odd). -/
  ego_is_odd : IsOddOperator KreinSymmetry EgoOperator
  
  /-- The Spinning Instability Trigger (The Non-Zero Commutation Supertrace). -/
  spinning_instability : supertrace KreinSymmetry (EgoOperator * AnimaOperator - AnimaOperator * EgoOperator) ≠ 0

/-- Standard validation lemma confirming that any valid Tomita packet guarantees 
    non-trivial separation of the spatial algebra sheets. -/
lemma validate_packet_separation (P : TomitaModularSeparationPacket R M) :
    P.KreinSymmetry ≠ 1 ∧ P.KreinSymmetry ≠ -1 := by
  have h := modular_phase_separation P.KreinSymmetry P.EgoOperator P.AnimaOperator P.ego_is_odd P.spinning_instability
  exact ⟨h.1, h.2.1⟩

end InfoGeometry.GrandUnification.ModularPhaseSeparation
