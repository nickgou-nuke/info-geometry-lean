import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace InfoGeometry.GrandUnification.MachianPhaseSeparation

open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

noncomputable def supertrace (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

def IsOddOperator (Γ A : Module.End R M) : Prop :=
  Γ * A = - (A * Γ)

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

theorem phase_separation_of_spinning_instability
    (Γ A B : Module.End R M)
    (h_odd_A : IsOddOperator Γ A)
    (h_anomaly : supertrace Γ (A * B - B * A) ≠ 0) :
    Γ ≠ 1 ∧ Γ ≠ -1 := by
  constructor
  · intro h_one
    have hA_zero := odd_operator_zero_of_grading_one Γ A h_odd_A h_one
    rw [hA_zero, zero_mul, mul_zero, sub_zero] at h_anomaly
    have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
      unfold supertrace
      rw [mul_zero, map_zero]
    exact h_anomaly h_str_zero
  · intro h_neg_one
    have hA_zero := odd_operator_zero_of_grading_neg_one Γ A h_odd_A h_neg_one
    rw [hA_zero, zero_mul, mul_zero, sub_zero] at h_anomaly
    have h_str_zero : supertrace Γ (0 : Module.End R M) = 0 := by
      unfold supertrace
      rw [mul_zero, map_zero]
    exact h_anomaly h_str_zero

structure MachianPhaseSeparationPacket (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] where
  ChiralGrading : Module.End R M
  VortexA : Module.End R M
  VortexB : Module.End R M
  vortexA_odd : IsOddOperator ChiralGrading VortexA
  spinning_instability : supertrace ChiralGrading (VortexA * VortexB - VortexB * VortexA) ≠ 0
  machian_equivalence_witness : 
    ChiralGrading ≠ 1 ∧ ChiralGrading ≠ -1 := 
      phase_separation_of_spinning_instability ChiralGrading VortexA VortexB vortexA_odd spinning_instability

def MachianPhaseSeparationTarget (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] : Prop :=
  Nonempty (MachianPhaseSeparationPacket R M)

theorem constructMachianPhaseSeparationTarget
    (P : MachianPhaseSeparationPacket R M) :
    MachianPhaseSeparationTarget R M := 
  ⟨P⟩

end InfoGeometry.GrandUnification.MachianPhaseSeparation
