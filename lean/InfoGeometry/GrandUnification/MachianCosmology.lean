import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace InfoGeometry.GrandUnification.MachianCosmology
open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-! ### 1. Core Definitions -/

/-- An operator is defined as 'odd' if it perfectly anti-commutes with the grading Γ. -/
def IsOddOperator (Γ A : Module.End R M) : Prop :=
  Γ * A = - (A * Γ)

/-- The Chiral Supertrace over the fluid endomorphism algebra. -/
noncomputable def supertrace [Module.Free R M] [Module.Finite R M] (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

/-! ### 2. The Triviality Lemmas (Node B) -/

/-- Lemma: In a completely positive space (Γ = 1), odd operators must be identically zero. -/
lemma odd_op_zero_of_grading_one (Γ A : Module.End R M)
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

/-- Lemma: In a completely negative space (Γ = -1), odd operators must be identically zero. -/
lemma odd_op_zero_of_grading_neg_one (Γ A : Module.End R M)
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

/-! ### 3. Machian Phase Separation Theorem (Node D) -/

/-- Theorem: A non-zero local spinning anomaly strictly prohibits a trivial vacuum state,
forcing global chiral phase separation (Γ ≠ 1 ∧ Γ ≠ -1). -/
theorem machian_phase_separation [Module.Free R M] [Module.Finite R M]
    (Γ A B : Module.End R M)
    (h_odd : IsOddOperator Γ A)
    (h_anomaly : supertrace Γ (A * B - B * A) ≠ 0) :
    Γ ≠ 1 ∧ Γ ≠ -1 := by
  constructor
  · intro h_one
    have hA := odd_op_zero_of_grading_one Γ A h_odd h_one
    rw [hA, zero_mul, mul_zero, sub_zero] at h_anomaly
    have h_str : supertrace Γ (0 : Module.End R M) = 0 := by
      unfold supertrace; rw [mul_zero, map_zero]
    exact h_anomaly h_str
  · intro h_neg_one
    have hA := odd_op_zero_of_grading_neg_one Γ A h_odd h_neg_one
    rw [hA, zero_mul, mul_zero, sub_zero] at h_anomaly
    have h_str : supertrace Γ (0 : Module.End R M) = 0 := by
      unfold supertrace; rw [mul_zero, map_zero]
    exact h_anomaly h_str

/-! ### 4. Spacetime Decompositions (Node E & F) -/

/-- The Ego Submodule represents the (+1) chiral eigenspace sheet. -/
def Ego (Γ : Module.End R M) : Submodule R M :=
  LinearMap.ker (Γ - 1)

/-- The Anima Submodule represents the (-1) chiral eigenspace sheet. -/
def Anima (Γ : Module.End R M) : Submodule R M :=
  LinearMap.ker (Γ + 1)

/-- Symmetries force the Anima to collapse to triviality if the grading is frozen at 1. -/
lemma anima_trivial_of_grading_one (Γ : Module.End R M) (h_one : Γ = 1) :
    Anima Γ = ⊥ := by
  ext x
  constructor
  · intro h
    have h_eval : (Γ + 1) x = 0 := h
    have h_eq : Γ x + x = 0 := h_eval
    rw [h_one] at h_eq
    have h_x : (1 : Module.End R M) x = x := rfl
    rw [h_x] at h_eq
    have h_two : (2 : R) • x = 0 := by
      calc (2 : R) • x = x + x := two_smul R x
                   _ = 0 := h_eq
    calc x = (1 : R) • x := by rw [one_smul]
         _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
         _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
         _ = ⅟(2 : R) • (0 : M) := by rw [h_two]
         _ = 0 := smul_zero _
  · intro h
    rw [Submodule.mem_bot.mp h]
    exact map_zero _

/-- Symmetries force the Ego to collapse to triviality if the grading is frozen at -1. -/
lemma ego_trivial_of_grading_neg_one (Γ : Module.End R M) (h_neg_one : Γ = -1) :
    Ego Γ = ⊥ := by
  ext x
  constructor
  · intro h
    have h_eval : (Γ - 1) x = 0 := h
    have h_eq : Γ x - x = 0 := h_eval
    rw [h_neg_one] at h_eq
    have h_neg_x : (-1 : Module.End R M) x = -x := rfl
    rw [h_neg_x] at h_eq
    have h_add : -(x + x) = 0 := by
      calc -(x + x) = -x - x := by ring
                   _ = 0 := h_eq
    have h_two : (2 : R) • x = 0 := by
      have h_sum : x + x = 0 := neg_eq_zero.mp h_add
      calc (2 : R) • x = x + x := two_smul R x
                   _ = 0 := h_sum
    calc x = (1 : R) • x := by rw [one_smul]
         _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
         _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
         _ = ⅟(2 : R) • (0 : M) := by rw [h_two]
         _ = 0 := smul_zero _
  · intro h
    rw [Submodule.mem_bot.mp h]
    exact map_zero _

/-- Theorem: Ego and Anima eigenspaces are strictly disjoint (Node F). -/
theorem ego_inf_anima_eq_bot (Γ : Module.End R M) : Ego Γ ⊓ Anima Γ = ⊥ := by
  ext x
  constructor
  · intro h
    have h_ego : (Γ - 1) x = 0 := h.1
    have h_anima : (Γ + 1) x = 0 := h.2
    have h_diff : (Γ + 1) x - (Γ - 1) x = 0 := by rw [h_anima, h_ego, sub_zero]
    have h_two : (2 : R) • x = 0 := by
      calc (2 : R) • x = x + x := two_smul R x
                   _ = Γ x + x - (Γ x - x) := by abel
                   _ = (Γ + 1) x - (Γ - 1) x := rfl
                   _ = 0 := h_diff
    calc x = (1 : R) • x := by rw [one_smul]
         _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
         _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
         _ = ⅟(2 : R) • (0 : M) := by rw [h_two]
         _ = 0 := smul_zero _
  · intro h
    rw [Submodule.mem_bot.mp h]
    exact Submodule.zero_mem _

end InfoGeometry.GrandUnification.MachianCosmology
