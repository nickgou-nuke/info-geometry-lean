import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import InfoGeometry.GrandUnification.ModularPhaseSeparation

namespace InfoGeometry.GrandUnification.MachianCosmology
open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-! ### Eigenspace carriers for the two grading signs -/

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
      calc (2 : R) • x = x + x := by simpa using two_smul (R:=R) x
                   _ = 0 := h_eq
    calc x = (1 : R) • x := by rw [one_smul]
         _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
         _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
         _ = ⅟(2 : R) • (0 : M) := by rw [h_two]
         _ = 0 := smul_zero _
  · intro h
    have hx : x = (0 : M) := by
      simpa [Submodule.mem_bot] using h
    simpa [hx] using (LinearMap.map_zero (Γ - 1))

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
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add] using h_eq
                   
    have h_two : (2 : R) • x = 0 := by
      have h_sum : x + x = 0 := neg_eq_zero.mp h_add
      calc (2 : R) • x = x + x := by simpa using two_smul (R:=R) x
                   _ = 0 := h_sum
    have hx : x = (0 : M) := by
      calc
        x = (1 : R) • x := by simpa [one_smul]
        _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
        _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
        _ = ⅟(2 : R) • (0 : M) := by rw [h_two]
        _ = 0 := smul_zero _
    simpa [Submodule.mem_bot] using hx
  · intro h
    have hx : x = (0 : M) := by
      simpa [Submodule.mem_bot] using h
    have h_ego : (Γ - 1) x = 0 := by
      simpa [hx] using (LinearMap.map_zero (Γ - 1))
    exact h_ego

/-- Theorem: Ego and Anima eigenspaces are strictly disjoint (Node F). -/
theorem ego_inf_anima_eq_bot (Γ : Module.End R M) : Ego Γ ⊓ Anima Γ = ⊥ := by
  ext x
  constructor
  · intro h
    have h_ego : (Γ - 1) x = 0 := h.1
    have h_anima : (Γ + 1) x = 0 := h.2
    have h_diff : (Γ + 1) x - (Γ - 1) x = 0 := by rw [h_anima, h_ego, sub_zero]
    have h_two : (2 : R) • x = 0 := by
      calc (2 : R) • x = x + x := by simpa using two_smul (R:=R) x
                   _ = Γ x + x - (Γ x - x) := by abel
                   _ = (Γ + 1) x - (Γ - 1) x := rfl
                   _ = 0 := h_diff
    have hx : x = (0 : M) := by
      calc
        x = (1 : R) • x := by rw [one_smul]
        _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
        _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
        _ = ⅟(2 : R) • (0 : M) := by rw [h_two]
        _ = 0 := smul_zero _
    simpa [Submodule.mem_bot] using hx
  · intro h
    have hx : x = (0 : M) := by
      simpa [Submodule.mem_bot] using h
    have h_ego : (Γ - 1) x = 0 := by
      simpa [hx] using (LinearMap.map_zero (Γ - 1))
    have h_anima : (Γ + 1) x = 0 := by
      simpa [hx] using (LinearMap.map_zero (Γ + 1))
    exact ⟨h_ego, h_anima⟩


end InfoGeometry.GrandUnification.MachianCosmology
