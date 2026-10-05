import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.GrandUnification.ModularPhaseSeparation

namespace InfoGeometry.GrandUnification.PauliRealization

open InfoGeometry.GrandUnification.ModularPhaseSeparation
open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

theorem pauli_commutator_forces_nontrivial_grading
    (σ₁ σ₂ σ₃ : Module.End R M)
    (h_odd : σ₃ * σ₁ = -(σ₁ * σ₃))
    (h_comm : σ₁ * σ₂ - σ₂ * σ₁ = (2 : R) • σ₃)
    (h_trace : supertrace σ₃ σ₃ ≠ 0) :
    σ₃ ≠ 1 ∧ σ₃ ≠ -1 := by
  have hA_odd : IsOddOperator σ₃ σ₁ := h_odd
  have h_spinning : supertrace σ₃ (σ₁ * σ₂ - σ₂ * σ₁) ≠ 0 := by
    rw [h_comm]
    have h_str : supertrace σ₃ ((2 : R) • σ₃) = (2 : R) * supertrace σ₃ σ₃ := by
      unfold supertrace
      rw [Algebra.mul_smul_comm]
      rw [LinearMap.map_smul, smul_eq_mul]
    rw [h_str]
    intro h_zero
    have h_inv : ⅟(2 : R) * ((2 : R) * supertrace σ₃ σ₃) = 0 := by rw [h_zero, mul_zero]
    rw [← mul_assoc, invOf_mul_self, one_mul] at h_inv
    exact h_trace h_inv
  have h_separated := modular_phase_separation σ₃ σ₁ σ₂ hA_odd h_spinning
  exact ⟨h_separated.1, h_separated.2.1⟩

end InfoGeometry.GrandUnification.PauliRealization
