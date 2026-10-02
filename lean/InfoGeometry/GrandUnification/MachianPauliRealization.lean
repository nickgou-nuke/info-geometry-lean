import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.GrandUnification.MachianPhaseSeparation

namespace InfoGeometry.GrandUnification.PauliRealization

open InfoGeometry.GrandUnification.MachianPhaseSeparation
open LinearMap

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

class PauliAlgebra (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  σ₁ : Module.End R M
  σ₂ : Module.End R M
  σ₃ : Module.End R M
  anti_comm_13 : σ₃ * σ₁ = - (σ₁ * σ₃)
  anti_comm_23 : σ₃ * σ₂ = - (σ₂ * σ₃)
  commutator_12 : σ₁ * σ₂ - σ₂ * σ₁ = (2 : R) • σ₃
  trace_identity : supertrace σ₃ σ₃ ≠ 0

theorem pauli_realizes_machian_phase_separation
    [PauliAlgebra R M] : MachianPhaseSeparationTarget R M := by
  let Γ := PauliAlgebra.σ₃ (R := R) (M := M)
  let A := PauliAlgebra.σ₁ (R := R) (M := M)
  let B := PauliAlgebra.σ₂ (R := R) (M := M)
  
  have hA_odd : IsOddOperator Γ A := PauliAlgebra.anti_comm_13
  
  have h_spinning : supertrace Γ (A * B - B * A) ≠ 0 := by
    have h_comm : A * B - B * A = (2 : R) • Γ := PauliAlgebra.commutator_12
    rw [h_comm]
    have h_str : supertrace Γ ((2 : R) • Γ) = (2 : R) * supertrace Γ Γ := by
      unfold supertrace
      rw [LinearMap.map_smul, smul_eq_mul]
    rw [h_str]
    intro h_zero
    have h_trace_neq := PauliAlgebra.trace_identity (R := R) (M := M)
    have h_inv : ⅟(2 : R) * ((2 : R) * supertrace Γ Γ) = 0 := by rw [h_zero, mul_zero]
    rw [← mul_assoc, invOf_mul_self, one_mul] at h_inv
    exact h_trace_neq h_inv
    
  exact constructMachianPhaseSeparationTarget {
    ChiralGrading := Γ
    VortexA := A
    VortexB := B
    vortexA_odd := hA_odd
    spinning_instability := h_spinning
  }

end InfoGeometry.GrandUnification.PauliRealization
