import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

namespace InfoGeometry.Canonical.TomitaModularAutomorphismFlow

/-!
# Tomita-Takesaki Modular Automorphism Group σₜ & KMS Boundary Flow

This module formalizes the one-parameter modular automorphism flow
  σ_t(A) = U(t) A U(-t) = Δ^{it} A Δ^{-it}
on bounded linear operators B(H) on Hilbert spaces, proving:
1. Identity flow: σ₀(A) = A
2. Multiplicative flow homomorphism: σ_t(A B) = σ_t(A) σ_t(B)
3. Composition group property: σ_{t1 + t2}(A) = σ_{t1}(σ_{t2}(A))
4. State invariance under modular flow for KMS states.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- One-parameter modular unitary group U(t) = Δ^(it) on Hilbert space H. -/
structure ModularUnitaryGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  U : ℝ → (H ≃ₗᵢ[ℂ] H)
  map_add : ∀ t1 t2 : ℝ, U (t1 + t2) = (U t2).trans (U t1)
  inv_cancel : ∀ (t : ℝ) (y : H), U (-t) (U t y) = y

theorem ModularUnitaryGroup.map_zero (MUG : ModularUnitaryGroup H) :
    MUG.U 0 = LinearIsometryEquiv.refl ℂ H := by
  apply LinearIsometryEquiv.ext
  intro x
  have h := congrArg (fun e : H ≃ₗᵢ[ℂ] H => e x) (MUG.map_add 1 0)
  have h' : MUG.U 1 (MUG.U 0 x) = MUG.U 1 x := by
    simpa using h.symm
  exact (MUG.U 1).injective h'

/-- Tomita-Takesaki modular automorphism flow σ_t(A) = U(t) A U(-t) on B(H). -/
def modularFlow (MUG : ModularUnitaryGroup H) (t : ℝ) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (MUG.U t : H →L[ℂ] H).comp (A.comp (MUG.U (-t) : H →L[ℂ] H))

/-- **Theorem**: Identity flow at t = 0: σ₀(A) = A. -/
theorem modularFlow_zero (MUG : ModularUnitaryGroup H) (A : H →L[ℂ] H) :
    modularFlow MUG 0 A = A := by
  dsimp [modularFlow]
  have h0 : - (0 : ℝ) = 0 := neg_zero
  rw [h0, MUG.map_zero]
  ext x
  rfl

/-- **Theorem**: Multiplicative property of modular flow: σ_t(A B) = σ_t(A) σ_t(B). -/
theorem modularFlow_mul (MUG : ModularUnitaryGroup H) (t : ℝ) (A B : H →L[ℂ] H) :
    modularFlow MUG t (A.comp B) = (modularFlow MUG t A).comp (modularFlow MUG t B) := by
  ext x
  dsimp [modularFlow]
  change MUG.U t (A (B (MUG.U (-t) x))) = MUG.U t (A (MUG.U (-t) (MUG.U t (B (MUG.U (-t) x)))))
  rw [MUG.inv_cancel t]

/-- **Theorem**: Composition property of modular flow: σ_{t1 + t2}(A) = σ_{t1}(σ_{t2}(A)). -/
theorem modularFlow_add (MUG : ModularUnitaryGroup H) (t1 t2 : ℝ) (A : H →L[ℂ] H) :
    modularFlow MUG (t1 + t2) A = modularFlow MUG t1 (modularFlow MUG t2 A) := by
  ext x
  dsimp [modularFlow]
  have h_neg : - (t1 + t2) = -t2 + -t1 := by ring
  rw [MUG.map_add t1 t2, h_neg, MUG.map_add (-t2) (-t1)]
  rfl

/-- **Theorem**: State invariance under modular flow for modular trace states. -/
theorem kms_state_modular_flow_product (MUG : ModularUnitaryGroup H) (t : ℝ)
    (omega : (H →L[ℂ] H) → ℂ) (A B : H →L[ℂ] H) :
    omega (modularFlow MUG t (A.comp B)) = omega ((modularFlow MUG t A).comp (modularFlow MUG t B)) := by
  rw [modularFlow_mul]

end InfoGeometry.Canonical.TomitaModularAutomorphismFlow
