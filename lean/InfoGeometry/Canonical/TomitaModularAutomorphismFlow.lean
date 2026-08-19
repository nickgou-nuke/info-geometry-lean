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
4. The explicit state-invariance contract for modular states.
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

/-- The modular flow has an explicit inverse at every time. -/
theorem modularFlow_neg_left (MUG : ModularUnitaryGroup H) (t : ℝ)
    (A : H →L[ℂ] H) :
    modularFlow MUG (-t) (modularFlow MUG t A) = A := by
  have h := modularFlow_add MUG (-t) t A
  have hzero : -t + t = 0 := by ring
  rw [hzero] at h
  exact h.symm.trans (modularFlow_zero MUG A)

/-- The inverse identity also holds with the two time directions exchanged. -/
theorem modularFlow_neg_right (MUG : ModularUnitaryGroup H) (t : ℝ)
    (A : H →L[ℂ] H) :
    modularFlow MUG t (modularFlow MUG (-t) A) = A := by
  have h := modularFlow_add MUG t (-t) A
  have hzero : t + -t = 0 := by ring
  rw [hzero] at h
  exact h.symm.trans (modularFlow_zero MUG A)

/-- Conjugation transports the operator norm pointwise along the unitary orbit. -/
theorem modularFlow_apply_unitary_norm (MUG : ModularUnitaryGroup H) (t : ℝ)
    (A : H →L[ℂ] H) (x : H) :
    ‖modularFlow MUG t A (MUG.U t x)‖ = ‖A x‖ := by
  dsimp [modularFlow]
  rw [MUG.inv_cancel t]
  exact (MUG.U t).norm_map _

/-- The product compatibility of modular conjugation.

This identity is valid for every functional `omega`; by itself it is not a
state-invariance theorem.  State invariance is recorded separately below as
an explicit property of the chosen state. -/
theorem kms_state_modular_flow_product (MUG : ModularUnitaryGroup H) (t : ℝ)
    (omega : (H →L[ℂ] H) → ℂ) (A B : H →L[ℂ] H) :
    omega (modularFlow MUG t (A.comp B)) = omega ((modularFlow MUG t A).comp (modularFlow MUG t B)) := by
  rw [modularFlow_mul]

/-- A state together with its modular-flow invariance law.

The invariance law is model data here: an arbitrary functional on bounded
operators is not invariant under conjugation without an additional theorem or
an explicit finite-dimensional trace hypothesis. -/
structure ModularInvariantState (MUG : ModularUnitaryGroup H) where
  omega : (H →L[ℂ] H) → ℂ
  invariant : ∀ t : ℝ, ∀ A : H →L[ℂ] H,
    omega (modularFlow MUG t A) = omega A

/-- The state readout is constant along the supplied modular flow. -/
theorem modularFlow_state_invariant
    (MUG : ModularUnitaryGroup H)
    (S : ModularInvariantState MUG)
    (t : ℝ) (A : H →L[ℂ] H) :
    S.omega (modularFlow MUG t A) = S.omega A := by
  exact S.invariant t A

/-- Invariance also applies to products of observables. -/
theorem modularFlow_product_state_invariant
    (MUG : ModularUnitaryGroup H)
    (S : ModularInvariantState MUG)
    (t : ℝ) (A B : H →L[ℂ] H) :
    S.omega (modularFlow MUG t (A.comp B)) = S.omega (A.comp B) := by
  exact S.invariant t (A.comp B)

end InfoGeometry.Canonical.TomitaModularAutomorphismFlow
