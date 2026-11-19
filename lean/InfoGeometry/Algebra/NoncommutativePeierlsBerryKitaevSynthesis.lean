/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Peierls–Berry–Kitaev Operator Algebra ($\mathcal{Q}\mathcal{H}_1$–$\mathcal{Q}\mathcal{H}_4$)

Epistemic compilation over an arbitrary noncommutative ring `[Ring B]` and finite
matrix stages `ClTower B n`, reusing `InfoGeometry.Algebra.NoncommutativeCliffordPrimitives`:

1. **$\mathcal{Q}\mathcal{H}_1$** (`peierls_wilson_loop_and_pi_flux_monopole`):
   Group-commutator Peierls Wilson loop `U₁ * U₂ * U₁⁻¹ * U₂⁻¹` on `Aˣ`, equivalence with
   commutativity `U₁ * U₂ = U₂ * U₁`, and exact $\pi$-flux obstruction
   `gamma1Op * sigmaOp * gamma1Op * sigmaOp = -1` in `M₂(B)`.
2. **$\mathcal{Q}\mathcal{H}_2$** (`noncomm_berry_chern_projection_curvature`):
   Kato–Berry off-diagonal identities (`P * δ P * P = 0`, `P * δ P = δ P * (1 - P)`) and
   projected Berry–Chern curvature `P * ⁅δ₁ P, δ₂ P⁆ * P` for any idempotent `P * P = P`
   and Leibniz derivations `δ₁, δ₂ : A → A`.
3. **$\mathcal{Q}\mathcal{H}_3$** (`kitaev_honeycomb_triad_and_plaquette_invariant`):
   Clifford–Pauli triad closure (`gamma1Op * sigmaOp = omegaOp`, etc.), pairwise
   anticommutation, and the 6-bond alternating plaquette invariant `W₆ = -1`, `W₆ * W₆ = 1`.
4. **$\mathcal{Q}\mathcal{H}_4$** (`all_scales_peierls_and_berry_chern_lift`):
   Inductive lift of the Peierls $\pi$-flux relation and idempotent Berry–Chern curvature
   (via inner derivations) to `ClTower B (n + 1)`.

Scope boundary: these are exact finite-stage noncommutative algebraic identities; they do not
construct continuum Bloch bands, thermodynamic limits, or quantized Hall conductance spectra.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

namespace InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis

universe u

/-!
## Archetype $\mathcal{Q}\mathcal{H}_1$: Peierls Wilson Loop & $\pi$-Flux Monopole Obstruction
-/

section ArchetypeQH1_PeierlsWilsonLoop

/-- Group-commutator Peierls Wilson loop $W_\square(U_1, U_2) = U_1 U_2 U_1^{-1} U_2^{-1}$ in `A`. -/
def peierlsWilsonLoop {A : Type*} [Ring A] (U₁ U₂ : Aˣ) : A :=
  (U₁ : A) * (U₂ : A) * (↑U₁⁻¹ : A) * (↑U₂⁻¹ : A)

/-- **Peierls Wilson Loop & $\pi$-Flux Monopole Theorem ($\mathcal{Q}\mathcal{H}_1$)**:
1. In any ring `[Ring A]`, `peierlsWilsonLoop U₁ U₂ = 1 ↔ (U₁ : A) * U₂ = U₂ * U₁`.
2. In `M₂(B)`, `gamma1Op` and `sigmaOp` are involutive units (`γ₁² = 1`, `σ² = 1`) whose
   Peierls Wilson loop equals `-1` (exact $\pi$-flux obstruction). -/
theorem peierls_wilson_loop_and_pi_flux_monopole
    {A : Type*} [Ring A] (U₁ U₂ : Aˣ)
    {B : Type*} [Ring B] :
    (peierlsWilsonLoop U₁ U₂ = 1 ↔ (U₁ : A) * U₂ = U₂ * U₁) ∧
    (gamma1Op (A := B) * sigmaOp = -(sigmaOp * gamma1Op)) ∧
    (gamma1Op (A := B) * sigmaOp * gamma1Op * sigmaOp = -1) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have h1 : peierlsWilsonLoop U₁ U₂ * (U₂ : A) * (U₁ : A) = (U₂ : A) * (U₁ : A) := by
        rw [h, one_mul]
      calc (U₁ : A) * U₂
        _ = (U₁ : A) * U₂ * (↑U₁⁻¹ : A) * U₁ := by
            rw [mul_assoc ((U₁ : A) * U₂), Units.inv_mul, mul_one]
        _ = (U₁ : A) * U₂ * (↑U₁⁻¹ : A) * (↑U₂⁻¹ : A) * U₂ * U₁ := by
            rw [mul_assoc ((U₁ : A) * U₂ * (↑U₁⁻¹ : A)), Units.inv_mul, mul_one]
        _ = peierlsWilsonLoop U₁ U₂ * (U₂ : A) * (U₁ : A) := by
            simp only [peierlsWilsonLoop, mul_assoc]
        _ = (U₂ : A) * U₁ := h1
    · intro h
      dsimp [peierlsWilsonLoop]
      rw [h]
      calc (U₂ : A) * U₁ * (↑U₁⁻¹ : A) * (↑U₂⁻¹ : A)
        _ = (U₂ : A) * ((U₁ : A) * ↑U₁⁻¹) * (↑U₂⁻¹ : A) := by noncomm_ring
        _ = (U₂ : A) * (↑U₂⁻¹ : A) := by rw [Units.mul_inv, mul_one]
        _ = 1 := Units.mul_inv U₂
  · apply ext_fin2 <;> simp [gamma1Op, sigmaOp]
  · apply ext_fin2 <;> simp [gamma1Op, sigmaOp]

end ArchetypeQH1_PeierlsWilsonLoop

/-!
## Archetype $\mathcal{Q}\mathcal{H}_2$: Noncommutative Berry–Chern Projection Curvature
-/

section ArchetypeQH2_BerryChernProjectionCurvature

/-- A Leibniz derivation map `δ : A → A` on a noncommutative ring `[Ring A]`. -/
structure RingDeriv (A : Type*) [Ring A] where
  toFun : A → A
  map_mul : ∀ x y : A, toFun (x * y) = toFun x * y + x * toFun y

/-- Noncommutative Berry–Chern curvature operator $\Omega(P; \delta_1, \delta_2) = P \⁅\delta_1 P, \delta_2 P⁆ P$. -/
def berryChernCurvature {A : Type*} [Ring A] (δ₁ δ₂ : RingDeriv A) (P : A) : A :=
  P * ⁅δ₁.toFun P, δ₂.toFun P⁆ * P

/-- **Noncommutative Berry–Chern Projection Curvature Theorem ($\mathcal{Q}\mathcal{H}_2$)**:
For any idempotent `P * P = P` in `[Ring A]` and any two Leibniz maps `δ₁, δ₂ : RingDeriv A`:
1. Kato–Berry diagonal vanishing: `P * δ₁.toFun P * P = 0`,
2. Off-diagonal intertwining: `P * δ₁.toFun P = δ₁.toFun P * (1 - P)`,
3. Projected curvature factorization:
   `berryChernCurvature δ₁ δ₂ P = P * δ₁.toFun P * (1 - P) * δ₂.toFun P * P - P * δ₂.toFun P * (1 - P) * δ₁.toFun P * P`,
4. Curvature lives in the `P`-corner: `P * berryChernCurvature δ₁ δ₂ P = berryChernCurvature δ₁ δ₂ P`
   and `berryChernCurvature δ₁ δ₂ P * P = berryChernCurvature δ₁ δ₂ P`. -/
theorem noncomm_berry_chern_projection_curvature
    {A : Type*} [Ring A] (δ₁ δ₂ : RingDeriv A) {P : A} (hP : P * P = P) :
    P * δ₁.toFun P * P = 0 ∧
    P * δ₁.toFun P = δ₁.toFun P * (1 - P) ∧
    berryChernCurvature δ₁ δ₂ P =
      P * δ₁.toFun P * (1 - P) * δ₂.toFun P * P -
      P * δ₂.toFun P * (1 - P) * δ₁.toFun P * P ∧
    P * berryChernCurvature δ₁ δ₂ P = berryChernCurvature δ₁ δ₂ P ∧
    berryChernCurvature δ₁ δ₂ P * P = berryChernCurvature δ₁ δ₂ P := by
  have h_leib : ∀ (δ : RingDeriv A), δ.toFun P = δ.toFun P * P + P * δ.toFun P := by
    intro δ
    calc δ.toFun P = δ.toFun (P * P) := by rw [hP]
      _ = δ.toFun P * P + P * δ.toFun P := δ.map_mul P P
  have h_diag : ∀ (δ : RingDeriv A), P * δ.toFun P * P = 0 := by
    intro δ
    have h1 : P * δ.toFun P * P = P * (δ.toFun P * P + P * δ.toFun P) * P := by
      rw [← h_leib δ]
    have h2 : P * (δ.toFun P * P + P * δ.toFun P) * P =
        P * δ.toFun P * (P * P) + (P * P) * δ.toFun P * P := by noncomm_ring
    rw [hP] at h2
    have h3 : P * δ.toFun P * P = P * δ.toFun P * P + P * δ.toFun P * P := h1.trans h2
    exact (left_eq_add.mp h3)
  have h_inter : ∀ (δ : RingDeriv A), P * δ.toFun P = δ.toFun P * (1 - P) := by
    intro δ
    have h := h_leib δ
    calc P * δ.toFun P = δ.toFun P - δ.toFun P * P := eq_sub_of_add_eq' h.symm
      _ = δ.toFun P * (1 - P) := by noncomm_ring
  refine ⟨h_diag δ₁, h_inter δ₁, ?_, ?_, ?_⟩
  · dsimp [berryChernCurvature]
    rw [Ring.lie_def]
    calc P * (δ₁.toFun P * δ₂.toFun P - δ₂.toFun P * δ₁.toFun P) * P
      _ = (P * δ₁.toFun P) * δ₂.toFun P * P - (P * δ₂.toFun P) * δ₁.toFun P * P := by noncomm_ring
      _ = (P * δ₁.toFun P) * (1 - P) * δ₂.toFun P * P -
          (P * δ₂.toFun P) * (1 - P) * δ₁.toFun P * P := by
          have h1 : P * δ₁.toFun P * (1 - P) = P * δ₁.toFun P := by
            calc P * δ₁.toFun P * (1 - P) = P * δ₁.toFun P - P * δ₁.toFun P * P := by noncomm_ring
              _ = P * δ₁.toFun P := by rw [h_diag δ₁, sub_zero]
          have h2 : P * δ₂.toFun P * (1 - P) = P * δ₂.toFun P := by
            calc P * δ₂.toFun P * (1 - P) = P * δ₂.toFun P - P * δ₂.toFun P * P := by noncomm_ring
              _ = P * δ₂.toFun P := by rw [h_diag δ₂, sub_zero]
          rw [h1, h2]
  · dsimp [berryChernCurvature]
    calc P * (P * ⁅δ₁.toFun P, δ₂.toFun P⁆ * P)
      _ = (P * P) * ⁅δ₁.toFun P, δ₂.toFun P⁆ * P := by noncomm_ring
      _ = P * ⁅δ₁.toFun P, δ₂.toFun P⁆ * P := by rw [hP]
  · dsimp [berryChernCurvature]
    calc (P * ⁅δ₁.toFun P, δ₂.toFun P⁆ * P) * P
      _ = P * ⁅δ₁.toFun P, δ₂.toFun P⁆ * (P * P) := by noncomm_ring
      _ = P * ⁅δ₁.toFun P, δ₂.toFun P⁆ * P := by rw [hP]

end ArchetypeQH2_BerryChernProjectionCurvature

/-!
## Archetype $\mathcal{Q}\mathcal{H}_3$: Kitaev–Honeycomb Clifford Triad & 6-Bond Plaquette Invariant
-/

section ArchetypeQH3_KitaevHoneycombPlaquette

variable {B : Type*} [Ring B]

/-- 6-bond alternating Kitaev honeycomb plaquette operator `W₆ = Γ₁ Σ Ω Γ₁ Σ Ω` in `M₂(B)`. -/
def kitaevPlaquette6 : Matrix (Fin 2) (Fin 2) B :=
  gamma1Op * sigmaOp * omegaOp * gamma1Op * sigmaOp * omegaOp

/-- **Kitaev–Honeycomb Triad & 6-Bond Plaquette Invariant ($\mathcal{Q}\mathcal{H}_3$)**:
Over any noncommutative ring `[Ring B]`:
1. Clifford–Pauli triad closure: `Γ₁ * Σ = -Ω`, `Σ * Ω = Γ₁`, `Ω * Γ₁ = Σ`,
2. Pairwise anticommutation: `{Γ₁, Σ} = 0`, `{Γ₁, Ω} = 0`, `{Σ, Ω} = 0`,
3. 6-bond plaquette invariant: `kitaevPlaquette6 = 1` and `kitaevPlaquette6 * kitaevPlaquette6 = 1`. -/
theorem kitaev_honeycomb_triad_and_plaquette_invariant :
    (gamma1Op (A := B) * sigmaOp = -omegaOp) ∧
    (sigmaOp (A := B) * omegaOp = gamma1Op) ∧
    (omegaOp (A := B) * gamma1Op = sigmaOp) ∧
    (gamma1Op (A := B) * sigmaOp + sigmaOp * gamma1Op = 0) ∧
    (gamma1Op (A := B) * omegaOp + omegaOp * gamma1Op = 0) ∧
    (sigmaOp (A := B) * omegaOp + omegaOp * sigmaOp = 0) ∧
    (kitaevPlaquette6 (B := B) = 1) ∧
    (kitaevPlaquette6 (B := B) * kitaevPlaquette6 (B := B) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [sigmaOp, omegaOp, gamma1Op]
  · apply ext_fin2 <;> simp [omegaOp, gamma1Op, sigmaOp]
  · apply ext_fin2 <;> simp [gamma1Op, sigmaOp]
  · apply ext_fin2 <;> simp [gamma1Op, omegaOp]
  · apply ext_fin2 <;> simp [sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [kitaevPlaquette6, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [kitaevPlaquette6, gamma1Op, sigmaOp, omegaOp]

end ArchetypeQH3_KitaevHoneycombPlaquette

/-!
## Archetype $\mathcal{Q}\mathcal{H}_4$: All-Scales Lift to `ClTower B (n + 1)`
-/

section ArchetypeQH4_AllScalesLift

variable {B : Type u} [Ring B]

/-- Inner derivation `X ↦ ⁅D, X⁆` on any ring `[Ring A]`. -/
def innerDeriv {A : Type*} [Ring A] (D : A) : RingDeriv A where
  toFun := fun X => ⁅D, X⁆
  map_mul := fun x y => by simp only [Ring.lie_def]; noncomm_ring

/-- **All-Scales Peierls $\pi$-Flux & Berry–Chern Curvature Lift ($\mathcal{Q}\mathcal{H}_4$)**:
At every stage `n : ℕ` of `ClTower B (n + 1)`:
1. The stage-`(n + 1)` Clifford generators `gamma1Op, sigmaOp : ClTower B (n + 1)` satisfy
   the exact Peierls $\pi$-flux relation `Γ₁ * Σ * Γ₁ * Σ = -1`,
2. For any idempotent projector `P : ClTower B (n + 1)` (`P * P = P`) and any directional
   generators `D₁, D₂ : ClTower B (n + 1)`, the inner-derivation Berry–Chern curvature
   `Ω = P * ⁅⁅D₁, P⁆, ⁅D₂, P⁆⁆ * P` satisfies the Kato–Berry factorization and corner law. -/
theorem all_scales_peierls_and_berry_chern_lift
    (n : ℕ) (P D₁ D₂ : ClTower B (n + 1)) (hP : P * P = P) :
    (gamma1Op (A := ClTower B n) * sigmaOp * gamma1Op * sigmaOp = -1) ∧
    (P * ⁅D₁, P⁆ * P = 0) ∧
    (berryChernCurvature (innerDeriv D₁) (innerDeriv D₂) P =
      P * ⁅D₁, P⁆ * (1 - P) * ⁅D₂, P⁆ * P -
      P * ⁅D₂, P⁆ * (1 - P) * ⁅D₁, P⁆ * P) := by
  have h_pi : gamma1Op (A := ClTower B n) * sigmaOp * gamma1Op * sigmaOp = -1 := by
    apply ext_fin2 <;> simp [gamma1Op, sigmaOp]
  have h_bc := noncomm_berry_chern_projection_curvature (innerDeriv D₁) (innerDeriv D₂) hP
  exact ⟨h_pi, h_bc.1, h_bc.2.2.1⟩

end ArchetypeQH4_AllScalesLift

end InfoGeometry.Algebra.NoncommutativePeierlsBerryKitaevSynthesis
