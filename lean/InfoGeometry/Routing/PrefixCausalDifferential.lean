/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

namespace InfoGeometry.Routing.BlockCausalSinkhorn

open scoped BigOperators
noncomputable section
variable {C : Type*} [LinearOrder C]

/-- A chunked operator `Φ : (C → E) → (C → F)` between normed spaces is block-causal
    if the output at chunk `t` depends only on inputs at chunks `s ≤ t`. -/
def IsBlockCausalOperator {E F : Type*} (Φ : (C → E) → (C → F)) : Prop :=
  ∀ (t : C) (x₁ x₂ : C → E), (∀ s ≤ t, x₁ s = x₂ s) → Φ x₁ t = Φ x₂ t

/-- Any pointwise chunk encoder preserves prefix locality. No continuity or
smoothness of the encoder is needed for independence of future inputs. -/
theorem IsBlockCausalOperator.encode
    {E X F : Type*} {Φ : (C → X) → C → F}
    (hΦ : IsBlockCausalOperator Φ) (encode : C → E → X) :
    IsBlockCausalOperator (fun x t => Φ (fun s => encode s (x s)) t) := by
  intro t x₁ x₂ hpast
  apply hΦ t
  intro s hs
  exact congrArg (encode s) (hpast s hs)

/-- **Zero Future Jacobian & Cotangent Pullback Theorem
    (`blockCausal_future_hasFDerivAt_zero_and_pullback_zero`):**
    For any block-causal operator `Φ : (C → E) → (C → F)` between normed spaces,
    any query chunk `t : C`, any strictly future chunk `s₀ > t`, and any upstream
    cotangent covector `ℓ : F →L[ℝ] ℝ`:
    1. The partial map `v ↦ Φ (Function.update x s₀ v) t` has Fréchet derivative
       identically equal to `0 : E →L[ℝ] F` at `x s₀`.
    2. The backward cotangent pullback `v ↦ ℓ (Φ (Function.update x s₀ v) t)` has
       Fréchet derivative `ℓ.comp 0 = 0 : E →L[ℝ] ℝ` at `x s₀`. -/
theorem blockCausal_future_hasFDerivAt_zero_and_pullback_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : (C → E) → (C → F)} (h_causal : IsBlockCausalOperator Φ)
    (x : C → E) {t s₀ : C} (hts₀ : t < s₀) (ℓ : F →L[ℝ] ℝ) :
    HasFDerivAt (fun v : E => Φ (Function.update x s₀ v) t)
      (0 : E →L[ℝ] F) (x s₀) ∧
    HasFDerivAt (fun v : E => ℓ (Φ (Function.update x s₀ v) t))
      (0 : E →L[ℝ] ℝ) (x s₀) ∧
    ℓ.comp (0 : E →L[ℝ] F) = 0 := by
  have h_const_fn :
      (fun v : E => Φ (Function.update x s₀ v) t) = fun _ : E => Φ x t := by
    ext v
    apply h_causal t (Function.update x s₀ v) x
    intro s hs
    have h_ne : s ≠ s₀ := ne_of_lt (lt_of_le_of_lt hs hts₀)
    simp [Function.update, h_ne]
  have h_fderiv :
      HasFDerivAt (fun v : E => Φ (Function.update x s₀ v) t)
        (0 : E →L[ℝ] F) (x s₀) := by
    rw [h_const_fn]
    exact hasFDerivAt_const (Φ x t) (x s₀)
  have h_pullback :
      HasFDerivAt (fun v : E => ℓ (Φ (Function.update x s₀ v) t))
        (0 : E →L[ℝ] ℝ) (x s₀) := by
    have h_chain := ℓ.hasFDerivAt.comp (x s₀) h_fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero] using h_chain
  exact ⟨h_fderiv, h_pullback, by simp⟩



/-- All future coordinates may vary simultaneously: the whole suffix slice
is constant, not merely each separately tested coordinate. -/
theorem blockCausal_future_suffix_hasFDerivAt_zero
    [Fintype C] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : (C → E) → C → F} (hΦ : IsBlockCausalOperator Φ)
    (x : C → E) (t : C) (z : C → E) :
    HasFDerivAt (fun future : C → E =>
      Φ (fun s => if s ≤ t then x s else future s) t)
      (0 : (C → E) →L[ℝ] F) z := by
  have hc : (fun future : C → E =>
      Φ (fun s => if s ≤ t then x s else future s) t) =
      fun _ : C → E => Φ x t := by
    funext future
    apply hΦ t
    intro s hs
    simp only [if_pos hs]
  rw [hc]
  exact hasFDerivAt_const (Φ x t) z

end
end InfoGeometry.Routing.BlockCausalSinkhorn
