/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.QuantumAffineFlagClusterPoset

/-!
# Self-adjoint completion of one-sided partial-flag inclusion

For arbitrary idempotents, one-sided absorption does not imply its reverse.
When both idempotents are self-adjoint, the star anti-homomorphism supplies
the missing absorption equation, allowing the existing two-sided flag-corner
theorem to apply.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section SelfAdjointFlag

variable {B : Type*} [Ring B] [StarRing B]

/-- Self-adjointness turns the one-sided absorption `P₂ * P₁ = P₁` into
the reverse absorption needed for a nested partial flag. -/
theorem one_sided_absorption_of_selfAdjoint_is_two_sided
    (P₁ P₂ : B) (h₁ : star P₁ = P₁) (h₂ : star P₂ = P₂)
    (h₂₁ : P₂ * P₁ = P₁) : P₁ * P₂ = P₁ := by
  calc
    P₁ * P₂ = star (P₂ * P₁) := by simp [h₁, h₂]
    _ = star P₁ := congrArg star h₂₁
    _ = P₁ := h₁

/-- With self-adjoint nested idempotents, the relative stratum is an
idempotent and the partial-flag corner has the existing top-corner formula.
The one-sided absorption hypothesis is sufficient here because self-adjointness
proves its converse in `one_sided_absorption_of_selfAdjoint_is_two_sided`. -/
theorem selfAdjoint_partial_flag_corner_embedding
    {P₁ P₂ : B} (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁star : star P₁ = P₁) (h₂star : star P₂ = P₂)
    (h₂₁ : P₂ * P₁ = P₁) (A : B) :
    flagStratumIdem P₁ P₂ * flagStratumIdem P₁ P₂ = flagStratumIdem P₁ P₂ ∧
    flagEmbeddedCorner P₁ P₂ A = conePlus P₂ (P₁ * A) := by
  have h₁₂ : P₁ * P₂ = P₁ :=
    one_sided_absorption_of_selfAdjoint_is_two_sided P₁ P₂ h₁star h₂star h₂₁
  rcases partial_flag_to_grassmannian_embedding h₁ h₂ h₁₂ h₂₁ A with
    ⟨hStratum, _, _, _, _, _, _, hCorner⟩
  exact ⟨hStratum, hCorner⟩

end SelfAdjointFlag

end InfoGeometry.OperatorAlgebra.PeirceSpine
