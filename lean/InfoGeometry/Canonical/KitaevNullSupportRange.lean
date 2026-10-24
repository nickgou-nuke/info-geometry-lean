/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevNullSupport

/-! The native active support projects onto the span of its normalized null pair. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevNullSupportRange
open Matrix KitaevNullPartner KitaevNullSupport

theorem active_action_mem_span (z : (Fin 2 × Fin 2) → ℂ) :
    active *ᵥ z ∈ Submodule.span ℂ {seed, partner} := by
  rw [Submodule.mem_span_pair]
  exact ⟨_, _, (active_action z).symm⟩

theorem active_fixed_iff_mem_span (z : (Fin 2 × Fin 2) → ℂ) :
    active *ᵥ z = z ↔ z ∈ Submodule.span ℂ {seed, partner} := by
  constructor
  · intro h
    rw [← h]
    exact active_action_mem_span z
  · intro h
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp h
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul,
      active_fixes_null_pair.1, active_fixes_null_pair.2]

theorem active_range_eq_span :
    Set.range (fun z : (Fin 2 × Fin 2) → ℂ => active *ᵥ z) =
      (Submodule.span ℂ {seed, partner} : Set ((Fin 2 × Fin 2) → ℂ)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact active_action_mem_span x
  · intro h
    exact ⟨z, (active_fixed_iff_mem_span z).2 h⟩

end InfoGeometry.Canonical.KitaevNullSupportRange
