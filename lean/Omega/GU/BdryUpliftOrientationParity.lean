/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.GU.BdryZ2JumpUniqueness
import Mathlib.Tactic

namespace Omega.GU

/-- The `ℤ₂`-valued orientation parity carried by a `k`-sheet boundary uplift delta-set. -/
abbrev UpliftOrientationParity (k : ℕ) := Equiv.Perm (Fin k) →* ℤˣ

/-- The canonical uplift orientation parity is the sign character. -/
noncomputable def upliftOrientationParity (k : ℕ) : UpliftOrientationParity k := signHom k

/-- Relabeling a finite delta-set only conjugates the symmetric-group action, so the orientation
parity is invariant. -/
theorem upliftOrientationParity_relabel (k : ℕ) (τ σ : Equiv.Perm (Fin k)) :
    upliftOrientationParity k (τ * σ * τ⁻¹) = upliftOrientationParity k σ := by
  change signHom k (τ * σ * τ⁻¹) = signHom k σ
  rw [map_mul, map_mul, map_inv]
  calc
    signHom k τ * signHom k σ * (signHom k τ)⁻¹ =
        signHom k σ * (signHom k τ * (signHom k τ)⁻¹) := by ac_rfl
    _ = signHom k σ := by simp

/-- On a two-sheet uplift fiber, the nontrivial parity is the swap parity. -/
theorem upliftOrientationParity_two_swap :
    upliftOrientationParity 2 (Equiv.swap 0 1) = -1 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simpa [upliftOrientationParity, signHom] using
    Equiv.Perm.sign_swap h01

/-- For three sheets, every nontrivial binary jump object agrees with the orientation parity. -/
theorem upliftOrientationParity_three_unique
    (φ : Equiv.Perm (Fin 3) →* ℤˣ) (hφ : φ ≠ 1) :
    φ = upliftOrientationParity 3 := by
  rcases paper_bdry_binary_jump_orientation_functor_uniqueness 3 (by decide) φ with hφtriv | hφsign
  · exact (hφ hφtriv).elim
  · simpa [upliftOrientationParity, signHom] using hφsign

/-- Paper-facing corollary: uplift parity is the orientation torsor, functorial under relabeling,
coincides with the unique nontrivial two-sheet parity, and is the unique nontrivial three-sheet
binary jump object.
    cor:bdry-uplift-orientation-parity -/
theorem paper_bdry_uplift_orientation_parity :
    (∀ k : ℕ, ∀ τ σ : Equiv.Perm (Fin k),
      upliftOrientationParity k (τ * σ * τ⁻¹) = upliftOrientationParity k σ) ∧
    upliftOrientationParity 2 (Equiv.swap 0 1) = -1 ∧
    (∀ φ : Equiv.Perm (Fin 3) →* ℤˣ, φ ≠ 1 → φ = upliftOrientationParity 3) := by
  refine ⟨?_, ?_⟩
  · intro k τ σ
    exact upliftOrientationParity_relabel k τ σ
  · refine ⟨upliftOrientationParity_two_swap, ?_⟩
    intro φ hφ
    exact upliftOrientationParity_three_unique φ hφ

end Omega.GU
