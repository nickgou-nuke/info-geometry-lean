import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Properties

Native Lean 4 counterpart of the elementary property interface used by the
legacy spectral sources.  A property is represented by a `Set`, so membership,
inclusion, and extensionality use Lean's ordinary propositional equality.

This file intentionally does not reproduce the old HoTT-specific `Prop` and
univalence infrastructure.
-/

namespace InfoGeometry.Spectral

universe u

/-- A property of `X`, represented as a predicate. -/
abbrev Property (X : Type u) := Set X

namespace Property

variable {X : Type u} {P Q R : Property X}

@[simp] theorem mem_def (x : X) (P : Property X) : x ∈ P ↔ P x :=
  Iff.rfl

theorem ext (h : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q := by
  ext x
  exact h x

theorem subset_refl (P : Property X) : P ⊆ P := by
  intro x hx
  exact hx

theorem subset_trans (hPQ : P ⊆ Q) (hQR : Q ⊆ R) : P ⊆ R := by
  intro x hx
  exact hQR (hPQ hx)

theorem subset_antisymm (hPQ : P ⊆ Q) (hQP : Q ⊆ P) : P = Q := by
  apply ext
  intro x
  exact ⟨fun hx => hPQ hx, fun hx => hQP hx⟩

end Property

end InfoGeometry.Spectral
