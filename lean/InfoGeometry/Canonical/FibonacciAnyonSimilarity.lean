import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic

/-!
# Canonical unit-conjugacy similarity for Fibonacci anyon readouts

This file avoids local relation and trace wrapper definitions.  Similarity is
stated directly as conjugacy by a mathlib unit `Aˣ`, and trace invariance is
stated for an explicit function `τ : A → ℝ` with an explicit cyclicity
hypothesis.

The original involutive-gauge relation `∃ F, F * F = 1 ∧ X = F * Y * F` is not
transitive in an arbitrary noncommutative ring without extra commutation
hypotheses.  The transitive canonical relation is unit conjugacy, used below.
-/

set_option autoImplicit false

namespace FibonacciAnyons.Similarity

variable {A : Type*} [Ring A]

/-- Reflexivity of canonical similarity by conjugation with a unit. -/
theorem similarity_refl (X : A) :
    ∃ u : Aˣ, X = (u : A) * X * ((u⁻¹ : Aˣ) : A) := by
  refine ⟨1, ?_⟩
  simp

/-- Symmetry of canonical similarity by conjugation with a unit. -/
theorem similarity_symm (X Y : A)
    (h : ∃ u : Aˣ, X = (u : A) * Y * ((u⁻¹ : Aˣ) : A)) :
    ∃ u : Aˣ, Y = (u : A) * X * ((u⁻¹ : Aˣ) : A) := by
  rcases h with ⟨u, rfl⟩
  refine ⟨u⁻¹, ?_⟩
  simp [mul_assoc]

/-- Transitivity of canonical similarity by conjugation with units. -/
theorem similarity_trans (X Y Z : A)
    (h1 : ∃ u : Aˣ, X = (u : A) * Y * ((u⁻¹ : Aˣ) : A))
    (h2 : ∃ u : Aˣ, Y = (u : A) * Z * ((u⁻¹ : Aˣ) : A)) :
    ∃ u : Aˣ, X = (u : A) * Z * ((u⁻¹ : Aˣ) : A) := by
  rcases h1 with ⟨u, rfl⟩
  rcases h2 with ⟨v, rfl⟩
  refine ⟨u * v, ?_⟩
  simp [mul_assoc]

/-- A cyclic real-valued trace is invariant under canonical similarity by a unit. -/
theorem trace_similarity_invariant (X Y : A)
    (h : ∃ u : Aˣ, X = (u : A) * Y * ((u⁻¹ : Aˣ) : A))
    (τ : A → ℝ) (h_cyclic : ∀ x y : A, τ (x * y) = τ (y * x)) :
    |τ X| = |τ Y| := by
  rcases h with ⟨u, rfl⟩
  have h_eq : τ ((u : A) * Y * ((u⁻¹ : Aˣ) : A)) = τ Y := by
    calc
      τ ((u : A) * Y * ((u⁻¹ : Aˣ) : A))
          = τ (((u : A) * Y) * ((u⁻¹ : Aˣ) : A)) := by rfl
      _ = τ (((u⁻¹ : Aˣ) : A) * ((u : A) * Y)) := by
            rw [h_cyclic ((u : A) * Y) (((u⁻¹ : Aˣ) : A))]
      _ = τ Y := by simp
  rw [h_eq]

/-- An involutive element `F` gives a unit, hence a canonical similarity witness. -/
theorem braid_generators_similar (B1 B2 F : A)
    (hF : F * F = 1) (h_B2 : B2 = F * B1 * F) :
    ∃ u : Aˣ, B2 = (u : A) * B1 * ((u⁻¹ : Aˣ) : A) := by
  let u : Aˣ :=
    { val := F
      inv := F
      val_inv := hF
      inv_val := hF }
  refine ⟨u, ?_⟩
  simpa [u] using h_B2

end FibonacciAnyons.Similarity
