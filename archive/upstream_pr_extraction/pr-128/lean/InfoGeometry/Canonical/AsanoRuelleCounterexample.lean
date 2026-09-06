import Mathlib.Tactic

/-!
# Asano--Ruelle contraction: counterexample to the unrestricted statement

The unrestricted statement

  zero-free off `K₁ × K₂`
    ⇒
  contracted polynomial zero-free off `-(K₁K₂)`

is false for arbitrary subsets `K₁ K₂ : Set ℂ`.

This file gives a nondegenerate counterexample.
No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.AsanoRuelleCounterexample

open Set

/--
The two-variable polynomial

  Φ(z₁,z₂) = z₁ z₂ - 1.

This is separately affine with

  A = -1, B = 0, C = 0, D = 1,

so `D ≠ 0` and `AD - BC = -1 ≠ 0`.
-/
def Phi (z₁ z₂ : ℂ) : ℂ :=
  z₁ * z₂ - 1

/--
The Asano contraction of `Phi`:

  Q(z) = A + D z = -1 + z.
-/
def Q (z : ℂ) : ℂ :=
  -1 + z

/--
Bad forbidden set in the first variable:

  K₁ = ℂ \ {0}.

Its complement is `{0}`. This set is not closed, which is exactly why the
unrestricted theorem fails.
-/
def K₁ : Set ℂ :=
  {z | z ≠ 0}

/-- Empty forbidden set in the second variable. -/
def K₂ : Set ℂ :=
  ∅

/-- Forbidden product set `-(K₁K₂)`. -/
def forbiddenProduct : Set ℂ :=
  {z | ∃ u ∈ K₁, ∃ v ∈ K₂, z = -(u * v)}

/--
`Phi` is zero-free whenever `z₁ ∉ K₁` and `z₂ ∉ K₂`.
-/
theorem Phi_zero_free_off_K₁_K₂ :
    ∀ z₁ z₂ : ℂ,
      z₁ ∉ K₁ →
      z₂ ∉ K₂ →
      Phi z₁ z₂ ≠ 0 := by
  intro z₁ z₂ hz₁ _hz₂
  have hz₁zero : z₁ = 0 := by
    by_contra h
    exact hz₁ h
  unfold Phi
  rw [hz₁zero]
  norm_num

/-- The contracted polynomial has a zero at `z = 1`. -/
theorem Q_one_eq_zero :
    Q 1 = 0 := by
  unfold Q
  norm_num

/-- `1` is not in the forbidden product set, because `K₂` is empty. -/
theorem one_not_mem_forbiddenProduct :
    (1 : ℂ) ∉ forbiddenProduct := by
  intro h
  rcases h with ⟨u, hu, v, hv, hz⟩
  simpa [K₂] using hv

/--
The example is genuinely nondegenerate:

  D = 1 ≠ 0,
  AD - BC = (-1)*1 - 0*0 = -1 ≠ 0.
-/
theorem nondegenerate_coefficients :
    (1 : ℂ) ≠ 0 ∧ ((-1 : ℂ) * 1 - 0 * 0) ≠ 0 := by
  constructor <;> norm_num

/--
Counterexample to the unrestricted Asano--Ruelle contraction statement.
-/
theorem unrestricted_AsanoRuelle_contraction_statement_false :
    (∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        Phi z₁ z₂ ≠ 0)
    ∧
    Q 1 = 0
    ∧
    (1 : ℂ) ∉ forbiddenProduct
    ∧
    ((1 : ℂ) ≠ 0 ∧ ((-1 : ℂ) * 1 - 0 * 0) ≠ 0) := by
  exact
    ⟨Phi_zero_free_off_K₁_K₂,
     Q_one_eq_zero,
     one_not_mem_forbiddenProduct,
     nondegenerate_coefficients⟩

end InfoGeometry.Canonical.AsanoRuelleCounterexample

