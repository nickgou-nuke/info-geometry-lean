import Mathlib.Tactic

/-!
Small native algebraic owner retained from the former Varlamov/Klein fixture.

The fixed representation dimensions and Boolean concept graph are not proofs
of a Weyl or spinor construction and are intentionally omitted.
-/

namespace VarlamovKleinSpectral

def tripotent (d : ℤ) : Prop := d ^ 3 = d

def tripotentPolynomial (d : ℤ) : ℤ := d ^ 3 - d

def mobiusInv (k : ℤ) : ℤ := -k

structure BrillouinMode where
  k : ℤ
  deriving DecidableEq, Repr

def kleinQuotient (m₁ m₂ : BrillouinMode) : Prop :=
  m₁.k = m₂.k ∨ m₁.k = mobiusInv m₂.k

theorem tripotent_roots (d : ℤ) :
    tripotent d ↔ d = 0 ∨ d = 1 ∨ d = -1 := by
  constructor
  · intro h
    have hfact : d * (d - 1) * (d + 1) = 0 := by
      have hsub : d ^ 3 - d = 0 := sub_eq_zero.mpr h
      simpa [show d ^ 3 - d = d * (d - 1) * (d + 1) by ring] using hsub
    rcases mul_eq_zero.mp hfact with hleft | hplus
    · rcases mul_eq_zero.mp hleft with h0 | hminus
      · exact Or.inl h0
      · exact Or.inr (Or.inl (sub_eq_zero.mp hminus))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hplus))
  · intro h
    rcases h with h | h | h <;> simp [tripotent, h]

theorem tripotent_polynomial_roots :
    tripotentPolynomial (-1) = 0 ∧
    tripotentPolynomial 0 = 0 ∧
    tripotentPolynomial 1 = 0 := by
  norm_num [tripotentPolynomial]

theorem mobius_involutive (k : ℤ) :
    mobiusInv (mobiusInv k) = k := by
  simp [mobiusInv]

theorem klein_quotient_equivalence : Equivalence kleinQuotient := by
  refine ⟨?refl, ?symm, ?trans⟩
  · intro m
    exact Or.inl rfl
  · intro m₁ m₂ h
    rcases h with h | h
    · exact Or.inl h.symm
    · right
      rw [h, mobius_involutive]
  · intro m₁ m₂ m₃ h₁ h₂
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inr (h₁.trans h₂)
    · rcases h₂ with h₂ | h₂
      · exact Or.inr (by rw [h₁, h₂])
      · exact Or.inl (by rw [h₁, h₂, mobius_involutive])

end VarlamovKleinSpectral
