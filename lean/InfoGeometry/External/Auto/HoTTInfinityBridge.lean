import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
Native categorical fragment retained from the former HoTT bridge.

The repository/source graph and external commit metadata are not theorem
objects.  The square-zero differential condition is a genuine categorical
proposition and is kept here as a small reusable owner.
-/

namespace HoTTInfinityBridge

open CategoryTheory
open CategoryTheory.Limits

variable {V : Type*} [Category V] [HasZeroMorphisms V]

def IsSpectralDifferential2
    {E2 : ℕ → ℤ → V}
    (d2 : ∀ p q, E2 p q ⟶ E2 (p + 2) (q - 1)) : Prop :=
  ∀ p : ℕ, ∀ q : ℤ,
    d2 p q ≫ d2 (p + 2) (q - 1) = 0

theorem d2Square
    {E2 : ℕ → ℤ → V}
    {d2 : ∀ p q, E2 p q ⟶ E2 (p + 2) (q - 1)}
    (h : IsSpectralDifferential2 d2) (p : ℕ) (q : ℤ) :
    d2 p q ≫ d2 (p + 2) (q - 1) = 0 :=
  h p q

def d2Bidegree (p q : ℕ) : ℕ × Int :=
  (p + 2, (q : Int) - 1)

@[simp] theorem d2Bidegree_zero_one :
    d2Bidegree 0 1 = (2, 0) := by
  rfl

@[simp] theorem d2Bidegree_two_one :
    d2Bidegree 2 1 = (4, 0) := by
  rfl

end HoTTInfinityBridge
