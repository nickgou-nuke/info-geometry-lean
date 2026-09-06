import Mathlib

/-!
# Finite Mobius Coefficient Extraction

This is the finite coefficient layer behind

`∏ᵢ (1 - xᵢ) = Σ occupation words (-1)^F ∏ occupied xᵢ`.

The infinite statement `Σ μ(n)n^{-s} = 1/ζ(s)` is not asserted here.  This
file proves the finite Fock expansion which produces the Mobius signs on
squarefree prime configurations.
-/

noncomputable section

namespace FiniteMobiusCoefficient

/-- Local graded fermion factor: empty state minus occupied state. -/
def gradedLocal (x : ℂ) : ℂ :=
  1 - x

/-- Finite graded determinant/product over a cutoff list. -/
def gradedProduct (xs : List ℂ) : ℂ :=
  xs.map gradedLocal |>.prod

/--
Coefficient-extraction recurrence:

* words not occupying the new mode contribute `occupationExpansion xs`;
* words occupying the new mode contribute `-x * occupationExpansion xs`.
-/
def occupationExpansion : List ℂ → ℂ
  | [] => 1
  | x :: xs => occupationExpansion xs + (-x) * occupationExpansion xs

theorem occupationExpansion_nil :
    occupationExpansion [] = 1 := rfl

theorem occupationExpansion_cons (x : ℂ) (xs : List ℂ) :
    occupationExpansion (x :: xs) =
      occupationExpansion xs + (-x) * occupationExpansion xs := rfl

/-- Finite word expansion equals the finite graded Euler factor. -/
theorem occupationExpansion_eq_gradedProduct (xs : List ℂ) :
    occupationExpansion xs = gradedProduct xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [occupationExpansion, gradedProduct, gradedLocal, ih]
      ring

/-- Fermion-parity coefficient for a word with `k` occupied modes. -/
def mobiusWordCoefficient (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k

theorem mobiusWordCoefficient_zero :
    mobiusWordCoefficient 0 = 1 := by
  simp [mobiusWordCoefficient]

theorem mobiusWordCoefficient_succ (k : ℕ) :
    mobiusWordCoefficient (k + 1) = -mobiusWordCoefficient k := by
  simp [mobiusWordCoefficient, pow_succ]

/-- Explicit two-mode coefficient expansion. -/
theorem two_mode_coefficients (x y : ℂ) :
    occupationExpansion [x, y] = 1 - x - y + x * y := by
  rw [occupationExpansion_eq_gradedProduct]
  simp [gradedProduct, gradedLocal]
  ring

/-- Explicit three-mode coefficient expansion. -/
theorem three_mode_coefficients (x y z : ℂ) :
    occupationExpansion [x, y, z] =
      1 - (x + y + z) + (x * y + x * z + y * z) - x * y * z := by
  rw [occupationExpansion_eq_gradedProduct]
  simp [gradedProduct, gradedLocal]
  ring

/--
Appending a new prime mode multiplies the already extracted finite Mobius
coefficient polynomial by the new local factor.
-/
theorem occupationExpansion_snoc (xs : List ℂ) (x : ℂ) :
    occupationExpansion (xs ++ [x]) = occupationExpansion xs * (1 - x) := by
  rw [occupationExpansion_eq_gradedProduct xs]
  rw [occupationExpansion_eq_gradedProduct (xs ++ [x])]
  induction xs with
  | nil =>
      simp [gradedProduct, gradedLocal]
  | cons y ys ih =>
      simp [gradedProduct, gradedLocal]
      ring

/--
Finite Mobius coefficient synthesis: the graded determinant is exactly the
even-minus-odd occupation expansion, with local coefficient `(-1)^F`.
-/
theorem finite_mobius_coefficient_synthesis :
    (∀ xs : List ℂ, occupationExpansion xs = gradedProduct xs) ∧
    mobiusWordCoefficient 0 = 1 ∧
    (∀ k : ℕ, mobiusWordCoefficient (k + 1) = -mobiusWordCoefficient k) ∧
    (∀ x y z : ℂ,
      occupationExpansion [x, y, z] =
        1 - (x + y + z) + (x * y + x * z + y * z) - x * y * z) ∧
    (∀ xs : List ℂ, ∀ x : ℂ,
      occupationExpansion (xs ++ [x]) = occupationExpansion xs * (1 - x)) := by
  exact ⟨occupationExpansion_eq_gradedProduct,
    mobiusWordCoefficient_zero,
    mobiusWordCoefficient_succ,
    three_mode_coefficients,
    occupationExpansion_snoc⟩

end FiniteMobiusCoefficient

end noncomputable section
