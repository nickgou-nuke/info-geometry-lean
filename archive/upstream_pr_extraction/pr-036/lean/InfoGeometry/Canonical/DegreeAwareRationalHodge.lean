import Mathlib
import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation

namespace InfoGeometry.Canonical

/-!
Degree-aware Hodge data indexed by `Fin (n + 1)`.  Using `Fin` makes the
degree reversal total and avoids silently truncating natural-number
subtraction at the endpoints.
-/

def degreeReverse (n : ℕ) (p : Fin (n + 1)) : Fin (n + 1) :=
  ⟨n - p.1, by omega⟩

theorem degreeReverse_degreeReverse
    (n : ℕ) (p : Fin (n + 1)) :
    degreeReverse n (degreeReverse n p) = p := by
  apply Fin.ext
  dsimp [degreeReverse]
  omega

def degreeReverseCast
    {n : ℕ}
    {V : Fin (n + 1) → Type*}
    (p : Fin (n + 1)) :
    V (degreeReverse n (degreeReverse n p)) → V p :=
  cast (congrArg V (degreeReverse_degreeReverse n p))

structure DegreeAwareRationalHodge
    (n : ℕ)
    (V : Fin (n + 1) → Type*)
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)] where
  star : ∀ p, V p ≃ₗ[ℚ] V (degreeReverse n p)
  squareSign : Fin (n + 1) → ℚ
  star_square :
    ∀ (p : Fin (n + 1)) (x : V p),
      degreeReverseCast p
        (star (degreeReverse n p) (star p x)) =
        squareSign p • x

theorem DegreeAwareRationalHodge.star_square_one
    {n : ℕ}
    {V : Fin (n + 1) → Type*}
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)]
    (H : DegreeAwareRationalHodge n V)
    (hSign : ∀ p, H.squareSign p = 1)
    (p : Fin (n + 1)) (x : V p) :
    degreeReverseCast p
      (H.star (degreeReverse n p) (H.star p x)) = x := by
  rw [H.star_square, hSign]
  simp

theorem DegreeAwareRationalHodge.star_involutive_apply
    {n : ℕ}
    {V : Fin (n + 1) → Type*}
    [∀ p, AddCommGroup (V p)]
    [∀ p, Module ℚ (V p)]
    (H : DegreeAwareRationalHodge n V)
    (hSign : ∀ p, H.squareSign p = 1)
    (p : Fin (n + 1)) (x : V p) :
    degreeReverseCast p
      (H.star (degreeReverse n p) (H.star p x)) = x :=
  H.star_square_one hSign p x

theorem degreeReverse_zero (n : ℕ) :
    degreeReverse n (0 : Fin (n + 1)) = ⟨n, by omega⟩ := by
  apply Fin.ext
  simp [degreeReverse]

theorem degreeReverse_top (n : ℕ) :
    degreeReverse n ⟨n, by omega⟩ = (0 : Fin (n + 1)) := by
  apply Fin.ext
  simp [degreeReverse]

end InfoGeometry.Canonical
