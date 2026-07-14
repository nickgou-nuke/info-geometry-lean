import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

/-!
# Projective Space Grothendieck Ring

Finite algebraic inverse theorem for the projective-space relation
`(1 - T) ^ (n + 1) = 0`.

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `geom_sum_mul_sub`
- `projective_space_inverse_identity`
- `projective_space_unit`
- `projective_space_nilpotent`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/

set_option autoImplicit false

namespace ProjectiveSpaceGrothendieckRing

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The finite geometric-series identity `(1 - X) * sum X^k = 1 - X^(n + 1)`. -/
lemma geom_sum_mul_sub (X : R) (n : Nat) :
    (1 - X) * Finset.sum (Finset.range (n + 1)) (fun k => X ^ k) =
      1 - X ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h_split :
          Finset.sum (Finset.range (n + 2)) (fun k => X ^ k) =
            Finset.sum (Finset.range (n + 1)) (fun k => X ^ k) + X ^ (n + 1) := by
        simpa [Nat.add_assoc] using Finset.sum_range_succ (fun k : Nat => X ^ k) (n + 1)
      rw [h_split, mul_add, ih]
      have h_pow : X * X ^ (n + 1) = X ^ (n + 2) := by
        ring
      calc
        (1 - X ^ (n + 1)) + (1 - X) * X ^ (n + 1)
            = 1 - X ^ (n + 1) + (X ^ (n + 1) - X * X ^ (n + 1)) := by
              ring
        _ = 1 - X * X ^ (n + 1) := by
              ring
        _ = 1 - X ^ (n + 2) := by
              rw [h_pow]

/--
The inverse polynomial identity for the projective-space coordinate `T`:
`T * sum (1 - T)^k = 1 - (1 - T)^(n + 1)`.
-/
theorem projective_space_inverse_identity (T : R) (n : Nat) :
    T * Finset.sum (Finset.range (n + 1)) (fun k => (1 - T) ^ k) =
      1 - (1 - T) ^ (n + 1) := by
  have h :
      (1 - (1 - T)) * Finset.sum (Finset.range (n + 1)) (fun k => (1 - T) ^ k) =
        1 - (1 - T) ^ (n + 1) :=
    geom_sum_mul_sub (1 - T) n
  have h_sub : 1 - (1 - T) = T := by
    ring
  rwa [h_sub] at h

/--
If `(1 - T)^(n + 1) = 0`, then `T` is a unit with inverse
`sum_{k=0}^n (1 - T)^k`.
-/
theorem projective_space_unit (T : R) (n : Nat) (h : (1 - T) ^ (n + 1) = 0) :
    IsUnit T := by
  let invT : R := Finset.sum (Finset.range (n + 1)) (fun k => (1 - T) ^ k)
  have h_mul : T * invT = 1 := by
    dsimp [invT]
    rw [projective_space_inverse_identity T n, h, sub_zero]
  exact isUnit_iff_exists.mpr ⟨invT, h_mul, by rwa [mul_comm]⟩

/-- The element `1 - T` is nilpotent under the projective-space relation. -/
theorem projective_space_nilpotent (T : R) (n : Nat) (h : (1 - T) ^ (n + 1) = 0) :
    IsNilpotent (1 - T) := by
  exact IsNilpotent.mk (1 - T) (n + 1) h

end ProjectiveSpaceGrothendieckRing
