import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

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

namespace InfoGeometry.Canonical.ProjectiveSpaceGrothendieckRing

open scoped BigOperators

variable {R : Type*} [Ring R]

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
        rw [← pow_succ']
      rw [sub_mul, one_mul, h_pow]
      abel

/-- The right-handed finite geometric-series identity `(sum X^k) * (1 - X) = 1 - X^(n + 1)`. -/
lemma sub_mul_geom_sum (X : R) (n : Nat) :
    Finset.sum (Finset.range (n + 1)) (fun k => X ^ k) * (1 - X) =
      1 - X ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h_split :
          Finset.sum (Finset.range (n + 2)) (fun k => X ^ k) =
            Finset.sum (Finset.range (n + 1)) (fun k => X ^ k) + X ^ (n + 1) := by
        simpa [Nat.add_assoc] using Finset.sum_range_succ (fun k : Nat => X ^ k) (n + 1)
      rw [h_split, add_mul, ih]
      have h_pow : X ^ (n + 1) * X = X ^ (n + 2) := by
        rw [← pow_succ]
      rw [mul_sub, mul_one, h_pow]
      abel

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
    abel
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
  have h_mul_right : invT * T = 1 := by
    dsimp [invT]
    have h_sub : 1 - (1 - T) = T := by abel
    have h_right := sub_mul_geom_sum (1 - T) n
    rw [h_sub, h, sub_zero] at h_right
    exact h_right
  exact isUnit_iff_exists.mpr ⟨invT, h_mul, h_mul_right⟩

/-- The element `1 - T` is nilpotent under the projective-space relation. -/
theorem projective_space_nilpotent (T : R) (n : Nat) (h : (1 - T) ^ (n + 1) = 0) :
    IsNilpotent (1 - T) := by
  exact IsNilpotent.mk (1 - T) (n + 1) h

end InfoGeometry.Canonical.ProjectiveSpaceGrothendieckRing
