/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDecomposition
import Mathlib.Algebra.Star.Basic

/-!
# Division-free reflection and two-block Peirce parity

This groups the existing four Peirce components into two complementary additive
projections. The split and its multiplication rules work in every ring. Only
identification with the reflection's sign eigenspaces requires injective doubling.
No inverse-existence, metric positivity, or semisimple Lie-algebra claim is made.
-/

namespace InfoGeometry.Core.IdempotentCartan

open InfoGeometry.Core.PeirceDecomposition

variable {R : Type*} [Ring R]

/-- The reflection associated to an idempotent, without division by two. -/
def reflection (p : R) : R := 2 • p - 1

/-- Diagonal sum of the existing two-block Peirce components. -/
def evenPart (p x : R) : R := component11 p x + component00 p x

/-- Off-diagonal sum; its individual directed corners, not its sum, are square-zero. -/
def oddPart (p x : R) : R := component10 p x + component01 p x

theorem even_add_odd (p x : R) : evenPart p x + oddPart p x = x := by
  calc
    _ = component11 p x + component10 p x + component01 p x + component00 p x := by
      dsimp [evenPart, oddPart]
      abel
    _ = x := (peirce_decomposition p x).symm

theorem evenPart_add (p x y : R) :
    evenPart p (x + y) = evenPart p x + evenPart p y := by
  simp only [evenPart, component11, component00, mul_add, add_mul]
  abel

theorem oddPart_add (p x y : R) :
    oddPart p (x + y) = oddPart p x + oddPart p y := by
  simp only [oddPart, component10, component01, mul_add, add_mul]
  abel

theorem oddPart_sub (p x y : R) :
    oddPart p (x - y) = oddPart p x - oddPart p y := by
  simp only [oddPart, component10, component01, mul_sub, sub_mul]
  abel

theorem reflection_sq {p : R} (hp : p * p = p) :
    reflection p * reflection p = 1 := by
  simp only [reflection, two_nsmul]
  noncomm_ring [hp]

theorem reflection_star [StarRing R] {p : R} (hp : star p = p) :
    star (reflection p) = reflection p := by
  simp only [reflection, two_nsmul, star_sub, star_add, star_one, hp]

/-- Conjugation by the reflection is an actual ring equivalence. -/
def reflectionConj (p : R) (hp : p * p = p) : R ≃+* R where
  toFun x := reflection p * x * reflection p
  invFun x := reflection p * x * reflection p
  left_inv x := by
    calc
      _ = (reflection p * reflection p) * x * (reflection p * reflection p) := by
        noncomm_ring
      _ = x := by rw [reflection_sq hp]; simp
  right_inv x := by
    calc
      _ = (reflection p * reflection p) * x * (reflection p * reflection p) := by
        noncomm_ring
      _ = x := by rw [reflection_sq hp]; simp
  map_mul' x y := by
    calc
      _ = reflection p * x * 1 * y * reflection p := by noncomm_ring
      _ = reflection p * x * (reflection p * reflection p) * y * reflection p := by
        rw [reflection_sq hp]
      _ = _ := by noncomm_ring
  map_add' x y := by simp only [mul_add, add_mul]

theorem conjugation_eq_even_sub_odd (p x : R) :
    reflection p * x * reflection p = evenPart p x - oddPart p x := by
  simp only [reflection, two_nsmul, evenPart, oddPart, component11, component00,
    component10, component01, complementIdempotent]
  noncomm_ring

theorem doubled_parts (p x : R) :
    x + reflection p * x * reflection p = 2 • evenPart p x ∧
    x - reflection p * x * reflection p = 2 • oddPart p x := by
  rw [conjugation_eq_even_sub_odd]
  constructor
  · calc
      x + (evenPart p x - oddPart p x) =
          (evenPart p x + oddPart p x) + (evenPart p x - oddPart p x) := by
            rw [even_add_odd]
      _ = 2 • evenPart p x := by rw [two_nsmul]; abel
  · calc
      x - (evenPart p x - oddPart p x) =
          (evenPart p x + oddPart p x) - (evenPart p x - oddPart p x) := by
            rw [even_add_odd]
      _ = 2 • oddPart p x := by rw [two_nsmul]; abel

theorem projection_laws {p : R} (hp : p * p = p) (x : R) :
    evenPart p (evenPart p x) = evenPart p x ∧
    evenPart p (oddPart p x) = 0 ∧
    oddPart p (evenPart p x) = 0 ∧
    oddPart p (oddPart p x) = oddPart p x := by
  simp only [evenPart, oddPart, component11, component00, component10, component01,
    complementIdempotent]
  constructor
  · noncomm_ring [hp]
  constructor
  · noncomm_ring [hp]
  constructor <;> noncomm_ring [hp]

/-- Unique diagonal/off-diagonal decomposition, including in characteristic two. -/
theorem decomposition_unique {p e o x : R} (hp : p * p = p)
    (he : evenPart p e = e) (ho : oddPart p o = o) (hx : e + o = x) :
    e = evenPart p x ∧ o = oddPart p x := by
  have heo : evenPart p o = 0 := by
    rw [← ho]
    exact (projection_laws hp o).2.1
  have hoe : oddPart p e = 0 := by
    rw [← he]
    exact (projection_laws hp e).2.2.1
  rw [← hx, evenPart_add, oddPart_add, he, ho, heo, hoe, add_zero, zero_add]
  exact ⟨rfl, rfl⟩

/-- The multiplication table giving an actual two-piece additive ring grading. -/
theorem multiplication_rules {p : R} (hp : p * p = p) (x y : R) :
    evenPart p (x * y) = evenPart p x * evenPart p y + oddPart p x * oddPart p y ∧
    oddPart p (x * y) = evenPart p x * oddPart p y + oddPart p x * evenPart p y := by
  simp only [evenPart, oddPart, component11, component00, component10, component01,
    complementIdempotent]
  constructor <;> noncomm_ring [hp]

theorem reflection_parities {p : R} (hp : p * p = p) (x : R) :
    reflection p * evenPart p x = evenPart p x * reflection p ∧
    reflection p * oddPart p x + oddPart p x * reflection p = 0 := by
  simp only [reflection, two_nsmul, evenPart, oddPart, component11, component00,
    component10, component01, complementIdempotent]
  constructor <;> noncomm_ring [hp]

theorem conjugation_on_parts {p : R} (hp : p * p = p) (x : R) :
    reflection p * evenPart p x * reflection p = evenPart p x ∧
    reflection p * oddPart p x * reflection p = -oddPart p x := by
  rcases projection_laws hp x with ⟨hee, heo, hoe, hoo⟩
  simp only [conjugation_eq_even_sub_odd, hee, heo, hoe, hoo, sub_zero, zero_sub,
    and_self]

theorem odd_eq_reflection_commutator {p : R} (hp : p * p = p) (x : R) :
    oddPart p x = reflection p * (p * x - x * p) := by
  simp only [oddPart, component10, component01, complementIdempotent,
    reflection, two_nsmul]
  noncomm_ring [hp]

theorem odd_eq_double_commutator {p : R} (hp : p * p = p) (x : R) :
    oddPart p x = p * (p * x - x * p) - (p * x - x * p) * p := by
  simp only [oddPart, component10, component01, complementIdempotent]
  noncomm_ring [hp]

theorem reflection_mul_odd {p : R} (hp : p * p = p) (x : R) :
    reflection p * oddPart p x = p * x - x * p := by
  rw [odd_eq_reflection_commutator hp, ← mul_assoc, reflection_sq hp, one_mul]

theorem odd_zero_iff_commute {p : R} (hp : p * p = p) (x : R) :
    oddPart p x = 0 ↔ p * x = x * p := by
  constructor
  · intro hx
    have h := reflection_mul_odd hp x
    rw [hx, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  · intro hx
    rw [odd_eq_reflection_commutator hp, hx, sub_self, mul_zero]

theorem even_eq_self_of_commute {p x : R} (hp : p * p = p)
    (hx : p * x = x * p) : evenPart p x = x := by
  have h := even_add_odd p x
  rw [(odd_zero_iff_commute hp x).2 hx, add_zero] at h
  exact h

theorem commutator_is_odd {p : R} (hp : p * p = p) (x : R) :
    oddPart p (p * x - x * p) = p * x - x * p ∧
    reflection p * (p * x - x * p) + (p * x - x * p) * reflection p = 0 := by
  simp only [oddPart, component10, component01, complementIdempotent,
    reflection, two_nsmul]
  constructor <;> noncomm_ring [hp]

theorem corners_square_zero {p : R} (hp : p * p = p) (x : R) :
    component10 p x * component10 p x = 0 ∧
    component01 p x * component01 p x = 0 :=
  ⟨peirce10_mul_peirce10_eq_zero p hp (component10_mem p x) (component10_mem p x),
    peirce01_mul_peirce01_eq_zero p hp (component01_mem p x) (component01_mem p x)⟩

/-- Injective doubling, rather than a hidden inverse of two, suffices. -/
theorem sign_eigenspaces {p : R} (hp : p * p = p)
    (h2 : Function.Injective (fun x : R => (2 : ℕ) • x)) (x : R) :
    (evenPart p x = x ↔ reflection p * x * reflection p = x) ∧
    (oddPart p x = x ↔ reflection p * x * reflection p = -x) := by
  constructor
  · constructor
    · intro hx
      simpa only [hx] using (conjugation_on_parts hp x).1
    · intro hx
      apply h2
      calc
        2 • evenPart p x = x + reflection p * x * reflection p :=
          (doubled_parts p x).1.symm
        _ = 2 • x := by rw [hx, two_nsmul]
  · constructor
    · intro hx
      simpa only [hx] using (conjugation_on_parts hp x).2
    · intro hx
      apply h2
      calc
        2 • oddPart p x = x - reflection p * x * reflection p :=
          (doubled_parts p x).2.symm
        _ = 2 • x := by rw [hx, sub_neg_eq_add, two_nsmul]

end InfoGeometry.Core.IdempotentCartan
