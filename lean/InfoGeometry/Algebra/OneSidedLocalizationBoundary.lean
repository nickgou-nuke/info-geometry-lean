/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SandwichLocalizationActions
import Mathlib.Algebra.Star.Basic

/-!
# The centralizer boundary of the naive one-sided formulas

These are exact congruence statements for the specified cross relation and
ordered representative multiplication. They do not assert nonexistence of
other localizations, transported involutions, or internally invertible
denominators. The raw cross relation is not installed as a setoid without
the regularity needed for transitivity.
-/

namespace InfoGeometry.Algebra.OneSidedLocalizationBoundary

open InfoGeometry.Algebra.SandwichLocalization

variable {B : Type*} [Ring B]

/-- The unsaturated one-sided cross relation from the submitted formulas. -/
def Rel (s : B) (k : ℕ) (x : B) (l : ℕ) (y : B) : Prop := s ^ l * x = s ^ k * y

/-- For a subring containing the denominator, the naive multiplication is a
congruence exactly when every numerator commutes with that denominator. -/
theorem mul_congr_iff_centralizer (s : B) (R : Subring B) (hs : s ∈ R) :
    (∀ k k' l l' : ℕ, ∀ x x' y y' : R,
      Rel s k (x : B) k' (x' : B) → Rel s l (y : B) l' (y' : B) →
      Rel s (k + l) ((x : B) * y) (k' + l') ((x' : B) * y')) ↔
      R ≤ Subring.centralizer ({s} : Set B) := by
  constructor
  · intro h x hx
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    have he := h 0 0 0 1 ⟨x, hx⟩ ⟨x, hx⟩ 1 ⟨s, hs⟩ rfl
      (by simp only [Rel, pow_one, pow_zero, Subring.coe_one, mul_one, one_mul])
    simpa only [Rel, Nat.add_zero, Nat.zero_add, pow_zero, pow_one,
      Subring.coe_one, mul_one, one_mul] using he
  · intro h k k' l l' x x' y y' hx hy
    have hc : Commute s (x : B) := h x.property s (Set.mem_singleton s)
    have hc' : Commute s (x' : B) := h x'.property s (Set.mem_singleton s)
    change s ^ (k' + l') * ((x : B) * y) = s ^ (k + l) * ((x' : B) * y')
    change s ^ k' * (x : B) = s ^ k * (x' : B) at hx
    change s ^ l' * (y : B) = s ^ l * (y' : B) at hy
    calc
      _ = (s ^ k' * (x : B)) * (s ^ l' * (y : B)) := by
        rw [pow_add]
        calc
          _ = s ^ k' * ((s ^ l' * (x : B)) * (y : B)) := by noncomm_ring
          _ = _ := by rw [(hc.pow_left l').eq]; simp only [mul_assoc]
      _ = (s ^ k * (x' : B)) * (s ^ l * (y' : B)) := by rw [hx, hy]
      _ = _ := by
        rw [pow_add]
        calc
          _ = s ^ k * (((x' : B) * s ^ l) * (y' : B)) := by noncomm_ring
          _ = _ := by rw [← (hc'.pow_left l).eq]; simp only [mul_assoc]

section Star

variable [StarRing B]

private theorem commute_star (s x : B) (hs : star s = s) (hx : Commute s x) :
    Commute s (star x) := by
  simpa only [star_mul, hs] using (congrArg star hx.eq).symm

/-- Numerator star respects the stated one-sided relation exactly on a
subring centralizing a self-adjoint denominator. Star-closure of the subring
is a separate condition when an internal involution is desired. -/
theorem star_congr_iff_centralizer (s : B) (hself : star s = s)
    (R : Subring B) (hs : s ∈ R) :
    (∀ k l : ℕ, ∀ x y : R, Rel s k (x : B) l (y : B) →
      Rel s k (star (x : B)) l (star (y : B))) ↔
      R ≤ Subring.centralizer ({s} : Set B) := by
  constructor
  · intro h x hx
    intro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    have he := h 0 1 ⟨x, hx⟩ ⟨s * x, R.mul_mem hs hx⟩
      (by simp only [Rel, pow_zero, pow_one, one_mul])
    have hc : s * star x = star x * s := by
      simpa only [Rel, pow_zero, pow_one, one_mul, star_mul, hself] using he
    simpa only [star_mul, star_star, hself] using (congrArg star hc).symm
  · intro h k l x y he
    have hx := commute_star s (x : B) hself (h x.property s (Set.mem_singleton s))
    have hy := commute_star s (y : B) hself (h y.property s (Set.mem_singleton s))
    change s ^ l * star (x : B) = s ^ k * star (y : B)
    have he' := congrArg star he
    change star (s ^ l * (x : B)) = star (s ^ k * (y : B)) at he'
    simpa only [star_mul, star_pow, hself, ← (hx.pow_left l).eq,
      ← (hy.pow_left k).eq] using he'

end Star

end InfoGeometry.Algebra.OneSidedLocalizationBoundary
