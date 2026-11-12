/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CentralPowerLocalization

/-!
# Star on central-power localization and internal Cayley unitaries

Self-adjointness of the central denominator makes numerator star descend to
the native quotient. The construction is valid even for singular denominators.
Unitary quotient elements are then produced from a polynomial norm identity.
-/

namespace InfoGeometry.Algebra.CentralPowerLocalization

open OreLocalization

variable {B : Type*} [Ring B] [StarRing B]
variable (s : B) [Fact (∀ x : B, Commute s x)] [hself : Fact (star s = s)]

omit [Fact (∀ x : B, Commute s x)] in
/-- All denominator powers are self-adjoint. -/
theorem star_denominator (a : Submonoid.powers s) : star (a : B) = a := by
  rcases a.property with ⟨n, hn⟩
  rw [← hn, star_pow, hself.out]

/-- Star preserves a central denominator cross product without reversing
the order of its two denominator factors. -/
theorem star_cross_product (t b : Submonoid.powers s) (x : B) :
    star ((t : B) * ((b : B) * x)) =
      (t : B) * ((b : B) * star x) := by
  rw [star_mul, star_mul, star_denominator, star_denominator,
    ← (denominator_commute s b (star x)).eq,
    ← (denominator_commute s t ((b : B) * star x)).eq]

/-- The numerator-star operation respects genuine Ore fraction equality. -/
theorem fraction_star_congr (x y : B) (a b : Submonoid.powers s)
    (h : (x /ₒ a : Away s) = y /ₒ b) :
    (star x /ₒ a : Away s) = star y /ₒ b := by
  obtain ⟨t, ht⟩ := (fraction_eq_iff_cross s x y a b).mp h
  apply (fraction_eq_iff_cross s (star x) (star y) a b).mpr
  refine ⟨t, ?_⟩
  simpa only [star_cross_product] using congrArg star ht

/-- Star is defined on the native quotient, with no inverse supplied. -/
def starMap : Away s → Away s :=
  Quotient.lift (fun p : B × Submonoid.powers s => star p.1 /ₒ p.2)
    (by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      exact fraction_star_congr s x y a b (Quotient.sound h))

instance awayStar : Star (Away s) where
  star := starMap s

/-- The induced star acts on stage numerators. -/
@[simp] theorem star_repr (k : ℕ) (x : B) :
    star (repr s k x) = repr s k (star x) := rfl

instance awayInvolutiveStar : InvolutiveStar (Away s) where
  star_involutive q := by
    obtain ⟨k, x, rfl⟩ := exists_repr s q
    simp only [star_repr, star_star]

instance awayStarMul : StarMul (Away s) where
  star_mul q r := by
    obtain ⟨k, x, rfl⟩ := exists_repr s q
    obtain ⟨l, y, rfl⟩ := exists_repr s r
    rw [repr_mul, star_repr, star_repr, star_repr, repr_mul, star_mul,
      Nat.add_comm k l]

instance awayStarRing : StarRing (Away s) where
  star_add q r := by
    obtain ⟨k, x, rfl⟩ := exists_repr s q
    obtain ⟨l, y, rfl⟩ := exists_repr s r
    rw [repr_add, star_repr, star_repr, star_repr, repr_add]
    congr 1
    rw [star_add, star_mul, star_mul, star_pow, star_pow, hself.out,
      ← (power_commute s l (star x)).eq,
      ← (power_commute s k (star y)).eq]

/-- The canonical map is star preserving. -/
@[simp] theorem star_of (x : B) : star (of s x) = of s (star x) := rfl

/-- The internally constructed inverse of a self-adjoint denominator is
self-adjoint. -/
@[simp] theorem star_inverse : star (inverse s) = inverse s := by
  simp only [inverse, star_repr, star_one]

omit [StarRing B] hself in
/-- A denominator power cancels against itself in the quotient. -/
theorem repr_self_power (k : ℕ) : repr s k (s ^ k) = 1 := by
  exact OreLocalization.div_eq_one (s := Submonoid.pow s k)

/-- The Cayley candidate is an explicit stage-one cocone element. -/
def cayley (a : B) : Away s := repr s 1 a

/-- A polynomial right norm identity gives a right unitary identity in the
localization; no unitary witness is assumed. -/
theorem star_cayley_mul (a : B) (ha : star a * a = s ^ 2) :
    star (cayley s a) * cayley s a = 1 := by
  unfold cayley
  rw [star_repr, repr_mul, ha]
  exact repr_self_power s 2

/-- The opposite polynomial norm identity gives the other unitary identity. -/
theorem cayley_mul_star (a : B) (ha : a * star a = s ^ 2) :
    cayley s a * star (cayley s a) = 1 := by
  unfold cayley
  rw [star_repr, repr_mul, ha]
  exact repr_self_power s 2

/-- Both polynomial identities yield a genuine unitary quotient element. -/
theorem cayley_unitary (a : B)
    (ha : star a * a = s ^ 2) (ha' : a * star a = s ^ 2) :
    star (cayley s a) * cayley s a = 1 ∧
      cayley s a * star (cayley s a) = 1 :=
  ⟨star_cayley_mul s a ha, cayley_mul_star s a ha'⟩

end InfoGeometry.Algebra.CentralPowerLocalization
