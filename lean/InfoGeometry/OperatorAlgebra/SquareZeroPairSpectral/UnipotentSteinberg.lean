/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.MassCommutant

/-!
# Unipotent conjugations, Weyl elements and Steinberg braids

For square-zero `u v` in an associative `R`-algebra `A`:

* `1 + u` is a unit with inverse `1 - u`; conjugation by it is the operator
  `unipotentConj R u = sandwichOp R (1 + u) (1 - u)` in `Module.End R A`;
* the Weyl element `W = (u - v) + (1 - V)` has unitarity defect
  `W W' - 1 = V² - V` against `W' = -(u - v) + (1 - V)`;
* the Steinberg braids `B₊ = (1 + u)(1 - v)(1 + u)` and
  `B₋ = (1 - v)(1 + u)(1 - v)` satisfy `B₊ = W + (1 - V) u`,
  `B₋ = W - (1 - V) v`, and are units.

The formula `B₊ = W + (1 - V) u` corrects the AI-generated intake claim
`B₊ = W + u + V u`, which fails already for corner operators in `Mat₅(ℚ)`.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.OperatorAlgebra.LieJordan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

section Unipotent

variable {u u' : A}

theorem one_add_mul_one_sub (hu : u * u = 0) : (1 + u) * (1 - u) = 1 := by
  noncomm_ring [hu]

theorem one_sub_mul_one_add (hu : u * u = 0) : (1 - u) * (1 + u) = 1 := by
  noncomm_ring [hu]

/-- The unipotent unit `1 + u` of a square-zero element. -/
@[simps]
def unipotentUnit (u : A) (hu : u * u = 0) : Aˣ where
  val := 1 + u
  inv := 1 - u
  val_inv := one_add_mul_one_sub hu
  inv_val := one_sub_mul_one_add hu

variable (R) in
/-- Conjugation by `1 + u`, as an element of the operator ring. -/
def unipotentConj (u : A) : Module.End R A := sandwichOp R (1 + u) (1 - u)

theorem unipotentConj_apply (x : A) :
    unipotentConj R u x = (1 + u) * x * (1 - u) := rfl

/-- `Ad(1 + u) x = x + [u, x] - u x u`. -/
theorem unipotentConj_expand (x : A) :
    unipotentConj R u x = x + (u * x - x * u) - u * x * u := by
  rw [unipotentConj_apply]; noncomm_ring

/-- Conjugation by `1 - u` inverts conjugation by `1 + u` in `Module.End R A`. -/
theorem unipotentConj_mul_neg (hu : u * u = 0) :
    unipotentConj R u * unipotentConj R (-u) = 1 := by
  ext x
  change (1 + u) * ((1 + -u) * x * (1 - -u)) * (1 - u) = x
  have h1 : (1 + u) * (1 + -u) = 1 := by noncomm_ring [hu]
  have h2 : (1 - -u) * (1 - u) = 1 := by noncomm_ring [hu]
  calc _ = ((1 + u) * (1 + -u)) * x * ((1 - -u) * (1 - u)) := by noncomm_ring
    _ = x := by rw [h1, h2, one_mul, mul_one]

theorem unipotentConj_neg_mul (hu : u * u = 0) :
    unipotentConj R (-u) * unipotentConj R u = 1 := by
  have := unipotentConj_mul_neg (R := R) (u := -u) (by rw [neg_mul_neg, hu])
  rwa [neg_neg] at this

/-- Group law on a mutually annihilating family (e.g. one Peirce corner). -/
theorem unipotentConj_mul_of_annihilate (h1 : u * u' = 0) (h2 : u' * u = 0) :
    unipotentConj R u * unipotentConj R u' = unipotentConj R (u + u') := by
  ext x
  change (1 + u) * ((1 + u') * x * (1 - u')) * (1 - u) = (1 + (u + u')) * x * (1 - (u + u'))
  have hl : (1 + u) * (1 + u') = 1 + (u + u') := by noncomm_ring [h1]
  have hr : (1 - u') * (1 - u) = 1 - (u + u') := by noncomm_ring [h2]
  calc _ = ((1 + u) * (1 + u')) * x * ((1 - u') * (1 - u)) := by noncomm_ring
    _ = _ := by rw [hl, hr]

/-- Conjugation fixes every element commuting with `u`. -/
theorem unipotentConj_of_commute (hu : u * u = 0) {m : A} (h : Commute m u) :
    unipotentConj R u m = m := by
  rw [unipotentConj_apply, mul_assoc, ((Commute.one_right m).sub_right h).eq,
    ← mul_assoc, one_add_mul_one_sub hu, one_mul]

end Unipotent

section Tetraktys

variable {u v : A}

theorem unipotentConj_left_mass (hu : u * u = 0) :
    unipotentConj R u (u * v + v * u) = u * v + v * u :=
  unipotentConj_of_commute hu (mass_commute_left hu)

theorem unipotentConj_right_mass (hv : v * v = 0) :
    unipotentConj R v (u * v + v * u) = u * v + v * u :=
  unipotentConj_of_commute hv (mass_commute_right hv)

theorem unipotentConj_left_spin (hu : u * u = 0) :
    unipotentConj R u (u * v - v * u) = (u * v - v * u) - (2 : ℕ) • ((u * v + v * u) * u) := by
  rw [unipotentConj_apply, two_nsmul]
  noncomm_ring [hu, mul_mul_eq_zero_of_sq hu]

theorem unipotentConj_left_sum (hu : u * u = 0) :
    unipotentConj R u (u + v) = (u + v) + (u * v - v * u) - (u * v + v * u) * u := by
  rw [unipotentConj_apply]
  noncomm_ring [hu, mul_mul_eq_zero_of_sq hu]

end Tetraktys

/-! ### Weyl element and Steinberg braids -/

section Weyl

variable {u v : A}

/-- Weyl element `W = (u - v) + (1 - V)`. -/
def weyl (u v : A) : A := (u - v) + (1 - (u * v + v * u))

/-- Its partner `W' = -(u - v) + (1 - V)`. -/
def weylPartner (u v : A) : A := -(u - v) + (1 - (u * v + v * u))

/-- `B₊ = (1 + u)(1 - v)(1 + u)`. -/
def steinbergPlus (u v : A) : A := (1 + u) * (1 - v) * (1 + u)

/-- `B₋ = (1 - v)(1 + u)(1 - v)`. -/
def steinbergMinus (u v : A) : A := (1 - v) * (1 + u) * (1 - v)

variable (hu : u * u = 0) (hv : v * v = 0)
include hu hv

/-- Unitarity defect of the Weyl element: `W W' - 1 = V² - V`. -/
theorem weyl_mul_partner :
    weyl u v * weylPartner u v - 1 =
      (u * v + v * u) * (u * v + v * u) - (u * v + v * u) := by
  simp only [weyl, weylPartner]
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem partner_mul_weyl :
    weylPartner u v * weyl u v - 1 =
      (u * v + v * u) * (u * v + v * u) - (u * v + v * u) := by
  simp only [weyl, weylPartner]
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem weyl_commute_mass : Commute (weyl u v) (u * v + v * u) := by
  have h := ((mass_commute_difference hu hv).add_right
    ((Commute.one_right _).sub_right (Commute.refl _))).symm
  simpa only [weyl] using h

/-- `J` exchanges the two mass blocks: `J (u v) (-J) = (v u)²`. -/
theorem difference_conj_upper_block :
    (u - v) * (u * v) * -(u - v) = v * u * (v * u) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem difference_conj_lower_block :
    (u - v) * (v * u) * -(u - v) = u * v * (u * v) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem sum_conj_upper_block : (u + v) * (u * v) * (u + v) = v * u * (v * u) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem sum_conj_lower_block : (u + v) * (v * u) * (u + v) = u * v * (u * v) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

omit hu hv in
/-- Corrected Steinberg decomposition: `B₊ = W + (1 - V) u`. -/
theorem steinbergPlus_eq (hu : u * u = 0) :
    steinbergPlus u v = weyl u v + (1 - (u * v + v * u)) * u := by
  simp only [steinbergPlus, weyl]
  noncomm_ring [hu, mul_mul_eq_zero_of_sq hu]

omit hu hv in
/-- Dual Steinberg decomposition: `B₋ = W - (1 - V) v`. -/
theorem steinbergMinus_eq (hv : v * v = 0) :
    steinbergMinus u v = weyl u v - (1 - (u * v + v * u)) * v := by
  simp only [steinbergMinus, weyl]
  noncomm_ring [hv, mul_mul_eq_zero_of_sq hv]

theorem steinbergPlus_sub_minus :
    steinbergPlus u v - steinbergMinus u v = (1 - (u * v + v * u)) * (u + v) := by
  rw [steinbergPlus_eq hu, steinbergMinus_eq hv]; noncomm_ring

theorem steinbergPlus_add_minus :
    steinbergPlus u v + steinbergMinus u v =
      (2 : ℕ) • weyl u v + (1 - (u * v + v * u)) * (u - v) := by
  rw [steinbergPlus_eq hu, steinbergMinus_eq hv, two_nsmul]; noncomm_ring

/-- `B₊` is a unit: it is a product of three unipotent units. -/
def steinbergPlusUnit : Aˣ :=
  unipotentUnit u hu * unipotentUnit (-v) (by rw [neg_mul_neg, hv]) * unipotentUnit u hu

theorem steinbergPlusUnit_val : (steinbergPlusUnit hu hv : A) = steinbergPlus u v := by
  simp [steinbergPlusUnit, steinbergPlus, sub_eq_add_neg]

/-- `B₋` is a unit. -/
def steinbergMinusUnit : Aˣ :=
  unipotentUnit (-v) (by rw [neg_mul_neg, hv]) * unipotentUnit u hu *
    unipotentUnit (-v) (by rw [neg_mul_neg, hv])

theorem steinbergMinusUnit_val : (steinbergMinusUnit hu hv : A) = steinbergMinus u v := by
  simp [steinbergMinusUnit, steinbergMinus, sub_eq_add_neg]

end Weyl

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
