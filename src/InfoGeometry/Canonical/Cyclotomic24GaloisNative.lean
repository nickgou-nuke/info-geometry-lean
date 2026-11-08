/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import Mathlib.GroupTheory.Exponent
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Native Galois group of the 24th cyclotomic field

The Galois group over `ℚ` is identified with `(ZMod 24)ˣ`.  The concrete
finite-group facts below establish order eight, commutativity, and exponent
two without conflating this arithmetic action with an operator symmetry.
-/

namespace InfoGeometry.Canonical.Cyclotomic24GaloisNative

noncomputable section

local instance : NeZero (24 : ℚ) := ⟨by norm_num⟩

local instance : IsCyclotomicExtension {24} ℚ (CyclotomicField 24 ℚ) := by
  exact CyclotomicField.isCyclotomicExtension 24 ℚ

abbrev Cyclotomic24Field := CyclotomicField 24 ℚ
abbrev Cyclotomic24Group := Gal(Cyclotomic24Field / ℚ)

/-- The native cyclotomic Galois action is the unit group modulo 24. -/
def cyclotomic24_galEquivUnits : Cyclotomic24Group ≃* (ZMod 24)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod 24 Cyclotomic24Field

/-- The native Galois action on any 24th root of unity is the power action
indexed by the corresponding unit modulo twenty-four. -/
theorem cyclotomic24_gal_action_on_root_of_unity
    (σ : Cyclotomic24Group) {x : Cyclotomic24Field} (hx : x ^ 24 = 1) :
    σ x = x ^ (cyclotomic24_galEquivUnits σ).val.val := by
  exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
    24 Cyclotomic24Field σ hx

/-- The Chinese remainder decomposition separates the 24th cyclotomic
Galois group into its 8-part and 3-part unit groups. -/
def cyclotomic24_galEquivCrt :
    Cyclotomic24Group ≃* (ZMod 8)ˣ × (ZMod 3)ˣ := by
  let hcrt : ZMod 24 ≃+* ZMod 8 × ZMod 3 :=
    ZMod.chineseRemainder (by norm_num : Nat.Coprime 8 3)
  exact cyclotomic24_galEquivUnits.trans <|
    (Units.mapEquiv hcrt.toMulEquiv).trans (MulEquiv.prodUnits)

/-- The 8-primary CRT factor is itself a Klein-four group. -/
theorem zmod8_units_sq_one (u : (ZMod 8)ˣ) : u ^ 2 = 1 := by
  fin_cases u <;> decide

theorem zmod8_units_isKleinFour : IsKleinFour (ZMod 8)ˣ := by
  refine IsKleinFour.mk ?_ ?_
  · simpa [Nat.card_eq_fintype_card] using
      (show Fintype.card (ZMod 8)ˣ = 4 by decide)
  · apply le_antisymm
    · apply Nat.le_of_dvd (by decide)
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr zmod8_units_sq_one
    · have hnotone : Monoid.exponent (ZMod 8)ˣ ≠ 1 := by
        intro h
        let u3 : (ZMod 8)ˣ := Units.mkOfMulEqOne (3 : ZMod 8) 3 (by decide)
        have hu3 : u3 ≠ 1 := by
          intro hu
          have hval : (3 : ZMod 8) = 1 := by
            simpa [u3] using congrArg Units.val hu
          exact (by decide : (3 : ZMod 8) ≠ 1) hval
        exact hu3 (by simpa [h] using Monoid.pow_exponent_eq_one u3)
      have hpos : 0 < Monoid.exponent (ZMod 8)ˣ := by
        exact Monoid.exponent_pos.mpr ⟨2, by decide, zmod8_units_sq_one⟩
      have hdiv : Monoid.exponent (ZMod 8)ˣ ∣ 2 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr zmod8_units_sq_one
      omega

/-- The 3-primary CRT factor has exactly two elements. -/
theorem zmod3_units_card : Fintype.card (ZMod 3)ˣ = 2 := by
  decide

/-- The 8-part of the CRT decomposition as a product of two cyclic groups
of order two. -/
noncomputable def zmod8_units_equiv_c2_pair :
    (ZMod 8)ˣ ≃* Multiplicative (ZMod 2 × ZMod 2) := by
  letI : IsKleinFour (ZMod 8)ˣ := zmod8_units_isKleinFour
  exact Classical.choice (IsKleinFour.nonempty_mulEquiv
    (G₁ := (ZMod 8)ˣ) (G₂ := Multiplicative (ZMod 2 × ZMod 2)))

/-- The 3-part of the CRT decomposition is cyclic of order two. -/
noncomputable def zmod3_units_equiv_c2 :
    (ZMod 3)ˣ ≃* Multiplicative (ZMod 2) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact mulEquivOfPrimeCardEq
    (by simpa [Nat.card_eq_fintype_card] using zmod3_units_card)
    (by
      classical
      rw [Nat.card_eq_fintype_card]
      decide)

/-- Explicit `C₂ × C₂ × C₂` model for the 24th cyclotomic Galois group.
The first factor is the Klein-four group, represented as the multiplicative
group of the additive group `ZMod 2 × ZMod 2`; the second factor is one more
copy of `C₂`. -/
noncomputable def cyclotomic24_galEquivC2Cube :
    Cyclotomic24Group ≃* (Multiplicative (ZMod 2 × ZMod 2) × Multiplicative (ZMod 2)) :=
  cyclotomic24_galEquivCrt.trans
    (MulEquiv.prodCongr zmod8_units_equiv_c2_pair zmod3_units_equiv_c2)

/-- There are eight automorphisms in the 24th cyclotomic Galois group. -/
theorem cyclotomic24_gal_card : Nat.card Cyclotomic24Group = 8 := by
  simpa [Nat.card_eq_fintype_card] using
    (Fintype.card_congr cyclotomic24_galEquivUnits.toEquiv).trans
      (show Fintype.card (ZMod 24)ˣ = 8 by decide)

/-- Every unit modulo 24 is an involution. -/
theorem zmod24_units_sq_one (u : (ZMod 24)ˣ) : u ^ 2 = 1 := by
  fin_cases u <;> decide

/-- The exponent of the 24th cyclotomic Galois group is exactly two. -/
theorem cyclotomic24_gal_exponent : Monoid.exponent Cyclotomic24Group = 2 := by
  rw [Monoid.exponent_eq_of_mulEquiv cyclotomic24_galEquivUnits]
  apply le_antisymm
  · apply Nat.le_of_dvd (by decide)
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro u
    exact zmod24_units_sq_one u
  · have hnotone : Monoid.exponent (ZMod 24)ˣ ≠ 1 := by
      intro h
      let u5 : (ZMod 24)ˣ := Units.mkOfMulEqOne (5 : ZMod 24) 5 (by decide)
      have hu5 : u5 ≠ 1 := by
        intro hu
        have hval : (5 : ZMod 24) = 1 := by
          simpa [u5] using congrArg Units.val hu
        exact (by decide : (5 : ZMod 24) ≠ 1) hval
      exact hu5 (by simpa [h] using Monoid.pow_exponent_eq_one u5)
    have hpos : 0 < Monoid.exponent (ZMod 24)ˣ := by
      exact Monoid.exponent_pos.mpr ⟨2, by decide, zmod24_units_sq_one⟩
    have hdiv : Monoid.exponent (ZMod 24)ˣ ∣ 2 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr zmod24_units_sq_one
    omega

/-- The Galois group is abelian, as witnessed by its equivalence to the unit
group of the commutative ring `ZMod 24`. -/
theorem cyclotomic24_gal_commutative (σ τ : Cyclotomic24Group) :
    σ * τ = τ * σ := by
  apply cyclotomic24_galEquivUnits.injective
  simp [map_mul, mul_comm]

end
end InfoGeometry.Canonical.Cyclotomic24GaloisNative
