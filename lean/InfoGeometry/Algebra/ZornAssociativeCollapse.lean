/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.AssociativityObstruction
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Associative images of the native Zorn product vanish

An additive map from `ZornVectorMatrix R` to an associative ring that preserves
the ordered native Zorn product is zero. The proof uses the existing explicit
associator of `U 0`, `U 1`, and `U 2`. That associator squares to the native unit.
Associativity of the target therefore kills the unit, and then every element.

No simplicity theorem or injectivity hypothesis is needed. The coefficient
ring may be any commutative ring; the target need not be commutative or unital.
For a nontrivial unital target there is consequently no *unital additive*
multiplicative map. The zero map remains a nonunital example.

The native nonassociative product remains explicit throughout. These results
do not prohibit injective linear maps, left multiplication operators, or Lie
representations of the derivation algebra.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R A : Type*} [CommRing R]

/-- The existing three-upper-vector associator is an involution. -/
theorem basis_associator_mul_self :
    mul (associator (U 0 : ZornVectorMatrix R) (U 1) (U 2))
      (associator (U 0 : ZornVectorMatrix R) (U 1) (U 2)) = one := by
  rw [associator_U_zero_U_one_U_two]
  ext i <;> simp [mul, sub, add, neg, E22, E11, one, ZornVec3.dot,
    ZornVec3.cross]

section AssociativeTarget

variable [NonUnitalRing A]

/-- An additive multiplicative map to an associative target annihilates every
native Zorn associator. -/
theorem additiveMap_associator_eq_zero
    (f : ZornVectorMatrix R →+ A)
    (hmul : ∀ X Y, f (mul X Y) = f X * f Y)
    (X Y Z : ZornVectorMatrix R) : f (associator X Y Z) = 0 := by
  letI : Mul (ZornVectorMatrix R) := ⟨mul⟩
  change f (mul (mul X Y) Z - mul X (mul Y Z)) = 0
  rw [map_sub]
  apply _root_.sub_eq_zero.mpr
  exact InfoGeometry.Algebra.multiplicative_map_identifies_associativity_paths
    f hmul X Y Z

/-- The involutive associator forces the native unit to vanish in every
associative additive multiplicative image. -/
theorem additiveMap_one_eq_zero
    (f : ZornVectorMatrix R →+ A)
    (hmul : ∀ X Y, f (mul X Y) = f X * f Y) : f one = 0 := by
  let J := associator (U 0 : ZornVectorMatrix R) (U 1) (U 2)
  have hJ : f J = 0 := additiveMap_associator_eq_zero f hmul _ _ _
  have hJsq : mul J J = one := basis_associator_mul_self
  calc
    f one = f (mul J J) := congrArg f hJsq.symm
    _ = f J * f J := hmul J J
    _ = 0 := by rw [hJ, _root_.zero_mul]

/-- Every additive map preserving the ordered native Zorn product into an
associative ring is zero. -/
theorem additiveMap_eq_zero_of_multiplicative
    (f : ZornVectorMatrix R →+ A)
    (hmul : ∀ X Y, f (mul X Y) = f X * f Y) : f = 0 := by
  ext X
  change f X = 0
  calc
    f X = f (mul one X) := congrArg f (one_mul X).symm
    _ = f one * f X := hmul one X
    _ = 0 := by rw [additiveMap_one_eq_zero f hmul, _root_.zero_mul]

/-- In particular, an `R`-linear multiplicative map has zero underlying linear
map. No compatibility between target scalar multiplication and multiplication
is needed for this stronger additive obstruction. -/
theorem linearMap_eq_zero_of_multiplicative [Module R A]
    (f : ZornVectorMatrix R →ₗ[R] A)
    (hmul : ∀ X Y, f (mul X Y) = f X * f Y) : f = 0 := by
  have hf := additiveMap_eq_zero_of_multiplicative f.toAddMonoidHom hmul
  ext X
  exact congrArg (fun g : ZornVectorMatrix R →+ A => g X) hf

end AssociativeTarget

/-- A nontrivial associative unital ring receives no additive map that
preserves both the native Zorn product and the native unit. -/
theorem no_unital_additive_multiplicative_map [Ring A] [Nontrivial A] :
    ¬ ∃ f : ZornVectorMatrix R →+ A,
      (∀ X Y, f (mul X Y) = f X * f Y) ∧ f one = 1 := by
  rintro ⟨f, hmul, hone⟩
  have hz := additiveMap_one_eq_zero f hmul
  exact one_ne_zero (hone.symm.trans hz)

end InfoGeometry.Algebra.ZornVectorMatrix
