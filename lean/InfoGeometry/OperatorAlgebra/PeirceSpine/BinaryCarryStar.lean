/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.BinaryCarry
import InfoGeometry.Algebra.QuarticRotor

/-!
# Star-compatible binary carry and normalized quartic rotor

A self-adjoint Peirce cut and flip, together with a skew-adjoint carried
element, identify the algebraic carry inverse with its actual star. The
result is proved from the primitive operators' star laws; an inner
conjugation formula alone would not supply this conclusion.

Combining these star identities with the existing carry power and
commutation theorems gives an element of Mathlib's `unitary B`. The
normalized quartic rotor requires `2` to be invertible, but the carry's own
unitarity does not. All statements use an arbitrary associative star ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]
variable {p f a : B}

/-- The primitive star laws identify the algebraic inverse expression with
the star of the carry. This calculation needs no square or normalization law. -/
theorem star_binaryCarry
    (hswap : f * p = (1 - p) * f) (hap : Commute a p) (haf : Commute a f)
    (hpstar : star p = p) (hfstar : star f = f) (hastar : star a = -a) :
    star (binaryCarry p f a) = binaryCarryInverse p f a := by
  have hswapc : f * (1 - p) = p * f := by
    calc
      f * (1 - p) = f - f * p := by rw [mul_sub, mul_one]
      _ = p * f := by rw [hswap]; noncomm_ring
  calc
    star (binaryCarry p f a) = f * p - f * a * (1 - p) := by
      simp only [binaryCarry, star_add, star_mul, star_sub, star_one,
        hpstar, hfstar, hastar]
      noncomm_ring
    _ = (1 - p) * f - a * (f * (1 - p)) := by
      rw [hswap, haf.eq.symm, mul_assoc]
    _ = (1 - p) * f - p * a * f := by
      rw [hswapc, ← mul_assoc, hap.eq]
    _ = binaryCarryInverse p f a := rfl

/-- For a square-negative carried element, the carry star is minus its cube. -/
theorem star_binaryCarry_eq_neg_cube
    (hp : p * p = p) (hf : f * f = 1)
    (hswap : f * p = (1 - p) * f) (hap : Commute a p) (haf : Commute a f)
    (ha : a * a = -1)
    (hpstar : star p = p) (hfstar : star f = f) (hastar : star a = -a) :
    star (binaryCarry p f a) = -(binaryCarry p f a ^ 3) :=
  (star_binaryCarry hswap hap haf hpstar hfstar hastar).trans
    (binaryCarryInverse_eq_neg_cube hp hf hswap hap haf ha)

/-- The star-compatible binary carry is a genuine unitary element, without
requiring division by `2`. -/
theorem binaryCarry_mem_unitary
    (hp : p * p = p) (hf : f * f = 1)
    (hswap : f * p = (1 - p) * f) (hap : Commute a p) (haf : Commute a f)
    (ha : a * a = -1)
    (hpstar : star p = p) (hfstar : star f = f) (hastar : star a = -a) :
    binaryCarry p f a ∈ unitary B := by
  constructor
  · rw [star_binaryCarry hswap hap haf hpstar hfstar hastar]
    exact binaryCarry_inverse_mul hp hf hswap hap haf ha
  · rw [star_binaryCarry hswap hap haf hpstar hfstar hastar]
    exact binaryCarry_mul_inverse hp hf hswap hap haf ha

/-- End-to-end normalized rotor unitarity from the primitive carry data and
local commutation of the bond operator with the cut, flip and carried element. -/
theorem binaryCarry_normalizedRotor_mem_unitary [Invertible (2 : B)] {X : B}
    (hp : p * p = p) (hf : f * f = 1)
    (hswap : f * p = (1 - p) * f) (hap : Commute a p) (haf : Commute a f)
    (ha : a * a = -1)
    (hpstar : star p = p) (hfstar : star f = f) (hastar : star a = -a)
    (hX4 : X ^ 4 = 1) (hXstar : star X = X ^ 3)
    (hpx : Commute p X) (hfx : Commute f X) (hax : Commute a X) :
    InfoGeometry.Algebra.QuarticRotor.normalizedRotor (binaryCarry p f a) X ∈ unitary B :=
  InfoGeometry.Algebra.QuarticRotor.normalizedRotor_mem_unitary
    (binaryCarry p f a) X
    (binaryCarry_pow_four hp hf hswap hap haf ha) hX4
    (binaryCarry_commute hpx hfx hax)
    (star_binaryCarry_eq_neg_cube hp hf hswap hap haf ha hpstar hfstar hastar) hXstar

end InfoGeometry.OperatorAlgebra.PeirceSpine
