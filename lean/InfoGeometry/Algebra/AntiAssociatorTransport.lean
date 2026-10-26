/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing

/-!
# Alternating associators under additive anti-automorphisms

The reversal statement applies to nonassociative multiplication. It neither
constructs a Tomita--Takesaki conjugation nor identifies a Zorn coordinate
permutation with an anti-automorphism.
-/

namespace InfoGeometry.Algebra.AntiAssociatorTransport

variable {A : Type*} [AddCommGroup A] [Mul A]

def assoc (x y z : A) : A := (x * y) * z - x * (y * z)

/-- Binary order reversal induces the negative of the reversed associator. -/
theorem map_assoc_reverse (J : A →+ A)
    (hanti : ∀ x y : A, J (x * y) = J y * J x)
    (x y z : A) :
    J (assoc x y z) = -assoc (J z) (J y) (J x) := by
  simp only [assoc, map_sub, hanti]
  abel

/-- Alternation supplies the second minus sign. -/
theorem map_assoc_of_reverse_alternating (J : A →+ A)
    (hanti : ∀ x y : A, J (x * y) = J y * J x)
    (halt : ∀ x y z : A, assoc z y x = -assoc x y z)
    (x y z : A) :
    J (assoc x y z) = assoc (J x) (J y) (J z) := by
  rw [map_assoc_reverse J hanti, halt, neg_neg]

end InfoGeometry.Algebra.AntiAssociatorTransport
