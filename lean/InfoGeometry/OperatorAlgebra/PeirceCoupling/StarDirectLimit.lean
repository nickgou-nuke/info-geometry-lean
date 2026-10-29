/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.StarReflection
import InfoGeometry.Core.DualSeedCartan
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Star-compatible transport into the native noncommutative direct limit

Bonding maps are actual star-ring homomorphisms. Mathlib constructs the star
on the quotient. No positive order, norm completion, or analytic gap is
inferred from the quotient's algebraic star structure.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling.StarDirectLimit

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.DualSeedPeirce

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {A : I → Type*} [∀ i, Ring (A i)] [∀ i, StarRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆+* A j)
variable [DirectedSystem A (fun i j hij => f i j hij)]

/-- The star of the quotient is constructed, not supplied as a witness field. -/
theorem of_star (i : I) (x : A i) :
    DirectLimit.Ring.of A f i (star x) = star (DirectLimit.Ring.of A f i x) := rfl

theorem of_reflection (i : I) (p : A i) :
    DirectLimit.Ring.of A f i (reflection p) =
      reflection (DirectLimit.Ring.of A f i p) := by
  simp only [reflection, map_sub, map_mul, map_ofNat, map_one]

theorem of_forward_corner (i : I) (p a : A i) :
    DirectLimit.Ring.of A f i (component10 p a) =
      component10 (DirectLimit.Ring.of A f i p) (DirectLimit.Ring.of A f i a) := by
  simp only [component10, complementIdempotent, map_mul, map_sub, map_one]

/-- Reflection intertwines the actual quotient inclusions. -/
theorem of_starReflection (i : I) (p x : A i) :
    DirectLimit.Ring.of A f i (reflection p * star x * reflection p) =
      reflection (DirectLimit.Ring.of A f i p) *
        star (DirectLimit.Ring.of A f i x) *
          reflection (DirectLimit.Ring.of A f i p) := by
  simp only [map_mul, of_reflection, of_star]

/-- The two-sided Gram expression is preserved, without adding an order on the limit. -/
theorem of_gram (i : I) (x : A i) :
    DirectLimit.Ring.of A f i (x * star x + star x * x) =
      DirectLimit.Ring.of A f i x * star (DirectLimit.Ring.of A f i x) +
        star (DirectLimit.Ring.of A f i x) * DirectLimit.Ring.of A f i x := by
  simp only [map_add, map_mul, of_star]

/-- A nonzero reflexive adjoint pair gives a native triple in the star colimit. -/
theorem adjoint_cartan_of
    (hf : ∀ i j hij, Function.Injective (f i j hij))
    {i : I} {d : A i} (h : IsDualSeedPair d (star d)) (hd : d ≠ 0) :
    IsSl2Triple
      (phasePolarization (DirectLimit.Ring.of A f i d)
        (star (DirectLimit.Ring.of A f i d)))
      (DirectLimit.Ring.of A f i d) (star (DirectLimit.Ring.of A f i d)) := by
  rw [← of_star f i d]
  exact h.isSl2Triple_map hd (DirectLimit.Ring.of A f i)
    (DirectLimit.mk_injective f hf i)

end InfoGeometry.OperatorAlgebra.PeirceCoupling.StarDirectLimit
