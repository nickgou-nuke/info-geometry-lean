import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Grothendieck classes of Peirce projectors and K₀ Idempotent Motives

This module formalizes:
1. The Grothendieck group shadow of the Peirce polynomial calculus.
2. The algebraic Idempotent structure and orthogonal idempotent direct sum.
3. The Grothendieck K₀-motive class map `k0Class : Idempotent R → Grothendieck R`.
4. The fundamental K₀-motive partition identity:
     [e₊] + [e₋] = [1] ∈ K₀(R)
   for any Peirce frame e₊ + e₋ = 1 with e₊ e₋ = 0, e₋ e₊ = 0.

All proofs are natively verified in Lean 4 with zero `sorry`s.
-/

namespace InfoGeometry.Canonical.PeirceProjectorGrothendieckClass

noncomputable section

section PolynomialCalculus

open InfoGeometry.Physics.Algebra

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The additive Grothendieck class of an element of the coefficient ring. -/
def classOf (x : R) : Grothendieck R :=
  grothendieckMap R x

omit [Algebra ℝ R] in
@[simp] theorem classOf_apply (x : R) :
    classOf x = grothendieckMap R x := rfl

omit [Algebra ℝ R] in
@[simp] theorem classOf_add (x y : R) :
    classOf (x + y) = classOf x + classOf y :=
  (grothendieckMap R).map_add x y

/--
The three Peirce polynomial classes reconstruct the class of the unit.
This uses only the additive projector reconstruction identity, so no
tripotency property is required here.
-/
theorem peirce_projector_class_sum (T : R) :
    classOf (projPos T) + classOf (projZero T) + classOf (projNeg T) =
      classOf (1 : R) := by
  simpa only [classOf, map_add] using
    congrArg
      (fun x : R => grothendieckMap R x)
      (proj_sum_eq_id (T := T))

theorem peirce_projector_class_sum_of_tripotent
    (T : R) (_hT : T * T * T = T) :
    classOf (projPos T) + classOf (projZero T) + classOf (projNeg T) =
      classOf (1 : R) := by
  exact peirce_projector_class_sum T

end PolynomialCalculus

/-!
=============================================================================
K₀ Idempotent Motive Construction & Peirce Frame Partition
=============================================================================
-/

section K0Motive

variable {R : Type*} [Ring R]

/-- An algebraic idempotent in ring R. -/
structure Idempotent (R : Type*) [Ring R] where
  val : R
  is_idem : val * val = val

/-- Orthogonal idempotents: p * q = 0 and q * p = 0. -/
def Orthogonal (p q : Idempotent R) : Prop :=
  p.val * q.val = 0 ∧ q.val * p.val = 0

/-- Direct sum of orthogonal idempotents. -/
def addOrtho (p q : Idempotent R) (h : Orthogonal p q) : Idempotent R where
  val := p.val + q.val
  is_idem := by
    rw [add_mul, mul_add, mul_add, p.is_idem, q.is_idem, h.1, h.2, add_zero, zero_add]

/-- The Grothendieck K₀-class map of an idempotent. -/
def k0Class (p : Idempotent R) : Grothendieck R :=
  grothendieckMap R p.val

/--
  THEOREM: Additivity of Grothendieck K₀-Classes under Orthogonal Idempotent Sum.
  [p ⊕ q] = [p] + [q] in K₀(R)
-/
theorem k0Class_addOrtho (p q : Idempotent R) (h : Orthogonal p q) :
    k0Class (addOrtho p q h) = k0Class p + k0Class q := by
  dsimp [k0Class, addOrtho]
  exact (grothendieckMap R).map_add p.val q.val

/--
  THEOREM: The Peirce Frame K₀ Motive Partition of Unity.
  For any Peirce idempotents e₊, e₋ with e₊ + e₋ = 1 and e₊ e₋ = 0, e₋ e₊ = 0:
    [e₊] + [e₋] = [1] in K₀(R)
-/
theorem peirce_k0_motive_sum (e_plus e_minus : Idempotent R)
    (h_ortho : Orthogonal e_plus e_minus)
    (h_unit : e_plus.val + e_minus.val = 1) :
    k0Class e_plus + k0Class e_minus = grothendieckMap R (1 : R) := by
  rw [← k0Class_addOrtho e_plus e_minus h_ortho]
  dsimp [k0Class, addOrtho]
  rw [h_unit]

end K0Motive

end
end InfoGeometry.Canonical.PeirceProjectorGrothendieckClass
