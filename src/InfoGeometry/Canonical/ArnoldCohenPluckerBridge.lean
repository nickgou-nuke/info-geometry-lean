import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.CommutingNilpotentSum

set_option linter.unusedSectionVars false

/-!
# Abstract Arnold Relation and Plücker Klein-Quadric Algebra

This module formalizes in native Lean 4 / Mathlib:
1. **An abstract exterior-algebra carrier** for three elements and their square-zero laws.
   It does not construct logarithmic differential forms on a configuration space.
2. **A separately assumed 3-Term Relation**:
   $$\omega_{12} \wedge \omega_{23} + \omega_{23} \wedge \omega_{31} + \omega_{31} \wedge \omega_{12} = 0$$
   The relation is an input to the algebraic rearrangement below; no BCFW recursion is proved.
3. **The Plücker Klein-quadric equation**:
   $$Q(p) = p_{12} p_{34} - p_{13} p_{24} + p_{14} p_{23} = 0$$
   Its zero locus characterizes decomposable bivectors in the repository's separate
   exterior-power owner. It is not the Minkowski mass shell.
4. The statements here do not identify the Arnold relation with a physical
   on-shell scattering or mass-shell condition.
-/

namespace InfoGeometry.Canonical.ArnoldCohenPluckerBridge

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

/-- The 6-dimensional Grassmannian $Gr(2,4)$ Plücker coordinate space. -/
structure PluckerCoordinates (R : Type*) [CommRing R] where
  p12 : R
  p13 : R
  p14 : R
  p23 : R
  p24 : R
  p34 : R

/-- The Klein Quadric polynomial $Q(p) = p_{12} p_{34} - p_{13} p_{24} + p_{14} p_{23}$. -/
def kleinQuadric (p : PluckerCoordinates R) : R :=
  p.p12 * p.p34 - p.p13 * p.p24 + p.p14 * p.p23

/-- A Plücker coordinate tuple is Klein-null when its Klein quadratic form vanishes. -/
def IsKleinNull (p : PluckerCoordinates R) : Prop :=
  kleinQuadric p = 0

/--
**Klein-quadric rearrangement**
Klein-nullity is equivalently written as the displayed coordinate equation.
-/
theorem kleinQuadric_factorization (p : PluckerCoordinates R) (h : IsKleinNull p) :
    p.p12 * p.p34 = p.p13 * p.p24 - p.p14 * p.p23 := by
  unfold IsKleinNull kleinQuadric at h
  linear_combination h

/-- The three-term relation on three explicitly supplied elements of the
exterior algebra. No generator record, square-zero side conditions, or
configuration-space interpretation is implicit in this predicate. -/
def ArnoldMixedRelation {V : Type*} [AddCommGroup V] [Module R V]
    (w12 w23 w31 : ExteriorAlgebra R V) : Prop :=
  w12 * w23 + w23 * w31 + w31 * w12 = 0

/-! The square-zero equations of two arbitrary exterior-algebra elements do
not by themselves imply that their sum is square-zero. The exact additional
condition is cancellation of the two cross-products. -/

theorem sum_sq_zero_iff_cross_terms_cancel
    {V : Type*} [AddCommGroup V] [Module R V]
    (A B : ExteriorAlgebra R V)
    (hA : A * A = 0) (hB : B * B = 0) :
    (A + B) * (A + B) = 0 ↔ A * B + B * A = 0 :=
  InfoGeometry.Algebra.CommutingNilpotentSum.add_sq_eq_zero_iff_cross_terms_cancel
    A B hA hB

/--
**Main Theorem 2: Arnold 3-Term Symmetry**
The Arnold mixed relation is invariant under cyclic permutation of terms.
-/
theorem arnold_relation_cyclic_invariant
    {V : Type*} [AddCommGroup V] [Module R V]
    (w12 w23 w31 : ExteriorAlgebra R V)
    (h_arnold : ArnoldMixedRelation w12 w23 w31) :
    w23 * w31 + w31 * w12 + w12 * w23 = 0 := by
  unfold ArnoldMixedRelation at h_arnold
  rw [add_comm (w23 * w31 + w31 * w12) (w12 * w23)]
  rw [← add_assoc]
  exact h_arnold

/--
Rearranging the assumed Arnold three-term relation expresses the first product
as the negative sum of the other two. This is an algebraic consequence of the
relation only; it does not state BCFW recursion, a pole residue, or on-shell
factorization.
-/
theorem arnold_relation_rearrange_w12_w23
    {V : Type*} [AddCommGroup V] [Module R V]
    (w12 w23 w31 : ExteriorAlgebra R V)
    (h_arnold : ArnoldMixedRelation w12 w23 w31) :
    w12 * w23 = - (w23 * w31 + w31 * w12) := by
  rw [← add_eq_zero_iff_eq_neg]
  rw [← add_assoc]
  exact h_arnold

end InfoGeometry.Canonical.ArnoldCohenPluckerBridge
