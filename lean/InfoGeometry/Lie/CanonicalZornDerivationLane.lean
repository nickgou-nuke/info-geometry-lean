import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornDerivation
import Mathlib.Algebra.Lie.OfAssociative

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-!
# The canonical Zorn derivation lane

The Lie object attached to the canonical Zorn carrier is its native
Leibniz-derivation subalgebra.  This is deliberately an operator-level
realization: the Zorn carrier remains the module on which the lane acts.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.NonAssocDerivation

abbrev ZornCarrier := InfoGeometry.Canonical.ZornMatrix ℝ

/-- The canonical Zorn derivations, viewed as a faithful operator Lie lane. -/
noncomputable def canonicalZornDerivationLane :
    LieActionLane ℝ ZornCarrier where
  L := canonicalZornDerivations
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := canonicalZornDerivations.incl

@[simp] theorem canonicalZornDerivationLane_act (D : canonicalZornDerivations) :
    canonicalZornDerivationLane.act D = D.1 := by
  rfl

@[simp] theorem canonicalZornDerivationLane_operatorAction (D : canonicalZornDerivations)
    (X : ZornCarrier) :
    canonicalZornDerivationLane.operatorAction D X = D.1 X := by
  rfl

end InfoGeometry.Lie.CanonicalZornDerivation
