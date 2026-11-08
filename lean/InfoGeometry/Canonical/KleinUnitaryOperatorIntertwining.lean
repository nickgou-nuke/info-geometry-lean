import InfoGeometry.Topology.KleinOperatorAlgebraBundleCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Vector/operator intertwining for the Klein six-state bundle

The vector fibre and the operator-algebra fibre use the same native
`Fin 2 × Fin 3` carrier.  This file records the exact intertwining identity
between the deck action on vectors and inner conjugation on matrices.
-/

noncomputable section
namespace InfoGeometry.Canonical.KleinUnitaryOperatorIntertwining

open KleinSixStateVectorBundleCore
open KleinOperatorAlgebraBundleCore
open KleinOperatorAlgebraAssociatedQuotient
open InfoGeometry.Canonical.KleinSixStateBundle
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas

abbrev State := KleinSixStateVectorBundleCore.State
abbrev Op := KleinOperatorAlgebraBundleCore.Op
abbrev Base := KleinSixStateVectorBundleCore.Base

theorem operatorGlide_mulVec (A : Op) (v : State) :
    (operatorGlide A).mulVec v = theta.mulVec (A.mulVec (theta.mulVec v)) := by
  unfold operatorGlide
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem operatorDeckMap_mulVec (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (g : Deck2) (A : Op) (v : State) :
    (operatorDeckMap g A).mulVec (deckFiberMap g v) =
      deckFiberMap g (A.mulVec v) := by
  have hcases (z : Deck2) : z = 0 ∨ z = 1 := by
    have hz : z.val < 2 := z.isLt
    have hval : z.val = 0 ∨ z.val = 1 := by omega
    rcases hval with hzero | hone
    · exact Or.inl ((ZMod.val_eq_zero z).mp hzero)
    · exact Or.inr ((ZMod.val_eq_one (by decide) z).mp hone)
  rcases hcases g with rfl | rfl
  · simp [operatorDeckMap, deckFiberMap]
  · have h10 : (1 : Deck2) ≠ 0 := by decide
    simp only [operatorDeckMap, deckFiberMap, if_neg h10]
    change (theta * A * theta).mulVec (theta.mulVec v) =
      theta.mulVec (A.mulVec v)
    have htheta : theta.mulVec (theta.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← pow_two, theta_sq]
      simp
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [htheta]

theorem operatorCoordChange_mulVec (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (i j x : Base) (A : Op) (v : State) :
    (operatorCoordChange i j x A).mulVec
        (deckFiberMap (deckTransition i j x) v) =
      deckFiberMap (deckTransition i j x) (A.mulVec v) := by
  exact operatorDeckMap_mulVec omega homega _ _ _

theorem operator_vector_transition_intertwining (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (i j x : Base) (A : Op) (v : State) :
    (operatorCoordChange i j x A).mulVec
        ((kleinSixStateVectorBundleCore omega homega).coordChange i j x v) =
      (kleinSixStateVectorBundleCore omega homega).coordChange i j x
        (A.mulVec v) := by
  exact operatorCoordChange_mulVec omega homega i j x A v

theorem operatorCoordChange_mul (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (i j x : Base) (A B : Op) :
    operatorCoordChange i j x (A * B) =
      operatorCoordChange i j x A * operatorCoordChange i j x B :=
  KleinOperatorAlgebraBundleCore.operatorCoordChange_mul omega homega i j x A B

end InfoGeometry.Canonical.KleinUnitaryOperatorIntertwining
end noncomputable section
