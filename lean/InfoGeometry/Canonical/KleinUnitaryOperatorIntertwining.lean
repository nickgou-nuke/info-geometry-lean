import proofs.KleinOperatorAlgebraBundleCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import proofs.KleinSixStateVectorBundleCore

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
open KleinSixStateBundle
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
  unfold operatorDeckMap deckFiberMap
  split_ifs with hg
  · simp
  · have hg' : g = 1 := by
      fin_cases g <;> simp_all
    subst g
    change (theta * A * theta).mulVec (theta.mulVec v) =
      theta.mulVec (A.mulVec v)
    have htheta : theta.mulVec (theta.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, theta_sq omega homega]
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
