import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.Meta.Architecture

/-!
# SuperMetriplectic Entropy/Shadow Bridge

Small theorem-backed bridge from the conservative scalar Schur/Drazin/entropy
shadow packets into nearby repo-owned projector/anomaly and entropy-split laws.

This file remains explicitly scalar/body-level. It does not reconstruct the
operator-owner inverse kernel. It only shows that the hidden scalar block obeys
exactly the same mismatch/anomaly identities as the owner Moore-Penrose/Drazin
lane, and that the body-entropy packet can be re-read as a coadjoint-leaf style
split with zero reversible contribution.
-/

namespace InfoGeometry.SuperMetriplectic.EntropyShadowBridge

open InfoGeometry.Canonical

/--
On the hidden scalar block, vanishing projector mismatch is exactly projector
agreement, via the repo-owned Moore-Penrose/Drazin identity.
-/
@[rep_depth transport]
theorem hiddenBlock_projectorMismatch_eq_zero_iff
    (B : InfoGeometry.SuperMetriplectic.ScalarSchurDrazinBlock) :
    MoorePenrose.projectorMismatch B.LΘΘ B.drazin.aD B.penrose.aPlus = 0 ↔
      MoorePenrose.spectralProjector B.LΘΘ B.drazin.aD
        = MoorePenrose.metricProjector B.LΘΘ B.penrose.aPlus := by
  exact MoorePenrose.projectorMismatch_eq_zero_iff

/--
On the hidden scalar block, vanishing mismatch kills the scalar chiral anomaly,
again by the repo-owned mismatch/anomaly law.
-/
@[rep_depth transport]
theorem hiddenBlock_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero
    (B : InfoGeometry.SuperMetriplectic.ScalarSchurDrazinBlock)
    (hΔ : MoorePenrose.projectorMismatch B.LΘΘ B.drazin.aD B.penrose.aPlus = 0) :
    MoorePenrose.chiralAnomaly B.LΘΘ B.drazin.aD B.penrose.aPlus = 0 := by
  exact MoorePenrose.chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero hΔ

/--
Body-level entropy production packet re-read as a coadjoint-leaf entropy split:
all entropy change is transverse, with zero reversible contribution.
-/
@[rep_depth transport]
def toCoadjointLeafEntropySplit
    (E : InfoGeometry.SuperMetriplectic.BodyEntropyProduction) :
    InfoGeometry.SuperMetriplectic.CoadjointLeafEntropySplit where
  leafEntropyChange := 0
  transverseEntropyProduction := E.production
  totalEntropyChange := E.production
  leafEntropyChange_eq_zero := rfl
  transverseEntropyProduction_nonnegative := E.production_nonneg
  totalEntropyChange_eq_leaf_plus_transverse := by simp

@[rep_depth transport]
theorem toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction
    (E : InfoGeometry.SuperMetriplectic.BodyEntropyProduction) :
    (toCoadjointLeafEntropySplit E).totalEntropyChange = E.production := by
  rfl

end InfoGeometry.SuperMetriplectic.EntropyShadowBridge
