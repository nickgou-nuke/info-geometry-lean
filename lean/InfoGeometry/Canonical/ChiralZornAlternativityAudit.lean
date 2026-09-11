import InfoGeometry.Canonical.ChiralZornNonUnitalNonAssocRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralZornNCZornBridge
import InfoGeometry.Canonical.NCZornAlternativityAudit

/-!
# Alternativity audit for the chiral Zorn presentation

The coordinate bridge transports the existing BdG counterexamples from the
native `NCZornElement` presentation.  Thus the named non-associative ring
contract must not be strengthened to an alternative-algebra contract for this
operator-valued coefficient ring.
-/

namespace InfoGeometry.Canonical.ChiralZorn

open InfoGeometry.Physics.Octonion
open InfoGeometry.Physics.PalatialTwistor
open InfoGeometry.Canonical.ChiralZornNCZornBridge

abbrev bdgUpperTwo (a b : BdGBlockQ) : ChiralZornMatrix BdGBlockQ :=
  ofNC (InfoGeometry.Canonical.NCZorn.upperTwo a b)

abbrev bdgPureNPlus (d : BdGBlockQ) : ChiralZornMatrix BdGBlockQ :=
  ofNC (InfoGeometry.Physics.NCG.NCZornElement.pureNPlus d)

abbrev bdgPureNMinus (d : BdGBlockQ) : ChiralZornMatrix BdGBlockQ :=
  ofNC (InfoGeometry.Physics.NCG.NCZornElement.pureNMinus d)

private theorem ofNC_mul (X Y : InfoGeometry.Physics.NCG.NCZornElement BdGBlockQ) :
    ofNC (InfoGeometry.Physics.NCG.NCZornElement.mul X Y) =
      ChiralZornMatrix.mul (ofNC X) (ofNC Y) := by
  apply chiralZornEquivNC.injective
  simpa only [chiralZornEquivNC_apply, to_of] using
    (toNC_mul (ofNC X) (ofNC Y)).symm

theorem bdg_left_alternativity_fails :
    ChiralZornMatrix.mul
          (ChiralZornMatrix.mul (bdgUpperTwo matrixE12 matrixE21)
            (bdgUpperTwo matrixE12 matrixE21))
          (bdgPureNPlus 1) ≠
        ChiralZornMatrix.mul (bdgUpperTwo matrixE12 matrixE21)
          (ChiralZornMatrix.mul (bdgUpperTwo matrixE12 matrixE21)
            (bdgPureNPlus 1)) := by
  intro h
  apply InfoGeometry.Canonical.NCZorn.bdg_left_alternativity_fails
  repeat rw [← ofNC_mul] at h
  exact congrArg toNC h

theorem bdg_right_alternativity_fails :
    ChiralZornMatrix.mul
          (ChiralZornMatrix.mul (bdgPureNMinus 1)
            (bdgUpperTwo matrixE12 matrixE21))
          (bdgUpperTwo matrixE12 matrixE21) ≠
        ChiralZornMatrix.mul (bdgPureNMinus 1)
          (ChiralZornMatrix.mul (bdgUpperTwo matrixE12 matrixE21)
            (bdgUpperTwo matrixE12 matrixE21)) := by
  intro h
  apply InfoGeometry.Canonical.NCZorn.bdg_right_alternativity_fails
  repeat rw [← ofNC_mul] at h
  exact congrArg toNC h

theorem bdg_not_left_alternative :
    ¬ (∀ X Y : ChiralZornMatrix BdGBlockQ,
      ChiralZornMatrix.mul (ChiralZornMatrix.mul X X) Y =
        ChiralZornMatrix.mul X (ChiralZornMatrix.mul X Y)) := by
  intro h
  apply bdg_left_alternativity_fails
  exact h (bdgUpperTwo matrixE12 matrixE21) (bdgPureNPlus 1)

theorem bdg_not_right_alternative :
    ¬ (∀ X Y : ChiralZornMatrix BdGBlockQ,
      ChiralZornMatrix.mul (ChiralZornMatrix.mul Y X) X =
        ChiralZornMatrix.mul Y (ChiralZornMatrix.mul X X)) := by
  intro h
  apply bdg_right_alternativity_fails
  exact h (bdgUpperTwo matrixE12 matrixE21) (bdgPureNMinus 1)

end InfoGeometry.Canonical.ChiralZorn
