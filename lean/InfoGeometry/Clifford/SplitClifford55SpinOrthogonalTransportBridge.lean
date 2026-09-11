import InfoGeometry.Clifford.SplitClifford55SpinActionTransportBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittSpinOrthogonalAction

/-!
# Transport of the native orthogonal Spin action to the Chevalley carrier

This owner transports the already constructed native hom
`Spin55 →* orthogonalGroup55` along the existing Chevalley/neutral Spin
equivalence.  It records only the resulting representation and its vector
readback; it adds no surjectivity, kernel, covering, or physical claim.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge

open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.SplitClifford55SpinActionTransportBridge
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Clifford55

abbrev Neutral55 := SplitClifford55NeutralFormBridge.Neutral55
abbrev ChevalleySpin55 := SplitClifford55NeutralFormBridge.ChevalleySpin55

noncomputable def transportedSpinActionOrthogonal :
    ChevalleySpin55 →* Clifford55.orthogonalGroup55 :=
  Clifford55.spinActionOrthogonalHom.comp spinGroupTransportEquiv.toMonoidHom

@[simp] theorem transportedSpinActionOrthogonal_apply
    (g : ChevalleySpin55) :
    transportedSpinActionOrthogonal g =
      Clifford55.spinActionOrthogonal (spinGroupTransportEquiv g) := by
  change Clifford55.spinActionOrthogonalHom (spinGroupTransportEquiv g) = _
  exact Clifford55.spinActionOrthogonalHom_apply _

theorem transportedSpinActionOrthogonal_readback
    (g : ChevalleySpin55) (x : Neutral55) :
    Clifford55.orthogonalGroup55IsometryEquiv
        (transportedSpinActionOrthogonal g) (neutralToV55 x) =
      neutralToV55 (transportedSpinAction g x) := by
  rw [transportedSpinActionOrthogonal_apply]
  change spinAction (spinGroupTransportEquiv g) (neutralToV55 x) =
    neutralToV55 (neutralToV55.symm
      (spinAction (spinGroupTransportEquiv g) (neutralToV55 x)))
  rw [neutralToV55.apply_symm_apply]

end InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
