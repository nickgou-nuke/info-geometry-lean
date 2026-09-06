import InfoGeometry.Physics.ThreeColorSL3ZornAction

/-!
# Three-color `SL₃` Zorn action bridge

Canonical re-export of the conditional three-color `SL₃` covariance layer.
This bridge does not add a new multiplicativity theorem; it only forwards the
verified physics owner.
-/

namespace InfoGeometry.Canonical.ThreeColorSL3ZornActionBridge

open InfoGeometry.Physics.ThreeColorSL3ZornAction

abbrev ColourVector := InfoGeometry.Physics.ThreeColorSL3ZornAction.ColourVector
abbrev Zorn := InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn

noncomputable abbrev colourFundamentalAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction g

noncomputable abbrev colourFundamentalActionLinear
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalActionLinear g

noncomputable abbrev colourDualAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction g

noncomputable abbrev colourDualActionLinear
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualActionLinear g

theorem continuous_colourFundamentalAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Continuous (colourFundamentalAction g) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.continuous_colourFundamentalAction g

theorem continuous_colourDualAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Continuous (colourDualAction g) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.continuous_colourDualAction g

noncomputable abbrev zornSL3Action
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action g

theorem zornSL3Action_mul_of_covariant
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hpair : InfoGeometry.Physics.ThreeColorSL3ZornAction.PreservesPairing g)
    (hcross : InfoGeometry.Physics.ThreeColorSL3ZornAction.PreservesCrossFundamental g)
    (hdualCross : InfoGeometry.Physics.ThreeColorSL3ZornAction.PreservesDualCross g)
    (X Y : Zorn) :
    zornSL3Action g (InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul X Y) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
        (zornSL3Action g X) (zornSL3Action g Y) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action_mul_of_covariant
    g hpair hcross hdualCross X Y

theorem zornSL3Action_preserves_norm_of_pairing
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hpair : InfoGeometry.Physics.ThreeColorSL3ZornAction.PreservesPairing g)
    (X : Zorn) :
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm (zornSL3Action g X) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm X :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action_preserves_norm_of_pairing
    g hpair X

end InfoGeometry.Canonical.ThreeColorSL3ZornActionBridge
