import InfoGeometry.Geometry.Statistical.SplitOctonionDualFlatDerivationBridge
import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# Dual-flat curvature from native standard split-octonion derivations

This owner specializes the abstract derivation-valued bridge using the
standard alternative-algebra derivations already constructed on the canonical
split-octonion carrier.
-/

namespace InfoGeometry.Geometry.Statistical.SplitOctonionStandardDualFlatBridge

noncomputable section

open InfoGeometry.Geometry.Statistical
open InfoGeometry.Geometry.Statistical.SplitOctonionDualFlatDerivationBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation

@[reducible] def CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
@[reducible] def Der := canonicalZornDerivations
@[reducible] def EndCZ := Module.End ℝ CZ

structure StandardSplitOctonionDualFlatDatum extends
    SplitOctonionDualFlatDatum where
  first : CZ → AbstractKingdon
  second : CZ → AbstractKingdon
  theta_eq : ∀ X,
    theta X = canonicalStandardDerivationOfCanonical
      (first X) (second X)

theorem curvature_eq_neg_standard_derivation_bracket
    (C : StandardSplitOctonionDualFlatDatum) (X Y : CZ) :
    C.R0 X Y =
      -((⁅canonicalStandardDerivationOfCanonical
          (C.first X) (C.second X),
        canonicalStandardDerivationOfCanonical
          (C.first Y) (C.second Y)⁆ : Der) : EndCZ) := by
  rw [curvature_eq_neg_derivation_bracket
      C.toSplitOctonionDualFlatDatum X Y,
    C.theta_eq X, C.theta_eq Y]

end
end InfoGeometry.Geometry.Statistical.SplitOctonionStandardDualFlatBridge
