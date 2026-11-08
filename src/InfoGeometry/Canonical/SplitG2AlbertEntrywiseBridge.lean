import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Canonical.H3ZornAlgebraicSoldering

/-! A native bridge for the entrywise action of the verified split `G₂`
derivation carrier on the three off-diagonal Zorn slots.  This deliberately
does not assert that the action preserves the Albert Jordan product; that is
the separate compatibility frontier. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitG2AlbertEntrywiseBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering

abbrev G2Der := canonicalZornDerivations
abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3

noncomputable def lift (D : G2Der) : EndH3 where
  toFun X :=
    { α₁ := 0, α₂ := 0, α₃ := 0
      a := canonicalToVectorDerivation D X.a
      b := canonicalToVectorDerivation D X.b
      c := canonicalToVectorDerivation D X.c }
  map_add' X Y := by
    apply H3Zorn.ext_h3
    · change (0 : ℝ) = 0 + 0
      ring
    · change (0 : ℝ) = 0 + 0
      ring
    · change (0 : ℝ) = 0 + 0
      ring
    · change canonicalToVectorDerivation D (X.a + Y.a) =
        canonicalToVectorDerivation D X.a + canonicalToVectorDerivation D Y.a
      exact (canonicalToVectorDerivation D).map_add X.a Y.a
    · change canonicalToVectorDerivation D (X.b + Y.b) =
        canonicalToVectorDerivation D X.b + canonicalToVectorDerivation D Y.b
      exact (canonicalToVectorDerivation D).map_add X.b Y.b
    · change canonicalToVectorDerivation D (X.c + Y.c) =
        canonicalToVectorDerivation D X.c + canonicalToVectorDerivation D Y.c
      exact (canonicalToVectorDerivation D).map_add X.c Y.c
  map_smul' r X := by
    apply H3Zorn.ext_h3
    · change 0 = r * 0
      ring
    · change 0 = r * 0
      ring
    · change 0 = r * 0
      ring
    · change canonicalToVectorDerivation D (r • X.a) =
        r • canonicalToVectorDerivation D X.a
      exact (canonicalToVectorDerivation D).map_smul r X.a
    · change canonicalToVectorDerivation D (r • X.b) =
        r • canonicalToVectorDerivation D X.b
      exact (canonicalToVectorDerivation D).map_smul r X.b
    · change canonicalToVectorDerivation D (r • X.c) =
        r • canonicalToVectorDerivation D X.c
      exact (canonicalToVectorDerivation D).map_smul r X.c

theorem lift_apply_diagonal (D : G2Der) (X : H3) :
    (lift D X).α₁ = 0 := by
  rfl

end InfoGeometry.Canonical.SplitG2AlbertEntrywiseBridge
end
