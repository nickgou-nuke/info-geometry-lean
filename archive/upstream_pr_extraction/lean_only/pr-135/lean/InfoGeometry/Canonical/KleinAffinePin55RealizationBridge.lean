import InfoGeometry.Canonical.AffinePin55Cover

/-!
# Reflection and conjugation in the affine split-Pin cover

The affine Pin cover already contains the fixed-translation glide square.
This owner adds the complementary anti-fixed reflection square and records
the conjugation law for translations.  The statements remain at the native
`V55 ⋊ Pin(5,5)` level; no physical Poincare or Spin double-cover claim is
made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinAffinePin55RealizationBridge

open InfoGeometry.Canonical.AffinePin55Cover
open InfoGeometry.Clifford.Clifford55

theorem affinePinReflection_square
    (t : V55) (r : realSplitPin55)
    (hr : r * r = 1)
    (ht : (realSplitPinAction r) (Multiplicative.ofAdd t) =
      Multiplicative.ofAdd (-t)) :
    affinePinGlide t r * affinePinGlide t r = 1 := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd t *
      (realSplitPinAction r) (Multiplicative.ofAdd t) = 1
    rw [ht]
    change Multiplicative.ofAdd (t + -t) = 1
    simp
  · exact hr

theorem affinePin_conj_translation
    (t : V55) (r : realSplitPin55) :
    affinePinGlide 0 r * affinePinGlide t 1 *
        (affinePinGlide 0 r)⁻¹ =
      affinePinGlide
        (((realSplitPinAction r) (Multiplicative.ofAdd t)).toAdd) 1 := by
  apply SemidirectProduct.ext <;>
    simp [affinePinGlide, realSplitPinAction, nativeOrthogonalAction]

end InfoGeometry.Canonical.KleinAffinePin55RealizationBridge
