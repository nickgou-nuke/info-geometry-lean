import InfoGeometry.Exceptional.G2ArtinKleinBridge
import InfoGeometry.Exceptional.G2CoordinateRootIndexBridge

/-!
# Klein throat flip on the native root-index carrier

The throat flip is transported by the existing carrier equivalence.  It is an
outer/Klein involution and is not identified with a Weyl reflection here.
-/

namespace InfoGeometry.Exceptional.G2KleinRootIndexTransport

open InfoGeometry.Exceptional.G2ArtinKleinBridge
open InfoGeometry.Exceptional.G2KleinRootLabelBridge
open InfoGeometry.Exceptional.G2CoordinateRootIndexBridge

noncomputable def rootIndexThroatFlip :
    InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex ≃
      InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex :=
  coordinateRootToLieRootIndex.symm.trans
    ((kleinRootLabelThroatFlip).trans coordinateRootToLieRootIndex)

theorem rootIndexThroatFlip_apply
    (i : InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex) :
    rootIndexThroatFlip i =
      coordinateRootToLieRootIndex
        (kleinRootLabelThroatFlip
          (coordinateRootToLieRootIndex.symm i)) :=
  rfl

theorem rootIndexThroatFlip_involutive
    (i : InfoGeometry.Lie.CanonicalZornRootSystemComparison.RootIndex) :
    rootIndexThroatFlip (rootIndexThroatFlip i) = i := by
  apply coordinateRootToLieRootIndex.symm.injective
  simp only [rootIndexThroatFlip_apply, Equiv.symm_apply_apply,
    kleinRootLabelThroatFlip_involutive, Equiv.apply_symm_apply]

end InfoGeometry.Exceptional.G2KleinRootIndexTransport
