import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport

/-!
# Readback for native line-fibre transport

The transported native line is represented by the image of its line-set.
This lemma exposes that fact at the carrier level, so concrete generators can
be read back without identifying dependent fibres definitionally.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiberActionReadback

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation

theorem nativeLineFiberMap_val_lineSet
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (y : G2ParabolicLineCarrier.OctImF2) (hy : y ∈ candidates) :
    ((nativeLineFiberMap g nativeBasePoint)
      ⟨lineSet y, lineSet_mem_nativeLines y hy⟩).1 =
      lineSet (octImAction g y) := by
  unfold nativeLineFiberMap
  change (lineSet y).image (octImAction g) = _
  exact (lineSet_action g hg y).symm

end InfoGeometry.Algebra.Zorn.G2NativeLineFiberActionReadback
