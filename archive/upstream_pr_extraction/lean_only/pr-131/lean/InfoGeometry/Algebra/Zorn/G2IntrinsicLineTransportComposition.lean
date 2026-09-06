import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport

/-!
# Composition readback for intrinsic line transport

The dependent codomain of a transported line prevents a plain equality of
maps from being the most useful interface.  This owner exposes the
underlying finite-set equality, which is the action-compatible readback used
when assembling dependent flags.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicLineTransportComposition

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport


theorem intrinsicLineMap_val_mul
    (g h : SplitOctF2Aut)
    {p : OctImIsotropicPoint}
    (L : IntrinsicLine p) :
    (intrinsicLineMap (g * h) L).val =
      (intrinsicLineMap g (intrinsicLineMap h L)).val := by
  rw [intrinsicLineMap_val, intrinsicLineMap_val, intrinsicLineMap_val]
  simpa using zornZeroTripleMap_mul g h L.1

end InfoGeometry.Algebra.Zorn.G2IntrinsicLineTransportComposition
