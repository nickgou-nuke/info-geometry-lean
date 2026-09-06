import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport

/-!
# Intrinsic line-fibre transport for the point stabilizer

This owner records the nearest structural consequence of the equivariant
line transport: an automorphism fixing the base point acts surjectively on
the intrinsic line fibre over that point.  It does not identify this action
with the native line carrier or assert transitivity.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicPointStabilizerFiber

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport

private theorem cast_intrinsicLine_val
    {p q : OctImIsotropicPoint} (h : p = q)
    (L : IntrinsicLine p) :
    (cast (congrArg IntrinsicLine h) L).val = L.val := by
  cases h
  rfl

theorem intrinsicPointStabilizer_lineFiber_surjective
    (g : SplitOctF2Aut)
    (hg : octImPointPerm g nativeBaseIsotropicPoint = nativeBaseIsotropicPoint) :
    Function.Surjective (fun L : IntrinsicLine nativeBaseIsotropicPoint =>
      cast (congrArg IntrinsicLine hg)
        ((intrinsicLineMapEquiv g nativeBaseIsotropicPoint) L)) := by
  intro L
  let e := intrinsicLineMapEquiv g nativeBaseIsotropicPoint
  let L' : IntrinsicLine (octImPointPerm g nativeBaseIsotropicPoint) :=
    cast (congrArg IntrinsicLine hg.symm) L
  obtain ⟨M, hM⟩ := e.surjective L'
  refine ⟨M, ?_⟩
  change cast (congrArg IntrinsicLine hg) (e M) = L
  rw [hM]
  apply Subtype.ext
  dsimp [L']
  exact (cast_intrinsicLine_val hg _).trans
    (cast_intrinsicLine_val hg.symm L)

end InfoGeometry.Algebra.Zorn.G2IntrinsicPointStabilizerFiber
