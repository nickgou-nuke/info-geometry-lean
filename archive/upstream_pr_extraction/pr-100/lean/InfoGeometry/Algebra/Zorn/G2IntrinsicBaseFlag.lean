import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

/-!
# Native base flag for the intrinsic incidence carrier

The base flag is constructed on the Zorn-zero intrinsic carrier.  The older
`octCross` line predicate is intentionally not used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

instance : DecidableEq OctImIsotropicPoint := by infer_instance

private theorem baseLineWitness_points_valid (v : OctImF2)
    (hv : v ∈ nativeBaseLineWitness) :
    splitQuad v = 0 ∧ v ≠ 0 := by
  native_decide +revert

theorem nativeBaseLineWitness_points_valid (v : OctImF2)
    (hv : v ∈ nativeBaseLineWitness) :
    splitQuad v = 0 ∧ v ≠ 0 :=
  baseLineWitness_points_valid v hv

private def intrinsicPointOf (v : OctImF2)
    (hv : v ∈ nativeBaseLineWitness) : OctImIsotropicPoint :=
  ⟨v, baseLineWitness_points_valid v hv⟩

def baseIntrinsicLineSet : Finset OctImIsotropicPoint :=
  nativeBaseLineWitness.attach.image (fun v => intrinsicPointOf v.1 v.2)

theorem baseIntrinsicLineSet_card : baseIntrinsicLineSet.card = 3 := by
  native_decide +revert

noncomputable def baseIntrinsicLine : IntrinsicLine nativeBaseIsotropicPoint := by
  refine ⟨baseIntrinsicLineSet, ?_⟩
  native_decide +revert

noncomputable def baseIntrinsicFlag : IntrinsicFlag :=
  ⟨nativeBaseIsotropicPoint, baseIntrinsicLine⟩

theorem mem_baseIntrinsicLine_iff (v : OctImIsotropicPoint) :
    v ∈ baseIntrinsicLine.1 ↔ v.1 ∈ nativeBaseLineWitness := by
  unfold baseIntrinsicLine baseIntrinsicLineSet
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, hEq⟩
    have hval : w.1 = v.1 := congrArg Subtype.val hEq
    simpa [hval] using w.2
  · intro hv
    refine Finset.mem_image.mpr ⟨⟨v.1, hv⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

end InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
