import InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
import InfoGeometry.Algebra.Zorn.G2ParabolicLineAction

/-!
# A native point-stabilizer witness for the base-fibre orbit

The GAP discovery probe identifies `parabolicReflection * pcGenerator 1` as
a point-stabilizer element.  This owner records only the native witness and
its point-fixing proof.  The Lean action convention must still be aligned
with the GAP convention before this product can be used as a third-line
witness; no orbit-class claim is made here.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiberThirdWitness

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

noncomputable def thirdFiberWitness : SplitOctF2Aut :=
  parabolicReflection * G2TwoSylowPCAutomorphisms.pcGenerator 1

noncomputable def thirdFiberWitnessLeanOrder : SplitOctF2Aut :=
  G2TwoSylowPCAutomorphisms.pcGenerator 1 * parabolicReflection

theorem thirdFiberWitness_mem_nativePointStabilizer :
    thirdFiberWitness ∈ nativePointStabilizer := by
  change thirdFiberWitness • nativeBasePointData = nativeBasePointData
  rw [thirdFiberWitness, mul_smul]
  calc
    parabolicReflection •
        (G2TwoSylowPCAutomorphisms.pcGenerator 1 • nativeBasePointData) =
        parabolicReflection • nativeBasePointData := by
          rw [G2NativeOnePointStabilizer.pcGenerator_pointData_fix]
    _ = nativeBasePointData := by
      simpa [parabolicReflection] using swap01Aut_pointData_fix

theorem thirdFiberWitness_fixes_base_point :
    octImAction thirdFiberWitness nativeBasePoint = nativeBasePoint := by
  have hfix := thirdFiberWitness_mem_nativePointStabilizer
  change thirdFiberWitness • nativeBasePointData = nativeBasePointData at hfix
  have hp := congrArg
    (fun p : G2ImaginaryPointAction.Point => imaginaryToOctIm p.1)
    hfix
  change imaginaryToOctIm (thirdFiberWitness •
      octImToImaginary nativeBasePoint) =
    imaginaryToOctIm (octImToImaginary nativeBasePoint) at hp
  unfold octImAction
  rw [hp]
  exact imaginaryOctImEquiv.right_inv nativeBasePoint

noncomputable def thirdFiberLine : NativeLine :=
  nativeLineAction thirdFiberWitness
    thirdFiberWitness_fixes_base_point
    lineZero

theorem thirdFiberLine_action :
    thirdFiberLine = nativeLineAction thirdFiberWitness
      thirdFiberWitness_fixes_base_point
      lineZero := by
  rfl

theorem thirdFiberWitnessLeanOrder_mem_nativePointStabilizer :
    thirdFiberWitnessLeanOrder ∈ nativePointStabilizer := by
  change thirdFiberWitnessLeanOrder • nativeBasePointData = nativeBasePointData
  rw [thirdFiberWitnessLeanOrder, mul_smul]
  calc
    G2TwoSylowPCAutomorphisms.pcGenerator 1 •
        (parabolicReflection • nativeBasePointData) =
        G2TwoSylowPCAutomorphisms.pcGenerator 1 • nativeBasePointData := by
          rw [show parabolicReflection = swap01Aut by rfl,
            swap01Aut_pointData_fix]
    _ = nativeBasePointData := by
      exact G2NativeOnePointStabilizer.pcGenerator_pointData_fix 1

theorem thirdFiberWitnessLeanOrder_fixes_base_point :
    octImAction thirdFiberWitnessLeanOrder nativeBasePoint = nativeBasePoint := by
  have hfix := thirdFiberWitnessLeanOrder_mem_nativePointStabilizer
  have hp := congrArg
    (fun p : G2ImaginaryPointAction.Point => imaginaryToOctIm p.1) hfix
  change imaginaryToOctIm (thirdFiberWitnessLeanOrder •
      octImToImaginary nativeBasePoint) =
    imaginaryToOctIm (octImToImaginary nativeBasePoint) at hp
  unfold octImAction
  rw [hp]
  exact imaginaryOctImEquiv.right_inv nativeBasePoint

theorem pointStabilizer_fixes_base_point
    {g : SplitOctF2Aut} (hg : g ∈ nativePointStabilizer) :
    octImAction g nativeBasePoint = nativeBasePoint := by
  change g • nativeBasePointData = nativeBasePointData at hg
  have hp := congrArg
    (fun p : G2ImaginaryPointAction.Point => imaginaryToOctIm p.1) hg
  change imaginaryToOctIm (g • octImToImaginary nativeBasePoint) =
    imaginaryToOctIm (octImToImaginary nativeBasePoint) at hp
  unfold octImAction
  rw [hp]
  exact imaginaryOctImEquiv.right_inv nativeBasePoint

noncomputable def thirdFiberLineLeanOrder : NativeLine :=
  nativeLineAction thirdFiberWitnessLeanOrder
    thirdFiberWitnessLeanOrder_fixes_base_point lineZero

theorem thirdFiberLineLeanOrder_ne_lineZero :
    thirdFiberLineLeanOrder ≠ lineZero := by
  decide

theorem thirdFiberLineLeanOrder_ne_lineInfinity :
    thirdFiberLineLeanOrder ≠ lineInfinity := by
  decide

end InfoGeometry.Algebra.Zorn.G2NativeLineFiberThirdWitness
