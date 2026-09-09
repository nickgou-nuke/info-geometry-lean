import InfoGeometry.Algebra.Zorn.G2NativeBaseFiberOrbit
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts

/-! Native parabolic action on the unified native line fibre. -/

namespace InfoGeometry.Algebra.Zorn.G2ParabolicLineAction

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

abbrev P := nativePointStabilizer

noncomputable def parabolicReflection : SplitOctF2Aut := swap01Aut
noncomputable def lineShear : SplitOctF2Aut := pcGenerator 0

def lineZero : NativeLine :=
  ⟨nativeBaseLineWitness, nativeBaseLineWitness_mem_nativeLines⟩

noncomputable def nativeLineAction
    (g : SplitOctF2Aut)
    (hg : octImAction g nativeBasePoint = nativeBasePoint)
    (L : NativeLine) : NativeLine :=
  by
    refine ⟨((nativeLineFiberMap g nativeBasePoint) L).1, ?_⟩
    simpa [hg] using ((nativeLineFiberMap g nativeBasePoint) L).2

noncomputable def lineInfinity : NativeLine :=
  nativeLineAction parabolicReflection
    (by simpa [parabolicReflection] using swap01Aut_fix_nativeBasePoint) lineZero

noncomputable def lineOne : NativeLine :=
  nativeLineAction lineShear (pcGenerator_fix 0) lineInfinity

theorem parabolicReflection_mem : parabolicReflection ∈ P := by
  change parabolicReflection • nativeBasePointData = nativeBasePointData
  simpa [parabolicReflection] using swap01Aut_pointData_fix

theorem lineShear_mem_unipotent : lineShear ∈ unipotentSubgroup := by
  change lineShear ∈ Set.range G2TwoSylowSubgroup.pcWord
  exact ⟨oneAt 0, by simpa [lineShear] using pcWord_oneAt_eq_generator 0⟩

theorem lineZero_mem_nativeLines : (lineZero : NativeLine).1 ∈ nativeLines := by
  exact nativeBaseLineWitness_mem_nativeLines

theorem lineInfinity_mem_nativeLines : (lineInfinity : NativeLine).1 ∈ nativeLines := by
  exact (nativeLineAction parabolicReflection
    (by simpa [parabolicReflection] using swap01Aut_fix_nativeBasePoint) lineZero).property

theorem lineOne_mem_nativeLines : (lineOne : NativeLine).1 ∈ nativeLines := by
  exact (nativeLineAction lineShear (pcGenerator_fix 0) lineInfinity).property

theorem parabolicReflection_lineZero :
    lineInfinity = nativeLineAction parabolicReflection
      (by simpa [parabolicReflection] using swap01Aut_fix_nativeBasePoint) lineZero := by
  rfl

theorem lineShear_lineInfinity :
    lineOne = nativeLineAction lineShear (pcGenerator_fix 0) lineInfinity := by
  rfl

theorem parabolicReflection_baseLineVector_readback :
    (lineInfinity : NativeLine).1 =
      lineSet (octImAction parabolicReflection baseLineVector) := by
  change (lineSet baseLineVector).image (octImAction parabolicReflection) = _
  rw [← lineSet_action parabolicReflection
    (by simpa [parabolicReflection] using swap01Aut_fix_nativeBasePoint)
    baseLineVector]

theorem lineShear_lineInfinityVector_readback :
    (lineOne : NativeLine).1 =
      lineSet (octImAction lineShear
        (octImAction parabolicReflection baseLineVector)) := by
  change (lineInfinity : NativeLine).1.image (octImAction lineShear) = _
  rw [parabolicReflection_baseLineVector_readback]
  rw [← lineSet_action lineShear (pcGenerator_fix 0)
    (octImAction parabolicReflection baseLineVector)]

end InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
