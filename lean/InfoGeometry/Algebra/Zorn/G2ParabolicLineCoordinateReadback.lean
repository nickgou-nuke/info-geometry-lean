import InfoGeometry.Algebra.Zorn.G2NativeOctImWeylAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

/-!
# Coordinate readback for the parabolic line generator

The native Weyl action already has a coordinate formula. This owner exposes the
structural coordinate facts needed to distinguish the transported base-line
witness from the original one, without enumerating the line fibre.
-/

namespace InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback

open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativeOctImWeylAction
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem parabolicReflection_baseLineVector_ne :
    octImAction swap01Aut baseLineVector ≠ baseLineVector := by
  intro h
  have hcoord := congrFun h 3
  simp [octImAction_swap01, swap01OctIm, baseLineVector] at hcoord

theorem parabolicReflection_baseLineVector_ne_base_add :
    octImAction swap01Aut baseLineVector ≠
      nativeBasePoint + baseLineVector := by
  intro h
  have hcoord := congrFun h 3
  simp [octImAction_swap01, swap01OctIm, baseLineVector,
    nativeBasePoint, G2ParabolicLineCarrier.canonicalBasePoint] at hcoord

theorem lineShear_fixes_parabolic_baseLineVector :
    octImAction lineShear (octImAction parabolicReflection baseLineVector) =
      octImAction parabolicReflection baseLineVector := by
  rw [show lineShear = pc1Aut by rfl]
  rw [show parabolicReflection = swap01Aut by rfl, octImAction_swap01]
  unfold octImAction
  have hfix : pc1Aut • octImToImaginary (swap01OctIm baseLineVector) =
      octImToImaginary (swap01OctIm baseLineVector) := by
    apply Subtype.ext
    change pc1Aut⁻¹.1 (basis8 6) = basis8 6
    rw [pc1Aut_inv_eq, InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.pc1Aut_basis8_6]
  calc
    imaginaryToOctIm (pc1Aut • octImToImaginary (swap01OctIm baseLineVector)) =
        imaginaryToOctIm (octImToImaginary (swap01OctIm baseLineVector)) := by
      exact congrArg imaginaryToOctIm hfix
    _ = swap01OctIm baseLineVector := imaginaryOctImEquiv.right_inv _

theorem lineInfinity_eq_lineOne : lineInfinity = lineOne := by
  apply Subtype.ext
  rw [parabolicReflection_baseLineVector_readback, lineShear_lineInfinityVector_readback,
    lineShear_fixes_parabolic_baseLineVector]

theorem lineZero_ne_lineInfinity : lineZero ≠ lineInfinity := by
  intro h
  have himage : octImAction parabolicReflection baseLineVector ∈ candidates := by
    exact kernelCandidate_action_of_fix parabolicReflection
      (by simpa [parabolicReflection] using swap01Aut_fix_nativeBasePoint)
      baseLineVector baseLineVector_mem_candidates
  have hset : lineSet baseLineVector =
      lineSet (octImAction parabolicReflection baseLineVector) := by
    have hval := congrArg Subtype.val h
    simpa [lineZero, nativeBaseLineWitness, parabolicReflection_baseLineVector_readback] using hval
  rcases (lineSet_eq_lineSet_iff baseLineVector_mem_candidates himage).mp hset with hsame | hsum
  · have hne : octImAction parabolicReflection baseLineVector ≠ baseLineVector := by
      simpa [parabolicReflection] using parabolicReflection_baseLineVector_ne
    exact hne hsame
  · have hne : octImAction parabolicReflection baseLineVector ≠ nativeBasePoint + baseLineVector := by
      simpa [parabolicReflection] using parabolicReflection_baseLineVector_ne_base_add
    exact hne hsum

theorem lineZero_ne_lineOne : lineZero ≠ lineOne := by
  intro h
  exact lineZero_ne_lineInfinity (h.trans lineInfinity_eq_lineOne.symm)

end InfoGeometry.Algebra.Zorn.G2ParabolicLineCoordinateReadback
