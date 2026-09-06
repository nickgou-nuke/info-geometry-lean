import InfoGeometry.Algebra.Zorn.G2NativeLineFiber
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2

/-!
# Weyl transport of the native three-line base fiber

This is the local fiber step in the full flag-orbit construction.  It does
not identify the native flag carrier with the exported 189-element quotient.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeBaseFiberOrbit

noncomputable section

open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def baseFiberWeyl : Fin 2 → SplitOctF2Aut
  | 0 => 1
  | 1 => swap01Aut

theorem baseFiberWeyl_fixes_point (k : Fin 2) :
    octImAction (baseFiberWeyl k) nativeBasePoint = nativeBasePoint := by
  fin_cases k
  · simp [baseFiberWeyl, octImAction_one]
  · exact swap01Aut_fix_nativeBasePoint

theorem cycle012Aut_not_fix_nativeBasePoint :
    octImAction cycle012Aut nativeBasePoint ≠ nativeBasePoint := by
  intro h
  let A := G2ImaginaryIsotropicPoints.actImaginary cycle012Aut
    (octImToImaginary nativeBasePoint)
  have hA : A = octImToImaginary nativeBasePoint := by
    apply imaginaryOctImEquiv.injective
    have h' : imaginaryToOctIm A = imaginaryToOctIm
        (octImToImaginary nativeBasePoint) := by
      change imaginaryToOctIm A = nativeBasePoint at h
      rw [← imaginaryOctImEquiv.right_inv nativeBasePoint] at h
      exact h
    exact h'
  have hcoord := congrArg (fun X : SplitOctF2 => X.x2)
    (congrArg Subtype.val hA)
  change ((cycle012Aut⁻¹).1 (octImToImaginary nativeBasePoint).1).x2 =
    (octImToImaginary nativeBasePoint).1.x2 at hcoord
  have hinv : cycle012Aut⁻¹ = cycle012Aut * cycle012Aut := by
    calc
      cycle012Aut⁻¹ = cycle012Aut⁻¹ * 1 := by simp
      _ = cycle012Aut⁻¹ *
          (cycle012Aut * cycle012Aut * cycle012Aut) := by
            rw [cycle012Aut_cube]
      _ = (cycle012Aut⁻¹ * cycle012Aut) *
          (cycle012Aut * cycle012Aut) := by simp [mul_assoc]
      _ = cycle012Aut * cycle012Aut := by simp
  rw [hinv] at hcoord
  have : False := by
    simp [cycle012Aut_apply, nativeBasePoint, octImToImaginary,
      cycle012Fun, zModToBool] at hcoord
  exact this

theorem baseFiberWeyl_maps_base_line (k : Fin 2) :
    nativeBaseLineWitness.image (octImAction (baseFiberWeyl k)) ∈ nativeLines := by
  apply lineSet_action_mem_nativeLines_of_fix _ (baseFiberWeyl_fixes_point k)
  exact baseLineVector_mem_candidates

end
end InfoGeometry.Algebra.Zorn.G2NativeBaseFiberOrbit
