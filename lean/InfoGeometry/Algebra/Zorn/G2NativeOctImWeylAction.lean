import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

namespace InfoGeometry.Algebra.Zorn.G2NativeOctImWeylAction

open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def swapCartanOctIm (v : G2ParabolicLineFiber.OctImF2) :
    G2ParabolicLineFiber.OctImF2 :=
  ![v 3, v 4, v 5, v 0, v 1, v 2, v 6]

def swap01OctIm (v : G2ParabolicLineFiber.OctImF2) :
    G2ParabolicLineFiber.OctImF2 :=
  ![v 1, v 0, v 2, v 4, v 3, v 5, v 6]

def cycle012OctIm (v : G2ParabolicLineFiber.OctImF2) :
    G2ParabolicLineFiber.OctImF2 :=
  ![v 2, v 0, v 1, v 5, v 3, v 4, v 6]

theorem octImAction_swapCartan (v : G2ParabolicLineFiber.OctImF2) :
    octImAction swapCartanAut v = swapCartanOctIm v := by
  unfold octImAction
  have hinv : swapCartanAut⁻¹ = swapCartanAut := by
    apply inv_eq_iff_mul_eq_one.mpr
    exact swapCartanAut_sq
  change imaginaryToOctIm
      ⟨swapCartanFun (octImToImaginary v).1, _⟩ = swapCartanOctIm v
  dsimp [imaginaryToOctIm, swapCartanOctIm, octImToImaginary,
    swapCartanAut, swapCartanEquiv, swapCartanFun]
  funext i
  fin_cases i <;>
    simp [imaginaryToOctIm, boolToZMod_zModToBool]

theorem octImAction_swap01 (v : G2ParabolicLineFiber.OctImF2) :
    octImAction swap01Aut v = swap01OctIm v := by
  unfold octImAction
  have hinv : swap01Aut⁻¹ = swap01Aut := by
    apply inv_eq_iff_mul_eq_one.mpr
    exact swap01Aut_sq
  change imaginaryToOctIm
      ⟨swap01Fun (octImToImaginary v).1, _⟩ = swap01OctIm v
  dsimp [imaginaryToOctIm, swap01OctIm, octImToImaginary,
    swap01Fun]
  funext i
  fin_cases i <;>
    simp [imaginaryToOctIm, boolToZMod_zModToBool]

theorem octImAction_cycle012 (v : G2ParabolicLineFiber.OctImF2) :
    octImAction cycle012Aut v = cycle012OctIm v := by
  unfold octImAction
  have hinv : cycle012Aut⁻¹ = cycle012Aut * cycle012Aut := by
    apply inv_eq_iff_mul_eq_one.mpr
    exact cycle012Aut_cube
  change imaginaryToOctIm
      ⟨(cycle012Aut * cycle012Aut).1 (octImToImaginary v).1, _⟩ =
        cycle012OctIm v
  change imaginaryToOctIm
      ⟨cycle012Fun (cycle012Fun (octImToImaginary v).1), _⟩ =
        cycle012OctIm v
  dsimp [imaginaryToOctIm, cycle012OctIm, octImToImaginary,
    cycle012Fun]
  funext i
  fin_cases i <;>
    simp [imaginaryToOctIm, boolToZMod_zModToBool]

noncomputable def c : SplitOctF2Aut :=
  swapCartanAut * cycle012Aut

noncomputable def flagFiberWitness : SplitOctF2Aut :=
  swapCartanAut * swap01Aut * (c * c)

theorem flagFiberWitness_maps_nativeBasePoint_to_baseLineVector :
    octImAction flagFiberWitness nativeBasePoint = baseLineVector := by
  rw [flagFiberWitness, c]
  simp only [octImAction_mul, octImAction_swapCartan,
    octImAction_swap01, octImAction_cycle012]
  rw [show nativeBasePoint = (fun i => if i = 2 then 1 else 0) from rfl]
  funext i
  dsimp [baseLineVector]
  fin_cases i <;>
    simp [swapCartanOctIm, swap01OctIm, cycle012OctIm]

end InfoGeometry.Algebra.Zorn.G2NativeOctImWeylAction
