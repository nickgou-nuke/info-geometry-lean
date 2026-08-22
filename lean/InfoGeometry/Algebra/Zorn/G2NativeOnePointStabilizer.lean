import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-!
# Native common fixed point of the PC unipotent generators

The old coordinate point `basePoint` is not fixed by the native PC carrier.
The split-Zorn unit is the correct common fixed point: each PC generator fixes
`one` by its native algebraic definition.  This file transports that fact to
the trace-zero seven-coordinate carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

def onePoint : G2ParabolicLineFiber.OctImF2 := fun i => if i = 6 then 1 else 0

theorem octImAction_mul (g h : SplitOctF2Aut) (v : G2ParabolicLineFiber.OctImF2) :
    octImAction (g * h) v = octImAction g (octImAction h v) := by
  unfold octImAction
  have hv : octImToImaginary (imaginaryToOctIm (h • octImToImaginary v)) =
      h • octImToImaginary v := imaginaryOctImEquiv.left_inv _
  rw [hv, mul_smul]

theorem pc1_fix : octImAction G2TwoSylowPCAutomorphisms.pc1Aut onePoint = onePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc1Aut (octImToImaginary onePoint)) = onePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, onePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc1Aut,
      involutiveEquiv, pc1Fun, boolToZMod, zModToBool]

theorem pc2_fix : octImAction G2TwoSylowPCAutomorphisms.pc2Aut onePoint = onePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc2Aut (octImToImaginary onePoint)) = onePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, onePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc2Aut,
      G2TwoSylowPCAutomorphisms.pc2Equiv,
      pc2Fun, pc6Fun, boolToZMod, zModToBool]

theorem pc3_fix : octImAction G2TwoSylowPCAutomorphisms.pc3Aut onePoint = onePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc3Aut (octImToImaginary onePoint)) = onePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, onePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc3Aut,
      G2TwoSylowPCAutomorphisms.pc3Equiv,
      pc3Fun, pc6Fun, boolToZMod, zModToBool]

theorem pc4_fix : octImAction G2TwoSylowPCAutomorphisms.pc4Aut onePoint = onePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc4Aut (octImToImaginary onePoint)) = onePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, onePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc4Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc4Fun, boolToZMod, zModToBool]

theorem pc5_fix : octImAction G2TwoSylowPCAutomorphisms.pc5Aut onePoint = onePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc5Aut (octImToImaginary onePoint)) = onePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, onePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc5Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc5Fun, boolToZMod, zModToBool]

theorem pc6_fix : octImAction G2TwoSylowPCAutomorphisms.pc6Aut onePoint = onePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc6Aut (octImToImaginary onePoint)) = onePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, onePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc6Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc6Fun, boolToZMod, zModToBool]

theorem pcGenerator_fix (i : Fin 6) :
    octImAction (G2TwoSylowPCAutomorphisms.pcGenerator i) onePoint = onePoint := by
  fin_cases i
  · exact pc1_fix
  · exact pc2_fix
  · exact pc3_fix
  · exact pc4_fix
  · exact pc5_fix
  · exact pc6_fix

theorem prod_fix (L : List SplitOctF2Aut)
    (hL : ∀ g ∈ L, octImAction g onePoint = onePoint) :
    octImAction L.prod onePoint = onePoint := by
  induction L with
  | nil =>
      change imaginaryToOctIm (octImToImaginary onePoint) = onePoint
      exact imaginaryOctImEquiv.right_inv onePoint
  | cons g gs ih =>
      rw [List.prod_cons, octImAction_mul]
      rw [ih (fun x hx => hL x (List.mem_cons_of_mem g hx))]
      exact hL g (List.mem_cons_self)

theorem pcWord_fix (e : Fin 6 → Bool) :
    octImAction (G2TwoSylowPCAutomorphisms.pcWord e) onePoint = onePoint := by
  unfold G2TwoSylowPCAutomorphisms.pcWord
  apply prod_fix
  intro g hg
  rw [List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  by_cases h : e i
  · simpa [h] using pcGenerator_fix i
  · rw [if_neg h]
    unfold octImAction
    rw [one_smul]
    exact imaginaryOctImEquiv.right_inv onePoint

end InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
