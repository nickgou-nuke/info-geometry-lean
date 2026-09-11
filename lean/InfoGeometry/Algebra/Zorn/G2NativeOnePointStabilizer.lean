import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2NativePointFoundation

/-!
# Native isotropic common fixed point of the PC unipotent generators

The old coordinate point `basePoint` and the split-Zorn unit are not the
parabolic isotropic point fixed by the native PC carrier.  The coordinate
vector supported at `2` is isotropic and is fixed by every native PC
generator.  This file transports that calculation to the trace-zero
seven-coordinate carrier and closes it under PC words.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation

export InfoGeometry.Algebra.Zorn.G2NativePointFoundation (nativeBasePoint)

theorem nativeBasePoint_isotropic :
    G2ParabolicLineFiber.splitQuad nativeBasePoint = 0 := by
  native_decide +revert

theorem nativeBasePoint_nonzero : nativeBasePoint ≠ 0 := by
  intro h
  have := congrFun h 2
  simp [nativeBasePoint] at this

theorem swap01Aut_fix_nativeBasePoint :
    octImAction swap01Aut nativeBasePoint = nativeBasePoint := by
  have hinv : swap01Aut⁻¹ = swap01Aut := by
    calc
      swap01Aut⁻¹ = swap01Aut⁻¹ * 1 := by simp
      _ = swap01Aut⁻¹ * (swap01Aut * swap01Aut) := by rw [swap01Aut_sq]
      _ = (swap01Aut⁻¹ * swap01Aut) * swap01Aut := by rw [mul_assoc]
      _ = swap01Aut := by rw [inv_mul_cancel]; simp
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary swap01Aut
        (octImToImaginary nativeBasePoint)) = nativeBasePoint
  unfold G2ImaginaryIsotropicPoints.actImaginary
  rw [← imaginaryOctImEquiv.right_inv nativeBasePoint]
  have hsub : G2ImaginaryIsotropicPoints.actImaginary swap01Aut
      (octImToImaginary nativeBasePoint) = octImToImaginary nativeBasePoint := by
    apply Subtype.ext
    change swap01Aut⁻¹.1 (octImToImaginary nativeBasePoint).1 =
      (octImToImaginary nativeBasePoint).1
    have hval := congrArg
      (fun f : SplitOctF2Aut => f.1 (octImToImaginary nativeBasePoint).1) hinv
    simpa [swap01Aut_apply] using hval
  exact congrArg imaginaryToOctIm hsub

def nativeBaseIsotropicPoint : OctImIsotropicPoint :=
  ⟨nativeBasePoint, nativeBasePoint_isotropic, nativeBasePoint_nonzero⟩

def nativeBasePointData : G2ImaginaryPointAction.Point :=
  octImToPoint nativeBaseIsotropicPoint

theorem swap01Aut_pointData_fix :
    swap01Aut • nativeBasePointData = nativeBasePointData := by
  apply Subtype.ext
  apply Subtype.ext
  change swap01Aut⁻¹.1 (octImToImaginary nativeBasePoint).1 =
    (octImToImaginary nativeBasePoint).1
  have hinv : swap01Aut⁻¹ = swap01Aut := by
    calc
      swap01Aut⁻¹ = swap01Aut⁻¹ * 1 := by simp
      _ = swap01Aut⁻¹ * (swap01Aut * swap01Aut) := by rw [swap01Aut_sq]
      _ = (swap01Aut⁻¹ * swap01Aut) * swap01Aut := by rw [mul_assoc]
      _ = swap01Aut := by rw [inv_mul_cancel]; simp
  have hval := congrArg
    (fun f : SplitOctF2Aut => f.1 (octImToImaginary nativeBasePoint).1) hinv
  simpa [swap01Aut_apply] using hval

theorem octImAction_mul (g h : SplitOctF2Aut) (v : G2ParabolicLineFiber.OctImF2) :
    octImAction (g * h) v = octImAction g (octImAction h v) := by
  unfold octImAction
  have hv : octImToImaginary (imaginaryToOctIm (h • octImToImaginary v)) =
      h • octImToImaginary v := imaginaryOctImEquiv.left_inv _
  rw [hv, mul_smul]

theorem pc1_fix : octImAction G2TwoSylowPCAutomorphisms.pc1Aut nativeBasePoint = nativeBasePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc1Aut (octImToImaginary nativeBasePoint)) = nativeBasePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, nativeBasePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc1Aut,
      involutiveEquiv, pc1Fun, boolToZMod, zModToBool]

theorem pc2_fix : octImAction G2TwoSylowPCAutomorphisms.pc2Aut nativeBasePoint = nativeBasePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc2Aut (octImToImaginary nativeBasePoint)) = nativeBasePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, nativeBasePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc2Aut,
      G2TwoSylowPCAutomorphisms.pc2Equiv,
      pc2Fun, pc6Fun, boolToZMod, zModToBool]

theorem pc3_fix : octImAction G2TwoSylowPCAutomorphisms.pc3Aut nativeBasePoint = nativeBasePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc3Aut (octImToImaginary nativeBasePoint)) = nativeBasePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, nativeBasePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc3Aut,
      G2TwoSylowPCAutomorphisms.pc3Equiv,
      pc3Fun, pc6Fun, boolToZMod, zModToBool]

theorem pc4_fix : octImAction G2TwoSylowPCAutomorphisms.pc4Aut nativeBasePoint = nativeBasePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc4Aut (octImToImaginary nativeBasePoint)) = nativeBasePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, nativeBasePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc4Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc4Fun, boolToZMod, zModToBool]

theorem pc5_fix : octImAction G2TwoSylowPCAutomorphisms.pc5Aut nativeBasePoint = nativeBasePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc5Aut (octImToImaginary nativeBasePoint)) = nativeBasePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, nativeBasePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc5Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc5Fun, boolToZMod, zModToBool]

theorem pc6_fix : octImAction G2TwoSylowPCAutomorphisms.pc6Aut nativeBasePoint = nativeBasePoint := by
  unfold octImAction
  change imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        G2TwoSylowPCAutomorphisms.pc6Aut (octImToImaginary nativeBasePoint)) = nativeBasePoint
  funext i
  fin_cases i <;>
    simp [G2ImaginaryIsotropicPoints.actImaginary, nativeBasePoint, octImToImaginary,
      imaginaryToOctIm, G2TwoSylowPCAutomorphisms.pc6Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc6Fun, boolToZMod, zModToBool]

theorem pcGenerator_fix (i : Fin 6) :
    octImAction (G2TwoSylowPCAutomorphisms.pcGenerator i) nativeBasePoint = nativeBasePoint := by
  fin_cases i
  · exact pc1_fix
  · exact pc2_fix
  · exact pc3_fix
  · exact pc4_fix
  · exact pc5_fix
  · exact pc6_fix

theorem pcGenerator_point_fix (i : Fin 6) :
    octImPointPerm (G2TwoSylowPCAutomorphisms.pcGenerator i) nativeBaseIsotropicPoint =
      nativeBaseIsotropicPoint := by
  rw [octImPointPerm_apply]
  apply Subtype.ext
  change octImAction (G2TwoSylowPCAutomorphisms.pcGenerator i) nativeBasePoint =
    nativeBasePoint
  exact pcGenerator_fix i

theorem pcGenerator_pointData_fix (i : Fin 6) :
    G2TwoSylowPCAutomorphisms.pcGenerator i • nativeBasePointData =
      nativeBasePointData := by
  apply Subtype.ext
  apply Subtype.ext
  change (G2TwoSylowPCAutomorphisms.pcGenerator i)⁻¹.1
      (octImToImaginary nativeBasePoint).1 =
    (octImToImaginary nativeBasePoint).1
  have hcoord : imaginaryToOctIm
      (G2ImaginaryIsotropicPoints.actImaginary
        (G2TwoSylowPCAutomorphisms.pcGenerator i)
      (octImToImaginary nativeBasePoint)) =
      imaginaryToOctIm (octImToImaginary nativeBasePoint) := by
    have h := pcGenerator_fix i
    unfold octImAction at h
    rw [← imaginaryOctImEquiv.right_inv nativeBasePoint] at h
    exact h
  have himag := imaginaryOctImEquiv.injective hcoord
  exact congrArg Subtype.val himag

def nativePointStabilizer : Subgroup SplitOctF2Aut :=
  MulAction.stabilizer SplitOctF2Aut nativeBasePointData

theorem pcSubgroup_le_nativePointStabilizer :
    G2TwoSylowPCAutomorphisms.pcSubgroup ≤ nativePointStabilizer := by
  rw [G2TwoSylowPCAutomorphisms.pcSubgroup]
  apply (Subgroup.closure_le _).2
  rintro g ⟨i, rfl⟩
  exact pcGenerator_pointData_fix i

theorem pcSubgroup_eq_sylowTwoSubgroup :
    G2TwoSylowPCAutomorphisms.pcSubgroup =
      G2TwoSylowSubgroup.sylowTwoSubgroup := by
  rfl

theorem prod_fix (L : List SplitOctF2Aut)
    (hL : ∀ g ∈ L, octImAction g nativeBasePoint = nativeBasePoint) :
    octImAction L.prod nativeBasePoint = nativeBasePoint := by
  induction L with
  | nil =>
      change imaginaryToOctIm (octImToImaginary nativeBasePoint) = nativeBasePoint
      exact imaginaryOctImEquiv.right_inv nativeBasePoint
  | cons g gs ih =>
      rw [List.prod_cons, octImAction_mul]
      rw [ih (fun x hx => hL x (List.mem_cons_of_mem g hx))]
      exact hL g (List.mem_cons_self)

theorem pcWord_fix (e : Fin 6 → Bool) :
    octImAction (G2TwoSylowPCAutomorphisms.pcWord e) nativeBasePoint = nativeBasePoint := by
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
    exact imaginaryOctImEquiv.right_inv nativeBasePoint

theorem pcWord_point_fix (e : Fin 6 → Bool) :
    octImPointPerm (G2TwoSylowPCAutomorphisms.pcWord e) nativeBaseIsotropicPoint =
      nativeBaseIsotropicPoint := by
  rw [octImPointPerm_apply]
  apply Subtype.ext
  change octImAction (G2TwoSylowPCAutomorphisms.pcWord e) nativeBasePoint =
    nativeBasePoint
  exact pcWord_fix e

theorem pcWord_pointData_fix (e : Fin 6 → Bool) :
    G2TwoSylowPCAutomorphisms.pcWord e • nativeBasePointData =
      nativeBasePointData := by
  apply Subtype.ext
  apply Subtype.ext
  change (G2TwoSylowPCAutomorphisms.pcWord e)⁻¹.1
      (octImToImaginary nativeBasePoint).1 =
    (octImToImaginary nativeBasePoint).1
  have h := pcWord_fix e
  unfold octImAction at h
  rw [← imaginaryOctImEquiv.right_inv nativeBasePoint] at h
  have himag := imaginaryOctImEquiv.injective h
  exact congrArg Subtype.val himag

/-- The concrete 64-element PC subgroup fixes the native base point. -/
theorem unipotentSubgroup_le_nativePointStabilizer :
    ∀ u ∈ unipotentSubgroup,
      u • nativeBasePointData = nativeBasePointData := by
  intro u hu
  rcases hu with ⟨e, rfl⟩
  exact pcWord_pointData_fix e

end InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
