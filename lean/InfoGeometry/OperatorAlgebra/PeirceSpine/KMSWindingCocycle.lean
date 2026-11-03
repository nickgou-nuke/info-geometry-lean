/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Integer winding in the Peirce nilpotent cone

The upper Peirce corner gives a genuine additive integer family of unipotent
operators. Its commutator with the sheet idempotent, paired with the lower
corner, recovers the winding multiple of the existing Jordan operator `genV`.
The statements are ring identities and make no commutativity assumption.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The integer winding operator `1 + n N₊`. -/
def peirceWinding (n : ℤ) (P A : B) : B :=
  1 + n • conePlus P A

/-- The inverse winding operator `1 - n N₊`. -/
def peirceWindingInv (n : ℤ) (P A : B) : B :=
  1 - n • conePlus P A

/-- Pair the logarithmic commutator with the lower Peirce corner. -/
def peirceWindingCharge (P C U UInv : B) : B :=
  anticomm (UInv * comm P U) (coneMinus P C)

variable {P : B} (hP : P * P = P)
include hP

/-- Integer winding composes additively, has the stated two-sided inverse,
and its noncommutative charge extraction is `+ n • V`. -/
theorem peirceWinding_group_and_charge (A C : B) (n m : ℤ) :
    peirceWinding m P A * peirceWinding n P A =
        peirceWinding (m + n) P A ∧
    peirceWinding n P A * peirceWindingInv n P A = 1 ∧
    peirceWindingInv n P A * peirceWinding n P A = 1 ∧
    peirceWindingCharge P C (peirceWinding n P A)
      (peirceWindingInv n P A) = n • genV P A C := by
  have hN2 : conePlus P A * conePlus P A = 0 :=
    conePlus_mul_conePlus hP A A
  have hMulLeft (r : ℤ) (X Y : B) : (r • X) * Y = r • (X * Y) :=
    map_zsmul (AddMonoidHom.mk' (fun U : B => U * Y)
      (fun U V => add_mul U V Y)) r X
  have hMulRight (r : ℤ) (X Y : B) : X * (r • Y) = r • (X * Y) :=
    map_zsmul (AddMonoidHom.mk' (fun V : B => X * V)
      (fun U V => mul_add X U V)) r Y
  have hCross : ∀ r s : ℤ,
      (r • conePlus P A) * (s • conePlus P A) = 0 := by
    intro r s
    calc
      (r • conePlus P A) * (s • conePlus P A) =
          r • (conePlus P A * (s • conePlus P A)) := hMulLeft r _ _
      _ = r • (s • (conePlus P A * conePlus P A)) := by rw [hMulRight]
      _ = (r * s) • (conePlus P A * conePlus P A) := by rw [mul_zsmul]
      _ = 0 := by rw [hN2, smul_zero]
  have hPN : P * conePlus P A = conePlus P A := P_mul_conePlus hP A
  have hNP : conePlus P A * P = 0 := conePlus_mul_P hP A
  have hPScaled : P * (n • conePlus P A) = n • conePlus P A := by
    rw [hMulRight, hPN]
  have hScaledNP : (n • conePlus P A) * P = 0 := by
    rw [hMulLeft, hNP, smul_zero]
  have hComm : comm P (peirceWinding n P A) = n • conePlus P A := by
    unfold comm peirceWinding
    rw [mul_add, add_mul, mul_one, one_mul, hPScaled, hScaledNP]
    abel
  have hInvComm : peirceWindingInv n P A * (n • conePlus P A) =
      n • conePlus P A := by
    unfold peirceWindingInv
    rw [sub_mul, one_mul, hCross, sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold peirceWinding
    simp only [mul_add, add_mul, one_mul, mul_one, hCross, add_zero]
    calc
      1 + m • conePlus P A + n • conePlus P A =
          1 + (m • conePlus P A + n • conePlus P A) := by rw [add_assoc]
      _ = 1 + (m + n) • conePlus P A := by
        rw [← add_zsmul (conePlus P A) m n]
  · unfold peirceWinding peirceWindingInv
    simp only [add_mul, mul_sub, one_mul, mul_one, hCross]
    abel
  · unfold peirceWinding peirceWindingInv
    simp only [sub_mul, mul_add, one_mul, mul_one, hCross, sub_zero]
    abel
  · unfold peirceWindingCharge
    rw [hComm, hInvComm]
    unfold genV anticomm
    rw [hMulLeft, hMulRight]
    exact (zsmul_add (conePlus P A * coneMinus P C)
      (coneMinus P C * conePlus P A) n).symm

end InfoGeometry.OperatorAlgebra.PeirceSpine
