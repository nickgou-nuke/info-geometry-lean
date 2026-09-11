import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

/-!
# CAS-aligned enumeration of the native 63-point carrier

The GAP carrier uses the ordered full split-Zorn coordinates
`(a,b,x0,x1,x2,y0,y1,y2)`.  Its column orbit of the native point `x2` has
63 elements.  This file records that orbit in the same coordinate order and
transports it to the seven-coordinate trace-zero carrier.  The enumeration is
an explicit finite certificate; it is not the arbitrary enumeration obtained
from `Fintype.equivFinOfCardEq`.
-/

namespace InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

abbrev F2 := ZMod 2

def casPointFull : Fin 63 → (Fin 8 → F2)
  | 0 => ![0,0,0,0,1,0,0,0]
  | 1 => ![0,0,0,1,0,0,0,0]
  | 2 => ![0,0,0,0,0,0,0,1]
  | 3 => ![1,1,0,1,1,0,1,0]
  | 4 => ![0,0,0,1,1,1,0,0]
  | 5 => ![0,0,0,1,1,0,0,0]
  | 6 => ![0,0,1,0,0,0,0,0]
  | 7 => ![0,0,0,0,0,0,1,0]
  | 8 => ![0,0,1,0,0,0,1,1]
  | 9 => ![1,1,0,0,1,1,1,1]
  | 10 => ![1,1,0,1,0,1,1,1]
  | 11 => ![0,0,0,0,0,0,1,1]
  | 12 => ![1,1,0,0,1,0,1,1]
  | 13 => ![0,0,0,0,0,1,0,1]
  | 14 => ![1,1,0,1,0,0,1,0]
  | 15 => ![1,1,0,1,1,1,1,0]
  | 16 => ![1,1,0,1,0,1,1,0]
  | 17 => ![1,1,1,0,1,1,0,0]
  | 18 => ![1,1,1,1,0,1,0,0]
  | 19 => ![1,1,0,1,0,0,1,1]
  | 20 => ![0,0,0,1,0,1,0,0]
  | 21 => ![0,0,1,0,1,0,1,0]
  | 22 => ![0,0,1,1,0,0,0,1]
  | 23 => ![0,0,1,0,1,0,0,0]
  | 24 => ![0,0,1,1,0,0,0,0]
  | 25 => ![0,0,1,1,0,1,1,0]
  | 26 => ![1,1,1,0,0,1,1,0]
  | 27 => ![0,0,1,0,0,0,1,0]
  | 28 => ![0,0,0,0,0,1,0,0]
  | 29 => ![0,0,0,0,0,1,1,0]
  | 30 => ![0,0,0,0,1,0,1,0]
  | 31 => ![1,1,1,1,1,1,1,1]
  | 32 => ![0,0,1,1,1,0,1,1]
  | 33 => ![0,0,1,0,0,0,0,1]
  | 34 => ![1,1,1,0,1,0,1,1]
  | 35 => ![0,0,1,0,1,1,1,1]
  | 36 => ![0,0,0,1,0,1,0,1]
  | 37 => ![0,0,0,0,1,1,1,0]
  | 38 => ![1,1,1,0,0,1,0,1]
  | 39 => ![0,0,0,1,0,0,0,1]
  | 40 => ![1,1,0,0,1,1,0,1]
  | 41 => ![1,1,1,1,1,0,0,1]
  | 42 => ![0,0,1,1,0,1,1,1]
  | 43 => ![1,1,0,1,1,1,0,1]
  | 44 => ![1,1,1,0,0,1,1,1]
  | 45 => ![1,1,1,1,1,0,1,0]
  | 46 => ![1,1,0,0,1,0,0,1]
  | 47 => ![0,0,0,0,0,1,1,1]
  | 48 => ![1,1,1,0,1,0,0,1]
  | 49 => ![1,1,0,1,1,0,0,1]
  | 50 => ![1,1,1,0,0,1,0,0]
  | 51 => ![1,1,1,0,1,1,1,0]
  | 52 => ![1,1,1,1,0,1,0,1]
  | 53 => ![1,1,1,1,0,0,1,1]
  | 54 => ![1,1,1,1,0,0,1,0]
  | 55 => ![0,0,1,1,1,1,1,0]
  | 56 => ![1,1,1,1,1,1,0,0]
  | 57 => ![0,0,1,1,1,0,0,0]
  | 58 => ![0,0,1,0,1,1,0,1]
  | 59 => ![0,0,1,1,1,1,0,1]
  | 60 => ![0,0,0,0,1,1,0,0]
  | 61 => ![0,0,0,1,1,1,1,1]
  | 62 => ![0,0,0,1,1,0,1,1]
  | _ => ![0,0,0,0,0,0,0,0]

def casPoint (i : Fin 63) : G2ParabolicLineFiber.OctImF2 := fun j =>
  match j with
  | 0 => casPointFull i 2
  | 1 => casPointFull i 3
  | 2 => casPointFull i 4
  | 3 => casPointFull i 5
  | 4 => casPointFull i 6
  | 5 => casPointFull i 7
  | 6 => casPointFull i 0

theorem casPoint_isotropic (i : Fin 63) :
    G2ParabolicLineFiber.splitQuad (casPoint i) = 0 := by
  fin_cases i <;> native_decide

theorem casPoint_nonzero (i : Fin 63) : casPoint i ≠ 0 := by
  fin_cases i <;> native_decide

noncomputable def casPointEnum : Fin 63 ≃ OctImIsotropicPoint :=
  let f : Fin 63 → OctImIsotropicPoint :=
    fun i => ⟨casPoint i, casPoint_isotropic i, casPoint_nonzero i⟩
  have hraw : Function.Injective casPoint := by
    native_decide
  have hf : Function.Injective f := by
    intro i j h
    exact hraw (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    have hcard : Fintype.card (Fin 63) = Fintype.card OctImIsotropicPoint := by
      rw [Fintype.card_fin, octImIsotropicPoint_card]
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
    exact hbij.2
  Equiv.ofBijective f ⟨hf, hsurj⟩

@[simp] theorem casPointEnum_apply (i : Fin 63) :
    casPointEnum i = ⟨casPoint i, casPoint_isotropic i, casPoint_nonzero i⟩ := by
  apply Subtype.ext
  rfl

theorem casPointEnum_card : Fintype.card OctImIsotropicPoint = 63 := by
  exact Fintype.card_congr casPointEnum

theorem casPoint_zero_eq_nativeBasePoint : casPoint 0 = nativeBasePoint := by
  funext j
  fin_cases j <;> rfl

theorem casPointEnum_zero_eq_nativeBaseIsotropicPoint :
    casPointEnum 0 = nativeBaseIsotropicPoint := by
  apply Subtype.ext
  exact casPoint_zero_eq_nativeBasePoint

end InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
