import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteHeisenbergGroup

/-!
# CRT transport for the finite Heisenberg carrier

The Chinese-remainder theorem is used only at the finite coordinate level.  It
gives an explicit group isomorphism for the cocycle carrier; no matrix
representation or identification with the additive Weyl algebra is inferred.
-/

namespace InfoGeometry.Canonical.FiniteHeisenbergCore

noncomputable section

private def crtRing : ZMod 6 ≃+* ZMod 2 × ZMod 3 :=
  ZMod.chineseRemainder (m := 2) (n := 3) (by decide)

def finiteHeisenbergCRTMap :
    FiniteHeisenberg 6 → FiniteHeisenberg 2 × FiniteHeisenberg 3 := by
  intro x
  let p := crtRing x.coord.1.1
  let q := crtRing x.coord.1.2
  let r := crtRing x.coord.2
  exact (⟨((p.1, q.1), r.1)⟩, ⟨((p.2, q.2), r.2)⟩)

def finiteHeisenbergCRTInv :
    FiniteHeisenberg 2 × FiniteHeisenberg 3 → FiniteHeisenberg 6 := by
  intro x
  let p := crtRing.symm (x.1.coord.1.1, x.2.coord.1.1)
  let q := crtRing.symm (x.1.coord.1.2, x.2.coord.1.2)
  let r := crtRing.symm (x.1.coord.2, x.2.coord.2)
  exact ⟨((p, q), r)⟩

theorem finiteHeisenbergCRTMap_mul (x y : FiniteHeisenberg 6) :
    finiteHeisenbergCRTMap (x * y) =
      finiteHeisenbergCRTMap x * finiteHeisenbergCRTMap y := by
  rcases x with ⟨⟨⟨a, b⟩, c⟩⟩
  rcases y with ⟨⟨⟨d, e⟩, f⟩⟩
  change finiteHeisenbergCRTMap
      (finiteHeisenbergMul ⟨⟨⟨a, b⟩, c⟩⟩ ⟨⟨⟨d, e⟩, f⟩⟩) =
    (finiteHeisenbergMul
      (finiteHeisenbergCRTMap ⟨⟨⟨a, b⟩, c⟩⟩).1
      (finiteHeisenbergCRTMap ⟨⟨⟨d, e⟩, f⟩⟩).1,
     finiteHeisenbergMul
      (finiteHeisenbergCRTMap ⟨⟨⟨a, b⟩, c⟩⟩).2
      (finiteHeisenbergCRTMap ⟨⟨⟨d, e⟩, f⟩⟩).2)
  ext <;> simp [finiteHeisenbergCRTMap, finiteHeisenbergMul,
    heisenbergMul, crtRing]

theorem finiteHeisenbergCRTMap_left_inv (x : FiniteHeisenberg 6) :
    finiteHeisenbergCRTInv (finiteHeisenbergCRTMap x) = x := by
  rcases x with ⟨⟨⟨a, b⟩, c⟩⟩
  apply congrArg FiniteHeisenberg.mk
  simp [finiteHeisenbergCRTMap, crtRing]

theorem finiteHeisenbergCRTMap_right_inv
    (x : FiniteHeisenberg 2 × FiniteHeisenberg 3) :
    finiteHeisenbergCRTMap (finiteHeisenbergCRTInv x) = x := by
  rcases x with ⟨⟨⟨a, b⟩, c⟩, ⟨⟨d, e⟩, f⟩⟩
  ext <;> simp [finiteHeisenbergCRTInv, finiteHeisenbergCRTMap, crtRing]

/-- The finite Heisenberg group over `ZMod 6` splits into its `2` and `3`
components by the Chinese-remainder equivalence. -/
def finiteHeisenbergCRTMulEquiv :
    FiniteHeisenberg 6 ≃* FiniteHeisenberg 2 × FiniteHeisenberg 3 where
  toFun := finiteHeisenbergCRTMap
  invFun := finiteHeisenbergCRTInv
  left_inv := finiteHeisenbergCRTMap_left_inv
  right_inv := finiteHeisenbergCRTMap_right_inv
  map_mul' := finiteHeisenbergCRTMap_mul

end
end InfoGeometry.Canonical.FiniteHeisenbergCore
