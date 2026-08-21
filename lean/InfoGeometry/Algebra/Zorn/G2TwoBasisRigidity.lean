import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import Mathlib.Tactic

/-!
# Basis rigidity for finite split-Zorn automorphisms

An automorphism is determined by its values on the eight coordinate basis
elements.  The only finite computation here is the decomposition of one
256-element carrier element into those coordinates; no permutation of the
carrier is enumerated.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def basis8 : Fin 8 → SplitOctF2 :=
  ![ePlus, eMinus, up0, up1, up2, down0, down1, down2]

def basisExpansion (X : SplitOctF2) : SplitOctF2 :=
  add (add (add (add (add (add (add
    (if X.a then ePlus else zero)
    (if X.b then eMinus else zero))
    (if X.x0 then up0 else zero))
    (if X.x1 then up1 else zero))
    (if X.x2 then up2 else zero))
    (if X.y0 then down0 else zero))
    (if X.y1 then down1 else zero))
    (if X.y2 then down2 else zero)

theorem basisExpansion_eq (X : SplitOctF2) :
    basisExpansion X = X := by
  cases X <;> native_decide

@[simp] theorem map_zero (f : SplitOctF2Aut) :
    f.1 zero = zero := by
  have h := f.2.2.1 zero zero
  rw [add_self] at h
  rw [add_self] at h
  exact h

theorem map_basisExpansion (f : SplitOctF2Aut) (X : SplitOctF2) :
    f.1 (basisExpansion X) =
      add (add (add (add (add (add (add
        (if X.a then f.1 ePlus else zero)
        (if X.b then f.1 eMinus else zero))
        (if X.x0 then f.1 up0 else zero))
        (if X.x1 then f.1 up1 else zero))
        (if X.x2 then f.1 up2 else zero))
        (if X.y0 then f.1 down0 else zero))
        (if X.y1 then f.1 down1 else zero))
        (if X.y2 then f.1 down2 else zero) := by
  simp only [basisExpansion, map_zero]
  rw [f.2.2.1, f.2.2.1, f.2.2.1, f.2.2.1,
    f.2.2.1, f.2.2.1, f.2.2.1]

theorem automorphism_ext_of_basis
    (f g : SplitOctF2Aut)
    (h : ∀ i : Fin 8, f.1 (basis8 i) = g.1 (basis8 i)) :
    f = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [← basisExpansion_eq X, map_basisExpansion, map_basisExpansion]
  fin_cases X <;> simp [basis8] at h ⊢

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
