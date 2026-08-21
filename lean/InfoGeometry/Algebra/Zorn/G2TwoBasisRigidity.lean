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
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> (dsimp [basisExpansion, add, add2, zero, ePlus, eMinus, up0, up1, up2, down0, down1, down2]; revert a b x0 x1 x2 y0 y1 y2; decide)

@[simp] theorem map_zero (f : SplitOctF2Aut) :
    f.1 zero = zero := by
  have h := f.2.2.1 zero zero
  rw [add_self] at h
  rw [add_self] at h
  exact h

lemma map_ite_zero (f : SplitOctF2Aut) (c : Bool) (E : SplitOctF2) :
    f.1 (if c then E else zero) = if c then f.1 E else zero := by
  cases c
  · simp [map_zero]
  · rfl

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
  dsimp [basisExpansion]
  rw [f.2.2.1, f.2.2.1, f.2.2.1, f.2.2.1,
    f.2.2.1, f.2.2.1, f.2.2.1]
  simp only [map_ite_zero]

theorem automorphism_ext_of_basis
    (f g : SplitOctF2Aut)
    (h : ∀ i : Fin 8, f.1 (basis8 i) = g.1 (basis8 i)) :
    f = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [← basisExpansion_eq X, map_basisExpansion, map_basisExpansion]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  dsimp [basis8] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

def basisRestriction (f : SplitOctF2Aut) : Fin 8 → SplitOctF2 :=
  fun i => f.1 (basis8 i)

def extendBasisMap (v : Fin 8 → SplitOctF2) (X : SplitOctF2) : SplitOctF2 :=
  add (add (add (add (add (add (add
    (if X.a then v 0 else zero)
    (if X.b then v 1 else zero))
    (if X.x0 then v 2 else zero))
    (if X.x1 then v 3 else zero))
    (if X.x2 then v 4 else zero))
    (if X.y0 then v 5 else zero))
    (if X.y1 then v 6 else zero))
    (if X.y2 then v 7 else zero)

theorem extendBasisMap_basisRestriction (f : SplitOctF2Aut) (X : SplitOctF2) :
    f.1 X = extendBasisMap (basisRestriction f) X := by
  have h := map_basisExpansion f X
  rw [basisExpansion_eq X] at h
  exact h

theorem basis8_injective : Function.Injective basis8 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [basis8] at h ⊢
  all_goals
    cases h

theorem basisRestriction_injective_on_basis (f : SplitOctF2Aut) :
    Function.Injective (basisRestriction f) := by
  intro i j h
  apply basis8_injective
  apply f.1.injective
  exact h

theorem basisRestriction_injective :
    Function.Injective basisRestriction := by
  intro f g h
  apply automorphism_ext_of_basis f g
  intro i
  exact congrFun h i

/-- The carrier cardinality is bounded by the possible eight basis images. -/
theorem automorphism_card_le_basis_maps :
    Fintype.card SplitOctF2Aut ≤ Fintype.card (Fin 8 → SplitOctF2) := by
  exact Fintype.card_le_of_injective basisRestriction basisRestriction_injective

theorem basisRestriction_preserves_mul
    (f : SplitOctF2Aut) (i j : Fin 8) :
    f.1 (mul (basis8 i) (basis8 j)) =
      mul (basisRestriction f i) (basisRestriction f j) := by
  exact f.2.2.2 (basis8 i) (basis8 j)

theorem basisRestriction_preserves_unit :
    ∀ f : SplitOctF2Aut, f.1 one = one := by
  intro f
  exact f.2.1

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
