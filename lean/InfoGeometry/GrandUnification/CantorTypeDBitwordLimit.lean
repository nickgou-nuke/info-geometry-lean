import Mathlib
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.GrandUnification.TypeDWeylSemidirectAction

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.GrandUnification.TypeDWeyl

namespace InfoGeometry.GrandUnification.CantorLimit

def padZeros (i j : ℕ) (hij : i ≤ j) : Bitword (Fin i) →ₗ[ZMod 2] Bitword (Fin j) where
  toFun w k := if h : k.val < i then w ⟨k.val, h⟩ else 0
  map_add' x y := by ext k; dsimp; split_ifs with h <;> rfl
  map_smul' c x := by ext k; dsimp; split_ifs with h <;> rfl

lemma padZeros_parity (i j : ℕ) (hij : i ≤ j) (w : Bitword (Fin i)) :
    bitwordParity (padZeros i j hij w) = bitwordParity w := by
  induction' j, hij using Nat.le_induction with k hk ih
  · dsimp [bitwordParity, padZeros, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro x _
    have h_lt : x.val < i := x.isLt
    simp [h_lt]
  · rw [← ih]
    dsimp [bitwordParity, padZeros, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fin.sum_univ_castSucc]
    have h_eq : (∑ x : Fin k, if h : (Fin.castSucc x).val < i then w ⟨(Fin.castSucc x).val, h⟩ else 0) = ∑ x : Fin k, if h : x.val < i then w ⟨x.val, h⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rfl
    rw [h_eq]
    have h_last : (if h : (Fin.last k).val < i then w ⟨(Fin.last k).val, h⟩ else 0) = 0 := by
      have h_not : ¬((Fin.last k).val < i) := by
        have h_eq_k : (Fin.last k).val = k := rfl
        rw [h_eq_k]
        omega
      rw [dif_neg h_not]
    rw [h_last, add_zero]

def typeDTransitionMap (i j : ℕ) (hij : i ≤ j) : 
    TypeDTransitionSubgroup (Fin i) →ₗ[ZMod 2] TypeDTransitionSubgroup (Fin j) where
  toFun w := ⟨padZeros i j hij w.val, by
    have hw := w.property
    change bitwordParity w.val = 0 at hw
    change bitwordParity (padZeros i j hij w.val) = 0
    rw [padZeros_parity]
    exact hw⟩
  map_add' x y := Subtype.ext ((padZeros i j hij).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((padZeros i j hij).map_smul c x.val)

def typeDSystem : ℕ ⥤ ModuleCat (ZMod 2) where
  obj n := ModuleCat.of (ZMod 2) (TypeDTransitionSubgroup (Fin n))
  map {i j} hij := ModuleCat.ofHom (typeDTransitionMap i j (leOfHom hij))
  map_id i := by
    ext ⟨w, hw⟩ k
    dsimp [ModuleCat.ofHom, typeDTransitionMap, padZeros, leOfHom]
    have h : k.val < i := k.isLt
    simp [h]
  map_comp {i j k} f g := by
    ext ⟨w, hw⟩ x
    dsimp [ModuleCat.ofHom, typeDTransitionMap, padZeros, leOfHom]
    by_cases h_lt_i : x.val < i
    · have h_lt_j : x.val < j := by
        have h_ij : i ≤ j := leOfHom f
        omega
      simp [h_lt_i, h_lt_j]
    · by_cases h_lt_j : x.val < j
      · simp [h_lt_i, h_lt_j]
      · simp [h_lt_i, h_lt_j]

noncomputable def TypeDCantorLimit := colimit typeDSystem

end InfoGeometry.GrandUnification.CantorLimit
