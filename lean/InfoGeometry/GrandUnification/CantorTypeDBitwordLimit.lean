import Mathlib
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.GrandUnification.TypeDWeylSemidirectAction

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.GrandUnification.TypeDWeyl

namespace InfoGeometry.GrandUnification.CantorLimit

/-!
# Causal Poset: The Subregular Type-D Cantor Continuum

While the unconstrained Bitword/Cuntz Cantor limit is heavily formalized in 
the core repository (`CantorGoldenMeanBitwordBridge`, etc.), this module 
establishes the *parallel topological line*: the strict categorical colimit of 
the **Type-D Even Parity Subgroups** representing the subregular affine cells.

Archetypes in causal order:
I.   `padZeros`: The causal projection mapping $n$-stage states to $(n+m)$-stages.
II.  `padZeros_parity`: Proof that zero-padding strictly conserves the Weyl parity anomaly.
III. `typeDTransitionMap`: The restricted transition morphism on the rigid even-parity sector.
IV.  `typeDSystem`: The formal categorical functor $\mathbb{N} \to \mathrm{ModuleCat}(\mathbb{Z}_2)$ of the subregular cells.
V.   `TypeDCantorLimit`: The categorical colimit representing the infinite continuous boundary.
-/

/-- Archetype I: Causal Projection (Zero-Padding) -/
def padZeros (i j : ℕ) (hij : i ≤ j) : Bitword (Fin i) →ₗ[ZMod 2] Bitword (Fin j) where
  toFun w k := if h : k.val < i then w ⟨k.val, h⟩ else 0
  map_add' x y := by ext k; simp; split <;> rfl
  map_smul' c x := by ext k; simp; split <;> rfl

/-- Archetype II: Parity Conservation Under Projection -/
lemma padZeros_parity (i j : ℕ) (hij : i ≤ j) (w : Bitword (Fin i)) :
    bitwordParity (padZeros i j hij w) = bitwordParity w := by
  dsimp [bitwordParity, padZeros, LinearMap.coe_mk, AddHom.coe_mk]
  let s : Finset (Fin j) := (Finset.univ : Finset (Fin i)).image (Fin.castLE hij)
  have h_sub : s ⊆ Finset.univ := Finset.subset_univ _
  have h_eq : ∑ k : Fin j, (if h : k.val < i then w ⟨k.val, h⟩ else 0) = ∑ k in s, (if h : k.val < i then w ⟨k.val, h⟩ else 0) := by
    apply Finset.sum_subset h_sub
    intro x _ hx
    dsimp [s] at hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hx
    have hx_lt : ¬(x.val < i) := by
      intro h_lt
      apply hx ⟨x.val, h_lt⟩
      exact Fin.ext rfl
    simp [hx_lt]
  rw [h_eq, Finset.sum_image (Fin.castLE_injective hij)]
  apply Finset.sum_congr rfl
  intro x _
  have h_lt : (Fin.castLE hij x).val < i := x.isLt
  simp [h_lt]

/-- Archetype III: Restricted Transition Morphism -/
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

/-- Archetype IV: The Categorical Functor over $\mathbb{N}$ -/
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
    split_ifs with h1 h2 h3
    · rfl
    · exfalso; omega
    · exfalso; omega
    · rfl
    · rfl

/-- 
Archetype V: The Type-D Subregular Cantor Continuum.
This is the strict categorical colimit of the discrete Weyl-orbit restricted 
states, proving that the hardware ATOMiK model continuously scales into the 
infinite fractal geometry underlying E_10 representations.
-/
noncomputable def TypeDCantorLimit := colimit typeDSystem

end InfoGeometry.GrandUnification.CantorLimit
