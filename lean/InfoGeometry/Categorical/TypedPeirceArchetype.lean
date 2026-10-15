/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Abel

/-!
# Pure Categorical Split Involutions and Peirce Projectors

This module formalizes the algebraic and categorical foundations of split involutions
and chiral Peirce decompositions using standalone definitions, lemmas, and theorems.
All properties are established via direct mathematical proofs without intermediate
witness structures.
-/

namespace InfoGeometry.Categorical

open CategoryTheory
open CategoryTheory.Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Canonical Projector Definitions -/

/-- Positive Peirce projector constructed from retraction and section data. -/
@[inline]
def peircePlus {X X_plus : C} (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X) : X ⟶ X :=
  p_plus ≫ i_plus

/-- Negative Peirce projector constructed from retraction and section data. -/
@[inline]
def peirceMinus {X X_minus : C} (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X) : X ⟶ X :=
  p_minus ≫ i_minus

/-! ### 2. Idempotency Theorems -/

/-- The positive Peirce projector is idempotent: `P₊ ∘ P₊ = P₊`. -/
theorem peirce_plus_idempotent {X X_plus : C}
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (hid_plus : i_plus ≫ p_plus = 𝟙 X_plus) :
    peircePlus p_plus i_plus ≫ peircePlus p_plus i_plus = peircePlus p_plus i_plus := by
  dsimp [peircePlus]
  calc
    (p_plus ≫ i_plus) ≫ (p_plus ≫ i_plus)
      = p_plus ≫ (i_plus ≫ p_plus) ≫ i_plus := by simp [Category.assoc]
    _ = p_plus ≫ 𝟙 X_plus ≫ i_plus := by rw [hid_plus]
    _ = p_plus ≫ i_plus := by simp

/-- The negative Peirce projector is idempotent: `P₋ ∘ P₋ = P₋`. -/
theorem peirce_minus_idempotent {X X_minus : C}
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hid_minus : i_minus ≫ p_minus = 𝟙 X_minus) :
    peirceMinus p_minus i_minus ≫ peirceMinus p_minus i_minus = peirceMinus p_minus i_minus := by
  dsimp [peirceMinus]
  calc
    (p_minus ≫ i_minus) ≫ (p_minus ≫ i_minus)
      = p_minus ≫ (i_minus ≫ p_minus) ≫ i_minus := by simp [Category.assoc]
    _ = p_minus ≫ 𝟙 X_minus ≫ i_minus := by rw [hid_minus]
    _ = p_minus ≫ i_minus := by simp

/-! ### 3. Orthogonality Theorems (Zero Seam Noise) -/

/-- Mutual annihilation of chiral projections: `P₊ ∘ P₋ = 0`. -/
theorem peirce_plus_annihilates_minus {X X_plus X_minus : C}
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (horth_pm : i_plus ≫ p_minus = 0) :
    peircePlus p_plus i_plus ≫ peirceMinus p_minus i_minus = 0 := by
  dsimp [peircePlus, peirceMinus]
  calc
    (p_plus ≫ i_plus) ≫ (p_minus ≫ i_minus)
      = p_plus ≫ (i_plus ≫ p_minus) ≫ i_minus := by simp [Category.assoc]
    _ = p_plus ≫ 0 ≫ i_minus := by rw [horth_pm]
    _ = 0 := by simp

/-- Mutual annihilation of chiral projections: `P₋ ∘ P₊ = 0`. -/
theorem peirce_minus_annihilates_plus {X X_plus X_minus : C}
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (horth_mp : i_minus ≫ p_plus = 0) :
    peirceMinus p_minus i_minus ≫ peircePlus p_plus i_plus = 0 := by
  dsimp [peircePlus, peirceMinus]
  calc
    (p_minus ≫ i_minus) ≫ (p_plus ≫ i_plus)
      = p_minus ≫ (i_minus ≫ p_plus) ≫ i_plus := by simp [Category.assoc]
    _ = p_minus ≫ 0 ≫ i_plus := by rw [horth_mp]
    _ = 0 := by simp

/-! ### 4. Canonical splitting on an actual biproduct -/

section Biproduct

variable {X_plus X_minus : C} [CategoryTheory.Limits.HasBinaryBiproduct X_plus X_minus]

/-- The positive projector on a binary biproduct. -/
noncomputable def biprodPeircePlus : X_plus ⊞ X_minus ⟶ X_plus ⊞ X_minus :=
  CategoryTheory.Limits.biprod.fst ≫ CategoryTheory.Limits.biprod.inl

/-- The negative projector on a binary biproduct. -/
noncomputable def biprodPeirceMinus : X_plus ⊞ X_minus ⟶ X_plus ⊞ X_minus :=
  CategoryTheory.Limits.biprod.snd ≫ CategoryTheory.Limits.biprod.inr

/-- The grading involution induced by the biproduct decomposition. -/
noncomputable def biprodPeirceInvolution : X_plus ⊞ X_minus ⟶ X_plus ⊞ X_minus :=
  biprodPeircePlus - biprodPeirceMinus

/-- The canonical projectors of a biproduct sum to its identity, by the
biproduct resolution of the identity. -/
theorem biprod_peirce_partition_of_unity :
    biprodPeircePlus (X_plus := X_plus) (X_minus := X_minus) +
      biprodPeirceMinus (X_plus := X_plus) (X_minus := X_minus) =
        𝟙 (X_plus ⊞ X_minus) := by
  exact CategoryTheory.Limits.biprod.total

/-- The positive biproduct projector is idempotent. -/
theorem biprod_peirce_plus_idempotent :
    biprodPeircePlus (X_plus := X_plus) (X_minus := X_minus) ≫
      biprodPeircePlus (X_plus := X_plus) (X_minus := X_minus) =
        biprodPeircePlus (X_plus := X_plus) (X_minus := X_minus) := by
  simp [biprodPeircePlus, Category.assoc]

/-- The negative biproduct projector is idempotent. -/
theorem biprod_peirce_minus_idempotent :
    biprodPeirceMinus (X_plus := X_plus) (X_minus := X_minus) ≫
      biprodPeirceMinus (X_plus := X_plus) (X_minus := X_minus) =
        biprodPeirceMinus (X_plus := X_plus) (X_minus := X_minus) := by
  simp [biprodPeirceMinus, Category.assoc]

/-- The canonical biproduct projectors annihilate in either order. -/
theorem biprod_peirce_plus_minus_zero :
    biprodPeircePlus (X_plus := X_plus) (X_minus := X_minus) ≫
      biprodPeirceMinus (X_plus := X_plus) (X_minus := X_minus) = 0 := by
  simp [biprodPeircePlus, biprodPeirceMinus, Category.assoc]

theorem biprod_peirce_minus_plus_zero :
    biprodPeirceMinus (X_plus := X_plus) (X_minus := X_minus) ≫
      biprodPeircePlus (X_plus := X_plus) (X_minus := X_minus) = 0 := by
  simp [biprodPeircePlus, biprodPeirceMinus, Category.assoc]

/-- The canonical biproduct grading operator is an involution. -/
theorem biprod_peirce_involution_sq :
    biprodPeirceInvolution (X_plus := X_plus) (X_minus := X_minus) ≫
      biprodPeirceInvolution (X_plus := X_plus) (X_minus := X_minus) =
        𝟙 (X_plus ⊞ X_minus) := by
  simp only [biprodPeirceInvolution, sub_comp, comp_sub,
    biprod_peirce_plus_idempotent, biprod_peirce_plus_minus_zero,
    biprod_peirce_minus_plus_zero, biprod_peirce_minus_idempotent,
    sub_zero, zero_sub, sub_neg_eq_add]
  exact biprod_peirce_partition_of_unity

end Biproduct

/-! ### 5. Split Decomposition Consequences -/

/-! ### 5. Chiral Eigenvalue Localization -/

/-- Positive section is an incoming chiral eigenstate: `i₊ ≫ ε = i₊`. -/
theorem chiral_positive_section_eigenvalue {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hid_plus : i_plus ≫ p_plus = 𝟙 X_plus)
    (horth_pm : i_plus ≫ p_minus = 0)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    i_plus ≫ eps = i_plus := by
  rw [← hdecomp_eps, comp_sub]
  calc
    i_plus ≫ (p_plus ≫ i_plus) - i_plus ≫ (p_minus ≫ i_minus)
      = (i_plus ≫ p_plus) ≫ i_plus - (i_plus ≫ p_minus) ≫ i_minus := by simp [Category.assoc]
    _ = 𝟙 X_plus ≫ i_plus - 0 ≫ i_minus := by rw [hid_plus, horth_pm]
    _ = i_plus := by simp

/-- Negative section is an outgoing chiral eigenstate: `i₋ ≫ ε = - i₋`. -/
theorem chiral_negative_section_eigenvalue {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hid_minus : i_minus ≫ p_minus = 𝟙 X_minus)
    (horth_mp : i_minus ≫ p_plus = 0)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    i_minus ≫ eps = - i_minus := by
  rw [← hdecomp_eps, comp_sub]
  calc
    i_minus ≫ (p_plus ≫ i_plus) - i_minus ≫ (p_minus ≫ i_minus)
      = (i_minus ≫ p_plus) ≫ i_plus - (i_minus ≫ p_minus) ≫ i_minus := by simp [Category.assoc]
    _ = 0 ≫ i_plus - 𝟙 X_minus ≫ i_minus := by rw [horth_mp, hid_minus]
    _ = - i_minus := by simp

/-- Involution preserves the positive projection: `ε ≫ p₊ = p₊`. -/
theorem chiral_positive_projection_eigenvalue {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hid_plus : i_plus ≫ p_plus = 𝟙 X_plus)
    (horth_mp : i_minus ≫ p_plus = 0)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    eps ≫ p_plus = p_plus := by
  rw [← hdecomp_eps, sub_comp]
  calc
    (p_plus ≫ i_plus) ≫ p_plus - (p_minus ≫ i_minus) ≫ p_plus
      = p_plus ≫ (i_plus ≫ p_plus) - p_minus ≫ (i_minus ≫ p_plus) := by simp [Category.assoc]
    _ = p_plus ≫ 𝟙 X_plus - p_minus ≫ 0 := by rw [hid_plus, horth_mp]
    _ = p_plus := by simp

/-- Involution inverts the negative projection: `ε ≫ p₋ = - p₋`. -/
theorem chiral_negative_projection_eigenvalue {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hid_minus : i_minus ≫ p_minus = 𝟙 X_minus)
    (horth_pm : i_plus ≫ p_minus = 0)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    eps ≫ p_minus = - p_minus := by
  rw [← hdecomp_eps, sub_comp]
  calc
    (p_plus ≫ i_plus) ≫ p_minus - (p_minus ≫ i_minus) ≫ p_minus
      = p_plus ≫ (i_plus ≫ p_minus) - p_minus ≫ (i_minus ≫ p_minus) := by simp [Category.assoc]
    _ = p_plus ≫ 0 - p_minus ≫ 𝟙 X_minus := by rw [horth_pm, hid_minus]
    _ = - p_minus := by simp

/-! ### 6. Derivation of the Involution Identity -/

/-- Direct-sum splitting implies the involution identity `ε ≫ ε = 𝟙 X`. -/
theorem split_involution_identity {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hid_plus : i_plus ≫ p_plus = 𝟙 X_plus)
    (hid_minus : i_minus ≫ p_minus = 𝟙 X_minus)
    (horth_pm : i_plus ≫ p_minus = 0)
    (horth_mp : i_minus ≫ p_plus = 0)
    (hdecomp_id : p_plus ≫ i_plus + p_minus ≫ i_minus = 𝟙 X)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    eps ≫ eps = 𝟙 X := by
  have h_split : eps ≫ eps = (peircePlus p_plus i_plus - peirceMinus p_minus i_minus) ≫ eps := by
    rw [← hdecomp_eps]
    rfl
  have h_distrib :
      (peircePlus p_plus i_plus - peirceMinus p_minus i_minus) ≫ eps =
      peircePlus p_plus i_plus ≫ eps - peirceMinus p_minus i_minus ≫ eps :=
    sub_comp _ _ _
  have h_plus_action : peircePlus p_plus i_plus ≫ eps = p_plus ≫ (i_plus ≫ eps) := by
    dsimp [peircePlus]
    rw [Category.assoc]
  have h_minus_action : peirceMinus p_minus i_minus ≫ eps = p_minus ≫ (i_minus ≫ eps) := by
    dsimp [peirceMinus]
    rw [Category.assoc]
  rw [h_split, h_distrib, h_plus_action, h_minus_action]
  rw [chiral_positive_section_eigenvalue eps p_plus i_plus p_minus i_minus hid_plus horth_pm hdecomp_eps]
  rw [chiral_negative_section_eigenvalue eps p_plus i_plus p_minus i_minus hid_minus horth_mp hdecomp_eps]
  rw [comp_neg, sub_neg_eq_add]
  exact hdecomp_id

/-! ### 7. Integer-Linear Inversion Laws -/

/-- `(2 : ℤ) • P₊ = 𝟙 X + ε` without requiring an invertible 2 in the scalar ring. -/
theorem two_smul_peirce_plus {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hdecomp_id : p_plus ≫ i_plus + p_minus ≫ i_minus = 𝟙 X)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    (2 : ℤ) • peircePlus p_plus i_plus = 𝟙 X + eps := by
  rw [← hdecomp_id, ← hdecomp_eps]
  dsimp [peircePlus, peirceMinus]
  have h2 : (2 : ℤ) • (p_plus ≫ i_plus) = (p_plus ≫ i_plus) + (p_plus ≫ i_plus) := by
    rw [two_zsmul]
  rw [h2]
  abel

/-- `(2 : ℤ) • P₋ = 𝟙 X - ε` without requiring an invertible 2 in the scalar ring. -/
theorem two_smul_peirce_minus {X X_plus X_minus : C}
    (eps : X ⟶ X)
    (p_plus : X ⟶ X_plus) (i_plus : X_plus ⟶ X)
    (p_minus : X ⟶ X_minus) (i_minus : X_minus ⟶ X)
    (hdecomp_id : p_plus ≫ i_plus + p_minus ≫ i_minus = 𝟙 X)
    (hdecomp_eps : p_plus ≫ i_plus - p_minus ≫ i_minus = eps) :
    (2 : ℤ) • peirceMinus p_minus i_minus = 𝟙 X - eps := by
  rw [← hdecomp_id, ← hdecomp_eps]
  dsimp [peircePlus, peirceMinus]
  have h2 : (2 : ℤ) • (p_minus ≫ i_minus) = (p_minus ≫ i_minus) + (p_minus ≫ i_minus) := by
    rw [two_zsmul]
  rw [h2]
  abel

end InfoGeometry.Categorical
