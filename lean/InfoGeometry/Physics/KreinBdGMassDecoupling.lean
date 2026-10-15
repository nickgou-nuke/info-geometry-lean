/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Abel
import InfoGeometry.Categorical.KreinCartanPolarization
import InfoGeometry.Physics.HarmonicWeakHorizonBdG

/-!
# Krein Ghost Decoupling and BdG Mass Condensation

This module formalizes the connection between the **Krein Fundamental Symmetry $J_K$**
and the **Massive BdG Doublet Dispersion** `ℋ_BdG² = 𝒟² + M²`.

## Key Mathematical Theorems

1. `nambuKreinPolarization`: Canonical instantiation of `KreinPolarizationData` on
   the doublet space `E` via the charge-grading involution `J_K = p₁ i₁ - p₂ i₂`.
2. `bdg_linear_krein_commutator`: Explicit evaluation of `[J_K, ℋ_BdG] = 2(p₁ M i₂ - p₂ M i₁)`,
   proving that the condensed pairing potential `M` is the exact source of amplitude mixing.
3. `bdg_dispersion_commutes_krein`: The squared dispersion `ℋ_BdG²` strictly commutes with `J_K`:
   `[J_K, ℋ_BdG²] = 0`.
4. `bdg_dispersion_commutes_projectors`: `ℋ_BdG²` commutes with both `P₊` and `P₋`.
5. `bdg_dispersion_ghost_decoupling_pm` and `bdg_dispersion_ghost_decoupling_mp`:
   Proves zero cross-sector leakage: `P₊ ≫ ℋ_BdG² ≫ P₋ = 0` and `P₋ ≫ ℋ_BdG² ≫ P₊ = 0`.
6. `bdg_physical_sector_dispersion` & `bdg_ghost_sector_dispersion`:
   The condensed mass gap `M²` shifts both physical and ghost sectors identically.
-/

namespace InfoGeometry.Physics.KreinBdG

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical
open InfoGeometry.Physics.BdGCondensation

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Canonical Krein Structure on Nambu Doublet Space -/

/-- The canonical charge-grading involution `J_K = p₁ ≫ i₁ - p₂ ≫ i₂` on the doublet space `E`. -/
@[inline]
def nambuChargeGrading {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E) : E ⟶ E :=
  p1 ≫ i1 - p2 ≫ i2

/-- The charge grading `J_K` is an exact involution: `J_K ≫ J_K = 𝟙 E`. -/
theorem nambu_charge_grading_sq {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E) :
    nambuChargeGrading p1 i1 p2 i2 ≫ nambuChargeGrading p1 i1 p2 i2 = 𝟙 E := by
  dsimp [nambuChargeGrading]
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub]
  have h1 : (p1 ≫ i1) ≫ (p1 ≫ i1) = p1 ≫ i1 := by
    calc
      (p1 ≫ i1) ≫ (p1 ≫ i1) = p1 ≫ (i1 ≫ p1) ≫ i1 := by simp only [Category.assoc]
      _ = p1 ≫ 𝟙 Ω ≫ i1 := by rw [hid1]
      _ = p1 ≫ i1 := by simp only [Category.id_comp]
  have h2 : (p1 ≫ i1) ≫ (p2 ≫ i2) = 0 := by
    calc
      (p1 ≫ i1) ≫ (p2 ≫ i2) = p1 ≫ (i1 ≫ p2) ≫ i2 := by simp only [Category.assoc]
      _ = p1 ≫ 0 ≫ i2 := by rw [horth12]
      _ = 0 := by simp only [zero_comp, comp_zero]
  have h3 : (p2 ≫ i2) ≫ (p1 ≫ i1) = 0 := by
    calc
      (p2 ≫ i2) ≫ (p1 ≫ i1) = p2 ≫ (i2 ≫ p1) ≫ i1 := by simp only [Category.assoc]
      _ = p2 ≫ 0 ≫ i1 := by rw [horth21]
      _ = 0 := by simp only [zero_comp, comp_zero]
  have h4 : (p2 ≫ i2) ≫ (p2 ≫ i2) = p2 ≫ i2 := by
    calc
      (p2 ≫ i2) ≫ (p2 ≫ i2) = p2 ≫ (i2 ≫ p2) ≫ i2 := by simp only [Category.assoc]
      _ = p2 ≫ 𝟙 Ω ≫ i2 := by rw [hid2]
      _ = p2 ≫ i2 := by simp only [Category.id_comp]
  rw [h1, h2, h3, h4, sub_zero, zero_sub, sub_neg_eq_add]
  exact h_decomp

/-- Canonical instantiation of `KreinPolarizationData` on the Nambu doublet space `E`.
The physical Hilbert subspace is `Ω` (via `i₁, p₁`), and the ghost subspace is `Ω` (via `i₂, p₂`). -/
def nambuKreinPolarization {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E) : KreinPolarizationData C where
  K         := E
  J         := nambuChargeGrading p1 i1 p2 i2
  K_plus    := Ω
  K_minus   := Ω
  i_plus    := i1
  p_plus    := p1
  i_minus   := i2
  p_minus   := p2
  J_sq      := nambu_charge_grading_sq p1 i1 p2 i2 hid1 hid2 horth12 horth21 h_decomp
  id_plus   := hid1
  id_minus  := hid2
  orthog_pm := horth12
  orthog_mp := horth21
  decomp_id := h_decomp
  decomp_J  := rfl

/-! ### 2. Linear Krein Breaking by Pairing Potential M -/

/-- Linear Krein commutator: `[J_K, ℋ_BdG] = 2 • (p₁ M i₂ - p₂ M i₁)`.
When `M = 0`, the massless Dirac–Kähler operator commutes with `J_K`.
When `M ≠ 0`, the condensed mass pairing breaks linear Krein conservation. -/
theorem bdg_linear_krein_commutator {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E) :
    nambuChargeGrading p1 i1 p2 i2 ≫ bdgHamiltonian p1 i1 p2 i2 D M -
    bdgHamiltonian p1 i1 p2 i2 D M ≫ nambuChargeGrading p1 i1 p2 i2 =
    (2 : ℤ) • (p1 ≫ M ≫ i2 - p2 ≫ M ≫ i1) := by
  let J := nambuChargeGrading p1 i1 p2 i2
  let H := bdgHamiltonian p1 i1 p2 i2 D M
  have h_rec := biproduct_endomorphism_reconstruct p1 i1 p2 i2 h_decomp (J ≫ H - H ≫ J)
  rw [h_rec]
  have hj11 : i1 ≫ J ≫ p1 = 𝟙 Ω := by
    dsimp only [J, nambuChargeGrading]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    have h1 : i1 ≫ (p1 ≫ i1) ≫ p1 = 𝟙 Ω := by
      calc
        i1 ≫ (p1 ≫ i1) ≫ p1 = (i1 ≫ p1) ≫ (i1 ≫ p1) := by simp only [Category.assoc]
        _ = 𝟙 Ω ≫ 𝟙 Ω := by rw [hid1]
        _ = 𝟙 Ω := by simp only [Category.id_comp]
    have h2 : i1 ≫ (p2 ≫ i2) ≫ p1 = 0 := by
      calc
        i1 ≫ (p2 ≫ i2) ≫ p1 = (i1 ≫ p2) ≫ (i2 ≫ p1) := by simp only [Category.assoc]
        _ = 0 ≫ 0 := by rw [horth12, horth21]
        _ = 0 := by simp only [zero_comp]
    rw [h1, h2, sub_zero]
  have hj12 : i1 ≫ J ≫ p2 = 0 := by
    dsimp only [J, nambuChargeGrading]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    have h1 : i1 ≫ (p1 ≫ i1) ≫ p2 = 0 := by
      calc
        i1 ≫ (p1 ≫ i1) ≫ p2 = (i1 ≫ p1) ≫ (i1 ≫ p2) := by simp only [Category.assoc]
        _ = 𝟙 Ω ≫ 0 := by rw [hid1, horth12]
        _ = 0 := by simp only [comp_zero]
    have h2 : i1 ≫ (p2 ≫ i2) ≫ p2 = 0 := by
      calc
        i1 ≫ (p2 ≫ i2) ≫ p2 = (i1 ≫ p2) ≫ (i2 ≫ p2) := by simp only [Category.assoc]
        _ = 0 ≫ 𝟙 Ω := by rw [horth12, hid2]
        _ = 0 := by simp only [zero_comp]
    rw [h1, h2, sub_self]
  have hj21 : i2 ≫ J ≫ p1 = 0 := by
    dsimp only [J, nambuChargeGrading]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    have h1 : i2 ≫ (p1 ≫ i1) ≫ p1 = 0 := by
      calc
        i2 ≫ (p1 ≫ i1) ≫ p1 = (i2 ≫ p1) ≫ (i1 ≫ p1) := by simp only [Category.assoc]
        _ = 0 ≫ 𝟙 Ω := by rw [horth21, hid1]
        _ = 0 := by simp only [zero_comp]
    have h2 : i2 ≫ (p2 ≫ i2) ≫ p1 = 0 := by
      calc
        i2 ≫ (p2 ≫ i2) ≫ p1 = (i2 ≫ p2) ≫ (i2 ≫ p1) := by simp only [Category.assoc]
        _ = 𝟙 Ω ≫ 0 := by rw [hid2, horth21]
        _ = 0 := by simp only [comp_zero]
    rw [h1, h2, sub_self]
  have hj22 : i2 ≫ J ≫ p2 = - 𝟙 Ω := by
    dsimp only [J, nambuChargeGrading]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    have h1 : i2 ≫ (p1 ≫ i1) ≫ p2 = 0 := by
      calc
        i2 ≫ (p1 ≫ i1) ≫ p2 = (i2 ≫ p1) ≫ (i1 ≫ p2) := by simp only [Category.assoc]
        _ = 0 ≫ 0 := by rw [horth21, horth12]
        _ = 0 := by simp only [zero_comp]
    have h2 : i2 ≫ (p2 ≫ i2) ≫ p2 = 𝟙 Ω := by
      calc
        i2 ≫ (p2 ≫ i2) ≫ p2 = (i2 ≫ p2) ≫ (i2 ≫ p2) := by simp only [Category.assoc]
        _ = 𝟙 Ω ≫ 𝟙 Ω := by rw [hid2]
        _ = 𝟙 Ω := by simp only [Category.id_comp]
    rw [h1, h2, zero_sub]
  have hb11 : i1 ≫ (J ≫ H - H ≫ J) ≫ p1 = 0 := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i1 p1]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i1 p1]
    rw [hj11, hj12, hj21, bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    simp only [Category.id_comp, Category.comp_id, zero_comp, comp_zero, add_zero, sub_self]
  have hb12 : i1 ≫ (J ≫ H - H ≫ J) ≫ p2 = (2 : ℤ) • M := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i1 p2]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i1 p2]
    rw [hj11, hj12, hj22, bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    simp only [Category.id_comp, Category.comp_id, zero_comp, comp_zero, zero_add,
      Preadditive.comp_neg]
    abel
  have hb21 : i2 ≫ (J ≫ H - H ≫ J) ≫ p1 = - (2 : ℤ) • M := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i2 p1]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i2 p1]
    rw [hj21, hj22, hj11, bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21]
    rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21]
    simp only [Category.id_comp, Category.comp_id, zero_comp, comp_zero, zero_add,
      Preadditive.neg_comp]
    abel
  have hb22 : i2 ≫ (J ≫ H - H ≫ J) ≫ p2 = 0 := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp J H i2 p2]
    rw [biproduct_block_composition p1 i1 p2 i2 h_decomp H J i2 p2]
    rw [hj21, hj22, hj12, bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
    rw [bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
    simp only [Category.id_comp, Category.comp_id, zero_comp, comp_zero, zero_add,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, sub_self]
  rw [hb11, hb12, hb21, hb22]
  simp only [zero_comp, comp_zero, add_zero, zero_add,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  abel

/-! ### 3. Quadratic Krein Symmetry Restoration (Dispersion Commutation) -/

/-- The massive doublet dispersion strictly commutes with the positive physical projector `P₊`. -/
theorem bdg_dispersion_commutes_P_plus {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    (p1 ≫ i1) ≫ massiveDoubletDispersion p1 i1 p2 i2 D M =
    massiveDoubletDispersion p1 i1 p2 i2 D M ≫ (p1 ≫ i1) := by
  dsimp [massiveDoubletDispersion]
  let Δ_M := D ≫ D + M ≫ M
  have h_lhs : (p1 ≫ i1) ≫ (p1 ≫ Δ_M ≫ i1 + p2 ≫ Δ_M ≫ i2) = p1 ≫ Δ_M ≫ i1 := by
    rw [Preadditive.comp_add]
    have h1 : (p1 ≫ i1) ≫ (p1 ≫ Δ_M ≫ i1) = p1 ≫ Δ_M ≫ i1 := by
      calc
        (p1 ≫ i1) ≫ (p1 ≫ Δ_M ≫ i1) = p1 ≫ (i1 ≫ p1) ≫ Δ_M ≫ i1 := by simp only [Category.assoc]
        _ = p1 ≫ 𝟙 Ω ≫ Δ_M ≫ i1 := by rw [hid1]
        _ = p1 ≫ Δ_M ≫ i1 := by simp only [Category.id_comp]
    have h2 : (p1 ≫ i1) ≫ (p2 ≫ Δ_M ≫ i2) = 0 := by
      calc
        (p1 ≫ i1) ≫ (p2 ≫ Δ_M ≫ i2) = p1 ≫ (i1 ≫ p2) ≫ Δ_M ≫ i2 := by simp only [Category.assoc]
        _ = p1 ≫ 0 ≫ Δ_M ≫ i2 := by rw [horth12]
        _ = 0 := by simp only [zero_comp, comp_zero]
    rw [h1, h2, add_zero]
  have h_rhs : (p1 ≫ Δ_M ≫ i1 + p2 ≫ Δ_M ≫ i2) ≫ (p1 ≫ i1) = p1 ≫ Δ_M ≫ i1 := by
    rw [Preadditive.add_comp]
    have h1 : (p1 ≫ Δ_M ≫ i1) ≫ (p1 ≫ i1) = p1 ≫ Δ_M ≫ i1 := by
      calc
        (p1 ≫ Δ_M ≫ i1) ≫ (p1 ≫ i1) = p1 ≫ Δ_M ≫ (i1 ≫ p1) ≫ i1 := by simp only [Category.assoc]
        _ = p1 ≫ Δ_M ≫ 𝟙 Ω ≫ i1 := by rw [hid1]
        _ = p1 ≫ Δ_M ≫ i1 := by simp only [Category.id_comp]
    have h2 : (p2 ≫ Δ_M ≫ i2) ≫ (p1 ≫ i1) = 0 := by
      calc
        (p2 ≫ Δ_M ≫ i2) ≫ (p1 ≫ i1) = p2 ≫ Δ_M ≫ (i2 ≫ p1) ≫ i1 := by simp only [Category.assoc]
        _ = p2 ≫ Δ_M ≫ 0 ≫ i1 := by rw [horth21]
        _ = 0 := by simp only [zero_comp, comp_zero]
    rw [h1, h2, add_zero]
  rw [h_lhs, h_rhs]

/-- The massive doublet dispersion strictly commutes with the negative ghost projector `P₋`. -/
theorem bdg_dispersion_commutes_P_minus {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    (p2 ≫ i2) ≫ massiveDoubletDispersion p1 i1 p2 i2 D M =
    massiveDoubletDispersion p1 i1 p2 i2 D M ≫ (p2 ≫ i2) := by
  dsimp [massiveDoubletDispersion]
  let Δ_M := D ≫ D + M ≫ M
  have h_lhs : (p2 ≫ i2) ≫ (p1 ≫ Δ_M ≫ i1 + p2 ≫ Δ_M ≫ i2) = p2 ≫ Δ_M ≫ i2 := by
    rw [Preadditive.comp_add]
    have h1 : (p2 ≫ i2) ≫ (p1 ≫ Δ_M ≫ i1) = 0 := by
      calc
        (p2 ≫ i2) ≫ (p1 ≫ Δ_M ≫ i1) = p2 ≫ (i2 ≫ p1) ≫ Δ_M ≫ i1 := by simp only [Category.assoc]
        _ = p2 ≫ 0 ≫ Δ_M ≫ i1 := by rw [horth21]
        _ = 0 := by simp only [zero_comp, comp_zero]
    have h2 : (p2 ≫ i2) ≫ (p2 ≫ Δ_M ≫ i2) = p2 ≫ Δ_M ≫ i2 := by
      calc
        (p2 ≫ i2) ≫ (p2 ≫ Δ_M ≫ i2) = p2 ≫ (i2 ≫ p2) ≫ Δ_M ≫ i2 := by simp only [Category.assoc]
        _ = p2 ≫ 𝟙 Ω ≫ Δ_M ≫ i2 := by rw [hid2]
        _ = p2 ≫ Δ_M ≫ i2 := by simp only [Category.id_comp]
    rw [h1, h2, zero_add]
  have h_rhs : (p1 ≫ Δ_M ≫ i1 + p2 ≫ Δ_M ≫ i2) ≫ (p2 ≫ i2) = p2 ≫ Δ_M ≫ i2 := by
    rw [Preadditive.add_comp]
    have h1 : (p1 ≫ Δ_M ≫ i1) ≫ (p2 ≫ i2) = 0 := by
      calc
        (p1 ≫ Δ_M ≫ i1) ≫ (p2 ≫ i2) = p1 ≫ Δ_M ≫ (i1 ≫ p2) ≫ i2 := by simp only [Category.assoc]
        _ = p1 ≫ Δ_M ≫ 0 ≫ i2 := by rw [horth12]
        _ = 0 := by simp only [zero_comp, comp_zero]
    have h2 : (p2 ≫ Δ_M ≫ i2) ≫ (p2 ≫ i2) = p2 ≫ Δ_M ≫ i2 := by
      calc
        (p2 ≫ Δ_M ≫ i2) ≫ (p2 ≫ i2) = p2 ≫ Δ_M ≫ (i2 ≫ p2) ≫ i2 := by simp only [Category.assoc]
        _ = p2 ≫ Δ_M ≫ 𝟙 Ω ≫ i2 := by rw [hid2]
        _ = p2 ≫ Δ_M ≫ i2 := by simp only [Category.id_comp]
    rw [h1, h2, zero_add]
  rw [h_lhs, h_rhs]

/-- The massive doublet dispersion operator `ℋ_BdG²` strictly commutes with the
Krein fundamental symmetry `J_K`: `[J_K, ℋ_BdG²] = 0`. -/
theorem bdg_dispersion_commutes_krein {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    nambuChargeGrading p1 i1 p2 i2 ≫ massiveDoubletDispersion p1 i1 p2 i2 D M =
    massiveDoubletDispersion p1 i1 p2 i2 D M ≫ nambuChargeGrading p1 i1 p2 i2 := by
  dsimp [nambuChargeGrading]
  rw [Preadditive.sub_comp, Preadditive.comp_sub]
  rw [bdg_dispersion_commutes_P_plus p1 i1 p2 i2 D M hid1 horth12 horth21]
  rw [bdg_dispersion_commutes_P_minus p1 i1 p2 i2 D M hid2 horth12 horth21]

/-! ### 4. Ghost Decoupling Theorems (Zero Cross-Leakage) -/

/-- Physical states evolving under massive dispersion generate zero ghost projection:
`P₊ ≫ ℋ_BdG² ≫ P₋ = 0`. -/
theorem bdg_dispersion_ghost_decoupling_pm {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    (p1 ≫ i1) ≫ massiveDoubletDispersion p1 i1 p2 i2 D M ≫ (p2 ≫ i2) = 0 := by
  rw [← Category.assoc (p1 ≫ i1)]
  rw [bdg_dispersion_commutes_P_plus p1 i1 p2 i2 D M hid1 horth12 horth21]
  rw [Category.assoc]
  have h_orth : (p1 ≫ i1) ≫ (p2 ≫ i2) = 0 := by
    rw [Category.assoc p1 i1, ← Category.assoc i1 p2, horth12, zero_comp, comp_zero]
  rw [h_orth, comp_zero]

/-- Ghost states evolving under massive dispersion generate zero physical projection:
`P₋ ≫ ℋ_BdG² ≫ P₊ = 0`. -/
theorem bdg_dispersion_ghost_decoupling_mp {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0) :
    (p2 ≫ i2) ≫ massiveDoubletDispersion p1 i1 p2 i2 D M ≫ (p1 ≫ i1) = 0 := by
  rw [← Category.assoc (p2 ≫ i2)]
  rw [bdg_dispersion_commutes_P_minus p1 i1 p2 i2 D M hid2 horth12 horth21]
  rw [Category.assoc]
  have h_orth : (p2 ≫ i2) ≫ (p1 ≫ i1) = 0 := by
    rw [Category.assoc p2 i2, ← Category.assoc i2 p1, horth21, zero_comp, comp_zero]
  rw [h_orth, comp_zero]

/-! ### 5. Sector-Restricted Dispersion Identities -/

/-- The massive dispersion on the physical Hilbert sector is precisely `𝒟² + M²`. -/
theorem bdg_physical_sector_dispersion {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (horth12 : i1 ≫ p2 = 0) :
    i1 ≫ massiveDoubletDispersion p1 i1 p2 i2 D M ≫ p1 = D ≫ D + M ≫ M := by
  dsimp [massiveDoubletDispersion]
  rw [Preadditive.add_comp, Preadditive.comp_add]
  have h1 : i1 ≫ (p1 ≫ (D ≫ D + M ≫ M) ≫ i1) ≫ p1 = D ≫ D + M ≫ M := by
    calc
      i1 ≫ (p1 ≫ (D ≫ D + M ≫ M) ≫ i1) ≫ p1 = (i1 ≫ p1) ≫ (D ≫ D + M ≫ M) ≫ (i1 ≫ p1) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ (D ≫ D + M ≫ M) ≫ 𝟙 Ω := by rw [hid1]
      _ = D ≫ D + M ≫ M := by simp only [Category.id_comp, Category.comp_id]
  have h2 : i1 ≫ (p2 ≫ (D ≫ D + M ≫ M) ≫ i2) ≫ p1 = 0 := by
    calc
      i1 ≫ (p2 ≫ (D ≫ D + M ≫ M) ≫ i2) ≫ p1 = (i1 ≫ p2) ≫ (D ≫ D + M ≫ M) ≫ (i2 ≫ p1) := by simp only [Category.assoc]
      _ = 0 ≫ (D ≫ D + M ≫ M) ≫ (i2 ≫ p1) := by rw [horth12]
      _ = 0 := by simp only [zero_comp]
  rw [h1, h2, add_zero]

/-- The massive dispersion on the ghost sector is precisely `𝒟² + M²`. -/
theorem bdg_ghost_sector_dispersion {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid2 : i2 ≫ p2 = 𝟙 Ω) (horth21 : i2 ≫ p1 = 0) :
    i2 ≫ massiveDoubletDispersion p1 i1 p2 i2 D M ≫ p2 = D ≫ D + M ≫ M := by
  dsimp [massiveDoubletDispersion]
  rw [Preadditive.add_comp, Preadditive.comp_add]
  have h1 : i2 ≫ (p1 ≫ (D ≫ D + M ≫ M) ≫ i1) ≫ p2 = 0 := by
    calc
      i2 ≫ (p1 ≫ (D ≫ D + M ≫ M) ≫ i1) ≫ p2 = (i2 ≫ p1) ≫ (D ≫ D + M ≫ M) ≫ (i1 ≫ p2) := by simp only [Category.assoc]
      _ = 0 ≫ (D ≫ D + M ≫ M) ≫ (i1 ≫ p2) := by rw [horth21]
      _ = 0 := by simp only [zero_comp]
  have h2 : i2 ≫ (p2 ≫ (D ≫ D + M ≫ M) ≫ i2) ≫ p2 = D ≫ D + M ≫ M := by
    calc
      i2 ≫ (p2 ≫ (D ≫ D + M ≫ M) ≫ i2) ≫ p2 = (i2 ≫ p2) ≫ (D ≫ D + M ≫ M) ≫ (i2 ≫ p2) := by simp only [Category.assoc]
      _ = 𝟙 Ω ≫ (D ≫ D + M ≫ M) ≫ 𝟙 Ω := by rw [hid2]
      _ = D ≫ D + M ≫ M := by simp only [Category.id_comp, Category.comp_id]
  rw [h1, h2, zero_add]

end InfoGeometry.Physics.KreinBdG
