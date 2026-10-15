/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Abel
import InfoGeometry.Physics.ChevalleySpinorIdeal
import InfoGeometry.Physics.ChevalleyDyads
import InfoGeometry.Physics.HarmonicWeakHorizonBdG
import InfoGeometry.Physics.ChevalleyNambuCARBridge
import InfoGeometry.Physics.NambuSpinorHolonomy

/-!
# LogCFT Symplectic Spinor Bridge: Maslov $\mathbb{Z}_4$-Holonomy and Jordan Shear

This module bridges the Nambu spinor holonomy and complex structure
from `InfoGeometry.Physics.NambuSpinorHolonomy` with the Chevalley transition
dyad Jordan unipotent shear:

1. **Complex Structure & $\mathbb{Z}_4$-Holonomy**:
   - Reuses `nambuComplexStructure` $J = \mathcal{H}_{\text{BdG}}^2$ satisfying $J^2 = -\mathbb{1}_E$.
   - Reuses $J^4 = \mathbb{1}_E$ ($\mathbb{Z}_4$ Maslov index cycle).
   - Reuses $4\pi$ spinor invariance $\mathcal{H}^8 = \mathbb{1}_E$.
   - Reuses the round-trip transmutation identity $(P_+ J P_-)(P_- J P_+) = -P_+$.
2. **Logarithmic CFT ($c = -2$) Jordan Nilpotent Shear**:
   - Proves unipotent shear inversion $(\mathbb{1} + N)(\mathbb{1} - N) = \mathbb{1}$
     for any category nilpotent $N^2 = 0$.
   - Instantiates this unipotent shear on the Chevalley transition dyad $E_{01}$.
3. **Master Integration**:
   - Unifies the Nambu holonomy and the Chevalley Jordan shear into a single
     deduplicated synthesis theorem under the standard biproduct and CAR hypotheses.
-/

namespace InfoGeometry.Physics.LogCFTSymplecticBridge

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Physics.Chevalley
open InfoGeometry.Physics.ChevalleyDyads
open InfoGeometry.Physics.BdGCondensation
open InfoGeometry.Physics.ChevalleyNambuBridge
open InfoGeometry.Physics.NambuSpinorHolonomy

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Symplectic Complex Structure Re-export from Owner -/

/-- Canonical alias for the Nambu complex structure $J = \mathcal{H}_{\text{BdG}}^2$. -/
@[inline]
def symplecticJ {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω) : E ⟶ E :=
  nambuComplexStructure p1 i1 p2 i2 D M

/-- **Almost Complex Structure**: $J^2 = -\mathbb{1}_E$.
Directly delegates to the owner theorem `nambuComplexStructure_sq`. -/
theorem symplecticJ_sq_neg_one {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    symplecticJ p1 i1 p2 i2 D M ≫ symplecticJ p1 i1 p2 i2 D M = -𝟙 E :=
  nambuComplexStructure_sq p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR

/-- **$\mathbb{Z}_4$-Holonomy**: $J^4 = \mathbb{1}_E$.
Directly delegates to the owner theorem `nambuComplexStructure_pow_four`. -/
theorem symplecticJ_fourth_power_identity {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (symplecticJ p1 i1 p2 i2 D M ≫ symplecticJ p1 i1 p2 i2 D M) ≫
      (symplecticJ p1 i1 p2 i2 D M ≫ symplecticJ p1 i1 p2 i2 D M) = 𝟙 E := by
  dsimp [symplecticJ]
  rw [Category.assoc]
  exact nambuComplexStructure_pow_four p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR

/-- The $4\pi$ Spinor Rotation: $\mathcal{H}_{\text{BdG}}^8 = \mathbb{1}_E$.
Directly delegates to the owner theorem `bdg_pow_eight`. -/
theorem bdgHamiltonian_eighth_power_identity {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    let H := bdgHamiltonian p1 i1 p2 i2 D M
    ((H ≫ H) ≫ (H ≫ H)) ≫ ((H ≫ H) ≫ (H ≫ H)) = 𝟙 E :=
  bdg_pow_eight p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR

/-- **Fermionic Parity Sign in Round-Trip Transmutation**:
$(P_+ J P_-) \gg (P_- J P_+) = -P_+$.
Directly delegates to the owner theorem `transmutation_round_trip_physical_sign`. -/
theorem transmutation_round_trip_fermionic_sign {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    let P_plus := p1 ≫ i1
    let P_minus := p2 ≫ i2
    let J := symplecticJ p1 i1 p2 i2 D M
    (P_plus ≫ J ≫ P_minus) ≫ (P_minus ≫ J ≫ P_plus) = -P_plus :=
  transmutation_round_trip_physical_sign p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR

/-! ### 2. Logarithmic CFT ($c = -2$) Unipotent Jordan Shear -/

/-- Unipotent shear operator $\mathbb{1}_X + N$ generated by a nilpotent $N : X \longrightarrow X$. -/
@[inline]
def unipotentShear {X : C} (N : X ⟶ X) : X ⟶ X :=
  𝟙 X + N

/-- Dual unipotent shear operator $\mathbb{1}_X - N$. -/
@[inline]
def unipotentShearInv {X : C} (N : X ⟶ X) : X ⟶ X :=
  𝟙 X - N

/-- THEOREM: For any nilpotent morphism $N^2 = 0$, the unipotent shear is strictly invertible:
$(\mathbb{1}_X + N) \gg (\mathbb{1}_X - N) = \mathbb{1}_X$.
This is the categorical finite Jordan shear of $c = -2$ LogCFT. -/
theorem unipotentShear_mul_inv {X : C} (N : X ⟶ X) (hN : N ≫ N = 0) :
    unipotentShear N ≫ unipotentShearInv N = 𝟙 X := by
  dsimp [unipotentShear, unipotentShearInv]
  rw [Preadditive.add_comp, Preadditive.comp_sub, Preadditive.comp_sub]
  simp only [Category.id_comp, Category.comp_id]
  rw [hN]
  abel

/-- THEOREM: Left invertibility of the unipotent shear:
$(\mathbb{1}_X - N) \gg (\mathbb{1}_X + N) = \mathbb{1}_X$. -/
theorem unipotentShearInv_mul {X : C} (N : X ⟶ X) (hN : N ≫ N = 0) :
    unipotentShearInv N ≫ unipotentShear N = 𝟙 X := by
  dsimp [unipotentShear, unipotentShearInv]
  rw [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_add]
  simp only [Category.id_comp, Category.comp_id]
  rw [hN]
  abel

/-- In the Chevalley dyad algebra, the transition dyad $E_{01}$ is identically nilpotent:
$E_{01}^2 = 0$. -/
theorem chevalley_dyad_01_nilpotent {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E01 n p ≫ E01 n p = 0 :=
  E01_mul_E01 n p hn hcar

/-- The Chevalley transition dyad $E_{01}$ generates the LogCFT unipotent shear:
$(\mathbb{1}_X + E_{01}) \gg (\mathbb{1}_X - E_{01}) = \mathbb{1}_X$. -/
theorem chevalley_unipotent_shear_identity {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    unipotentShear (E01 n p) ≫ unipotentShearInv (E01 n p) = 𝟙 X :=
  unipotentShear_mul_inv (E01 n p) (chevalley_dyad_01_nilpotent n p hn hcar)

/-! ### 3. Master DAG Synthesis Theorem -/

/-- MASTER THEOREM: Comprehensive Soundness of the Symplectic Spinor DAG.
From the biproduct doublet and CAR pair alone, proves:
1. $J^2 = -\mathbb{1}_E$ (Almost Complex Structure).
2. $J^4 = \mathbb{1}_E$ ($\mathbb{Z}_4$ Maslov Holonomy).
3. $\mathcal{H}^8 = \mathbb{1}_E$ ($4\pi$ Spinor Invariance).
4. $(P_+ J P_-)(P_- J P_+) = -P_+$ (Fermionic Parity Sign).
5. $(\mathbb{1} + E_{01})(\mathbb{1} - E_{01}) = \mathbb{1}$ (LogCFT Unipotent Shear). -/
theorem master_symplectic_spinor_soundness {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    let J := symplecticJ p1 i1 p2 i2 D M
    let P_plus := p1 ≫ i1
    let P_minus := p2 ≫ i2
    let H := bdgHamiltonian p1 i1 p2 i2 D M
    -- 1. Almost Complex Structure
    J ≫ J = -𝟙 E ∧
    -- 2. Z_4 Maslov Holonomy
    (J ≫ J) ≫ (J ≫ J) = 𝟙 E ∧
    -- 3. 4π Spinor Holonomy
    ((H ≫ H) ≫ (H ≫ H)) ≫ ((H ≫ H) ≫ (H ≫ H)) = 𝟙 E ∧
    -- 4. Transmutation Fermionic Minus Sign
    (P_plus ≫ J ≫ P_minus) ≫ (P_minus ≫ J ≫ P_plus) = -P_plus ∧
    -- 5. LogCFT Unipotent Shear Inversion
    unipotentShear (E01 D M) ≫ unipotentShearInv (E01 D M) = 𝟙 Ω := by
  intros J P_plus P_minus H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact symplecticJ_sq_neg_one p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR
  · exact symplecticJ_fourth_power_identity p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR
  · exact bdgHamiltonian_eighth_power_identity p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR
  · exact transmutation_round_trip_fermionic_sign p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR
  · exact chevalley_unipotent_shear_identity D M hD hCAR

end InfoGeometry.Physics.LogCFTSymplecticBridge
