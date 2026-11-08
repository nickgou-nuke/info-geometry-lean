/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ChevalleySpinorIdeal
import InfoGeometry.Physics.HarmonicWeakHorizonBdG

/-!
# Chevalley–Nambu CAR Bridge

This module connects the two genuinely owned layers of the repository without
postulating any relation between them:

* the **Chevalley CAR algebra** on one object (`ChevalleySpinorIdeal`): a pair
  of nilpotents `D, M : Ω ⟶ Ω` with `D ≫ D = 0`, `M ≫ M = 0` and the
  anticommutator `D ≫ M + M ≫ D = 𝟙 Ω`;
* the **Nambu biproduct doublet** (`HarmonicWeakHorizonBdG`): a splitting
  `E ≅ Ω ⊞ Ω` given by `p₁, i₁, p₂, i₂` with the standard axioms.

The bridge is entirely constructive.  The CAR pair supplies the Chevalley
split involution `ε = [D, M]`, and the BdG Hamiltonian assembled from the very
same pair squares to the purely off-diagonal `ε`-block operator

```
ℋ_BdG² = p₁ ≫ ε ≫ i₂ - p₂ ≫ ε ≫ i₁
```

so that the doubled Hamiltonian is a fourth root of minus the identity,
`ℋ_BdG⁴ = -𝟙 E`.  Every hypothesis below is either the CAR data or the
biproduct data.  In particular:

* no dispersion hypothesis `ℋ² = λ² • 𝟙` is used. The theorem
  `chevalleyGrading_vanishes_of_commuting` only says that a commuting pair has
  trivial grading. Together with the CAR involution theorem, this rules out a
  commuting CAR pair when `𝟙 Ω ≠ 0`; it does not rule one out on a zero object;
* the dispersion theorem of `HarmonicWeakHorizonBdG` assumes `D ≫ M = M ≫ D`,
  so it cannot be applied to a nonzero CAR carrier;
* no Peirce relation is postulated: the projectors are the doubled forms
  `𝟙 ± ε`, constructed from the proved involution.
-/

namespace InfoGeometry.Physics.ChevalleyNambuBridge

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Physics.Chevalley
open InfoGeometry.Physics.BdGCondensation

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. The Chevalley grading of a CAR pair -/

/-- The Chevalley split involution `ε = [D, M] = D ≫ M - M ≫ D`. -/
@[inline]
def chevalleyGrading {Ω : C} (D M : Ω ⟶ Ω) : Ω ⟶ Ω := D ≫ M - M ≫ D

/-- The CAR data makes `ε` an exact split involution: `ε ≫ ε = 𝟙 Ω`.
This is the owner theorem `cat_chiralGrading_sq` under the bridge name. -/
theorem chevalleyGrading_sq {Ω : C} (D M : Ω ⟶ Ω)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    chevalleyGrading D M ≫ chevalleyGrading D M = 𝟙 Ω :=
  cat_chiralGrading_sq D M hD hM hCAR

/-- The grading anticommutes with the annihilation nilpotent:
`ε ≫ D + D ≫ ε = 0`.  This completes the categorical Chevalley algebra, whose
ring-level counterpart is `chiralGrading_anticommutes_n`. -/
theorem chevalleyGrading_anticommutes_D {Ω : C} (D M : Ω ⟶ Ω)
    (hD : D ≫ D = 0) :
    chevalleyGrading D M ≫ D + D ≫ chevalleyGrading D M = 0 := by
  show (D ≫ M - M ≫ D) ≫ D + D ≫ (D ≫ M - M ≫ D) = 0
  rw [Preadditive.sub_comp, Preadditive.comp_sub]
  simp only [Category.assoc]
  have h1 : M ≫ (D ≫ D) = 0 := by rw [hD, comp_zero]
  have h2 : D ≫ (D ≫ M) = 0 := by rw [← Category.assoc, hD, zero_comp]
  rw [h1, h2]
  abel

/-- The grading anticommutes with the creation nilpotent:
`ε ≫ M + M ≫ ε = 0`. -/
theorem chevalleyGrading_anticommutes_M {Ω : C} (D M : Ω ⟶ Ω)
    (hM : M ≫ M = 0) :
    chevalleyGrading D M ≫ M + M ≫ chevalleyGrading D M = 0 := by
  show (D ≫ M - M ≫ D) ≫ M + M ≫ (D ≫ M - M ≫ D) = 0
  rw [Preadditive.sub_comp, Preadditive.comp_sub]
  simp only [Category.assoc]
  have h1 : D ≫ (M ≫ M) = 0 := by rw [hM, comp_zero]
  have h2 : M ≫ (M ≫ D) = 0 := by rw [← Category.assoc, hM, zero_comp]
  rw [h1, h2]
  abel

/-- A commuting pair has trivial Chevalley grading.  This records precisely
why the dispersion theorem `bdg_hamiltonian_squared`, whose hypothesis is
`D ≫ M = M ≫ D`, cannot be applied to a CAR pair: the two hypotheses are
incompatible, since a CAR pair has `ε² = 𝟙`. -/
theorem chevalleyGrading_vanishes_of_commuting {Ω : C} (D M : Ω ⟶ Ω)
    (h_comm : D ≫ M = M ≫ D) :
    chevalleyGrading D M = 0 := by
  show D ≫ M - M ≫ D = 0
  rw [h_comm, sub_self]

/-- A CAR pair on a nonzero carrier cannot commute.  The nonzero-identity
hypothesis is essential in an arbitrary preadditive category, which may have a
zero object. -/
theorem car_pair_not_commuting {Ω : C} (D M : Ω ⟶ Ω)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) (hone : (𝟙 Ω) ≠ 0) :
    D ≫ M ≠ M ≫ D := by
  intro hcomm
  have hgrading : chevalleyGrading D M = 0 :=
    chevalleyGrading_vanishes_of_commuting D M hcomm
  have hgrading_sq : chevalleyGrading D M ≫ chevalleyGrading D M = 𝟙 Ω :=
    chevalleyGrading_sq D M hD hM hCAR
  have hone_zero : (𝟙 Ω) = 0 := by
    calc
      𝟙 Ω = chevalleyGrading D M ≫ chevalleyGrading D M := hgrading_sq.symm
      _ = 0 := by rw [hgrading]; simp
  exact hone hone_zero

/-! ### 2. The four block values of the CAR BdG square -/

/-- The physical block of `ℋ_BdG²` vanishes: `i₁ ≫ ℋ² ≫ p₁ = 0`, because the
kinetic and mass squares cancel inside the physical sector. -/
theorem carBdg_block_11 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    i1 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ p1 = 0 := by
  rw [biproduct_block_composition p1 i1 p2 i2 h_decomp
    (bdgHamiltonian p1 i1 p2 i2 D M) (bdgHamiltonian p1 i1 p2 i2 D M) i1 p1]
  rw [bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21,
      bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21,
      bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12, hD, hM]
  abel

/-- The off-diagonal physical block of `ℋ_BdG²` is the Chevalley grading:
`i₁ ≫ ℋ² ≫ p₂ = ε`. -/
theorem carBdg_block_12 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    i1 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ p2 = chevalleyGrading D M := by
  show i1 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ p2 = D ≫ M - M ≫ D
  rw [biproduct_block_composition p1 i1 p2 i2 h_decomp
    (bdgHamiltonian p1 i1 p2 i2 D M) (bdgHamiltonian p1 i1 p2 i2 D M) i1 p2]
  rw [bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21,
      bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21,
      bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12]
  rw [Preadditive.comp_neg]
  abel

/-- The off-diagonal ghost block of `ℋ_BdG²` is the negated Chevalley grading:
`i₂ ≫ ℋ² ≫ p₁ = -ε`. -/
theorem carBdg_block_21 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    i2 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ p1 = -chevalleyGrading D M := by
  show i2 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ p1 = -(D ≫ M - M ≫ D)
  rw [biproduct_block_composition p1 i1 p2 i2 h_decomp
    (bdgHamiltonian p1 i1 p2 i2 D M) (bdgHamiltonian p1 i1 p2 i2 D M) i2 p1]
  rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21,
      bdg_block_11 p1 i1 p2 i2 D M hid1 horth12 horth21,
      bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
  rw [Preadditive.neg_comp]
  abel

/-- The ghost block of `ℋ_BdG²` vanishes: `i₂ ≫ ℋ² ≫ p₂ = 0`. -/
theorem carBdg_block_22 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    i2 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ p2 = 0 := by
  rw [biproduct_block_composition p1 i1 p2 i2 h_decomp
    (bdgHamiltonian p1 i1 p2 i2 D M) (bdgHamiltonian p1 i1 p2 i2 D M) i2 p2]
  rw [bdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth21,
      bdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12,
      bdg_block_22 p1 i1 p2 i2 D M hid2 horth12 horth21]
  rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, hM, hD]
  abel

/-! ### 3. The Chevalley–Nambu bridge -/

/-- **The Chevalley–Nambu bridge.** For a CAR pair `D, M` on `Ω`, the square of
the BdG Hamiltonian is the purely off-diagonal `ε`-block operator
`p₁ ≫ ε ≫ i₂ - p₂ ≫ ε ≫ i₁`: the kinetic and mass squares cancel inside each
sector (`D² = M² = 0`), and only the Chevalley commutator survives across the
doublet. -/
theorem carBdg_squared_eq_offdiagonal {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M =
      p1 ≫ chevalleyGrading D M ≫ i2 - p2 ≫ chevalleyGrading D M ≫ i1 := by
  rw [biproduct_endomorphism_reconstruct p1 i1 p2 i2 h_decomp
    (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M)]
  rw [carBdg_block_11 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR,
      carBdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR,
      carBdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR,
      carBdg_block_22 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR]
  simp only [zero_comp, comp_zero, zero_add, add_zero, Preadditive.neg_comp,
    Preadditive.comp_neg]
  abel

/-! ### 4. Fourth root of minus the identity -/

/-- The doubled BdG Hamiltonian of a CAR pair is a fourth root of minus the
identity: `ℋ_BdG ≫ ℋ_BdG ≫ ℋ_BdG ≫ ℋ_BdG = -𝟙 E`.  This is the honest
doubled-level form of the Dirac–Kähler identity `𝒟² = -1`, obtained from the
CAR data alone. -/
theorem carBdg_fourth_power_neg_identity {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) ≫
      (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) =
    -𝟙 E := by
  have hsq := carBdg_squared_eq_offdiagonal p1 i1 p2 i2 D M hid1 hid2 horth12
    horth21 h_decomp hD hM hCAR
  have hε := chevalleyGrading_sq D M hD hM hCAR
  have h1 : (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p1 ≫ chevalleyGrading D M ≫ i2) = 0 := by
    calc
      (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p1 ≫ chevalleyGrading D M ≫ i2)
          = p1 ≫ chevalleyGrading D M ≫ (i2 ≫ p1) ≫ chevalleyGrading D M ≫ i2 := by
            simp only [Category.assoc]
      _ = 0 := by rw [horth21]; simp only [comp_zero, zero_comp]
  have h2 : (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p2 ≫ chevalleyGrading D M ≫ i1) = 0 := by
    calc
      (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p2 ≫ chevalleyGrading D M ≫ i1)
          = p2 ≫ chevalleyGrading D M ≫ (i1 ≫ p2) ≫ chevalleyGrading D M ≫ i1 := by
            simp only [Category.assoc]
      _ = 0 := by rw [horth12]; simp only [comp_zero, zero_comp]
  have h3 : (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p2 ≫ chevalleyGrading D M ≫ i1)
      = p1 ≫ i1 := by
    calc
      (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p2 ≫ chevalleyGrading D M ≫ i1)
          = p1 ≫ chevalleyGrading D M ≫ (i2 ≫ p2) ≫ chevalleyGrading D M ≫ i1 := by
            simp only [Category.assoc]
      _ = p1 ≫ (chevalleyGrading D M ≫ chevalleyGrading D M) ≫ i1 := by
            rw [hid2]; simp only [Category.id_comp, Category.assoc]
      _ = p1 ≫ i1 := by rw [hε]; simp only [Category.id_comp, Category.comp_id]
  have h4 : (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p1 ≫ chevalleyGrading D M ≫ i2)
      = p2 ≫ i2 := by
    calc
      (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p1 ≫ chevalleyGrading D M ≫ i2)
          = p2 ≫ chevalleyGrading D M ≫ (i1 ≫ p1) ≫ chevalleyGrading D M ≫ i2 := by
            simp only [Category.assoc]
      _ = p2 ≫ (chevalleyGrading D M ≫ chevalleyGrading D M) ≫ i2 := by
            rw [hid1]; simp only [Category.id_comp, Category.assoc]
      _ = p2 ≫ i2 := by rw [hε]; simp only [Category.id_comp, Category.comp_id]
  have hG2 : (p1 ≫ chevalleyGrading D M ≫ i2 - p2 ≫ chevalleyGrading D M ≫ i1) ≫
      (p1 ≫ chevalleyGrading D M ≫ i2 - p2 ≫ chevalleyGrading D M ≫ i1) = -𝟙 E := by
    calc
      (p1 ≫ chevalleyGrading D M ≫ i2 - p2 ≫ chevalleyGrading D M ≫ i1) ≫
          (p1 ≫ chevalleyGrading D M ≫ i2 - p2 ≫ chevalleyGrading D M ≫ i1)
          = (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p1 ≫ chevalleyGrading D M ≫ i2) -
            (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p2 ≫ chevalleyGrading D M ≫ i1) -
            (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p1 ≫ chevalleyGrading D M ≫ i2) +
            (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p2 ≫ chevalleyGrading D M ≫ i1) := by
              rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub]
              abel
      _ = -(p1 ≫ i1) - (p2 ≫ i2) := by
              rw [h1, h3, h4, h2]
              simp only [zero_sub, sub_zero, add_zero]
      _ = -𝟙 E := by
              have hneg : -(p1 ≫ i1) - (p2 ≫ i2) = -(p1 ≫ i1 + p2 ≫ i2) := by abel
              rw [hneg, h_decomp]
  rw [hsq]
  rw [hG2]

/-! ### 5. Sector decoupling and transmutation -/

/-- The square of the CAR BdG Hamiltonian kills the physical sector:
`P₊ ≫ ℋ_BdG² ≫ P₊ = 0`.  The kinetic and mass squares cancel inside the
physical sector, so no dispersion is generated there. -/
theorem carBdg_squared_kills_physical_sector {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (p1 ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p1 ≫ i1) = 0 := by
  have key : (p1 ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p1 ≫ i1)
      = p1 ≫ (i1 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
        bdgHamiltonian p1 i1 p2 i2 D M) ≫ p1) ≫ i1 := by
    simp only [Category.assoc]
  rw [key, carBdg_block_11 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR]
  simp only [comp_zero, zero_comp]

/-- The square of the CAR BdG Hamiltonian kills the ghost sector:
`P₋ ≫ ℋ_BdG² ≫ P₋ = 0`. -/
theorem carBdg_squared_kills_ghost_sector {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (p2 ≫ i2) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p2 ≫ i2) = 0 := by
  have key : (p2 ≫ i2) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p2 ≫ i2)
      = p2 ≫ (i2 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
        bdgHamiltonian p1 i1 p2 i2 D M) ≫ p2) ≫ i2 := by
    simp only [Category.assoc]
  rw [key, carBdg_block_22 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR]
  simp only [comp_zero, zero_comp]

/-- The square of the CAR BdG Hamiltonian transmutes the ghost sector into the
physical sector through the Chevalley grading:
`P₊ ≫ ℋ_BdG² ≫ P₋ = p₁ ≫ ε ≫ i₂`. -/
theorem carBdg_squared_transmutes_ghost_to_physical {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (p1 ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p2 ≫ i2) =
    p1 ≫ chevalleyGrading D M ≫ i2 := by
  have key : (p1 ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p2 ≫ i2)
      = p1 ≫ (i1 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
        bdgHamiltonian p1 i1 p2 i2 D M) ≫ p2) ≫ i2 := by
    simp only [Category.assoc]
  rw [key, carBdg_block_12 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR]

/-- The square of the CAR BdG Hamiltonian transmutes the physical sector into
the ghost sector through the negated Chevalley grading:
`P₋ ≫ ℋ_BdG² ≫ P₊ = -(p₂ ≫ ε ≫ i₁)`. -/
theorem carBdg_squared_transmutes_physical_to_ghost {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (p2 ≫ i2) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p1 ≫ i1) =
    -(p2 ≫ chevalleyGrading D M ≫ i1) := by
  have key : (p2 ≫ i2) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p1 ≫ i1)
      = p2 ≫ (i2 ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
        bdgHamiltonian p1 i1 p2 i2 D M) ≫ p1) ≫ i1 := by
    simp only [Category.assoc]
  rw [key, carBdg_block_21 p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR]
  rw [Preadditive.neg_comp, Preadditive.comp_neg]

/-! ### 6. Transmutation round trips -/

/-- The transmutation round trip on the physical sector is minus the physical
projector: `(P₊ ≫ ℋ² ≫ P₋) ≫ (P₋ ≫ ℋ² ≫ P₊) = -P₊`, because the Chevalley
grading is an involution. -/
theorem carBdg_transmutation_round_trip_physical {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    ((p1 ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p2 ≫ i2)) ≫
      ((p2 ≫ i2) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
        bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p1 ≫ i1)) =
    -(p1 ≫ i1) := by
  rw [carBdg_squared_transmutes_ghost_to_physical p1 i1 p2 i2 D M hid1 hid2
    horth12 horth21 h_decomp hD hM hCAR]
  rw [carBdg_squared_transmutes_physical_to_ghost p1 i1 p2 i2 D M hid1 hid2
    horth12 horth21 h_decomp hD hM hCAR]
  have hε := chevalleyGrading_sq D M hD hM hCAR
  have hkey : (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p2 ≫ chevalleyGrading D M ≫ i1)
      = p1 ≫ i1 := by
    calc
      (p1 ≫ chevalleyGrading D M ≫ i2) ≫ (p2 ≫ chevalleyGrading D M ≫ i1)
          = p1 ≫ chevalleyGrading D M ≫ (i2 ≫ p2) ≫ chevalleyGrading D M ≫ i1 := by
            simp only [Category.assoc]
      _ = p1 ≫ (chevalleyGrading D M ≫ chevalleyGrading D M) ≫ i1 := by
            rw [hid2]; simp only [Category.id_comp, Category.assoc]
      _ = p1 ≫ i1 := by rw [hε]; simp only [Category.id_comp, Category.comp_id]
  rw [Preadditive.comp_neg, hkey]

/-- The transmutation round trip on the ghost sector is minus the ghost
projector: `(P₋ ≫ ℋ² ≫ P₊) ≫ (P₊ ≫ ℋ² ≫ P₋) = -P₋`. -/
theorem carBdg_transmutation_round_trip_ghost {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    ((p2 ≫ i2) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
      bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p1 ≫ i1)) ≫
      ((p1 ≫ i1) ≫ (bdgHamiltonian p1 i1 p2 i2 D M ≫
        bdgHamiltonian p1 i1 p2 i2 D M) ≫ (p2 ≫ i2)) =
    -(p2 ≫ i2) := by
  rw [carBdg_squared_transmutes_physical_to_ghost p1 i1 p2 i2 D M hid1 hid2
    horth12 horth21 h_decomp hD hM hCAR]
  rw [carBdg_squared_transmutes_ghost_to_physical p1 i1 p2 i2 D M hid1 hid2
    horth12 horth21 h_decomp hD hM hCAR]
  have hε := chevalleyGrading_sq D M hD hM hCAR
  have hkey : (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p1 ≫ chevalleyGrading D M ≫ i2)
      = p2 ≫ i2 := by
    calc
      (p2 ≫ chevalleyGrading D M ≫ i1) ≫ (p1 ≫ chevalleyGrading D M ≫ i2)
          = p2 ≫ chevalleyGrading D M ≫ (i1 ≫ p1) ≫ chevalleyGrading D M ≫ i2 := by
            simp only [Category.assoc]
      _ = p2 ≫ (chevalleyGrading D M ≫ chevalleyGrading D M) ≫ i2 := by
            rw [hid1]; simp only [Category.id_comp, Category.assoc]
      _ = p2 ≫ i2 := by rw [hε]; simp only [Category.id_comp, Category.comp_id]
  rw [Preadditive.neg_comp, hkey]

end InfoGeometry.Physics.ChevalleyNambuBridge
