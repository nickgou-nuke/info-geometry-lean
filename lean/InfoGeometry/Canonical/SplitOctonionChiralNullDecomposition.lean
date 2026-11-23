/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Split-Circular Chiral Zorn Basis and Maximal 4D Totally Isotropic Nullspaces

This module develops the split-circular chiral Zorn decomposition on the 8-dimensional
split-octonion algebra `SplitOctCD` over `ℝ`:

1. Preliminary `FiniteDimensional ℝ SplitOctCD` (`finrank = 8`) and full bilinearity /
   polarization identities for `cdNorm` and `cdKreinForm`.
2. The split-circular chiral Zorn basis `uPlusCD = (1 + ℓ)/2`, `uMinusCD = (1 - ℓ)/2`,
   `ePlusCD k = uPlusCD * iCD k = (iCD k + sCD k)/2 = iCD k * uMinusCD`, and
   `eMinusCD k = uMinusCD * iCD k = (iCD k - sCD k)/2 = iCD k * uPlusCD`, together with their
   exact images under `splitOctCDEquivZornMatrix`.
3. Maximal 4-dimensional totally isotropic nullspaces `nullSpacePlus = range (leftMulEnd uPlusCD)`
   and `nullSpaceMinus = range (leftMulEnd uMinusCD)`, identified with the conjugate graphs
   `{(q, +star q)}` and `{(q, -star q)}`, Witt bound `finrank ≤ 4`, maximality, and the
   direct-sum decomposition `IsCompl nullSpacePlus nullSpaceMinus`.
4. Dual quaternionic right-multiplication spin frames `spinFrameRightMulPlus` and
   `spinFrameRightMulMinus` on `nullSpacePlus` and `nullSpaceMinus` (preserving chirality under
   `i₃` rotation) contrasted with the ambient nonassociative product `ePlusCD 0 * iCD 2 = -eMinusCD 1`.
5. Max Zorn's `2 × 2` vector-matrix representation `chiralZornReconstruct` / `chiralZornEquiv` and
   the pure cross-pairing norm identity `cdNorm X = α₊ * α₋ + ∑ k, a k * b k = 2 * cdKreinForm x₊ x₋`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionChiralNullDecomposition

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionCayleyDickson

/-! ## Section 1: Ambient Finite-Dimensionality and `cdKreinForm` Polarization -/

instance : FiniteDimensional ℝ SplitOctCD :=
  LinearEquiv.finiteDimensional cdLinearEquivFin8.symm

theorem splitOctCD_finrank : Module.finrank ℝ SplitOctCD = 8 := by
  rw [cdLinearEquivFin8.finrank_eq, Module.finrank_fin_fun]

theorem cdNorm_add (x y : SplitOctCD) :
    cdNorm (x + y) = cdNorm x + cdNorm y + 2 * cdKreinForm x y := by
  unfold cdKreinForm
  ring

theorem cdNorm_smul (c : ℝ) (x : SplitOctCD) :
    cdNorm (c • x) = c ^ 2 * cdNorm x := by
  simp [cdNorm, Quaternion.normSq_smul]
  ring

theorem cdKreinForm_symm (x y : SplitOctCD) :
    cdKreinForm x y = cdKreinForm y x := by
  simp [cdKreinForm, add_comm]
  ring

theorem cdKreinForm_self (x : SplitOctCD) :
    cdKreinForm x x = cdNorm x := by
  have h2 : x + x = (2 : ℝ) • x := by
    ext <;> simp <;> ring
  unfold cdKreinForm
  rw [h2, cdNorm_smul]
  ring

theorem cdKreinForm_add_left (x y z : SplitOctCD) :
    cdKreinForm (x + y) z = cdKreinForm x z + cdKreinForm y z := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases y with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  rcases z with ⟨⟨e0, e1, e2, e3⟩, ⟨f0, f1, f2, f3⟩⟩
  simp [cdKreinForm, cdNorm, Quaternion.normSq_def']
  ring

theorem cdKreinForm_add_right (x y z : SplitOctCD) :
    cdKreinForm x (y + z) = cdKreinForm x y + cdKreinForm x z := by
  rw [cdKreinForm_symm, cdKreinForm_add_left, cdKreinForm_symm y x, cdKreinForm_symm z x]

theorem cdKreinForm_smul_left (c : ℝ) (x y : SplitOctCD) :
    cdKreinForm (c • x) y = c * cdKreinForm x y := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases y with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  simp [cdKreinForm, cdNorm, Quaternion.normSq_def']
  ring

theorem cdKreinForm_smul_right (c : ℝ) (x y : SplitOctCD) :
    cdKreinForm x (c • y) = c * cdKreinForm x y := by
  rw [cdKreinForm_symm, cdKreinForm_smul_left, cdKreinForm_symm]

theorem cdKreinForm_eq_zero_of_isotropic (W : Submodule ℝ SplitOctCD)
    (hW : ∀ x ∈ W, cdNorm x = 0) {x y : SplitOctCD} (hx : x ∈ W) (hy : y ∈ W) :
    cdKreinForm x y = 0 := by
  have hxy := hW (x + y) (W.add_mem hx hy)
  have hx0 := hW x hx
  have hy0 := hW y hy
  have hadd := cdNorm_add x y
  linarith

/-! ## Section 2: Split-Circular Chiral Zorn Basis (Feature F5) -/

/-- Upper split-circular chiral idempotent `u₊ = (1 + ℓ) / 2`. -/
def uPlusCD : SplitOctCD := (1 / 2 : ℝ) • (oneCD + ellCD)

/-- Lower split-circular chiral idempotent `u₋ = (1 - ℓ) / 2`. -/
def uMinusCD : SplitOctCD := (1 / 2 : ℝ) • (oneCD - ellCD)

/-- Upper chiral vector basis element `eₖ⁺ = u₊ * iₖ`. -/
def ePlusCD (k : Fin 3) : SplitOctCD := uPlusCD * iCD k

/-- Lower chiral vector basis element `eₖ⁻ = u₋ * iₖ`. -/
def eMinusCD (k : Fin 3) : SplitOctCD := uMinusCD * iCD k

theorem uPlusCD_components :
    uPlusCD = ⟨⟨1 / 2, 0, 0, 0⟩, ⟨1 / 2, 0, 0, 0⟩⟩ := by
  ext <;> simp [uPlusCD, oneCD, ellCD]

theorem uMinusCD_components :
    uMinusCD = ⟨⟨1 / 2, 0, 0, 0⟩, ⟨-(1 / 2), 0, 0, 0⟩⟩ := by
  ext <;> simp [uMinusCD, oneCD, ellCD]

theorem uPlusCD_sq : uPlusCD * uPlusCD = uPlusCD := by
  ext <;> simp [uPlusCD, oneCD, ellCD] <;> norm_num

theorem uMinusCD_sq : uMinusCD * uMinusCD = uMinusCD := by
  ext <;> simp [uMinusCD, oneCD, ellCD] <;> norm_num

theorem uPlusCD_mul_uMinusCD : uPlusCD * uMinusCD = 0 := by
  ext <;> simp [uPlusCD, uMinusCD, oneCD, ellCD]

theorem uMinusCD_mul_uPlusCD : uMinusCD * uPlusCD = 0 := by
  ext <;> simp [uPlusCD, uMinusCD, oneCD, ellCD]

theorem uPlusCD_add_uMinusCD : uPlusCD + uMinusCD = 1 := by
  ext <;> (simp [uPlusCD, uMinusCD, oneCD, ellCD]; try norm_num)

theorem uPlusCD_sub_uMinusCD : uPlusCD - uMinusCD = ellCD := by
  ext <;> (simp [uPlusCD, uMinusCD, oneCD, ellCD]; try norm_num)

theorem cdConj_uPlusCD : cdConj uPlusCD = uMinusCD := by
  ext <;> simp [cdConj, uPlusCD, uMinusCD, oneCD, ellCD]

theorem cdConj_uMinusCD : cdConj uMinusCD = uPlusCD := by
  ext <;> simp [cdConj, uPlusCD, uMinusCD, oneCD, ellCD]

theorem cdNorm_uPlusCD : cdNorm uPlusCD = 0 := by
  simp [cdNorm, uPlusCD_components]

theorem cdNorm_uMinusCD : cdNorm uMinusCD = 0 := by
  simp [cdNorm, uMinusCD_components, Quaternion.normSq_def']

theorem ePlusCD_components (k : Fin 3) :
    ePlusCD k = ⟨(1 / 2 : ℝ) • qBasis k, -(1 / 2 : ℝ) • qBasis k⟩ := by
  fin_cases k <;> ext <;> simp [ePlusCD, uPlusCD, oneCD, ellCD, iCD, qBasis]

theorem eMinusCD_components (k : Fin 3) :
    eMinusCD k = ⟨(1 / 2 : ℝ) • qBasis k, (1 / 2 : ℝ) • qBasis k⟩ := by
  fin_cases k <;> ext <;> simp [eMinusCD, uMinusCD, oneCD, ellCD, iCD, qBasis]

theorem ePlusCD_eq_half_add (k : Fin 3) :
    ePlusCD k = (1 / 2 : ℝ) • (iCD k + sCD k) := by
  fin_cases k <;>
    ext <;>
    simp [ePlusCD, uPlusCD, oneCD, ellCD, iCD, sCD_formula, qBasis]

theorem ePlusCD_eq_mul_uMinus (k : Fin 3) :
    ePlusCD k = iCD k * uMinusCD := by
  fin_cases k <;>
    ext <;>
    simp [ePlusCD, uPlusCD, uMinusCD, oneCD, ellCD, iCD, qBasis]

theorem eMinusCD_eq_half_sub (k : Fin 3) :
    eMinusCD k = (1 / 2 : ℝ) • (iCD k - sCD k) := by
  fin_cases k <;>
    ext <;>
    simp [eMinusCD, uMinusCD, oneCD, ellCD, iCD, sCD_formula, qBasis]

theorem eMinusCD_eq_mul_uPlus (k : Fin 3) :
    eMinusCD k = iCD k * uPlusCD := by
  fin_cases k <;>
    ext <;>
    simp [eMinusCD, uPlusCD, uMinusCD, oneCD, ellCD, iCD, qBasis]

theorem cdConj_ePlusCD (k : Fin 3) : cdConj (ePlusCD k) = -ePlusCD k := by
  fin_cases k <;> ext <;> simp [cdConj, ePlusCD_components, qBasis]

theorem cdConj_eMinusCD (k : Fin 3) : cdConj (eMinusCD k) = -eMinusCD k := by
  fin_cases k <;> ext <;> simp [cdConj, eMinusCD_components, qBasis]

theorem cdNorm_ePlusCD (k : Fin 3) : cdNorm (ePlusCD k) = 0 := by
  simp [cdNorm, ePlusCD_components]

theorem cdNorm_eMinusCD (k : Fin 3) : cdNorm (eMinusCD k) = 0 := by
  simp [cdNorm, eMinusCD_components]

theorem splitOctCDEquivZornMatrix_uPlusCD :
    splitOctCDEquivZornMatrix uPlusCD = ZornMatrix.zornPlus := by
  apply ZornMatrix.ext
  · simp [uPlusCD_components, ZornMatrix.zornPlus]; norm_num
  · simp [uPlusCD_components, ZornMatrix.zornPlus]
  · funext i; fin_cases i <;> simp [uPlusCD_components, ZornMatrix.zornPlus]
  · funext i; fin_cases i <;> simp [uPlusCD_components, ZornMatrix.zornPlus]

theorem splitOctCDEquivZornMatrix_uMinusCD :
    splitOctCDEquivZornMatrix uMinusCD = ZornMatrix.zornMinus := by
  apply ZornMatrix.ext
  · simp [uMinusCD_components, ZornMatrix.zornMinus]
  · simp [uMinusCD_components, ZornMatrix.zornMinus]; norm_num
  · funext i; fin_cases i <;> simp [uMinusCD_components, ZornMatrix.zornMinus]
  · funext i; fin_cases i <;> simp [uMinusCD_components, ZornMatrix.zornMinus]

theorem splitOctCDEquivZornMatrix_ePlusCD (k : Fin 3) :
    splitOctCDEquivZornMatrix (ePlusCD k) = -ZornMatrix.chiralUpperBasis k := by
  apply ZornMatrix.ext
  · fin_cases k <;> simp [ePlusCD_components, qBasis, ZornMatrix.chiralUpperBasis]
  · fin_cases k <;> simp [ePlusCD_components, qBasis, ZornMatrix.chiralUpperBasis]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [ePlusCD_components, qBasis, ZornMatrix.chiralUpperBasis] <;> norm_num
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [ePlusCD_components, qBasis, ZornMatrix.chiralUpperBasis]

theorem splitOctCDEquivZornMatrix_eMinusCD (k : Fin 3) :
    splitOctCDEquivZornMatrix (eMinusCD k) = ZornMatrix.chiralLowerBasis k := by
  apply ZornMatrix.ext
  · fin_cases k <;> simp [eMinusCD_components, qBasis, ZornMatrix.chiralLowerBasis]
  · fin_cases k <;> simp [eMinusCD_components, qBasis, ZornMatrix.chiralLowerBasis]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [eMinusCD_components, qBasis, ZornMatrix.chiralLowerBasis]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [eMinusCD_components, qBasis, ZornMatrix.chiralLowerBasis] <;> norm_num

/-! ## Section 3: Maximal 4D Totally Isotropic Nullspaces (Feature F6) -/

/-- Upper chiral nullspace `𝒩₊ = u₊ * 𝕆̃`. -/
def nullSpacePlus : Submodule ℝ SplitOctCD :=
  LinearMap.range (leftMulEnd uPlusCD)

/-- Lower chiral nullspace `𝒩₋ = u₋ * 𝕆̃`. -/
def nullSpaceMinus : Submodule ℝ SplitOctCD :=
  LinearMap.range (leftMulEnd uMinusCD)

theorem mem_nullSpacePlus_iff (x : SplitOctCD) :
    x ∈ nullSpacePlus ↔ x.snd = star x.fst := by
  constructor
  · rintro ⟨z, rfl⟩
    change (uPlusCD * z).snd = star (uPlusCD * z).fst
    rw [uPlusCD_components]
    ext <;> simp <;> ring
  · intro hx
    refine ⟨x, ?_⟩
    change uPlusCD * x = x
    rw [uPlusCD_components]
    ext <;> simp [hx] <;> ring

theorem mem_nullSpaceMinus_iff (x : SplitOctCD) :
    x ∈ nullSpaceMinus ↔ x.snd = -star x.fst := by
  constructor
  · rintro ⟨z, rfl⟩
    change (uMinusCD * z).snd = -star (uMinusCD * z).fst
    rw [uMinusCD_components]
    ext <;> simp <;> ring
  · intro hx
    refine ⟨x, ?_⟩
    change uMinusCD * x = x
    rw [uMinusCD_components]
    ext <;> simp [hx] <;> ring

/-- Conjugate graph submodule `{(q, +star q) | q : Quaternion ℝ}`. -/
def graphConjSubmodule : Submodule ℝ SplitOctCD where
  carrier := {x : SplitOctCD | x.snd = star x.fst}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change x.snd = star x.fst at hx
    change y.snd = star y.fst at hy
    change (x + y).snd = star (x + y).fst
    simp [hx, hy]
  smul_mem' c {x} hx := by
    change x.snd = star x.fst at hx
    change (c • x).snd = star (c • x).fst
    simp [hx]

/-- Anticonjugate graph submodule `{(q, -star q) | q : Quaternion ℝ}`. -/
def negGraphConjSubmodule : Submodule ℝ SplitOctCD where
  carrier := {x : SplitOctCD | x.snd = -star x.fst}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change x.snd = -star x.fst at hx
    change y.snd = -star y.fst at hy
    change (x + y).snd = -star (x + y).fst
    simp [hx, hy]
    abel
  smul_mem' c {x} hx := by
    change x.snd = -star x.fst at hx
    change (c • x).snd = -star (c • x).fst
    simp [hx]

theorem nullSpacePlus_eq_graph_conj_submodule :
    nullSpacePlus = graphConjSubmodule := by
  ext x
  exact mem_nullSpacePlus_iff x

theorem nullSpaceMinus_eq_neg_graph_conj_submodule :
    nullSpaceMinus = negGraphConjSubmodule := by
  ext x
  exact mem_nullSpaceMinus_iff x

theorem nullSpacePlus_eq_graph_conj :
    (nullSpacePlus : Set SplitOctCD) = {x : SplitOctCD | x.snd = star x.fst} := by
  ext x
  exact mem_nullSpacePlus_iff x

theorem nullSpaceMinus_eq_neg_graph_conj :
    (nullSpaceMinus : Set SplitOctCD) = {x : SplitOctCD | x.snd = -star x.fst} := by
  ext x
  exact mem_nullSpaceMinus_iff x

theorem uPlusCD_mem_nullSpacePlus : uPlusCD ∈ nullSpacePlus := by
  rw [mem_nullSpacePlus_iff, uPlusCD_components]
  simp

theorem ePlusCD_mem_nullSpacePlus (k : Fin 3) : ePlusCD k ∈ nullSpacePlus := by
  rw [mem_nullSpacePlus_iff, ePlusCD_components]
  simp [qBasis_star]

theorem uMinusCD_mem_nullSpaceMinus : uMinusCD ∈ nullSpaceMinus := by
  rw [mem_nullSpaceMinus_iff, uMinusCD_components]
  simp

theorem eMinusCD_mem_nullSpaceMinus (k : Fin 3) : eMinusCD k ∈ nullSpaceMinus := by
  rw [mem_nullSpaceMinus_iff, eMinusCD_components]
  simp [qBasis_star]

/-- Linear equivalence identifying `nullSpacePlus` with `Quaternion ℝ`. -/
def nullSpacePlusEquivQuaternion : nullSpacePlus ≃ₗ[ℝ] Quaternion ℝ where
  toFun x := x.1.fst
  invFun q := ⟨⟨q, star q⟩, (mem_nullSpacePlus_iff _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (mem_nullSpacePlus_iff x.1).mp x.2
    ext <;> simp [hx]
  right_inv q := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Linear equivalence identifying `nullSpaceMinus` with `Quaternion ℝ`. -/
def nullSpaceMinusEquivQuaternion : nullSpaceMinus ≃ₗ[ℝ] Quaternion ℝ where
  toFun x := x.1.fst
  invFun q := ⟨⟨q, -star q⟩, (mem_nullSpaceMinus_iff _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (mem_nullSpaceMinus_iff x.1).mp x.2
    ext <;> simp [hx]
  right_inv q := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

theorem nullSpacePlus_finrank : Module.finrank ℝ nullSpacePlus = 4 := by
  rw [nullSpacePlusEquivQuaternion.finrank_eq, Quaternion.finrank_eq_four]

theorem nullSpaceMinus_finrank : Module.finrank ℝ nullSpaceMinus = 4 := by
  rw [nullSpaceMinusEquivQuaternion.finrank_eq, Quaternion.finrank_eq_four]

theorem cdNorm_eq_zero_on_nullSpacePlus {x : SplitOctCD} (hx : x ∈ nullSpacePlus) :
    cdNorm x = 0 := by
  rw [mem_nullSpacePlus_iff] at hx
  simp [cdNorm, hx]

theorem cdNorm_eq_zero_on_nullSpaceMinus {x : SplitOctCD} (hx : x ∈ nullSpaceMinus) :
    cdNorm x = 0 := by
  rw [mem_nullSpaceMinus_iff] at hx
  simp [cdNorm, hx]

theorem cdKreinForm_eq_zero_on_nullSpacePlus {x y : SplitOctCD}
    (hx : x ∈ nullSpacePlus) (hy : y ∈ nullSpacePlus) :
    cdKreinForm x y = 0 :=
  cdKreinForm_eq_zero_of_isotropic nullSpacePlus
    (fun _ hz => cdNorm_eq_zero_on_nullSpacePlus hz) hx hy

theorem cdKreinForm_eq_zero_on_nullSpaceMinus {x y : SplitOctCD}
    (hx : x ∈ nullSpaceMinus) (hy : y ∈ nullSpaceMinus) :
    cdKreinForm x y = 0 :=
  cdKreinForm_eq_zero_of_isotropic nullSpaceMinus
    (fun _ hz => cdNorm_eq_zero_on_nullSpaceMinus hz) hx hy

/-- Witt bound in signature `(4, 4)`: any `cdNorm`-isotropic subspace has dimension `≤ 4`. -/
theorem totally_isotropic_finrank_le_four (W : Submodule ℝ SplitOctCD)
    (hW : ∀ x ∈ W, cdNorm x = 0) : Module.finrank ℝ W ≤ 4 := by
  let proj : W →ₗ[ℝ] Quaternion ℝ :=
    { toFun := fun x => x.1.fst
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective proj := by
    intro x y hxy
    have hdiff : x.1 - y.1 ∈ W := W.sub_mem x.2 y.2
    have hnorm : cdNorm (x.1 - y.1) = 0 := hW (x.1 - y.1) hdiff
    have hfst : (x.1 - y.1).fst = 0 := sub_eq_zero.mpr hxy
    have hsnd : (x.1 - y.1).snd = 0 := by
      simpa [cdNorm, hfst] using hnorm
    apply Subtype.ext
    apply sub_eq_zero.mp
    exact SplitOctCD.ext hfst hsnd
  calc
    Module.finrank ℝ W ≤ Module.finrank ℝ (Quaternion ℝ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    _ = 4 := Quaternion.finrank_eq_four

/-- Witt bound in signature `(4, 4)` stated for `cdKreinForm`-totally-isotropic subspaces. -/
theorem totally_isotropic_bilin_finrank_le_four (W : Submodule ℝ SplitOctCD)
    (hW : ∀ x ∈ W, ∀ y ∈ W, cdKreinForm x y = 0) : Module.finrank ℝ W ≤ 4 := by
  refine totally_isotropic_finrank_le_four W ?_
  intro x hx
  rw [← cdKreinForm_self x]
  exact hW x hx x hx

theorem nullSpacePlus_maximal_isotropic (W : Submodule ℝ SplitOctCD)
    (hW : ∀ x ∈ W, cdNorm x = 0) (hle : nullSpacePlus ≤ W) :
    W = nullSpacePlus := by
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [nullSpacePlus_finrank]
  exact totally_isotropic_finrank_le_four W hW

theorem nullSpaceMinus_maximal_isotropic (W : Submodule ℝ SplitOctCD)
    (hW : ∀ x ∈ W, cdNorm x = 0) (hle : nullSpaceMinus ≤ W) :
    W = nullSpaceMinus := by
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [nullSpaceMinus_finrank]
  exact totally_isotropic_finrank_le_four W hW

theorem nullSpacePlus_inf_nullSpaceMinus :
    nullSpacePlus ⊓ nullSpaceMinus = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases hx with ⟨hxP, hxM⟩
  change x ∈ nullSpacePlus at hxP
  change x ∈ nullSpaceMinus at hxM
  rw [mem_nullSpacePlus_iff] at hxP
  rw [mem_nullSpaceMinus_iff] at hxM
  have h2 : star x.fst = -star x.fst := hxP.symm.trans hxM
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  have ha0 : a0 = 0 := by
    have hre := congrArg QuaternionAlgebra.re h2
    simp at hre
    linarith
  have ha1 : a1 = 0 := by
    have himI := congrArg QuaternionAlgebra.imI h2
    simp at himI
    linarith
  have ha2 : a2 = 0 := by
    have himJ := congrArg QuaternionAlgebra.imJ h2
    simp at himJ
    linarith
  have ha3 : a3 = 0 := by
    have himK := congrArg QuaternionAlgebra.imK h2
    simp at himK
    linarith
  have hfst : (⟨a0, a1, a2, a3⟩ : Quaternion ℝ) = 0 := by
    ext <;> simp [ha0, ha1, ha2, ha3]
  have hsnd : (⟨b0, b1, b2, b3⟩ : Quaternion ℝ) = 0 := by
    simpa [hfst] using hxP
  exact SplitOctCD.ext hfst hsnd

theorem nullSpacePlus_sup_nullSpaceMinus :
    nullSpacePlus ⊔ nullSpaceMinus = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine Submodule.mem_sup.mpr ⟨uPlusCD * x, ⟨x, rfl⟩, uMinusCD * x, ⟨x, rfl⟩, ?_⟩
  rw [← cdMul_add_left, uPlusCD_add_uMinusCD, one_cdMul]

theorem splitOctCD_direct_sum_nullSpaces :
    IsCompl nullSpacePlus nullSpaceMinus :=
  IsCompl.of_eq nullSpacePlus_inf_nullSpaceMinus nullSpacePlus_sup_nullSpaceMinus

/-! ## Section 4: Dual Quaternionic Spin Frames vs Ambient Nonassociativity (Feature F7) -/

/-- Right `Quaternion ℝ` spin-frame action on `nullSpacePlus` via `⟨q, star q⟩ ↦ ⟨q * r, star (q * r)⟩`. -/
def spinFrameRightMulPlus (r : Quaternion ℝ) : Module.End ℝ nullSpacePlus where
  toFun x := ⟨⟨x.1.fst * r, star (x.1.fst * r)⟩, (mem_nullSpacePlus_iff _).mpr rfl⟩
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp [add_mul]
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

/-- Right `Quaternion ℝ` spin-frame action on `nullSpaceMinus` via
`⟨q, -star q⟩ ↦ ⟨q * r, -star (q * r)⟩`. -/
def spinFrameRightMulMinus (r : Quaternion ℝ) : Module.End ℝ nullSpaceMinus where
  toFun x := ⟨⟨x.1.fst * r, -star (x.1.fst * r)⟩, (mem_nullSpaceMinus_iff _).mpr rfl⟩
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp [add_mul] <;> ring
  map_smul' c x := by
    apply Subtype.ext
    ext <;> simp

@[simp] theorem spinFrameRightMulPlus_apply (r : Quaternion ℝ) (x : nullSpacePlus) :
    (spinFrameRightMulPlus r x).1 = ⟨x.1.fst * r, star (x.1.fst * r)⟩ := rfl

@[simp] theorem spinFrameRightMulMinus_apply (r : Quaternion ℝ) (x : nullSpaceMinus) :
    (spinFrameRightMulMinus r x).1 = ⟨x.1.fst * r, -star (x.1.fst * r)⟩ := rfl

theorem spinFrameRightMulPlus_one :
    spinFrameRightMulPlus 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx := (mem_nullSpacePlus_iff x.1).mp x.2
  ext <;> simp [hx]

theorem spinFrameRightMulMinus_one :
    spinFrameRightMulMinus 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx := (mem_nullSpaceMinus_iff x.1).mp x.2
  ext <;> simp [hx]

theorem spinFrameRightMulPlus_mul (r₁ r₂ : Quaternion ℝ) :
    spinFrameRightMulPlus (r₁ * r₂) =
      spinFrameRightMulPlus r₂ * spinFrameRightMulPlus r₁ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  ext <;> simp [Module.End.mul_apply, mul_assoc]

theorem spinFrameRightMulMinus_mul (r₁ r₂ : Quaternion ℝ) :
    spinFrameRightMulMinus (r₁ * r₂) =
      spinFrameRightMulMinus r₂ * spinFrameRightMulMinus r₁ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  ext <;> simp [Module.End.mul_apply, mul_assoc]

theorem spinFrameRightMulPlus_eq_uPlus_mul (q r : Quaternion ℝ) :
    (spinFrameRightMulPlus r ⟨uPlusCD * ⟨q, 0⟩, ⟨⟨q, 0⟩, rfl⟩⟩).1 =
      uPlusCD * ⟨q * r, 0⟩ := by
  ext <;> simp [uPlusCD_components] <;> ring

theorem spinFrameRightMulMinus_eq_uMinus_mul (q r : Quaternion ℝ) :
    (spinFrameRightMulMinus r ⟨uMinusCD * ⟨q, 0⟩, ⟨⟨q, 0⟩, rfl⟩⟩).1 =
      uMinusCD * ⟨q * r, 0⟩ := by
  ext <;> simp [uMinusCD_components] <;> ring

/-- Right multiplication by `i₃` in the `+` chiral spin frame rotates `(e₁⁺, e₂⁺) ↦ (-e₂⁺, +e₁⁺)`. -/
theorem ePlusCD_spinFrame_i3_rot :
    spinFrameRightMulPlus (qBasis 2) ⟨ePlusCD 0, ePlusCD_mem_nullSpacePlus 0⟩ =
        -⟨ePlusCD 1, ePlusCD_mem_nullSpacePlus 1⟩ ∧
      spinFrameRightMulPlus (qBasis 2) ⟨ePlusCD 1, ePlusCD_mem_nullSpacePlus 1⟩ =
        ⟨ePlusCD 0, ePlusCD_mem_nullSpacePlus 0⟩ := by
  constructor <;>
    · apply Subtype.ext
      ext <;> simp [ePlusCD_components, qBasis]

/-- Right multiplication by `i₃` in the `-` chiral spin frame rotates `(e₁⁻, e₂⁻) ↦ (-e₂⁻, +e₁⁻)`. -/
theorem eMinusCD_spinFrame_i3_rot :
    spinFrameRightMulMinus (qBasis 2) ⟨eMinusCD 0, eMinusCD_mem_nullSpaceMinus 0⟩ =
        -⟨eMinusCD 1, eMinusCD_mem_nullSpaceMinus 1⟩ ∧
      spinFrameRightMulMinus (qBasis 2) ⟨eMinusCD 1, eMinusCD_mem_nullSpaceMinus 1⟩ =
        ⟨eMinusCD 0, eMinusCD_mem_nullSpaceMinus 0⟩ := by
  constructor <;>
    · apply Subtype.ext
      ext <;> simp [eMinusCD_components, qBasis]

/-- In the ambient nonassociative split-octonion product, right multiplication by `i₃` flips
chirality (`e₁⁺ * i₃ = -e₂⁻` and `e₂⁺ * i₃ = +e₁⁻`). -/
theorem ePlusCD_mul_i3_ambient :
    ePlusCD 0 * iCD 2 = -eMinusCD 1 ∧ ePlusCD 1 * iCD 2 = eMinusCD 0 := by
  constructor <;>
    · ext <;> simp [ePlusCD_components, eMinusCD_components, iCD, qBasis]

/-- In the ambient nonassociative split-octonion product, right multiplication by `i₃` flips
chirality (`e₁⁻ * i₃ = -e₂⁺` and `e₂⁻ * i₃ = +e₁⁺`). -/
theorem eMinusCD_mul_i3_ambient :
    eMinusCD 0 * iCD 2 = -ePlusCD 1 ∧ eMinusCD 1 * iCD 2 = ePlusCD 0 := by
  constructor <;>
    · ext <;> simp [ePlusCD_components, eMinusCD_components, iCD, qBasis]

/-! ## Section 5: Zorn `2 × 2` Vector-Matrix Representation and Cross-Pairing Norm (Feature F8) -/

/-- Reconstruct a split-octonion from Zorn chiral coordinates `(alphaP, alphaM, a, b)`. -/
def chiralZornReconstruct (alphaP alphaM : ℝ) (a b : Fin 3 → ℝ) : SplitOctCD :=
  alphaP • uPlusCD + alphaM • uMinusCD +
    ∑ k : Fin 3, a k • ePlusCD k + ∑ k : Fin 3, b k • eMinusCD k

theorem chiralZornReconstruct_plus_mem (alphaP : ℝ) (a : Fin 3 → ℝ) :
    alphaP • uPlusCD + ∑ k : Fin 3, a k • ePlusCD k ∈ nullSpacePlus := by
  refine nullSpacePlus.add_mem (nullSpacePlus.smul_mem alphaP uPlusCD_mem_nullSpacePlus) ?_
  refine Submodule.sum_mem nullSpacePlus ?_
  intro k _
  exact nullSpacePlus.smul_mem (a k) (ePlusCD_mem_nullSpacePlus k)

theorem chiralZornReconstruct_minus_mem (alphaM : ℝ) (b : Fin 3 → ℝ) :
    alphaM • uMinusCD + ∑ k : Fin 3, b k • eMinusCD k ∈ nullSpaceMinus := by
  refine nullSpaceMinus.add_mem (nullSpaceMinus.smul_mem alphaM uMinusCD_mem_nullSpaceMinus) ?_
  refine Submodule.sum_mem nullSpaceMinus ?_
  intro k _
  exact nullSpaceMinus.smul_mem (b k) (eMinusCD_mem_nullSpaceMinus k)

theorem chiralZornReconstruct_components (alphaP alphaM : ℝ) (a b : Fin 3 → ℝ) :
    chiralZornReconstruct alphaP alphaM a b =
      ⟨ ⟨(alphaP + alphaM) / 2, (a 0 + b 0) / 2, (a 1 + b 1) / 2, (a 2 + b 2) / 2⟩,
        ⟨(alphaP - alphaM) / 2, (b 0 - a 0) / 2, (b 1 - a 1) / 2, (b 2 - a 2) / 2⟩ ⟩ := by
  unfold chiralZornReconstruct
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  ext <;> simp [uPlusCD_components, uMinusCD_components,
    ePlusCD_components, eMinusCD_components, qBasis] <;> ring

/-- Exact `ℝ`-linear equivalence between `SplitOctCD` and Zorn chiral coordinates
`(alphaP, alphaM, a, b) : ℝ × ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)`. -/
def chiralZornEquiv : SplitOctCD ≃ₗ[ℝ] (ℝ × ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)) where
  toFun X :=
    (X.fst.re + X.snd.re,
     X.fst.re - X.snd.re,
     ![X.fst.imI - X.snd.imI, X.fst.imJ - X.snd.imJ, X.fst.imK - X.snd.imK],
     ![X.fst.imI + X.snd.imI, X.fst.imJ + X.snd.imJ, X.fst.imK + X.snd.imK])
  invFun p := chiralZornReconstruct p.1 p.2.1 p.2.2.1 p.2.2.2
  left_inv X := by
    dsimp
    rw [chiralZornReconstruct_components]
    rcases X with ⟨⟨q0, q1, q2, q3⟩, ⟨r0, r1, r2, r3⟩⟩
    ext <;> dsimp <;> ring
  right_inv p := by
    rcases p with ⟨alphaP, alphaM, a, b⟩
    dsimp
    rw [chiralZornReconstruct_components]
    refine Prod.ext (by dsimp; ring) (Prod.ext (by dsimp; ring) (Prod.ext ?_ ?_))
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  map_add' X Y := by
    refine Prod.ext (by dsimp; ring) (Prod.ext (by dsimp; ring) (Prod.ext ?_ ?_))
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  map_smul' c X := by
    refine Prod.ext (by simp [smul_eq_mul]; ring) (Prod.ext (by simp [smul_eq_mul]; ring)
      (Prod.ext ?_ ?_))
    · funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring
    · funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

@[simp] theorem chiralZornEquiv_apply (X : SplitOctCD) :
    chiralZornEquiv X =
      (X.fst.re + X.snd.re,
       X.fst.re - X.snd.re,
       ![X.fst.imI - X.snd.imI, X.fst.imJ - X.snd.imJ, X.fst.imK - X.snd.imK],
       ![X.fst.imI + X.snd.imI, X.fst.imJ + X.snd.imJ, X.fst.imK + X.snd.imK]) := rfl

@[simp] theorem chiralZornEquiv_symm_apply (p : ℝ × ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    chiralZornEquiv.symm p = chiralZornReconstruct p.1 p.2.1 p.2.2.1 p.2.2.2 := rfl

theorem splitOctCDEquivZornMatrix_chiralZornReconstruct (alphaP alphaM : ℝ) (a b : Fin 3 → ℝ) :
    splitOctCDEquivZornMatrix (chiralZornReconstruct alphaP alphaM a b) =
      { a := alphaP, b := alphaM, x := -a, y := b } := by
  rw [chiralZornReconstruct_components]
  apply ZornMatrix.ext
  · dsimp; ring
  · dsimp; ring
  · funext i; fin_cases i <;> simp <;> ring
  · funext i; fin_cases i <;> simp <;> ring

/-- Full Zorn `2 × 2` vector-matrix multiplication in chiral coordinates `(alphaP, alphaM, a, b)`. -/
theorem chiralZornReconstruct_mul (α₁ β₁ α₂ β₂ : ℝ) (a₁ b₁ a₂ b₂ : Fin 3 → ℝ) :
    chiralZornReconstruct α₁ β₁ a₁ b₁ * chiralZornReconstruct α₂ β₂ a₂ b₂ =
      chiralZornReconstruct
        (α₁ * α₂ - ZornMatrix.dot a₁ b₂)
        (β₁ * β₂ - ZornMatrix.dot b₁ a₂)
        (α₁ • a₂ + β₂ • a₁ + ZornMatrix.cross b₁ b₂)
        (β₁ • b₂ + α₂ • b₁ + ZornMatrix.cross a₁ a₂) := by
  apply splitOctCDEquivZornMatrix.injective
  rw [splitOctCDEquivZornMatrix_mul,
    splitOctCDEquivZornMatrix_chiralZornReconstruct,
    splitOctCDEquivZornMatrix_chiralZornReconstruct,
    splitOctCDEquivZornMatrix_chiralZornReconstruct]
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul, ZornMatrix.dot]; ring
  · simp [ZornMatrix.mul, ZornMatrix.dot]; ring
  · funext i
    fin_cases i <;> simp [ZornMatrix.mul, ZornMatrix.cross] <;> ring
  · funext i
    fin_cases i <;> simp [ZornMatrix.mul, ZornMatrix.cross]

/-- The `(4, 4)` Krein norm in Zorn chiral coordinates equals `alphaP * alphaM + ∑ k, a k * b k`. -/
theorem cdNorm_chiralZorn_cross_pairing (alphaP alphaM : ℝ) (a b : Fin 3 → ℝ) :
    cdNorm (chiralZornReconstruct alphaP alphaM a b) = alphaP * alphaM + ∑ k : Fin 3, a k * b k := by
  rw [← splitOctCDEquivZornMatrix_norm, splitOctCDEquivZornMatrix_chiralZornReconstruct]
  simp [InfoGeometry.Canonical.ZornClifford.zornNormFun, ZornMatrix.dot, Fin.sum_univ_three]
  ring

/-- On `SplitOctCD = nullSpacePlus ⊕ nullSpaceMinus`, `cdNorm (xPlus + xMinus)` arises purely from
the cross-pairing `2 * cdKreinForm xPlus xMinus`. -/
theorem cdNorm_nullSpace_cross_pairing {xPlus xMinus : SplitOctCD}
    (hxPlus : xPlus ∈ nullSpacePlus) (hxMinus : xMinus ∈ nullSpaceMinus) :
    cdNorm (xPlus + xMinus) = 2 * cdKreinForm xPlus xMinus := by
  rw [cdNorm_add, cdNorm_eq_zero_on_nullSpacePlus hxPlus,
    cdNorm_eq_zero_on_nullSpaceMinus hxMinus, zero_add, zero_add]

theorem cdKreinForm_chiralZorn_cross_pairing (alphaP alphaM : ℝ) (a b : Fin 3 → ℝ) :
    2 * cdKreinForm
      (alphaP • uPlusCD + ∑ k : Fin 3, a k • ePlusCD k)
      (alphaM • uMinusCD + ∑ k : Fin 3, b k • eMinusCD k) =
      alphaP * alphaM + ∑ k : Fin 3, a k * b k := by
  have hxPlus := chiralZornReconstruct_plus_mem alphaP a
  have hxMinus := chiralZornReconstruct_minus_mem alphaM b
  rw [← cdNorm_nullSpace_cross_pairing hxPlus hxMinus]
  have hsum :
      (alphaP • uPlusCD + ∑ k : Fin 3, a k • ePlusCD k) +
        (alphaM • uMinusCD + ∑ k : Fin 3, b k • eMinusCD k) =
      chiralZornReconstruct alphaP alphaM a b := by
    unfold chiralZornReconstruct
    abel
  rw [hsum, cdNorm_chiralZorn_cross_pairing]

/-! ## Section 6: Non-Commutativity and Non-Associativity Confirmations (Trap T16) -/

/-- Closed non-commutativity theorem for `Module.End ℝ nullSpacePlus`. -/
theorem spinFrameRightMulPlus_noncommutative :
    ∃ A B : Module.End ℝ nullSpacePlus, A * B ≠ B * A := by
  refine ⟨spinFrameRightMulPlus (qBasis 0), spinFrameRightMulPlus (qBasis 1), ?_⟩
  intro h
  have h1 := congrArg
    (fun f : Module.End ℝ nullSpacePlus =>
      (f ⟨uPlusCD, uPlusCD_mem_nullSpacePlus⟩).1.fst.imK) h
  norm_num [Module.End.mul_apply, uPlusCD_components, qBasis] at h1

/-- Closed non-commutativity theorem for `Module.End ℝ nullSpaceMinus`. -/
theorem spinFrameRightMulMinus_noncommutative :
    ∃ A B : Module.End ℝ nullSpaceMinus, A * B ≠ B * A := by
  refine ⟨spinFrameRightMulMinus (qBasis 0), spinFrameRightMulMinus (qBasis 1), ?_⟩
  intro h
  have h1 := congrArg
    (fun f : Module.End ℝ nullSpaceMinus =>
      (f ⟨uMinusCD, uMinusCD_mem_nullSpaceMinus⟩).1.fst.imK) h
  norm_num [Module.End.mul_apply, uMinusCD_components, qBasis] at h1

/-- Chiral basis non-commutativity: `e₁⁺ * e₁⁻ = -u₊ ≠ -u₋ = e₁⁻ * e₁⁺`. -/
theorem ePlusCD_mul_eMinusCD_noncommutative :
    ePlusCD 0 * eMinusCD 0 ≠ eMinusCD 0 * ePlusCD 0 := by
  intro h
  have h1 := congrArg (fun r : SplitOctCD => r.snd.re) h
  norm_num [ePlusCD_components, eMinusCD_components, qBasis] at h1

/-- Non-associativity of `u₊`, `i₁`, `i₃` separating the chiral spin frame from the ambient
split-octonion product. -/
theorem uPlusCD_iCD_nonassociative :
    (uPlusCD * iCD 0) * iCD 2 ≠ uPlusCD * (iCD 0 * iCD 2) := by
  intro h
  have h1 := congrArg (fun r : SplitOctCD => r.snd.imJ) h
  norm_num [uPlusCD_components, iCD, qBasis] at h1

end InfoGeometry.Canonical.SplitOctonionChiralNullDecomposition
