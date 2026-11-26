/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3OctonionZornComplexification
import InfoGeometry.Algebra.H3ZornF4Simplicity
import InfoGeometry.Algebra.H3ZornE6Simplicity
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Simplicity of Complex `E₆(ℂ)` and Compact `𝔢₆(-26)` / `𝔣₄(-52)`

This module establishes:

1. General `LieEquiv.isSimple` transport and `isSimple_of_isSimple_extendScalars` descent
   from `ℂ ⊗[ℝ] L` to `L`.
2. `complexH3ZornCubicStabilizer_isSimple : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3zornCubicStabilizer)`
   (`E₆(ℂ)`) via `SplitChevalleyData.extendScalars ℂ` applied to `e6SplitChevalleyData`.
3. Transport across the complexification equivalences in `H3OctonionZornComplexification` and
   descent to the compact real forms:
   - `instance h3OctonionCubicStabilizer_isSimple : LieAlgebra.IsSimple ℝ h3OctonionCubicStabilizer` (`𝔢₆(-26)`)
   - `instance h3OctonionF4Derivations_isSimple : LieAlgebra.IsSimple ℝ H3OctonionF4Derivations` (`𝔣₄(-52)`)
   - Together with `IsSemisimple ℝ`, `HasTrivialRadical ℝ`, and `center = ⊥` theorems/instances.
-/

noncomputable section

namespace InfoGeometry.Algebra

open InfoGeometry.Exceptional.CFSGPort.Chevalley
open scoped TensorProduct

section BaseChangeSimplicityBridge

/-- Lie algebra simplicity transports across a `K`-Lie algebra equivalence. -/
theorem LieEquiv.isSimple {K L₁ L₂ : Type*} [CommRing K] [LieRing L₁] [LieAlgebra K L₁]
    [LieRing L₂] [LieAlgebra K L₂] (e : L₁ ≃ₗ⁅K⁆ L₂) [h : LieAlgebra.IsSimple K L₁] :
    LieAlgebra.IsSimple K L₂ where
  eq_bot_or_eq_top I := by
    let I₁ : LieIdeal K L₁ :=
      { carrier := {x | e x ∈ I}
        zero_mem' := by simp
        add_mem' := fun hx hy => by
          simp only [Set.mem_ofPred_eq, map_add] at *
          exact I.add_mem hx hy
        smul_mem' := fun c _ hx => by
          simp only [Set.mem_ofPred_eq, map_smul] at *
          exact I.smul_mem c hx
        lie_mem := fun {a _} hy => by
          change e ⁅a, _⁆ ∈ I
          rw [e.map_lie]
          exact I.lie_mem hy }
    rcases h.eq_bot_or_eq_top I₁ with hbot | htop
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : x ∈ I₁ := hy
      rw [hbot, LieSubmodule.mem_bot] at hx
      subst hx
      simp
    · right
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : x ∈ I₁ := by rw [htop]; trivial
      exact hx
  non_abelian := by
    rw [← lie_abelian_iff_equiv_lie_abelian e]
    exact h.non_abelian

/-- Descent of simplicity from the complexification `ℂ ⊗[ℝ] L` to the real Lie algebra `L`. -/
theorem isSimple_of_isSimple_extendScalars {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (h : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] L)) :
    LieAlgebra.IsSimple ℝ L where
  eq_bot_or_eq_top I := by
    let reProj : ℂ ⊗[ℝ] L →ₗ[ℝ] L :=
      (TensorProduct.lid ℝ L).toLinearMap ∘ₗ Complex.reLm.rTensor L
    have hreProj_tmul : ∀ (z : ℂ) (x : L), reProj (z ⊗ₜ[ℝ] x) = z.re • x := fun z x => by
      simp [reProj]
    rcases h.eq_bot_or_eq_top (I.baseChange ℂ) with hbot | htop
    · left
      rw [eq_bot_iff]
      intro x hx
      have hmem : (1 : ℂ) ⊗ₜ[ℝ] x ∈ I.baseChange ℂ :=
        LieSubmodule.tmul_mem_baseChange_of_mem 1 hx
      rw [hbot, LieSubmodule.mem_bot] at hmem
      have hx0 := congrArg reProj hmem
      rw [hreProj_tmul, Complex.one_re, one_smul, map_zero] at hx0
      exact hx0
    · right
      rw [eq_top_iff]
      intro x _
      have hmem : (1 : ℂ) ⊗ₜ[ℝ] x ∈ LieSubmodule.toSubmodule (I.baseChange ℂ) := by
        rw [htop]; trivial
      rw [LieSubmodule.coe_baseChange] at hmem
      obtain ⟨u, hu⟩ := Submodule.toBaseChange_surjective ℂ (I : Submodule ℝ L) ⟨_, hmem⟩
      have hu' : ((Submodule.toBaseChange ℂ (I : Submodule ℝ L) u :
          ↥(Submodule.baseChange ℂ (I : Submodule ℝ L))) : ℂ ⊗[ℝ] L) = (1 : ℂ) ⊗ₜ[ℝ] x :=
        congrArg Subtype.val hu
      have hproj : ∀ v : ℂ ⊗[ℝ] ↥(I : Submodule ℝ L),
          reProj ((Submodule.toBaseChange ℂ (I : Submodule ℝ L) v :
            ↥(Submodule.baseChange ℂ (I : Submodule ℝ L))) : ℂ ⊗[ℝ] L) ∈ I := by
        intro v
        induction v using TensorProduct.inductionOn with
        | tmul z y =>
          rw [Submodule.coe_toBaseChange_tmul, hreProj_tmul]
          exact I.smul_mem z.re y.2
        | add a b ha hb =>
          rw [map_add, Submodule.coe_add, map_add]
          exact I.add_mem ha hb
      have hxI := hproj u
      rw [hu', hreProj_tmul, Complex.one_re, one_smul] at hxI
      exact hxI
  non_abelian := by
    intro hab
    apply h.non_abelian
    refine ⟨fun u v => ?_⟩
    induction u using TensorProduct.inductionOn generalizing v with
    | tmul z₁ x₁ =>
      induction v using TensorProduct.inductionOn with
      | tmul z₂ x₂ =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hab.trivial x₁ x₂, TensorProduct.tmul_zero]
      | add a b ha hb => rw [lie_add, ha, hb, add_zero]
    | add a b ha hb => rw [add_lie, ha, hb, add_zero]

end BaseChangeSimplicityBridge

section ComplexE6Simplicity

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private theorem e6_rootEigenvalue_ne_zero (r : Fin 72) : ∃ i : Fin 6, rootEigenvalue i r ≠ 0 := by
  have h : (List.finRange 72).all (fun r =>
      (List.finRange 6).any (fun i => rootEigenvalue i r != 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨i, _, hi⟩ := h r
  exact ⟨i, hi⟩

private theorem e6_rootEigenvalue_eq_imp {r₁ r₂ : Fin 72}
    (h : ∀ i : Fin 6, rootEigenvalue i r₁ = rootEigenvalue i r₂) : r₁ = r₂ := by
  have hchk : (List.finRange 72).all (fun r₁ => (List.finRange 72).all (fun r₂ =>
      if r₁ = r₂ then true else
        (List.finRange 6).any (fun i => rootEigenvalue i r₁ != rootEigenvalue i r₂))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  by_contra hne
  have h12 := hchk r₁ r₂
  simp only [hne, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne,
    ne_eq] at h12
  obtain ⟨i, hi⟩ := h12
  exact hi (h i)

private theorem e6_posRaiseStep_spec (r : Fin 72) (hpos : 0 < e6RootHeight r)
    (hne : r ≠ e6HighestRootIdx) :
    let st := posRaiseStep r
    ⁅e6SimpleE st.1, e6RootVec r⁆ = (st.2.2 : ℝ) • e6RootVec st.2.1 ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ st.2.2 ≠ 0 := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (0 < e6RootHeight r) && (r != e6HighestRootIdx) then
        let st := posRaiseStep r
        sparseEq (sparseComm (e6SimpleESparse st.1) (e6RootSparse r))
          (sparseSmul st.2.2 (e6RootSparse st.2.1)) &&
        decide (e6RootHeight r < e6RootHeight st.2.1) &&
        (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : (decide (0 < e6RootHeight r) && (r != e6HighestRootIdx)) = true := by
    simp [hpos, hne]
  simp only [hcond, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
  refine ⟨?_, hr.1.2, hr.2⟩
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅e6SimpleE (posRaiseStep r).1, e6RootVec r⁆ :
    Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6RootVec,
    SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec]
  have hcomm : (sparseToMat (e6SimpleESparse (posRaiseStep r).1)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse r)).map Int.cast -
      (sparseToMat (e6RootSparse r)).map Int.cast *
        (sparseToMat (e6SimpleESparse (posRaiseStep r).1)).map Int.cast =
      (sparseToMat (sparseComm (e6SimpleESparse (posRaiseStep r).1) (e6RootSparse r))).map
        Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem e6_negRaiseStep_spec (r : Fin 72) (hneg : e6RootHeight r < -1) :
    let st := negRaiseStep r
    ⁅e6SimpleE st.1, e6RootVec r⁆ = (st.2.2 : ℝ) • e6RootVec st.2.1 ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ e6RootHeight st.2.1 < 0 ∧ st.2.2 ≠ 0 := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (e6RootHeight r < -1) then
        let st := negRaiseStep r
        sparseEq (sparseComm (e6SimpleESparse st.1) (e6RootSparse r))
          (sparseSmul st.2.2 (e6RootSparse st.2.1)) &&
        decide (e6RootHeight r < e6RootHeight st.2.1) &&
        decide (e6RootHeight st.2.1 < 0) &&
        (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (e6RootHeight r < -1) = true := decide_eq_true hneg
  simp only [hcond, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
  refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅e6SimpleE (negRaiseStep r).1, e6RootVec r⁆ :
    Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6RootVec,
    SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec]
  have hcomm : (sparseToMat (e6SimpleESparse (negRaiseStep r).1)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse r)).map Int.cast -
      (sparseToMat (e6RootSparse r)).map Int.cast *
        (sparseToMat (e6SimpleESparse (negRaiseStep r).1)).map Int.cast =
      (sparseToMat (sparseComm (e6SimpleESparse (negRaiseStep r).1) (e6RootSparse r))).map
        Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem e6_negHeight_negOne_eq_fSimple (r : Fin 72) (h1 : e6RootHeight r = -1) :
    ∃ i : Fin 6, r = fSimpleIdx i := by
  have hchk : (List.finRange 72).all (fun r =>
      if e6RootHeight r == -1 then
        (List.finRange 6).any (fun i => r == fSimpleIdx i)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : (e6RootHeight r == -1) = true := beq_iff_eq.mpr h1
  simp only [hcond, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq] at hr
  exact hr

private theorem e6_posLowerStep_spec (r : Fin 72) (hpos : 0 < e6RootHeight r) :
    (posLowerStep r = none → r = e6HighestRootIdx) ∧
    (∀ st, posLowerStep r = some st →
      ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ = (st.2.2 : ℝ) • e6RootVec r ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ 0 < e6RootHeight st.2.1 ∧ st.2.2 ≠ 0) := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (0 < e6RootHeight r) then
        match posLowerStep r with
        | none => r == e6HighestRootIdx
        | some st =>
          sparseEq (sparseComm (e6SimpleFSparse st.1) (e6RootSparse st.2.1))
            (sparseSmul st.2.2 (e6RootSparse r)) &&
          decide (e6RootHeight r < e6RootHeight st.2.1) &&
          decide (0 < e6RootHeight st.2.1) &&
          (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (0 < e6RootHeight r) = true := decide_eq_true hpos
  simp only [hcond, ↓reduceIte] at hr
  constructor
  · intro hnone
    rw [hnone] at hr
    exact beq_iff_eq.mp hr
  · intro st hsome
    rw [hsome] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
    refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
    apply Subtype.ext
    apply h3zornToMatrix.injective
    change h3zornToMatrix (⁅e6SimpleF st.1, e6RootVec st.2.1⁆ :
      Module.End ℝ (H3Zorn ℝ)) = _
    rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleF, h3zornToMatrix_e6RootVec,
      SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec]
    have hcomm : (sparseToMat (e6SimpleFSparse st.1)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (e6RootSparse st.2.1)).map Int.cast -
        (sparseToMat (e6RootSparse st.2.1)).map Int.cast *
          (sparseToMat (e6SimpleFSparse st.1)).map Int.cast =
        (sparseToMat (sparseComm (e6SimpleFSparse st.1) (e6RootSparse st.2.1))).map Int.cast := by
      rw [sparseToMat_comm]
      ext a b; simp [Matrix.mul_apply]
    rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
    ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem e6_negLowerStep_spec (r : Fin 72) (hneg : e6RootHeight r < 0) :
    (negLowerStep r = none → ∃ i : Fin 6, r = fSimpleIdx i) ∧
    (∀ st, negLowerStep r = some st →
      ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ = (st.2.2 : ℝ) • e6RootVec r ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ e6RootHeight st.2.1 < 0 ∧ st.2.2 ≠ 0) := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (e6RootHeight r < 0) then
        match negLowerStep r with
        | none => (List.finRange 6).any (fun i => r == fSimpleIdx i)
        | some st =>
          sparseEq (sparseComm (e6SimpleFSparse st.1) (e6RootSparse st.2.1))
            (sparseSmul st.2.2 (e6RootSparse r)) &&
          decide (e6RootHeight r < e6RootHeight st.2.1) &&
          decide (e6RootHeight st.2.1 < 0) &&
          (st.2.2 != 0)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (e6RootHeight r < 0) = true := decide_eq_true hneg
  simp only [hcond, ↓reduceIte] at hr
  constructor
  · intro hnone
    rw [hnone] at hr
    simp only [List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq] at hr
    exact hr
  · intro st hsome
    rw [hsome] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
    refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
    apply Subtype.ext
    apply h3zornToMatrix.injective
    change h3zornToMatrix (⁅e6SimpleF st.1, e6RootVec st.2.1⁆ :
      Module.End ℝ (H3Zorn ℝ)) = _
    rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleF, h3zornToMatrix_e6RootVec,
      SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec]
    have hcomm : (sparseToMat (e6SimpleFSparse st.1)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (e6RootSparse st.2.1)).map Int.cast -
        (sparseToMat (e6RootSparse st.2.1)).map Int.cast *
          (sparseToMat (e6SimpleFSparse st.1)).map Int.cast =
        (sparseToMat (sparseComm (e6SimpleFSparse st.1) (e6RootSparse st.2.1))).map Int.cast := by
      rw [sparseToMat_comm]
      ext a b; simp [Matrix.mul_apply]
    rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
    ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private def e6CartanInv3 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 3, 5, 6, 4, 2;
     3, 6, 6, 9, 6, 3;
     5, 6, 10, 12, 8, 4;
     6, 9, 12, 18, 12, 6;
     4, 6, 8, 12, 10, 5;
     2, 3, 4, 6, 5, 4]

private theorem e6CartanInv3_mul_transpose (i k : Fin 6) :
    ∑ j : Fin 6, e6CartanInv3 i j * Tag.cartan .E6 k j = if i = k then 3 else 0 := by
  have h : (List.finRange 6).all (fun i => (List.finRange 6).all (fun k =>
      (∑ j : Fin 6, e6CartanInv3 i j * Tag.cartan .E6 k j) == (if i = k then 3 else 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i k

/-- Bundled split Chevalley data for `h3zornCubicStabilizer` (`𝔢₆(6)`). -/
def e6SplitChevalleyData : SplitChevalleyData ℝ h3zornCubicStabilizer 6 72 where
  rk_pos := by decide
  H := e6SimpleH
  E := e6SimpleE
  F := e6SimpleF
  R := e6RootVec
  basis := e6ChevalleyBasis
  basis_inl := e6ChevalleyBasis_inl
  basis_inr := e6ChevalleyBasis_inr
  ev := rootEigenvalue
  C := Tag.cartan .E6
  C_inv := e6CartanInv3
  detC := 3
  detC_ne_zero := by decide
  C_inv_mul_transpose := e6CartanInv3_mul_transpose
  C_diag i := by fin_cases i <;> decide
  eIdx := eSimpleIdx
  fIdx := fSimpleIdx
  eSgn _ := 1
  fSgn := fSimpleSign
  eSgn_ne_zero _ := by decide
  fSgn_ne_zero i := by fin_cases i <;> decide
  e_eq i := by simp [e6SimpleE]
  f_eq _ := rfl
  hiIdx := e6HighestRootIdx
  ht := e6RootHeight
  maxHt := 11
  ht_bounds := e6RootHeight_bounds
  ht_hi := e6RootHeight_highest
  ht_eSimple i := by fin_cases i <;> decide
  ht_fSimple := e6RootHeight_fSimple
  negHeight_negOne_eq_fSimple := e6_negHeight_negOne_eq_fSimple
  posRaise := posRaiseStep
  negRaise := negRaiseStep
  posLower := posLowerStep
  negLower := negLowerStep
  bracket_HH := e6SimpleH_comm
  bracket_HR := e6RootVec_bracket_H
  bracket_HE := e6Simple_bracket_HE
  bracket_HF_same i := by
    rw [e6Simple_bracket_HF]
    have hc : Tag.cartan .E6 i i = 2 := by fin_cases i <;> decide
    rw [hc]
    norm_num
  bracket_EF_same := e6Simple_bracket_EF_same
  ev_ne_zero := e6_rootEigenvalue_ne_zero
  ev_inj := e6_rootEigenvalue_eq_imp
  posRaise_spec := e6_posRaiseStep_spec
  negRaise_spec := e6_negRaiseStep_spec
  posLower_spec := e6_posLowerStep_spec
  negLower_spec := e6_negLowerStep_spec

/-- **Unconditional Simplicity of Complex `E₆(ℂ)`**:
`ℂ ⊗[ℝ] h3zornCubicStabilizer` is a simple 78-dimensional complex Lie algebra. -/
instance complexH3zornCubicStabilizer_isSimple :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3zornCubicStabilizer) :=
  (e6SplitChevalleyData.extendScalars ℂ).isSimple

/-- Explicit non-commutativity witness on `Matrix (Fin 27) (Fin 27) ℝ` from `E₆`. -/
theorem e6_simplicity_matrix27_real_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A :=
  matrix27_real_noncomm_witness

end ComplexE6Simplicity

section CompactSimplicityExports

private instance : Module.Finite ℝ h3OctonionCubicStabilizer :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_h3OctonionCubicStabilizer]; decide)

private instance : Module.Finite ℝ H3OctonionF4Derivations :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_H3OctonionF4Derivations]; decide)

/-- Simplicity of complexified compact `𝔢₆(-26)`, transported from `E₆(ℂ)` on `H3Zorn ℝ`. -/
instance complexH3OctonionCubicStabilizer_isSimple :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h3OctonionCubicStabilizer) :=
  LieEquiv.isSimple h3OctonionCubicStabilizerBaseChangeEquiv.symm

/-- Simplicity of complexified compact `𝔣₄(-52)`, transported from `F₄(ℂ)` on `H3Zorn ℝ`. -/
instance complexH3OctonionF4Derivations_isSimple :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] H3OctonionF4Derivations) :=
  LieEquiv.isSimple h3OctonionF4DerivationsBaseChangeEquiv.symm

/-- **Unconditional Simplicity of Compact `𝔢₆(-26)`**:
`h3OctonionCubicStabilizer` is a simple 78-dimensional real Lie algebra. -/
instance h3OctonionCubicStabilizer_isSimple :
    LieAlgebra.IsSimple ℝ h3OctonionCubicStabilizer :=
  isSimple_of_isSimple_extendScalars complexH3OctonionCubicStabilizer_isSimple

instance h3OctonionCubicStabilizer_isSemisimple :
    LieAlgebra.IsSemisimple ℝ h3OctonionCubicStabilizer :=
  inferInstance

instance h3OctonionCubicStabilizer_hasTrivialRadical :
    LieAlgebra.HasTrivialRadical ℝ h3OctonionCubicStabilizer :=
  inferInstance

theorem center_h3OctonionCubicStabilizer_eq_bot :
    LieAlgebra.center ℝ h3OctonionCubicStabilizer = ⊥ :=
  le_antisymm (LieAlgebra.center_le_radical _ _ |>.trans (by simp)) bot_le

/-- **Unconditional Simplicity of Compact `𝔣₄(-52)`**:
`H3OctonionF4Derivations` is a simple 52-dimensional real Lie algebra. -/
instance h3OctonionF4Derivations_isSimple :
    LieAlgebra.IsSimple ℝ H3OctonionF4Derivations :=
  isSimple_of_isSimple_extendScalars complexH3OctonionF4Derivations_isSimple

instance h3OctonionF4Derivations_isSemisimple :
    LieAlgebra.IsSemisimple ℝ H3OctonionF4Derivations :=
  inferInstance

instance h3OctonionF4Derivations_hasTrivialRadical :
    LieAlgebra.HasTrivialRadical ℝ H3OctonionF4Derivations :=
  inferInstance

theorem center_h3OctonionF4Derivations_eq_bot :
    LieAlgebra.center ℝ H3OctonionF4Derivations = ⊥ :=
  le_antisymm (LieAlgebra.center_le_radical _ _ |>.trans (by simp)) bot_le

end CompactSimplicityExports

end InfoGeometry.Algebra
