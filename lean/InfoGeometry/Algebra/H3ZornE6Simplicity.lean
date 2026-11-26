/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Unconditional Simplicity of Split `𝔢₆(6)` (`h3zornCubicStabilizer`)

Proves natively (without external axioms or `sorry`) that the 78-dimensional reduced structure
Lie algebra `h3zornCubicStabilizer` of `H3Zorn ℝ` is simple (`LieAlgebra.IsSimple`), hence
semisimple (`LieAlgebra.IsSemisimple`), has trivial radical (`LieAlgebra.HasTrivialRadical`),
and trivial center (`LieAlgebra.center ℝ h3zornCubicStabilizer = ⊥`).
-/

noncomputable section

namespace InfoGeometry.Algebra

open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private instance : Module.Finite ℝ h3zornCubicStabilizer :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_h3zornCubicStabilizer]; decide)

section RootChains

def e6RootHeight (r : Fin 72) : ℤ := ∑ i : Fin 6, e6RootCoord r i

theorem e6RootHeight_bounds (r : Fin 72) :
    e6RootHeight r ≠ 0 ∧ -11 ≤ e6RootHeight r ∧ e6RootHeight r ≤ 11 := by
  have h : (List.finRange 72).all (fun r =>
      (e6RootHeight r != 0) && decide (-11 ≤ e6RootHeight r) && decide (e6RootHeight r ≤ 11)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at h
  exact ⟨(h r).1.1, (h r).1.2, (h r).2⟩

theorem e6RootHeight_highest : e6RootHeight e6HighestRootIdx = 11 := by decide

theorem e6RootHeight_fSimple (i : Fin 6) : e6RootHeight (fSimpleIdx i) = -1 := by
  fin_cases i <;> decide

def posRaiseStep (r : Fin 72) : Fin 6 × Fin 72 × ℤ :=
  match r.val with

  | 0 => (1, 1, -1)
  | 1 => (3, 2, -1)
  | 2 => (2, 25, 1)
  | 4 => (1, 3, 1)
  | 5 => (3, 4, 1)
  | 12 => (3, 15, -1)
  | 15 => (2, 33, -1)
  | 16 => (1, 15, 1)
  | 18 => (0, 63, 1)
  | 19 => (0, 61, -1)
  | 21 => (0, 59, 1)
  | 24 => (2, 5, -1)
  | 25 => (4, 5, -1)
  | 32 => (2, 19, -1)
  | 33 => (0, 48, 1)
  | 34 => (1, 32, 1)
  | 35 => (0, 50, 1)
  | 36 => (3, 34, 1)
  | 37 => (0, 52, 1)
  | 48 => (4, 61, 1)
  | 49 => (2, 60, -1)
  | 50 => (1, 48, 1)
  | 51 => (1, 49, 1)
  | 52 => (3, 50, 1)
  | 53 => (3, 51, 1)
  | 54 => (5, 25, -1)
  | 55 => (0, 24, 1)
  | 58 => (0, 0, -1)
  | 59 => (1, 61, -1)
  | 60 => (0, 1, -1)
  | 61 => (3, 63, -1)
  | 62 => (0, 2, -1)
  | 63 => (2, 54, 1)
  | 70 => (4, 53, 1)
  | 71 => (2, 52, -1)
  | _ => (0, 3, 1)


def negRaiseStep (r : Fin 72) : Fin 6 × Fin 72 × ℤ :=
  match r.val with

  | 6 => (3, 7, -1)
  | 7 => (1, 11, -1)
  | 9 => (1, 13, -1)
  | 10 => (1, 14, -1)
  | 11 => (2, 29, 1)
  | 14 => (3, 17, -1)
  | 17 => (2, 39, -1)
  | 20 => (0, 65, 1)
  | 22 => (0, 67, 1)
  | 23 => (0, 69, 1)
  | 26 => (1, 28, -1)
  | 27 => (1, 29, -1)
  | 28 => (2, 13, -1)
  | 29 => (3, 31, -1)
  | 38 => (2, 23, 1)
  | 39 => (0, 40, -1)
  | 40 => (4, 69, -1)
  | 41 => (2, 68, 1)
  | 42 => (1, 44, -1)
  | 43 => (0, 26, -1)
  | 44 => (3, 46, -1)
  | 45 => (0, 28, -1)
  | 46 => (4, 57, 1)
  | 47 => (0, 30, -1)
  | 64 => (0, 11, -1)
  | 65 => (2, 44, -1)
  | 66 => (0, 7, 1)
  | 67 => (1, 65, 1)
  | 68 => (0, 6, -1)
  | 69 => (3, 67, 1)
  | _ => (0, 56, 1)


def posLowerStep (r : Fin 72) : Option (Fin 6 × Fin 72 × ℤ) :=
  match r.val with

  | 0 => some (1, 1, -1)
  | 1 => some (3, 2, -1)
  | 2 => some (4, 24, 1)
  | 4 => some (1, 3, 1)
  | 5 => some (3, 4, 1)
  | 12 => some (3, 15, -1)
  | 15 => some (4, 32, -1)
  | 16 => some (4, 34, -1)
  | 18 => some (5, 62, 1)
  | 19 => some (5, 60, -1)
  | 21 => some (5, 58, 1)
  | 24 => some (2, 5, -1)
  | 25 => some (4, 5, -1)
  | 32 => some (5, 49, -1)
  | 33 => some (4, 19, -1)
  | 34 => some (5, 51, -1)
  | 35 => some (4, 21, -1)
  | 36 => some (5, 53, -1)
  | 37 => some (3, 35, 1)
  | 48 => some (4, 61, 1)
  | 49 => some (2, 60, -1)
  | 50 => some (4, 59, -1)
  | 51 => some (2, 58, 1)
  | 52 => some (3, 50, 1)
  | 53 => some (3, 51, 1)
  | 54 => some (5, 25, -1)
  | 55 => some (0, 24, 1)
  | 58 => some (1, 60, -1)
  | 59 => some (5, 0, -1)
  | 60 => some (3, 62, -1)
  | 61 => some (5, 1, -1)
  | 62 => some (4, 55, -1)
  | 63 => some (5, 2, -1)
  | 70 => some (4, 53, 1)
  | 71 => some (2, 52, -1)
  | _ => none


def negLowerStep (r : Fin 72) : Option (Fin 6 × Fin 72 × ℤ) :=
  match r.val with

  | 6 => some (3, 7, -1)
  | 7 => some (4, 26, 1)
  | 9 => some (3, 8, 1)
  | 10 => some (1, 14, -1)
  | 11 => some (4, 28, 1)
  | 14 => some (3, 17, -1)
  | 17 => some (4, 38, -1)
  | 20 => some (5, 64, 1)
  | 22 => some (5, 66, 1)
  | 23 => some (5, 68, 1)
  | 26 => some (2, 9, -1)
  | 27 => some (4, 9, -1)
  | 28 => some (3, 30, -1)
  | 29 => some (4, 13, -1)
  | 38 => some (5, 41, 1)
  | 39 => some (4, 23, 1)
  | 40 => some (4, 69, -1)
  | 41 => some (2, 68, 1)
  | 42 => some (5, 27, 1)
  | 43 => some (1, 45, -1)
  | 44 => some (5, 29, 1)
  | 45 => some (3, 47, -1)
  | 46 => some (5, 31, 1)
  | 47 => some (2, 56, -1)
  | 64 => some (4, 45, 1)
  | 65 => some (5, 11, -1)
  | 66 => some (4, 43, -1)
  | 67 => some (5, 7, 1)
  | 68 => some (3, 66, 1)
  | 69 => some (5, 6, -1)
  | _ => none


private theorem posRaiseStep_spec (r : Fin 72) (hpos : 0 < e6RootHeight r)
    (hne : r ≠ e6HighestRootIdx) :
    let st := posRaiseStep r
    ⁅e6SimpleE st.1, e6RootVec r⁆ = (st.2.2 : ℝ) • e6RootVec st.2.1 ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ (st.2.2 = 1 ∨ st.2.2 = -1) := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (0 < e6RootHeight r) && (r != e6HighestRootIdx) then
        let st := posRaiseStep r
        sparseEq (sparseComm (e6SimpleESparse st.1) (e6RootSparse r))
          (sparseSmul st.2.2 (e6RootSparse st.2.1)) &&
        decide (e6RootHeight r < e6RootHeight st.2.1) &&
        ((st.2.2 == 1) || (st.2.2 == -1))
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : (decide (0 < e6RootHeight r) && (r != e6HighestRootIdx)) = true := by
    simp [hpos, hne]
  simp only [hcond, ↓reduceIte] at hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  refine ⟨?_, hr.1.2, hr.2⟩
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅e6SimpleE (posRaiseStep r).1, e6RootVec r⁆ : Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6RootVec,
    SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec]
  have hcomm : (sparseToMat (e6SimpleESparse (posRaiseStep r).1)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse r)).map Int.cast -
      (sparseToMat (e6RootSparse r)).map Int.cast *
        (sparseToMat (e6SimpleESparse (posRaiseStep r).1)).map Int.cast =
      (sparseToMat (sparseComm (e6SimpleESparse (posRaiseStep r).1) (e6RootSparse r))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem negRaiseStep_spec (r : Fin 72) (hneg : e6RootHeight r < -1) :
    let st := negRaiseStep r
    ⁅e6SimpleE st.1, e6RootVec r⁆ = (st.2.2 : ℝ) • e6RootVec st.2.1 ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ e6RootHeight st.2.1 < 0 ∧
      (st.2.2 = 1 ∨ st.2.2 = -1) := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (e6RootHeight r < -1) then
        let st := negRaiseStep r
        sparseEq (sparseComm (e6SimpleESparse st.1) (e6RootSparse r))
          (sparseSmul st.2.2 (e6RootSparse st.2.1)) &&
        decide (e6RootHeight r < e6RootHeight st.2.1) &&
        decide (e6RootHeight st.2.1 < 0) &&
        ((st.2.2 == 1) || (st.2.2 == -1))
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : decide (e6RootHeight r < -1) = true := decide_eq_true hneg
  simp only [hcond, ↓reduceIte] at hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅e6SimpleE (negRaiseStep r).1, e6RootVec r⁆ : Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6RootVec,
    SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec]
  have hcomm : (sparseToMat (e6SimpleESparse (negRaiseStep r).1)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse r)).map Int.cast -
      (sparseToMat (e6RootSparse r)).map Int.cast *
        (sparseToMat (e6SimpleESparse (negRaiseStep r).1)).map Int.cast =
      (sparseToMat (sparseComm (e6SimpleESparse (negRaiseStep r).1) (e6RootSparse r))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_of_sparseEq hr.1.1.1, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem negHeight_negOne_eq_fSimple (r : Fin 72) (h1 : e6RootHeight r = -1) :
    ∃ i : Fin 6, r = fSimpleIdx i := by
  have hchk : (List.finRange 72).all (fun r =>
      if e6RootHeight r == -1 then
        (List.finRange 6).any (fun i => r == fSimpleIdx i)
      else true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hr := hchk r
  have hcond : (e6RootHeight r == -1) = true := beq_iff_eq.mpr h1
  simp only [hcond, ↓reduceIte] at hr
  simp only [List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq] at hr
  exact hr

private theorem posLowerStep_spec (r : Fin 72) (hpos : 0 < e6RootHeight r) :
    (posLowerStep r = none → r = e6HighestRootIdx) ∧
    (∀ st, posLowerStep r = some st →
      ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ = (st.2.2 : ℝ) • e6RootVec r ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ 0 < e6RootHeight st.2.1 ∧
      (st.2.2 = 1 ∨ st.2.2 = -1)) := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (0 < e6RootHeight r) then
        match posLowerStep r with
        | none => r == e6HighestRootIdx
        | some st =>
          sparseEq (sparseComm (e6SimpleFSparse st.1) (e6RootSparse st.2.1))
            (sparseSmul st.2.2 (e6RootSparse r)) &&
          decide (e6RootHeight r < e6RootHeight st.2.1) &&
          decide (0 < e6RootHeight st.2.1) &&
          ((st.2.2 == 1) || (st.2.2 == -1))
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
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
    refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
    apply Subtype.ext
    apply h3zornToMatrix.injective
    change h3zornToMatrix (⁅e6SimpleF st.1, e6RootVec st.2.1⁆ : Module.End ℝ (H3Zorn ℝ)) = _
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

private theorem negLowerStep_spec (r : Fin 72) (hneg : e6RootHeight r < 0) :
    (negLowerStep r = none → ∃ i : Fin 6, r = fSimpleIdx i) ∧
    (∀ st, negLowerStep r = some st →
      ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ = (st.2.2 : ℝ) • e6RootVec r ∧
      e6RootHeight r < e6RootHeight st.2.1 ∧ e6RootHeight st.2.1 < 0 ∧
      (st.2.2 = 1 ∨ st.2.2 = -1)) := by
  have hchk : (List.finRange 72).all (fun r =>
      if decide (e6RootHeight r < 0) then
        match negLowerStep r with
        | none => (List.finRange 6).any (fun i => r == fSimpleIdx i)
        | some st =>
          sparseEq (sparseComm (e6SimpleFSparse st.1) (e6RootSparse st.2.1))
            (sparseSmul st.2.2 (e6RootSparse r)) &&
          decide (e6RootHeight r < e6RootHeight st.2.1) &&
          decide (e6RootHeight st.2.1 < 0) &&
          ((st.2.2 == 1) || (st.2.2 == -1))
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
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
    refine ⟨?_, hr.1.1.2, hr.1.2, hr.2⟩
    apply Subtype.ext
    apply h3zornToMatrix.injective
    change h3zornToMatrix (⁅e6SimpleF st.1, e6RootVec st.2.1⁆ : Module.End ℝ (H3Zorn ℝ)) = _
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

end RootChains

section SimplicityProof

private theorem smul_unit_sign_mem {I : LieIdeal ℝ h3zornCubicStabilizer}
    {s : ℤ} (hs : s = 1 ∨ s = -1) {x : h3zornCubicStabilizer}
    (hx : (s : ℝ) • x ∈ I) : x ∈ I := by
  have hsne : (s : ℝ) ≠ 0 := by
    rcases hs with rfl | rfl <;> norm_num
  have hsm := I.smul_mem (s : ℝ)⁻¹ hx
  rw [smul_smul, inv_mul_cancel₀ hsne, one_smul] at hsm
  exact hsm

private theorem pos_root_mem_ideal_imp_highest (I : LieIdeal ℝ h3zornCubicStabilizer) :
    ∀ n : ℕ, ∀ r : Fin 72, 0 < e6RootHeight r → (11 - e6RootHeight r).toNat ≤ n →
      e6RootVec r ∈ I → e6RootVec e6HighestRootIdx ∈ I := by
  intro n
  induction n with
  | zero =>
    intro r hpos hle hrI
    have hhi : e6RootHeight r = 11 := by
      have hb := (e6RootHeight_bounds r).2.2
      omega
    by_cases heq : r = e6HighestRootIdx
    · subst heq; exact hrI
    · exfalso
      have hst := posRaiseStep_spec r hpos heq
      have hb := (e6RootHeight_bounds (posRaiseStep r).2.1).2.2
      omega
  | succ n ih =>
    intro r hpos hle hrI
    by_cases heq : r = e6HighestRootIdx
    · subst heq; exact hrI
    · have hst := posRaiseStep_spec r hpos heq
      have hbr : ⁅e6SimpleE (posRaiseStep r).1, e6RootVec r⁆ ∈ I := I.lie_mem hrI
      rw [hst.1] at hbr
      have hnext : e6RootVec (posRaiseStep r).2.1 ∈ I := smul_unit_sign_mem hst.2.2 hbr
      have hb := (e6RootHeight_bounds (posRaiseStep r).2.1).2.2
      exact ih (posRaiseStep r).2.1 (by omega) (by omega) hnext

private theorem highest_mem_ideal_imp_pos_roots (I : LieIdeal ℝ h3zornCubicStabilizer)
    (hhi : e6RootVec e6HighestRootIdx ∈ I) :
    ∀ n : ℕ, ∀ r : Fin 72, 0 < e6RootHeight r → (11 - e6RootHeight r).toNat ≤ n →
      e6RootVec r ∈ I := by
  intro n
  induction n with
  | zero =>
    intro r hpos hle
    have h11 : e6RootHeight r = 11 := by
      have hb := (e6RootHeight_bounds r).2.2
      omega
    have hspec := posLowerStep_spec r hpos
    cases hst : posLowerStep r with
    | none => rw [hspec.1 hst]; exact hhi
    | some st =>
      exfalso
      have hlt := (hspec.2 st hst).2.1
      have hb := (e6RootHeight_bounds st.2.1).2.2
      omega
  | succ n ih =>
    intro r hpos hle
    have hspec := posLowerStep_spec r hpos
    cases hst : posLowerStep r with
    | none => rw [hspec.1 hst]; exact hhi
    | some st =>
      have hm := hspec.2 st hst
      have hb := (e6RootHeight_bounds st.2.1).2.2
      have hpar : e6RootVec st.2.1 ∈ I := ih st.2.1 hm.2.2.1 (by omega)
      have hbr : ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ ∈ I := I.lie_mem hpar
      rw [hm.1] at hbr
      exact smul_unit_sign_mem hm.2.2.2 hbr

private theorem highest_mem_ideal_imp_top (I : LieIdeal ℝ h3zornCubicStabilizer)
    (hhi : e6RootVec e6HighestRootIdx ∈ I) : I = ⊤ := by
  have hpos_all : ∀ r : Fin 72, 0 < e6RootHeight r → e6RootVec r ∈ I := by
    intro r hr
    exact highest_mem_ideal_imp_pos_roots I hhi 12 r hr (by
      have hb := (e6RootHeight_bounds r).2.1; omega)
  have he_mem : ∀ i : Fin 6, e6SimpleE i ∈ I := by
    intro i
    apply hpos_all (eSimpleIdx i)
    fin_cases i <;> decide
  have hh_mem : ∀ i : Fin 6, e6SimpleH i ∈ I := by
    intro i
    rw [← e6Simple_bracket_EF_same i, ← lie_skew]
    exact I.neg_mem (I.lie_mem (he_mem i))
  have hf_mem : ∀ i : Fin 6, e6SimpleF i ∈ I := by
    intro i
    have hbr : ⁅e6SimpleH i, e6SimpleF i⁆ ∈ I := by
      rw [← lie_skew]
      exact I.neg_mem (I.lie_mem (hh_mem i))
    rw [e6Simple_bracket_HF] at hbr
    have hc : Tag.cartan .E6 i i = 2 := by fin_cases i <;> decide
    rw [hc] at hbr
    have hsm := I.smul_mem (-2 : ℝ)⁻¹ hbr
    have h2 : (-((2 : ℤ) : ℝ)) = (-2 : ℝ) := by norm_num
    rw [h2, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at hsm
    exact hsm
  have hf_root_mem : ∀ i : Fin 6, e6RootVec (fSimpleIdx i) ∈ I := by
    intro i
    have hfi := hf_mem i
    change (fSimpleSign i : ℝ) • e6RootVec (fSimpleIdx i) ∈ I at hfi
    exact smul_unit_sign_mem (by fin_cases i <;> simp [fSimpleSign]) hfi
  have hneg_all : ∀ n : ℕ, ∀ r : Fin 72, e6RootHeight r < 0 →
      (e6RootHeight r).natAbs ≤ n → e6RootVec r ∈ I := by
    intro n
    induction n with
    | zero =>
      intro r hneg hle
      omega
    | succ n ih =>
      intro r hneg hle
      have hspec := negLowerStep_spec r hneg
      cases hst : negLowerStep r with
      | none =>
        obtain ⟨i, rfl⟩ := hspec.1 hst
        exact hf_root_mem i
      | some st =>
        have hm := hspec.2 st hst
        have hpar : e6RootVec st.2.1 ∈ I := ih st.2.1 hm.2.2.1 (by omega)
        have hbr : ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ ∈ I := I.lie_mem hpar
        rw [hm.1] at hbr
        exact smul_unit_sign_mem hm.2.2.2 hbr
  have hall_roots : ∀ r : Fin 72, e6RootVec r ∈ I := by
    intro r
    have hnz := (e6RootHeight_bounds r).1
    rcases lt_or_gt_of_ne hnz with hneg | hpos
    · exact hneg_all 12 r hneg (by have hb := (e6RootHeight_bounds r).2.1; omega)
    · exact hpos_all r hpos
  rw [eq_top_iff]
  intro x _
  have hrep := e6ChevalleyBasis.sum_repr x
  rw [← hrep, Fintype.sum_sum_type]
  refine I.add_mem (I.sum_mem fun i _ => I.smul_mem _ ?_)
    (I.sum_mem fun r _ => I.smul_mem _ ?_)
  · rw [e6ChevalleyBasis_inl]; exact hh_mem i
  · rw [e6ChevalleyBasis_inr]; exact hall_roots r

private theorem smul_unit_sign_mem_submodule
    {S : Submodule ℝ h3zornCubicStabilizer} {s : ℤ}
    (hs : s = 1 ∨ s = -1) {x : h3zornCubicStabilizer}
    (hx : (s : ℝ) • x ∈ S) : x ∈ S := by
  have hsne : (s : ℝ) ≠ 0 := by
    rcases hs with rfl | rfl <;> norm_num
  have hsm := S.smul_mem (s : ℝ)⁻¹ hx
  rw [smul_smul, inv_mul_cancel₀ hsne, one_smul] at hsm
  exact hsm

private theorem pos_root_mem_subalgebra_imp_highest
    (S : LieSubalgebra ℝ h3zornCubicStabilizer)
    (hE : ∀ i : Fin 6, e6SimpleE i ∈ S) :
    ∀ n : ℕ, ∀ r : Fin 72, 0 < e6RootHeight r →
      (11 - e6RootHeight r).toNat ≤ n → e6RootVec r ∈ S →
      e6RootVec e6HighestRootIdx ∈ S := by
  intro n
  induction n with
  | zero =>
      intro r hpos hle hrS
      have hhi : e6RootHeight r = 11 := by
        have hb := (e6RootHeight_bounds r).2.2
        omega
      by_cases heq : r = e6HighestRootIdx
      · simpa [heq] using hrS
      · have hst := posRaiseStep_spec r hpos heq
        have hb := (e6RootHeight_bounds (posRaiseStep r).2.1).2.2
        omega
  | succ n ih =>
      intro r hpos hle hrS
      by_cases heq : r = e6HighestRootIdx
      · simpa [heq] using hrS
      · have hst := posRaiseStep_spec r hpos heq
        have hbr : ⁅e6SimpleE (posRaiseStep r).1, e6RootVec r⁆ ∈ S :=
          S.lie_mem (hE _) hrS
        rw [hst.1] at hbr
        have hnext : e6RootVec (posRaiseStep r).2.1 ∈ S :=
          smul_unit_sign_mem_submodule hst.2.2 hbr
        have hb := (e6RootHeight_bounds (posRaiseStep r).2.1).2.2
        exact ih (posRaiseStep r).2.1 (by omega) (by omega) hnext

private theorem highest_mem_subalgebra_imp_pos_roots
    (S : LieSubalgebra ℝ h3zornCubicStabilizer)
    (hF : ∀ i : Fin 6, e6SimpleF i ∈ S)
    (hhi : e6RootVec e6HighestRootIdx ∈ S) :
    ∀ n : ℕ, ∀ r : Fin 72, 0 < e6RootHeight r →
      (11 - e6RootHeight r).toNat ≤ n → e6RootVec r ∈ S := by
  intro n
  induction n with
  | zero =>
      intro r hpos hle
      have h11 : e6RootHeight r = 11 := by
        have hb := (e6RootHeight_bounds r).2.2
        omega
      have hspec := posLowerStep_spec r hpos
      cases hst : posLowerStep r with
      | none => rw [hspec.1 hst]; exact hhi
      | some st =>
          exfalso
          have hlt := (hspec.2 st hst).2.1
          have hb := (e6RootHeight_bounds st.2.1).2.2
          omega
  | succ n ih =>
      intro r hpos hle
      have hspec := posLowerStep_spec r hpos
      cases hst : posLowerStep r with
      | none => rw [hspec.1 hst]; exact hhi
      | some st =>
          have hm := hspec.2 st hst
          have hb := (e6RootHeight_bounds st.2.1).2.2
          have hpar : e6RootVec st.2.1 ∈ S := ih st.2.1 hm.2.2.1 (by omega)
          have hbr : ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ ∈ S :=
            S.lie_mem (hF _) hpar
          rw [hm.1] at hbr
          exact smul_unit_sign_mem_submodule hm.2.2.2 hbr

/-- The six simple `E`, `F`, and `H` generators generate the full split Albert
`E₆` cubic-stabilizer Lie algebra. This is the finite root-chain bridge needed
to prove surjectivity of the Serre-presentation map. -/
theorem h3zornE6_simple_generators_generate
    (S : LieSubalgebra ℝ h3zornCubicStabilizer)
    (hH : ∀ i : Fin 6, e6SimpleH i ∈ S)
    (hE : ∀ i : Fin 6, e6SimpleE i ∈ S)
    (hF : ∀ i : Fin 6, e6SimpleF i ∈ S) : S = ⊤ := by
  have hhi : e6RootVec e6HighestRootIdx ∈ S :=
    pos_root_mem_subalgebra_imp_highest S hE 12 (eSimpleIdx 0)
      (by
        have hh : e6RootHeight (eSimpleIdx 0) = 1 := by decide
        omega) (by
        have hh : e6RootHeight (eSimpleIdx 0) = 1 := by decide
        omega) (hE 0)
  have hpos : ∀ r : Fin 72, 0 < e6RootHeight r → e6RootVec r ∈ S := by
    intro r hr
    exact highest_mem_subalgebra_imp_pos_roots S hF hhi 12 r hr (by
      have hb := (e6RootHeight_bounds r).2.1
      omega)
  have hfRoot : ∀ i : Fin 6, e6RootVec (fSimpleIdx i) ∈ S := by
    intro i
    have hsign : fSimpleSign i = 1 ∨ fSimpleSign i = -1 := by
      fin_cases i <;> simp [fSimpleSign]
    have hscaled : (fSimpleSign i : ℝ) • e6RootVec (fSimpleIdx i) ∈ S := by
      simpa [e6SimpleF] using hF i
    exact smul_unit_sign_mem_submodule hsign hscaled
  have hneg : ∀ n : ℕ, ∀ r : Fin 72, e6RootHeight r < 0 →
      (e6RootHeight r).natAbs ≤ n → e6RootVec r ∈ S := by
    intro n
    induction n with
    | zero =>
        intro r hneg hle
        omega
    | succ n ih =>
        intro r hneg hle
        have hspec := negLowerStep_spec r hneg
        cases hst : negLowerStep r with
        | none =>
            obtain ⟨i, rfl⟩ := hspec.1 hst
            exact hfRoot i
        | some st =>
            have hm := hspec.2 st hst
            have hpar : e6RootVec st.2.1 ∈ S := ih st.2.1 hm.2.2.1 (by omega)
            have hbr : ⁅e6SimpleF st.1, e6RootVec st.2.1⁆ ∈ S :=
              S.lie_mem (hF _) hpar
            rw [hm.1] at hbr
            exact smul_unit_sign_mem_submodule hm.2.2.2 hbr
  have hroots : ∀ r : Fin 72, e6RootVec r ∈ S := by
    intro r
    have hnz := (e6RootHeight_bounds r).1
    rcases lt_or_gt_of_ne hnz with hheightNeg | hheightPos
    · exact hneg 12 r hheightNeg (by
        have hb := (e6RootHeight_bounds r).2.1
        omega)
    · exact hpos r hheightPos
  rw [eq_top_iff]
  intro x _
  have hrep := e6ChevalleyBasis.sum_repr x
  rw [← hrep, Fintype.sum_sum_type]
  simp only [e6ChevalleyBasis_inl, e6ChevalleyBasis_inr]
  refine S.add_mem (S.sum_mem fun i _ => S.smul_mem _ (hH i))
    (S.sum_mem fun r _ => S.smul_mem _ (hroots r))



private theorem cartan_ne_zero_mem_ideal_imp_highest (I : LieIdeal ℝ h3zornCubicStabilizer)
    (h : h3zornCubicStabilizer) (hh : h ∈ h3zornCartan) (hne : h ≠ 0) (hI : h ∈ I) :
    e6RootVec e6HighestRootIdx ∈ I := by
  change h ∈ Submodule.span ℝ (Set.range e6SimpleH) at hh
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hh
  have ha_ne : ∃ j : Fin 6, ∑ i : Fin 6, a i * (Tag.cartan .E6 i j : ℝ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon 0; have h1 := hcon 1; have h2 := hcon 2
    have h3 := hcon 3; have h4 := hcon 4; have h5 := hcon 5
    have hcZ : ∀ i j : Fin 6, Tag.cartan .E6 i j =
        match i.val, j.val with
        | 0, 0 => 2 | 0, 2 => -1
        | 1, 1 => 2 | 1, 3 => -1
        | 2, 0 => -1 | 2, 2 => 2 | 2, 3 => -1
        | 3, 1 => -1 | 3, 2 => -1 | 3, 3 => 2 | 3, 4 => -1
        | 4, 3 => -1 | 4, 4 => 2 | 4, 5 => -1
        | 5, 4 => -1 | 5, 5 => 2
        | _, _ => 0 := by
      intro i j; fin_cases i <;> fin_cases j <;> decide
    simp only [Fin.sum_univ_six, hcZ] at h0 h1 h2 h3 h4 h5
    norm_num [Fin.val] at h0 h1 h2 h3 h4 h5
    have ha0 : a 0 = 0 := by linarith
    have ha1 : a 1 = 0 := by linarith
    have ha2 : a 2 = 0 := by linarith
    have ha3 : a 3 = 0 := by linarith
    have ha4 : a 4 = 0 := by linarith
    have ha5 : a 5 = 0 := by linarith
    exact hne (Finset.sum_eq_zero fun i _ => by fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4, ha5])
  obtain ⟨j, hj⟩ := ha_ne
  have hbr : ⁅∑ i : Fin 6, a i • e6SimpleH i, e6SimpleE j⁆ ∈ I := by
    rw [← lie_skew]
    exact I.neg_mem (I.lie_mem hI)
  have heq : ⁅∑ i : Fin 6, a i • e6SimpleH i, e6SimpleE j⁆ =
      (∑ i : Fin 6, a i * (Tag.cartan .E6 i j : ℝ)) • e6SimpleE j := by
    rw [sum_lie]
    simp only [smul_lie, e6Simple_bracket_HE, smul_smul, Finset.sum_smul]
  rw [heq] at hbr
  have hej : e6SimpleE j ∈ I := by
    have hs := I.smul_mem (∑ i : Fin 6, a i * (Tag.cartan .E6 i j : ℝ))⁻¹ hbr
    rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hs
    exact hs
  exact pos_root_mem_ideal_imp_highest I 12 (eSimpleIdx j)
    (by fin_cases j <;> decide)
    (by have hh : e6RootHeight (eSimpleIdx j) = 1 := by fin_cases j <;> decide
        omega)
    hej

private theorem neg_root_mem_ideal_imp_highest (I : LieIdeal ℝ h3zornCubicStabilizer) :
    ∀ n : ℕ, ∀ r : Fin 72, e6RootHeight r < 0 → (e6RootHeight r).natAbs ≤ n →
      e6RootVec r ∈ I → e6RootVec e6HighestRootIdx ∈ I := by
  intro n
  induction n with
  | zero =>
    intro r hneg hle
    omega
  | succ n ih =>
    intro r hneg hle hrI
    by_cases h1 : e6RootHeight r = -1
    · obtain ⟨i, rfl⟩ := negHeight_negOne_eq_fSimple r h1
      have hfi : e6SimpleF i ∈ I := I.smul_mem (fSimpleSign i : ℝ) hrI
      have hhi : e6SimpleH i ∈ I := by
        rw [← e6Simple_bracket_EF_same i]
        exact I.lie_mem hfi
      have hne : e6SimpleH i ≠ 0 := by
        intro h0
        have := Fintype.linearIndependent_iff.mp e6SimpleH_linearIndependent
          (fun j => if j = i then 1 else 0)
          (by simp [h0]) i
        norm_num at this
      exact cartan_ne_zero_mem_ideal_imp_highest I (e6SimpleH i) (e6SimpleH_mem_h3zornCartan i)
        hne hhi
    · have hlt : e6RootHeight r < -1 := by omega
      have hst := negRaiseStep_spec r hlt
      have hbr : ⁅e6SimpleE (negRaiseStep r).1, e6RootVec r⁆ ∈ I := I.lie_mem hrI
      rw [hst.1] at hbr
      have hnext : e6RootVec (negRaiseStep r).2.1 ∈ I := smul_unit_sign_mem hst.2.2.2 hbr
      exact ih (negRaiseStep r).2.1 hst.2.2.1 (by omega) hnext

theorem e6RootVec_mem_ideal_imp_highest (I : LieIdeal ℝ h3zornCubicStabilizer)
    (r : Fin 72) (hr : e6RootVec r ∈ I) : e6RootVec e6HighestRootIdx ∈ I := by
  have hnz := (e6RootHeight_bounds r).1
  rcases lt_or_gt_of_ne hnz with hneg | hpos
  · exact neg_root_mem_ideal_imp_highest I 12 r hneg
      (by have hb := (e6RootHeight_bounds r).2.1; omega) hr
  · exact pos_root_mem_ideal_imp_highest I 12 r hpos
      (by have hb := (e6RootHeight_bounds r).2.1; omega) hr

/-- **Unconditional Simplicity of Split `𝔢₆(6)`**:
`h3zornCubicStabilizer` is a simple 78-dimensional real Lie algebra. -/
instance h3zornCubicStabilizer_isSimple : LieAlgebra.IsSimple ℝ h3zornCubicStabilizer where
  eq_bot_or_eq_top I := by
    by_cases hbot : I = ⊥
    · exact Or.inl hbot
    · right
      have hne : ∃ x ∈ I, x ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        exact hall x hx
      obtain ⟨x, hxI, hxne⟩ := hne
      have hrep := e6ChevalleyBasis.sum_repr x
      rw [Fintype.sum_sum_type] at hrep
      simp only [e6ChevalleyBasis_inl, e6ChevalleyBasis_inr] at hrep
      have hhpart : (∑ i : Fin 6, e6ChevalleyBasis.repr x (Sum.inl i) • e6SimpleH i) ∈
          h3zornCartan :=
        Submodule.sum_mem _ fun i _ => h3zornCartan.smul_mem _ (e6SimpleH_mem_h3zornCartan i)
      have hkill := cartan_weight_kill_mem I.toSubmodule (fun i y hy => I.lie_mem hy)
        Finset.univ (∑ i : Fin 6, e6ChevalleyBasis.repr x (Sum.inl i) • e6SimpleH i) hhpart
        (fun r => e6ChevalleyBasis.repr x (Sum.inr r)) (by rw [hrep]; exact hxI)
      by_cases hhp0 : (∑ i : Fin 6, e6ChevalleyBasis.repr x (Sum.inl i) • e6SimpleH i) = 0
      · have hex : ∃ r : Fin 72, e6ChevalleyBasis.repr x (Sum.inr r) ≠ 0 := by
          by_contra hall
          push Not at hall
          have hs0 : (∑ r : Fin 72, e6ChevalleyBasis.repr x (Sum.inr r) • e6RootVec r) = 0 :=
            Finset.sum_eq_zero fun r _ => by rw [hall r, zero_smul]
          apply hxne
          rw [← hrep, hhp0, hs0, add_zero]
        obtain ⟨r, hr⟩ := hex
        have hrI : e6RootVec r ∈ I := by
          have hs := I.smul_mem (e6ChevalleyBasis.repr x (Sum.inr r))⁻¹
            (hkill.2 r (Finset.mem_univ r))
          rw [smul_smul, inv_mul_cancel₀ hr, one_smul] at hs
          exact hs
        exact highest_mem_ideal_imp_top I (e6RootVec_mem_ideal_imp_highest I r hrI)
      · exact highest_mem_ideal_imp_top I
          (cartan_ne_zero_mem_ideal_imp_highest I
            (∑ i : Fin 6, e6ChevalleyBasis.repr x (Sum.inl i) • e6SimpleH i) hhpart hhp0 hkill.1)
  non_abelian := by
    intro hab
    have h0 := hab.trivial (e6SimpleH 0) (e6SimpleE 0)
    rw [e6Simple_bracket_HE] at h0
    have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
    rw [hc] at h0
    have hne := e6RootVec_ne_zero (eSimpleIdx 0)
    change ((2 : ℤ) : ℝ) • e6RootVec (eSimpleIdx 0) = 0 at h0
    have hsm := smul_eq_zero.mp h0
    norm_num at hsm
    exact hne hsm

instance h3zornCubicStabilizer_isSemisimple : LieAlgebra.IsSemisimple ℝ h3zornCubicStabilizer :=
  inferInstance

instance h3zornCubicStabilizer_hasTrivialRadical :
    LieAlgebra.HasTrivialRadical ℝ h3zornCubicStabilizer :=
  inferInstance

theorem center_h3zornCubicStabilizer_eq_bot :
    LieAlgebra.center ℝ h3zornCubicStabilizer = ⊥ :=
  le_antisymm (LieAlgebra.center_le_radical _ _ |>.trans (by simp)) bot_le

end SimplicityProof

end InfoGeometry.Algebra
