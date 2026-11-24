/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CartanTriality
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic

/-!
# Faithful native S₃ representation by the Cartan triality matrices

The matrix identities are assembled into a homomorphism from Mathlib's
`DihedralGroup 3`, with faithfulness proved on the six distinct matrices.
An explicit group equivalence with `Equiv.Perm (Fin 3)` gives a native S₃
representation on the full four-dimensional real vector space.

This is a linear representation. Extending it to outer automorphisms of a
particular Lie group requires an additional integration/identification theorem.
-/

set_option autoImplicit false
noncomputable section
open BigOperators Matrix

namespace InfoGeometry.Lie.CartanTriality

open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

/-- Six matrices in the normal form `C^i` or `S C^i`. -/
def dihedralMatrix : DihedralGroup 3 → Matrix (Fin 4) (Fin 4) ℝ
  | .r i => cyclicTriality ^ i.val
  | .sr i => conjugationReflection * cyclicTriality ^ i.val

/-- The six concrete matrices respect the native dihedral multiplication. -/
theorem dihedralMatrix_mul (a b : DihedralGroup 3) :
    dihedralMatrix (a * b) = dihedralMatrix a * dihedralMatrix b := by
  have hrot (i j : ZMod 3) :
      cyclicTriality ^ (i + j).val = cyclicTriality ^ i.val * cyclicTriality ^ j.val := by
    rw [ZMod.val_add, ← pow_add]
    simpa only [cyclicTriality_order] using
      (pow_mod_orderOf cyclicTriality (i.val + j.val))
  have hCS : cyclicTriality * conjugationReflection =
      conjugationReflection * cyclicTriality ^ 2 := by
    calc
      cyclicTriality * conjugationReflection =
          (conjugationReflection * conjugationReflection) *
            (cyclicTriality * conjugationReflection) := by
              rw [conjugationReflection_sq, one_mul]
      _ = conjugationReflection *
          (conjugationReflection * cyclicTriality * conjugationReflection) := by
            simp only [mul_assoc]
      _ = conjugationReflection * cyclicTriality ^ 2 := by rw [reflection_conj_cycle]
  have hSC : conjugationReflection * cyclicTriality =
      cyclicTriality ^ 2 * conjugationReflection := by
    calc
      conjugationReflection * cyclicTriality =
          (conjugationReflection * cyclicTriality) *
            (conjugationReflection * conjugationReflection) := by
              rw [conjugationReflection_sq, mul_one]
      _ = (conjugationReflection * cyclicTriality * conjugationReflection) *
          conjugationReflection := by simp only [mul_assoc]
      _ = cyclicTriality ^ 2 * conjugationReflection := by rw [reflection_conj_cycle]
  have hconj (i : ZMod 3) : cyclicTriality ^ i.val * conjugationReflection =
      conjugationReflection * cyclicTriality ^ (-i).val := by
    rw [ZMod.neg_val']
    fin_cases i
    · change cyclicTriality ^ 0 * conjugationReflection =
        conjugationReflection * cyclicTriality ^ 0
      simp only [pow_zero, one_mul, mul_one]
    · change cyclicTriality ^ 1 * conjugationReflection =
        conjugationReflection * cyclicTriality ^ 2
      simpa only [pow_one] using hCS
    · change cyclicTriality ^ 2 * conjugationReflection =
        conjugationReflection * cyclicTriality ^ 1
      simpa only [pow_one] using hSC.symm
  have hsub (i j : ZMod 3) : cyclicTriality ^ (j - i).val =
      cyclicTriality ^ (-i).val * cyclicTriality ^ j.val := by
    rw [sub_eq_add_neg, add_comm j (-i)]
    exact hrot (-i) j
  cases a with
  | r i =>
    cases b with
    | r j =>
      change cyclicTriality ^ (i + j).val =
        cyclicTriality ^ i.val * cyclicTriality ^ j.val
      exact hrot i j
    | sr j =>
      change conjugationReflection * cyclicTriality ^ (j - i).val =
        cyclicTriality ^ i.val * (conjugationReflection * cyclicTriality ^ j.val)
      symm
      calc
        cyclicTriality ^ i.val * (conjugationReflection * cyclicTriality ^ j.val) =
            (cyclicTriality ^ i.val * conjugationReflection) * cyclicTriality ^ j.val :=
              (mul_assoc _ _ _).symm
        _ = (conjugationReflection * cyclicTriality ^ (-i).val) * cyclicTriality ^ j.val := by
          rw [hconj i]
        _ = conjugationReflection *
            (cyclicTriality ^ (-i).val * cyclicTriality ^ j.val) := mul_assoc _ _ _
        _ = conjugationReflection * cyclicTriality ^ (j - i).val := by rw [← hsub i j]
  | sr i =>
    cases b with
    | r j =>
      change conjugationReflection * cyclicTriality ^ (i + j).val =
        (conjugationReflection * cyclicTriality ^ i.val) * cyclicTriality ^ j.val
      rw [hrot i j, mul_assoc]
    | sr j =>
      change cyclicTriality ^ (j - i).val =
        (conjugationReflection * cyclicTriality ^ i.val) *
          (conjugationReflection * cyclicTriality ^ j.val)
      symm
      calc
        (conjugationReflection * cyclicTriality ^ i.val) *
            (conjugationReflection * cyclicTriality ^ j.val) =
            conjugationReflection *
              ((cyclicTriality ^ i.val * conjugationReflection) * cyclicTriality ^ j.val) := by
                simp only [mul_assoc]
        _ = conjugationReflection *
            ((conjugationReflection * cyclicTriality ^ (-i).val) * cyclicTriality ^ j.val) := by
              rw [hconj i]
        _ = (conjugationReflection * conjugationReflection) *
            (cyclicTriality ^ (-i).val * cyclicTriality ^ j.val) := by simp only [mul_assoc]
        _ = cyclicTriality ^ (-i).val * cyclicTriality ^ j.val := by
          rw [conjugationReflection_sq, one_mul]
        _ = cyclicTriality ^ (j - i).val := (hsub i j).symm

/-- The full matrix representation, bundled as a native monoid homomorphism. -/
def dihedralMatrixHom : DihedralGroup 3 →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun := dihedralMatrix
  map_one' := by change cyclicTriality ^ (0 : ZMod 3).val = 1; simp
  map_mul' := dihedralMatrix_mul

set_option maxHeartbeats 1000000 in
/-- Two entries suffice to distinguish all six matrices. -/
theorem dihedralMatrixHom_injective : Function.Injective dihedralMatrixHom := by
  intro a b h
  cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | exfalso
      norm_num [dihedralMatrixHom, dihedralMatrix, ZMod.val] at h
      have h0 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
      have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
      norm_num [cyclicTriality, conjugationReflection, trialitySwapVS, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_four] at h0 <;>
        norm_num [cyclicTriality, conjugationReflection, trialitySwapVS, pow_succ,
          Matrix.mul_apply, Fin.sum_univ_four] at h1

/-- Conversion through native matrix units and the general linear group. -/
def dihedralLinearAction :
    DihedralGroup 3 →* ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Fin 4 → ℝ)).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 4) (R := ℝ)).toMonoidHom.comp
      dihedralMatrixHom.toHomUnits)

@[simp] theorem dihedralLinearAction_apply (g : DihedralGroup 3) (v : Fin 4 → ℝ) :
    dihedralLinearAction g v = (dihedralMatrixHom g).mulVec v := rfl

theorem dihedralLinearAction_injective : Function.Injective dihedralLinearAction := by
  intro a b h
  apply dihedralMatrixHom_injective
  apply Matrix.toLin'.injective
  exact congrArg LinearEquiv.toLinearMap h

/-- Three-cycle on the three labels. -/
def labelCycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- Reflection of the three labels. -/
def labelReflection : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Dihedral normal forms acting on three labels. -/
def dihedralPermutation : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | .r i => labelCycle ^ i.val
  | .sr i => labelReflection * labelCycle ^ i.val

/-- The native dihedral group acts on three labels. -/
def dihedralPermutationHom : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun := dihedralPermutation
  map_one' := rfl
  map_mul' := by
    intro a b
    cases a with
    | r i =>
      cases b with
      | r j =>
        rw [DihedralGroup.r_mul_r]
        fin_cases i <;> fin_cases j <;> decide
      | sr j =>
        rw [DihedralGroup.r_mul_sr]
        fin_cases i <;> fin_cases j <;> decide
    | sr i =>
      cases b with
      | r j =>
        rw [DihedralGroup.sr_mul_r]
        fin_cases i <;> fin_cases j <;> decide
      | sr j =>
        rw [DihedralGroup.sr_mul_sr]
        fin_cases i <;> fin_cases j <;> decide

theorem dihedralPermutationHom_injective : Function.Injective dihedralPermutationHom := by
  decide

theorem dihedralPermutationHom_bijective : Function.Bijective dihedralPermutationHom := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact dihedralPermutationHom_injective
  · norm_num [DihedralGroup.card, Fintype.card_perm]

/-- An actual group equivalence with the symmetric group on three elements. -/
def dihedralPermutationEquiv : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective dihedralPermutationHom dihedralPermutationHom_bijective

/-- A faithful native S₃ linear representation on the requested four-dimensional space. -/
def s3LinearAction : Equiv.Perm (Fin 3) →* ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) :=
  dihedralLinearAction.comp dihedralPermutationEquiv.symm.toMonoidHom

theorem s3LinearAction_injective : Function.Injective s3LinearAction :=
  dihedralLinearAction_injective.comp dihedralPermutationEquiv.symm.injective

@[simp] theorem dihedralMatrix_rotation :
    dihedralMatrixHom (.r 1) = cyclicTriality := by
  change cyclicTriality ^ 1 = cyclicTriality
  exact pow_one _

@[simp] theorem dihedralMatrix_reflection :
    dihedralMatrixHom (.sr 0) = conjugationReflection := by
  simp [dihedralMatrixHom, dihedralMatrix]

theorem dihedralMatrix_hadamard : dihedralMatrixHom (.sr 2) = trialitySwapVS := by
  change conjugationReflection * cyclicTriality ^ 2 = trialitySwapVS
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicTriality, conjugationReflection, trialitySwapVS,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_four]

/-- The generator-fixed plane is the fixed space of the entire faithful representation. -/
theorem fixed_by_dihedral_iff (v : Fin 4 → ℝ) :
    (∀ g : DihedralGroup 3, dihedralLinearAction g v = v) ↔ v ∈ fixedCartan := by
  constructor
  · intro h
    change trialitySwapVS.mulVec v = v ∧ conjugationReflection.mulVec v = v
    constructor
    · simpa only [dihedralLinearAction_apply, dihedralMatrix_hadamard] using h (.sr 2)
    · simpa only [dihedralLinearAction_apply, dihedralMatrix_reflection] using h (.sr 0)
  · intro hv g
    rcases hv with ⟨hH, hS⟩
    have hC : cyclicTriality.mulVec v = v := by
      simp [cyclicTriality, ← Matrix.mulVec_mulVec, hH, hS]
    cases g with
    | r i =>
      fin_cases i <;>
        simp [dihedralLinearAction_apply, dihedralMatrixHom, dihedralMatrix, ZMod.val, pow_two,
          ← Matrix.mulVec_mulVec, hC]
    | sr i =>
      fin_cases i <;>
        simp [dihedralLinearAction_apply, dihedralMatrixHom, dihedralMatrix, ZMod.val, pow_two,
          ← Matrix.mulVec_mulVec, hC, hS]

/-- The fixed space is unchanged after expressing the action as native S₃. -/
theorem fixed_by_s3_iff (v : Fin 4 → ℝ) :
    (∀ s : Equiv.Perm (Fin 3), s3LinearAction s v = v) ↔ v ∈ fixedCartan := by
  rw [← fixed_by_dihedral_iff]
  constructor
  · intro h g
    simpa [s3LinearAction] using h (dihedralPermutationEquiv g)
  · intro h s
    exact h (dihedralPermutationEquiv.symm s)

end InfoGeometry.Lie.CartanTriality
