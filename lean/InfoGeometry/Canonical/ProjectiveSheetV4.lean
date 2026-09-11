import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

open scoped Matrix

namespace InfoGeometry.Canonical.ProjectiveSheetV4

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev Mat23C := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def liftedJ : Mat23C := Matrix.kronecker sheetExchange (1 : Mat3C)
def liftedGamma : Mat23C := Matrix.kronecker sheetParity (1 : Mat3C)

theorem sheet_reflection_anticommutes_with_parity :
    sheetExchange * sheetParity = -(sheetParity * sheetExchange) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, sheetParity, uPlus, uMinus, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem liftedJ_sq : liftedJ ^ 2 = 1 := by
  calc
    liftedJ ^ 2 =
        Matrix.kronecker (sheetExchange * sheetExchange) ((1 : Mat3C) * 1) := by
          simpa [liftedJ, pow_two] using kronecker_mul sheetExchange sheetExchange
            (1 : Mat3C) 1
    _ = 1 := by rw [sheetExchange_sq]; simp

theorem liftedGamma_sq : liftedGamma ^ 2 = 1 := by
  calc
    liftedGamma ^ 2 =
        Matrix.kronecker (sheetParity * sheetParity) ((1 : Mat3C) * 1) := by
          simpa [liftedGamma, pow_two] using kronecker_mul sheetParity sheetParity
            (1 : Mat3C) 1
    _ = 1 := by rw [sheetParity_sq]; simp

theorem liftedJ_liftedGamma_anticommute :
    liftedJ * liftedGamma = -(liftedGamma * liftedJ) := by
  calc
    liftedJ * liftedGamma =
        Matrix.kronecker (sheetExchange * sheetParity) ((1 : Mat3C) * 1) := by
          simpa [liftedJ, liftedGamma] using
            (kronecker_mul sheetExchange sheetParity (1 : Mat3C) 1)
    _ = -(Matrix.kronecker (sheetParity * sheetExchange) ((1 : Mat3C) * 1)) := by
          rw [sheet_reflection_anticommutes_with_parity]
          simpa using
            (Matrix.smul_kronecker (-1 : ℂ) (sheetParity * sheetExchange)
              (1 : Mat3C))
    _ = -(liftedGamma * liftedJ) := by
          congr 1
          symm
          exact kronecker_mul sheetParity sheetExchange (1 : Mat3C) 1

theorem liftedJGamma_sq : (liftedJ * liftedGamma) ^ 2 = -(1 : Mat23C) := by
  calc
    (liftedJ * liftedGamma) ^ 2 =
        liftedJ * liftedGamma * liftedJ * liftedGamma := by
          simp [pow_two, Matrix.mul_assoc]
    _ = -(liftedJ * liftedJ) * (liftedGamma * liftedGamma) := by
          have h : liftedGamma * liftedJ = -(liftedJ * liftedGamma) := by
            calc
              liftedGamma * liftedJ = -(-(liftedGamma * liftedJ)) := by simp
              _ = -(liftedJ * liftedGamma) := by
                rw [liftedJ_liftedGamma_anticommute]
          calc
            liftedJ * liftedGamma * liftedJ * liftedGamma =
                liftedJ * (liftedGamma * liftedJ) * liftedGamma := by
                  simp [Matrix.mul_assoc]
            _ = liftedJ * (-(liftedJ * liftedGamma)) * liftedGamma := by rw [h]
            _ = -(liftedJ * liftedJ) * (liftedGamma * liftedGamma) := by
                  simp [Matrix.mul_assoc]
    _ = -1 := by
          rw [show liftedJ * liftedJ = 1 by simpa [pow_two] using liftedJ_sq,
            show liftedGamma * liftedGamma = 1 by
              simpa [pow_two] using liftedGamma_sq]
          simp

theorem scalar_sign_central (M : Mat23C) (ε : ℂ) :
    (ε • (1 : Mat23C)) * M = M * (ε • (1 : Mat23C)) := by
  simp [Matrix.smul_mul, Matrix.mul_smul]

theorem projective_sheet_packet_relations :
    liftedJ ^ 2 = 1 ∧
      liftedGamma ^ 2 = 1 ∧
      liftedJ * liftedGamma = -(liftedGamma * liftedJ) ∧
      (liftedJ * liftedGamma) ^ 2 = -(1 : Mat23C) := by
  exact ⟨liftedJ_sq, liftedGamma_sq, liftedJ_liftedGamma_anticommute,
    liftedJGamma_sq⟩

def rotationParity : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num) (ZMod 2)

def projectivize : DihedralGroup 4 →* DihedralGroup 2 where
  toFun
    | DihedralGroup.r i => DihedralGroup.r (rotationParity i)
    | DihedralGroup.sr i => DihedralGroup.sr (rotationParity i)
  map_one' := by
    change DihedralGroup.r (rotationParity 0) = DihedralGroup.r 0
    rw [map_zero]
  map_mul' := by
    intro a b
    cases a <;> cases b <;>
      simp [rotationParity, map_add, map_sub]

theorem projectivize_surjective : Function.Surjective projectivize := by
  intro g
  cases g with
  | r i =>
      obtain ⟨j, hj⟩ :=
        ZMod.castHom_surjective (n := 4) (m := 2) (by norm_num) i
      refine ⟨DihedralGroup.r j, ?_⟩
      change DihedralGroup.r (rotationParity j) = DihedralGroup.r i
      rw [show rotationParity j = i from hj]
  | sr i =>
      obtain ⟨j, hj⟩ :=
        ZMod.castHom_surjective (n := 4) (m := 2) (by norm_num) i
      refine ⟨DihedralGroup.sr j, ?_⟩
      change DihedralGroup.sr (rotationParity j) = DihedralGroup.sr i
      rw [show rotationParity j = i from hj]

theorem projectivize_mem_ker_iff (g : DihedralGroup 4) :
    g ∈ projectivize.ker ↔
      g = DihedralGroup.r 0 ∨ g = DihedralGroup.r 2 := by
  cases g with
  | r i =>
      change DihedralGroup.r (rotationParity i) = DihedralGroup.r 0 ↔
        DihedralGroup.r i = DihedralGroup.r 0 ∨
          DihedralGroup.r i = DihedralGroup.r 2
      fin_cases i <;> decide
  | sr i =>
      change DihedralGroup.sr (rotationParity i) = DihedralGroup.r 0 ↔
        DihedralGroup.sr i = DihedralGroup.r 0 ∨
          DihedralGroup.sr i = DihedralGroup.r 2
      fin_cases i <;> decide

theorem centralSign_mem_projectivize_ker :
    DihedralGroup.r 2 ∈ projectivize.ker := by
  rw [projectivize_mem_ker_iff]
  exact Or.inr rfl

theorem projectivize_ker_eq_centralSign :
    projectivize.ker = Subgroup.closure ({DihedralGroup.r 2} : Set (DihedralGroup 4)) := by
  apply le_antisymm
  · intro g hg
    rw [projectivize_mem_ker_iff] at hg
    rcases hg with rfl | rfl
    · simpa using
        (Subgroup.one_mem (Subgroup.closure ({DihedralGroup.r 2} : Set (DihedralGroup 4))))
    · exact Subgroup.subset_closure (by simp)
  · refine (Subgroup.closure_le projectivize.ker).2 ?_
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact centralSign_mem_projectivize_ker

theorem projectivize_kernel_card : Nat.card projectivize.ker = 2 := by
  have hrange : projectivize.range = ⊤ :=
    MonoidHom.range_eq_top.mpr projectivize_surjective
  have hindex : projectivize.ker.index = 4 := by
    rw [Subgroup.index_ker, hrange]
    simp [DihedralGroup.nat_card]
  have hcard := projectivize.ker.card_mul_index
  rw [hindex, DihedralGroup.nat_card] at hcard
  norm_num at hcard ⊢
  omega

noncomputable def projectivize_quotient_equiv :
    (DihedralGroup 4 ⧸ projectivize.ker) ≃* DihedralGroup 2 :=
  QuotientGroup.quotientKerEquivOfSurjective projectivize projectivize_surjective

theorem projectivize_quotient_equiv_apply (g : DihedralGroup 4) :
    projectivize_quotient_equiv (QuotientGroup.mk g) = projectivize g := by
  rfl

end InfoGeometry.Canonical.ProjectiveSheetV4
