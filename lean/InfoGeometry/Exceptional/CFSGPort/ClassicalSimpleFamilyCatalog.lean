/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.SimpleFamilyCatalog
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Classical

open Matrix

theorem specialLinear_eq_detKer (n : ℕ) (K : Type) [Field K] :
    SpecialLinear n K = (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  have hset : {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1} =
      ((Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker : Set (GL (Fin n) K)) := by
    ext A
    simp [Units.ext_iff]
  rw [SpecialLinear, hset, Subgroup.closure_eq]

theorem specialLinear_eq_range_toGL (n : ℕ) (K : Type) [Field K] :
    SpecialLinear n K = (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
  rw [specialLinear_eq_detKer, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

noncomputable def specialLinearGroupEquiv (n : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K ≃* SpecialLinear n K :=
  (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (specialLinear_eq_range_toGL n K).symm)

theorem specialLinearGroupEquiv_coe (n : ℕ) (K : Type) [Field K]
    (A : Matrix.SpecialLinearGroup (Fin n) K) :
    ((specialLinearGroupEquiv n K A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A := by
  simp [specialLinearGroupEquiv, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

theorem map_center_eq_scalars (n : ℕ) (K : Type) [Field K] :
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)).map
        (specialLinearGroupEquiv n K : Matrix.SpecialLinearGroup (Fin n) K →*
          SpecialLinear n K) =
      (Scalars (Fin n) K).subgroupOf (SpecialLinear n K) := by
  ext x
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquiv n K).surjective x
  have key : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) ↔
      specialLinearGroupEquiv n K A ∈ (Scalars (Fin n) K).subgroupOf (SpecialLinear n K) := by
    rw [Subgroup.mem_subgroupOf, Matrix.SpecialLinearGroup.mem_center_iff, Scalars,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨r, hr, hA⟩
      rcases isEmpty_or_nonempty (Fin n) with hn | hn
      · have := hn
        exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [Fintype.card_fin, zero_pow (Fin.pos_iff_nonempty.mpr hn).ne'] at hr
        exact zero_ne_one hr
      refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, specialLinearGroupEquiv_coe, ← hA]
      rfl
    · rintro ⟨c, hc⟩
      have hmat : (A : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
        rw [← specialLinearGroupEquiv_coe, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
      refine ⟨c, ?_, hmat.symm⟩
      have hdet := A.prop
      rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
        Finset.card_univ] at hdet
      exact hdet
  rw [← key, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    rwa [(specialLinearGroupEquiv n K).injective hBA] at hB
  · intro h
    exact ⟨A, h, rfl⟩

noncomputable def projectiveSpecialLinearGroupEquiv (n : ℕ) (K : Type) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* Projective (SpecialLinear n K) :=
  QuotientGroup.congr _ _ (specialLinearGroupEquiv n K) (map_center_eq_scalars n K)

theorem projectiveSpecialLinearTwo_isSimple (K : Type) [Field K]
    [Finite K] (hK : 4 ≤ Nat.card K) : IsSimpleGroup (Projective (SpecialLinear 2 K)) := by
  exact (projectiveSpecialLinearGroupEquiv 2 K).isSimpleGroup_congr.mp
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK)

theorem pslTwoModel_fieldCard_ge_four {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f)
    (h22 : (2, p ^ f) ≠ (2, 2)) (h23 : (2, p ^ f) ≠ (2, 3)) :
    4 ≤ p ^ f := by
  rcases hp.eq_two_or_odd' with hp2 | hpOdd
  · subst p
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have hf1 : f = 1 := by omega
      subst f
      apply h22
      simp
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hf2
  · have hp3 : 3 ≤ p := hp.odd_iff.mp hpOdd
    have hle : p ≤ p ^ f := by
      cases f with
      | zero => omega
      | succ f =>
        rw [pow_succ]
        nlinarith [Nat.one_le_pow f p (by omega)]
    have hne : p ^ f ≠ 3 := by
      intro h
      apply h23
      simp [h]
    omega

theorem isSimpleGroup_of_PSL2Model {G : Type} [Group G] {p f : ℕ}
    (h : Model G .PSL 2 p f) : IsSimpleGroup G := by
  obtain ⟨⟨hp, hf, -, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hfield : 4 ≤ Nat.card K := by
    rw [hK]
    exact pslTwoModel_fieldCard_ge_four hp hf h22 h23
  exact e.isSimpleGroup_congr.mpr (projectiveSpecialLinearTwo_isSimple K hfield)

end InfoGeometry.Exceptional.CFSGPort.Classical

end
