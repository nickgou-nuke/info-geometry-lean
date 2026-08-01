import InfoGeometry.Algebra.H3ZornTopologicalReadout
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` action morphisms for the finite `S₃` permutation layer

The algebraic carrier and its finite permutation maps are owned by
`F4Derivations`.  This file only packages their already-proved continuity as
`TopCat` morphisms and transports the existing composition closure.  No Jordan
product preservation is assumed.
-/

noncomputable section

namespace InfoGeometry.Algebra

open CategoryTheory

theorem continuous_S3OnH3Zorn_joint :
    Continuous (fun p : S3Perm × H3Zorn ℝ =>
      S3OnH3Zorn p.1 p.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro σ
  simpa using continuous_S3OnH3Zorn σ

def S3OnH3ZornJointTopCat :
    TopCat.of (S3Perm × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p => S3OnH3Zorn p.1 p.2
      continuous_toFun := continuous_S3OnH3Zorn_joint }

@[simp] theorem S3OnH3ZornJointTopCat_apply (p : S3Perm × H3Zorn ℝ) :
    S3OnH3ZornJointTopCat p = S3OnH3Zorn p.1 p.2 :=
  rfl

theorem continuous_S3OnH3Zorn_joint_inverse :
    Continuous (fun p : S3Perm × H3Zorn ℝ =>
      S3OnH3Zorn (S3Perm.inverse p.1) p.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro σ
  simpa using continuous_S3OnH3Zorn (S3Perm.inverse σ)

noncomputable def S3OnH3ZornJointProductHomeomorph :
    (S3Perm × H3Zorn ℝ) ≃ₜ (S3Perm × H3Zorn ℝ) where
  toEquiv :=
    { toFun := fun p => (p.1, S3OnH3Zorn p.1 p.2)
      invFun := fun p =>
        (p.1, S3OnH3Zorn (S3Perm.inverse p.1) p.2)
      left_inv := by
        rintro ⟨σ, X⟩
        simp [S3OnH3Zorn_inverse_left]
      right_inv := by
        rintro ⟨σ, X⟩
        simp [S3OnH3Zorn_inverse_right] }
  continuous_toFun :=
    continuous_fst.prodMk continuous_S3OnH3Zorn_joint
  continuous_invFun :=
    continuous_fst.prodMk continuous_S3OnH3Zorn_joint_inverse

def S3OnH3ZornJointProductTopCatIso :
    TopCat.of (S3Perm × H3Zorn ℝ) ≅ TopCat.of (S3Perm × H3Zorn ℝ) :=
  TopCat.isoOfHomeo S3OnH3ZornJointProductHomeomorph

@[simp] theorem S3OnH3ZornJointProductTopCatIso_hom_apply
    (p : S3Perm × H3Zorn ℝ) :
    S3OnH3ZornJointProductTopCatIso.hom p =
      (p.1, S3OnH3Zorn p.1 p.2) :=
  rfl

@[simp] theorem S3OnH3ZornJointProductTopCatIso_inv_apply
    (p : S3Perm × H3Zorn ℝ) :
    S3OnH3ZornJointProductTopCatIso.inv p =
      (p.1, S3OnH3Zorn (S3Perm.inverse p.1) p.2) :=
  rfl

def S3OnH3ZornJointProductFstTopCat :
    TopCat.of (S3Perm × H3Zorn ℝ) ⟶ TopCat.of S3Perm :=
  TopCat.ofHom
    { toFun := fun p : S3Perm × H3Zorn ℝ => p.1
      continuous_toFun := continuous_fst }

def S3OnH3ZornJointProductSndTopCat :
    TopCat.of (S3Perm × H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun p : S3Perm × H3Zorn ℝ => p.2
      continuous_toFun := continuous_snd }

theorem S3OnH3ZornJointProductTopCatIso_hom_comp_fst :
    (S3OnH3ZornJointProductTopCatIso.hom ≫
        S3OnH3ZornJointProductFstTopCat) =
      S3OnH3ZornJointProductFstTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  rfl

theorem S3OnH3ZornJointProductTopCatIso_hom_comp_snd :
    (S3OnH3ZornJointProductTopCatIso.hom ≫
        S3OnH3ZornJointProductSndTopCat) =
      S3OnH3ZornJointTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  rfl

def S3OnH3ZornTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := S3OnH3Zorn σ
      continuous_toFun := continuous_S3OnH3Zorn σ }

@[simp] theorem S3OnH3ZornTopCat_apply (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornTopCat σ X = S3OnH3Zorn σ X :=
  rfl

def S3OnH3ZornContinuousLinearMap (σ : S3Perm) :
    H3Zorn ℝ →L[ℝ] H3Zorn ℝ :=
  ContinuousLinearMap.mk
    (S3OnH3ZornLinearMap σ)
    (continuous_S3OnH3Zorn σ)

@[simp] theorem S3OnH3ZornContinuousLinearMap_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornContinuousLinearMap σ X = S3OnH3Zorn σ X :=
  rfl

theorem S3OnH3ZornContinuousLinearMap_comp_closure
    (σ τ : S3Perm) :
    ∃ ρ,
      S3OnH3ZornContinuousLinearMap ρ =
        (S3OnH3ZornContinuousLinearMap τ).comp
          (S3OnH3ZornContinuousLinearMap σ) := by
  rcases S3OnH3ZornLinearMap_comp_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  apply ContinuousLinearMap.ext
  intro X
  have hX := congrArg
    (fun f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ => f X) hρ
  simpa [LinearMap.comp_apply, ContinuousLinearMap.comp_apply] using hX

theorem S3OnH3ZornContinuousLinearMap_inverse_left (σ : S3Perm) :
    (S3OnH3ZornContinuousLinearMap (S3Perm.inverse σ)).comp
        (S3OnH3ZornContinuousLinearMap σ) =
      ContinuousLinearMap.id ℝ (H3Zorn ℝ) := by
  apply ContinuousLinearMap.ext
  intro X
  simpa [ContinuousLinearMap.comp_apply] using
    S3OnH3Zorn_inverse_left σ X

theorem S3OnH3ZornContinuousLinearMap_inverse_right (σ : S3Perm) :
    (S3OnH3ZornContinuousLinearMap σ).comp
        (S3OnH3ZornContinuousLinearMap (S3Perm.inverse σ)) =
      ContinuousLinearMap.id ℝ (H3Zorn ℝ) := by
  apply ContinuousLinearMap.ext
  intro X
  simpa [ContinuousLinearMap.comp_apply] using
    S3OnH3Zorn_inverse_right σ X

def S3OnH3ZornContinuousLinearMapTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := S3OnH3ZornContinuousLinearMap σ
      continuous_toFun := (S3OnH3ZornContinuousLinearMap σ).continuous }

theorem S3OnH3ZornContinuousLinearMapTopCat_eq
    (σ : S3Perm) :
    S3OnH3ZornContinuousLinearMapTopCat σ = S3OnH3ZornTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rfl

def S3OnH3ZornTopCatIso (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ≅ TopCat.of (H3Zorn ℝ) :=
  TopCat.isoOfHomeo (S3OnH3ZornHomeomorph σ)

@[simp] theorem S3OnH3ZornTopCatIso_hom (σ : S3Perm) :
    (S3OnH3ZornTopCatIso σ).hom = S3OnH3ZornTopCat σ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rfl

@[simp] theorem S3OnH3ZornTopCatIso_inv_apply (σ : S3Perm) (X : H3Zorn ℝ) :
    (S3OnH3ZornTopCatIso σ).inv X =
      S3OnH3Zorn (S3Perm.inverse σ) X :=
  rfl

theorem S3OnH3ZornTopCatIso_hom_inv (σ : S3Perm) :
    (S3OnH3ZornTopCatIso σ).hom ≫ (S3OnH3ZornTopCatIso σ).inv =
      𝟙 (TopCat.of (H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn (S3Perm.inverse σ) (S3OnH3Zorn σ X) = X
  exact S3OnH3Zorn_inverse_left σ X

theorem S3OnH3ZornTopCatIso_inv_hom (σ : S3Perm) :
    (S3OnH3ZornTopCatIso σ).inv ≫ (S3OnH3ZornTopCatIso σ).hom =
      𝟙 (TopCat.of (H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn σ (S3OnH3Zorn (S3Perm.inverse σ) X) = X
  exact S3OnH3Zorn_inverse_right σ X

theorem S3OnH3ZornTopCatIso_hom_eq_continuousLinearMapTopCat
    (σ : S3Perm) :
    (S3OnH3ZornTopCatIso σ).hom =
      S3OnH3ZornContinuousLinearMapTopCat σ := by
  rw [S3OnH3ZornTopCatIso_hom,
    S3OnH3ZornContinuousLinearMapTopCat_eq]

theorem S3OnH3ZornTopCatIso_inv_eq_continuousLinearMapTopCat
    (σ : S3Perm) :
    (S3OnH3ZornTopCatIso σ).inv =
      S3OnH3ZornContinuousLinearMapTopCat (S3Perm.inverse σ) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [S3OnH3ZornTopCatIso_inv_apply]
  rfl

theorem S3OnH3ZornTopCat_comp (σ τ : S3Perm) :
    ∃ ρ : S3Perm,
      S3OnH3ZornTopCat σ ≫ S3OnH3ZornTopCat τ =
        S3OnH3ZornTopCat ρ := by
  rcases S3OnH3Zorn_group_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn τ (S3OnH3Zorn σ X) = S3OnH3Zorn ρ X
  simpa [Function.comp_apply] using (congrFun hρ X).symm

theorem S3OnH3ZornTopCat_comp_mul (σ τ : S3Perm) :
    S3OnH3ZornTopCat σ ≫ S3OnH3ZornTopCat τ =
      S3OnH3ZornTopCat (σ * τ) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn τ (S3OnH3Zorn σ X) =
    S3OnH3Zorn (σ * τ) X
  exact (S3OnH3Zorn_mul_apply σ τ X).symm

theorem S3OnH3ZornTopCat_s12_involutive :
    S3OnH3ZornTopCat S3Perm.s12 ≫ S3OnH3ZornTopCat S3Perm.s12 =
      𝟙 (TopCat.of (H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn S3Perm.s12 (S3OnH3Zorn S3Perm.s12 X) = X
  exact S3OnH3Zorn_s12_involutive X

theorem S3OnH3ZornTopCat_s23_involutive :
    S3OnH3ZornTopCat S3Perm.s23 ≫ S3OnH3ZornTopCat S3Perm.s23 =
      𝟙 (TopCat.of (H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn S3Perm.s23 (S3OnH3Zorn S3Perm.s23 X) = X
  exact S3OnH3Zorn_s23_involutive X

theorem S3OnH3ZornTopCat_s31_involutive :
    S3OnH3ZornTopCat S3Perm.s31 ≫ S3OnH3ZornTopCat S3Perm.s31 =
      𝟙 (TopCat.of (H3Zorn ℝ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn S3Perm.s31 (S3OnH3Zorn S3Perm.s31 X) = X
  exact S3OnH3Zorn_s31_involutive X

end InfoGeometry.Algebra
