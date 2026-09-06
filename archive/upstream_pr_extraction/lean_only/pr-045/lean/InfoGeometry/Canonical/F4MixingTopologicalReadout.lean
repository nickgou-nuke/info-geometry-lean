import InfoGeometry.Canonical.F4DerivationsTopCatAction
import InfoGeometry.Albert.F4Action
import InfoGeometry.Canonical.CubicJordanOsTopologicalReadout

/-!
# Topological readout of the finite mixing action

The algebraic owner supplies the real `actMatrixOnAlbert` action on the native
`CubicJordanOs.AlbertMatrix` carrier.  This file records its ordinary product-
topology continuity and packages the parameterized action as a `TopCat`
morphism.  It makes no claim about unitarity or phenomenological parameter
values.
-/

noncomputable section

namespace InfoGeometry.Algebra

open InfoGeometry.Algebra.CubicJordanOs

theorem continuous_actMatrixOnAlbert_left (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (fun X : AlbertMatrix => actMatrixOnAlbert M X) := by
  apply (continuous_induced_rng).2
  change Continuous (fun X : AlbertMatrix =>
    (M.mulVec ![X.α₁, X.α₂, X.α₃] 0,
      M.mulVec ![X.α₁, X.α₂, X.α₃] 1,
      M.mulVec ![X.α₁, X.α₂, X.α₃] 2,
      X.z₁, X.z₂, X.z₃))
  have h₁ := continuous_albertMatrix_α₁
  have h₂ := continuous_albertMatrix_α₂
  have h₃ := continuous_albertMatrix_α₃
  have ha₁ : Continuous (fun X : AlbertMatrix =>
      M 0 0 * X.α₁ + M 0 1 * X.α₂ + M 0 2 * X.α₃) := by
    exact ((continuous_const.mul h₁).add (continuous_const.mul h₂)).add
      (continuous_const.mul h₃)
  have ha₂ : Continuous (fun X : AlbertMatrix =>
      M 1 0 * X.α₁ + M 1 1 * X.α₂ + M 1 2 * X.α₃) := by
    exact ((continuous_const.mul h₁).add (continuous_const.mul h₂)).add
      (continuous_const.mul h₃)
  have ha₃ : Continuous (fun X : AlbertMatrix =>
      M 2 0 * X.α₁ + M 2 1 * X.α₂ + M 2 2 * X.α₃) := by
    exact ((continuous_const.mul h₁).add (continuous_const.mul h₂)).add
      (continuous_const.mul h₃)
  have htuple := ha₁.prodMk
    (ha₂.prodMk (ha₃.prodMk
      ((continuous_albertMatrix_z₁).prodMk
        ((continuous_albertMatrix_z₂).prodMk continuous_albertMatrix_z₃))))
  simpa [actMatrixOnAlbert, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using htuple

theorem continuous_actMatrixOnAlbert :
    Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × AlbertMatrix =>
      actMatrixOnAlbert p.1 p.2) := by
  apply (continuous_induced_rng).2
  change Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × AlbertMatrix =>
    (p.1.mulVec ![p.2.α₁, p.2.α₂, p.2.α₃] 0,
      p.1.mulVec ![p.2.α₁, p.2.α₂, p.2.α₃] 1,
      p.1.mulVec ![p.2.α₁, p.2.α₂, p.2.α₃] 2,
      p.2.z₁, p.2.z₂, p.2.z₃))
  let hM : ∀ i j : Fin 3, Continuous
      (fun p : Matrix (Fin 3) (Fin 3) ℝ × AlbertMatrix => p.1 i j) := by
    intro i j
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hx₁ : Continuous
      (fun p : Matrix (Fin 3) (Fin 3) ℝ × AlbertMatrix => p.2.α₁) :=
    continuous_albertMatrix_α₁.comp continuous_snd
  have hx₂ : Continuous
      (fun p : Matrix (Fin 3) (Fin 3) ℝ × AlbertMatrix => p.2.α₂) :=
    continuous_albertMatrix_α₂.comp continuous_snd
  have hx₃ : Continuous
      (fun p : Matrix (Fin 3) (Fin 3) ℝ × AlbertMatrix => p.2.α₃) :=
    continuous_albertMatrix_α₃.comp continuous_snd
  have ha₁ := ((hM 0 0).mul hx₁).add ((hM 0 1).mul hx₂) |>.add ((hM 0 2).mul hx₃)
  have ha₂ := ((hM 1 0).mul hx₁).add ((hM 1 1).mul hx₂) |>.add ((hM 1 2).mul hx₃)
  have ha₃ := ((hM 2 0).mul hx₁).add ((hM 2 1).mul hx₂) |>.add ((hM 2 2).mul hx₃)
  have htuple := ha₁.prodMk
    (ha₂.prodMk (ha₃.prodMk
      ((continuous_albertMatrix_z₁.comp continuous_snd).prodMk
        ((continuous_albertMatrix_z₂.comp continuous_snd).prodMk
          (continuous_albertMatrix_z₃.comp continuous_snd)))))
  simpa [actMatrixOnAlbert, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using htuple

theorem continuous_actMatrixOnAlbert_of_continuous
    {P : Type} [TopologicalSpace P]
    (M : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hM : Continuous M) :
    Continuous (fun p : P × AlbertMatrix => actMatrixOnAlbert (M p.1) p.2) :=
  continuous_actMatrixOnAlbert.comp
    ((hM.comp continuous_fst).prodMk continuous_snd)

def actMatrixOnAlbertTopCat
    {P : Type} [TopologicalSpace P]
    (M : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hM : Continuous M) :
    TopCat.of (P × AlbertMatrix) ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun p => actMatrixOnAlbert (M p.1) p.2
      continuous_toFun := continuous_actMatrixOnAlbert_of_continuous M hM }

@[simp] theorem actMatrixOnAlbertTopCat_apply
    {P : Type} [TopologicalSpace P]
    (M : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hM : Continuous M) (p : P × AlbertMatrix) :
    actMatrixOnAlbertTopCat M hM p = actMatrixOnAlbert (M p.1) p.2 :=
  rfl

def actMatrixOnAlbertFixedTopCat
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := actMatrixOnAlbert M
      continuous_toFun := continuous_actMatrixOnAlbert_left M }

@[simp] theorem actMatrixOnAlbertFixedTopCat_apply
    (M : Matrix (Fin 3) (Fin 3) ℝ) (X : AlbertMatrix) :
    actMatrixOnAlbertFixedTopCat M X = actMatrixOnAlbert M X :=
  rfl

theorem actMatrixOnAlbert_comp
    (M N : Matrix (Fin 3) (Fin 3) ℝ) (X : AlbertMatrix) :
    actMatrixOnAlbert M (actMatrixOnAlbert N X) =
      actMatrixOnAlbert (M * N) X := by
  cases X with
  | mk α₁ α₂ α₃ z₁ z₂ z₃ =>
    have hv : M.mulVec (N.mulVec ![α₁, α₂, α₃]) =
        (M * N).mulVec ![α₁, α₂, α₃] := by
      exact Matrix.mulVec_mulVec ![α₁, α₂, α₃] M N
    dsimp [actMatrixOnAlbert]
    congr 1
    · exact congrFun hv 0
    · exact congrFun hv 1
    · exact congrFun hv 2

theorem actMatrixOnAlbertFixedTopCat_comp_apply
    (M N : Matrix (Fin 3) (Fin 3) ℝ) (X : AlbertMatrix) :
    (CategoryTheory.ConcreteCategory.hom
      (CategoryTheory.CategoryStruct.comp
        (actMatrixOnAlbertFixedTopCat N)
        (actMatrixOnAlbertFixedTopCat M))) X =
      actMatrixOnAlbertFixedTopCat (M * N) X := by
  rw [TopCat.comp_app]
  exact actMatrixOnAlbert_comp M N X

theorem actMatrixOnAlbertFixedTopCat_comp
    (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    CategoryTheory.CategoryStruct.comp
        (actMatrixOnAlbertFixedTopCat N)
        (actMatrixOnAlbertFixedTopCat M) =
      actMatrixOnAlbertFixedTopCat (M * N) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  exact actMatrixOnAlbertFixedTopCat_comp_apply M N X

theorem actMatrixOnAlbert_one (X : AlbertMatrix) :
    actMatrixOnAlbert (1 : Matrix (Fin 3) (Fin 3) ℝ) X = X := by
  cases X with
  | mk α₁ α₂ α₃ z₁ z₂ z₃ =>
    ext <;>
      simp [actMatrixOnAlbert, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem actMatrixOnAlbertFixedTopCat_identity_apply (X : AlbertMatrix) :
    (CategoryTheory.ConcreteCategory.hom
      (CategoryTheory.CategoryStruct.id (TopCat.of AlbertMatrix))) X =
      actMatrixOnAlbertFixedTopCat (1 : Matrix (Fin 3) (Fin 3) ℝ) X := by
  change X = actMatrixOnAlbert (1 : Matrix (Fin 3) (Fin 3) ℝ) X
  exact (actMatrixOnAlbert_one X).symm

theorem actMatrixOnAlbertFixedTopCat_identity :
    CategoryTheory.CategoryStruct.id (TopCat.of AlbertMatrix) =
      actMatrixOnAlbertFixedTopCat (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  exact actMatrixOnAlbertFixedTopCat_identity_apply X

theorem actMatrixOnAlbert_inverse_apply
    (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hMN : M * N = 1) (X : AlbertMatrix) :
    actMatrixOnAlbert M (actMatrixOnAlbert N X) = X := by
  rw [actMatrixOnAlbert_comp, hMN, actMatrixOnAlbert_one]

theorem actMatrixOnAlbertFixedTopCat_inverse_apply
    (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hMN : M * N = 1) (X : AlbertMatrix) :
    (CategoryTheory.ConcreteCategory.hom
      (CategoryTheory.CategoryStruct.comp
        (actMatrixOnAlbertFixedTopCat N)
        (actMatrixOnAlbertFixedTopCat M))) X = X := by
  rw [TopCat.comp_app]
  exact actMatrixOnAlbert_inverse_apply M N hMN X

theorem continuous_CKMMatrix : Continuous CKMMatrix := by
  simpa [CKMMatrix] using
    continuous_actMatrixOnAlbert_left
      (mixingMatrix 0.227 0.042 0.0036 1.20)

theorem continuous_PMNSMatrix : Continuous PMNSMatrix := by
  simpa [PMNSMatrix] using
    continuous_actMatrixOnAlbert_left
      (mixingMatrix 0.58 0.86 0.15 3.77)

def CKMMatrixTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := CKMMatrix
      continuous_toFun := continuous_CKMMatrix }

@[simp] theorem CKMMatrixTopCat_apply (X : AlbertMatrix) :
    CKMMatrixTopCat X = CKMMatrix X :=
  rfl

def PMNSMatrixTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := PMNSMatrix
      continuous_toFun := continuous_PMNSMatrix }

@[simp] theorem PMNSMatrixTopCat_apply (X : AlbertMatrix) :
    PMNSMatrixTopCat X = PMNSMatrix X :=
  rfl

theorem CKMMatrixTopCat_factorization :
    CKMMatrixTopCat =
      actMatrixOnAlbertFixedTopCat
        (mixingMatrix 0.227 0.042 0.0036 1.20) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rfl

theorem PMNSMatrixTopCat_factorization :
    PMNSMatrixTopCat =
      actMatrixOnAlbertFixedTopCat
        (mixingMatrix 0.58 0.86 0.15 3.77) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rfl

theorem PMNSMatrixTopCat_comp_CKMMatrixTopCat :
    CategoryTheory.CategoryStruct.comp PMNSMatrixTopCat CKMMatrixTopCat =
      actMatrixOnAlbertFixedTopCat
        ((mixingMatrix 0.227 0.042 0.0036 1.20) *
          (mixingMatrix 0.58 0.86 0.15 3.77)) := by
  rw [CKMMatrixTopCat_factorization, PMNSMatrixTopCat_factorization]
  exact actMatrixOnAlbertFixedTopCat_comp
    (mixingMatrix 0.227 0.042 0.0036 1.20)
    (mixingMatrix 0.58 0.86 0.15 3.77)

theorem CKMMatrixTopCat_comp_PMNSMatrixTopCat :
    CategoryTheory.CategoryStruct.comp CKMMatrixTopCat PMNSMatrixTopCat =
      actMatrixOnAlbertFixedTopCat
        ((mixingMatrix 0.58 0.86 0.15 3.77) *
          (mixingMatrix 0.227 0.042 0.0036 1.20)) := by
  rw [CKMMatrixTopCat_factorization, PMNSMatrixTopCat_factorization]
  exact actMatrixOnAlbertFixedTopCat_comp
    (mixingMatrix 0.58 0.86 0.15 3.77)
    (mixingMatrix 0.227 0.042 0.0036 1.20)

end InfoGeometry.Algebra
