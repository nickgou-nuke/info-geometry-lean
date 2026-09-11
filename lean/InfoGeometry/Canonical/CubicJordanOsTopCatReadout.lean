import InfoGeometry.Canonical.CubicJordanOsTopologicalReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` readout for the native cubic Albert invariant

This bridge packages only the already-proved continuity of `normCubic`.
Continuity of `adjointQuad` and a Jordan product are intentionally not
introduced here because the current native owners do not provide those
theorems on the same topological carrier.
-/

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

def normCubicContinuousMap : ContinuousMap AlbertMatrix ℝ :=
  ContinuousMap.mk normCubic continuous_normCubic

@[simp] theorem normCubicContinuousMap_apply (X : AlbertMatrix) :
    normCubicContinuousMap X = normCubic X :=
  rfl

def normCubicTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := normCubic
      continuous_toFun := continuous_normCubic }

@[simp] theorem normCubicTopCat_apply (X : AlbertMatrix) :
    normCubicTopCat X = normCubic X :=
  rfl

def traceBilinContinuousMap :
    ContinuousMap (AlbertMatrix × AlbertMatrix) ℝ :=
  ContinuousMap.mk
    (fun p : AlbertMatrix × AlbertMatrix => traceBilin p.1 p.2)
    continuous_traceBilin

@[simp] theorem traceBilinContinuousMap_apply
    (p : AlbertMatrix × AlbertMatrix) :
    traceBilinContinuousMap p = traceBilin p.1 p.2 :=
  rfl

def traceBilinTopCat :
    TopCat.of (AlbertMatrix × AlbertMatrix) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrix × AlbertMatrix => traceBilin p.1 p.2
      continuous_toFun := continuous_traceBilin }

@[simp] theorem traceBilinTopCat_apply
    (p : AlbertMatrix × AlbertMatrix) :
    traceBilinTopCat p = traceBilin p.1 p.2 :=
  rfl

def albertMatrixAddContinuousMap :
    ContinuousMap (AlbertMatrix × AlbertMatrix) AlbertMatrix :=
  ContinuousMap.mk
    (fun p : AlbertMatrix × AlbertMatrix => p.1 + p.2)
    continuous_albertMatrix_add

def albertMatrixAddTopCat :
    TopCat.of (AlbertMatrix × AlbertMatrix) ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrix × AlbertMatrix => p.1 + p.2
      continuous_toFun := continuous_albertMatrix_add }

def peirceFullReconstructionContinuousMap :
    ContinuousMap AlbertMatrix AlbertMatrix := by
  let h11 : Continuous (fun X : AlbertMatrix => peirceProj11 X) :=
    continuous_peirceProj11
  let h22 : Continuous (fun X : AlbertMatrix => peirceProj22 X) :=
    continuous_peirceProj22
  let h33 : Continuous (fun X : AlbertMatrix => peirceProj33 X) :=
    continuous_peirceProj33
  let h23 : Continuous (fun X : AlbertMatrix => peirceProj23 X) :=
    continuous_peirceProj23
  let h31 : Continuous (fun X : AlbertMatrix => peirceProj31 X) :=
    continuous_peirceProj31
  let h12 : Continuous (fun X : AlbertMatrix => peirceProj12 X) :=
    continuous_peirceProj12
  let h1122 : Continuous
      (fun X : AlbertMatrix => peirceProj11 X + peirceProj22 X) :=
    continuous_albertMatrix_add.comp (h11.prodMk h22)
  let h112233 : Continuous
      (fun X : AlbertMatrix => peirceProj11 X + peirceProj22 X + peirceProj33 X) :=
    continuous_albertMatrix_add.comp (h1122.prodMk h33)
  let h11223323 : Continuous
      (fun X : AlbertMatrix =>
        peirceProj11 X + peirceProj22 X + peirceProj33 X + peirceProj23 X) :=
    continuous_albertMatrix_add.comp (h112233.prodMk h23)
  let h1122332331 : Continuous
      (fun X : AlbertMatrix =>
        peirceProj11 X + peirceProj22 X + peirceProj33 X +
          peirceProj23 X + peirceProj31 X) :=
    continuous_albertMatrix_add.comp (h11223323.prodMk h31)
  exact ContinuousMap.mk
    (fun X : AlbertMatrix =>
      peirceProj11 X + peirceProj22 X + peirceProj33 X +
        peirceProj23 X + peirceProj31 X + peirceProj12 X)
    (continuous_albertMatrix_add.comp (h1122332331.prodMk h12))

def peirceFullReconstructionTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix =>
        peirceProj11 X + peirceProj22 X + peirceProj33 X +
          peirceProj23 X + peirceProj31 X + peirceProj12 X
      continuous_toFun := by
        let h11 : Continuous (fun X : AlbertMatrix => peirceProj11 X) :=
          continuous_peirceProj11
        let h22 : Continuous (fun X : AlbertMatrix => peirceProj22 X) :=
          continuous_peirceProj22
        let h33 : Continuous (fun X : AlbertMatrix => peirceProj33 X) :=
          continuous_peirceProj33
        let h23 : Continuous (fun X : AlbertMatrix => peirceProj23 X) :=
          continuous_peirceProj23
        let h31 : Continuous (fun X : AlbertMatrix => peirceProj31 X) :=
          continuous_peirceProj31
        let h12 : Continuous (fun X : AlbertMatrix => peirceProj12 X) :=
          continuous_peirceProj12
        let h1122 : Continuous
            (fun X : AlbertMatrix => peirceProj11 X + peirceProj22 X) :=
          continuous_albertMatrix_add.comp (h11.prodMk h22)
        let h112233 : Continuous
            (fun X : AlbertMatrix => peirceProj11 X + peirceProj22 X + peirceProj33 X) :=
          continuous_albertMatrix_add.comp (h1122.prodMk h33)
        let h11223323 : Continuous
            (fun X : AlbertMatrix =>
              peirceProj11 X + peirceProj22 X + peirceProj33 X + peirceProj23 X) :=
          continuous_albertMatrix_add.comp (h112233.prodMk h23)
        let h1122332331 : Continuous
            (fun X : AlbertMatrix =>
              peirceProj11 X + peirceProj22 X + peirceProj33 X +
                peirceProj23 X + peirceProj31 X) :=
          continuous_albertMatrix_add.comp (h11223323.prodMk h31)
        exact continuous_albertMatrix_add.comp (h1122332331.prodMk h12) }

@[simp] theorem peirceFullReconstructionTopCat_apply (X : AlbertMatrix) :
    peirceFullReconstructionTopCat X = X := by
  change peirceProj11 X + peirceProj22 X + peirceProj33 X +
      peirceProj23 X + peirceProj31 X + peirceProj12 X = X
  exact (peirce_full_decomposition X).symm

theorem peirceFullReconstructionContinuousMap_eq_id :
    peirceFullReconstructionContinuousMap = ContinuousMap.id AlbertMatrix := by
  apply ContinuousMap.ext
  intro X
  change peirceProj11 X + peirceProj22 X + peirceProj33 X +
      peirceProj23 X + peirceProj31 X + peirceProj12 X = X
  exact (peirce_full_decomposition X).symm

theorem peirceFullReconstructionTopCat_eq_id :
    peirceFullReconstructionTopCat =
      CategoryTheory.CategoryStruct.id (TopCat.of AlbertMatrix) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change peirceProj11 X + peirceProj22 X + peirceProj33 X +
      peirceProj23 X + peirceProj31 X + peirceProj12 X = X
  exact (peirce_full_decomposition X).symm

def normCubicAfterPeirceReconstructionContinuousMap :
    ContinuousMap AlbertMatrix ℝ :=
  normCubicContinuousMap.comp peirceFullReconstructionContinuousMap

def normCubicAfterPeirceReconstructionTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of ℝ :=
  CategoryTheory.CategoryStruct.comp peirceFullReconstructionTopCat normCubicTopCat

theorem normCubicAfterPeirceReconstructionContinuousMap_eq_normCubic :
    normCubicAfterPeirceReconstructionContinuousMap = normCubicContinuousMap := by
  apply ContinuousMap.ext
  intro X
  change normCubic (peirceFullReconstructionContinuousMap X) = normCubic X
  rw [peirceFullReconstructionContinuousMap_eq_id]
  rfl

theorem normCubicAfterPeirceReconstructionTopCat_eq_normCubic :
    normCubicAfterPeirceReconstructionTopCat = normCubicTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change normCubicTopCat (peirceFullReconstructionTopCat X) = normCubicTopCat X
  rw [peirceFullReconstructionTopCat_apply]

abbrev AlbertMatrixPeirceSixProduct :=
  (((((AlbertMatrix × AlbertMatrix) × AlbertMatrix) × AlbertMatrix) ×
      AlbertMatrix) × AlbertMatrix)

def peirceProjectionProductContinuousMap :
    ContinuousMap AlbertMatrix AlbertMatrixPeirceSixProduct := by
  let h11 : Continuous (fun X : AlbertMatrix => peirceProj11 X) :=
    continuous_peirceProj11
  let h22 : Continuous (fun X : AlbertMatrix => peirceProj22 X) :=
    continuous_peirceProj22
  let h33 : Continuous (fun X : AlbertMatrix => peirceProj33 X) :=
    continuous_peirceProj33
  let h23 : Continuous (fun X : AlbertMatrix => peirceProj23 X) :=
    continuous_peirceProj23
  let h31 : Continuous (fun X : AlbertMatrix => peirceProj31 X) :=
    continuous_peirceProj31
  let h12 : Continuous (fun X : AlbertMatrix => peirceProj12 X) :=
    continuous_peirceProj12
  let h1122 : Continuous (fun X : AlbertMatrix =>
      (peirceProj11 X, peirceProj22 X)) := h11.prodMk h22
  let h112233 : Continuous (fun X : AlbertMatrix =>
      ((peirceProj11 X, peirceProj22 X), peirceProj33 X)) :=
    h1122.prodMk h33
  let h11223323 : Continuous (fun X : AlbertMatrix =>
      (((peirceProj11 X, peirceProj22 X), peirceProj33 X), peirceProj23 X)) :=
    h112233.prodMk h23
  let h1122332331 : Continuous (fun X : AlbertMatrix =>
      ((((peirceProj11 X, peirceProj22 X), peirceProj33 X), peirceProj23 X),
        peirceProj31 X)) :=
    h11223323.prodMk h31
  exact ContinuousMap.mk
    (fun X : AlbertMatrix =>
      (((((peirceProj11 X, peirceProj22 X), peirceProj33 X), peirceProj23 X),
        peirceProj31 X), peirceProj12 X))
    (h1122332331.prodMk h12)

def peirceProjectionProductTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrixPeirceSixProduct :=
  TopCat.ofHom peirceProjectionProductContinuousMap

@[simp] theorem peirceProjectionProductTopCat_apply (X : AlbertMatrix) :
    peirceProjectionProductTopCat X =
      (((((peirceProj11 X, peirceProj22 X), peirceProj33 X), peirceProj23 X),
        peirceProj31 X), peirceProj12 X) :=
  rfl

def peirceNestedSumContinuousMap :
    ContinuousMap AlbertMatrixPeirceSixProduct AlbertMatrix := by
  let h11 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.1) := by fun_prop
  let h22 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.2) := by fun_prop
  let h33 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.2) := by fun_prop
  let h23 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.2) := by fun_prop
  let h31 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.2) := by fun_prop
  let h12 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.2) := by fun_prop
  let h1122 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.1 + X.1.1.1.1.2) :=
    continuous_albertMatrix_add.comp (h11.prodMk h22)
  let h112233 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.1 + X.1.1.1.1.2 + X.1.1.1.2) :=
    continuous_albertMatrix_add.comp (h1122.prodMk h33)
  let h11223323 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.1 + X.1.1.1.1.2 + X.1.1.1.2 + X.1.1.2) :=
    continuous_albertMatrix_add.comp (h112233.prodMk h23)
  let h1122332331 : Continuous (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.1 + X.1.1.1.1.2 + X.1.1.1.2 + X.1.1.2 + X.1.2) :=
    continuous_albertMatrix_add.comp (h11223323.prodMk h31)
  exact ContinuousMap.mk
    (fun X : AlbertMatrixPeirceSixProduct =>
      X.1.1.1.1.1 + X.1.1.1.1.2 + X.1.1.1.2 + X.1.1.2 + X.1.2 + X.2)
    (continuous_albertMatrix_add.comp (h1122332331.prodMk h12))

def peirceNestedSumTopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom peirceNestedSumContinuousMap

@[simp] theorem peirceNestedSumTopCat_apply
    (X : AlbertMatrixPeirceSixProduct) :
    peirceNestedSumTopCat X =
      X.1.1.1.1.1 + X.1.1.1.1.2 + X.1.1.1.2 + X.1.1.2 + X.1.2 + X.2 :=
  rfl

theorem peirceNestedSumTopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceNestedSumTopCat =
      peirceFullReconstructionTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  rfl

def peirceSixProj11TopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrixPeirceSixProduct => X.1.1.1.1.1
      continuous_toFun := by fun_prop }

def peirceSixProj22TopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrixPeirceSixProduct => X.1.1.1.1.2
      continuous_toFun := by fun_prop }

def peirceSixProj33TopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrixPeirceSixProduct => X.1.1.1.2
      continuous_toFun := by fun_prop }

def peirceSixProj23TopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrixPeirceSixProduct => X.1.1.2
      continuous_toFun := by fun_prop }

def peirceSixProj31TopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrixPeirceSixProduct => X.1.2
      continuous_toFun := by fun_prop }

def peirceSixProj12TopCat :
    TopCat.of AlbertMatrixPeirceSixProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrixPeirceSixProduct => X.2
      continuous_toFun := by fun_prop }

@[simp] theorem albertMatrixAddContinuousMap_apply
    (p : AlbertMatrix × AlbertMatrix) :
    albertMatrixAddContinuousMap p = p.1 + p.2 :=
  rfl

@[simp] theorem albertMatrixAddTopCat_apply
    (p : AlbertMatrix × AlbertMatrix) :
    albertMatrixAddTopCat p = p.1 + p.2 :=
  rfl

def peirceProj11ContinuousMap : ContinuousMap AlbertMatrix AlbertMatrix :=
  ContinuousMap.mk peirceProj11 continuous_peirceProj11

def peirceProj22ContinuousMap : ContinuousMap AlbertMatrix AlbertMatrix :=
  ContinuousMap.mk peirceProj22 continuous_peirceProj22

def peirceProj33ContinuousMap : ContinuousMap AlbertMatrix AlbertMatrix :=
  ContinuousMap.mk peirceProj33 continuous_peirceProj33

def peirceProj23ContinuousMap : ContinuousMap AlbertMatrix AlbertMatrix :=
  ContinuousMap.mk peirceProj23 continuous_peirceProj23

def peirceProj31ContinuousMap : ContinuousMap AlbertMatrix AlbertMatrix :=
  ContinuousMap.mk peirceProj31 continuous_peirceProj31

def peirceProj12ContinuousMap : ContinuousMap AlbertMatrix AlbertMatrix :=
  ContinuousMap.mk peirceProj12 continuous_peirceProj12

def peirceProj11TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := peirceProj11
      continuous_toFun := continuous_peirceProj11 }

def peirceProj22TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := peirceProj22
      continuous_toFun := continuous_peirceProj22 }

def peirceProj33TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := peirceProj33
      continuous_toFun := continuous_peirceProj33 }

def peirceProj23TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := peirceProj23
      continuous_toFun := continuous_peirceProj23 }

def peirceProj31TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := peirceProj31
      continuous_toFun := continuous_peirceProj31 }

def peirceProj12TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom
    { toFun := peirceProj12
      continuous_toFun := continuous_peirceProj12 }

@[simp] theorem peirceProj11TopCat_apply (X : AlbertMatrix) :
    peirceProj11TopCat X = peirceProj11 X := rfl

@[simp] theorem peirceProj22TopCat_apply (X : AlbertMatrix) :
    peirceProj22TopCat X = peirceProj22 X := rfl

@[simp] theorem peirceProj33TopCat_apply (X : AlbertMatrix) :
    peirceProj33TopCat X = peirceProj33 X := rfl

@[simp] theorem peirceProj23TopCat_apply (X : AlbertMatrix) :
    peirceProj23TopCat X = peirceProj23 X := rfl

@[simp] theorem peirceProj31TopCat_apply (X : AlbertMatrix) :
    peirceProj31TopCat X = peirceProj31 X := rfl

@[simp] theorem peirceProj12TopCat_apply (X : AlbertMatrix) :
    peirceProj12TopCat X = peirceProj12 X := rfl

theorem peirceSixProj11TopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceSixProj11TopCat = peirceProj11TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  simp [peirceSixProj11TopCat, peirceProjectionProductTopCat,
    peirceProjectionProductContinuousMap, peirceProj11TopCat]

theorem peirceSixProj22TopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceSixProj22TopCat = peirceProj22TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  simp [peirceSixProj22TopCat, peirceProjectionProductTopCat,
    peirceProjectionProductContinuousMap, peirceProj22TopCat]

theorem peirceSixProj33TopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceSixProj33TopCat = peirceProj33TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  simp [peirceSixProj33TopCat, peirceProjectionProductTopCat,
    peirceProjectionProductContinuousMap, peirceProj33TopCat]

theorem peirceSixProj23TopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceSixProj23TopCat = peirceProj23TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  simp [peirceSixProj23TopCat, peirceProjectionProductTopCat,
    peirceProjectionProductContinuousMap, peirceProj23TopCat]

theorem peirceSixProj31TopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceSixProj31TopCat = peirceProj31TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  simp [peirceSixProj31TopCat, peirceProjectionProductTopCat,
    peirceProjectionProductContinuousMap, peirceProj31TopCat]

theorem peirceSixProj12TopCat_comp_projectionProduct :
    CategoryTheory.CategoryStruct.comp peirceProjectionProductTopCat
        peirceSixProj12TopCat = peirceProj12TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  rw [TopCat.comp_app]
  simp [peirceSixProj12TopCat, peirceProjectionProductTopCat,
    peirceProjectionProductContinuousMap, peirceProj12TopCat]

def peirceDiag1ContinuousMap : ContinuousMap AlbertMatrix ℝ :=
  ContinuousMap.mk
    (fun X : AlbertMatrix => (peirceDecomposition X).diag₁)
    continuous_peirceDecomposition_diag₁

def peirceDiag2ContinuousMap : ContinuousMap AlbertMatrix ℝ :=
  ContinuousMap.mk
    (fun X : AlbertMatrix => (peirceDecomposition X).diag₂)
    continuous_peirceDecomposition_diag₂

def peirceDiag3ContinuousMap : ContinuousMap AlbertMatrix ℝ :=
  ContinuousMap.mk
    (fun X : AlbertMatrix => (peirceDecomposition X).diag₃)
    continuous_peirceDecomposition_diag₃

def peirceOff23ContinuousMap : ContinuousMap AlbertMatrix SplitOct :=
  ContinuousMap.mk
    (fun X : AlbertMatrix => (peirceDecomposition X).off₂₃)
    continuous_peirceDecomposition_off₂₃

def peirceOff31ContinuousMap : ContinuousMap AlbertMatrix SplitOct :=
  ContinuousMap.mk
    (fun X : AlbertMatrix => (peirceDecomposition X).off₃₁)
    continuous_peirceDecomposition_off₃₁

def peirceOff12ContinuousMap : ContinuousMap AlbertMatrix SplitOct :=
  ContinuousMap.mk
    (fun X : AlbertMatrix => (peirceDecomposition X).off₁₂)
    continuous_peirceDecomposition_off₁₂

def peirceDiag1TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix => (peirceDecomposition X).diag₁
      continuous_toFun := continuous_peirceDecomposition_diag₁ }

def peirceDiag2TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix => (peirceDecomposition X).diag₂
      continuous_toFun := continuous_peirceDecomposition_diag₂ }

def peirceDiag3TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix => (peirceDecomposition X).diag₃
      continuous_toFun := continuous_peirceDecomposition_diag₃ }

def peirceOff23TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of SplitOct :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix => (peirceDecomposition X).off₂₃
      continuous_toFun := continuous_peirceDecomposition_off₂₃ }

def peirceOff31TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of SplitOct :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix => (peirceDecomposition X).off₃₁
      continuous_toFun := continuous_peirceDecomposition_off₃₁ }

def peirceOff12TopCat : TopCat.of AlbertMatrix ⟶ TopCat.of SplitOct :=
  TopCat.ofHom
    { toFun := fun X : AlbertMatrix => (peirceDecomposition X).off₁₂
      continuous_toFun := continuous_peirceDecomposition_off₁₂ }

@[simp] theorem peirceDiag1TopCat_apply (X : AlbertMatrix) :
    peirceDiag1TopCat X = (peirceDecomposition X).diag₁ := rfl

@[simp] theorem peirceDiag2TopCat_apply (X : AlbertMatrix) :
    peirceDiag2TopCat X = (peirceDecomposition X).diag₂ := rfl

@[simp] theorem peirceDiag3TopCat_apply (X : AlbertMatrix) :
    peirceDiag3TopCat X = (peirceDecomposition X).diag₃ := rfl

@[simp] theorem peirceOff23TopCat_apply (X : AlbertMatrix) :
    peirceOff23TopCat X = (peirceDecomposition X).off₂₃ := rfl

@[simp] theorem peirceOff31TopCat_apply (X : AlbertMatrix) :
    peirceOff31TopCat X = (peirceDecomposition X).off₃₁ := rfl

@[simp] theorem peirceOff12TopCat_apply (X : AlbertMatrix) :
    peirceOff12TopCat X = (peirceDecomposition X).off₁₂ := rfl

abbrev AlbertMatrixPeirceReadoutProduct :=
  ℝ × ℝ × ℝ × SplitOct × SplitOct × SplitOct

def peirceDecompositionContinuousMap :
    ContinuousMap AlbertMatrix AlbertMatrixPeirceReadoutProduct := by
  let hdiag₁ : Continuous
      (fun X : AlbertMatrix => (peirceDecomposition X).diag₁) :=
    continuous_peirceDecomposition_diag₁
  let hdiag₂ : Continuous
      (fun X : AlbertMatrix => (peirceDecomposition X).diag₂) :=
    continuous_peirceDecomposition_diag₂
  let hdiag₃ : Continuous
      (fun X : AlbertMatrix => (peirceDecomposition X).diag₃) :=
    continuous_peirceDecomposition_diag₃
  let hoff₂₃ : Continuous
      (fun X : AlbertMatrix => (peirceDecomposition X).off₂₃) :=
    continuous_peirceDecomposition_off₂₃
  let hoff₃₁ : Continuous
      (fun X : AlbertMatrix => (peirceDecomposition X).off₃₁) :=
    continuous_peirceDecomposition_off₃₁
  let hoff₁₂ : Continuous
      (fun X : AlbertMatrix => (peirceDecomposition X).off₁₂) :=
    continuous_peirceDecomposition_off₁₂
  exact ContinuousMap.mk
    (fun X : AlbertMatrix =>
      ((peirceDecomposition X).diag₁,
        (peirceDecomposition X).diag₂,
        (peirceDecomposition X).diag₃,
        (peirceDecomposition X).off₂₃,
        (peirceDecomposition X).off₃₁,
        (peirceDecomposition X).off₁₂))
    (hdiag₁.prodMk (hdiag₂.prodMk (hdiag₃.prodMk
      (hoff₂₃.prodMk (hoff₃₁.prodMk hoff₁₂)))))

def peirceDecompositionTopCat :
    TopCat.of AlbertMatrix ⟶ TopCat.of AlbertMatrixPeirceReadoutProduct :=
  TopCat.ofHom peirceDecompositionContinuousMap

@[simp] theorem peirceDecompositionTopCat_apply (X : AlbertMatrix) :
    peirceDecompositionTopCat X =
      ((peirceDecomposition X).diag₁,
        (peirceDecomposition X).diag₂,
        (peirceDecomposition X).diag₃,
        (peirceDecomposition X).off₂₃,
        (peirceDecomposition X).off₃₁,
        (peirceDecomposition X).off₁₂) :=
  rfl

def peirceReadoutDiag1TopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrixPeirceReadoutProduct => p.1
      continuous_toFun := by fun_prop }

def peirceReadoutDiag2TopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrixPeirceReadoutProduct => p.2.1
      continuous_toFun := by fun_prop }

def peirceReadoutDiag3TopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrixPeirceReadoutProduct => p.2.2.1
      continuous_toFun := by fun_prop }

def peirceReadoutOff23TopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of SplitOct :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrixPeirceReadoutProduct => p.2.2.2.1
      continuous_toFun := by fun_prop }

def peirceReadoutOff31TopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of SplitOct :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrixPeirceReadoutProduct => p.2.2.2.2.1
      continuous_toFun := by fun_prop }

def peirceReadoutOff12TopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of SplitOct :=
  TopCat.ofHom
    { toFun := fun p : AlbertMatrixPeirceReadoutProduct => p.2.2.2.2.2
      continuous_toFun := by fun_prop }

theorem peirceReadoutDiag1TopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutDiag1TopCat = peirceDiag1TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (peirceDecomposition X).diag₁ = (peirceDecomposition X).diag₁
  rfl

theorem peirceReadoutDiag2TopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutDiag2TopCat = peirceDiag2TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (peirceDecomposition X).diag₂ = (peirceDecomposition X).diag₂
  rfl

theorem peirceReadoutDiag3TopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutDiag3TopCat = peirceDiag3TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (peirceDecomposition X).diag₃ = (peirceDecomposition X).diag₃
  rfl

theorem peirceReadoutOff23TopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutOff23TopCat = peirceOff23TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (peirceDecomposition X).off₂₃ = (peirceDecomposition X).off₂₃
  rfl

theorem peirceReadoutOff31TopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutOff31TopCat = peirceOff31TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (peirceDecomposition X).off₃₁ = (peirceDecomposition X).off₃₁
  rfl

theorem peirceReadoutOff12TopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutOff12TopCat = peirceOff12TopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (peirceDecomposition X).off₁₂ = (peirceDecomposition X).off₁₂
  rfl

def peirceReadoutReconstructionContinuousMap :
    ContinuousMap AlbertMatrixPeirceReadoutProduct AlbertMatrix :=
  ContinuousMap.mk albertMatrixEquiv.invFun (by
    apply (continuous_induced_rng).2
    have hcomp :
        albertMatrixEquiv.toFun ∘ albertMatrixEquiv.invFun = id := by
      funext p
      exact albertMatrixEquiv.apply_symm_apply p
    rw [hcomp]
    exact continuous_id)

def peirceReadoutReconstructionTopCat :
    TopCat.of AlbertMatrixPeirceReadoutProduct ⟶ TopCat.of AlbertMatrix :=
  TopCat.ofHom peirceReadoutReconstructionContinuousMap

@[simp] theorem peirceReadoutReconstructionTopCat_apply
    (p : AlbertMatrixPeirceReadoutProduct) :
    peirceReadoutReconstructionTopCat p = albertMatrixEquiv.invFun p :=
  rfl

theorem peirceReadoutReconstructionTopCat_comp_decomposition :
    CategoryTheory.CategoryStruct.comp peirceDecompositionTopCat
        peirceReadoutReconstructionTopCat =
      CategoryTheory.CategoryStruct.id (TopCat.of AlbertMatrix) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change albertMatrixEquiv.invFun (albertMatrixEquiv X) = X
  exact albertMatrixEquiv.symm_apply_apply X

theorem peirceDecompositionTopCat_comp_readoutReconstruction :
    CategoryTheory.CategoryStruct.comp peirceReadoutReconstructionTopCat
        peirceDecompositionTopCat =
      CategoryTheory.CategoryStruct.id
        (TopCat.of AlbertMatrixPeirceReadoutProduct) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change albertMatrixEquiv (albertMatrixEquiv.invFun p) = p
  exact albertMatrixEquiv.apply_symm_apply p

end InfoGeometry.Algebra.CubicJordanOs
