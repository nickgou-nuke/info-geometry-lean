import InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit

/-!
# Tensor fusion carrier into the UHF/Cuntz topological colimit

The finite tensor carrier `M₂(ℂ) ⊗ M₂(ℂ)` is canonically the stage-two
matrix algebra `M₄(ℂ)`.  This file records that identification as a continuous
`TopCat` morphism and descends it to the existing matrix-tower colimit.  The
construction is a genuine colimit cocone, rather than an informal choice of
an infinite-dimensional target.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit
open FilteredColimit.Native.Topological
open scoped Kronecker

/-- The finite index identification `(Fin 2 × Fin 2) ≃ Fin 4`. -/
noncomputable def fusionTensorStageTwoEquiv :
    (Fin 2 × Fin 2) ≃ Fin (2 ^ 2) :=
  finProdFinEquiv.trans (finCongr (by norm_num))

/-- The matrix-algebra isomorphism from the tensor carrier to `MatrixStage 2`. -/
noncomputable def fusionTensorStageTwoAlgEquiv :
    FusionTensorCarrier ℂ ≃ₐ[ℂ] MatrixStage 2 :=
  Matrix.reindexAlgEquiv ℂ ℂ fusionTensorStageTwoEquiv

theorem fusionTensorStageTwoAlgEquiv_kronecker
    (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    fusionTensorStageTwoAlgEquiv (M ⊗ₖ N) =
      Matrix.reindexAlgEquiv ℂ ℂ fusionTensorStageTwoEquiv
        (M ⊗ₖ N) := rfl

def fusionTensorStageTwoTopCatHom :
    TopCat.of (FusionTensorCarrier ℂ) ⟶ TopCat.of (MatrixStage 2) :=
  TopCat.ofHom
    { toFun := fusionTensorStageTwoAlgEquiv
      continuous_toFun :=
        fusionTensorStageTwoAlgEquiv.toLinearMap.continuous_of_finiteDimensional }

@[simp]
theorem fusionTensorStageTwoTopCatHom_apply
    (X : FusionTensorCarrier ℂ) :
    fusionTensorStageTwoTopCatHom X = fusionTensorStageTwoAlgEquiv X := rfl

def fusionTensorToUHFColimitCocone
    (T : CuntzMatrixTraceTower.Data) :
    Cocone (fusionTensorTopologicalDiagram (K := ℂ)) where
  pt := topologicalColimitObject T
  ι :=
    { app := fun _ => fusionTensorStageTwoTopCatHom ≫
        topologicalInclusion T 2
      naturality := by
        intro i j f
        simp [fusionTensorTopologicalDiagram] }

noncomputable def fusionTensorToUHFTopologicalColimit
    (T : CuntzMatrixTraceTower.Data) :
    topologicalDirectColimit (fusionTensorTopologicalDiagram (K := ℂ)) ⟶
      topologicalColimitObject T :=
  topologicalDirectDescend (fusionTensorTopologicalDiagram (K := ℂ))
    (fusionTensorToUHFColimitCocone T)

theorem fusionTensorToUHFTopologicalColimit_stage
    (T : CuntzMatrixTraceTower.Data) (n : ℕ) :
    topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n ≫
      fusionTensorToUHFTopologicalColimit T =
    fusionTensorStageTwoTopCatHom ≫ topologicalInclusion T 2 := by
  exact topologicalDirectDescend_stage
    (fusionTensorTopologicalDiagram (K := ℂ))
    (fusionTensorToUHFColimitCocone T) n

theorem fusionTensorToUHFTopologicalColimit_stage_apply
    (T : CuntzMatrixTraceTower.Data) (n : ℕ)
    (X : FusionTensorCarrier ℂ) :
    fusionTensorToUHFTopologicalColimit T
      (topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := ℂ)) n X) =
      topologicalInclusion T 2 (fusionTensorStageTwoAlgEquiv X) := by
  have h := fusionTensorToUHFTopologicalColimit_stage T n
  have hx := congrArg (fun f => f X) h
  simpa only [Category.assoc, fusionTensorStageTwoTopCatHom_apply] using hx

end InfoGeometry.Canonical.NonAbelianFusionTensorUHFTopologicalBridge
