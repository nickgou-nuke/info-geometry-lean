import InfoGeometry.Canonical.UHFBoundaryFunctionOperatorTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFBoundaryOperatorTopCat

/-!
# Cylinder-to-function-space operator compatibility

The finite cylinder subalgebra embeds continuously into the full product
function space.  This owner records that the UHF boundary and Laplacian
operators commute with this inclusion.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryCylinderFunctionTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBoundaryOperatorTopology
open InfoGeometry.Canonical.UHFBoundaryFunctionOperatorTopCat
open InfoGeometry.Canonical.UHFBoundaryExactSequence

abbrev CylinderAlgebra :=
  InfoGeometry.Canonical.UHFBoundaryOperatorTopology.CylinderAlgebra

def cylinderToBoundaryFunctionTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := fun g => g.1
      continuous_toFun := continuous_subtype_val }

theorem cylinderToBoundaryFunctionTopCatHom_apply (g : CylinderAlgebra) :
    cylinderToBoundaryFunctionTopCatHom g = g.1 := rfl

def UHF_boundary_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := UHF_boundary_cylinderMap
      continuous_toFun := continuous_UHF_boundary_cylinderMap }

def star_UHF_boundary_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := star_UHF_boundary_cylinderMap
      continuous_toFun := continuous_star_UHF_boundary_cylinderMap }

def UHF_laplacian_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := UHF_Laplacian_cylinderMap
      continuous_toFun := continuous_UHF_Laplacian_cylinderMap }

def S_L_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := S_L_cylinderMap
      continuous_toFun := continuous_S_L_cylinderMap }

def S_R_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := S_R_cylinderMap
      continuous_toFun := continuous_S_R_cylinderMap }

def star_S_L_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := star_S_L_cylinderMap
      continuous_toFun := continuous_star_S_L_cylinderMap }

def star_S_R_cylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := star_S_R_cylinderMap
      continuous_toFun := continuous_star_S_R_cylinderMap }

def zeroCylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := 0
      continuous_toFun := continuous_const }

def cuntzPartitionCylinderTopCatHom :
    TopCat.of CylinderAlgebra ⟶ TopCat.of CylinderAlgebra :=
  TopCat.ofHom
    { toFun := fun g =>
        S_L_cylinderMap (star_S_L_cylinderMap g) +
          S_R_cylinderMap (star_S_R_cylinderMap g)
      continuous_toFun := by
        exact (continuous_S_L_cylinderMap.comp
          continuous_star_S_L_cylinderMap).add
          (continuous_S_R_cylinderMap.comp
            continuous_star_S_R_cylinderMap) }

theorem UHF_boundary_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫
        UHF_boundary_topCatHom =
      UHF_boundary_cylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change UHF_boundary_op g =
    (UHF_boundary_cylinderMap g : BoundaryFunction)
  rfl

theorem UHF_laplacian_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫
        UHF_laplacian_topCatHom =
      UHF_laplacian_cylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change UHF_Laplacian_op g =
    (UHF_Laplacian_cylinderMap g : BoundaryFunction)
  rfl

theorem S_L_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫ S_L_topCatHom =
      S_L_cylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change S_L_op g = (S_L_cylinderMap g : BoundaryFunction)
  rfl

theorem S_R_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫ S_R_topCatHom =
      S_R_cylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change S_R_op g = (S_R_cylinderMap g : BoundaryFunction)
  rfl

theorem star_S_L_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫ star_S_L_topCatHom =
      star_S_L_cylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change star_S_L_op g = (star_S_L_cylinderMap g : BoundaryFunction)
  rfl

theorem star_S_R_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫ star_S_R_topCatHom =
      star_S_R_cylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change star_S_R_op g = (star_S_R_cylinderMap g : BoundaryFunction)
  rfl

theorem UHF_laplacian_cylinderTopCatHom_eq_id :
    UHF_laplacian_cylinderTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.id_app]
  exact UHF_Laplacian_cylinderMap_eq_id g

theorem UHF_boundary_cylinderTopCatHom_comp_eq_zero :
    UHF_boundary_cylinderTopCatHom ≫ UHF_boundary_cylinderTopCatHom =
      zeroCylinderTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app]
  exact UHF_boundary_cylinderMap_sq_zero g

theorem star_UHF_boundary_cylinderTopCatHom_comp_eq_zero :
    star_UHF_boundary_cylinderTopCatHom ≫
        star_UHF_boundary_cylinderTopCatHom =
      zeroCylinderTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app]
  dsimp [star_UHF_boundary_cylinderTopCatHom,
    zeroCylinderTopCatHom]
  exact star_UHF_boundary_cylinderMap_sq_zero g

theorem cuntzPartition_cylinderTopCatHom_eq_id :
    cuntzPartitionCylinderTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.id_app]
  apply Subtype.ext
  change S_L_op (star_S_L_op (g : BoundaryFunction)) +
      S_R_op (star_S_R_op (g : BoundaryFunction)) = (g : BoundaryFunction)
  exact cuntz_partition_op (g : BoundaryFunction)

theorem cuntzPartition_cylinder_function_square :
    cylinderToBoundaryFunctionTopCatHom ≫ cuntzPartitionTopCatHom =
      cuntzPartitionCylinderTopCatHom ≫
        cylinderToBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.comp_app]
  change S_L_op (star_S_L_op (g : BoundaryFunction)) +
      S_R_op (star_S_R_op (g : BoundaryFunction)) =
    ↑(S_L_cylinderMap (star_S_L_cylinderMap g) +
      S_R_cylinderMap (star_S_R_cylinderMap g) : CylinderAlgebra)
  exact rfl

theorem S_L_cylinderTopCatHom_star_comp_eq_id :
    S_L_cylinderTopCatHom ≫ star_S_L_cylinderTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.id_app]
  apply Subtype.ext
  exact star_S_L_op_S_L_op (g : BoundaryFunction)

theorem S_R_cylinderTopCatHom_star_comp_eq_id :
    S_R_cylinderTopCatHom ≫ star_S_R_cylinderTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app, TopCat.id_app]
  apply Subtype.ext
  exact star_S_R_op_S_R_op (g : BoundaryFunction)

theorem S_R_cylinderTopCatHom_star_S_L_comp_eq_zero :
    S_R_cylinderTopCatHom ≫ star_S_L_cylinderTopCatHom =
      zeroCylinderTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app]
  apply Subtype.ext
  exact star_S_L_op_S_R_op (g : BoundaryFunction)

theorem S_L_cylinderTopCatHom_star_S_R_comp_eq_zero :
    S_L_cylinderTopCatHom ≫ star_S_R_cylinderTopCatHom =
      zeroCylinderTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro g
  rw [TopCat.comp_app]
  apply Subtype.ext
  exact star_S_R_op_S_L_op (g : BoundaryFunction)

end InfoGeometry.Canonical.UHFBoundaryCylinderFunctionTopCat
