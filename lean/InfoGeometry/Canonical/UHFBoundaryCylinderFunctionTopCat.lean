import InfoGeometry.Canonical.UHFBoundaryFunctionOperatorTopCat
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

end InfoGeometry.Canonical.UHFBoundaryCylinderFunctionTopCat
