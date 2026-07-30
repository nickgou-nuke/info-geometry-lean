import InfoGeometry.Canonical.UHFBoundaryOperatorTopology
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` boundary-function operators

The product-topological boundary function space already carries continuous
Cuntz branch operators.  This owner exposes those operators as categorical
endomorphisms, without adding a norm or Hilbert completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryFunctionOperatorTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBoundaryOperatorTopology
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.UHFBoundaryExactSequence

abbrev BoundaryFunction := CantorBoundary → ℂ

def S_L_topCatHom : TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := S_L_op
      continuous_toFun := continuous_S_L_op }

def S_R_topCatHom : TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := S_R_op
      continuous_toFun := continuous_S_R_op }

def star_S_L_topCatHom : TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := star_S_L_op
      continuous_toFun := continuous_star_S_L_op }

def star_S_R_topCatHom : TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := star_S_R_op
      continuous_toFun := continuous_star_S_R_op }

def UHF_boundary_topCatHom : TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := UHF_boundary_op
      continuous_toFun := continuous_UHF_boundary_op }

def star_UHF_boundary_topCatHom :
    TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := star_UHF_boundary_op
      continuous_toFun := continuous_star_UHF_boundary_op }

def UHF_laplacian_topCatHom :
    TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := UHF_Laplacian_op
      continuous_toFun := continuous_UHF_Laplacian_op }

def zeroBoundaryFunctionTopCatHom :
    TopCat.of BoundaryFunction ⟶ TopCat.of BoundaryFunction :=
  TopCat.ofHom
    { toFun := fun _ => 0
      continuous_toFun := continuous_const }

theorem star_S_L_topCatHom_S_L (f : BoundaryFunction) :
    (S_L_topCatHom ≫ star_S_L_topCatHom) f = f := by
  rw [TopCat.comp_app]
  change star_S_L_op (S_L_op f) = f
  exact star_S_L_op_S_L_op f

theorem star_S_R_topCatHom_S_R (f : BoundaryFunction) :
    (S_R_topCatHom ≫ star_S_R_topCatHom) f = f := by
  rw [TopCat.comp_app]
  change star_S_R_op (S_R_op f) = f
  exact star_S_R_op_S_R_op f

theorem star_S_L_topCatHom_S_R (f : BoundaryFunction) :
    (S_R_topCatHom ≫ star_S_L_topCatHom) f = 0 := by
  rw [TopCat.comp_app]
  change star_S_L_op (S_R_op f) = 0
  exact star_S_L_op_S_R_op f

theorem star_S_R_topCatHom_S_L (f : BoundaryFunction) :
    (S_L_topCatHom ≫ star_S_R_topCatHom) f = 0 := by
  rw [TopCat.comp_app]
  change star_S_R_op (S_L_op f) = 0
  exact star_S_R_op_S_L_op f

theorem UHF_boundary_topCatHom_sq_zero (f : BoundaryFunction) :
    (UHF_boundary_topCatHom ≫ UHF_boundary_topCatHom) f = 0 := by
  rw [TopCat.comp_app]
  change UHF_boundary_op (UHF_boundary_op f) = 0
  exact UHF_boundary_op_sq_zero f

theorem star_UHF_boundary_topCatHom_sq_zero (f : BoundaryFunction) :
    (star_UHF_boundary_topCatHom ≫ star_UHF_boundary_topCatHom) f = 0 := by
  rw [TopCat.comp_app]
  change star_UHF_boundary_op (star_UHF_boundary_op f) = 0
  exact star_UHF_boundary_op_sq_zero f

theorem UHF_laplacian_topCatHom_apply (f : BoundaryFunction) :
    UHF_laplacian_topCatHom f = f := by
  change UHF_Laplacian_op f = f
  exact UHF_Laplacian_op_eq_id f

theorem S_L_topCatHom_star_comp_eq_id :
    S_L_topCatHom ≫ star_S_L_topCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  rw [TopCat.comp_app, TopCat.id_app]
  exact star_S_L_topCatHom_S_L f

theorem S_R_topCatHom_star_comp_eq_id :
    S_R_topCatHom ≫ star_S_R_topCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  rw [TopCat.comp_app, TopCat.id_app]
  exact star_S_R_topCatHom_S_R f

theorem UHF_laplacian_topCatHom_eq_id :
    UHF_laplacian_topCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  rw [TopCat.id_app]
  exact UHF_laplacian_topCatHom_apply f

theorem S_R_topCatHom_star_S_L_comp_eq_zero :
    S_R_topCatHom ≫ star_S_L_topCatHom = zeroBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  rw [TopCat.comp_app]
  change star_S_L_op (S_R_op f) = 0
  exact star_S_L_op_S_R_op f

theorem S_L_topCatHom_star_S_R_comp_eq_zero :
    S_L_topCatHom ≫ star_S_R_topCatHom = zeroBoundaryFunctionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  rw [TopCat.comp_app]
  change star_S_R_op (S_L_op f) = 0
  exact star_S_R_op_S_L_op f

end InfoGeometry.Canonical.UHFBoundaryFunctionOperatorTopCat
