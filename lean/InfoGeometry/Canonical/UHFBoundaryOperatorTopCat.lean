import InfoGeometry.Canonical.UHFBoundaryOperatorTopology
import Mathlib.Topology.Category.TopCat.Basic

/-!
# TopCat interface for the Cantor-boundary Cuntz operators

The product-topological operator owner already proves continuity of the branch
maps and the UHF Laplacian.  This file promotes those maps to categorical
endomorphisms and transports the exact Cuntz inverse and Laplacian identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryOperatorTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBoundaryOperatorTopology
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.UHFBoundaryExactSequence

def S_L_opTopCatHom :
    TopCat.of ((ℕ → Bool) → ℂ) ⟶ TopCat.of ((ℕ → Bool) → ℂ) :=
  TopCat.ofHom
    { toFun := S_L_op
      continuous_toFun := continuous_S_L_op }

def S_R_opTopCatHom :
    TopCat.of ((ℕ → Bool) → ℂ) ⟶ TopCat.of ((ℕ → Bool) → ℂ) :=
  TopCat.ofHom
    { toFun := S_R_op
      continuous_toFun := continuous_S_R_op }

def star_S_L_opTopCatHom :
    TopCat.of ((ℕ → Bool) → ℂ) ⟶ TopCat.of ((ℕ → Bool) → ℂ) :=
  TopCat.ofHom
    { toFun := star_S_L_op
      continuous_toFun := continuous_star_S_L_op }

def star_S_R_opTopCatHom :
    TopCat.of ((ℕ → Bool) → ℂ) ⟶ TopCat.of ((ℕ → Bool) → ℂ) :=
  TopCat.ofHom
    { toFun := star_S_R_op
      continuous_toFun := continuous_star_S_R_op }

def UHF_boundary_topCatHom :
    TopCat.of ((ℕ → Bool) → ℂ) ⟶ TopCat.of ((ℕ → Bool) → ℂ) :=
  TopCat.ofHom
    { toFun := UHF_boundary_op
      continuous_toFun := continuous_UHF_boundary_op }

def UHF_Laplacian_opTopCatHom :
    TopCat.of ((ℕ → Bool) → ℂ) ⟶ TopCat.of ((ℕ → Bool) → ℂ) :=
  TopCat.ofHom
    { toFun := UHF_Laplacian_op
      continuous_toFun := continuous_UHF_Laplacian_op }

@[simp] theorem UHF_Laplacian_opTopCatHom_apply (f : (ℕ → Bool) → ℂ) :
    UHF_Laplacian_opTopCatHom f = UHF_Laplacian_op f := by
  rfl

@[simp] theorem S_L_opTopCatHom_apply (f : (ℕ → Bool) → ℂ) :
    S_L_opTopCatHom f = S_L_op f := by
  rfl

@[simp] theorem S_R_opTopCatHom_apply (f : (ℕ → Bool) → ℂ) :
    S_R_opTopCatHom f = S_R_op f := by
  rfl

@[simp] theorem star_S_L_opTopCatHom_apply (f : (ℕ → Bool) → ℂ) :
    star_S_L_opTopCatHom f = star_S_L_op f := by
  rfl

@[simp] theorem star_S_R_opTopCatHom_apply (f : (ℕ → Bool) → ℂ) :
    star_S_R_opTopCatHom f = star_S_R_op f := by
  rfl

theorem star_S_L_opTopCatHom_comp_S_L_opTopCatHom :
    S_L_opTopCatHom ≫ star_S_L_opTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  change star_S_L_op (S_L_op f) = f
  exact star_S_L_op_S_L_op f

theorem star_S_R_opTopCatHom_comp_S_R_opTopCatHom :
    S_R_opTopCatHom ≫ star_S_R_opTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  change star_S_R_op (S_R_op f) = f
  exact star_S_R_op_S_R_op f

theorem UHF_Laplacian_opTopCatHom_eq_id :
    UHF_Laplacian_opTopCatHom = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  change UHF_Laplacian_op f = f
  exact UHF_Laplacian_op_eq_id f

end InfoGeometry.Canonical.UHFBoundaryOperatorTopCat
