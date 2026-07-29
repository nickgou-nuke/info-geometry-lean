import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Complex
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import InfoGeometry.Canonical.UHFColimitRepresentationBridge

/-!
# Topology of the finite Cuntz boundary operators

The boundary differential owner defines operators on the product function
space `CantorBoundary → ℂ` but intentionally does not choose a Hilbert or
C*-norm.  This owner records the honest product-topological statement: each
branch operator, pullback, differential, and Laplacian is continuous as an
operator on that function space.  The algebraic identities remain those of
`UHFBoundaryExactSequence`.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryOperatorTopology

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge

theorem continuous_S_L_op :
    Continuous (S_L_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) := by
  apply continuous_pi
  intro x
  by_cases h : x 0 = false
  · simp only [S_L_op, h]
    exact continuous_apply (tail x)
  · simp only [S_L_op, h]
    exact continuous_const

theorem continuous_S_R_op :
    Continuous (S_R_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) := by
  apply continuous_pi
  intro x
  by_cases h : x 0 = true
  · simp only [S_R_op, h]
    exact continuous_apply (tail x)
  · simp only [S_R_op, h]
    exact continuous_const

theorem continuous_star_S_L_op :
    Continuous (star_S_L_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) := by
  apply continuous_pi
  intro x
  exact continuous_apply (prependBit false x)

theorem continuous_star_S_R_op :
    Continuous (star_S_R_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) := by
  apply continuous_pi
  intro x
  exact continuous_apply (prependBit true x)

theorem continuous_UHF_boundary_op :
    Continuous (UHF_boundary_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) :=
  continuous_S_L_op.comp continuous_star_S_R_op

theorem continuous_star_UHF_boundary_op :
    Continuous (star_UHF_boundary_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) :=
  continuous_S_R_op.comp continuous_star_S_L_op

theorem continuous_UHF_Laplacian_op :
    Continuous (UHF_Laplacian_op :
      (CantorBoundary → ℂ) → (CantorBoundary → ℂ)) :=
  (continuous_UHF_boundary_op.comp continuous_star_UHF_boundary_op).add
    (continuous_star_UHF_boundary_op.comp continuous_UHF_boundary_op)

/-! Continuous restrictions to the finite-cylinder subalgebra. -/

abbrev CylinderAlgebra := cylinderColimitSubalgebra

def restrictCylinderMap (F : (CantorBoundary → ℂ) → (CantorBoundary → ℂ))
    (hF : ∀ g, g ∈ CylinderColimit → F g ∈ CylinderColimit) :
    CylinderAlgebra → CylinderAlgebra :=
  fun g => ⟨F g, hF g g.property⟩

theorem continuous_restrictCylinderMap
    (F : (CantorBoundary → ℂ) → (CantorBoundary → ℂ))
    (hF : ∀ g, g ∈ CylinderColimit → F g ∈ CylinderColimit)
    (hcont : Continuous F) :
    Continuous (restrictCylinderMap F hF) := by
  apply (hcont.comp continuous_subtype_val).subtype_mk

def S_L_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap S_L_op
    (fun _ hg => S_L_op_preserves_cylinder_colimit hg)

def S_R_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap S_R_op
    (fun _ hg => S_R_op_preserves_cylinder_colimit hg)

def star_S_L_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap star_S_L_op
    (fun _ hg => star_S_L_op_preserves_cylinder_colimit hg)

def star_S_R_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap star_S_R_op
    (fun _ hg => star_S_R_op_preserves_cylinder_colimit hg)

def UHF_boundary_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap UHF_boundary_op
    (fun _ hg => UHF_boundary_op_preserves_cylinder_colimit hg)

def star_UHF_boundary_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap star_UHF_boundary_op
    (fun _ hg => star_UHF_boundary_op_preserves_cylinder_colimit hg)

def UHF_Laplacian_cylinderMap : CylinderAlgebra → CylinderAlgebra :=
  restrictCylinderMap UHF_Laplacian_op
    (fun _ hg => UHF_Laplacian_op_preserves_cylinder_colimit hg)

theorem continuous_S_L_cylinderMap : Continuous S_L_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_S_L_op

theorem continuous_S_R_cylinderMap : Continuous S_R_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_S_R_op

theorem continuous_star_S_L_cylinderMap : Continuous star_S_L_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_star_S_L_op

theorem continuous_star_S_R_cylinderMap : Continuous star_S_R_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_star_S_R_op

theorem continuous_UHF_boundary_cylinderMap :
    Continuous UHF_boundary_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_UHF_boundary_op

theorem continuous_star_UHF_boundary_cylinderMap :
    Continuous star_UHF_boundary_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_star_UHF_boundary_op

theorem continuous_UHF_Laplacian_cylinderMap :
    Continuous UHF_Laplacian_cylinderMap := by
  exact continuous_restrictCylinderMap _ _ continuous_UHF_Laplacian_op

@[simp] theorem S_L_cylinderMap_apply (g : CylinderAlgebra) :
    S_L_cylinderMap g =
      ⟨S_L_op g, S_L_op_preserves_cylinder_colimit g.property⟩ := rfl

@[simp] theorem S_R_cylinderMap_apply (g : CylinderAlgebra) :
    S_R_cylinderMap g =
      ⟨S_R_op g, S_R_op_preserves_cylinder_colimit g.property⟩ := rfl

@[simp] theorem star_S_L_cylinderMap_apply (g : CylinderAlgebra) :
    star_S_L_cylinderMap g =
      ⟨star_S_L_op g, star_S_L_op_preserves_cylinder_colimit g.property⟩ := rfl

@[simp] theorem star_S_R_cylinderMap_apply (g : CylinderAlgebra) :
    star_S_R_cylinderMap g =
      ⟨star_S_R_op g, star_S_R_op_preserves_cylinder_colimit g.property⟩ := rfl

@[simp] theorem UHF_boundary_cylinderMap_apply (g : CylinderAlgebra) :
    UHF_boundary_cylinderMap g =
      ⟨UHF_boundary_op g,
        UHF_boundary_op_preserves_cylinder_colimit g.property⟩ := rfl

@[simp] theorem star_UHF_boundary_cylinderMap_apply (g : CylinderAlgebra) :
    star_UHF_boundary_cylinderMap g =
      ⟨star_UHF_boundary_op g,
        star_UHF_boundary_op_preserves_cylinder_colimit g.property⟩ := rfl

@[simp] theorem UHF_Laplacian_cylinderMap_apply (g : CylinderAlgebra) :
    UHF_Laplacian_cylinderMap g =
      ⟨UHF_Laplacian_op g,
        UHF_Laplacian_op_preserves_cylinder_colimit g.property⟩ := rfl

theorem UHF_boundary_cylinderMap_sq_zero (g : CylinderAlgebra) :
    UHF_boundary_cylinderMap (UHF_boundary_cylinderMap g) = 0 := by
  apply Subtype.ext
  exact UHF_boundary_op_sq_zero g

theorem star_UHF_boundary_cylinderMap_sq_zero (g : CylinderAlgebra) :
    star_UHF_boundary_cylinderMap (star_UHF_boundary_cylinderMap g) = 0 := by
  apply Subtype.ext
  exact star_UHF_boundary_op_sq_zero g

theorem UHF_Laplacian_cylinderMap_eq_id (g : CylinderAlgebra) :
    UHF_Laplacian_cylinderMap g = g := by
  apply Subtype.ext
  exact UHF_Laplacian_op_eq_id g

end InfoGeometry.Canonical.UHFBoundaryOperatorTopology
