import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Complex
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import InfoGeometry.Canonical.UHFColimitRepresentationBridge

/-!
# Topology of the finite Cuntz boundary operators

The boundary differential owner defines operators on the product function
space `(ℕ → Bool) → ℂ` but intentionally does not choose a Hilbert or
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
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) := by
  apply continuous_pi
  intro x
  by_cases h : x 0 = false
  · simp only [S_L_op, h]
    exact continuous_apply (tail x)
  · simp only [S_L_op, h]
    exact continuous_const

theorem continuous_S_R_op :
    Continuous (S_R_op :
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) := by
  apply continuous_pi
  intro x
  by_cases h : x 0 = true
  · simp only [S_R_op, h]
    exact continuous_apply (tail x)
  · simp only [S_R_op, h]
    exact continuous_const

theorem continuous_star_S_L_op :
    Continuous (star_S_L_op :
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) := by
  apply continuous_pi
  intro x
  exact continuous_apply (prependBit false x)

theorem continuous_star_S_R_op :
    Continuous (star_S_R_op :
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) := by
  apply continuous_pi
  intro x
  exact continuous_apply (prependBit true x)

theorem continuous_UHF_boundary_op :
    Continuous (UHF_boundary_op :
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) :=
  continuous_S_L_op.comp continuous_star_S_R_op

theorem continuous_star_UHF_boundary_op :
    Continuous (star_UHF_boundary_op :
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) :=
  continuous_S_R_op.comp continuous_star_S_L_op

theorem continuous_UHF_Laplacian_op :
    Continuous (UHF_Laplacian_op :
      ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ)) :=
  (continuous_UHF_boundary_op.comp continuous_star_UHF_boundary_op).add
    (continuous_star_UHF_boundary_op.comp continuous_UHF_boundary_op)

/-! The branch partition also glues continuous boundary functions. -/

theorem branchSet_eq_head (b : Bool) :
    Set.range (prependBit b) = {x : (ℕ → Bool) | x 0 = b} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact prependBit_head b y
  · intro hx
    exact ⟨tail x, prependBit_tail_of_head hx⟩

theorem branchSet_frontier_empty (b : Bool) :
    frontier {x : (ℕ → Bool) | x 0 = b} = ∅ := by
  rw [← branchSet_eq_head b]
  rw [frontier, (prependBit_image_closed b).closure_eq,
    (prependBit_image_clopen b).isOpen.interior_eq]
  simp

theorem continuous_S_L_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (S_L_op f) := by
  change Continuous (fun x => if x 0 = false then f (tail x) else 0)
  apply Continuous.if _
    (hf.comp
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail)
    continuous_const
  intro x hx
  rw [branchSet_frontier_empty false] at hx
  exact False.elim (by exact hx)

theorem continuous_S_R_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (S_R_op f) := by
  change Continuous (fun x => if x 0 = true then f (tail x) else 0)
  apply Continuous.if _
    (hf.comp
      InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_tail)
    continuous_const
  intro x hx
  rw [branchSet_frontier_empty true] at hx
  exact False.elim (by exact hx)

theorem continuous_star_S_L_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (star_S_L_op f) :=
  hf.comp
    (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_prependBit
      false)

theorem continuous_star_S_R_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (star_S_R_op f) :=
  hf.comp
    (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.continuous_prependBit
      true)

theorem continuous_UHF_boundary_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (UHF_boundary_op f) :=
  continuous_S_L_op_of_continuous
    (continuous_star_S_R_op_of_continuous hf)

theorem continuous_star_UHF_boundary_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (star_UHF_boundary_op f) :=
  continuous_S_R_op_of_continuous
    (continuous_star_S_L_op_of_continuous hf)

theorem continuous_UHF_Laplacian_op_of_continuous
    {f : (ℕ → Bool) → ℂ} (hf : Continuous f) :
    Continuous (UHF_Laplacian_op f) :=
  (continuous_UHF_boundary_op_of_continuous
      (continuous_star_UHF_boundary_op_of_continuous hf)).add
    (continuous_star_UHF_boundary_op_of_continuous
      (continuous_UHF_boundary_op_of_continuous hf))

noncomputable def S_L_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := S_L_op f
    continuous_toFun := continuous_S_L_op_of_continuous f.continuous }

noncomputable def S_R_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := S_R_op f
    continuous_toFun := continuous_S_R_op_of_continuous f.continuous }

noncomputable def star_S_L_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := star_S_L_op f
    continuous_toFun := continuous_star_S_L_op_of_continuous f.continuous }

noncomputable def star_S_R_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := star_S_R_op f
    continuous_toFun := continuous_star_S_R_op_of_continuous f.continuous }

noncomputable def UHF_boundary_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := UHF_boundary_op f
    continuous_toFun := continuous_UHF_boundary_op_of_continuous f.continuous }

noncomputable def star_UHF_boundary_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := star_UHF_boundary_op f
    continuous_toFun := continuous_star_UHF_boundary_op_of_continuous f.continuous }

noncomputable def UHF_Laplacian_continuousMap
    (f : C((ℕ → Bool), ℂ)) : C((ℕ → Bool), ℂ) :=
  { toFun := UHF_Laplacian_op f
    continuous_toFun := continuous_UHF_Laplacian_op_of_continuous f.continuous }

@[simp] theorem S_L_continuousMap_apply
    (f : C((ℕ → Bool), ℂ)) (x : (ℕ → Bool)) :
    S_L_continuousMap f x = S_L_op f x := rfl

@[simp] theorem S_R_continuousMap_apply
    (f : C((ℕ → Bool), ℂ)) (x : (ℕ → Bool)) :
    S_R_continuousMap f x = S_R_op f x := rfl

@[simp] theorem star_S_L_continuousMap_apply
    (f : C((ℕ → Bool), ℂ)) (x : (ℕ → Bool)) :
    star_S_L_continuousMap f x = star_S_L_op f x := rfl

@[simp] theorem star_S_R_continuousMap_apply
    (f : C((ℕ → Bool), ℂ)) (x : (ℕ → Bool)) :
    star_S_R_continuousMap f x = star_S_R_op f x := rfl

/-! Cuntz and Hodge identities transported to continuous boundary functions. -/

theorem star_S_L_continuousMap_S_L
    (f : C((ℕ → Bool), ℂ)) :
    star_S_L_continuousMap (S_L_continuousMap f) = f := by
  ext x
  exact congrFun (star_S_L_op_S_L_op f) x

theorem star_S_R_continuousMap_S_R
    (f : C((ℕ → Bool), ℂ)) :
    star_S_R_continuousMap (S_R_continuousMap f) = f := by
  ext x
  exact congrFun (star_S_R_op_S_R_op f) x

theorem S_L_continuousMap_injective :
    Function.Injective S_L_continuousMap := by
  intro f g hfg
  have h := congrArg star_S_L_continuousMap hfg
  simpa only [star_S_L_continuousMap_S_L] using h

theorem S_R_continuousMap_injective :
    Function.Injective S_R_continuousMap := by
  intro f g hfg
  have h := congrArg star_S_R_continuousMap hfg
  simpa only [star_S_R_continuousMap_S_R] using h

theorem star_S_L_continuousMap_S_R
    (f : C((ℕ → Bool), ℂ)) :
    star_S_L_continuousMap (S_R_continuousMap f) = 0 := by
  ext x
  exact congrFun (star_S_L_op_S_R_op f) x

theorem star_S_R_continuousMap_S_L
    (f : C((ℕ → Bool), ℂ)) :
    star_S_R_continuousMap (S_L_continuousMap f) = 0 := by
  ext x
  exact congrFun (star_S_R_op_S_L_op f) x

theorem cuntz_partition_continuousMap
    (f : C((ℕ → Bool), ℂ)) :
    S_L_continuousMap (star_S_L_continuousMap f) +
      S_R_continuousMap (star_S_R_continuousMap f) = f := by
  ext x
  exact congrFun (cuntz_partition_op f) x

theorem UHF_boundary_continuousMap_sq_zero
    (f : C((ℕ → Bool), ℂ)) :
    UHF_boundary_continuousMap (UHF_boundary_continuousMap f) = 0 := by
  ext x
  exact congrFun (UHF_boundary_op_sq_zero f) x

theorem star_UHF_boundary_continuousMap_sq_zero
    (f : C((ℕ → Bool), ℂ)) :
    star_UHF_boundary_continuousMap (star_UHF_boundary_continuousMap f) = 0 := by
  ext x
  exact congrFun
    (InfoGeometry.Canonical.UHFBoundaryExactSequence.star_UHF_boundary_op_sq_zero f) x

theorem UHF_Laplacian_continuousMap_eq_id
    (f : C((ℕ → Bool), ℂ)) :
    UHF_Laplacian_continuousMap f = f := by
  ext x
  exact congrFun (UHF_Laplacian_op_eq_id f) x

/-! Continuous restrictions to the finite-cylinder subalgebra. -/

abbrev CylinderAlgebra := cylinderColimitSubalgebra

def restrictCylinderMap (F : ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ))
    (hF : ∀ g, g ∈ CylinderColimit → F g ∈ CylinderColimit) :
    CylinderAlgebra → CylinderAlgebra :=
  fun g => ⟨F g, hF g g.property⟩

theorem continuous_restrictCylinderMap
    (F : ((ℕ → Bool) → ℂ) → ((ℕ → Bool) → ℂ))
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

theorem cylinderContinuousMap_S_L_intertwines
    (g : CylinderAlgebra) :
    S_L_continuousMap (cylinderContinuousMap g) =
      cylinderContinuousMap (S_L_cylinderMap g) := by
  ext x
  rfl

theorem cylinderContinuousMap_S_R_intertwines
    (g : CylinderAlgebra) :
    S_R_continuousMap (cylinderContinuousMap g) =
      cylinderContinuousMap (S_R_cylinderMap g) := by
  ext x
  rfl

theorem cylinderContinuousMap_star_S_L_intertwines
    (g : CylinderAlgebra) :
    star_S_L_continuousMap (cylinderContinuousMap g) =
      cylinderContinuousMap (star_S_L_cylinderMap g) := by
  ext x
  rfl

theorem cylinderContinuousMap_star_S_R_intertwines
    (g : CylinderAlgebra) :
    star_S_R_continuousMap (cylinderContinuousMap g) =
      cylinderContinuousMap (star_S_R_cylinderMap g) := by
  ext x
  rfl

theorem UHF_boundary_cylinderMap_sq_zero (g : CylinderAlgebra) :
    UHF_boundary_cylinderMap (UHF_boundary_cylinderMap g) = 0 := by
  apply Subtype.ext
  exact UHF_boundary_op_sq_zero g

theorem star_UHF_boundary_cylinderMap_sq_zero (g : CylinderAlgebra) :
    star_UHF_boundary_cylinderMap (star_UHF_boundary_cylinderMap g) = 0 := by
  apply Subtype.ext
  exact
    InfoGeometry.Canonical.UHFBoundaryExactSequence.star_UHF_boundary_op_sq_zero g

theorem UHF_Laplacian_cylinderMap_eq_id (g : CylinderAlgebra) :
    UHF_Laplacian_cylinderMap g = g := by
  apply Subtype.ext
  exact UHF_Laplacian_op_eq_id g

end InfoGeometry.Canonical.UHFBoundaryOperatorTopology
