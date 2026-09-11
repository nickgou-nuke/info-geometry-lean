import Mathlib.LinearAlgebra.TensorProduct.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic

open scoped TensorProduct

namespace InfoGeometry.Topology.CFT

/-- The tensor decomposition of a 2D CFT state space into independent
left-moving and right-moving (holomorphic and anti-holomorphic) factors.
Here `V_L` represents the left-moving sector, and `V_R` the right-moving sector. -/
structure ChiralStateSpace (V_L V_R : Type*)
  [AddCommGroup V_L] [Module ℂ V_L]
  [AddCommGroup V_R] [Module ℂ V_R] where
  /-- The Virasoro generators for the left-moving (holomorphic) sector -/
  L : ℤ → (V_L →ₗ[ℂ] V_L)
  /-- The Virasoro generators for the right-moving (anti-holomorphic) sector -/
  Lbar : ℤ → (V_R →ₗ[ℂ] V_R)
  /-- The central charge of the left-moving sector -/
  c_L : ℂ
  /-- The central charge of the right-moving sector -/
  c_R : ℂ

variable {V_L V_R : Type*}
  [AddCommGroup V_L] [Module ℂ V_L]
  [AddCommGroup V_R] [Module ℂ V_R]

/-- A property of an operator on the total state space to be "left chiral".
It means the operator acts exclusively on the left factor, taking the form O_L ⊗ id_R. -/
def IsLeftChiralOperator (O : (V_L ⊗[ℂ] V_R) →ₗ[ℂ] (V_L ⊗[ℂ] V_R)) : Prop :=
  ∃ (O_L : V_L →ₗ[ℂ] V_L), O = TensorProduct.map O_L (LinearMap.id : V_R →ₗ[ℂ] V_R)

/-- A property of an operator on the total state space to be "right chiral".
It means the operator acts exclusively on the right factor, taking the form id_L ⊗ O_R. -/
def IsRightChiralOperator (O : (V_L ⊗[ℂ] V_R) →ₗ[ℂ] (V_L ⊗[ℂ] V_R)) : Prop :=
  ∃ (O_R : V_R →ₗ[ℂ] V_R), O = TensorProduct.map (LinearMap.id : V_L →ₗ[ℂ] V_L) O_R

variable (cft : ChiralStateSpace V_L V_R)

/-- The total Virasoro generators acting on the full state space.
The left generators L_n act as L_n ⊗ id. -/
def totalL (n : ℤ) : (V_L ⊗[ℂ] V_R) →ₗ[ℂ] (V_L ⊗[ℂ] V_R) :=
  TensorProduct.map (cft.L n) (LinearMap.id : V_R →ₗ[ℂ] V_R)

/-- The right generators \bar{L}_n act as id ⊗ \bar{L}_n. -/
def totalLbar (n : ℤ) : (V_L ⊗[ℂ] V_R) →ₗ[ℂ] (V_L ⊗[ℂ] V_R) :=
  TensorProduct.map (LinearMap.id : V_L →ₗ[ℂ] V_L) (cft.Lbar n)

/-- Proof that totalL is a left chiral operator by definition. -/
theorem totalL_is_left_chiral (n : ℤ) : IsLeftChiralOperator (totalL cft n) :=
  ⟨cft.L n, rfl⟩

/-- Proof that totalLbar is a right chiral operator by definition. -/
theorem totalLbar_is_right_chiral (n : ℤ) : IsRightChiralOperator (totalLbar cft n) :=
  ⟨cft.Lbar n, rfl⟩

/-- Two chiral operators from opposite sectors commute. -/
theorem left_right_chiral_commute (O_L O_R : (V_L ⊗[ℂ] V_R) →ₗ[ℂ] (V_L ⊗[ℂ] V_R))
    (hL : IsLeftChiralOperator O_L) (hR : IsRightChiralOperator O_R) :
    O_L ∘ₗ O_R = O_R ∘ₗ O_L := by
  obtain ⟨O_L', rfl⟩ := hL
  obtain ⟨O_R', rfl⟩ := hR
  -- Left chiral operator is O_L' ⊗ id, right chiral operator is id ⊗ O_R'
  -- Their composition in either order is O_L' ⊗ O_R'
  ext x
  simp [LinearMap.comp_apply, TensorProduct.map_map]

/-- The structural definition of a 2D Chiral Conformal Field Theory,
incorporating the primary state and field aspects on top of the chiral spaces. -/
structure ChiralCFT (V_L V_R : Type*)
  [AddCommGroup V_L] [Module ℂ V_L]
  [AddCommGroup V_R] [Module ℂ V_R] extends ChiralStateSpace V_L V_R where
  /-- Vacuum state for the left sector -/
  vacuum_L : V_L
  /-- Vacuum state for the right sector -/
  vacuum_R : V_R
  /-- Invariance of the left vacuum under global conformal transformations -/
  vacuum_L_inv_zero : L 0 vacuum_L = 0
  vacuum_L_inv_one : L 1 vacuum_L = 0
  vacuum_L_inv_neg_one : L (-1) vacuum_L = 0
  /-- Invariance of the right vacuum under global conformal transformations -/
  vacuum_R_inv_zero : Lbar 0 vacuum_R = 0
  vacuum_R_inv_one : Lbar 1 vacuum_R = 0
  vacuum_R_inv_neg_one : Lbar (-1) vacuum_R = 0

end InfoGeometry.Topology.CFT
