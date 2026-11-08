import Mathlib.Basic.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Scalar dlog Weights and Finite-Dimensional Wedge Algebra

This module proves identities about scalar reciprocal-coordinate weights, products
with one factor erased, linear functionals, and an explicitly defined wedge
evaluation. It does not define differential forms, a positroid cell, an
analytic Poincaré residue, or a BCFW amplitude. The `poincareResidue*` names
below are historical labels for the corresponding scalar factorization only.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.Canonical.AmplituhedronResidue

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The scalar reciprocal weight associated to a nonzero coordinate. -/
def dlogDensity (α : ℝ) : ℝ := α⁻¹

/-- Positivity of dlog density for interior positive coordinates. -/
theorem dlogDensity_pos {α : ℝ} (hα : 0 < α) : 0 < dlogDensity α := by
  dsimp [dlogDensity]
  exact inv_pos.mpr hα

/-- The total volume density of a d-dimensional positroid cell with coordinates α : Fin d → ℝ. -/
def cellVolumeDensity {d : ℕ} (α : Fin d → ℝ) : ℝ :=
  ∏ i, dlogDensity (α i)

/-- Positivity of total cell volume density in the positive Grassmannian interior. -/
theorem cellVolumeDensity_pos {d : ℕ} (α : Fin d → ℝ) (hα : ∀ i, 0 < α i) :
    0 < cellVolumeDensity α := by
  dsimp [cellVolumeDensity]
  apply Finset.prod_pos
  intro i _
  exact dlogDensity_pos (hα i)

/-- 
  Product of reciprocal weights with coordinate `i` omitted. This is an
  algebraic product, not an analytic residue at `α i = 0`.
-/
def poincareResidueDensity {d : ℕ} (α : Fin d → ℝ) (i : Fin d) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, dlogDensity (α j)

/-- 
  The Residue Factorization of the Cell Volume Density at coordinate boundary i.
  Removing coordinate i factors the density into: (1 / α i) * ∏_{j ≠ i} (1 / α j).
-/
theorem cell_density_residue_factorization {d : ℕ} (α : Fin d → ℝ) (i : Fin d) :
    cellVolumeDensity α = dlogDensity (α i) * poincareResidueDensity α i := by
  dsimp [cellVolumeDensity, poincareResidueDensity]
  exact (Finset.mul_prod_erase univ (fun j => dlogDensity (α j)) (mem_univ i)).symm

/-- 
  Multiplying the full reciprocal-coordinate product by `α i` cancels its
  `i`-th factor whenever that coordinate is nonzero.
-/
theorem bcfw_boundary_residue_cancellation
    {d : ℕ} (α : Fin d → ℝ) (i : Fin d) (hαi : α i ≠ 0) :
    α i * cellVolumeDensity α = poincareResidueDensity α i := by
  rw [cell_density_residue_factorization α i]
  dsimp [dlogDensity]
  rw [← mul_assoc, mul_inv_cancel₀ hαi, one_mul]

/-- 
  Product with coordinates `i` and `j` erased.
-/
def iteratedBoundaryResidueDensity {d : ℕ} (α : Fin d → ℝ) (i j : Fin d) : ℝ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, dlogDensity (α k)

/-- 
  Erasing two coordinates from a finite product is independent of order.
-/
theorem iterated_poincare_residues_commute
    {d : ℕ} (α : Fin d → ℝ) (i j : Fin d) :
    iteratedBoundaryResidueDensity α i j = iteratedBoundaryResidueDensity α j i := by
  dsimp [iteratedBoundaryResidueDensity]
  have h_set : (Finset.univ.erase i).erase j = (Finset.univ.erase j).erase i := by
    ext k
    simp only [mem_erase, mem_univ, and_true]
    tauto
  rw [h_set]

/-!
=============================================================================
PART 2: Differential 2-Forms, Interior Contraction, and Arnold–Cohen Relations
=============================================================================
-/

/-- The wedge product of two linear 1-forms: (α ∧ β)(u, v) = α(u) * β(v) - α(v) * β(u). -/
def wedge (α β : V →ₗ[ℝ] ℝ) (u v : V) : ℝ :=
  α u * β v - α v * β u

/-- Skew-symmetry of the wedge 2-form. -/
theorem wedge_skew (α β : V →ₗ[ℝ] ℝ) (u v : V) :
    wedge α β u v = - wedge α β v u := by
  dsimp [wedge]
  ring

/-- Skew-symmetry with respect to swapping the 1-forms: β ∧ α = - (α ∧ β). -/
theorem wedge_form_skew (α β : V →ₗ[ℝ] ℝ) (u v : V) :
    wedge β α u v = - wedge α β u v := by
  dsimp [wedge]
  ring

/-- The interior contraction of a 2-form by a tangent vector X: (ι_X (α ∧ β))(v) = (α ∧ β)(X, v). -/
def interiorContraction (X : V) (α β : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ where
  toFun := fun v => wedge α β X v
  map_add' := by
    intro u v
    dsimp [wedge]
    rw [map_add, map_add]
    ring
  map_smul' := by
    intro c v
    dsimp [wedge]
    rw [LinearMap.map_smul, LinearMap.map_smul]
    dsimp
    ring

/-- 
  For the explicitly defined wedge evaluation, if α(X) = 1 and β(X) = 0:
    ι_X (α ∧ β) = β.
-/
theorem poincare_residue_contraction
    (X : V) (α β : V →ₗ[ℝ] ℝ)
    (hα : α X = 1) (hβ : β X = 0) :
    interiorContraction X α β = β := by
  ext v
  change α X * β v - α v * β X = β v
  rw [hα, hβ]
  ring

/-- 
  An algebraic identity for the explicitly defined wedge evaluation:
  (α ∧ β) + (β ∧ γ) + (γ ∧ α) = (α - β) ∧ (β - γ).
-/
theorem arnold_cohen_relation (α β γ : V →ₗ[ℝ] ℝ) (u v : V) :
    wedge α β u v + wedge β γ u v + wedge γ α u v =
      wedge (α - β) (β - γ) u v := by
  dsimp [wedge]
  ring

end InfoGeometry.Canonical.AmplituhedronResidue

end noncomputable section
