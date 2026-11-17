/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.ProjectedGramDissipation
import InfoGeometry.Canonical.SplitOctonionRegularOperators
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Associator Gram operators in chosen positive coordinates

The coordinate equivalence is explicit. The bounded maps themselves are
constructed from the existing right-regular multiplication defect; their
associator action is proved rather than assumed. Finite dimensionality of the
positive coordinate space supplies continuity after transport. No norm or
topology is installed on the source split-octonion type.

The positive inner product is a coordinate choice. It is neither the indefinite
split composition form nor a claimed canonical physical observer. This owner
asserts algebraic operator identities, not differential evolution or heat laws.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace BigOperators

namespace InfoGeometry.Analysis.SplitOctonionProjectedGram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- The right-regular associator defect transported to positive coordinates.
Its domain is finite-dimensional, so the actual linear map is continuous. -/
def associatorMap (e : SplitOctonion ≃ₗ[ℝ] H) (a b : SplitOctonion) : H →L[ℝ] H :=
  LinearMap.toContinuousLinearMap
    (e.toLinearMap.comp
      (((SplitOctonion.rightRegular b).comp (SplitOctonion.rightRegular a) -
        SplitOctonion.rightRegular (a * b)).comp e.symm.toLinearMap))

/-- This formula retains the original multiplication order and parentheses. -/
theorem associatorMap_apply (e : SplitOctonion ≃ₗ[ℝ] H)
    (a b : SplitOctonion) (x : H) :
    associatorMap e a b x = e (SplitOctonion.associator (e.symm x) a b) := by
  change e (SplitOctonion.rightRegular b
      (SplitOctonion.rightRegular a (e.symm x)) -
      SplitOctonion.rightRegular (a * b) (e.symm x)) = _
  rw [SplitOctonion.rightRegular_comp_defect_apply]

theorem associatorMap_apply_coordinate (e : SplitOctonion ≃ₗ[ℝ] H)
    (a b v : SplitOctonion) :
    associatorMap e a b (e v) = e (SplitOctonion.associator v a b) := by
  rw [associatorMap_apply, e.symm_apply_apply]

theorem associatorMap_apply_eq_zero_iff (e : SplitOctonion ≃ₗ[ℝ] H)
    (a b : SplitOctonion) (x : H) :
    associatorMap e a b x = 0 ↔ SplitOctonion.associator (e.symm x) a b = 0 := by
  rw [associatorMap_apply, e.map_eq_zero_iff]

variable {ι : Type*} [Fintype ι]

/-- The projected Gram construction for every ordered pair of the supplied
actual split-octonion generators. -/
def associatorDissipator (e : SplitOctonion ≃ₗ[ℝ] H) (γ : ℝ) (h : H)
    (g : ι → SplitOctonion) : H →L[ℝ] H :=
  ProjectedGramDissipation.dissipator γ h
    (fun p : ι × ι => associatorMap e (g p.1) (g p.2))

theorem associatorDissipator_isPositive (e : SplitOctonion ≃ₗ[ℝ] H)
    (γ : ℝ) (hγ : 0 ≤ γ) (h : H) (g : ι → SplitOctonion) :
    (associatorDissipator e γ h g).IsPositive :=
  ProjectedGramDissipation.dissipator_isPositive γ hγ h _

@[simp] theorem associatorDissipator_energy (e : SplitOctonion ≃ₗ[ℝ] H)
    (γ : ℝ) (h : H) (g : ι → SplitOctonion) :
    associatorDissipator e γ h g h = 0 :=
  ProjectedGramDissipation.dissipator_energy γ h _

theorem inner_associatorDissipator_self (e : SplitOctonion ≃ₗ[ℝ] H)
    (γ : ℝ) (h : H) (g : ι → SplitOctonion) (x : H) :
    ⟪x, associatorDissipator e γ h g x⟫_ℝ =
      γ * ∑ p : ι × ι,
        ‖e (SplitOctonion.associator
          (e.symm (ProjectedGramDissipation.energyProjection h x))
          (g p.1) (g p.2))‖ ^ 2 := by
  simpa only [associatorDissipator, associatorMap_apply] using
    (ProjectedGramDissipation.inner_dissipator_self γ h
      (fun p : ι × ι => associatorMap e (g p.1) (g p.2)) x)

/-- For a nonzero rate, vanishing is exactly the joint associator kernel after
the energy projection. No associative-subspace shortcut is assumed. -/
theorem inner_associatorDissipator_self_eq_zero_iff
    (e : SplitOctonion ≃ₗ[ℝ] H) (γ : ℝ) (hγ : γ ≠ 0) (h : H)
    (g : ι → SplitOctonion) (x : H) :
    ⟪x, associatorDissipator e γ h g x⟫_ℝ = 0 ↔
      ∀ a b, SplitOctonion.associator
        (e.symm (ProjectedGramDissipation.energyProjection h x)) (g a) (g b) = 0 := by
  simpa only [associatorDissipator, associatorMap_apply_eq_zero_iff, Prod.forall] using
    (ProjectedGramDissipation.inner_dissipator_self_eq_zero_iff γ hγ h
      (fun p : ι × ι => associatorMap e (g p.1) (g p.2)) x)

theorem associatorDissipator_apply_eq_zero_iff
    (e : SplitOctonion ≃ₗ[ℝ] H) (γ : ℝ) (hγ : γ ≠ 0) (h : H)
    (g : ι → SplitOctonion) (x : H) :
    associatorDissipator e γ h g x = 0 ↔
      ∀ a b, SplitOctonion.associator
        (e.symm (ProjectedGramDissipation.energyProjection h x)) (g a) (g b) = 0 := by
  simpa only [associatorDissipator, associatorMap_apply_eq_zero_iff, Prod.forall] using
    (ProjectedGramDissipation.dissipator_apply_eq_zero_iff γ hγ h
      (fun p : ι × ι => associatorMap e (g p.1) (g p.2)) x)

namespace QuaternionPairWitness

/-- The quaternion `j` in the first component of the existing pair model. -/
def j : SplitOctonion := ⟨⟨0, 0, 1, 0⟩, 0⟩

/-- The doubling direction in the existing pair model. -/
def ell : SplitOctonion := ⟨0, 1⟩

/-- The product `i * ell`, written in the existing pair coordinates. -/
def iell : SplitOctonion := ⟨0, ⟨0, 1, 0, 0⟩⟩

/-- The quaternion `k` in the first component of the existing pair model. -/
def k : SplitOctonion := ⟨⟨0, 0, 0, 1⟩, 0⟩

/-- The exact ambient associator is nonzero despite `j` having zero second
quaternion component. The calculation reduces to native real components. -/
theorem associator_j_ell_iell :
    SplitOctonion.associator j ell iell = (-2 : ℝ) • k := by
  apply SplitOctonion.ext <;>
    apply QuaternionAlgebra.ext <;>
    norm_num [SplitOctonion.associator, j, ell, iell, k,
      SplitOctonion.mul_a, SplitOctonion.mul_b]

theorem associator_j_ell_iell_ne_zero :
    SplitOctonion.associator j ell iell ≠ 0 := by
  intro hzero
  have hk := congrArg (fun z : SplitOctonion => z.a.imK) hzero
  rw [associator_j_ell_iell] at hk
  norm_num [k] at hk

theorem associatorMap_ell_iell_apply_j_ne_zero
    (e : SplitOctonion ≃ₗ[ℝ] H) :
    associatorMap e ell iell (e j) ≠ 0 := by
  intro hzero
  rw [associatorMap_apply_coordinate] at hzero
  exact associator_j_ell_iell_ne_zero (e.map_eq_zero_iff.mp hzero)

theorem associatorMap_ell_iell_ne_zero
    (e : SplitOctonion ≃ₗ[ℝ] H) : associatorMap e ell iell ≠ 0 := by
  intro hzero
  apply associatorMap_ell_iell_apply_j_ne_zero e
  simp [hzero]

end QuaternionPairWitness

end InfoGeometry.Analysis.SplitOctonionProjectedGram
