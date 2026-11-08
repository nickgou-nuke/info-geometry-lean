/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GradedGraphCocycle
import InfoGeometry.SuperGrassmannian.GraphTransitionScalarExtension
import InfoGeometry.SuperGrassmannian.GraphChartOddRegression

/-!
# Nonvacuity and overlap failure

Shears act on arbitrary module maps, and an even shear with genuine exterior
coefficients moves the zero graph to the nonzero odd graph. In contrast, the
invertible swap of two equal summands sends the zero graph outside the chart.
-/

namespace InfoGeometry.SuperGrassmannian.GraphOverlapRegression

open GradedGraphChart GraphChartCocycle GraphChartBaseChange FreeSupermoduleChart

variable {A U W : Type*} [Ring A]
  [AddCommGroup U] [Module A U] [AddCommGroup W] [Module A W]

/-- An actual invertible change of coordinates, defined on arbitrary modules. -/
def lowerShear (s : U →ₗ[A] W) : (U × W) ≃ₗ[A] (U × W) where
  toLinearMap := (LinearMap.fst A U W).prod (s.coprod LinearMap.id)
  invFun z := (z.1, z.2 - s z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- Every graph lies in a lower-shear overlap. -/
theorem lowerShear_overlap (s f : U →ₗ[A] W) : Overlap (lowerShear s).toLinearMap f :=
  Function.bijective_id

/-- The fractional formula reduces to translation by the shear parameter. -/
theorem lowerShear_transition (s f : U →ₗ[A] W) :
    transition (lowerShear s).toLinearMap f (lowerShear_overlap s f) = s + f := by
  apply LinearMap.ext
  intro x
  exact transition_denominator (lowerShear s).toLinearMap f (lowerShear_overlap s f) x

/-- An even parameter gives an even ambient shear. -/
theorem lowerShear_even {k ι : Type*} [CommRing k] [Module k U] [Module k W]
    (GU : ι → Submodule k U) (GW : ι → Submodule k W) (s : U →ₗ[A] W)
    (hs : PreservesDegree GU GW s) :
    PreservesDegree (fun i => (GU i).prod (GW i))
      (fun i => (GU i).prod (GW i)) (lowerShear s).toLinearMap := by
  intro i z hz
  exact ⟨hz.1, (GW i).add_mem (hs i z.1 hz.1) hz.2⟩

/-- The swap overlap is exactly invertibility of the graph map. -/
theorem swap_overlap_iff (f : Module.End A U) :
    Overlap (LinearEquiv.prodComm A U U).toLinearMap f ↔ Function.Bijective f := Iff.rfl

/-- Invertible ambient changes do not preserve a single chart globally. -/
theorem swap_zero_not_overlap [Nontrivial U] :
    ¬ Overlap (LinearEquiv.prodComm A U U).toLinearMap (0 : Module.End A U) := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : U)
  exact hx (h.injective (show (0 : Module.End A U) x = (0 : Module.End A U) 0 from rfl))

/-- On its genuine domain, the swap transition is the inverse operator. -/
theorem swap_transition (u : U ≃ₗ[A] U) :
    transition (LinearEquiv.prodComm A U U).toLinearMap u.toLinearMap u.bijective =
      u.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  have h := transition_denominator (LinearEquiv.prodComm A U U).toLinearMap
    u.toLinearMap u.bijective (u.symm x)
  simpa [denominator, numerator] using h

section Exterior

open GraphChartOddRegression

variable (k : Type*) [CommRing k]

/-- A nontrivial odd coefficient supplies an actual even ambient shear. -/
theorem odd_shear_even :
    PreservesDegree
      (fun i => (freeGrade (coeffGrade k) (fun _ : Fin 1 => 0) i).prod
        (freeGrade (coeffGrade k) (fun _ : Fin 1 => 1) i))
      (fun i => (freeGrade (coeffGrade k) (fun _ : Fin 1 => 0) i).prod
        (freeGrade (coeffGrade k) (fun _ : Fin 1 => 1) i))
      (lowerShear (coordinateLinearMap (fun _ _ : Fin 1 => theta k))).toLinearMap := by
  apply lowerShear_even
  apply coordinate_preservesDegree
  intro i j
  simpa using theta_odd k

/-- This graded coordinate change moves the zero submodule to the genuine odd point. -/
theorem odd_shear_moves_zero :
    (zeroPoint k).val.map
      (lowerShear (coordinateLinearMap (fun _ _ : Fin 1 => theta k))).toLinearMap =
        (oddPoint k).val := by
  have hz : coordinateLinearMap (fun _ _ : Fin 1 => (0 : Coeff k)) = 0 := by
    ext x j
    simp
  simp only [zeroPoint, oddPoint, coefficientChartEquiv_submodule, hz]
  rw [transition_graph _ _ (lowerShear_overlap _ _), lowerShear_transition, add_zero]

end Exterior
end InfoGeometry.SuperGrassmannian.GraphOverlapRegression
