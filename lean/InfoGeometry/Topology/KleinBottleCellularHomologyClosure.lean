/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCellularEuler

/-!
# Homology readback for the finite Klein cellular model

This file computes the two cohomology ranks of the explicitly defined finite
periodic cellular complex.  It does not identify that finite model with a
Topological quotient; it closes the algebraic homology calculation owned by
`KleinBottleCellularEuler`.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCellularEuler

open InfoGeometry.OperatorAlgebra.FiniteParityComplex

private def edgeCycle : EvenCells := fun i => if i = 1 then 2 else 0

private theorem edgeCycle_ne_zero : edgeCycle ≠ 0 := by
  intro h
  have h' := congrFun h 1
  simp [edgeCycle] at h'

private theorem oddToEven_range_eq_span :
    LinearMap.range oddToEven = ℝ ∙ edgeCycle := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i <;> simp [oddToEven, edgeCycle] <;> ring
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨(fun i => if i = 0 then 1 else 0), ?_⟩
    funext i
    fin_cases i <;> simp [oddToEven, edgeCycle]

private theorem oddToEven_range_finrank :
    Module.finrank ℝ (LinearMap.range oddToEven) = 1 := by
  rw [oddToEven_range_eq_span]
  exact finrank_span_singleton edgeCycle_ne_zero

private theorem oddToEven_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker oddToEven) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker oddToEven
  rw [oddToEven_range_finrank, Module.finrank_fin_fun] at h
  omega

theorem positiveCohomology_finrank :
    Module.finrank ℝ cellularComplex.PositiveCohomology = 1 := by
  have h := cellularComplex.positiveCohomology_finrank_add_range
  have hker : Module.finrank ℝ (LinearMap.ker evenToOdd) = 2 := by
    rw [show evenToOdd = 0 by rfl, LinearMap.ker_zero]
    simpa [EvenCells] using (Module.finrank_fin_fun ℝ (n := 2))
  change Module.finrank ℝ cellularComplex.PositiveCohomology +
      Module.finrank ℝ (LinearMap.range oddToEven) =
      Module.finrank ℝ (LinearMap.ker evenToOdd) at h
  rw [hker, oddToEven_range_finrank] at h
  omega

theorem negativeCohomology_finrank :
    Module.finrank ℝ cellularComplex.NegativeCohomology = 1 := by
  have h := cellularComplex.negativeCohomology_finrank_add_range
  have hker : Module.finrank ℝ (LinearMap.ker oddToEven) = 1 :=
    oddToEven_kernel_finrank
  have hzero : Module.finrank ℝ (LinearMap.range evenToOdd) = 0 := by
    rw [show evenToOdd = 0 by rfl, LinearMap.range_zero]
    simp
  change Module.finrank ℝ cellularComplex.NegativeCohomology +
      Module.finrank ℝ (LinearMap.range evenToOdd) =
      Module.finrank ℝ (LinearMap.ker oddToEven) at h
  rw [hker, hzero] at h
  omega

end InfoGeometry.Topology.KleinBottleCellularEuler

end noncomputable section
