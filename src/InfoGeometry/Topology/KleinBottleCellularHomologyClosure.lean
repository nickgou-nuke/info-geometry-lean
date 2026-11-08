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
topological quotient; it closes the algebraic homology calculation owned by
`KleinBottleCellularEuler`.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCellularEuler

open InfoGeometry.OperatorAlgebra.FiniteParityComplex
open InfoGeometry.Topology.KleinBottleCWChain

private theorem oddToEven_zero : oddToEven = 0 := by
  apply LinearMap.ext
  intro x
  change (KleinBottleCWChain.boundary₁ x, (0 : C2)) = 0
  simp [KleinBottleCWChain.boundary₁]

private theorem oddToEven_range_finrank :
    Module.finrank ℝ (LinearMap.range oddToEven) = 0 := by
  rw [oddToEven_zero, LinearMap.range_zero]
  simp

private theorem oddToEven_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker oddToEven) = 2 := by
  rw [oddToEven_zero, LinearMap.ker_zero]
  simp [C1]

private theorem evenToOdd_range_finrank :
    Module.finrank ℝ (LinearMap.range evenToOdd) = 1 := by
  rw [evenToOdd_range_eq_polygonBoundary₂]
  exact boundary₂_range_finrank

private theorem evenToOdd_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker evenToOdd) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker evenToOdd
  rw [evenToOdd_range_finrank] at h
  have hEven : Module.finrank ℝ EvenCells = 2 := by
    simp [EvenCells, C0, C2]
  omega

theorem positiveCohomology_finrank :
    Module.finrank ℝ polygonParityComplex.PositiveCohomology = 1 := by
  have h := polygonParityComplex.positiveCohomology_finrank_add_range
  change Module.finrank ℝ polygonParityComplex.PositiveCohomology +
      Module.finrank ℝ (LinearMap.range oddToEven) =
      Module.finrank ℝ (LinearMap.ker evenToOdd) at h
  rw [oddToEven_range_finrank, evenToOdd_kernel_finrank] at h
  omega

theorem negativeCohomology_finrank :
    Module.finrank ℝ polygonParityComplex.NegativeCohomology = 1 := by
  have h := polygonParityComplex.negativeCohomology_finrank_add_range
  change Module.finrank ℝ polygonParityComplex.NegativeCohomology +
      Module.finrank ℝ (LinearMap.range evenToOdd) =
      Module.finrank ℝ (LinearMap.ker oddToEven) at h
  rw [evenToOdd_range_finrank, oddToEven_kernel_finrank] at h
  omega

end InfoGeometry.Topology.KleinBottleCellularEuler

end noncomputable section
