/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.MeasureTheory.Function.ContinuousMapDense
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding

/-!
# The finite-cylinder colimit in Bernoulli `L²`

The existing finite-cylinder star algebra is dense in the continuous functions
on Cantor space, and continuous functions are dense in `L²` for the finite
Bernoulli measure. This owner composes those canonical maps, identifies each
finite stage with its existing `L²` representation, and proves dense range.
It concerns the diagonal cylinder system only; it does not identify the full
matrix GNS colimit with boundary `L²`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliCylinderColimitL2

open MeasureTheory
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

/-- The finite-cylinder star algebra represented in the Bernoulli boundary
`L²` space by continuous inclusion followed by `ContinuousMap.toLp`. -/
noncomputable def cylinderColimitToL2 :
    cylinderColimitStarSubalgebra →ₗ[ℂ] L2Boundary :=
  (ContinuousMap.toLp 2 μC ℂ).toLinearMap.comp
    cylinderColimitToContinuousMapStarAlgHom.toLinearMap

/-- On every finite stage, the colimit map is the existing cylinder `L²`
representation. -/
theorem cylinderColimitToL2_stage (n : ℕ) (f : DiagAlg n) :
    cylinderColimitToL2
        ⟨cylinder n f, cylinder_mem_colimit n f⟩ = diagonalCylinderL2 n f := by
  change ContinuousMap.toLp 2 μC ℂ
      (cylinderColimitToContinuousMapStarAlgHom
        ⟨cylinder n f, cylinder_mem_colimit n f⟩) = diagonalCylinderL2 n f
  apply Lp.ext
  have hcontinuous :=
    ContinuousMap.coeFn_toLp (p := 2) (μ := μC) (𝕜 := ℂ)
      (cylinderColimitToContinuousMapStarAlgHom
        ⟨cylinder n f, cylinder_mem_colimit n f⟩)
  have hstage := diagonalCylinderL2_coeFn n f
  filter_upwards [hcontinuous, hstage] with x hcontinuous hstage
  rw [hcontinuous, hstage]
  rfl

/-- The finite-cylinder diagonal colimit is dense in the concrete Bernoulli
boundary `L²` space. -/
theorem cylinderColimitToL2_denseRange :
    DenseRange cylinderColimitToL2 := by
  have hcontinuous : DenseRange
      (cylinderColimitToContinuousMapStarAlgHom :
        cylinderColimitStarSubalgebra → C(Boundary, ℂ)) :=
    cylinderColimitToContinuousMapStarAlgHom_denseRange
  have htoLp : DenseRange
      (ContinuousMap.toLp 2 μC ℂ : C(Boundary, ℂ) →L[ℂ] L2Boundary) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (μ := μC) (𝕜 := ℂ) (p := 2)
      (hp := by norm_num)
  dsimp [cylinderColimitToL2]
  exact htoLp.comp hcontinuous (ContinuousMap.toLp 2 μC ℂ).continuous

end InfoGeometry.Canonical.CantorBernoulliCylinderColimitL2

end
