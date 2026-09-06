import InfoGeometry.Thermo.ModularKLDivergence

/-!
# Canonical Modular KL scale/shape wrapper (constructive)

This module keeps a theorem-facing entry point for the scale/shape split while
remaining fully constructive (no `sorry`).

Current kernel-checked lane is the owner `PositiveMeasure` surface used
throughout the repo:

`generalizedKL μ ν = Z μ * generalizedKL (normalize μ) (normalize ν) + gklTerm (Z μ) (Z ν)`.

The infinite-measure extension remains an explicit open problem and must be
added with a concrete witness theorem before this file is broadened again.
-/

namespace InfoGeometry.Canonical.DimensionAgnosticModularKLDivergence

open InfoGeometry
open InfoGeometry.PositiveMeasure
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Projective (shape) term on normalized rays. -/
noncomputable def activeShapeTerm (μ ν : PositiveMeasure α ℝ) : ℝ :=
  Z (α := α) (R := ℝ) μ
    * generalizedKL (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν)

/-- Radial/gauge (mass) term. -/
noncomputable def kernelMassTerm (μ ν : PositiveMeasure α ℝ) : ℝ :=
  gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν)

/--
Constructive scale/shape split on the owner positive-measure lane.
-/
theorem generalizedKL_scale_shape_split (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν = activeShapeTerm (α := α) μ ν + kernelMassTerm (α := α) μ ν := by
  simpa [activeShapeTerm, kernelMassTerm] using
    InfoGeometry.Thermo.ModularKLDivergence.generalizedKL_scale_shape_split (α := α) μ ν

end InfoGeometry.Canonical.DimensionAgnosticModularKLDivergence
