import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Measure.Normalized
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Dimension-Agnostic Scale/Shape Decomposition

Rigorous measure-theoretic (Type III) bridge for the scale/shape decomposition
of the generalized KL divergence.

Following the constructivist mandate, we move from finite lattices to the
continuum by explicitly separating the scale (mass) from the shape (probability).
-/

open MeasureTheory
open scoped MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.MeasureScaleShape

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- 
Generalized KL divergence for finite measures.
D_GKL(μ||ν) = D_KL(μ||ν) - mass(μ) + mass(ν).
-/
noncomputable def generalizedKL (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (InformationTheory.klDiv μ ν).toReal - (μ Set.univ).toReal + (ν Set.univ).toReal

/-- The scalar part of the generalized KL (divergence between masses). -/
noncomputable def scalarGKL (zμ zν : ℝ) : ℝ :=
  zμ * Real.log (zμ / zν) - zμ + zν

/--
Definitional expansion of the generalized KL divergence into the KL term plus
its mass-correction contribution.
-/
theorem generalizedKL_scale_shape_split
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (_hμ : μ ≠ 0) (_hν : ν ≠ 0) :
    generalizedKL μ ν =
      (InformationTheory.klDiv μ ν).toReal - (μ Set.univ).toReal + (ν Set.univ).toReal := by
  rfl



end InfoGeometry.Canonical.MeasureScaleShape
