import InfoGeometry.Basic
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

namespace InfoGeometry.Canonical.MeasureScaleShape

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- 
Generalized KL divergence for non-normalized finite measures.
This is exactly `InformationTheory.klDiv` re-typed to `ℝ`.
-/
noncomputable def generalizedKL (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  (InformationTheory.klDiv μ ν).toReal

/-- The scalar part of the generalized KL (divergence between masses). -/
noncomputable def scalarGKL (zμ zν : ℝ) : ℝ :=
  zμ * Real.log (zμ / zν) - zμ + zν



end InfoGeometry.Canonical.MeasureScaleShape
