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

/--
Theorem commented out by hollow theorem detector: proof is trivial or conclusion is already known.
-- theorem generalizedKL_scale_shape_split ... := ...
-- sorry
-/

theorem generalizedKL_scale_shape_split
  (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (hμν : μ ≪ ν) (hμ : μ ≠ 0) (hν : ν ≠ 0)
  (h_int : Integrable (llr μ ν) μ) :
  generalizedKL μ ν =
    (μ Set.univ).toReal *
      (InformationTheory.klDiv
        ((FiniteMeasure.normalize ⟨μ, inferInstance⟩ : ProbabilityMeasure α) : Measure α)
        ((FiniteMeasure.normalize ⟨ν, inferInstance⟩ : ProbabilityMeasure α) : Measure α)
      ).toReal
    + scalarGKL (μ Set.univ).toReal (ν Set.univ).toReal :=
by
  -- The proof involves the scaling properties of the Radon-Nikodym derivative 
  -- and the linearity of the integral.
  -- Specifically: dμ/dν = (zμ/zν) * (dmμ/dmν)
  -- and ∫ log(dμ/dν) dμ = zμ * ∫ log(dmμ/dmν) dmμ + zμ * log(zμ/zν)
  sorry

end InfoGeometry.Canonical.MeasureScaleShape
