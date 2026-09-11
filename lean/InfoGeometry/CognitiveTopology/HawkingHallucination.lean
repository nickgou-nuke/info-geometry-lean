import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.CognitiveTopology.ExceptionalPointGrokking

/-!
# Thermal noise beside an exceptional-point witness

This module keeps the "hallucination as Hawking radiation" slogan out of the
theorem surface.  It proves only that, from explicit premises, the nilpotent
exceptional-point socket and a positive temperature/noise parameter can be
carried together.

#### BUCKET 1: CLOSED FINITE THEOREMS

None.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`exceptionalPoint_with_positive_temperature`.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here identifies LLM hallucination with Hawking radiation, proves a
sampling distribution, or derives any stochastic inference bound.
-/

noncomputable section

namespace InfoGeometry.CognitiveTopology.Thermodynamics

open ContinuousLinearMap
open InfoGeometry.CognitiveTopology.Grokking

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- The thermodynamic noise parameter carried as an explicit premise.
variable (T : ℝ)

/--
Conditional thermal socket.

From an explicit exceptional-point witness and a positive temperature/noise
premise, we can carry both the square-zero nilpotent part and the positivity
fact.  This does not identify the noise with hallucination or Hawking radiation.
-/
theorem exceptionalPoint_with_positive_temperature (A N : H →L[ℂ] H)
    (h_ep : IsExceptionalPoint A N) (h_T_pos : T > 0) :
    (N ∘L N = 0) ∧ T > 0 := by
  exact ⟨exceptionalPoint_nilpotent_part_square_zero A N h_ep, h_T_pos⟩

end InfoGeometry.CognitiveTopology.Thermodynamics
