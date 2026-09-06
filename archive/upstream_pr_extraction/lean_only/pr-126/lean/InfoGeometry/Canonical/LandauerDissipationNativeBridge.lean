import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite erasure positivity readouts

This module defines finite erasure data and proves positivity of two explicit
real-valued readouts:

1. The quotient `(Kx - Ky) * log 2 / beta` is positive.

2. The numerator `(Kx - Ky) * log 2` is positive.

The thermodynamic interpretation is not an additional theorem here.
-/

namespace InfoGeometry.Canonical.LandauerDissipationNativeBridge

/-- Landauer erasure state data with complexity decrease. -/
def LandauerErasureData :=
  {x : ℕ × (ℕ × ℝ) // x.2.1 < x.1 ∧ 0 < x.2.2}

namespace LandauerErasureData

abbrev kolmogorovX (data : LandauerErasureData) : ℕ := data.1.1

abbrev kolmogorovY (data : LandauerErasureData) : ℕ := data.1.2.1

abbrev beta (data : LandauerErasureData) : ℝ := data.1.2.2

def complexity_decrease (data : LandauerErasureData) :
    kolmogorovY data < kolmogorovX data := data.2.1

def beta_pos (data : LandauerErasureData) : 0 < beta data := data.2.2

end LandauerErasureData

/-- Heat dissipated to the environment during erasure: $\Delta Q = \frac{(K_x - K_y) \ln 2}{\beta}$. -/
noncomputable def landauerHeat (data : LandauerErasureData) : ℝ :=
  ((data.kolmogorovX : ℝ) - (data.kolmogorovY : ℝ)) * Real.log 2 / data.beta

/-- Entropy transferred to the thermal environment: $\Delta S = (K_x - K_y) \ln 2$. -/
noncomputable def environmentEntropyIncrease (data : LandauerErasureData) : ℝ :=
  ((data.kolmogorovX : ℝ) - (data.kolmogorovY : ℝ)) * Real.log 2

/--
**Positive quotient readout.**
The explicitly defined quotient expression is positive.
-/
theorem landauer_heat_positivity (data : LandauerErasureData) :
    0 < landauerHeat data := by
  unfold landauerHeat
  have h_diff : 0 < (data.kolmogorovX : ℝ) - (data.kolmogorovY : ℝ) := by
    rw [sub_pos]
    exact Nat.cast_lt.mpr data.complexity_decrease
  have h_log2 : 0 < Real.log 2 := by
    apply Real.log_pos
    linarith
  have h_num : 0 < ((data.kolmogorovX : ℝ) - (data.kolmogorovY : ℝ)) * Real.log 2 := by
    exact mul_pos h_diff h_log2
  exact div_pos h_num data.beta_pos

/--
**Positive numerator readout.**
The explicitly defined numerator expression is positive.
-/
theorem environment_entropy_increase_pos (data : LandauerErasureData) :
    0 < environmentEntropyIncrease data := by
  unfold environmentEntropyIncrease
  have h_diff : 0 < (data.kolmogorovX : ℝ) - (data.kolmogorovY : ℝ) := by
    rw [sub_pos]
    exact Nat.cast_lt.mpr data.complexity_decrease
  have h_log2 : 0 < Real.log 2 := by
    apply Real.log_pos
    linarith
  exact mul_pos h_diff h_log2

end InfoGeometry.Canonical.LandauerDissipationNativeBridge
