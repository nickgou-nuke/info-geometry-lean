import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ModularPoissonCompact

Scalar Poisson/KL potential in the bounded modular Cayley coordinate.

This file pins down only the finite scalar coordinate bridge:

* `x ↦ x - 1 - log x` is the Poisson/KL log potential;
* `delta ↦ (1 - delta)/(1 + delta)` is the bounded modular Cayley chart;
* `T ↦ (1 - T)/(1 + T)` is the inverse chart;
* positivity of the scalar potential transfers to the bounded chart for
  `-1 < T < 1`.

No Araki relative entropy theorem.
No operator logarithm.
No functional calculus.
No natural-cone or Type III assertion.
-/

namespace InfoGeometry.Canonical.ModularPoissonCompact

noncomputable section

/-- Scalar Poisson/KL log potential based at the reference scale `1`. -/
def poissonLogPotential (x : ℝ) : ℝ :=
  x - 1 - Real.log x

/-- Bounded modular Cayley coordinate `T = (1 - delta)/(1 + delta)`. -/
def boundedModularCoordinate (delta : ℝ) : ℝ :=
  (1 - delta) / (1 + delta)

/-- Inverse bounded modular Cayley coordinate `delta = (1 - T)/(1 + T)`. -/
def invBoundedModularCoordinate (T : ℝ) : ℝ :=
  (1 - T) / (1 + T)

/-- The scalar Poisson/KL potential is nonnegative on positive scales. -/
theorem poissonLogPotential_nonneg_of_pos {x : ℝ} (hx : 0 < x) :
    0 ≤ poissonLogPotential x := by
  unfold poissonLogPotential
  have h := Real.log_le_sub_one_of_pos hx
  linarith

/-- The inverse bounded coordinate is positive for `-1 < T < 1`. -/
theorem invBoundedModularCoordinate_pos
    {T : ℝ} (hlo : -1 < T) (hhi : T < 1) :
    0 < invBoundedModularCoordinate T := by
  unfold invBoundedModularCoordinate
  exact div_pos (by linarith) (by linarith)

/-- Scalar KL nonnegativity transported to the bounded modular coordinate. -/
theorem poissonLogPotential_invBoundedModularCoordinate_nonneg
    {T : ℝ} (hlo : -1 < T) (hhi : T < 1) :
    0 ≤ poissonLogPotential (invBoundedModularCoordinate T) :=
  poissonLogPotential_nonneg_of_pos (invBoundedModularCoordinate_pos hlo hhi)

/-- Explicit scalar potential in bounded modular coordinate. -/
theorem poissonLogPotential_invBoundedModularCoordinate_eq
    {T : ℝ} (hT : T ≠ -1) :
    poissonLogPotential (invBoundedModularCoordinate T) =
      (-2 * T) / (1 + T) - Real.log ((1 - T) / (1 + T)) := by
  unfold poissonLogPotential invBoundedModularCoordinate
  have hden : 1 + T ≠ 0 := by
    intro h
    apply hT
    linarith
  rw [show (1 - T) / (1 + T) - 1 = (-2 * T) / (1 + T) by
    field_simp [hden]
    ring]

/-- The bounded chart sends every positive scale into the interval `(-1, 1)`. -/
theorem neg_one_lt_boundedModularCoordinate_of_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    -1 < boundedModularCoordinate delta := by
  unfold boundedModularCoordinate
  rw [lt_div_iff₀ (by linarith)]
  ring_nf
  linarith

/-- The bounded chart sends every positive scale into the interval `(-1, 1)`. -/
theorem boundedModularCoordinate_lt_one_of_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    boundedModularCoordinate delta < 1 := by
  unfold boundedModularCoordinate
  rw [div_lt_iff₀ (by linarith)]
  ring_nf
  linarith

/-- The reference scale `delta = 1` maps to the equilibrium coordinate `T = 0`. -/
theorem boundedModularCoordinate_one :
    boundedModularCoordinate 1 = 0 := by
  unfold boundedModularCoordinate
  norm_num

/-- The scalar Poisson/KL potential vanishes at the reference scale. -/
theorem poissonLogPotential_one :
    poissonLogPotential 1 = 0 := by
  unfold poissonLogPotential
  simp

/-- The inverse chart is a left inverse away from `delta = -1`. -/
theorem invBoundedModularCoordinate_bounded_left
    {delta : ℝ} (hdelta : delta ≠ -1) :
    invBoundedModularCoordinate (boundedModularCoordinate delta) = delta := by
  unfold invBoundedModularCoordinate boundedModularCoordinate
  have hden : 1 + delta ≠ 0 := by
    intro h
    apply hdelta
    linarith
  have hinner : 1 + (1 - delta) / (1 + delta) ≠ 0 := by
    rw [show 1 + (1 - delta) / (1 + delta) = 2 / (1 + delta) by
      field_simp [hden]
      ring]
    exact div_ne_zero (by norm_num) hden
  field_simp [hden, hinner]
  ring

/-- The bounded chart is a left inverse to its inverse away from `T = -1`. -/
theorem boundedModularCoordinate_invBounded_right
    {T : ℝ} (hT : T ≠ -1) :
    boundedModularCoordinate (invBoundedModularCoordinate T) = T := by
  unfold invBoundedModularCoordinate boundedModularCoordinate
  have hden : 1 + T ≠ 0 := by
    intro h
    apply hT
    linarith
  have hinner : 1 + (1 - T) / (1 + T) ≠ 0 := by
    rw [show 1 + (1 - T) / (1 + T) = 2 / (1 + T) by
      field_simp [hden]
      ring]
    exact div_ne_zero (by norm_num) hden
  field_simp [hden, hinner]
  ring

end

end InfoGeometry.Canonical.ModularPoissonCompact
