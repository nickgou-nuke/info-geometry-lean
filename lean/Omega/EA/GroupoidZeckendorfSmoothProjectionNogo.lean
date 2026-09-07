import Mathlib

namespace Omega.EA

/-- Concrete `C^1` chain-rule obstruction for a smooth hidden trajectory in a finite-dimensional
state space (`ℝ × ℝ`) and a smooth scalar readout.

A `C^1` hidden trajectory composed with a `C^1` readout is again `C^1`; hence a finite
dimensional smooth hidden state cannot by itself produce an everywhere nondifferentiable visible
signal.
    prop:groupoid-zeckendorf-smooth-projection-nogo -/
theorem paper_groupoid_zeckendorf_smooth_projection_nogo_spec :
    ∀ (γ : ℝ → ℝ × ℝ) (O : ℝ × ℝ → ℝ),
      ContDiff ℝ 1 γ → ContDiff ℝ 1 O → ContDiff ℝ 1 (fun t => O (γ t)) := by
  intro γ O hγ hO
  simpa using hO.comp hγ

theorem paper_groupoid_zeckendorf_smooth_projection_nogo_verified :
    ∀ (γ : ℝ → ℝ × ℝ) (O : ℝ × ℝ → ℝ),
      ContDiff ℝ 1 γ → ContDiff ℝ 1 O → ContDiff ℝ 1 (fun t => O (γ t)) := by
  exact paper_groupoid_zeckendorf_smooth_projection_nogo_spec

end Omega.EA
