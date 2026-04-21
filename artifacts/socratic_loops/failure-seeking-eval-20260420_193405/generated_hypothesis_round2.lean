import Mathlib
import Mathlib



import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace NegLogHypothesis

structure NegLogRectifier where
  generate : ℝ → ℝ
  map_one : generate 1 = 0
  map_mul : ∀ {r s : ℝ}, 0 < r → 0 < s →
    generate (r * s) = generate r + generate s

noncomputable def negLog : NegLogRectifier where
  generate r := -Real.log r
  map_one := by
    simp
  map_mul := by
    intro r s hr hs
    rw [Real.log_mul (ne_of_gt hr) (ne_of_gt hs)]
    ring

namespace NegLogRectifier

@[simp]
theorem negLog_generate (r : ℝ) :
    negLog.generate r = -Real.log r :=
  rfl

theorem generate_mul {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    negLog.generate (r * s) = negLog.generate r + negLog.generate s :=
  negLog.map_mul hr hs

end NegLogRectifier

structure AdditivePotentialAction (X : Type u) where
  act : ℝ → X → X
  act_zero : ∀ x : X, act 0 x = x
  act_add : ∀ a b x, act (a + b) x = act a (act b x)

structure RatioToGeneratorSurface where
  generate : ℝ → ℝ
  map_one : generate 1 = 0
  generate_mul : ∀ {r s : ℝ}, 0 < r → 0 < s →
    generate (r * s) = generate r + generate s

noncomputable def RatioToGeneratorSurface.standard : RatioToGeneratorSurface where
  generate := negLog.generate
  map_one := negLog.map_one
  generate_mul := negLog.map_mul

theorem generate_mul {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    RatioToGeneratorSurface.standard.generate (r * s)
      = RatioToGeneratorSurface.standard.generate r
        + RatioToGeneratorSurface.standard.generate s :=
  RatioToGeneratorSurface.standard.generate_mul hr hs

end NegLogHypothesis
