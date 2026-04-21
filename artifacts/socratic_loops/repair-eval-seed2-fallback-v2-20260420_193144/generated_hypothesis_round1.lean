import Mathlib
import Mathlib



import Mathlib

noncomputable section

structure AdditivePotentialAction where
  act : ℝ → ℝ → ℝ
  act_zero : ∀ x, act 0 x = x
  act_add : ∀ a b x, act (a + b) x = act a (act b x)

structure RatioToGeneratorSurface where
  action : AdditivePotentialAction

namespace RatioToGeneratorSurface

/-- Negative logarithm rectifies positive multiplicative relative data into additive potential data. -/
def NegLogRectifier (r : ℝ) : ℝ :=
  -Real.log r

namespace NegLogRectifier

theorem map_mul {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    NegLogRectifier (r * s) = NegLogRectifier r + NegLogRectifier s := by
  unfold NegLogRectifier
  rw [Real.log_mul (ne_of_gt hr) (ne_of_gt hs)]
  ring

theorem map_one : NegLogRectifier 1 = 0 := by
  unfold NegLogRectifier
  rw [Real.log_one]
  ring

end NegLogRectifier

def generate (S : RatioToGeneratorSurface) (r x : ℝ) : ℝ :=
  S.action.act (NegLogRectifier r) x

theorem generate_one (S : RatioToGeneratorSurface) (x : ℝ) :
    generate S 1 x = x := by
  unfold generate
  rw [NegLogRectifier.map_one]
  exact S.action.act_zero x

theorem generate_mul (S : RatioToGeneratorSurface) {r s x : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    generate S (r * s) x = S.action.act (NegLogRectifier r) (generate S s x) := by
  unfold generate
  rw [NegLogRectifier.map_mul hr hs]
  exact S.action.act_add (NegLogRectifier r) (NegLogRectifier s) x

end RatioToGeneratorSurface

end
