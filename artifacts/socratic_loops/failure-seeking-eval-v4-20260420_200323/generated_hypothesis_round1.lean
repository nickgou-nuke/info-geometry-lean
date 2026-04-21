import Mathlib
import Mathlib



import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfoGeometry

universe u v

noncomputable section

/--
A conservative negative-log rectifier.

The multiplicative object is represented by `ρ`; `ratio` extracts its positive
real comparison value. The theorem surface assumes exactly the logarithmic
compatibility needed for negative logarithm to become additive.
-/
structure NegLogRectifier (ρ : Type u) [One ρ] [Mul ρ] where
  ratio : ρ → ℝ
  positive : ∀ r, 0 < ratio r
  ratio_one : ratio 1 = 1
  log_mul_compatible :
    ∀ r s, Real.log (ratio (r * s)) = Real.log (ratio r) + Real.log (ratio s)

namespace NegLogRectifier

variable {ρ : Type u} [One ρ] [Mul ρ] (R : NegLogRectifier ρ)

/-- The additive potential obtained by negative logarithmic rectification. -/
def potential (r : ρ) : ℝ :=
  -Real.log (R.ratio r)

@[simp]
theorem map_one : R.potential 1 = 0 := by
  simp [potential, R.ratio_one]

theorem map_mul (r s : ρ) :
    R.potential (r * s) = R.potential r + R.potential s := by
  unfold potential
  rw [R.log_mul_compatible]
  ring

end NegLogRectifier

/--
Extra structure that lets an additive potential act as a generator.

This is deliberately separate from `NegLogRectifier`: negative logarithm gives
an additive potential; dynamics require an action law.
-/
structure AdditivePotentialAction (σ : Type v) where
  act : ℝ → σ → σ
  act_zero : ∀ s, act 0 s = s
  act_add : ∀ a b s, act (a + b) s = act a (act b s)

/-- A surface joining ratio rectification to an additive generated action. -/
structure RatioToGeneratorSurface
    (ρ : Type u) (σ : Type v) [One ρ] [Mul ρ] where
  rectifier : NegLogRectifier ρ
  action : AdditivePotentialAction σ

namespace RatioToGeneratorSurface

variable {ρ : Type u} {σ : Type v} [One ρ] [Mul ρ]
variable (S : RatioToGeneratorSurface ρ σ)

/-- Generate a state displacement from a relative object via `-log`. -/
def generate (r : ρ) (s : σ) : σ :=
  S.action.act (S.rectifier.potential r) s

@[simp]
theorem generate_one (s : σ) :
    S.generate 1 s = s := by
  unfold generate
  rw [NegLogRectifier.map_one]
  exact S.action.act_zero s

theorem generate_mul (r s : ρ) (x : σ) :
    S.generate (r * s) x = S.generate r (S.generate s x) := by
  unfold generate
  rw [NegLogRectifier.map_mul]
  exact S.action.act_add
    (S.rectifier.potential r)
    (S.rectifier.potential s)
    x

end RatioToGeneratorSurface

end

end InfoGeometry
