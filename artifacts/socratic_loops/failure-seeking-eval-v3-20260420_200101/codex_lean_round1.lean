import Mathlib

noncomputable section

abbrev PositiveReal := {x : ℝ // 0 < x}

structure NegLogRectifier where
  generate : PositiveReal → ℝ
  map_one : generate ⟨1, by norm_num⟩ = 0
  map_mul : ∀ r s : PositiveReal,
    generate ⟨r.1 * s.1, mul_pos r.2 s.2⟩ = generate r + generate s

namespace NegLogRectifier

def negLog : NegLogRectifier where
  generate r := -Real.log r.1
  map_one := by simp
  map_mul r s := by
    have hr : r.1 ≠ 0 := ne_of_gt r.2
    have hs : s.1 ≠ 0 := ne_of_gt s.2
    rw [Real.log_mul hr hs]
    ring

@[simp] theorem generate_one : negLog.generate ⟨1, by norm_num⟩ = 0 :=
  negLog.map_one

theorem generate_mul (r s : PositiveReal) :
    negLog.generate ⟨r.1 * s.1, mul_pos r.2 s.2⟩ =
      negLog.generate r + negLog.generate s :=
  negLog.map_mul r s

end NegLogRectifier

structure AdditivePotentialAction (Ratio State : Type*) [Mul Ratio] [Add State] where
  generate : Ratio → State
  generate_mul : ∀ r s : Ratio, generate (r * s) = generate r + generate s

abbrev RatioToGeneratorSurface := AdditivePotentialAction PositiveReal ℝ

namespace RatioToGeneratorSurface

def negLog : RatioToGeneratorSurface where
  generate := NegLogRectifier.negLog.generate
  generate_mul := NegLogRectifier.generate_mul

@[simp] theorem generate_eq_negLog (r : PositiveReal) :
    AdditivePotentialAction.generate negLog r = -Real.log r.1 := rfl

theorem generate_mul (r s : PositiveReal) :
    AdditivePotentialAction.generate negLog ⟨r.1 * s.1, mul_pos r.2 s.2⟩ =
      AdditivePotentialAction.generate negLog r + AdditivePotentialAction.generate negLog s :=
  AdditivePotentialAction.generate_mul negLog r s

end RatioToGeneratorSurface