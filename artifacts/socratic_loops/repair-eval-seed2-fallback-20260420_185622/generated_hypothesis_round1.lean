import Mathlib
import Mathlib



import Mathlib

noncomputable section

structure NegLogRectifier (α β : Type*) [Mul α] [AddCommGroup β] where
  positive : α → Prop
  log : α → β
  log_mul :
    ∀ {x y : α}, positive x → positive y → log (x * y) = log x + log y

namespace NegLogRectifier

variable {α β : Type*} [Mul α] [AddCommGroup β]

def generate (R : NegLogRectifier α β) (x : α) : β :=
  -R.log x

theorem generate_mul
    (R : NegLogRectifier α β) {x y : α}
    (hx : R.positive x) (hy : R.positive y) :
    R.generate (x * y) = R.generate x + R.generate y := by
  unfold generate
  rw [R.log_mul hx hy]
  abel

theorem map_mul
    (R : NegLogRectifier α β) {x y : α}
    (hx : R.positive x) (hy : R.positive y) :
    R.generate (x * y) = R.generate x + R.generate y :=
  R.generate_mul hx hy

end NegLogRectifier

structure AdditivePotentialAction (β σ : Type*) [AddMonoid β] where
  act : β → σ → σ
  zero_act : ∀ s : σ, act 0 s = s
  add_act : ∀ a b : β, ∀ s : σ, act (a + b) s = act a (act b s)

structure RatioToGeneratorSurface
    (α β σ : Type*) [Mul α] [AddCommGroup β] where
  rectifier : NegLogRectifier α β
  action : AdditivePotentialAction β σ

namespace RatioToGeneratorSurface

variable {α β σ : Type*} [Mul α] [AddCommGroup β]

def generate (S : RatioToGeneratorSurface α β σ) (x : α) : β :=
  S.rectifier.generate x

theorem generate_mul
    (S : RatioToGeneratorSurface α β σ) {x y : α}
    (hx : S.rectifier.positive x) (hy : S.rectifier.positive y) :
    S.generate (x * y) = S.generate x + S.generate y :=
  S.rectifier.generate_mul hx hy

end RatioToGeneratorSurface
