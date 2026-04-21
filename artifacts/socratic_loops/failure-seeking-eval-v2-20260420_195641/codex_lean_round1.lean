import Mathlib

set_option autoImplicit false

namespace InfoGeometry.Alchemical

structure NegLogRectifier (Ratio Potential : Type*)
    [One Ratio] [Mul Ratio] [Zero Potential] [Add Potential] where
  toPotential : Ratio → Potential
  map_one' : toPotential 1 = 0
  map_mul' : ∀ x y : Ratio, toPotential (x * y) = toPotential x + toPotential y

instance {Ratio Potential : Type*} [One Ratio] [Mul Ratio]
    [Zero Potential] [Add Potential] :
    CoeFun (NegLogRectifier Ratio Potential) (fun _ => Ratio → Potential) where
  coe R := R.toPotential

namespace NegLogRectifier

variable {Ratio Potential : Type*}
variable [One Ratio] [Mul Ratio] [Zero Potential] [Add Potential]

@[simp]
theorem map_one (R : NegLogRectifier Ratio Potential) : R 1 = 0 :=
  R.map_one'

@[simp]
theorem map_mul (R : NegLogRectifier Ratio Potential) (x y : Ratio) :
    R (x * y) = R x + R y :=
  R.map_mul' x y

end NegLogRectifier

structure AdditivePotentialAction (Potential State : Type*)
    [Zero Potential] [Add Potential] where
  act : Potential → State → State
  act_zero : ∀ s : State, act 0 s = s
  act_add : ∀ p q : Potential, ∀ s : State,
    act (p + q) s = act p (act q s)

structure RatioToGeneratorSurface (Ratio Potential State : Type*)
    [One Ratio] [Mul Ratio] [Zero Potential] [Add Potential]
    extends NegLogRectifier Ratio Potential,
      AdditivePotentialAction Potential State

namespace RatioToGeneratorSurface

variable {Ratio Potential State : Type*}
variable [One Ratio] [Mul Ratio] [Zero Potential] [Add Potential]

def generate (G : RatioToGeneratorSurface Ratio Potential State)
    (r : Ratio) : State → State :=
  G.act (G.toPotential r)

@[simp]
theorem generate_one (G : RatioToGeneratorSurface Ratio Potential State)
    (s : State) :
    G.generate 1 s = s := by
  simp [generate, G.act_zero]

theorem generate_mul (G : RatioToGeneratorSurface Ratio Potential State)
    (x y : Ratio) (s : State) :
    G.generate (x * y) s = G.generate x (G.generate y s) := by
  calc
    G.generate (x * y) s = G.act (G.toPotential (x * y)) s := rfl
    _ = G.act (G.toPotential x + G.toPotential y) s := by
      rw [G.map_mul' x y]
    _ = G.act (G.toPotential x) (G.act (G.toPotential y) s) :=
      G.act_add (G.toPotential x) (G.toPotential y) s
    _ = G.generate x (G.generate y s) := rfl

end RatioToGeneratorSurface

abbrev PositiveRatio := {x : ℝ // 0 < x}

namespace PositiveRatio

instance : One PositiveRatio where
  one := ⟨1, by norm_num⟩

instance : Mul PositiveRatio where
  mul x y := ⟨x.1 * y.1, mul_pos x.2 y.2⟩

@[simp]
theorem coe_mul (x y : PositiveRatio) :
    ((x * y : PositiveRatio) : ℝ) = x.1 * y.1 :=
  rfl

@[simp]
theorem coe_one : ((1 : PositiveRatio) : ℝ) = 1 :=
  rfl

noncomputable def negLog (r : PositiveRatio) : ℝ :=
  -Real.log r.1

@[simp]
theorem negLog_one : negLog 1 = 0 := by
  simp [negLog]

theorem negLog_mul (x y : PositiveRatio) :
    negLog (x * y) = negLog x + negLog y := by
  simp only [negLog, coe_mul]
  rw [Real.log_mul (ne_of_gt x.2) (ne_of_gt y.2)]
  ring

noncomputable def rectifier : NegLogRectifier PositiveRatio ℝ where
  toPotential := negLog
  map_one' := negLog_one
  map_mul' := negLog_mul

end PositiveRatio

end InfoGeometry.Alchemical