set_option autoImplicit false

namespace InfoGeometry.Alchemical

/--
A negative-log rectifier is only the lawful passage from multiplicative ratios
to additive potentials. It does not, by itself, assert dynamics.
-/
structure NegLogRectifier (Ratio Potential : Type*)
    [Mul Ratio] [Add Potential] where
  negLog : Ratio → Potential
  negLog_mul :
    ∀ x y : Ratio, negLog (x * y) = negLog x + negLog y

instance {Ratio Potential : Type*} [Mul Ratio] [Add Potential] :
    CoeFun (NegLogRectifier Ratio Potential) (fun _ => Ratio → Potential) where
  coe R := R.negLog

@[simp]
theorem NegLogRectifier.map_mul
    {Ratio Potential : Type*} [Mul Ratio] [Add Potential]
    (R : NegLogRectifier Ratio Potential) (x y : Ratio) :
    R (x * y) = R x + R y :=
  R.negLog_mul x y

/--
A potential becomes generator-like only relative to an independent additive
action on a state space.
-/
structure AdditivePotentialAction (Potential State : Type*)
    [Add Potential] where
  act : Potential → State → State
  act_add :
    ∀ p q : Potential, ∀ s : State,
      act (p + q) s = act p (act q s)

/--
The conservative surface: ratios yield generators only after rectification and
an external additive action have both been supplied.
-/
structure RatioToGeneratorSurface (Ratio Potential State : Type*)
    [Mul Ratio] [Add Potential]
    extends NegLogRectifier Ratio Potential,
      AdditivePotentialAction Potential State

namespace RatioToGeneratorSurface

variable {Ratio Potential State : Type*}
variable [Mul Ratio] [Add Potential]

def generate
    (G : RatioToGeneratorSurface Ratio Potential State)
    (r : Ratio) : State → State :=
  G.act (G.negLog r)

theorem generate_mul
    (G : RatioToGeneratorSurface Ratio Potential State)
    (x y : Ratio) (s : State) :
    G.generate (x * y) s = G.generate x (G.generate y s) := by
  calc
    G.generate (x * y) s
        = G.act (G.negLog (x * y)) s := rfl
    _ = G.act (G.negLog x + G.negLog y) s := by
        rw [G.negLog_mul x y]
    _ = G.act (G.negLog x) (G.act (G.negLog y) s) :=
        G.act_add (G.negLog x) (G.negLog y) s
    _ = G.generate x (G.generate y s) := rfl

end RatioToGeneratorSurface

end InfoGeometry.Alchemical