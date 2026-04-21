import Mathlib

namespace Hypothesis

/--
A conservative surface for the distilled claim:
multiplicative relative data can be rectified into additive potential data.

The concrete intended example is `r ↦ -log r`; logarithmic compatibility is
kept as a lawful field rather than asserted universally.
-/
structure NegLogRectifier (R A : Type*) [Mul R] [One R] [Add A] [Zero A] where
  toPotential : R -> A
  map_one : toPotential 1 = 0
  map_mul : forall x y : R, toPotential (x * y) = toPotential x + toPotential y

namespace NegLogRectifier

variable {R A : Type*} [Mul R] [One R] [Add A] [Zero A]

@[simp]
theorem map_one_apply (N : NegLogRectifier R A) : N.toPotential 1 = 0 :=
  N.map_one

theorem map_mul_apply (N : NegLogRectifier R A) (x y : R) :
    N.toPotential (x * y) = N.toPotential x + N.toPotential y :=
  N.map_mul x y

end NegLogRectifier

/-- The scalar negative-log expression. Positivity laws are supplied separately. -/
def negLog (r : ℝ) : ℝ :=
  -Real.log r

/--
A potential becomes a generator only relative to an action/dynamics interface.
This records the extra structure without claiming it follows from `-log` alone.
-/
structure AdditivePotentialAction (R A X : Type*) [Mul R] [One R] [Add A] [Zero A] where
  rectifier : NegLogRectifier R A
  act : A -> X -> X

namespace AdditivePotentialAction

variable {R A X : Type*} [Mul R] [One R] [Add A] [Zero A]

def generate (S : AdditivePotentialAction R A X) (r : R) (x : X) : X :=
  S.act (S.rectifier.toPotential r) x

theorem generate_mul_potential (S : AdditivePotentialAction R A X) (r s : R) :
    S.rectifier.toPotential (r * s) =
      S.rectifier.toPotential r + S.rectifier.toPotential s :=
  S.rectifier.map_mul r s

end AdditivePotentialAction

/-- A named surface for the ratio-to-generator reading. -/
abbrev RatioToGeneratorSurface (R A X : Type*) [Mul R] [One R] [Add A] [Zero A] :=
  AdditivePotentialAction R A X

end Hypothesis