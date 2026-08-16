import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace FiniteContinuousBivariantModel

/--
This file records a finite continuous-linear bivariant model.
It is deliberately *not* a definition of standard Kasparov `KK`-theory:
no C*-algebras, Hilbert modules, positivity, or compactness axioms are
introduced here.  The model is useful only for the associative composition
laws of bounded continuous linear maps, which are proved below.
-/
abbrev Element (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B] :=
  A →L[ℂ] B

namespace Element

variable {A B C D : Type*}
variable [NormedAddCommGroup A] [NormedSpace ℂ A]
variable [NormedAddCommGroup B] [NormedSpace ℂ B]
variable [NormedAddCommGroup C] [NormedSpace ℂ C]
variable [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- Finite bivariant composition `x : A → B`, `y : B → C`, by operator composition.

This is a continuous-linear model operation, not the internal Kasparov product. -/
def composition (x : Element A B) (y : Element B C) : Element A C :=
  y.comp x

/-- Associativity of the continuous-linear composition model. -/
theorem composition_assoc (x : Element A B) (y : Element B C) (z : Element C D) :
    composition (composition x y) z = composition x (composition y z) := by
  change z.comp (y.comp x) = (z.comp y).comp x
  ext
  rfl

/-- Identity element for the continuous-linear composition model. -/
def identity (A : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] : Element A A :=
  ContinuousLinearMap.id ℂ A

/-- Left identity for the continuous-linear composition model. -/
theorem composition_left_identity (x : Element A B) :
    composition (identity A) x = x := by
  change x.comp (ContinuousLinearMap.id ℂ A) = x
  ext
  rfl

/-- Right identity for the continuous-linear composition model. -/
theorem composition_right_identity (x : Element A B) :
    composition x (identity B) = x := by
  change (ContinuousLinearMap.id ℂ B).comp x = x
  ext
  rfl

end Element

end FiniteContinuousBivariantModel
