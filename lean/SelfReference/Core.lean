/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# SelfReference.Core

Core structures for agents, feedback loops, persistence, and reflection.
-/

namespace SelfReference

/-- Minimal transition system with universe polymorphism. -/
structure Agent.{u} where
  State  : Type u
  Input  : Type u
  Output : Type u
  step   : State → Input → State × Output

/-- Outputs can be reintroduced as later inputs. -/
structure ClosedLoop.{u} (A : Agent.{u}) where
  feed : A.Output → A.Input

/-- Some memory carrier can be read from and written back into state. -/
structure Persistent.{u} (A : Agent.{u}) where
  Memory : Type u
  read   : A.State → Memory
  write  : A.State → Memory → A.State

/-- The system can internalize some representation of its own state. -/
structure Reflective.{u} (A : Agent.{u}) where
  Rep        : Type u
  reifyState : A.State → Rep

/-- Stronger reflection: reification is at least left-invertible. -/
structure FaithfulReflective.{u} (A : Agent.{u}) extends Reflective A where
  interpretState : Rep → A.State
  sound : ∀ s, interpretState (reifyState s) = s

/-- The system can induce an admissible update on its own state. -/
structure SelfModifying.{u} (A : Agent.{u}) where
  rewrite : A.State → A.State

/-- State itself is a faithful representation for every transition system.
This witnesses the present interface, not operational introspection. -/
def Agent.stateReflection.{u} (A : Agent.{u}) : FaithfulReflective A where
  Rep := A.State
  reifyState := id
  interpretState := id
  sound _ := rfl

/-- Any faithful reification retains all distinctions between states. -/
theorem FaithfulReflective.reifyState_injective.{u}
    {A : Agent.{u}} (R : FaithfulReflective A) :
    Function.Injective R.reifyState :=
  Function.LeftInverse.injective R.sound

/-- A fixed input induces a state update from the actual transition rule.
The interface imposes no nontriviality or endogenous-policy requirement. -/
def Agent.transitionRewrite.{u} (A : Agent.{u}) (i : A.Input) : SelfModifying A where
  rewrite s := (A.step s i).1

/-- One closed-loop step on extended state. -/
def loopStep.{u} (A : Agent.{u}) (L : ClosedLoop A) :
    A.State × A.Input → A.State × A.Input
  | (s, i) =>
      let (s', o) := A.step s i
      (s', L.feed o)

/-- n closed-loop steps. Definition matched to proof requirements. -/
def iterateClosedLoop.{u} (A : Agent.{u}) (L : ClosedLoop A) :
    Nat → A.State × A.Input → A.State × A.Input
  | 0, x => x
  | n + 1, x => loopStep A L (iterateClosedLoop A L n x)

end SelfReference
