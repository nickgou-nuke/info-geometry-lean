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
