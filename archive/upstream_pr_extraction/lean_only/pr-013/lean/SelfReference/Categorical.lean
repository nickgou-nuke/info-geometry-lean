import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types.Basic
import SelfReference.Core
import SelfReference.Reflection

/-!
# SelfReference.Categorical

Categorical interfaces and compatibility bridges for reflective agents.
-/

namespace SelfReference

open CategoryTheory

/--
The Agent Interface Functor F(X) = Input → X × Output.
This captures the shape of a single transition.
-/
@[simps]
def agentFunctor (A : Agent.{u}) : Type u ⥤ Type u where
  obj X := A.Input → X × A.Output
  map f transition := fun i => (f (transition i).1, (transition i).2)
  map_id X := by
    funext transition i
    ext
    · rfl
    · rfl
  map_comp f g := by
    funext transition i
    ext
    · rfl
    · rfl

/--
An `Agent` state space as a coalgebra for its own interface functor.
This lifts the operational transition law to a categorical morphism α : S ⟶ F(S).
-/
structure AgentCoalgebra (A : Agent.{u}) where
  α : A.State ⟶ (agentFunctor A).obj A.State

/-- Any operational Agent induces a canonical Coalgebra structure. -/
def inducedCoalgebra (A : Agent.{u}) : AgentCoalgebra A where
  α s := fun i => A.step s i

/-! ## The Reflection-Dynamics Bridge -/

/--
Compatibility structure between reflection and coalgebraic dynamics.
An agent's reified view `Rep` is compatible if the transition dynamics
can be represented as a morphism in the category of representations.
-/
structure ReflectiveCompatibility (A : Agent.{u}) (R : Reflective.{u} A) where
  coalg : AgentCoalgebra A
  /--
    A transition dynamics defined purely on the representation space.
    f_R : R.Rep ⟶ (agentFunctor A).obj R.Rep
  -/
  rep_dynamics : R.Rep ⟶ (agentFunctor A).obj R.Rep
  /--
    Compatibility Law: Reifying the next state is the same as evolving the reified current state.
  -/
  commutes : ∀ s i,
    let (s_next, _) := A.step s i
    (rep_dynamics (R.reifyState s) i).1 = R.reifyState s_next

end SelfReference
