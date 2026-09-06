import SelfReference.Core

/-!
# SelfReference.Problem

Problem, catastrophe, and resolution structures for recursive research states.
-/

namespace SelfReference

universe u

/--
  A Problem is a specification for a required state transition.
-/
structure ResearchProblem (S : Type u) where
  context : S
  goal : S → Prop
  complexity : Float

/--
  A Catastrophe is a ResearchProblem triggered by a topological singularity.
-/
structure Catastrophe (S : Type u) extends ResearchProblem S where
  singularity_index : Float
  is_singular : singularity_index < 0

/--
  A Resolution is a witness that an informational phase has condensed.
-/
structure Resolution (S : Type u) (P : ResearchProblem S) where
  condensedState : S
  verification : P.goal condensedState

end SelfReference
