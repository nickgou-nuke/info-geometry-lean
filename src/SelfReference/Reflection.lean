import SelfReference.Core

/-!
# SelfReference.Reflection

Policy-level reflection structures and fidelity laws.
-/

namespace SelfReference

/--
Extends reflection to policy space.
A policy is effectively the "prepared" transition for a given state.
-/
structure PolicyReflective (A : Agent) extends Reflective A where
  PolicyRep : Type
  reifyPolicy : A.State → PolicyRep
  /-- Optionally: interpretation of policy back into an operational function -/
  interpretPolicy : PolicyRep → (A.Input → A.State × A.Output)

/--
Fidelity law for policy reflection:
Reifying the state's implicit policy and then interpreting it
should recover the agent's original step function for that state.
-/
structure FaithfulPolicyReflective (A : Agent) extends PolicyReflective A where
  fidelity : ∀ s i, interpretPolicy (reifyPolicy s) i = A.step s i

end SelfReference
