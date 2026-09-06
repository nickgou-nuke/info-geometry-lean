import SelfReference.Core

/-!
# SelfReference.Memory

Persistence models and trace-based recoverability for agents.
-/

namespace SelfReference

/-- Persistence through internal state modification. -/
structure InternalPersistent (A : Agent) extends Persistent A where
  /-- read and write laws -/
  read_write : ∀ s m, read (write s m) = m
  write_read : ∀ s, write s (read s) = s

/-- Persistence through an external immutable trace/log. -/
structure TracePersistent (A : Agent) where
  Trace : Type
  initialTrace : Trace
  append : Trace → A.Input → A.Output → Trace

/-- A system that can reconstruct its state from its trace. -/
structure Recoverable (A : Agent) extends TracePersistent A where
  recover : Trace → A.State
  consistency : ∀ t i, recover (append t i (A.step (recover t) i).2) = (A.step (recover t) i).1

end SelfReference
