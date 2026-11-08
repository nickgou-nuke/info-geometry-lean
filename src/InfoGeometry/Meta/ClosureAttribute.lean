import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Trust

open Lean Meta

namespace InfoGeometry.Meta

/--
⚓ THE CLOSURE READY ATTRIBUTE
A declaration marked `@[closure_ready]` is claimed to be formally closed,
anchored to the DAG, and free of `sorry` or `admit`.
-/
initialize closureReadyAttr : TagAttribute ←
  registerTagAttribute `closure_ready "Mark a declaration as formally closed and audit-ready."

/-- Check if a declaration is marked as closure-ready. -/
def isClosureReady (env : Environment) (declName : Name) : Bool :=
  closureReadyAttr.hasTag env declName

end InfoGeometry.Meta
