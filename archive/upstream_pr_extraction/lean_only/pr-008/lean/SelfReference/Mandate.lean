import SelfReference.Core
import SelfReference.Problem

/-!
# SelfReference.Mandate

Simplified mandate-state agent model for self-reference workflows.
-/

namespace SelfReference

/-- A simplified, buildable state carrier for a mandate-driven agent. -/

structure MandateState where
  mandate      : List String
  sebf         : List String
  verified     : List String
  openProblems : List String -- Simplified to avoid mutual recursion
  citations    : List String
  revision     : Nat
  terminalFail : Bool

/-- Outputs produced by the mandate agent at each transition step. -/
inductive MandateOutput where
  | latexChunk : List String → MandateOutput
  | spawnedProblem : String → MandateOutput
  | revisedMandate : List String → MandateOutput

/-- External inputs consumed by the mandate agent. -/
inductive MandateInput where
  | userMsg : String → MandateInput
  | replaySEBF : List String → MandateInput
  | solveProblem : String → MandateInput
  | adoptRevision : List String → MandateInput

/-- Build an `Agent` from a mandate-specific transition function. -/
def mandateAgent
    (step_fn : MandateState → MandateInput → MandateState × MandateOutput) :
    Agent where
  State := MandateState
  Input := MandateInput
  Output := MandateOutput
  step := step_fn

end SelfReference
