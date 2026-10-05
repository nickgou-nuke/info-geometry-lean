import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace InfoGeometry.MetaCompiler

inductive Phase
  | primaMateriaIntake
  | archetypalCausalNormalization
  | typedMathematicalProjection
  | proofCarryingScheduling
  | multiAgentCandidateRepair
  | kernelCertifiedPromotion
  deriving DecidableEq, Repr

inductive Status
  | raw
  | speculative
  | stabilizing
  | corridorReady
  | conditional
  | socket
  | debt
  | proved
  deriving DecidableEq, Repr

structure TypedArchetype (Input : Type*) where
  claim : Input → Prop
  phase : Phase
  status : Status
  owner : String
  evidence : ∀ input, status = Status.proved → claim input

namespace TypedArchetype

def discharge {Input : Type*} (archetype : TypedArchetype Input) :
    Option (∀ input, PLift (archetype.claim input)) :=
  if h : archetype.status = Status.proved then
    some (fun input => ⟨archetype.evidence input h⟩)
  else
    none

theorem discharge_rejects_unproved {Input : Type*}
    (archetype : TypedArchetype Input)
    (status : archetype.status ≠ Status.proved) :
    archetype.discharge = none := by
  simp [discharge, status]

theorem discharge_proved {Input : Type*}
    (archetype : TypedArchetype Input)
    (status : archetype.status = Status.proved) :
    ∃ proofs : ∀ input, PLift (archetype.claim input),
      archetype.discharge = some proofs := by
  use (fun input => ⟨archetype.evidence input status⟩)
  simp [discharge, status]

end TypedArchetype
end InfoGeometry.MetaCompiler
