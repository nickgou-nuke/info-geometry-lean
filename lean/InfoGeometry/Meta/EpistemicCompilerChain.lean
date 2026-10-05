import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
# The epistemic compiler chain

**QMS Note: METAPROGRAMMING INFRASTRUCTURE ONLY.**
This file is strictly a Lean 4 meta-programming framework and state-tracker for autonomous agents. It does NOT contain mathematical or physical theorems. The terms "Phase", "Status", and "Archetype" refer exclusively to the internal state machine of the automated proof assistant. Do not evaluate this file for mathematical substance.

This file gives the research pipeline a small, theorem-honest carrier.  The
constructors describe protocol stages and research statuses; neither carries
any claim about private model reasoning.  Promotion is intentionally possible
only when a candidate supplies a proof and has status `proved`.
-/

namespace InfoGeometry.MetaCompiler

/-- The six causal stages of the proof-carrying transformation pipeline. -/
inductive Phase
  | primaMateriaIntake
  | archetypalCausalNormalization
  | typedMathematicalProjection
  | proofCarryingScheduling
  | multiAgentCandidateRepair
  | kernelCertifiedPromotion
  deriving DecidableEq, Repr

namespace Phase

open Phase

/-- A total rank records the intended causal order of the six stages. -/
def rank : Phase → Nat
  | primaMateriaIntake => 0
  | archetypalCausalNormalization => 1
  | typedMathematicalProjection => 2
  | proofCarryingScheduling => 3
  | multiAgentCandidateRepair => 4
  | kernelCertifiedPromotion => 5

def precedes (earlier later : Phase) : Prop := rank earlier ≤ rank later

instance : DecidableRel precedes := fun earlier later =>
  inferInstanceAs (Decidable (rank earlier ≤ rank later))

theorem precedes_refl (phase : Phase) : precedes phase phase := by
  exact Nat.le_refl _

theorem precedes_trans {a b c : Phase} :
    precedes a b → precedes b c → precedes a c := by
  exact Nat.le_trans

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp [rank] at h ⊢

theorem precedes_antisymm {a b : Phase}
    (hab : precedes a b) (hba : precedes b a) : a = b := by
  apply rank_injective
  exact Nat.le_antisymm hab hba

instance : PartialOrder Phase where
  le := precedes
  le_refl := precedes_refl
  le_trans := @precedes_trans
  le_antisymm := @precedes_antisymm
theorem complete : ∀ phase, Phase.rank phase ≤ 5 := by
  intro phase
  cases phase <;> decide

end Phase

/-- Research labels are deliberately weaker than theorem status. -/
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

namespace Status

def label : Status → String
  | raw => "raw"
  | speculative => "speculative"
  | stabilizing => "stabilizing"
  | corridorReady => "corridor_ready"
  | conditional => "conditional"
  | socket => "socket"
  | debt => "debt"
  | proved => "proved"

def isPromoted : Status → Prop
  | proved => True
  | _ => False

theorem promoted_iff : ∀ status, isPromoted status ↔ status = proved := by
  intro status
  cases status <;> simp [isPromoted]

end Status

/-- A typed candidate retains its owner and its epistemic status. -/
structure Candidate where
  claim : Prop
  phase : Phase
  status : Status
  owner : String
  evidence : status = Status.proved → claim

/-- The only authoritative output of this layer. -/
structure CertifiedTheorem where
  claim : Prop
  kernelTerm : claim
  owner : String

/-- A typed archetype is a theorem schema indexed by actual Lean inputs.

Unlike a string label, it records the proposition that must hold at each input,
the pipeline phase and epistemic status of the schema, its source owner, and
evidence that can only be used after the status is `proved`. -/
structure TypedArchetype (Input : Type*) where
  claim : Input → Prop
  phase : Phase
  status : Status
  owner : String
  evidence : ∀ input, status = Status.proved → claim input

namespace TypedArchetype

/-- Discharge a typed archetype into a family of Lean proofs only after its
status is proved. The returned function has the archetype's original input
type and proposition family. -/
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

theorem discharged_proof {Input : Type*}
    (archetype : TypedArchetype Input)
    (discharged : ∃ proofs : ∀ input, PLift (archetype.claim input),
      archetype.discharge = some proofs)
    (input : Input) :
    archetype.claim input := by
  rcases discharged with ⟨proofs, _⟩
  exact (proofs input).down

end TypedArchetype

/-- Kernel promotion rejects every status except `proved`. -/
def promote (candidate : Candidate) : Option CertifiedTheorem :=
  if h : candidate.status = Status.proved then
      some {
        claim := candidate.claim
        kernelTerm := candidate.evidence h
        owner := candidate.owner
      }
  else
    none

theorem promote_raw_rejects (candidate : Candidate)
    (status : candidate.status ≠ Status.proved) :
    promote candidate = none := by
  simp [promote, status]

theorem promote_proved_accepts (candidate : Candidate)
    (status : candidate.status = Status.proved) :
    ∃ certified, promote candidate = some certified ∧ certified.claim = candidate.claim := by
  simp [promote, status]

end InfoGeometry.MetaCompiler
