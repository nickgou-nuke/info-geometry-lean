/-!
# InfoGeometry.Canonical.CognitiveLineage

Canonical lineage scaffold for the black-book-to-theorem corridor.

This file records the path from symbolic seed to theorem authority as data.
It does not claim that a seed is a theorem, nor that lineage metadata proves
anything on its own.
-/

noncomputable section

namespace CognitiveLineage

/--
Typed lineage record for a single theorem-factory corridor.

The record keeps the black-book/source signal separate from the formal output
and explicit residual debt.
-/
structure CognitiveLineage where
  /-- Stable continuity identifier. -/
  lineageId : String

  /-- Human-readable source or black-book anchor. -/
  sourceAnchor : String

  /-- Conjectural or symbolic seed text. -/
  symbolicSeed : String

  /-- Candidate theorem names for the corridor. -/
  theoremCandidates : Array Lean.Name

  /-- Theorems currently owned by this lineage. -/
  ownedTheorems : Array Lean.Name

  /-- Explicit remaining debt for this lineage. -/
  shadowDebt : Array String

  /-- Archive or packet manifest refs for this lineage. -/
  manifests : Array String

  /-- Current lineage status. -/
  status : String

namespace CognitiveLineage

variable (L : CognitiveLineage)

/-- Number of candidate theorem names tracked by the lineage. -/
def theoremCandidateCount : Nat :=
  Array.size (α := Lean.Name) L.theoremCandidates

/-- Number of owned theorem names tracked by the lineage. -/
def ownedTheoremCount : Nat :=
  Array.size (α := Lean.Name) L.ownedTheorems

/-- Number of explicit debt markers tracked by the lineage. -/
def debtCount : Nat :=
  Array.size (α := String) L.shadowDebt

/-- Number of archived/manifests refs tracked by the lineage. -/
def manifestCount : Nat :=
  Array.size (α := String) L.manifests

/-- A lineage is debt-free when no explicit shadow debt remains. -/
def debtFree : Prop :=
  L.shadowDebt.isEmpty

/-- A lineage is proof-bearing when it owns at least one theorem. -/
def proofBearing : Prop :=
  ¬ L.ownedTheorems.isEmpty

/-- A lineage is candidate-bearing when it still has open theorem candidates. -/
def candidateBearing : Prop :=
  ¬ L.theoremCandidates.isEmpty

/-- Compact summary of a lineage corridor. -/
structure Summary where
  theoremCandidateCount : Nat
  ownedTheoremCount : Nat
  debtCount : Nat
  manifestCount : Nat
  status : String

/-- The current lineage summary. -/
def summary : Summary :=
  { theoremCandidateCount := L.theoremCandidateCount
    ownedTheoremCount := L.ownedTheoremCount
    debtCount := L.debtCount
    manifestCount := L.manifestCount
    status := L.status }

end CognitiveLineage

end CognitiveLineage
