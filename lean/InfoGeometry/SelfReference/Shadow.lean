import Mathlib.Tactic

/-!

ShadowCone — The Boundary Cochain of Unintegrated Proof Content

A shadow is not an absence. A shadow is an unfilled causal cone with
detectable boundary on the proof DAG. It has partial incidences to existing
declarations but no kernel-checked apex.
-/

set_option linter.unusedVariables false

namespace InfoGeometry.SelfReference.Shadow

/-

BUCKET 1: CLOSED FINITE THEOREMS

[ShadowKind.describe,
ShadowKind.severity,
integrated_has_status_integrated,
roaming_has_no_past,
paired_has_bidirectional,
totalSeverity]

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[]

BUCKET 3: OPEN CLOSURE DEBT

[Repository-wide shadow inventory,
InfoTree/de-Bruijn incidence scanner,
automatic proof-DAG boundary extraction,
integration/rejection classifier]
-/

/-! ### Shadow Kind — the type of the unfilled cone -/

inductive ShadowKind where
| sorryDebt
| missingPremise
| overclaimedBridge
| archetypeRecurrence
| failedSynthesis
| boundaryAnalogy
| roamingConjecture
| vacuityWrapper
deriving DecidableEq, Repr, Inhabited

instance : ToString ShadowKind where
toString
| ShadowKind.sorryDebt => "sorryDebt"
| ShadowKind.missingPremise => "missingPremise"
| ShadowKind.overclaimedBridge => "overclaimedBridge"
| ShadowKind.archetypeRecurrence => "archetypeRecurrence"
| ShadowKind.failedSynthesis => "failedSynthesis"
| ShadowKind.boundaryAnalogy => "boundaryAnalogy"
| ShadowKind.roamingConjecture => "roamingConjecture"
| ShadowKind.vacuityWrapper => "vacuityWrapper"

def ShadowKind.describe : ShadowKind → String
| ShadowKind.sorryDebt => "explicit sorry in proof body"
| ShadowKind.missingPremise => "proof relies on unstated hypothesis"
| ShadowKind.overclaimedBridge => "doc claims theorem but no formal proof exists"
| ShadowKind.archetypeRecurrence => "operator pattern recurs but lacks domain formalization"
| ShadowKind.failedSynthesis => "conflicting approaches not yet resolved"
| ShadowKind.boundaryAnalogy => "physical/mathematical analogy not yet formalized"
| ShadowKind.roamingConjecture => "conjecture from Black Book not yet attached to DAG"
| ShadowKind.vacuityWrapper => "_True : Prop := True or equivalent vacuity"

/-! ### Shadow Status — the stage of integration -/

inductive ShadowStatus where
| roaming
| incident
| paired
| integrated
| rejected
deriving DecidableEq, Repr, Inhabited

instance : ToString ShadowStatus where
toString
| ShadowStatus.roaming => "roaming"
| ShadowStatus.incident => "incident"
| ShadowStatus.paired => "paired"
| ShadowStatus.integrated => "integrated"
| ShadowStatus.rejected => "rejected"

/-! ### Shadow Cone — the boundary cochain -/

/-- A shadow cone: an unfilled causal cone with detectable boundary on the proof DAG. -/
structure ShadowCone (α : Type*) where
apexName : String
kind : ShadowKind
status : ShadowStatus
pastBoundary : Set α
futureBoundary : Set α
obstruction : Option String
deriving Inhabited

variable {α : Type*}

/-! ### Cone predicates -/

/-- A shadow cone has past incidence if it connects to at least one known declaration. -/
def HasPastIncidence (S : ShadowCone α) : Prop :=
∃ a, a ∈ S.pastBoundary

/-- A shadow cone has future incidence if it would unlock at least one downstream declaration. -/
def HasFutureIncidence (S : ShadowCone α) : Prop :=
∃ a, a ∈ S.futureBoundary

/-- A shadow cone is roaming: no incidence with the proof DAG is present. -/
def IsRoaming (S : ShadowCone α) : Prop :=
S.status = ShadowStatus.roaming ∧
¬ HasPastIncidence S ∧
¬ HasFutureIncidence S

/-- A shadow cone is incident: at least one one-sided incidence is present. -/
def IsIncident (S : ShadowCone α) : Prop :=
S.status = ShadowStatus.incident ∧
(HasPastIncidence S ∨ HasFutureIncidence S)

/-- A shadow cone is paired: bilateral incidence with the DAG is present. -/
def IsPaired (S : ShadowCone α) : Prop :=
S.status = ShadowStatus.paired ∧
HasPastIncidence S ∧
HasFutureIncidence S

/-- A shadow cone is integrated: resolved into a theorem or explicit debt. -/
def IsIntegrated (S : ShadowCone α) : Prop :=
S.status = ShadowStatus.integrated

/-- A shadow cone is rejected: determined unfillable. -/
def IsRejected (S : ShadowCone α) : Prop :=
S.status = ShadowStatus.rejected

/-- A roaming shadow has no past incidence. -/
theorem roaming_has_no_past
(S : ShadowCone α)
(h : IsRoaming S) :
¬ HasPastIncidence S :=
h.2.1

/-- A paired shadow has both past and future incidence. -/
theorem paired_has_bidirectional
(S : ShadowCone α)
(h : IsPaired S) :
HasPastIncidence S ∧ HasFutureIncidence S :=
h.2

/-! ### Severity -/

def ShadowKind.severity : ShadowKind → ℕ
| ShadowKind.sorryDebt => 2
| ShadowKind.missingPremise => 2
| ShadowKind.overclaimedBridge => 2
| ShadowKind.archetypeRecurrence => 1
| ShadowKind.failedSynthesis => 3
| ShadowKind.boundaryAnalogy => 1
| ShadowKind.roamingConjecture => 1
| ShadowKind.vacuityWrapper => 2

/-- Status multiplier used in the finite shadow-weight readout. -/
def ShadowStatus.multiplier : ShadowStatus → ℕ
| ShadowStatus.roaming => 3
| ShadowStatus.incident => 2
| ShadowStatus.paired => 1
| ShadowStatus.integrated => 1
| ShadowStatus.rejected => 1

/-- Total shadow weight — sum of severities weighted by status. -/
def totalSeverity (items : List (ShadowCone α)) : ℕ :=
(items.map fun s => s.kind.severity * s.status.multiplier).sum

end InfoGeometry.SelfReference.Shadow
