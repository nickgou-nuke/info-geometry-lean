import Mathlib
open Set

/-!
# Shadow Cone — Boundary Object Model of Proof Debt

This file refines the flat shadow inventory into an incidence-aware boundary
object.

The core claim is conservative:
- a shadow may have past/future incidences into the proof graph,
- a shadow may be roaming, incident, paired, integrated, or rejected,
- but no status value is promoted to theorem authority on its own.
-/

namespace InfoGeometry.SelfReference.ShadowCone

/-- Shadow kinds for the boundary-object model. -/
inductive ShadowKind where
  | sorryDebt
  | missingPremise
  | overclaimedBridge
  | archetypeRecurrence
  | failedSynthesis
  | boundaryAnalogy
  | roamingConjecture
deriving DecidableEq, Repr, Inhabited

/-- Incidence status of a shadow cone. -/
inductive ShadowStatus where
  | roaming
  | incident
  | paired
  | integrated
  | rejected
deriving DecidableEq, Repr, Inhabited

/--
An unintegrated apex of a causal cone.

`α` is the type of existing declaration nodes.
-/
structure ShadowCone (α : Type*) where
  apexName : String
  kind : ShadowKind
  status : ShadowStatus
  pastBoundary : Set α
  futureBoundary : Set α
  obstruction : Option String

namespace ShadowCone

variable {α : Type*} (S : ShadowCone α)

/-- The cone has a past incidence when its past boundary is nonempty. -/
def HasPastIncidence : Prop :=
  ∃ a, a ∈ S.pastBoundary

/-- The cone has a future incidence when its future boundary is nonempty. -/
def HasFutureIncidence : Prop :=
  ∃ a, a ∈ S.futureBoundary

/-- The cone is roaming exactly when its status says so. -/
def IsRoaming : Prop :=
  S.status = ShadowStatus.roaming

/-- The cone is incident exactly when its status says so. -/
def IsIncident : Prop :=
  S.status = ShadowStatus.incident

/-- The cone is paired exactly when its status says so. -/
def IsPaired : Prop :=
  S.status = ShadowStatus.paired

/-- The cone is integrated exactly when its status says so. -/
def IsIntegrated : Prop :=
  S.status = ShadowStatus.integrated

/-- The cone is rejected exactly when its status says so. -/
def IsRejected : Prop :=
  S.status = ShadowStatus.rejected

/-- An integrated shadow has status `integrated`. -/
theorem integrated_has_status_integrated
    (h : IsIntegrated S) :
    S.status = ShadowStatus.integrated :=
  h

end ShadowCone

end InfoGeometry.SelfReference.ShadowCone
