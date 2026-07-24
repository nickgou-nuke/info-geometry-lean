import InfoGeometry.SelfReference.Shadow

/-!
# Shadow Cone forwarding shim

To prevent structural duplication and satisfy the deduplication mandate, the
incidence-aware boundary model aliases the canonical definitions from `Shadow.lean`.
-/

namespace InfoGeometry.SelfReference

/-- Redirects to the canonical `ShadowKind`. -/
abbrev ShadowKind := InfoGeometry.SelfReference.Shadow.ShadowKind

/-- Redirects to the canonical `ShadowStatus`. -/
abbrev ShadowStatus := InfoGeometry.SelfReference.Shadow.ShadowStatus

/-- Redirects to the canonical `ShadowCone`. -/
abbrev ShadowCone := InfoGeometry.SelfReference.Shadow.ShadowCone

namespace ShadowCone

open InfoGeometry.SelfReference.Shadow

/-- Checks past boundary. -/
def HasPastIncidence {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.HasPastIncidence S

/-- Checks future boundary. -/
def HasFutureIncidence {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.HasFutureIncidence S

/-- Checks status. -/
def IsRoaming {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.IsRoaming S

def IsIncident {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.IsIncident S

def IsPaired {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.IsPaired S

def IsIntegrated {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.IsIntegrated S

def IsRejected {α : Type*} (S : ShadowCone α) : Prop :=
  Shadow.IsRejected S

/-- Forwarded theorem showing integration status. -/
theorem integrated_has_status_integrated {α : Type*} (S : ShadowCone α)
    (h : IsIntegrated S) :
    S.status = ShadowStatus.integrated := by
  exact h

end ShadowCone

end InfoGeometry.SelfReference
