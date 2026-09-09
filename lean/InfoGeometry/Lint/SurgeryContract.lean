import Lean

/-!
# LeanTrail Surgery Contract

This module records the Lean-side names for the biopsy and surgery control-plane
contract.  It deliberately contains only serializable data shapes.  Graph
reachability, SCC independence, byte-patch validation, and `shadow_approved`
semantics remain external operational checks; the Lean kernel and build gates
remain the proof authority.
-/

open Lean

namespace InfoGeometry.Lint

/-- Vacuity classification used by LeanTrail biopsy packets. -/
inductive VacuityRole where
  | fake_transport
  | pure_conductor
  | dead_socket
  | gate
  | orphan_genuine
  | closure_debt
  | unknown
deriving Repr, BEq, Inhabited

/-- Contamination classification used by LeanTrail audit packets. -/
inductive ContaminationState where
  | clean
  | honest_sorry
  | forbidden_axiom
  | opaque_boundary
  | local_axiom
  | contaminated
deriving Repr, BEq, Inhabited

/-- Source provenance classification for declarations eligible for source patching. -/
inductive SourceInfoKind where
  | original
  | syntheticOrNone
deriving Repr, BEq, Inhabited

/-- Stable typed boundary for declaration-local LeanTrail biopsy output. -/
structure BiopsyContract where
  declName : Name
  isProp : Bool
  vacuityRole : VacuityRole
  contamination : ContaminationState
  declSpanKind : String
  patchSpanKind : String
  sourceInfoKind : SourceInfoKind
  certificateRef : String
  auditHash : String
deriving Repr, Inhabited

end InfoGeometry.Lint
