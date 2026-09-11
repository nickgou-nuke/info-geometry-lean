import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Admission
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.Vacuity

open Lean

namespace InfoGeometry.Meta

/-- Region tier used by the strict admission audit. -/
inductive AdmissionRegion where
  | protectedRegion
  | bridgeRegion
  | workbenchRegion
  | ordinaryRegion
  deriving Repr, Inhabited, DecidableEq, BEq

def AdmissionRegion.asString : AdmissionRegion → String
  | .protectedRegion => "protected"
  | .bridgeRegion => "bridge"
  | .workbenchRegion => "workbench"
  | .ordinaryRegion => "ordinary"

/-- Default repository region policy for the first-pass admission supervisor. -/
def defaultPolicySnapshot : PolicySnapshot :=
  { protectedNamespaces := ["InfoGeometry.Canonical".toName, "InfoGeometry.Meta".toName]
    bridgeNamespaces := ["InfoGeometry.LLM".toName, "Agent".toName, "DAG".toName]
    workbenchNamespaces := ["InfoGeometry.Unstable".toName, "InfoGeometry.Exploration".toName]
    requiredAttrsByRegion := [("protected", [`rep_depth])] }

private def inRegionPrefixes (prefixes : List Name) (declName : Name) : Bool :=
  prefixes.any fun prefixName => Name.isPrefixOf prefixName declName

/-- Compute the admission region for a declaration name from the policy snapshot. -/
def regionOfDecl (policy : PolicySnapshot) (declName : Name) : AdmissionRegion :=
  if inRegionPrefixes policy.protectedNamespaces declName then
    .protectedRegion
  else if inRegionPrefixes policy.bridgeNamespaces declName then
    .bridgeRegion
  else if inRegionPrefixes policy.workbenchNamespaces declName then
    .workbenchRegion
  else
    .ordinaryRegion

/-- Required admission attributes for a given region label. -/
def requiredAttrsForRegion (policy : PolicySnapshot) (region : AdmissionRegion) : List Name :=
  let regionKey := region.asString
  match policy.requiredAttrsByRegion.find? (fun (label, _) => label = regionKey) with
  | some (_, attrs) => attrs
  | none => []

/-- Explicit role/depth metadata recognized by the supervisor. -/
def hasExplicitAdmissionMetadata (env : Environment) (declName : Name) : Bool :=
  (repDepth? env declName).isSome ||
    capstoneAttr.hasTag env declName ||
    isVacuityRoleTagged env declName

/-- Region-based postprocessing after hard/soft evidence evaluation. -/
def adjustDecisionForRegion (region : AdmissionRegion) (decision : AdmissionDecision) :
    AdmissionDecision :=
  match decision with
  | .blocked => .blocked
  | .needsReview => .needsReview
  | .admitted =>
      match region with
      | .bridgeRegion | .workbenchRegion => .notPromotable
      | .protectedRegion | .ordinaryRegion => .admitted
  | .notPromotable => .notPromotable

end InfoGeometry.Meta
