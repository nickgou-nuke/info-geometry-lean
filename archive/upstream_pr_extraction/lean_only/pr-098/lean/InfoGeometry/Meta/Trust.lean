import Lean
import Lean.Util.CollectAxioms
import DAG.Basic
import InfoGeometry.Meta.Admission
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.RegionPolicy
import InfoGeometry.Meta.Vacuity

open Lean

namespace InfoGeometry.Meta

/-- First-pass forbidden axioms beyond explicit `sorryAx` detection. -/
def defaultForbiddenAxioms : List Name := ["admitAx".toName]

/-- Repository kinds audited by the first-pass supervisor. -/
def isAuditableDecl : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => true
  | _ => false

/-- Kind label used by the strict audit surface. -/
def constantKindLabel : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "ax!om"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- Module defining a declaration, falling back to the main module when unavailable. -/
def moduleNameOf (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

private def usesUnsafeDependency (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | none => false
  | some info =>
      if info.isUnsafe then
        true
      else
        let deps := transitivelyUsedConstants env declName
        Id.run do
          let mut found := false
          for dep in deps do
            if found then
              break
            match env.find? dep with
            | some depInfo =>
                if depInfo.isUnsafe then
                  found := true
            | none => pure ()
          found

private def requiredAttrsMissing
    (policy : PolicySnapshot)
    (env : Environment)
    (declName : Name)
    (region : AdmissionRegion)
    (info : ConstantInfo) : List Name :=
  if region != .protectedRegion then
    []
  else if !isAuditableDecl info then
    []
  else if hasExplicitAdmissionMetadata env declName then
    []
  else
    requiredAttrsForRegion policy region

private def hasRepDepthViolation (env : Environment) (declName : Name) : Bool :=
  match repDepth? env declName with
  | some depth =>
      let allowComposite := capstoneAttr.hasTag env declName
      !(taggedDependencyViolations env declName depth allowComposite).isEmpty
  | none => false

private def forbiddenRegionKind
    (region : AdmissionRegion)
    (info : ConstantInfo) : Bool :=
  region == .protectedRegion && constantKindLabel info = "ax!om"

/-- Collect hard-trust evidence for a declaration under the current policy. -/
def collectHardEvidence (policy : PolicySnapshot) (declName : Name) : CoreM HardEvidence := do
  let env ← getEnv
  let some info := env.find? declName
    | return {
        hasSorryAx := false
        forbiddenAxioms := []
        unsafeLeakage := false
        missingRequiredAttrs := []
        repDepthViolation := false
        forbiddenRegionKind := false
      }
  let axioms ← Lean.collectAxioms declName
  let region := regionOfDecl policy declName
  let forbidden :=
    defaultForbiddenAxioms.filter fun axiomName => axioms.contains axiomName
  let missingRequiredAttrs := requiredAttrsMissing policy env declName region info
  return {
    hasSorryAx := axioms.contains ``sorryAx
    forbiddenAxioms := forbidden
    unsafeLeakage := usesUnsafeDependency env declName
    missingRequiredAttrs := missingRequiredAttrs
    repDepthViolation := hasRepDepthViolation env declName
    forbiddenRegionKind := forbiddenRegionKind region info
  }

end InfoGeometry.Meta
