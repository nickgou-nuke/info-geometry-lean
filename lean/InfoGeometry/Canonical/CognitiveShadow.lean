import InfoGeometry.Canonical.CognitiveArchetype

/-!
# InfoGeometry.Canonical.CognitiveShadow

Canonical shadow inventory for explicit debt, obfuscation, and critic-lane
roles.

This is a typed record of what the system is refusing, delaying, or
quarantining. It does not prove anything on its own.
-/

namespace InfoGeometry.Canonical.CognitiveShadow

inductive ShadowKind
  | honestSorryTriage
  | obfuscationSuspicion
  | orphanGenuineReview
  | axiomaticFrontierReview
  | alignmentCandidateReview
  | educationalAliasProtection
  deriving DecidableEq

inductive ShadowPolicy
  | proofHoleTriage
  | quarantineExplicitBridge
  | preserveAndExpose
  | quarantineAndBridge
  | kernelObligation
  | blockDestructiveSurgery
  deriving DecidableEq

inductive ShadowStatus
  | recognized
  deriving DecidableEq

def ShadowKind.label : ShadowKind → String
  | .honestSorryTriage => "HonestSorryTriage"
  | .obfuscationSuspicion => "ObfuscationSuspicion"
  | .orphanGenuineReview => "OrphanGenuineReview"
  | .axiomaticFrontierReview => "AxiomaticFrontierReview"
  | .alignmentCandidateReview => "AlignmentCandidateReview"
  | .educationalAliasProtection => "EducationalAliasProtection"

def ShadowPolicy.label : ShadowPolicy → String
  | .proofHoleTriage => "route to proof-hole triage"
  | .quarantineExplicitBridge => "quarantine or require explicit bridge obligation"
  | .preserveAndExpose => "preserve and bridge/expose"
  | .quarantineAndBridge => "quarantine or bridge; do not vacuum"
  | .kernelObligation => "route through kernel obligation"
  | .blockDestructiveSurgery => "block destructive surgery"

def ShadowStatus.label : ShadowStatus → String
  | .recognized => "recognized"

/-- Shadow modes recognized by the LeanTrail critic lane. -/
structure ShadowTemplate where
  name : ShadowKind
  triggerTerms : Array String
  criticKind : ShadowKind
  policyEffect : ShadowPolicy
  status : ShadowStatus

namespace ShadowTemplate

/-- A shadow template is detected when all trigger terms appear in the observed terms. -/
def detects (T : ShadowTemplate) (observedTerms : Array String) : Bool :=
  T.triggerTerms.all (fun t => observedTerms.contains t)

end ShadowTemplate

/-- A detected shadow pattern with its observed terms. -/
structure DetectedShadow where
  template : ShadowTemplate
  observedTerms : Array String

namespace DetectedShadow

/-- Validity is conservative trigger matching. -/
def isValid (S : DetectedShadow) : Bool :=
  S.template.detects S.observedTerms

end DetectedShadow

/-- Known shadow modes from the critic-lane taxonomy. -/
def knownShadows : Array ShadowTemplate :=
  #[
    { name := .honestSorryTriage
      triggerTerms := #["sorry", "proof debt", "hole"]
      criticKind := .honestSorryTriage
      policyEffect := .proofHoleTriage
      status := .recognized },
    { name := .obfuscationSuspicion
      triggerTerms := #["axiom", "opaque", "certificate", "socket", "witness"]
      criticKind := .obfuscationSuspicion
      policyEffect := .quarantineExplicitBridge
      status := .recognized },
    { name := .orphanGenuineReview
      triggerTerms := #["orphan", "genuine", "dense", "valid mathematics"]
      criticKind := .orphanGenuineReview
      policyEffect := .preserveAndExpose
      status := .recognized },
    { name := .axiomaticFrontierReview
      triggerTerms := #["axiomatic frontier", "axiom", "opaque boundary"]
      criticKind := .axiomaticFrontierReview
      policyEffect := .quarantineAndBridge
      status := .recognized },
    { name := .alignmentCandidateReview
      triggerTerms := #["Hodge", "de Bruijn", "structural overlap", "bridge candidate"]
      criticKind := .alignmentCandidateReview
      policyEffect := .kernelObligation
      status := .recognized },
    { name := .educationalAliasProtection
      triggerTerms := #["pedagogical", "wrapper", "alias", "educational"]
      criticKind := .educationalAliasProtection
      policyEffect := .blockDestructiveSurgery
      status := .recognized }
  ]

/-- Return all detected shadow patterns with their observed terms. -/
def detectedShadows (observedTerms : Array String) : Array DetectedShadow :=
  knownShadows.filter (fun T => T.detects observedTerms) |>.map (fun T =>
    { template := T, observedTerms := observedTerms })

end InfoGeometry.Canonical.CognitiveShadow
