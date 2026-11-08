import InfoGeometry.Canonical.CognitiveArchetype
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.CognitiveShadow

Canonical shadow inventory for explicit debt, obfuscation, and critic-lane
roles.

This is a typed record of what the system is refusing, delaying, or
quarantining. It does not prove anything on its own.
-/

namespace InfoGeometry.Canonical.CognitiveShadow

/-- Shadow modes recognized by the LeanTrail critic lane. -/
structure ShadowTemplate where
  name : String
  triggerTerms : Array String
  criticKind : String
  policyEffect : String
  status : String

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
    { name := "HonestSorryTriage"
      triggerTerms := #["sorry", "proof debt", "hole"]
      criticKind := "honest_sorry_triage"
      policyEffect := "route to proof-hole triage"
      status := "recognized" },
    { name := "ObfuscationSuspicion"
      triggerTerms := #["axiom", "opaque", "certificate", "socket", "witness"]
      criticKind := "obfuscation_suspicion"
      policyEffect := "quarantine or require explicit bridge obligation"
      status := "recognized" },
    { name := "OrphanGenuineReview"
      triggerTerms := #["orphan", "genuine", "dense", "valid mathematics"]
      criticKind := "orphan_genuine_review"
      policyEffect := "preserve and bridge/expose"
      status := "recognized" },
    { name := "AxiomaticFrontierReview"
      triggerTerms := #["axiomatic frontier", "axiom", "opaque boundary"]
      criticKind := "axiomatic_frontier_review"
      policyEffect := "quarantine or bridge; do not vacuum"
      status := "recognized" },
    { name := "AlignmentCandidateReview"
      triggerTerms := #["Hodge", "de Bruijn", "structural overlap", "bridge candidate"]
      criticKind := "alignment_candidate_review"
      policyEffect := "route through kernel obligation"
      status := "recognized" },
    { name := "EducationalAliasProtection"
      triggerTerms := #["pedagogical", "wrapper", "alias", "educational"]
      criticKind := "educational_alias_protection"
      policyEffect := "block destructive surgery"
      status := "recognized" }
  ]

/-- Return the names of shadow templates detected by the observed terms. -/
def detectShadows (observedTerms : Array String) : Array String :=
  knownShadows.filter (fun T => T.detects observedTerms) |>.map (fun T => T.name)

/-- Return all detected shadow patterns with their observed terms. -/
def detectedShadows (observedTerms : Array String) : Array DetectedShadow :=
  knownShadows.filter (fun T => T.detects observedTerms) |>.map (fun T =>
    { template := T, observedTerms := observedTerms })

end InfoGeometry.Canonical.CognitiveShadow
