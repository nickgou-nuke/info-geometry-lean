import Lean

/-!
# Vacuity Role Attributes

Lightweight semantic role tags for theorem-surface accounting.

These tags live in `InfoGeometry.Meta` so domain files can annotate support
declarations without importing the full linter layer.
-/

open Lean

namespace InfoGeometry.Meta

/-- Support lemma not counted as theorem-level mathematical content. -/
initialize infrastructureAttr : TagAttribute ←
  registerTagAttribute `infrastructure
    "Mark a declaration as infrastructure — not theorem-level content."

/-- Public terminal declaration with no expected downstream reuse. -/
initialize terminalAttr : TagAttribute ←
  registerTagAttribute `terminal
    "Mark a public declaration as terminal — no expected downstream reuse."

/-- Public wrapper/restatement kept for reader-facing surface reasons. -/
initialize expositoryAttr : TagAttribute ←
  registerTagAttribute `expository
    "Mark a declaration as an expository wrapper kept for readability."

/-- Ordered list of supported vacuity-role tags. -/
def vacuityRoleTagNames : Array Name :=
  #[`infrastructure, `terminal, `expository]

/-- Collect all vacuity-role tags attached to a declaration. -/
def vacuityRoleTagsOf (env : Environment) (declName : Name) : Array Name :=
  Id.run do
    let mut tags := #[]
    if infrastructureAttr.hasTag env declName then
      tags := tags.push `infrastructure
    if terminalAttr.hasTag env declName then
      tags := tags.push `terminal
    if expositoryAttr.hasTag env declName then
      tags := tags.push `expository
    tags

/-- Collect all vacuity-role tags attached to a declaration as strings. -/
def vacuityRoleTagStringsOf (env : Environment) (declName : Name) : Array String :=
  (vacuityRoleTagsOf env declName).map toString

/-- Test whether a declaration carries any vacuity-role annotation. -/
def isVacuityRoleTagged (env : Environment) (declName : Name) : Bool :=
  !(vacuityRoleTagsOf env declName).isEmpty

end InfoGeometry.Meta
