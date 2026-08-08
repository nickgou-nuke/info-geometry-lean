/-
# InfoGeometry.Tooling.VacuityCritic

Vacuity critic that checks whether Lean declarations are vacuous (i.e., holes
or unsolved goals).  Used by `PipelineSpec` to detect certificates that fail
inspection.

This file is only the typed transport model used by `PipelineSpec`.  Kernel-level
vacuity checks live in `InfoGeometry.Lint.Vacuity`; this model must therefore
fail closed when no inspection payload is present.
-/

namespace InfoGeometry.Tooling.VacuityCritic

/-- One concrete field emitted by an external inspection pass. -/
structure InspectionField where
  key : String
  value : String

/-- A field is usable only when both its key and value are present and not a
known placeholder token. -/
def InspectionField.hasContent (field : InspectionField) : Bool :=
  !field.key.isEmpty && !field.value.isEmpty &&
    field.value != "sorry" && field.value != "sorry"

/-- An inspected Lean declaration together with its concrete inspection fields. -/
structure InspectedDeclaration where
  name : String
  fields : List InspectionField

/-- Field-level inspection fails closed on an empty payload. -/
def InspectedDeclaration.fieldsPass : List InspectionField → Bool
  | [] => false
  | fields => fields.all InspectionField.hasContent

/-- Executable inspection predicate used by the pipeline model. -/
def InspectedDeclaration.hasInspectablePayload (d : InspectedDeclaration) : Bool :=
  !d.name.isEmpty && InspectedDeclaration.fieldsPass d.fields

/-- Returns `true` exactly when the supplied inspection payload is present and
contains no known placeholder token. -/
def passes (d : InspectedDeclaration) : Bool :=
  d.hasInspectablePayload

theorem passes_empty_fields (name : String) :
    passes ({ name := name, fields := [] } : InspectedDeclaration) = false := by
  simp [passes, InspectedDeclaration.hasInspectablePayload,
    InspectedDeclaration.fieldsPass]

end InfoGeometry.Tooling.VacuityCritic
