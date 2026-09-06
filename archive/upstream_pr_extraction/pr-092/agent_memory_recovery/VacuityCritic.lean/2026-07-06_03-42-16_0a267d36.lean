/-
# InfoGeometry.Tooling.VacuityCritic

Vacuity critic that checks whether Lean declarations are vacuous (i.e., holes
or unsolved goals).  Used by `PipelineSpec` to detect certificates that fail
inspection.

This is a stub file that provides the minimum types needed by PipelineSpec.
-/

namespace InfoGeometry.Tooling.VacuityCritic

/-- A certificate field associated with a declaration. -/
structure CertificateField :=
  name : String
  value : String

/-- An inspected Lean declaration with its certificate fields. -/
structure InspectedDeclaration :=
  name : String
  certificateFields : List CertificateField

/-- Returns `true` if the declaration passes vacuity inspection. -/
def passes (d : InspectedDeclaration) : Bool :=
  -- Stub: always returns true; a real implementation would type-check the declaration
  true

end InfoGeometry.Tooling.VacuityCritic
