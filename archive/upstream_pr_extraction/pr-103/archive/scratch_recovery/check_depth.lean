import InfoGeometry.Canonical.CasimirWeylDrazinContext
import InfoGeometry.Meta.Architecture

open InfoGeometry.Meta

def main : IO Unit := do
  let env ← Lean.importModules [{module := `InfoGeometry.Canonical.CasimirWeylDrazinContext}, {module := `InfoGeometry.Meta.Architecture}] {}
  let name := `InfoGeometry.Canonical.CasimirWeylDrazinContext.CasimirWeylDrazinData
  match repDepth? env name with
  | some d => IO.println s!"{name} depth: {d.slug} ({d.toNat})"
  | none => IO.println s!"{name} has no depth tag"

