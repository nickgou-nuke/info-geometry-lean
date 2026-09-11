import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Lean Elab Command

namespace InfoGeometry.Meta.DrazinRefactor

/-- Parse a dotted declaration path into a `Name`. -/
def nameFromDotted (path : String) : Name :=
  (path.splitOn ".").foldl (init := Name.anonymous) fun acc seg =>
    Name.str acc seg

/-- Legacy witness-bearing classical Riesz surface. -/
def legacyClassicalRieszName : Name :=
  nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero"

/-- Legacy compatibility package surface. -/
def legacyInfiniteAssumptionsName : Name :=
  nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.DrazinInfiniteAssumptions"

/-- Existential Riesz-Drazin data owner surface. -/
def legacyCanonicalRieszDataName : Name :=
  nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.exists_rieszDrazinData_endCLM"

/-- Field projections used by witness-readback and projector-readback surfaces. -/
def legacyProjectionTargets : Array Name :=
  #[ nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.D"
   , nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.k"
   , nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.hIsDrazin"
   , nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.hP"
   ]

/-- Auxiliary package-like targets for migration classification. -/
def legacyPackagingTargets : Array Name :=
  #[legacyInfiniteAssumptionsName, legacyCanonicalRieszDataName]

/-- Exclude generated/internal declarations from migration scans. -/
def shouldSkip (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes

/-- True iff an expression mentions a specific constant. -/
def usesConst (e : Expr) (target : Name) : Bool :=
  e.find? (fun sub => sub.isConstOf target) |>.isSome

/-- True iff an expression mentions any constant from a target list. -/
def usesAnyConst (e : Expr) (targets : Array Name) : Bool :=
  targets.any (fun target => usesConst e target)

/-- Return the subset of target constants mentioned in an expression. -/
def usedTargets (e : Expr) (targets : Array Name) : Array Name :=
  targets.filter (fun target => usesConst e target)

/-- Extract the body/proof term where available. -/
def constantValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .axiomInfo _ => none
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | .opaqueInfo _ => none
  | .quotInfo _ => none
  | .inductInfo _ => none
  | .ctorInfo _ => none
  | .recInfo _ => none

/-- Scan declarations whose types mention a legacy constant. -/
def scanTypes (target : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut hits := #[]
  for (declName, ci) in env.constants.toList do
    if shouldSkip declName then
      continue
    if usesConst ci.type target then
      hits := hits.push declName
  pure hits

/-- Scan declarations whose values/proofs mention a legacy constant. -/
def scanValues (target : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut hits := #[]
  for (declName, ci) in env.constants.toList do
    if shouldSkip declName then
      continue
    match constantValue? ci with
    | some val =>
        if usesConst val target then
          hits := hits.push declName
    | none => pure ()
  pure hits

/-- Scan declarations that extract legacy witness fields from values/proofs. -/
def scanProjectionUsage (targets : Array Name) : CoreM (Array (Name × Array Name)) := do
  let env ← getEnv
  let mut hits : Array (Name × Array Name) := #[]
  for (declName, ci) in env.constants.toList do
    if shouldSkip declName then
      continue
    match constantValue? ci with
    | some val =>
        let present := usedTargets val targets
        if !present.isEmpty then
          hits := hits.push (declName, present)
    | none => pure ()
  pure hits

/-- Print a flat hit list with cardinality. -/
def logHits (header : String) (hits : Array Name) : CoreM Unit := do
  logInfo m!"{header}: {hits.size}"
  for declName in hits do
    logInfo m!"  - {declName}"

/-- Pretty label for projection constants in scan logs. -/
def projectionLabel (n : Name) : String :=
  let s := toString n
  match s.splitOn "." |>.reverse with
  | leaf :: _ => leaf
  | [] => s

/-- Print projection-usage hits with exact field-level dependencies. -/
def logProjectionHits (header : String) (hits : Array (Name × Array Name)) : CoreM Unit := do
  logInfo m!"{header}: {hits.size}"
  for (declName, fields) in hits do
    let labels := (fields.toList.map projectionLabel).intersperse ", "
    logInfo m!"  - {declName} [{String.join labels}]"

/--
Classify value-level legacy usage into migration buckets.

`readback` means direct extraction of `(D, k, hIsDrazin)`.
`projector-readback` means direct extraction of `hP`.
`packaging` means dependency on known legacy package surfaces.
-/
def classifyLegacyUsage : CoreM (Array Name × Array Name × Array Name) := do
  let env ← getEnv
  let fieldD := nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.D"
  let fieldK := nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.k"
  let fieldIsD := nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.hIsDrazin"
  let fieldHP := nameFromDotted "InfoGeometry.Canonical.DrazinInfiniteCore.HasClassicalRieszDecompositionAtZero.hP"
  let mut readback : Array Name := #[]
  let mut projector : Array Name := #[]
  let mut packaging : Array Name := #[]
  for (declName, ci) in env.constants.toList do
    if shouldSkip declName then
      continue
    match constantValue? ci with
    | some val =>
        let usesReadbackField :=
          usesConst val fieldD || usesConst val fieldK || usesConst val fieldIsD
        let usesProjectorField := usesConst val fieldHP
        let usesPackaging := usesAnyConst val legacyPackagingTargets
        if usesReadbackField then
          readback := readback.push declName
        if usesProjectorField then
          projector := projector.push declName
        if usesPackaging then
          packaging := packaging.push declName
    | none => pure ()
  pure (readback, projector, packaging)

elab "#find_old_riesz_in_types" : command => do
  let hits ← Command.liftCoreM <| scanTypes legacyClassicalRieszName
  Command.liftCoreM <| logHits
    "Type-level references to HasClassicalRieszDecompositionAtZero"
    hits

elab "#find_old_riesz_in_values" : command => do
  let hits ← Command.liftCoreM <| scanValues legacyClassicalRieszName
  Command.liftCoreM <| logHits
    "Value-level references to HasClassicalRieszDecompositionAtZero"
    hits

elab "#find_riesz_projections" : command => do
  let hits ← Command.liftCoreM <| scanProjectionUsage legacyProjectionTargets
  Command.liftCoreM <| logProjectionHits
    "Value-level extractions of legacy Drazin fields (D, k, hIsDrazin, hP)"
    hits

elab "#classify_old_riesz_usage" : command => do
  let (readback, projector, packaging) ← Command.liftCoreM classifyLegacyUsage
  Command.liftCoreM <| logHits "Readback surfaces (D/k/hIsDrazin)" readback
  Command.liftCoreM <| logHits "Projector-readback surfaces (hP)" projector
  Command.liftCoreM <| logHits "Packaging surfaces" packaging

end InfoGeometry.Meta.DrazinRefactor
