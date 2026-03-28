import Lean
import DAG.Basic

open Lean Elab Command

namespace InfoGeometry.Meta

/-- Representation-depth ladder for the stable information-geometry spine. -/
inductive RepDepth where
  | count
  | projective
  | operator
  | krein
  | transport
  | thermo
  deriving DecidableEq, Repr, Inhabited

/-- Numeric depth index used by the architecture auditor. -/
def RepDepth.toNat : RepDepth → Nat
  | .count => 0
  | .projective => 1
  | .operator => 2
  | .krein => 3
  | .transport => 4
  | .thermo => 5

/-- Parse attribute syntax into the internal representation depth. -/
def parseRepDepth? (n : Name) : Option RepDepth :=
  match n.eraseMacroScopes with
  | `count => some .count
  | `projective => some .projective
  | `operator => some .operator
  | `krein => some .krein
  | `transport => some .transport
  | `thermo => some .thermo
  | _ => none

syntax (name := rep_depth) "rep_depth " ident : attr

/-- Attach a representation depth to a declaration participating in the stable spine. -/
initialize repDepthAttr : ParametricAttribute RepDepth ←
  registerParametricAttribute {
    name := `rep_depth
    descr := "Assign a representation depth to a declaration in the stable spine."
    getParam := fun _ stx => do
      match stx with
      | `(attr| rep_depth $id:ident) =>
          match parseRepDepth? id.getId with
          | some d => pure d
          | none =>
              throwError "invalid `rep_depth` value `{id.getId}`; expected count, projective, operator, krein, transport, or thermo"
      | _ => throwUnsupportedSyntax
  }

/-- Mark a theorem as a composite capstone exempt from strict adjacency. -/
initialize capstoneAttr : TagAttribute ←
  registerTagAttribute `capstone
    "Mark a theorem as a capstone composition exempt from adjacency policing."

/-- Look up the representation depth attached to a declaration, if any. -/
def repDepth? (env : Environment) (declName : Name) : Option RepDepth :=
  repDepthAttr.getParam? env declName

/-- True iff the constant info describes a theorem. -/
def isTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- Transitive closure of constants used by a declaration body or proof term. -/
def transitivelyUsedConstants (env : Environment) (root : Name) : NameSet := Id.run do
  let mut used : NameSet := {}
  let mut frontier : NameSet := {}
  if let some info := env.find? root then
    for (dep, _) in DAG.edgesFromConstantInfo info do
      frontier := frontier.insert dep
  while !frontier.isEmpty do
    let current := frontier.min!
    frontier := frontier.erase current
    if used.contains current then
      continue
    used := used.insert current
    if let some info := env.find? current then
      for (dep, _) in DAG.edgesFromConstantInfo info do
        if !used.contains dep then
          frontier := frontier.insert dep
  return used

/-- Direct constants used by a declaration body or proof term. -/
def directlyUsedConstants (env : Environment) (root : Name) : NameSet := Id.run do
  let mut used : NameSet := {}
  if let some info := env.find? root then
    for (dep, _) in DAG.edgesFromConstantInfo info do
      used := used.insert dep
  return used

/-- Architecture violations detected from direct tagged dependencies. -/
def taggedDependencyViolations
    (env : Environment) (declName : Name) (depth : RepDepth) (allowComposite : Bool) : Array MessageData := Id.run do
  let mut out := #[]
  let deps := directlyUsedConstants env declName
  for dep in deps do
    if let some depDepth := repDepth? env dep then
      let d := depth.toNat
      let d' := depDepth.toNat
      if d' > d then
        out := out.push m!"REGRESSION: {declName} (L{d}) directly depends on {dep} (L{d'})."
      else if !allowComposite && d' + 1 < d then
        out := out.push m!"WORMHOLE: {declName} (L{d}) directly depends on {dep} (L{d'})."
  out

/-- Lean-native architecture audit for the tagged stable spine. -/
def checkArchitectureTopology : CoreM Unit := do
  let env ← getEnv
  let mut errors : Array MessageData := #[]
  let taggedDecls : Array (Name × RepDepth) :=
    env.constants.fold (init := #[]) fun acc declName _ =>
      match repDepth? env declName with
      | some depth => acc.push (declName, depth)
      | none => acc
  let capstones : Array Name :=
    env.constants.fold (init := #[]) fun acc declName _ =>
      if capstoneAttr.hasTag env declName then
        acc.push declName
      else
        acc

  for declName in capstones do
    match env.find? declName with
    | some info =>
        unless isTheoremInfo info do
          errors := errors.push m!"INVALID CAPSTONE: {declName} is tagged `@[capstone]` but is not a theorem."
        unless (repDepth? env declName).isSome do
          errors := errors.push m!"INVALID CAPSTONE: {declName} is tagged `@[capstone]` but has no `@[rep_depth ...]`."
    | none =>
        errors := errors.push m!"INVALID CAPSTONE: {declName} is tagged `@[capstone]` but missing from the environment."

  for (declName, depth) in taggedDecls do
    let allowComposite := capstoneAttr.hasTag env declName
    errors := errors ++ taggedDependencyViolations env declName depth allowComposite

  if errors.isEmpty then
    logInfo m!"Architecture Audit PASS: {taggedDecls.size} tagged declarations obey the stable depth grammar."
  else
    for err in errors do
      logError err
    throwError "Architecture Audit FAILED with {errors.size} violation(s)."

/-- Command entrypoint for the Lean-native architecture audit. -/
elab "#audit_architecture" : command => do
  Command.liftCoreM checkArchitectureTopology

end InfoGeometry.Meta
