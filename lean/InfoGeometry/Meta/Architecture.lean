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

/-- True iff the constant info describes a theorem or a definition. -/
def isDefOrTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | .defnInfo _ => true
  | _ => false

/-- Final dotted component of a declaration name. -/
def declNameLeaf (declName : Name) : String :=
  match (toString declName).splitOn "." |>.reverse with
  | leaf :: _ => leaf
  | [] => toString declName

/-- Heuristic generated/infrastructure leaf names to exclude from coverage auditing. -/
def isGeneratedLeafName (leaf : String) : Bool :=
  leaf.startsWith "inst" ||
    leaf.startsWith "_proof_" ||
    leaf.startsWith "_match_" ||
    leaf.startsWith "proof_" ||
    leaf.startsWith "match_" ||
    leaf.startsWith "eq_" ||
    leaf == "mk" ||
    leaf == "rec" ||
    leaf == "recOn" ||
    leaf == "casesOn" ||
    leaf == "noConfusion" ||
    leaf == "noConfusionType" ||
    leaf == "brecOn" ||
    leaf == "below" ||
    leaf == "ibelow" ||
    leaf == "sizeOf_spec" ||
    leaf == "injEq" ||
    leaf == "inj" ||
    leaf == "ctorIdx"

/-- Name-fragment markers for generated/auxiliary declarations. -/
def hasGeneratedNameFragment (s : String) : Bool :=
  s.contains "._private." ||
    s.contains ".proof_" ||
    s.contains "._proof_" ||
    s.contains ".match_" ||
    s.contains "._match_" ||
    s.contains ".equations._eqn_" ||
    s.contains ".sizeOf_spec" ||
    s.contains ".congr_simp" ||
    s.contains ".ctorElim" ||
    s.contains ".ctorElimType" ||
    s.contains ".toCtorIdx" ||
    s.contains ".ofNat" ||
    s.contains ".ofNat_ctorIdx" ||
    s.contains ".repr" ||
    s.contains ".elim"

/--
True iff a declaration should be covered by the strict rep-depth coverage audit.

Scope:
- canonical namespace only;
- public def/theorem surfaces;
- excludes generated/private internals and instance scaffolding.
-/
def isRepDepthCoverageTarget (env : Environment) (declName : Name) (info : ConstantInfo) : Bool :=
  let s := toString declName
  let leaf := declNameLeaf declName
  isDefOrTheoremInfo info &&
    s.startsWith "InfoGeometry.Canonical." &&
    !declName.isInternal &&
    !declName.hasMacroScopes &&
    !hasGeneratedNameFragment s &&
    !isGeneratedLeafName leaf &&
    !(env.isProjectionFn declName) &&
    !(env.isConstructor declName)

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
  -- Strict architecture adjacency is enforced on the canonical spine only.
  -- Other namespaces may carry exploratory tags without gating canonical admission.
  let isCanonicalSpine (declName : Name) : Bool :=
    (toString declName).startsWith "InfoGeometry.Canonical."
  let taggedDecls : Array (Name × RepDepth) :=
    env.constants.fold (init := #[]) fun acc declName _ =>
      if !isCanonicalSpine declName then
        acc
      else
        match repDepth? env declName with
        | some depth => acc.push (declName, depth)
        | none => acc
  let capstones : Array Name :=
    env.constants.fold (init := #[]) fun acc declName _ =>
      if isCanonicalSpine declName && capstoneAttr.hasTag env declName then
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

/--
Strict rep-depth coverage audit for canonical declaration owners.

This check complements `#audit_architecture`: it reports missing `@[rep_depth ...]`
on canonical public theorem/definition declarations instead of only checking
adjacency among already-tagged declarations.
-/
def checkRepDepthCoverage : CoreM Unit := do
  let env ← getEnv
  let (total, covered, missing) :=
    env.constants.fold (init := (0, 0, (#[] : Array Name))) fun (total, covered, missing) declName info =>
      if isRepDepthCoverageTarget env declName info then
        match repDepth? env declName with
        | some _ => (total + 1, covered + 1, missing)
        | none => (total + 1, covered, missing.push declName)
      else
        (total, covered, missing)
  if missing.isEmpty then
    logInfo m!"Rep-Depth Coverage PASS: {covered}/{total} canonical def/theorem declarations are tagged."
  else
    for declName in missing do
      logError m!"MISSING REP-DEPTH: {declName}"
    throwError
      "Rep-Depth Coverage FAILED: {missing.size} missing tag(s) out of {total} canonical def/theorem declaration(s)."

/-- Command entrypoint for the Lean-native architecture audit. -/
elab "#audit_architecture" : command => do
  Command.liftCoreM checkArchitectureTopology

/-- Command entrypoint for strict canonical rep-depth coverage auditing. -/
elab "#audit_rep_depth_coverage" : command => do
  Command.liftCoreM checkRepDepthCoverage

end InfoGeometry.Meta
