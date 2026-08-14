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

/-- Stable short slug used in exported metadata. -/
def RepDepth.slug : RepDepth → String
  | .count => "count"
  | .projective => "projective"
  | .operator => "operator"
  | .krein => "krein"
  | .transport => "transport"
  | .thermo => "thermo"

/--
Canonical L0-L5 layer label.

These labels give the existing `@[rep_depth ...]` tags a stable
machine-readable ontology for Arango and agent retrieval without changing the
existing attribute grammar used across the repo.
-/
def RepDepth.layerLabel : RepDepth → String
  | .count => "L0_Count"
  | .projective => "L1_Projective"
  | .operator => "L2_Operator"
  | .krein => "L3_Krein"
  | .transport => "L4_ModularTransport"
  | .thermo => "L5_ThermodynamicClosure"

/-- Human description of the representation layer. -/
def RepDepth.layerDescription : RepDepth → String
  | .count => "counting/combinatorial substrate"
  | .projective => "projection/support/compression substrate"
  | .operator => "operator-algebraic bridge substrate"
  | .krein => "Krein/doubled-geometry substrate"
  | .transport => "modular/transport/flow substrate"
  | .thermo => "thermodynamic/free-energy/closure substrate"

/-- Exportable metadata strings attached to DAG declaration rows. -/
def RepDepth.exportTags (depth : RepDepth) : Array String :=
  #[ s!"rep_depth:{depth.slug}"
   , s!"rep_depth_nat:{depth.toNat}"
   , s!"rep_layer:{depth.layerLabel}"
   , s!"rep_layer_description:{depth.layerDescription}" ]

/-! ### Typed semantic-edge metadata

These tags classify the *meaning of a declaration-level bridge* for graph
projection.  They do not assert that a dependency edge is a theorem: Lean
source and the kernel remain the authority for that.  The exporter merely
preserves the author-supplied ontology alongside the declaration node.
-/

inductive EdgeKind where
  | theorem
  | equivalence
  | representation
  | analogy
  | conjecturalBridge
  deriving DecidableEq, Repr, Inhabited

def EdgeKind.slug : EdgeKind → String
  | .theorem => "theorem"
  | .equivalence => "equivalence"
  | .representation => "representation"
  | .analogy => "analogy"
  | .conjecturalBridge => "conjectural_bridge"

def parseEdgeKind? (n : Name) : Option EdgeKind :=
  if n.toString == "proof" then some .theorem else match n.eraseMacroScopes with
  | `theorem => some .theorem
  | `proof => some .theorem
  | `equivalence => some .equivalence
  | `representation => some .representation
  | `analogy => some .analogy
  | `conjectural_bridge => some .conjecturalBridge
  | _ => none

syntax (name := edge_kind) "edge_kind " ident : attr

initialize edgeKindAttr : ParametricAttribute EdgeKind ←
  registerParametricAttribute {
    name := `edge_kind
    descr := "Classify the semantic role of a declaration-level graph bridge."
    getParam := fun _ stx => do
      match stx with
      | `(attr| edge_kind $id:ident) =>
          let raw := id.getId
          match parseEdgeKind? raw with
          | some k => pure k
          | none =>
              throwError "invalid `edge_kind` value `{raw}`; expected theorem, equivalence, representation, analogy, or conjectural_bridge"
      | _ => throwUnsupportedSyntax
    }

def edgeKind? (env : Environment) (declName : Name) : Option EdgeKind :=
  edgeKindAttr.getParam? env declName

def edgeKindTagStringsOf (env : Environment) (declName : Name) : Array String :=
  match edgeKind? env declName with
  | some kind => #[s!"edge_kind:{kind.slug}"]
  | none => #[]

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

/-- Collect representation-depth tags attached to a declaration as strings. -/
def repDepthTagStringsOf (env : Environment) (declName : Name) : Array String :=
  match repDepth? env declName with
  | some depth => depth.exportTags
  | none => #[]

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

/-- Direct dependency adjacency for all constants in an environment. -/
def directDependencyMap (env : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let mut out : Std.HashMap Name (Array Name) := {}
  for (declName, info) in env.constants do
    let mut deps : Array Name := #[]
    for (dep, _) in DAG.edgesFromConstantInfo info do
      deps := deps.push dep
    out := out.insert declName deps
  return out

/-- Nearest tagged constants reachable from a declaration through untagged nodes. -/
def nearestTaggedDescendants (env : Environment) (root : Name) : NameSet := Id.run do
  let mut nearest : NameSet := {}
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[]
  if let some info := env.find? root then
    for (dep, _) in DAG.edgesFromConstantInfo info do
      queue := queue.push dep
  let mut i := 0
  while i < queue.size do
    let curr := queue[i]!
    i := i + 1
    if visited.contains curr then continue
    visited := visited.insert curr
    if (repDepth? env curr).isSome then
      nearest := nearest.insert curr
    else
      if let some info := env.find? curr then
        for (dep, _) in DAG.edgesFromConstantInfo info do
          queue := queue.push dep
  return nearest

/--
Nearest tagged constants reachable from a declaration through untagged nodes,
using a precomputed direct-dependency map.

This is semantically the same traversal as `nearestTaggedDescendants`; it keeps
the full dependency universe intact and only avoids recomputing direct edges for
every audited root.
-/
def nearestTaggedDescendantsFromDeps
    (env : Environment) (directDeps : Std.HashMap Name (Array Name)) (root : Name) : NameSet := Id.run do
  let mut nearest : NameSet := {}
  let mut visited : NameSet := {}
  let mut queue : Array Name := directDeps.getD root #[]
  let mut i := 0
  while i < queue.size do
    let curr := queue[i]!
    i := i + 1
    if visited.contains curr then continue
    visited := visited.insert curr
    if (repDepth? env curr).isSome then
      nearest := nearest.insert curr
    else
      for dep in directDeps.getD curr #[] do
        queue := queue.push dep
  return nearest

/--
Memoized exact version of `nearestTaggedDescendantsFromDeps`.

For an untagged node, the nearest tagged descendants are the union of directly
tagged dependencies and the nearest tagged descendants of directly untagged
dependencies.  This computes the same relation as the breadth-first traversal,
but shares results across audited roots instead of repeatedly walking the same
subgraph.
-/
def nearestTaggedDescendantsMemo
    (env : Environment)
    (directDeps : Std.HashMap Name (Array Name))
    (cacheRef : IO.Ref (Std.HashMap Name NameSet))
    (root : Name)
    (_visiting : NameSet := {}) : CoreM NameSet := do
  let cache ← cacheRef.get
  match cache.get? root with
  | some cached => pure cached
  | none =>
      let nearest := nearestTaggedDescendantsFromDeps env directDeps root
      cacheRef.modify fun cache => cache.insert root nearest
      pure nearest

/-- Architecture violations detected from direct and transitive tagged dependencies. -/
def taggedDependencyViolations
    (env : Environment) (declName : Name) (depth : RepDepth) (allowComposite : Bool) : Array MessageData := Id.run do
  let mut out := #[]
  let deps := nearestTaggedDescendants env declName
  for dep in deps do
    match env.find? dep with
    | some depInfo =>
        -- Architecture adjacency is enforced on proof/program surfaces, not on
        -- inductive/structure container declarations used as parameter contexts.
        if isDefOrTheoremInfo depInfo then
          if let some depDepth := repDepth? env dep then
            let d := depth.toNat
            let d' := depDepth.toNat
            if d' > d && !(d == 2 && d' == 3) then
              out := out.push m!"REGRESSION: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
            else if !allowComposite && d' + 1 < d then
              out := out.push m!"WORMHOLE: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
    | none =>
      pure ()
  out

/--
Architecture violations detected from nearest tagged dependencies, using a
precomputed direct-dependency map.
-/
def taggedDependencyViolationsFromDeps
    (env : Environment) (directDeps : Std.HashMap Name (Array Name))
    (declName : Name) (depth : RepDepth) (allowComposite : Bool) : Array MessageData := Id.run do
  let mut out := #[]
  let deps := nearestTaggedDescendantsFromDeps env directDeps declName
  for dep in deps do
    match env.find? dep with
    | some depInfo =>
        -- Architecture adjacency is enforced on proof/program surfaces, not on
        -- inductive/structure container declarations used as parameter contexts.
        if isDefOrTheoremInfo depInfo then
          if let some depDepth := repDepth? env dep then
            let d := depth.toNat
            let d' := depDepth.toNat
            if d' > d && !(d == 2 && d' == 3) then
              out := out.push m!"REGRESSION: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
            else if !allowComposite && d' + 1 < d then
              out := out.push m!"WORMHOLE: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
    | none =>
        pure ()
  out

/--
Architecture violations detected from memoized nearest tagged dependencies.
-/
def taggedDependencyViolationsFromDepsM
    (env : Environment) (directDeps : Std.HashMap Name (Array Name))
    (cacheRef : IO.Ref (Std.HashMap Name NameSet))
    (declName : Name) (depth : RepDepth) (allowComposite : Bool) : CoreM (Array MessageData) := do
  let mut out := #[]
  let deps ← nearestTaggedDescendantsMemo env directDeps cacheRef declName
  for dep in deps do
    match env.find? dep with
    | some depInfo =>
        -- Architecture adjacency is enforced on proof/program surfaces, not on
        -- inductive/structure container declarations used as parameter contexts.
        if isDefOrTheoremInfo depInfo then
          if let some depDepth := repDepth? env dep then
            let d := depth.toNat
            let d' := depDepth.toNat
            if d' > d && !(d == 2 && d' == 3) then
              out := out.push m!"REGRESSION: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
            else if !allowComposite && d' + 1 < d then
              out := out.push m!"WORMHOLE: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
    | none =>
        pure ()
  pure out

/-- Lean-native architecture audit for the tagged stable spine. -/
def checkArchitectureTopology : CoreM Unit := do
  let env ← getEnv
  let mut errors : Array MessageData := #[]
  -- Strict architecture adjacency is enforced on the canonical spine only.
  -- Other namespaces may carry exploratory tags without gating canonical admission.
  let isCanonicalSpine (declName : Name) : Bool :=
    (toString declName).startsWith "InfoGeometry.Canonical."
  let taggedDecls : Array (Name × RepDepth) :=
    env.constants.toList.foldl (init := #[]) fun acc (declName, _) =>
      if !isCanonicalSpine declName then
        acc
      else
        match repDepth? env declName with
        | some depth => acc.push (declName, depth)
        | none => acc
  let capstones : Array Name :=
    env.constants.toList.foldl (init := #[]) fun acc (declName, _) =>
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

  let directDeps := directDependencyMap env
  let nearestCache ← IO.mkRef ({} : Std.HashMap Name NameSet)
  for (declName, depth) in taggedDecls do
    let allowComposite := capstoneAttr.hasTag env declName
    let newErrors ←
      taggedDependencyViolationsFromDepsM env directDeps nearestCache declName depth allowComposite
    errors := errors ++ newErrors

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
    env.constants.toList.foldl (init := (0, 0, (#[] : Array Name))) fun (total, covered, missing) (declName, info) =>
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
