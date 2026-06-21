/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import Lean
import Lean.Meta.Basic
import Lean.Meta.Sorry
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Data.Json
import Std

open Lean Meta Elab Command

namespace InfoGeometry.Lint

/-!
# LeanTrail v1.2 Biopsy / Non-Triviality Gate

This module is a drop-in replacement for the old shallow `NonTriviality.lean`.
It keeps the legacy `auditExprTriviality : Expr → MetaM Bool` wrapper for
compatibility with `Pauli.lean`, and adds a v1.3 biopsy layer with Honest Sorry closure debt:

* bounded Expr-shape audit for fake transport / pure conductor detection;
* Prop-vs-Type guard for DefEq protection;
* transitive axiom audit using `Lean.collectAxioms`, with explicit `sorry` treated as honest closure debt when configured;
* transitive opaque-boundary scan over referenced constants;
* JSON command output for one-declaration biopsy inspection.

Source-body byte spans must still come from command syntax / InfoTree extraction,
not from `ConstantInfo.value`. This module reports source patchability as
`unsupported` unless supplied by a separate provenance extractor.
-/

/-- Product-backed audit configuration, avoiding a proof-carrier structure. -/
abbrev AuditConfig :=
  List Name × Nat × Bool × List Name × Bool

namespace AuditConfig

def default : AuditConfig :=
  ([`InfoGeometry], 32, true, [``propext, ``Quot.sound, ``Classical.choice], true)

def projectRoots : AuditConfig → List Name
  | (roots, _, _, _, _) => roots

def maxLocalUnfoldDepth : AuditConfig → Nat
  | (_, depth, _, _, _) => depth

def rejectLocalAxioms : AuditConfig → Bool
  | (_, _, reject, _, _) => reject

def allowedAxioms : AuditConfig → List Name
  | (_, _, _, allowed, _) => allowed

/-- Permit explicit `sorry` as honest, visible closure debt. -/
def allowSorry : AuditConfig → Bool
  | (_, _, _, _, allow) => allow

end AuditConfig

structure MathfulnessMetric where
  termNodeCount : Nat
  utilizesMathlibAxioms : Bool
  containsVacuousSockets : Bool
  unfoldedLocalWrapperCount : Nat
  hitUnfoldLimit : Bool
  containsSorry : Bool := false
deriving Repr

def MathfulnessMetric.isGenuine (m : MathfulnessMetric) : Bool :=
  (decide (m.termNodeCount > 5)) &&
    m.utilizesMathlibAxioms &&
    !m.containsVacuousSockets &&
    !m.hitUnfoldLimit &&
    !m.containsSorry

/-- Product-backed expression-audit result, avoiding a proof-carrier structure. -/
abbrev AuditResult :=
  Nat × Bool × Bool × List Name × List Name × Bool × Bool

namespace AuditResult

def mk
    (termNodeCount : Nat := 0)
    (hasNontrivialConst : Bool := false)
    (containsVacuousSockets : Bool := false)
    (unfoldedLocalConsts : List Name := [])
    (suspiciousConsts : List Name := [])
    (hitUnfoldLimit : Bool := false)
    (containsSorry : Bool := false) : AuditResult :=
  (termNodeCount, hasNontrivialConst, containsVacuousSockets, unfoldedLocalConsts,
    suspiciousConsts, hitUnfoldLimit, containsSorry)

def termNodeCount : AuditResult → Nat
  | (n, _, _, _, _, _, _) => n

def hasNontrivialConst : AuditResult → Bool
  | (_, b, _, _, _, _, _) => b

def containsVacuousSockets : AuditResult → Bool
  | (_, _, b, _, _, _, _) => b

def unfoldedLocalConsts : AuditResult → List Name
  | (_, _, _, xs, _, _, _) => xs

def suspiciousConsts : AuditResult → List Name
  | (_, _, _, _, xs, _, _) => xs

def hitUnfoldLimit : AuditResult → Bool
  | (_, _, _, _, _, b, _) => b

def containsSorry : AuditResult → Bool
  | (_, _, _, _, _, _, b) => b

def merge (a b : AuditResult) : AuditResult :=
  mk
    (termNodeCount := termNodeCount a + termNodeCount b)
    (hasNontrivialConst := hasNontrivialConst a || hasNontrivialConst b)
    (containsVacuousSockets := containsVacuousSockets a || containsVacuousSockets b)
    (unfoldedLocalConsts := unfoldedLocalConsts a ++ unfoldedLocalConsts b)
    (suspiciousConsts := suspiciousConsts a ++ suspiciousConsts b)
    (hitUnfoldLimit := hitUnfoldLimit a || hitUnfoldLimit b)
    (containsSorry := containsSorry a || containsSorry b)

def addNode (a : AuditResult) : AuditResult :=
  mk
    (termNodeCount := termNodeCount a + 1)
    (hasNontrivialConst := hasNontrivialConst a)
    (containsVacuousSockets := containsVacuousSockets a)
    (unfoldedLocalConsts := unfoldedLocalConsts a)
    (suspiciousConsts := suspiciousConsts a)
    (hitUnfoldLimit := hitUnfoldLimit a)
    (containsSorry := containsSorry a)

def markSuspicious (a : AuditResult) (declName : Name) : AuditResult :=
  mk
    (termNodeCount := termNodeCount a)
    (hasNontrivialConst := hasNontrivialConst a)
    (containsVacuousSockets := true)
    (unfoldedLocalConsts := unfoldedLocalConsts a)
    (suspiciousConsts := declName :: suspiciousConsts a)
    (hitUnfoldLimit := hitUnfoldLimit a)
    (containsSorry := containsSorry a)

def toMetric (a : AuditResult) : MathfulnessMetric :=
  { termNodeCount := termNodeCount a
    utilizesMathlibAxioms := hasNontrivialConst a
    containsVacuousSockets := containsVacuousSockets a
    unfoldedLocalWrapperCount := (unfoldedLocalConsts a).length
    hitUnfoldLimit := hitUnfoldLimit a
    containsSorry := containsSorry a }

end AuditResult

private def suspiciousExactComponents : List String :=
  [ "_sorry"
  , "_statement"
  , "_law"
  , "_cert"
  , "certificate"
  , "witness"
  , "socket"
  , "readback"
  , "proof"
  ]

private def suspiciousSubstrings : List String :=
  [ "kms_law"
  , "projective_kms_law"
  , "perfectReconstruction_law"
  , "perfect_reflection_below_gap_law"
  , "sorryProof"
  ]

private def isSuspiciousComponent (s : String) : Bool :=
  suspiciousExactComponents.any (fun t => s == t) ||
    suspiciousSubstrings.any (fun t => s.contains t)

private def isTrivialProjectionOrAccessor : Name → Bool
  | .anonymous => false
  | .str p s   => isSuspiciousComponent s || isTrivialProjectionOrAccessor p
  | .num p _   => isTrivialProjectionOrAccessor p

private def isBuiltinTrivialConst (declName : Name) : Bool :=
  declName == ``Eq.refl ||
  declName == ``Iff.rfl ||
  declName == ``True.intro ||
  declName == ``False.elim

private def isProofConst : ConstantInfo → Bool
  | ConstantInfo.thmInfo _ => true
  | ConstantInfo.axiomInfo _ => true
  | _ => false

private def isOpaqueConst : ConstantInfo → Bool
  | ConstantInfo.opaqueInfo _ => true
  | _ => false

private def isProjectLocal (cfg : AuditConfig) (declName : Name) : Bool :=
  (AuditConfig.projectRoots cfg).any (fun root => root.isPrefixOf declName)

private def isNontrivialExternalConst
    (cfg : AuditConfig) (env : Environment) (declName : Name) : Bool :=
  if isBuiltinTrivialConst declName ||
     isTrivialProjectionOrAccessor declName ||
     isProjectLocal cfg declName then
    false
  else
    match env.find? declName with
    | some info => isProofConst info
    | none => false

partial def auditExprTrivialityDetailed
    (cfg : AuditConfig)
    (env : Environment)
    (seen : List Name)
    (depth : Nat)
    (e : Expr) : MetaM AuditResult := do

  if (e.getSorry?).isSome then
    return AuditResult.mk
      (termNodeCount := 1)
      (containsSorry := true)
      (suspiciousConsts := [``sorryAx])

  match e.consumeMData with
  | Expr.app fn arg =>
      let fnAudit ← auditExprTrivialityDetailed cfg env seen depth fn
      let argAudit ← auditExprTrivialityDetailed cfg env seen depth arg
      return AuditResult.addNode (AuditResult.merge fnAudit argAudit)

  | Expr.lam _ _ body _ =>
      let bodyAudit ← auditExprTrivialityDetailed cfg env seen depth body
      return AuditResult.addNode bodyAudit

  | Expr.forallE _ _ body _ =>
      let bodyAudit ← auditExprTrivialityDetailed cfg env seen depth body
      return AuditResult.addNode bodyAudit

  | Expr.letE _ _ value body _ =>
      let valAudit ← auditExprTrivialityDetailed cfg env seen depth value
      let bodyAudit ← auditExprTrivialityDetailed cfg env seen depth body
      return AuditResult.addNode (AuditResult.merge valAudit bodyAudit)

  | Expr.proj _ _ struct =>
      let structAudit ← auditExprTrivialityDetailed cfg env seen depth struct
      return AuditResult.addNode structAudit

  | Expr.mdata _ body =>
      auditExprTrivialityDetailed cfg env seen depth body

  | Expr.const declName _ =>
      if isBuiltinTrivialConst declName then
        return AuditResult.mk (termNodeCount := 1)
      else if isTrivialProjectionOrAccessor declName then
        return AuditResult.markSuspicious (AuditResult.addNode AuditResult.mk) declName
      else
        match env.find? declName with
        | none => return AuditResult.mk (termNodeCount := 1)
        | some info =>
            if isProjectLocal cfg declName then
              if seen.contains declName then
                return AuditResult.mk
                  (termNodeCount := 1)
                  (containsVacuousSockets := true)
                  (suspiciousConsts := [declName])
              else if depth == 0 then
                return AuditResult.mk
                  (termNodeCount := 1)
                  (containsVacuousSockets := true)
                  (suspiciousConsts := [declName])
                  (hitUnfoldLimit := true)
              else
                match info.value? (allowOpaque := true) with
                | some val =>
                    let audit ← auditExprTrivialityDetailed cfg env (declName :: seen) (depth - 1) val
                    let auditNode := AuditResult.addNode audit
                    return AuditResult.mk
                      (termNodeCount := AuditResult.termNodeCount auditNode)
                      (hasNontrivialConst := AuditResult.hasNontrivialConst auditNode)
                      (containsVacuousSockets := AuditResult.containsVacuousSockets auditNode)
                      (unfoldedLocalConsts := declName :: AuditResult.unfoldedLocalConsts auditNode)
                      (suspiciousConsts := AuditResult.suspiciousConsts auditNode)
                      (hitUnfoldLimit := AuditResult.hitUnfoldLimit auditNode)
                      (containsSorry := AuditResult.containsSorry auditNode)
                | none =>
                    if isProofConst info && AuditConfig.rejectLocalAxioms cfg then
                      return AuditResult.mk
                        (termNodeCount := 1)
                        (containsVacuousSockets := true)
                        (suspiciousConsts := [declName])
                    else
                      return AuditResult.mk
                        (termNodeCount := 1)
                        (hasNontrivialConst := isProofConst info)
            else
              return AuditResult.mk
                (termNodeCount := 1)
                (hasNontrivialConst := isNontrivialExternalConst cfg env declName)

  | Expr.bvar _ => return AuditResult.mk (termNodeCount := 1)
  | Expr.fvar _ => return AuditResult.mk (termNodeCount := 1)
  | Expr.mvar _ =>
      return AuditResult.mk (termNodeCount := 1) (containsVacuousSockets := true)
  | Expr.sort _ => return AuditResult.mk (termNodeCount := 1)
  | Expr.lit _ => return AuditResult.mk (termNodeCount := 1)

/-- Legacy compatibility wrapper used by `InfoGeometry.Lint.Pauli`. -/
partial def auditExprTriviality (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let cfg := AuditConfig.default
  let audit ← auditExprTrivialityDetailed cfg env [] (AuditConfig.maxLocalUnfoldDepth cfg) e
  return MathfulnessMetric.isGenuine (AuditResult.toMetric audit)

private def namesJson (xs : List Name) : Json :=
  Json.arr (xs.toArray.map (fun n => Json.str n.toString))

private def arrNamesJson (xs : Array Name) : Json :=
  Json.arr (xs.map (fun n => Json.str n.toString))

private def nameSetOfList (xs : List Name) : Std.HashSet Name :=
  xs.foldl (fun acc n => acc.insert n) ({} : Std.HashSet Name)

private def constsInExpr (e : Expr) : Std.HashSet Name :=
  e.foldConsts (init := ({} : Std.HashSet Name)) fun n acc => acc.insert n

private def directDepsOfConstantInfo (ci : ConstantInfo) : Std.HashSet Name :=
  let typeDeps := constsInExpr ci.type
  match ci.value? (allowOpaque := true) with
  | none => typeDeps
  | some v =>
      let valDeps := constsInExpr v
      valDeps.fold (init := typeDeps) fun acc n => acc.insert n

/-- Product-backed bounded dependency scan result. -/
abbrev DependencyScanResult :=
  Std.HashSet Name × Bool

namespace DependencyScanResult

def deps : DependencyScanResult → Std.HashSet Name
  | (deps, _) => deps

def hitFuelLimit : DependencyScanResult → Bool
  | (_, hit) => hit

end DependencyScanResult

partial def collectTransitiveDeps
    (env : Environment) (fuel : Nat) (frontier : List Name) (seen : Std.HashSet Name)
    : CoreM DependencyScanResult := do
  match fuel, frontier with
  | 0, [] => pure (seen, false)
  | 0, _ => pure (seen, true)
  | _, [] => pure (seen, false)
  | fuel + 1, n :: rest =>
      if seen.contains n then
        collectTransitiveDeps env fuel rest seen
      else
        let seen := seen.insert n
        match env.find? n with
        | none => collectTransitiveDeps env fuel rest seen
        | some ci =>
            let deps := directDepsOfConstantInfo ci |>.toList
            collectTransitiveDeps env fuel (deps ++ rest) seen

/-- Product-backed dependency contamination result, avoiding a proof-carrier structure. -/
abbrev ContaminationResult :=
  String × Array Name × Array Name × Array Name × Bool × Array Name

namespace ContaminationResult

def mk
    (state : String)
    (violations : Array Name)
    (allAxioms : Array Name)
    (opaqueBoundaries : Array Name)
    (hitDependencyFuelLimit : Bool)
    (closureDebts : Array Name := #[]) : ContaminationResult :=
  (state, violations, allAxioms, opaqueBoundaries, hitDependencyFuelLimit, closureDebts)

def state : ContaminationResult → String
  | (state, _, _, _, _, _) => state

def violations : ContaminationResult → Array Name
  | (_, xs, _, _, _, _) => xs

def allAxioms : ContaminationResult → Array Name
  | (_, _, xs, _, _, _) => xs

def opaqueBoundaries : ContaminationResult → Array Name
  | (_, _, _, xs, _, _) => xs

def hitDependencyFuelLimit : ContaminationResult → Bool
  | (_, _, _, _, b, _) => b

def closureDebts : ContaminationResult → Array Name
  | (_, _, _, _, _, xs) => xs

end ContaminationResult

def auditTransitiveDependencies
    (declName : Name) (allowedAxioms : Std.HashSet Name) (allowSorry : Bool) : CoreM ContaminationResult := do
  let env ← getEnv
  let axioms ← Lean.collectAxioms declName
  let mut state := "clean"
  let mut violations : Array Name := #[]
  let mut allAxioms : Array Name := #[]
  let mut closureDebts : Array Name := #[]

  for ax in axioms.toList do
    allAxioms := allAxioms.push ax
    if ax == ``sorryAx then
      if allowSorry then
        if state == "clean" then
          state := "honest_sorry"
        closureDebts := closureDebts.push ax
      else
        state := "sorryAx"
        violations := violations.push ax
    else if !(allowedAxioms.contains ax) then
      if state != "sorryAx" then
        state := "forbidden_axiom"
      violations := violations.push ax

  -- `collectAxioms` intentionally reports axiom constants, not every opaque or
  -- no-value declaration. Run a bounded dependency DFS to catch opaque boundary
  -- laundering without normalizing or unfolding terms.
  let depScan ← collectTransitiveDeps env 200000 [declName] {}
  let deps := DependencyScanResult.deps depScan
  let hitDependencyFuelLimit := DependencyScanResult.hitFuelLimit depScan
  if hitDependencyFuelLimit && (state == "clean" || state == "honest_sorry") then
    state := "dependency_fuel_limit"
  let mut opaqueBoundaries : Array Name := #[]
  for dep in deps.toList do
    match env.find? dep with
    | some ci =>
        if isOpaqueConst ci then
          opaqueBoundaries := opaqueBoundaries.push dep
          if state == "clean" || state == "honest_sorry" then
            state := "opaque_boundary"
    | none => pure ()

  return ContaminationResult.mk
    state
    violations
    allAxioms
    opaqueBoundaries
    hitDependencyFuelLimit
    closureDebts

def checkDeclIsProp (declName : Name) : MetaM Bool := do
  let env ← getEnv
  match env.find? declName with
  | none => pure false
  | some ci => isProp ci.type

private def declKindString : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

private def moduleNameString (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some midx =>
      match env.header.moduleNames[midx.toNat]? with
      | some n => n.toString
      | none => "unknown"
  | none => env.mainModule.toString

private def classifyVacuityRole
    (isProp : Bool) (metric : MathfulnessMetric) (audit : AuditResult) (contamState : String) : String :=
  if contamState == "honest_sorry" then
    "closure_debt"
  else if contamState != "clean" then
    "contaminated"
  else if !isProp then
    if MathfulnessMetric.isGenuine metric then "gate" else "type_boundary"
  else if MathfulnessMetric.isGenuine metric then
    "gate"
  else if AuditResult.containsVacuousSockets audit || AuditResult.hitUnfoldLimit audit then
    "fake_transport"
  else
    "pure_conductor"

private def sourcePatchUnsupportedJson : Json :=
  Json.mkObj [
    ("state", "manual_refactor_required"),
    ("decl_span_kind", "unknown"),
    ("patch_span_kind", "unsupported"),
    ("source_info_kind", "synthetic/none"),
    ("reason_code", "source_provenance_extractor_required")
  ]

def biopsyDeclJson (cfg : AuditConfig) (declName : Name) : CommandElabM Json := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError m!"Declaration `{declName}` not found."
  let val? := ci.value? (allowOpaque := true)
  let audit ←
    match val? with
    | some val =>
        liftTermElabM do
          auditExprTrivialityDetailed cfg env [declName] (AuditConfig.maxLocalUnfoldDepth cfg) val
    | none => pure <| AuditResult.mk (termNodeCount := 1) (containsVacuousSockets := true)
  let metric := AuditResult.toMetric audit
  let isProp ← liftTermElabM do checkDeclIsProp declName
  let allowed := nameSetOfList (AuditConfig.allowedAxioms cfg)
  let contamination ←
    liftCoreM <| auditTransitiveDependencies declName allowed (AuditConfig.allowSorry cfg)
  let role := classifyVacuityRole isProp metric audit (ContaminationResult.state contamination)
  let moduleName := moduleNameString env declName

  return Json.mkObj [
    ("target", declName.toString),
    ("name", declName.toString),
    ("module", moduleName),
    ("decl_kind", declKindString ci),
    ("attrs", Json.mkObj [
      ("vacuity", Json.mkObj [
        ("role", role),
        ("is_prop", Json.bool isProp),
        ("term_node_count", metric.termNodeCount),
        ("uses_external_gate", Json.bool metric.utilizesMathlibAxioms),
        ("contains_vacuous_sockets", Json.bool metric.containsVacuousSockets),
        ("unfolded_local_wrapper_count", metric.unfoldedLocalWrapperCount),
        ("hit_unfold_limit", Json.bool metric.hitUnfoldLimit),
        ("contains_sorry", Json.bool metric.containsSorry),
        ("unfolded_local_consts", namesJson (AuditResult.unfoldedLocalConsts audit)),
        ("suspicious_consts", namesJson (AuditResult.suspiciousConsts audit))
      ]),
      ("contamination", Json.mkObj [
        ("state", ContaminationResult.state contamination),
        ("violations", arrNamesJson (ContaminationResult.violations contamination)),
        ("all_axioms", arrNamesJson (ContaminationResult.allAxioms contamination)),
        ("opaque_boundaries", arrNamesJson (ContaminationResult.opaqueBoundaries contamination)),
        ("closure_debts", arrNamesJson (ContaminationResult.closureDebts contamination)),
        ("hit_dependency_fuel_limit",
          Json.bool (ContaminationResult.hitDependencyFuelLimit contamination))
      ]),
      ("source_patch", sourcePatchUnsupportedJson),
      ("surgery", Json.mkObj [
        ("state", if role == "contaminated" then "quarantine" else if role == "closure_debt" then "closure_obligation" else if isProp then "proposed" else "manual_refactor_required"),
        ("reason", if role == "closure_debt" then "honest_sorry_permitted" else if !isProp then "def_eq_protection_required" else "")
      ])
    ])
  ]

private def runNonTrivialityGate (cfg : AuditConfig) (hardFail : Bool) (id : Syntax) : CommandElabM Unit := do
  let declName ← resolveGlobalConstNoOverload id
  let env ← getEnv
  match env.find? declName with
  | none => throwErrorAt id m!"Audit failure: declaration `{declName}` not found."
  | some decl =>
      match decl.value? (allowOpaque := true) with
      | none => throwErrorAt id m!"[Pauli/AST-Vacuity] Declaration `{declName}` has no auditable value."
      | some val =>
          let audit ←
            liftTermElabM do
              auditExprTrivialityDetailed cfg env [declName]
                (AuditConfig.maxLocalUnfoldDepth cfg) val
          let metric := AuditResult.toMetric audit
          if MathfulnessMetric.isGenuine metric then
            logInfo m!"Audit complete: `{declName}` passed non-triviality scan. Metric: {repr metric}"
          else
            let msg := m!"[Pauli/AST-Vacuity] Declaration `{declName}` failed non-triviality scan. Metric: {repr metric}. Suspicious constants: {repr (AuditResult.suspiciousConsts audit)}. Unfolded local constants: {repr (AuditResult.unfoldedLocalConsts audit)}"
            if hardFail then throwErrorAt id msg else logWarning msg

elab "#audit_non_triviality " id:ident : command => do
  runNonTrivialityGate AuditConfig.default false id

elab "#enforce_non_triviality " id:ident : command => do
  runNonTrivialityGate AuditConfig.default true id

elab "#biopsy_non_triviality " id:ident : command => do
  let declName ← resolveGlobalConstNoOverload id
  let j ← biopsyDeclJson AuditConfig.default declName
  logInfo m!"{j.compress}"

end InfoGeometry.Lint
