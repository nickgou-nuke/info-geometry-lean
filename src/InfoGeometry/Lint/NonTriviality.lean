/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
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
  ([`InfoGeometry, `DAG, `Omega, `Experimental, `VirasoroProject, `proofs,
    `Agent, `Socratic, `Docs, `OAI, `SelfReference, `PrimitiveSetsAboveX, `scripts],
    32, true, [``propext, ``Quot.sound, ``Classical.choice], false)

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
  containsSorry : Bool
deriving Inhabited, Repr

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

private def dedupAppendNames (xs ys : List Name) : List Name :=
  if ys.isEmpty then xs
  else if xs.isEmpty then ys
  else
    Id.run do
      let mut seen : Std.HashSet Name := {}
      let mut out : Array Name := #[]
      for x in xs do
        if !seen.contains x then
          seen := seen.insert x
          out := out.push x
      for y in ys do
        if !seen.contains y then
          seen := seen.insert y
          out := out.push y
      return out.toList

def merge (a b : AuditResult) : AuditResult :=
  mk
    (termNodeCount := termNodeCount a + termNodeCount b)
    (hasNontrivialConst := hasNontrivialConst a || hasNontrivialConst b)
    (containsVacuousSockets := containsVacuousSockets a || containsVacuousSockets b)
    (unfoldedLocalConsts := dedupAppendNames (unfoldedLocalConsts a) (unfoldedLocalConsts b))
    (suspiciousConsts := dedupAppendNames (suspiciousConsts a) (suspiciousConsts b))
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

private def declarationModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some midx => env.header.moduleNames[midx.toNat]?.getD env.mainModule
  | none => env.mainModule

private def isProjectLocal (cfg : AuditConfig) (env : Environment) (declName : Name) : Bool :=
  (AuditConfig.projectRoots cfg).any (fun root =>
    root.isPrefixOf declName || root.isPrefixOf (declarationModule env declName))

private def isNontrivialExternalConst
    (cfg : AuditConfig) (env : Environment) (declName : Name) : Bool :=
  if isBuiltinTrivialConst declName ||
     isTrivialProjectionOrAccessor declName ||
     isProjectLocal cfg env declName ||
     !(`Mathlib).isPrefixOf (declarationModule env declName) then
    false
  else
    match env.find? declName with
    | some info => isProofConst info
    | none => false

private partial def auditDeclBodyMemo
    (cfg : AuditConfig)
    (env : Environment)
    (declMemoRef : IO.Ref (Std.HashMap Name (AuditResult × Nat)))
    (seenSet : NameSet)
    (depth : Nat)
    (rootExpr : Expr) : MetaM (AuditResult × Nat × NameSet) := do
  let mut visitedExprs : Std.HashSet Lean.ExprStructEq := {}
  let mut stack : Array Expr := #[rootExpr]
  let mut termCount : Nat := 0
  let mut hasNontrivial : Bool := false
  let mut hasVacuous : Bool := false
  let mut hitLimit : Bool := false
  let mut hasSorry : Bool := false
  let mut unfoldedArr : Array Name := #[]
  let mut unfoldedSet : Std.HashSet Name := {}
  let mut suspiciousArr : Array Name := #[]
  let mut suspiciousSet : Std.HashSet Name := {}
  let mut maxSubLevels : Nat := 0
  let mut ancestorsHit : NameSet := {}

  while !stack.isEmpty do
    let curr := stack.back!
    stack := stack.pop
    let isCompound :=
      match curr with
      | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. | .mdata .. => true
      | _ => false
    if isCompound then
      let key : Lean.ExprStructEq := ⟨curr⟩
      if visitedExprs.contains key then
        continue
      visitedExprs := visitedExprs.insert key

    if (curr.getSorry?).isSome then
      termCount := termCount + 1
      hasSorry := true
      if !suspiciousSet.contains ``sorryAx then
        suspiciousSet := suspiciousSet.insert ``sorryAx
        suspiciousArr := suspiciousArr.push ``sorryAx
      continue

    match curr with
    | Expr.app fn arg =>
        termCount := termCount + 1
        stack := stack.push arg
        stack := stack.push fn
    | Expr.lam _ _ body _ =>
        termCount := termCount + 1
        stack := stack.push body
    | Expr.forallE _ _ body _ =>
        termCount := termCount + 1
        stack := stack.push body
    | Expr.letE _ _ value body _ =>
        termCount := termCount + 1
        stack := stack.push body
        stack := stack.push value
    | Expr.proj s idx struct =>
        termCount := termCount + 1
        if isProjectLocal cfg env s then
          if isTrivialProjectionOrAccessor s then
            hasVacuous := true
            if !suspiciousSet.contains s then
              suspiciousSet := suspiciousSet.insert s
              suspiciousArr := suspiciousArr.push s
          if let some sinfo := Lean.getStructureInfo? env s then
            if let some projFn := sinfo.getProjFn? idx then
              if isTrivialProjectionOrAccessor projFn then
                hasVacuous := true
                if !suspiciousSet.contains projFn then
                  suspiciousSet := suspiciousSet.insert projFn
                  suspiciousArr := suspiciousArr.push projFn
        stack := stack.push struct
    | Expr.mdata _ body =>
        stack := stack.push body
    | Expr.const declName _ =>
        if isBuiltinTrivialConst declName then
          termCount := termCount + 1
        else if isTrivialProjectionOrAccessor declName then
          termCount := termCount + 1
          hasVacuous := true
          if !suspiciousSet.contains declName then
            suspiciousSet := suspiciousSet.insert declName
            suspiciousArr := suspiciousArr.push declName
        else
          match env.find? declName with
          | none =>
              termCount := termCount + 1
          | some info =>
              if isProjectLocal cfg env declName then
                if seenSet.contains declName then
                  termCount := termCount + 1
                  hasVacuous := true
                  ancestorsHit := ancestorsHit.insert declName
                  if !suspiciousSet.contains declName then
                    suspiciousSet := suspiciousSet.insert declName
                    suspiciousArr := suspiciousArr.push declName
                else if depth == 0 then
                  termCount := termCount + 1
                  hasVacuous := true
                  hitLimit := true
                  if !suspiciousSet.contains declName then
                    suspiciousSet := suspiciousSet.insert declName
                    suspiciousArr := suspiciousArr.push declName
                else
                  let cached? := (← declMemoRef.get)[declName]?
                  let usedCache ←
                    match cached? with
                    | some (cachedRes, reqLevels) => do
                        if reqLevels ≤ depth - 1 then
                          termCount := termCount + 1 + AuditResult.termNodeCount cachedRes
                          if AuditResult.hasNontrivialConst cachedRes then
                            hasNontrivial := true
                          if AuditResult.containsVacuousSockets cachedRes then
                            hasVacuous := true
                          if AuditResult.containsSorry cachedRes then
                            hasSorry := true
                          if !unfoldedSet.contains declName then
                            unfoldedSet := unfoldedSet.insert declName
                            unfoldedArr := unfoldedArr.push declName
                          for uc in AuditResult.unfoldedLocalConsts cachedRes do
                            if !unfoldedSet.contains uc then
                              unfoldedSet := unfoldedSet.insert uc
                              unfoldedArr := unfoldedArr.push uc
                          for sc in AuditResult.suspiciousConsts cachedRes do
                            if !suspiciousSet.contains sc then
                              suspiciousSet := suspiciousSet.insert sc
                              suspiciousArr := suspiciousArr.push sc
                          maxSubLevels := Nat.max maxSubLevels (1 + reqLevels)
                          pure true
                        else
                          pure false
                    | none => pure false
                  if !usedCache then
                    match info.value? (allowOpaque := true) with
                    | some val =>
                        let (subRes, subLevels, subAnc) ←
                          auditDeclBodyMemo cfg env declMemoRef (seenSet.insert declName) (depth - 1) val
                        termCount := termCount + 1 + AuditResult.termNodeCount subRes
                        if AuditResult.hasNontrivialConst subRes then
                          hasNontrivial := true
                        if AuditResult.containsVacuousSockets subRes then
                          hasVacuous := true
                        if AuditResult.hitUnfoldLimit subRes then
                          hitLimit := true
                        if AuditResult.containsSorry subRes then
                          hasSorry := true
                        if !unfoldedSet.contains declName then
                          unfoldedSet := unfoldedSet.insert declName
                          unfoldedArr := unfoldedArr.push declName
                        for uc in AuditResult.unfoldedLocalConsts subRes do
                          if !unfoldedSet.contains uc then
                            unfoldedSet := unfoldedSet.insert uc
                            unfoldedArr := unfoldedArr.push uc
                        for sc in AuditResult.suspiciousConsts subRes do
                          if !suspiciousSet.contains sc then
                            suspiciousSet := suspiciousSet.insert sc
                            suspiciousArr := suspiciousArr.push sc
                        let cleanedAnc := subAnc.erase declName
                        ancestorsHit := ancestorsHit.union cleanedAnc
                        maxSubLevels := Nat.max maxSubLevels (1 + subLevels)
                        if cleanedAnc.isEmpty && !AuditResult.hitUnfoldLimit subRes then
                          declMemoRef.modify fun m => m.insert declName (subRes, subLevels)
                    | none =>
                        termCount := termCount + 1
                        if isProofConst info && AuditConfig.rejectLocalAxioms cfg then
                          hasVacuous := true
                          if !suspiciousSet.contains declName then
                            suspiciousSet := suspiciousSet.insert declName
                            suspiciousArr := suspiciousArr.push declName
                        else if isProofConst info then
                          hasNontrivial := true
              else
                termCount := termCount + 1
                if isNontrivialExternalConst cfg env declName then
                  hasNontrivial := true
    | Expr.bvar _ => termCount := termCount + 1
    | Expr.fvar _ => termCount := termCount + 1
    | Expr.mvar _ =>
        termCount := termCount + 1
        hasVacuous := true
    | Expr.sort _ => termCount := termCount + 1
    | Expr.lit _ => termCount := termCount + 1

  let res := AuditResult.mk
    (termNodeCount := termCount)
    (hasNontrivialConst := hasNontrivial)
    (containsVacuousSockets := hasVacuous)
    (unfoldedLocalConsts := unfoldedArr.toList)
    (suspiciousConsts := suspiciousArr.toList)
    (hitUnfoldLimit := hitLimit)
    (containsSorry := hasSorry)
  return (res, maxSubLevels, ancestorsHit)

def auditExprTrivialityDetailed
    (cfg : AuditConfig)
    (env : Environment)
    (seen : List Name)
    (depth : Nat)
    (e : Expr) : MetaM AuditResult := do
  let queryEnv := env.setExporting false
  let declMemoRef ← IO.mkRef ({} : Std.HashMap Name (AuditResult × Nat))
  let mut seenSet : NameSet := {}
  for n in seen do
    seenSet := seenSet.insert n
  let (res, _, _) ← auditDeclBodyMemo cfg queryEnv declMemoRef seenSet depth e
  return res

/-- Legacy compatibility wrapper used by `InfoGeometry.Lint.Pauli`. -/
def auditExprTriviality (e : Expr) : MetaM Bool := do
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

private def collectProjFnsFromExpr (queryEnv : Environment) (e : Expr)
    (seen : Std.HashSet Name) (out : Array Name) : Std.HashSet Name × Array Name := Id.run do
  let base := e.getUsedConstants
  if !base.any (fun c => (Lean.getStructureInfo? queryEnv c).isSome) then
    return (seen, out)
  let mut visited : Std.HashSet Lean.ExprStructEq := {}
  let mut stack : Array Expr := #[e]
  let mut seenNames := seen
  let mut outNames := out
  while !stack.isEmpty do
    let curr := stack.back!
    stack := stack.pop
    match curr with
    | .const .. | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. =>
        continue
    | _ => pure ()
    let key : Lean.ExprStructEq := ⟨curr⟩
    if visited.contains key then continue
    visited := visited.insert key
    match curr with
    | .proj s idx struct =>
        if let some sinfo := Lean.getStructureInfo? queryEnv s then
          if let some projFn := sinfo.getProjFn? idx then
            if !seenNames.contains projFn then
              seenNames := seenNames.insert projFn
              outNames := outNames.push projFn
        stack := stack.push struct
    | .app fn arg =>
        stack := stack.push arg
        stack := stack.push fn
    | .lam _ ty body _ =>
        stack := stack.push body
        stack := stack.push ty
    | .forallE _ ty body _ =>
        stack := stack.push body
        stack := stack.push ty
    | .letE _ ty val body _ =>
        stack := stack.push body
        stack := stack.push val
        stack := stack.push ty
    | .mdata _ body =>
        stack := stack.push body
    | _ => pure ()
  return (seenNames, outNames)

private def directDepsArrayOfConstantInfo
    (queryEnv : Environment) (declName : Name) (ci : ConstantInfo) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Name := #[]
  for c in ci.type.getUsedConstants do
    if !seen.contains c then
      seen := seen.insert c
      out := out.push c
  let (seen', out') := collectProjFnsFromExpr queryEnv ci.type seen out
  seen := seen'
  out := out'
  if let some v := ci.value? (allowOpaque := true) then
    for c in v.getUsedConstants do
      if !seen.contains c then
        seen := seen.insert c
        out := out.push c
    let (seen'', out'') := collectProjFnsFromExpr queryEnv v seen out
    seen := seen''
    out := out''
  if let some implName := Lean.Compiler.getImplementedBy? queryEnv declName then
    if !seen.contains implName then
      seen := seen.insert implName
      out := out.push implName
  return out

/-- Product-backed bounded dependency scan result. -/
abbrev DependencyScanResult :=
  Std.HashSet Name × Bool

namespace DependencyScanResult

def deps : DependencyScanResult → Std.HashSet Name
  | (deps, _) => deps

def hitFuelLimit : DependencyScanResult → Bool
  | (_, hit) => hit

end DependencyScanResult

def collectTransitiveDeps
    (env : Environment) (fuel : Nat) (frontier : List Name) (seen : Std.HashSet Name)
    : CoreM DependencyScanResult := do
  let queryEnv := env.setExporting false
  let mut visited := seen
  let mut enqueued : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for n in frontier do
    if !visited.contains n && !enqueued.contains n then
      enqueued := enqueued.insert n
      queue := queue.push n
  let mut cursor := 0
  let mut remaining := fuel
  while cursor < queue.size && remaining > 0 do
    let n := queue[cursor]!
    cursor := cursor + 1
    if !visited.contains n then
      visited := visited.insert n
      remaining := remaining - 1
      if let some ci := queryEnv.find? n then
        for dep in directDepsArrayOfConstantInfo queryEnv n ci do
          if !visited.contains dep && !enqueued.contains dep then
            enqueued := enqueued.insert dep
            queue := queue.push dep
  return (visited, cursor < queue.size)

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
  let queryEnv := env.setExporting false
  let mut opaqueBoundaries : Array Name := #[]
  for dep in deps.toList do
    match queryEnv.find? dep with
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
  (declarationModule env name).toString

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
          let contamination ← liftCoreM <|
            auditTransitiveDependencies declName
              (nameSetOfList (AuditConfig.allowedAxioms cfg)) false
          if ContaminationResult.state contamination != "clean" then
            let msg := m!"[Pauli/AST-Vacuity] Transitive dependency audit requires review for `{declName}`: {ContaminationResult.state contamination}."
            if hardFail then throwErrorAt id msg else logWarning msg
            return
          let audit ←
            liftTermElabM do
              auditExprTrivialityDetailed cfg env [declName]
                (AuditConfig.maxLocalUnfoldDepth cfg) val
          let metric := AuditResult.toMetric audit
          if MathfulnessMetric.isGenuine metric then
            logInfo m!"Expression/dependency screening completed for `{declName}`; semantic nonvacuity still requires owner review. Metric: {repr metric}"
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
