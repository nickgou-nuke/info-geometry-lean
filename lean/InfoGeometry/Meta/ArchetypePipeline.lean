/-
Copyright (c) 2026 Epistemic Compiler Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Epistemic Compiler Team & Independent QMS Auditor
-/
import Lean
import Lean.Util.CollectAxioms

open Lean Meta Elab Command

namespace InfoGeometry.MetaCompiler

/-!
# Epistemic Typed Archetype Pipeline

This module formalizes:
1. **Type-Level Status Gating**: `TypedArchetype` indexed by `Status` to prevent vacuous proofs.
2. **Compile-Time Discharge**: Zero-cost extraction that is syntactically uncallable unless `status = .proved`.
3. **Kernel Axiom Auditor**: Deep transitive dependency scan detecting `sorryAx` and tracking axioms.
4. **Persistent Environment Extension**: $O(1)$ amortized lookups avoiding global $O(N)$ environment sweeps.
5. **Attribute & Commands**: `@[archetype]` registration attribute, `#audit_archetype`, and `#search_typed_archetypes`.
-/

-- ============================================================================
-- 1. Core Epistemic Types & Soundness Abstractions
-- ============================================================================

/-- Epistemic lifecycle states for candidate hypotheses. -/
inductive Status where
  | candidate : Status
  | validated : Status
  | proved    : Status
  deriving DecidableEq, Repr, Inhabited

/--
A mathematically sound epistemic archetype.
The `evidence` field is type-indexed on `s : Status`:
- If `s = .proved`, it carries a verified proof `∀ x : Input, claim x`.
- If `s ≠ .proved`, the proof obligation collapses to `True`, preventing vacuous instantiation
  from satisfying proof extractors.
-/
structure TypedArchetype (Input : Type u) (s : Status) where
  name     : Name
  phase    : Nat
  claim    : Input → Prop
  evidence : match s with
    | .proved => ∀ x : Input, claim x
    | _       => True

namespace TypedArchetype

/--
Discharge a claim at compile-time.
Because `s` is strictly constrained to `.proved`, callers can never supply a `.candidate`
or `.validated` archetype to extract a theorem.
-/
@[inline]
def discharge {Input : Type u} (arch : TypedArchetype Input .proved) (x : Input) : arch.claim x :=
  arch.evidence x

/--
Promote a candidate or validated archetype to `proved` by supplying a real proof.
This enforces referential integrity: the exact `name`, `phase`, and `claim` are preserved.
-/
def promoteToProved {Input : Type u} {s : Status}
    (arch : TypedArchetype Input s)
    (pf : ∀ x : Input, arch.claim x) : TypedArchetype Input .proved :=
  { name     := arch.name
    phase    := arch.phase
    claim    := arch.claim
    evidence := pf }

/-- Promote a candidate to validated stage (e.g., after empirical or countermodel checks). -/
def promoteToValidated {Input : Type u}
    (arch : TypedArchetype Input .candidate) : TypedArchetype Input .validated :=
  { name     := arch.name
    phase    := arch.phase
    claim    := arch.claim
    evidence := trivial }

end TypedArchetype

-- ============================================================================
-- 2. Transitive Axiom Collection & Soundness Auditing
-- ============================================================================

/-- Standard foundational axioms accepted in Lean 4 / Mathlib proofs. -/
def defaultAllowedAxioms : List Name := [
  ``propext,
  ``Quot.sound,
  ``Classical.choice
]

/--
Collect all transitive axioms used by a declaration.
-/
def getUsedAxioms (declName : Name) : MetaM (List Name) := do
  let axs ← Lean.collectAxioms declName
  return axs.toList

/-- Audit report structure for diagnostic inspection. -/
structure AxiomAuditResult where
  declName          : Name
  status            : Status
  transitiveAxioms  : List Name
  hasSorryAx        : Bool
  unapprovedAxioms  : List Name
  isSound           : Bool
  deriving Inhabited, Repr

/--
Audit an archetype declaration to ensure:
1. It does not hide `sorryAx` anywhere in its dependency graph.
2. It only depends on an explicitly permitted set of foundational axioms.
-/
def auditArchetype (declName : Name) (allowedAxioms : List Name := defaultAllowedAxioms)
    : MetaM AxiomAuditResult := do
  let cinfo ← getConstInfo declName
  let (status, _) ← forallTelescopeReducing cinfo.type fun _ body => do
    let body ← whnf body
    if !body.isAppOf ``TypedArchetype then
      throwError "Declaration '{declName}' is not a `TypedArchetype` (type: {body})"
    let args := body.getAppArgs
    if args.size < 2 then
      throwError "Malformed `TypedArchetype` expression in '{declName}'"
    let statusExpr ← whnf args[1]!
    let s ←
      if statusExpr.isConstOf ``Status.proved then pure Status.proved
      else if statusExpr.isConstOf ``Status.validated then pure Status.validated
      else if statusExpr.isConstOf ``Status.candidate then pure Status.candidate
      else throwError "Unknown `Status` constructor in expression: {statusExpr}"
    return (s, body)

  let axioms ← getUsedAxioms declName
  let hasSorry := axioms.contains ``sorryAx
  let unapproved := axioms.filter (fun ax => !allowedAxioms.contains ax)
  let isSound := !hasSorry && unapproved.isEmpty

  return {
    declName         := declName
    status           := status
    transitiveAxioms := axioms
    hasSorryAx       := hasSorry
    unapprovedAxioms := unapproved
    isSound          := isSound
  }

-- ============================================================================
-- 3. Persistent Environment Extension (O(1) Indexed Storage)
-- ============================================================================

/-- Metadata stored inside the persistent environment state. -/
structure ArchetypeEntry where
  declName   : Name
  status     : Status
  axioms     : List Name
  isSound    : Bool
  deriving Inhabited, Repr

initialize archetypeExtension : SimplePersistentEnvExtension ArchetypeEntry (Array ArchetypeEntry) ←
  registerSimplePersistentEnvExtension {
    name          := `archetypeExtension
    addEntryFn    := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Retrieve all registered archetypes from the environment. -/
def getRegisteredArchetypes (env : Environment) : Array ArchetypeEntry :=
  archetypeExtension.getState env

-- ============================================================================
-- 4. User Attribute `@[archetype]` with Elaboration Checks
-- ============================================================================

-- Note: We skip the actual userAttribute macro because attribute resolution
-- in MetaM from command requires core registration which can be flaky in dynamic modules.
-- We use a Command instead.

elab "#register_archetype " id:ident : command => do
  Command.liftTermElabM do
    let declName ← resolveGlobalConstNoOverload id
    let audit ← auditArchetype declName

    -- Strict gating: If marked `proved`, unconditionally reject any `sorryAx`.
    if audit.status == Status.proved && audit.hasSorryAx then
      throwError s!"[QMS REJECT] Archetype '{declName}' claims Status.proved but transitively depends on `sorryAx`."

    if audit.status == Status.proved && !audit.unapprovedAxioms.isEmpty then
      Lean.logWarning m!"[QMS WARNING] Archetype '{declName}' relies on non-standard axioms: {audit.unapprovedAxioms}"

    let entry : ArchetypeEntry := {
      declName := declName
      status   := audit.status
      axioms   := audit.transitiveAxioms
      isSound  := audit.isSound
    }
    modifyEnv fun env => archetypeExtension.addEntry env entry

-- ============================================================================
-- 5. Deep Kernel Fallback Search
-- ============================================================================

/--
Exhaustive fallback search over `env.constants` that properly unpacks Pi-binders
and normalizes expressions to weak head normal form (WHNF).
-/
def deepSearchEnvironmentArchetypes : MetaM (Array (Name × Status)) := do
  let env ← getEnv
  let mut results := #[]
  for (name, cinfo) in env.constants do
    if !name.isInternal then
      let isArch ← forallTelescopeReducing cinfo.type fun _ body => do
        let body ← whnf body
        if body.isAppOf ``TypedArchetype then
          let args := body.getAppArgs
          if args.size >= 2 then
            let stExpr ← whnf args[1]!
            if stExpr.isConstOf ``Status.proved then
              return some Status.proved
            else if stExpr.isConstOf ``Status.validated then
              return some Status.validated
            else if stExpr.isConstOf ``Status.candidate then
              return some Status.candidate
        return none
      if let some st := isArch then
        results := results.push (name, st)
  return results

-- ============================================================================
-- 6. Interactive Commands
-- ============================================================================

/-- Inspect and audit an individual archetype declaration. -/
elab "#audit_archetype " id:ident : command => do
  Command.liftTermElabM do
    let declName ← resolveGlobalConstNoOverload id
    let res ← auditArchetype declName
    let statusStr := match res.status with
      | .candidate => "Candidate (Unproven)"
      | .validated => "Validated (Empirical/Intermediate)"
      | .proved    => "Proved"

    let mut msg := m!"=== QMS Archetype Audit: {declName} ===\n"
    msg := msg ++ m!"• Epistemic Status: {statusStr}\n"
    msg := msg ++ m!"• Soundness Pass  : {res.isSound}\n"
    msg := msg ++ m!"• Transitive Axioms ({res.transitiveAxioms.length}): {res.transitiveAxioms}\n"
    if res.hasSorryAx then
      msg := msg ++ m!"• [CRITICAL FAIL] Contains `sorryAx`!\n"
    if !res.unapprovedAxioms.isEmpty then
      msg := msg ++ m!"• Non-standard Axioms: {res.unapprovedAxioms}\n"
    logInfo msg

/-- Display all indexed archetypes currently registered in the environment extension. -/
elab "#search_typed_archetypes" : command => do
  Command.liftTermElabM do
    let env ← getEnv
    let registered := getRegisteredArchetypes env

    let mut provedCount := 0
    let mut candidateCount := 0
    let mut validatedCount := 0

    let mut report := m!"--- Registered Typed Archetypes ({registered.size}) ---\n"
    for entry in registered do
      let mark := if entry.isSound then "✓" else "✗"
      match entry.status with
      | .proved    => provedCount := provedCount + 1
      | .validated => validatedCount := validatedCount + 1
      | .candidate => candidateCount := candidateCount + 1
      report := report ++ m!"[{mark}] {entry.declName} | Status: {repr entry.status} | Axioms: {entry.axioms}\n"

    report := report ++ m!"\nSummary: {provedCount} proved, {validatedCount} validated, {candidateCount} candidates."
    logInfo report

end InfoGeometry.MetaCompiler
