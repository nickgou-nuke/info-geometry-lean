/-
Copyright (c) 2026 Epistemic Compiler Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Epistemic Compiler Team & Independent QMS Auditor
-/
import InfoGeometry.Meta.ArchetypePipeline
import Lean
import Lean.Elab.Tactic
import Lean.Elab.Command

open Lean Meta Elab Command Term Tactic

namespace InfoGeometry.MetaCompiler

-- ============================================================================
-- 1. Automated Solver Engine
-- ============================================================================

def autoDischargeCascade (mvarId : MVarId) : TermElabM Unit := do
  let autoTac ← `(tactic| first
    | intros; rfl
    | intros; decide
    | intros; simp_all
    | intros; omega)
  try
    let remaining ← Tactic.run mvarId do
      evalTactic autoTac
    if !remaining.isEmpty then
      throwError "Discharge cascade left {remaining.length} unsolved goal(s)."
  catch ex =>
    throwError m!"Automated discharge cascade failed to close the goal.\n\
                  Portfolio attempted: [rfl, decide, simp_all, omega].\n\
                  Details: {ex.toMessageData}"

-- ============================================================================
-- 2. Promotion Synthesis Core
-- ============================================================================

def synthesizePromotion
    (candName : Name)
    (targetName? : Option Name := none)
    (tacStx? : Option Syntax := none)
    : TermElabM (Name × Declaration) := do
  let env ← getEnv
  let cinfo ← getConstInfo candName
  let targetName := targetName?.getD (candName ++ `proved)

  if env.contains targetName then
    throwError "Cannot promote '{candName}': Target declaration '{targetName}' already exists."

  forallTelescopeReducing cinfo.type fun xs body => do
    let body ← whnf body
    if !body.isAppOf ``TypedArchetype then
      throwError "Declaration '{candName}' is not a `TypedArchetype` (type: {body})"

    let args := body.getAppArgs
    if args.size < 2 then
      throwError "Malformed `TypedArchetype` expression in '{candName}'"

    let u := body.getAppFn.constLevels!.headD Level.zero
    let inputType := args[0]!
    let statusExpr := args[1]!

    let stNorm ← whnf statusExpr
    if stNorm.isConstOf ``Status.proved then
      throwError "Archetype '{candName}' is already in Status.proved."

    let candidateConst := Lean.mkConst candName (cinfo.levelParams.map mkLevelParam)
    let candidateApp   := mkAppN candidateConst xs
    let claimApp       := mkApp3 (Lean.mkConst ``TypedArchetype.claim [u]) inputType statusExpr candidateApp

    let goalType ← withLocalDeclD `x inputType fun x => do
      let claimX ← whnf (mkApp claimApp x)
      mkForallFVars #[x] claimX

    let mvar ← mkFreshExprMVar goalType (userName := targetName.appendAfter "_evidence")

    match tacStx? with
    | some customTac =>
      let remaining ← Tactic.run mvar.mvarId! do
        evalTactic customTac
      if !remaining.isEmpty then
        throwError "Custom tactic script left {remaining.length} unsolved goal(s)."
    | none =>
      autoDischargeCascade mvar.mvarId!

    let proofTerm ← instantiateMVars mvar

    let innerVal := mkApp4
      (Lean.mkConst ``TypedArchetype.promoteToProved [u])
      inputType
      statusExpr
      candidateApp
      proofTerm

    let innerType := mkApp2 (Lean.mkConst ``TypedArchetype [u]) inputType (Lean.mkConst ``Status.proved)

    let fullVal  ← mkLambdaFVars xs innerVal
    let fullType ← mkForallFVars xs innerType

    let decl := Declaration.defnDecl {
      name        := targetName
      levelParams := cinfo.levelParams
      type        := ← instantiateMVars fullType
      value       := ← instantiateMVars fullVal
      hints       := .regular 0
      safety      := .safe
    }
    return (targetName, decl)

def executePromotion
    (candName : Name)
    (targetName? : Option Name := none)
    (tacStx? : Option Syntax := none)
    : CommandElabM Name := do
  let (targetName, decl) ← Command.liftTermElabM <|
    synthesizePromotion candName targetName? tacStx?

  Command.liftCoreM <| addDecl decl

  let audit ← Command.liftTermElabM <| auditArchetype targetName
  if audit.hasSorryAx then
    throwError s!"[QMS AUDIT REJECT] Proof for '{targetName}' transitively relies on `sorryAx`."

  if !audit.unapprovedAxioms.isEmpty then
    logWarning m!"[QMS WARNING] '{targetName}' relies on non-standard axioms: {audit.unapprovedAxioms}"

  modifyEnv fun env => archetypeExtension.addEntry env {
    declName := targetName
    status   := .proved
    axioms   := audit.transitiveAxioms
    isSound  := audit.isSound
  }

  logInfo m!"[PROMOTION SUCCESS] Registered proved archetype '{targetName}'\n\
             • Soundness: {audit.isSound}\n\
             • Transitive Axioms: {audit.transitiveAxioms}"
  return targetName

-- ============================================================================
-- 3. User Commands
-- ============================================================================

syntax (name := autoPromoteCmd) "#auto_promote " ident (" as " ident)? : command

elab_rules : command
  | `(command| #auto_promote $id:ident $[as $target:ident]?) => do
    let candName ← Command.liftTermElabM <| resolveGlobalConstNoOverload id
    let targetName? := target.map (·.getId)
    let _ ← executePromotion candName targetName? none

syntax (name := promoteArchetypeByCmd) "#promote_archetype " ident (" as " ident)? " by " tacticSeq : command

elab_rules : command
  | `(command| #promote_archetype $id:ident $[as $target:ident]? by $tac:tacticSeq) => do
    let candName ← Command.liftTermElabM <| resolveGlobalConstNoOverload id
    let targetName? := target.map (·.getId)
    let _ ← executePromotion candName targetName? (some tac.raw)

elab "#auto_promote_all" : command => do
  let env ← getEnv
  let registered := getRegisteredArchetypes env
  let candidates := registered.filter (·.status == Status.candidate)

  if candidates.isEmpty then
    logInfo "No unproven candidate archetypes found in environment registry."
    return

  let mut succeeded : Array (Name × Name) := #[]
  let mut failed    : Array (Name × String) := #[]

  for cand in candidates do
    try
      let targetName ← executePromotion cand.declName none none
      succeeded := succeeded.push (cand.declName, targetName)
    catch ex =>
      let errStr ← liftCoreM <| ex.toMessageData.toString
      failed := failed.push (cand.declName, errStr)

  let mut msg := m!"=== Epistemic Batch Promotion Audit ===\n\
                    Evaluated Candidates : {candidates.size}\n\
                    Successfully Proved  : {succeeded.size}\n\
                    Unsolved / Blocked   : {failed.size}\n\n"

  if !succeeded.isEmpty then
    msg := msg ++ "Promoted Archetypes:\n"
    for (src, dst) in succeeded do
      msg := msg ++ m!"  ✓ {src} ➜ {dst}\n"

  if !failed.isEmpty then
    msg := msg ++ "\nUnsolved Claims (Require Manual Guided Proof):\n"
    for (src, err) in failed do
      msg := msg ++ m!"  ✗ {src}: {err}\n"

  logInfo msg

-- ============================================================================
-- 4. Interactive Proof-Mode Tactics
-- ============================================================================

syntax (name := dischargeArchetypeTac) "discharge_archetype " ident (ppSpace term)? : tactic

@[tactic dischargeArchetypeTac]
def elabDischargeArchetype : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| discharge_archetype $id:ident $t:term) =>
    evalTactic (← `(tactic| exact (TypedArchetype.discharge $id $t)))
  | `(tactic| discharge_archetype $id:ident) =>
    evalTactic (← `(tactic| exact (TypedArchetype.discharge $id ·)))
  | _ => throwUnsupportedSyntax

syntax (name := haveArchetypeTac) "have_archetype " ident " with " term " as " ident : tactic

@[tactic haveArchetypeTac]
def elabHaveArchetype : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| have_archetype $id:ident with $t:term as $h:ident) =>
    evalTactic (← `(tactic| have $h := TypedArchetype.discharge $id $t))
  | _ => throwUnsupportedSyntax

end InfoGeometry.MetaCompiler
