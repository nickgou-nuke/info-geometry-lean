import Lean

open Lean Meta Elab Tactic Command

namespace InfoGeometry.Meta.HiveLogos

structure ProbeArtifact where
  artifactKind : String
  space : String
  module : String
  goalIndex : Nat
  targetPretty : String
  canonicalPreimage : String
  targetHashShapeCanonical : String
  normalizationPolicy : String
  fvarPolicy : String
  hasUnassignedMVars : Bool
  unabstractedFVars : Array String
  deriving ToJson

structure FossilArtifact where
  artifactKind : String
  space : String
  constName : String
  declarationKind : String
  fullTypePretty : String
  conclusionPretty : String
  fullTypeHashShapeCanonical : String
  conclusionHashShapeCanonical : String
  kernelStatus : String
  deriving ToJson

abbrev jsonPrefix : String := "HIVE_JSON "

def toShapeString : Expr → String
  | .bvar idx        => s!"(bvar {idx})"
  | .fvar _          => "(error unabstracted_fvar)"
  | .mvar _          => "(error unassigned_mvar)"
  | .sort _          => "(sort)"
  | .const n _       => s!"(const {n})"
  | .app f a         => s!"(app {toShapeString f} {toShapeString a})"
  | .lam _ d b _     => s!"(lam {toShapeString d} {toShapeString b})"
  | .forallE _ d b _ => s!"(forall {toShapeString d} {toShapeString b})"
  | .letE _ t v b _  => s!"(let {toShapeString t} {toShapeString v} {toShapeString b})"
  | .lit (.natVal n) => s!"(nat {n})"
  | .lit (.strVal s) => s!"(str {s.quote})"
  | .mdata _ e       => toShapeString e
  | .proj n i e      => s!"(proj {n} {i} {toShapeString e})"


def getUsedFVarsInOrder (e : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let mut used : Array Expr := #[]
  for fvar in lctx.getFVars do
    if e.containsFVar fvar.fvarId! then
      used := used.push fvar
  return used


def canonicalizeShape (e : Expr) : MetaM String := do
  let eInst ← instantiateMVars e
  let usedFVars ← getUsedFVarsInOrder eInst
  let eWhnf ← whnf eInst
  let abstracted := eWhnf.abstract usedFVars
  return toShapeString abstracted


def unabstractedFVarNames (e : Expr) : MetaM (Array String) := do
  let lctx ← getLCtx
  let mut out : Array String := #[]
  for fvar in lctx.getFVars do
    if e.containsFVar fvar.fvarId! then
      out := out.push (toString fvar)
  return out


def declarationKindString (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _      => "ax!om"
  | .thmInfo _        => "theorem"
  | .defnInfo _       => "definition"
  | .opaqueInfo _     => "opaque"
  | .quotInfo _       => "quot"
  | .inductInfo _     => "inductive"
  | .ctorInfo _       => "constructor"
  | .recInfo _        => "recursor"


def emitJsonLine [ToJson α] (payload : α) : TacticM Unit :=
  logInfo m!"{jsonPrefix}{(toJson payload).compress}"


elab "hive_probe" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let targetInst ← instantiateMVars target
    let usedFVars ← getUsedFVarsInOrder targetInst
    let targetWhnf ← whnf targetInst
    let abstracted := targetWhnf.abstract usedFVars
    let shapeStr := toShapeString abstracted
    let pretty ← ppExpr target
    let leftovers ← unabstractedFVarNames abstracted
    let payload : ProbeArtifact := {
      artifactKind := "InfoTreeArtifact"
      space := "infotree"
      module := toString (← getMainModule)
      goalIndex := 0
      targetPretty := toString pretty
      canonicalPreimage := shapeStr
      targetHashShapeCanonical := shapeStr
      normalizationPolicy := "instantiateMVars+whnf(default)"
      fvarPolicy := "used-fvars-in-local-context-order"
      hasUnassignedMVars := target.hasExprMVar
      unabstractedFVars := leftovers
    }
    emitJsonLine payload


elab "#hive_index_decl " ident:ident : command => withRef ident do
  liftTermElabM do
    let name ← resolveGlobalConstNoOverload ident
    let env ← getEnv
    let some info := env.find? name
      | throwError m!"Declaration not found: {name}"
    let fullTypePretty := toString info.type
    let fullTypeShape ← canonicalizeShape info.type
    let (conclusionPretty, conclusionShape) ← forallTelescopeReducing info.type fun _ body => do
      return (toString body, ← canonicalizeShape body)
    let payload : FossilArtifact := {
      artifactKind := "DiamondFossil"
      space := "logos"
      constName := toString name
      declarationKind := declarationKindString info
      fullTypePretty := fullTypePretty
      conclusionPretty := conclusionPretty
      fullTypeHashShapeCanonical := fullTypeShape
      conclusionHashShapeCanonical := conclusionShape
      kernelStatus := "verified"
    }
    logInfo m!"{jsonPrefix}{(toJson payload).compress}"


private def applyRetrievedConst (name : Name) (strict : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  let saved ← saveState
  let newGoals ←
    try
      withMainContext do
        goal.applyConst name
    catch e =>
      saved.restore
      throwError m!"[HIVE REFUSAL] {name} cannot be applied: {e.toMessageData}"
  if strict && !newGoals.isEmpty then
    saved.restore
    throwError m!"[HIVE REFUSAL] {name} applied but left {newGoals.length} subgoal(s)."
  replaceMainGoal newGoals
  if newGoals.isEmpty then
    logInfo m!"[HIVE CLOSED] {name} closed the goal."
  else
    logInfo m!"[HIVE APPLIED] {name} generated {newGoals.length} subgoal(s)."


elab "hive_try_const " c:ident : tactic => do
  let name ← resolveGlobalConstNoOverload c
  applyRetrievedConst name false


elab "hive_annihilate " c:ident : tactic => do
  let name ← resolveGlobalConstNoOverload c
  applyRetrievedConst name true

end InfoGeometry.Meta.HiveLogos
