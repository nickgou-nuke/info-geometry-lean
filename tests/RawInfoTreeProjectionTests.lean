/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.RawInfoTreeExport

/-! The reused digest must give the same display fields as the original
expression projection, including absent assignments and let values. -/

open Lean DAG.RawInfoTreeExport

example (lctx : LocalContext) (e : Expr) :
    "t_" ++ ((DAG.TermDigest.digestWithLctx lctx e).digest.take 40).toString =
      exprProjectionWithLctx lctx e := rfl

example (lctx : LocalContext) (e : Option Expr) :
    (e.map fun value => (DAG.TermDigest.digestWithLctx lctx value).digest).map
        (fun digest => "t_" ++ (digest.take 40).toString) =
      e.map (exprProjectionWithLctx lctx) := by
  cases e <;> rfl

-- Same variable identity with a changed type or let value must produce new
-- context rows; repeating an identical snapshot must still share those rows.
#eval show IO Unit from do
  let id : FVarId := ⟨`x⟩
  let nat := mkConst `Nat
  let bool := mkConst `Bool
  let original := LocalContext.empty.mkLocalDecl id `x nat
  let changed := original.setType id bool
  let letOne := LocalContext.empty.mkLetDecl id `x nat (mkNatLit 1)
  let letTwo := LocalContext.empty.mkLetDecl id `x nat (mkNatLit 2)
  unless lctxSignature original == lctxSignature changed do
    throw (IO.userError "fixture no longer exercises the old signature collision")
  let action : ExportM Unit := do
    for ctx in [original, changed, letOne, letTwo, original] do
      emitLctxRef "root" "Module" "Module.lean" "node" "term" "source" ctx
  let (_, state) ← action.run {}
  unless state.lctxRefs.size == 5 && state.lctxDecls.size == 4 do
    throw (IO.userError "local context sharing lost a type/value distinction")
  unless (state.lctxRefs[0]?.map (·.lctxKey)) == (state.lctxRefs[4]?.map (·.lctxKey)) do
    throw (IO.userError "identical local contexts no longer share rows")

#eval show IO Unit from do
  let id : MVarId := ⟨`goal⟩
  let original := ({} : MetavarContext).addExprMVarDecl id `goal {} #[] (mkConst `Nat)
  let changed := ({} : MetavarContext).addExprMVarDecl id `goal {} #[] (mkConst `Bool)
  let assignedOne := { original with eAssignment := original.eAssignment.insert id (mkNatLit 1) }
  let assignedTwo := { original with eAssignment := original.eAssignment.insert id (mkNatLit 2) }
  unless mctxSignature original == mctxSignature changed do
    throw (IO.userError "fixture no longer exercises the old metavariable signature collision")
  let action : ExportM Unit := do
    for ctx in [original, changed, assignedOne, assignedTwo, original] do
      discard <| emitMctxRefAndDecls "root" "Module" "Module.lean" "node" "ref" ctx
  let (_, state) ← action.run {}
  unless state.mctxRefs.size == 5 && state.mctxDecls.size == 4 do
    throw (IO.userError "metavariable sharing lost a type or assignment distinction")
  unless (state.mctxRefs[0]?.map (·.mctxKey)) == (state.mctxRefs[4]?.map (·.mctxKey)) do
    throw (IO.userError "identical metavariable declarations no longer share rows")
