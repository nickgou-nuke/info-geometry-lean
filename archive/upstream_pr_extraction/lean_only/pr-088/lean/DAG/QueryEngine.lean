import Lean
import DAG.Basic

open Lean

namespace DAG

structure QueryState where
  env : Environment

def QueryM (α : Type) := QueryState → List α

instance : Monad QueryM where
  pure x := fun _ => [x]
  bind x f := fun s => (x s).flatMap (fun a => f a s)

namespace Query

def getEnv : QueryM Environment := fun s => [s.env]

def matchDeclaration : QueryM (Name × ConstantInfo) := fun s =>
  s.env.constants.toList

def where_ (p : Bool) : QueryM Unit := fun _ =>
  if p then [()] else []

inductive Chirality | Type | Value

def followChirality (ci : ConstantInfo) : Chirality → QueryM Expr
  | .Type => fun _ => [ci.type]
  | .Value => fun _ => match ci.value? with
    | some v => [v]
    | none => []

def stepExpr : Expr → QueryM Expr
  | .app f a         => fun _ => [f, a]
  | .lam _ t b _     => fun _ => [t, b]
  | .forallE _ t b _ => fun _ => [t, b]
  | .letE _ t v b _  => fun _ => [t, v, b]
  | .mdata _ e       => fun _ => [e]
  | .proj _ _ e      => fun _ => [e]
  | _                => fun _ => []

partial def reachExpr (start : Expr) (maxDepth : Nat) : QueryM Expr := do
  if maxDepth == 0 then return start
  let next ← stepExpr start
  let rest ← reachExpr next (maxDepth - 1)
  return rest

end Query

end DAG
