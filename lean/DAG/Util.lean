import Lean

namespace DAG
open Lean

def arrayReplicate {α} (n : Nat) (x : α) : Array α :=
  Array.replicate n x

/-- Collect all constant names referenced in an expression. -/

def collectDeps (e : Expr) : List Name :=
  let rec go (ex : Expr) (acc : List Name) : List Name :=
    match ex with
    | Expr.const n _ => n :: acc
    | Expr.app f a => go f (go a acc)
    | Expr.lam _ _ b _ => go b acc
    | Expr.forallE _ _ b _ => go b acc
    | Expr.letE _ _ v b _ => go v (go b acc)
    | Expr.mdata _ b => go b acc
    | Expr.proj _ _ b => go b acc
    | _ => acc
  go e []

end DAG
