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



def isFromMainModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some midx =>
      let mods := env.header.moduleNames
      let m := mods[midx.toNat]!
      m == env.mainModule
  | none => false


def leafNameString (n : Name) : String :=
  match (toString n).splitOn "." |>.reverse with
  | x :: _ => x
  | [] => ""

def containsPrivateMarker (s : String) : Bool :=
  (s.splitOn "._private.").length > 1 || s.startsWith "_private."

def isGeneratedOrUnstableName (n : Name) : Bool :=
  let s := toString n
  let leaf := leafNameString n
  containsPrivateMarker s ||
  leaf.startsWith "match_" ||
  leaf.startsWith "proof_" ||
  leaf.startsWith "_aux" ||
  leaf.endsWith "brecOn" ||
  leaf.endsWith "below" ||
  leaf.endsWith "ibelow" ||
  leaf.endsWith "injEq" ||
  leaf.endsWith "sizeOf_spec"

end DAG
