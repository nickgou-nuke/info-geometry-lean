import Lean

namespace DAG
open Lean

def arrayReplicate {α} (n : Nat) (x : α) : Array α :=
  Array.replicate n x

def collectDeps (e : Expr) : List Name :=
  e.foldConsts [] (· :: ·)

def isFromMainModule (env : Environment) (n : Name) : Bool :=
  env.getModuleIdxFor? n |>.any (env.header.moduleNames[·.toNat]! == env.mainModule)

def leafNameString (n : Name) : String :=
  (toString n).splitOn "." |>.getLastD ""

def containsPrivateMarker (s : String) : Bool :=
  (s.splitOn "._private.").length > 1 || s.startsWith "_private."

def isGeneratedOrUnstableName (n : Name) : Bool :=
  let l := leafNameString n
  containsPrivateMarker (toString n) ||
  ["match_", "proof_", "_aux"].any (l.startsWith ·) ||
  ["brecOn", "below", "ibelow", "injEq", "sizeOf_spec"].any (l.endsWith ·)

end DAG
