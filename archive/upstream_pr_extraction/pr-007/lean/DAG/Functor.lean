import Lean
import DAG.Basic
import DAG.Disassembler
import DAG.Isomorphism
import DAG.QueryEngine

open Lean
open DAG

namespace DAG

/--
  Optimized Categorical Shape Search.
  Instead of O(N^4) nested loops, we use Hash Joins for O(N^2) or better.
-/

structure MorphismInfo where
  decl : Name
  dom  : Name
  cod  : Name
  deriving BEq, Hashable, Repr

/-- Shallow, pure morphism recognition to avoid MetaM/whnf overhead during global scans. -/
def recognizeMorphismShallow (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .forallE _ d b _ =>
      if !b.hasLooseBVars then some (d, b) else none
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isConst && args.size >= 2 then
        let s := fn.constName!.toString
        if s.endsWith "Hom" || s.endsWith "Equiv" || s.endsWith "Iso" || s.endsWith "Map" then
          some (args[args.size - 2]!, args[args.size - 1]!)
        else none
      else none

def getAllMorphisms (env : Environment) (ns? : Option Name := none) : IO (Array MorphismInfo) := do
  let mut morphs := #[]
  for (name, ci) in env.constants do
    if let some ns := ns? then
      if !ns.isPrefixOf name then continue
    match recognizeMorphismShallow ci.type with
    | some (dom, cod) =>
        match dom.getAppFn, cod.getAppFn with
        | .const d _ , .const c _ =>
            morphs := morphs.push { decl := name, dom := d, cod := c }
        | _, _ => pure ()
    | none => pure ()
  return morphs

def findCommutativeSquares (env : Environment) (ns? : Option Name := none) : IO (Array (MorphismInfo × MorphismInfo × MorphismInfo × MorphismInfo)) := do
  let morphs ← getAllMorphisms env ns?
  let mut byDom : Std.HashMap Name (Array MorphismInfo) := {}
  for m in morphs do
    byDom := byDom.insert m.dom (byDom.getD m.dom #[] |>.push m)

  let mut results := #[]

  -- Iterate through pairs starting at the same node A
  for f in morphs do
    let A := f.dom
    let B := f.cod

    -- Look for g: A -> C
    if let some g_candidates := byDom.get? A then
      for g in g_candidates do
        if f.decl == g.decl then continue -- Avoid triviality
        let C := g.cod

        -- Look for h: B -> D
        if let some h_candidates := byDom.get? B then
          for h in h_candidates do
            let D := h.cod

            -- Look for k: C -> D
            if let some k_candidates := byDom.get? C then
              for k in k_candidates do
                if k.cod != D then continue
                if h.decl == k.decl then continue

                -- The Commutativity Test
                let h_of_f := Expr.lam `x (Expr.const A [])
                  (Expr.app (Expr.const h.decl []) (Expr.app (Expr.const f.decl []) (Expr.bvar 0))) .default
                let k_of_g := Expr.lam `x (Expr.const A [])
                  (Expr.app (Expr.const k.decl []) (Expr.app (Expr.const g.decl []) (Expr.bvar 0))) .default

                let hash1 := computeStructuralHash h_of_f (k := 5) (blindConstants := false)
                let hash2 := computeStructuralHash k_of_g (k := 5) (blindConstants := false)

                if hash1 == hash2 then
                  results := results.push (f, g, h, k)

  return results

end DAG
