import InfoGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Lean

open Lean

def printDebt : CoreM Unit := do
  let env ← getEnv
  let mut sorryDecls := #[]
  let mut axiomDecls := #[]
  
  for (name, info) in env.constants do
    -- Only look at definitions in this package
    if name.getRoot == `InfoGeometry then
      match info with
      | .axiomInfo _ => axiomDecls := axiomDecls.push name
      | _ => pure ()
      
      if let some value := info.value? then
        if value.containsConst (fun n => n == `sorryAx) then
          sorryDecls := sorryDecls.push name
          
  IO.println s!"Found {sorryDecls.size} declarations natively depending on `sorryAx`:"
  for decl in sorryDecls do
    IO.println s!"  - {decl}"
    
  IO.println s!"\nFound {axiomDecls.size} explicit `axiom` definitions:"
  for decl in axiomDecls do
    IO.println s!"  - {decl}"

#eval! printDebt
