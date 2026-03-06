import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Lean

open Lean Meta

def searchEnv (q : String) : MetaM Unit := do
  let env ← getEnv
  IO.println s!"--- Searching for {q} ---"
  let mut count := 0
  for (name, _) in env.constants do
    let n := toString name
    if n.contains q then
      if count < 50 then IO.println n
      count := count + 1
  IO.println s!"Total matches for {q}: {count}"
