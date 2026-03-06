import Mathlib
import Lean

open Lean Meta

def searchEnv (queries : List String) : MetaM Unit := do
  let env ← getEnv
  for q in queries do
    IO.println s!"--- Searching for '{q}' ---"
    let mut found := false
    for (name, _) in env.constants do
      let n := toString name
      if n.contains q then
        IO.println n
        found := true
    if !found then IO.println "❌ Not found."
