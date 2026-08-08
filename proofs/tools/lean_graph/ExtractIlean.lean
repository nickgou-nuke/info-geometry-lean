import Lean
open Lean Elab Server

def testIlean (path : String) : IO Unit := do
  let ilean ← Ilean.load path
  IO.println s!"Loaded {path}, contains {ilean.module.trees.size} trees"
  
def main (args : List String) : IO Unit := do
  if args.isEmpty then return
  testIlean args.head!
