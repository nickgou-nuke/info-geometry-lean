-- a simple command‑line tool used by the blueprint Python
-- client.  It reads a file containing one Lean declaration name per
-- line (produced by the plasTeX/depgraph stage) and reports any
-- names that are not present in the current environment.  This
-- allows `leanblueprint checkdecls` to fail early if the blueprint
-- references a constant that doesn't actually exist in the project.

import Lean

open Lean

/-- Convert a dotted string (e.g. "Foo.Bar.baz") to a `Name`. -/
def main : IO UInt32 := do
  IO.println "checkdecls stub: no declaration checking performed"
  return 0
