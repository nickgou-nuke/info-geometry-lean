import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import DAG.Search
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.Search

Exploratory script for environment search with hybrid and ranked token matching.
-/

open Lean Meta

private def imports : Array Import := #[
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Basic },
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Contraction },
  { module := `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic },
  { module := `Mathlib.LinearAlgebra.ExteriorPower.Basis },
  { module := `Mathlib.LinearAlgebra.Dimension.Finrank },
  { module := `DAG.Search }
]

private def runSearch : MetaM Unit :=
  DAG.Search.searchEnvMany
    ["finrank_matrix", "finrank_exteriorAlgebra", "finrank_clif"]

def main : IO Unit :=
  ScriptDAGExploration.runMetaScript imports runSearch
