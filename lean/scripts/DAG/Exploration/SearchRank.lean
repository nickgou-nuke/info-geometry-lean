import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import DAG.SearchRank
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.SearchRank

Exploratory script for ranked token-frequency search over the environment.
-/

open Lean Meta

private def imports : Array Import := #[
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Basic },
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Contraction },
  { module := `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic },
  { module := `Mathlib.LinearAlgebra.Dimension.Finrank },
  { module := `DAG.SearchRank }
]

private def runSearch : MetaM Unit :=
  DAG.SearchRank.searchEnvMany
    ["ExteriorAlgebra", "CliffordAlgebra", "finrank"]

def main : IO Unit :=
  ScriptDAGExploration.runMetaScript imports runSearch
