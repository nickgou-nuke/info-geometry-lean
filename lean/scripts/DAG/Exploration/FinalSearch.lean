import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import DAG.FinalSearch
import scripts.DAG.Exploration.Common

/-!
# scripts.DAG.Exploration.FinalSearch

Exploratory script that runs final environment search queries for key algebraic tokens.
-/

open Lean Meta

private def imports : Array Import := #[
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Basic },
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Contraction },
  { module := `Mathlib.LinearAlgebra.CliffordAlgebra.Equivs },
  { module := `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic },
  { module := `Mathlib.LinearAlgebra.Dimension.Finrank },
  { module := `DAG.FinalSearch }
]

private def runSearch : MetaM Unit :=
  DAG.FinalSearch.searchEnv
    ["finrank_matrix", "equivExterior", "ExteriorAlgebra", "CliffordAlgebra", "finrank"]

def main : IO Unit :=
  ScriptDAGExploration.runMetaScript imports runSearch
