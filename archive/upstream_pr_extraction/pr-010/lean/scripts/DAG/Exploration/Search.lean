import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import DAG.Search

/-!
# scripts.DAG.Exploration.Search

Exploratory script for environment search with hybrid and ranked token matching.
-/

open Lean Meta

#eval! DAG.Search.searchEnvMany
  ["finrank_matrix", "finrank_exteriorAlgebra", "finrank_clif"]
