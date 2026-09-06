import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import DAG.SearchRank

/-!
# scripts.DAG.Exploration.SearchRank

Exploratory script for ranked token-frequency search over the environment.
-/

open Lean Meta

#eval! DAG.SearchRank.searchEnvMany
  ["ExteriorAlgebra", "CliffordAlgebra", "finrank"]
