import Lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import DAG.FinalSearch

/-!
# scripts.DAG.Exploration.FinalSearch

Exploratory script that runs final environment search queries for key algebraic tokens.
-/

open Lean Meta

#eval! DAG.FinalSearch.searchEnv
  ["finrank_matrix", "equivExterior", "ExteriorAlgebra", "CliffordAlgebra", "finrank"]
