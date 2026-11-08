import InfoGeometry.Analysis.Graph
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
`InfoGeometry.Analysis`

Lightweight support library for self‑analysis of the InfoGeometry project.
The goal is to collect graph‑theoretic utilities and other tools that may be
used by both Lean and external Python code.

This module re‑exports the core graph definitions from
`InfoGeometry.Analysis.Graph` so that `import InfoGeometry.Analysis` is
sufficient to access them.
-/

namespace InfoGeometry.Analysis

open InfoGeometry.Analysis.Graph

-- reexport names from the submodule for convenience
export InfoGeometry.Analysis.Graph (
  SimpleGraph EdgeKind IndexedGraph
  collectConsts collectDeps envToIndexedGraph envToGraph indexedToGraph
)

end InfoGeometry.Analysis
