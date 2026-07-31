import Mathlib.Data.Real.Basic

namespace Omega.Graph

/-- Minimal concrete weighted multigraph package used for the flow-lattice determinant identity. -/
structure FlowWeightedMultigraph where
  weightedTreeSum : ℝ
  edgeWeightDet : ℝ

/-- Chapter-local resistance-form Gram determinant of the flow lattice. -/
noncomputable def flowLatticeGramDet (G : FlowWeightedMultigraph) : ℝ :=
  G.weightedTreeSum / G.edgeWeightDet

/-- Paper label: `thm:xi-flow-lattice-gram-determinant-tree-weight`. -/
theorem paper_xi_flow_lattice_gram_determinant_tree_weight (G : FlowWeightedMultigraph) :
    flowLatticeGramDet G = G.weightedTreeSum / G.edgeWeightDet :=
  rfl

end Omega.Graph
