import InfoGeometry.Canonical.ProofTwoCategoryHodgeColimitBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ProofTwoCategoryHodgeColimitCapstone

open InfoGeometry.Canonical.ProofTwoCategoryHodge

theorem proof_2cat_hodge_colimit_canonical_capstone
    (TwoCat : ProofTwoCategoryData)
    {nE nV : ℕ} (b1 : Matrix (Fin nE) (Fin nV) ℝ)
    {Node : Type*} (D : DAGNodeCone Node) (a : Node)
    {Stage : ℕ → Type*} {Limit : Type*}
    (Colim : DAGColimitCocone Stage Limit) (n : ℕ) (x : Stage n) :
    (graphDiracMatrix b1 * graphDiracMatrix b1 =
      Matrix.fromBlocks (b1 * b1.transpose) 0 0 (b1.transpose * b1)) ∧
    (a ∈ D.forwardCone a ∩ D.backwardCone a) ∧
    (Colim.toLimit (n + 1) (Colim.shift n x) = Colim.toLimit n x) :=
  ⟨dirac_square_eq_hodge_laplacian b1,
    dag_cone_acyclic_self D a,
    colimit_transport_invariance Colim n x⟩

end InfoGeometry.Canonical.ProofTwoCategoryHodgeColimitCapstone
