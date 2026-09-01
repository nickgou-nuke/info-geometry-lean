import InfoGeometry.MassSpectrometry.Core
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling

/-!
# Integrated finite mass-spectrometry model

This structure packages the formally justified layers without asserting that a
molecular graph, SMILES string, or learned latent state is uniquely determined
by a spectrum. Those are downstream inference problems.
-/

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-- Finite spectrum + latent fragmentation DAG + soft peak/fragment assignment
+ energy-conditioned fragmentation grammar. -/
structure FiniteFragmentationModel (n : ℕ) where
  spectrum : Spectrum n
  dag : FragmentationDAG n
  assignment : AssignmentMatrix n
  assignment_soft : IsSoftAssignment assignment
  grammar : EnergyConditionedGrammar dag

namespace FiniteFragmentationModel

variable {n : ℕ} (M : FiniteFragmentationModel n)

/-- The latent fragmentation relation is acyclic by construction. -/
theorem dag_isDAG : M.dag.IsDAG :=
  M.dag.isDAG

/-- Every model assignment admits a Birkhoff-von Neumann decomposition into
hard permutation assignments. -/
theorem assignment_decomposes :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = M.assignment := by
  exact softAssignment_birkhoff_decomposition M.assignment M.assignment_soft

/-- Read the grammar associated with one experimental condition. -/
def grammarAt (cond : CollisionCondition) : StochasticGrammar M.dag :=
  M.grammar.kernel cond

/-- Any nonzero transition selected at a collision condition lowers DAG rank. -/
theorem grammarAt_rank_decreases
    (cond : CollisionCondition) {u v : Fin n}
    (h : (M.grammarAt cond).weight u v ≠ 0) :
    M.dag.rank v < M.dag.rank u := by
  exact (M.grammarAt cond).rank_decreases_of_weight_ne_zero h

end FiniteFragmentationModel

end InfoGeometry.MassSpectrometry
