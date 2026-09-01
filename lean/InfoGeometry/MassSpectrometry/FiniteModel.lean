import InfoGeometry.MassSpectrometry.Core
import InfoGeometry.MassSpectrometry.FragmentationPath
import InfoGeometry.MassSpectrometry.ValuedFragmentationDAG
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling

/-!
# Integrated finite mass-spectrometry model

This structure packages the formally justified layers without asserting that a
molecular graph, SMILES string, or learned latent state is uniquely determined
by a spectrum. Those are downstream inference problems.
-/

namespace InfoGeometry.MassSpectrometry

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

/-- The measured spectrum has a deterministic proof-carrying mass-sorted serialization. -/
def canonicalSpectrum : CanonicalSpectrum :=
  M.spectrum.canonicalize

/-- Free-monoid sentence associated with the certified mass-sorted spectrum. -/
def spectralSentence : SpectralSentence :=
  M.spectrum.toSentence

@[simp] theorem spectralSentence_length :
    (FreeMonoid.toList M.spectralSentence).length = n := by
  exact M.spectrum.toSentence_length

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

/-- Every term in a Birkhoff decomposition is supported on a perfect matching. -/
theorem assignment_decomposes_over_perfectMatchings :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = M.assignment ∧
      ∀ σ,
        InfoGeometry.Routing.PermutationPerfectMatching.IsPerfectMatching
          (InfoGeometry.Routing.PermutationPerfectMatching.matrixSupport
            (hardAssignment σ)) := by
  exact softAssignment_decomposes_over_perfectMatchings M.assignment M.assignment_soft

/-- Read the grammar associated with one experimental condition. -/
def grammarAt (cond : CollisionCondition) : StochasticGrammar M.dag :=
  M.grammar.kernel cond

/-- Any nonzero transition selected at a collision condition lowers DAG rank. -/
theorem grammarAt_rank_decreases
    (cond : CollisionCondition) {u v : Fin n}
    (h : (M.grammarAt cond).weight u v ≠ 0) :
    M.dag.rank v < M.dag.rank u := by
  exact (M.grammarAt cond).rank_decreases_of_weight_ne_zero h

/-- Probability of a proof-carrying fragmentation path under one experimental condition. -/
def pathProbabilityAt (cond : CollisionCondition) {u v : Fin n}
    (p : M.dag.ValidPath u v) : ℝ :=
  (M.grammarAt cond).validPathProbability p

/-- Surprisal of a proof-carrying fragmentation path under one experimental condition. -/
def pathSurprisalAt (cond : CollisionCondition) {u v : Fin n}
    (p : M.dag.ValidPath u v) : ℝ :=
  (M.grammarAt cond).validPathSurprisal p

/-- Energy-conditioned path probability is multiplicative under valid path concatenation. -/
theorem pathProbabilityAt_concat
    (cond : CollisionCondition) {u v w : Fin n}
    (p : M.dag.ValidPath u v) (q : M.dag.ValidPath v w) :
    M.pathProbabilityAt cond (FragmentationDAG.ValidPath.concat p q) =
      M.pathProbabilityAt cond p * M.pathProbabilityAt cond q := by
  exact (M.grammarAt cond).validPathProbability_concat p q

/-- Energy-conditioned path surprisal is additive under valid path concatenation. -/
theorem pathSurprisalAt_concat
    (cond : CollisionCondition) {u v w : Fin n}
    (p : M.dag.ValidPath u v) (q : M.dag.ValidPath v w) :
    M.pathSurprisalAt cond (FragmentationDAG.ValidPath.concat p q) =
      M.pathSurprisalAt cond p + M.pathSurprisalAt cond q := by
  exact (M.grammarAt cond).validPathSurprisal_concat p q

end FiniteFragmentationModel

/--
Physical specialization of the finite capstone with an explicit positive mass
valuation.  The stochastic grammar is still indexed by the underlying
rank-certified DAG, while `valuedDag` separately certifies physical mass loss.
-/
structure FiniteValuedFragmentationModel (n : ℕ) where
  spectrum : Spectrum n
  valuedDag : ValuedFragmentationDAG n
  assignment : AssignmentMatrix n
  assignment_soft : IsSoftAssignment assignment
  grammar : EnergyConditionedGrammar valuedDag.toDAG

namespace FiniteValuedFragmentationModel

variable {n : ℕ} (M : FiniteValuedFragmentationModel n)

/-- The physical fragmentation graph is acyclic both by rank and by mass decrease. -/
theorem dag_isDAG : M.valuedDag.toDAG.IsDAG :=
  M.valuedDag.base_isDAG

/-- Every physical cleavage edge has strictly positive neutral mass loss. -/
theorem neutralLoss_pos {u v : Fin n} (h : M.valuedDag.edge u v) :
    0 < M.valuedDag.deltaMass u v :=
  M.valuedDag.deltaMass_pos h

/-- Every nonempty physical fragmentation path strictly decreases mass. -/
theorem mass_decreases_along_path {u v : Fin n}
    (p : Relation.TransGen M.valuedDag.edge u v) :
    M.valuedDag.massOf v < M.valuedDag.massOf u :=
  M.valuedDag.transGen_mass_lt p

/-- The soft assignment of a mass-valued model still admits the native Birkhoff decomposition. -/
theorem assignment_decomposes :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = M.assignment := by
  exact softAssignment_birkhoff_decomposition M.assignment M.assignment_soft

end FiniteValuedFragmentationModel

end InfoGeometry.MassSpectrometry
