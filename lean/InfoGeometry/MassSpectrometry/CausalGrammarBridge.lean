import InfoGeometry.MassSpectrometry.CausalTransferArchitecture
import InfoGeometry.MassSpectrometry.FragmentationPath

/-!
# Certified causal transfer as a stochastic grammar

The transfer architecture supplies support and mass-descent facts, while
`StochasticGrammar` supplies the probabilistic path semantics.  This module is
the deliberately small interface between those owners: normalization is an
explicit certificate and is never inferred from a transfer matrix alone.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-- The diagonal of a genuine Gram operator is nonnegative.  This is the
native finite-dimensional positivity fact available for the correlation lane;
it does not imply entrywise positivity of a directed cross-Gramian. -/
theorem gramOperator_diag_nonneg {n d : ℕ}
    (Z : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    0 ≤ gramOperator Z i i := by
  rw [gramOperator, Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro j hj
  simpa [Matrix.transpose_apply] using mul_self_nonneg (Z i j)

structure CausalGrammarCertificate {n d q : ℕ}
    (D : ValuedFragmentationDAG n)
    (ZParent ZChild : Matrix (Fin n) (Fin d) ℝ)
    (Φ : FiniteKANCausalKernel q) where
  weight_nonneg :
    ∀ i j, 0 ≤ fusedCausalTransfer D ZParent ZChild Φ i j
  row_sum_le_one :
    ∀ i, ∑ j, fusedCausalTransfer D ZParent ZChild Φ i j ≤ 1

def CausalGrammarCertificate.grammar
    {n d q : ℕ}
    {D : ValuedFragmentationDAG n}
    {ZParent ZChild : Matrix (Fin n) (Fin d) ℝ}
    {Φ : FiniteKANCausalKernel q}
    (C : CausalGrammarCertificate D ZParent ZChild Φ) :
    StochasticGrammar D.toDAG where
  weight := fusedCausalTransfer D ZParent ZChild Φ
  weight_nonneg := C.weight_nonneg
  support := by
    intro i j h
    exact fusedCausalTransfer_support_edge D ZParent ZChild Φ h
  row_sum_le_one := C.row_sum_le_one

@[simp] theorem CausalGrammarCertificate.grammar_weight
    {n d q : ℕ}
    {D : ValuedFragmentationDAG n}
    {ZParent ZChild : Matrix (Fin n) (Fin d) ℝ}
    {Φ : FiniteKANCausalKernel q}
    (C : CausalGrammarCertificate D ZParent ZChild Φ) (i j : Fin n) :
    C.grammar.weight i j = fusedCausalTransfer D ZParent ZChild Φ i j :=
  rfl

theorem CausalGrammarCertificate.grammar_rank_decreases
    {n d q : ℕ}
    {D : ValuedFragmentationDAG n}
    {ZParent ZChild : Matrix (Fin n) (Fin d) ℝ}
    {Φ : FiniteKANCausalKernel q}
    (C : CausalGrammarCertificate D ZParent ZChild Φ)
    {i j : Fin n} (h : C.grammar.weight i j ≠ 0) :
    D.toDAG.rank j < D.toDAG.rank i := by
  exact C.grammar.rank_decreases_of_weight_ne_zero h

theorem CausalGrammarCertificate.grammar_mass_decreases
    {n d q : ℕ}
    {D : ValuedFragmentationDAG n}
    {ZParent ZChild : Matrix (Fin n) (Fin d) ℝ}
    {Φ : FiniteKANCausalKernel q}
    (C : CausalGrammarCertificate D ZParent ZChild Φ)
    {i j : Fin n} (h : C.grammar.weight i j ≠ 0) :
    D.massOf j < D.massOf i := by
  exact fusedCausalTransfer_mass_decreases D ZParent ZChild Φ h

theorem CausalGrammarCertificate.path_probability_nonneg
    {n d q : ℕ}
    {D : ValuedFragmentationDAG n}
    {ZParent ZChild : Matrix (Fin n) (Fin d) ℝ}
    {Φ : FiniteKANCausalKernel q}
    (C : CausalGrammarCertificate D ZParent ZChild Φ)
    {u v : Fin n} (p : D.toDAG.ValidPath u v) :
    0 ≤ C.grammar.validPathProbability p := by
  unfold StochasticGrammar.validPathProbability
  induction p with
  | nil => simp [StochasticGrammar.pathProbability]
  | cons edge rest ih =>
      simp only [FragmentationDAG.ValidPath.edges]
      rw [StochasticGrammar.pathProbability]
      exact mul_nonneg (C.weight_nonneg _ _) ih

theorem CausalGrammarCertificate.path_mass_decreases_of_cons
    {n d q : ℕ}
    {D : ValuedFragmentationDAG n}
    {ZParent ZChild : Matrix (Fin n) (Fin d) ℝ}
    {Φ : FiniteKANCausalKernel q}
    (C : CausalGrammarCertificate D ZParent ZChild Φ)
    {u v : Fin n} {w : Fin n}
    (edge : D.toDAG.edge u v) (rest : D.toDAG.ValidPath v w) :
    D.massOf v < D.massOf u := by
  exact D.mass_decreases edge

end InfoGeometry.MassSpectrometry
