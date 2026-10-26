import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar

/-!
# Terminating fragmentation and absorbing completion

A nonempty finite strictly rank-decreasing DAG has a terminal vertex. Thus an
exactly row-normalized grammar on only its strict edges is uninhabited. The
existing substochastic grammar instead admits an explicit absorbing completion.
The completed Markov carrier is not itself claimed to be a strict DAG.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry
open scoped BigOperators

namespace FragmentationDAG

theorem exists_terminal_vertex {n : ℕ} [Nonempty (Fin n)] (D : FragmentationDAG n) :
    ∃ u, ∀ v, ¬ D.edge u v := by
  classical
  have hex : ∃ k : ℕ, ∃ u, D.rank u = k :=
    ⟨D.rank (Classical.arbitrary (Fin n)), Classical.arbitrary (Fin n), rfl⟩
  obtain ⟨u, hu⟩ := Nat.find_spec hex
  refine ⟨u, ?_⟩
  intro v hv
  have hmin : Nat.find hex ≤ D.rank v := Nat.find_min' hex ⟨v, rfl⟩
  have hdec := D.rank_decreases hv
  omega

end FragmentationDAG

namespace StochasticGrammar
variable {n : ℕ} {D : FragmentationDAG n}

theorem terminal_row_zero (G : StochasticGrammar D) {u : Fin n}
    (hu : ∀ v, ¬ D.edge u v) (v : Fin n) : G.weight u v = 0 := by
  by_contra h
  exact hu v (G.support h)

theorem terminal_weight_one (G : StochasticGrammar D) {u : Fin n}
    (hu : ∀ v, ¬ D.edge u v) : G.terminalWeight u = 1 := by
  simp [terminalWeight, G.terminal_row_zero hu]

theorem exists_full_terminal_weight [Nonempty (Fin n)] (G : StochasticGrammar D) :
    ∃ u, G.terminalWeight u = 1 := by
  obtain ⟨u, hu⟩ := D.exists_terminal_vertex
  exact ⟨u, G.terminal_weight_one hu⟩

/-- `none` is absorption; `some u` is an original fragment state. -/
def absorbingCompletion (G : StochasticGrammar D) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ
  | none, none => 1
  | none, some _ => 0
  | some u, none => G.terminalWeight u
  | some u, some v => G.weight u v

theorem absorbingCompletion_nonneg (G : StochasticGrammar D)
    (u v : Option (Fin n)) : 0 ≤ G.absorbingCompletion u v := by
  cases u <;> cases v
  · norm_num [absorbingCompletion]
  · norm_num [absorbingCompletion]
  · exact G.terminalWeight_nonneg _
  · exact G.weight_nonneg _ _

theorem absorbingCompletion_row_sum (G : StochasticGrammar D)
    (u : Option (Fin n)) : ∑ v, G.absorbingCompletion u v = 1 := by
  cases u with
  | none => simp [Fintype.sum_option, absorbingCompletion]
  | some u =>
    simp [Fintype.sum_option, absorbingCompletion, terminalWeight]

@[simp] theorem absorbingCompletion_original (G : StochasticGrammar D)
    (u v : Fin n) : G.absorbingCompletion (some u) (some v) = G.weight u v := rfl

@[simp] theorem absorbingCompletion_absorbs (G : StochasticGrammar D) :
    G.absorbingCompletion none none = 1 := rfl

theorem absorbingCompletion_original_rank_decreases (G : StochasticGrammar D)
    {u v : Fin n} (h : G.absorbingCompletion (some u) (some v) ≠ 0) :
    D.rank v < D.rank u := G.rank_decreases_of_weight_ne_zero h

end StochasticGrammar

/-- The old normalized strict-DAG carrier has no inhabitant when n is nonzero.
The empty-state exception is intentional. -/
theorem no_normalized_strict_grammar {n : ℕ} [Nonempty (Fin n)]
    {D : FragmentationDAG n} (G : NormalizedGrammar D) : False := by
  obtain ⟨u, hu⟩ := D.exists_terminal_vertex
  have hz : ∑ v, G.weight u v = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_contra h
    exact hu v (G.support h)
  have hone := G.row_sum u
  linarith

end InfoGeometry.MassSpectrometry
