/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar

/-!
# Terminal completion of fragmentation grammars

State zero is absorbing; `Fin.succ` embeds the original fragments. The
absorbing self-loop is deliberately outside the strictly decreasing DAG.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry

/-- A finite nonempty strict DAG cannot support a row-stochastic kernel. -/
theorem normalizedGrammar_uninhabited {n : ℕ} (hn : 0 < n)
    (D : FragmentationDAG n) : ¬ Nonempty (NormalizedGrammar D) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := Finite.exists_min D.rank
  rintro ⟨G⟩
  have hz : ∀ v, G.weight u v = 0 := by
    intro v
    by_contra h
    exact (not_lt_of_ge (hu v)) (D.rank_decreases (G.support h))
  have hsum := G.row_sum u
  simp only [hz, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

namespace StochasticGrammar
variable {n : ℕ} {D : FragmentationDAG n} (G : StochasticGrammar D)

/-- Complete the missing row mass by one absorbing state, using the existing
row-stochastic matrix owner rather than requiring terminal fragments to emit. -/
def absorbingFinCompletion :
    InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge.StochasticTransitionMatrix (n + 1) where
  A := Fin.cons (Fin.cons 1 (fun _ => 0))
    (fun u => Fin.cons (G.terminalWeight u) (G.weight u))
  nonneg := by
    intro u v
    refine Fin.cases ?_ (fun u => ?_) u
    · refine Fin.cases ?_ (fun _ => ?_) v <;> simp
    · refine Fin.cases ?_ (fun v => ?_) v
      · exact G.terminalWeight_nonneg u
      · exact G.weight_nonneg u v
  row_sum := by
    intro u
    refine Fin.cases ?_ (fun u => ?_) u
    · simp [Fin.sum_univ_succ]
    · simp [Fin.sum_univ_succ, terminalWeight]

@[simp] theorem absorbingFinCompletion_fragment (u v : Fin n) :
    G.absorbingFinCompletion.A u.succ v.succ = G.weight u v := rfl

@[simp] theorem absorbingFinCompletion_terminal (u : Fin n) :
    G.absorbingFinCompletion.A u.succ 0 = G.terminalWeight u := rfl

@[simp] theorem absorbingFinCompletion_absorbs :
    G.absorbingFinCompletion.A 0 0 = 1 := rfl

@[simp] theorem absorbingFinCompletion_no_return (v : Fin n) :
    G.absorbingFinCompletion.A 0 v.succ = 0 := rfl

/-- A fragment with no outgoing cleavage terminates with probability one. -/
theorem terminalWeight_eq_one_of_sink {u : Fin n}
    (hu : ∀ v, ¬ D.edge u v) : G.terminalWeight u = 1 := by
  have hz : ∀ v, G.weight u v = 0 := by
    intro v
    by_contra h
    exact hu v (G.support h)
  simp [terminalWeight, hz]

/-- Square-root amplitude normalization now applies to a usable completion. -/
theorem absorbingFinCompletion_amplitude_normalized (u : Fin (n + 1)) :
    ∑ v, (G.absorbingFinCompletion.amplitudeMatrix u v) ^ 2 = 1 :=
  G.absorbingFinCompletion.amplitude_row_l2_normalization u

end StochasticGrammar
end InfoGeometry.MassSpectrometry
