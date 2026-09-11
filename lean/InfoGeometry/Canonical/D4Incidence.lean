import Mathlib.Data.Fin.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionKleinFourTriality

open SimpleGraph

namespace InfoGeometry.Canonical

def d4IncidenceGraph : SimpleGraph KleinFour where
  Adj g h := (g = (0,0) ∧ h ≠ (0,0)) ∨ (h = (0,0) ∧ g ≠ (0,0))
  symm := by
    intro g h hAdj
    rcases hAdj with hAdj | hAdj
    · exact Or.inr hAdj
    · exact Or.inl hAdj
  loopless := ⟨by
    intro g hAdj
    rcases hAdj with hAdj | hAdj
    · exact hAdj.2 hAdj.1
    · exact hAdj.2 hAdj.1⟩

def d4DynkinGraph : SimpleGraph (Fin 4) where
  Adj i j := (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)
  symm := by
    intro i j h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := ⟨by
    intro i h
    rcases h with h | h
    · exact h.2 h.1
    · exact h.2 h.1⟩

def kleinFourEquivFin4 : KleinFour ≃ Fin 4 where
  toFun := fun g =>
    match g with
    | (0,0) => 0
    | (1,0) => 1
    | (0,1) => 2
    | (1,1) => 3
  invFun := fun i =>
    match i with
    | 0 => (0,0)
    | 1 => (1,0)
    | 2 => (0,1)
    | _ => (1,1)
  left_inv := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def d4GraphIso : SimpleGraph.Iso d4IncidenceGraph d4DynkinGraph where
  toEquiv := kleinFourEquivFin4
  map_rel_iff' := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    dsimp [d4IncidenceGraph, d4DynkinGraph, kleinFourEquivFin4]
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

def d4Incidence_isomorphic : d4IncidenceGraph ≃g d4DynkinGraph :=
  d4GraphIso

/-- The `d4IncidenceGraph` is connected. -/
theorem d4Incidence_connected : d4IncidenceGraph.Connected := by
  constructor
  · intro v w
    by_cases hv : v = (0, 0)
    · by_cases hw : w = (0, 0)
      · rw [hv, hw]
      · apply SimpleGraph.Adj.reachable
        rw [hv]; exact Or.inl ⟨rfl, hw⟩
    · by_cases hw : w = (0, 0)
      · rw [hw]
        apply Reachable.symm
        apply SimpleGraph.Adj.reachable
        exact Or.inl ⟨rfl, hv⟩
      · exact Reachable.trans (SimpleGraph.Adj.reachable (Or.inr ⟨rfl, hv⟩))
          (SimpleGraph.Adj.reachable (Or.inl ⟨rfl, hw⟩))

/-- The diameter of the incidence graph is `2`. -/
theorem d4Incidence_diameter : d4IncidenceGraph.Connected ∧ (∀ v w : KleinFour, d4IncidenceGraph.dist v w ≤ 2) := by
  refine ⟨d4Incidence_connected, ?_⟩
  intro v w
  by_cases hv : v = (0, 0)
  · by_cases hw : w = (0, 0)
    · rw [hv, hw, SimpleGraph.dist_self]; exact zero_le 2
    · have h_adj : d4IncidenceGraph.Adj v w := by
        rw [hv]; exact Or.inl ⟨rfl, hw⟩
      have hd : d4IncidenceGraph.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_adj
      linarith
  · by_cases hw : w = (0, 0)
    · have h_adj : d4IncidenceGraph.Adj v w := by
        rw [hw]; exact Or.inr ⟨rfl, hv⟩
      have hd : d4IncidenceGraph.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_adj
      linarith
    · have h1 : d4IncidenceGraph.Adj v (0,0) := Or.inr ⟨rfl, hv⟩
      have h2 : d4IncidenceGraph.Adj (0,0) w := Or.inl ⟨rfl, hw⟩
      have hd1 : d4IncidenceGraph.dist v (0,0) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1
      have hd2 : d4IncidenceGraph.dist (0,0) w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h2
      -- dist v w ≤ dist v (0,0) + dist (0,0) w
      have h_triangle := SimpleGraph.Reachable.dist_triangle_right (SimpleGraph.Adj.reachable h2) v
      linarith

instance : DecidableRel d4IncidenceGraph.Adj := fun g h =>
  inferInstanceAs (Decidable ((g = (0,0) ∧ h ≠ (0,0)) ∨ (h = (0,0) ∧ g ≠ (0,0))))

/-- The incidence matrix of `d4IncidenceGraph`. -/
def d4IncidenceMatrix (g h : KleinFour) : Bool :=
  decide (d4IncidenceGraph.Adj g h)

theorem d4IncidenceMatrix_symm (g h : KleinFour) :
    d4IncidenceMatrix g h = d4IncidenceMatrix h g := by
  by_cases h_adj : d4IncidenceGraph.Adj g h
  · have h_adj_symm := d4IncidenceGraph.symm h_adj
    simp [d4IncidenceMatrix, h_adj, h_adj_symm]
  · have h_adj_symm : ¬ d4IncidenceGraph.Adj h g := fun h_symm => h_adj (d4IncidenceGraph.symm h_symm)
    simp [d4IncidenceMatrix, h_adj, h_adj_symm]

theorem d4IncidenceMatrix_diag (g : KleinFour) :
    d4IncidenceMatrix g g = false := by
  simp [d4IncidenceMatrix]

theorem d4IncidenceMatrix_eq_true_iff (g h : KleinFour) :
    d4IncidenceMatrix g h = true ↔ d4IncidenceGraph.Adj g h := by
  exact decide_eq_true_iff

/-- Relating the graph adjacency to the grading submodules. -/
theorem adj_iff_planeComponent_ne (g h : KleinFour) :
    d4IncidenceGraph.Adj g h ↔ (g = (0,0) ∧ h ≠ (0,0)) ∨ (h = (0,0) ∧ g ≠ (0,0)) := by
  rfl

end InfoGeometry.Canonical
