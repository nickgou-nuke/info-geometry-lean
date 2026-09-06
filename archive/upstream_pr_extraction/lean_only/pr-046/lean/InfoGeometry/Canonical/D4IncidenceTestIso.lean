import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
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

end InfoGeometry.Canonical
