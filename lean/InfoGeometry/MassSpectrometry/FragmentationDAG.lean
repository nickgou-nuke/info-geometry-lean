import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ranked fragmentation DAG

This module follows the repository's existing ranked-causal-net pattern:
acyclicity is proved from strict rank decrease and reachability is represented
with Mathlib's `Relation.ReflTransGen` / `Relation.TransGen`.
-/

namespace InfoGeometry.MassSpectrometry

/-- A finite directed fragmentation system certified by a strictly decreasing
natural-valued rank along every edge. -/
structure FragmentationDAG (n : ℕ) where
  edge : Fin n → Fin n → Prop
  rank : Fin n → ℕ
  rank_decreases : ∀ {u v}, edge u v → rank v < rank u

namespace FragmentationDAG

variable {n : ℕ} (D : FragmentationDAG n)

/-- Reflexive-transitive fragment reachability. -/
def Reach (u v : Fin n) : Prop :=
  Relation.ReflTransGen D.edge u v

/-- Nonempty fragment reachability. -/
def StrictReach (u v : Fin n) : Prop :=
  Relation.TransGen D.edge u v

/-- DAG condition expressed as absence of a nonempty directed self-path. -/
def IsDAG : Prop :=
  ∀ u, ¬ D.StrictReach u u

theorem edge_irrefl (u : Fin n) : ¬ D.edge u u := by
  intro h
  exact (Nat.lt_irrefl (D.rank u)) (D.rank_decreases h)

/-- Every nonempty fragmentation path strictly decreases the rank. -/
theorem transGen_rank_lt {u v : Fin n}
    (path : D.StrictReach u v) : D.rank v < D.rank u := by
  induction path with
  | single step => exact D.rank_decreases step
  | tail _ step ih =>
      exact Nat.lt_trans (D.rank_decreases step) ih

/-- Rank certification proves acyclicity for arbitrary finite path length. -/
theorem isDAG : D.IsDAG := by
  intro u loop
  exact Nat.lt_irrefl (D.rank u) (D.transGen_rank_lt loop)

theorem not_two_cycle {u v : Fin n} (huv : D.edge u v) : ¬ D.edge v u := by
  intro hvu
  have h₁ := D.rank_decreases huv
  have h₂ := D.rank_decreases hvu
  omega

theorem not_three_cycle {u v w : Fin n}
    (huv : D.edge u v) (hvw : D.edge v w) : ¬ D.edge w u := by
  intro hwu
  have h₁ := D.rank_decreases huv
  have h₂ := D.rank_decreases hvw
  have h₃ := D.rank_decreases hwu
  omega

end FragmentationDAG

end InfoGeometry.MassSpectrometry
