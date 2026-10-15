import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Kernel of the graph coboundary

For a simple undirected graph, the degree-zero coboundary sends a vertex
potential to its oriented edge differences. Its kernel consists exactly of
the functions constant on connected components. The edge carrier contains
both orientations of each adjacency; this avoids choosing an orientation and
does not introduce edge weights.

This is the graph-theoretic specialization needed alongside the finite
matrix-gradient calculation. It does not identify a separately chosen matrix
with this coboundary.
-/

namespace InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceKernel

open SimpleGraph

variable {V : Type*}

/-- Ordered orientations of the edges of a simple graph. -/
def OrientedEdge (G : SimpleGraph V) := {p : V × V // G.Adj p.1 p.2}

/-- The degree-zero graph coboundary: an oriented edge receives the
potential at its head minus the potential at its tail. -/
def incidence (G : SimpleGraph V) (f : V → ℝ) : OrientedEdge G → ℝ :=
  fun e => f e.1.2 - f e.1.1

/-- Vanishing of the coboundary is equivalent to equality across every edge. -/
theorem incidence_eq_zero_iff_adjacent_eq (G : SimpleGraph V) (f : V → ℝ) :
    incidence G f = 0 ↔ ∀ u v, G.Adj u v → f u = f v := by
  constructor
  · intro h u v huv
    have hEdge := congrFun h ⟨(u, v), huv⟩
    change f v - f u = 0 at hEdge
    exact (sub_eq_zero.mp hEdge).symm
  · intro h
    funext e
    change f e.1.2 - f e.1.1 = 0
    exact sub_eq_zero.mpr (h e.1.1 e.1.2 e.2).symm

/-- A potential whose coboundary vanishes is constant along every walk. -/
theorem equal_of_reachable_of_incidence_eq_zero
    (G : SimpleGraph V) (f : V → ℝ)
    (hinc : incidence G f = 0) {u v : V} (hReach : G.Reachable u v) :
    f u = f v := by
  have hedge := (incidence_eq_zero_iff_adjacent_eq G f).mp hinc
  rcases hReach with ⟨p⟩
  induction p with
  | nil => rfl
  | @cons a b c hab p ih => exact (hedge a b hab).trans ih

/-- The kernel of the graph coboundary consists precisely of functions
constant on each connected component. -/
theorem incidence_eq_zero_iff_componentwise_constant
    (G : SimpleGraph V) (f : V → ℝ) :
    incidence G f = 0 ↔
      ∀ u v, G.connectedComponentMk u = G.connectedComponentMk v → f u = f v := by
  constructor
  · intro h u v hcomp
    exact equal_of_reachable_of_incidence_eq_zero G f h
      (ConnectedComponent.exact hcomp)
  · intro h
    apply (incidence_eq_zero_iff_adjacent_eq G f).mpr
    intro u v huv
    exact h u v (ConnectedComponent.sound huv.reachable)

/-- Equivalent reachable-relation formulation of the componentwise kernel. -/
theorem incidence_eq_zero_iff_constant_on_reachable_pairs
    (G : SimpleGraph V) (f : V → ℝ) :
    incidence G f = 0 ↔ ∀ u v, G.Reachable u v → f u = f v := by
  constructor
  · intro h u v huv
    exact equal_of_reachable_of_incidence_eq_zero G f h huv
  · intro h
    apply (incidence_eq_zero_iff_adjacent_eq G f).mpr
    intro u v huv
    exact h u v huv.reachable

end InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceKernel
