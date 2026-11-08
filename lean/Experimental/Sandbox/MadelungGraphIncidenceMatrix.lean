import Mathlib.Data.Matrix.Mul
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Experimental.Sandbox.MadelungGraphIncidenceKernel

/-!
# Matrix realization of the simple-graph coboundary

The row index is an ordered adjacent pair, so every unoriented simple edge
has its two orientations. Each row has coefficient `-1` at its tail and `+1`
at its head. The resulting matrix-vector product is exactly the edge-difference
coboundary from `MadelungGraphIncidenceKernel`; consequently its kernel is the
space of functions constant on connected components.

This is the unweighted incidence matrix. A weighted gradient needs additional
hypotheses (in particular, nonzero edge weights) to have the same kernel.
Because both orientations occur, summing squared edge differences over this
carrier counts every unoriented edge twice. Thus the associated Dirichlet
energy and incidence Gram Laplacian have a factor of two relative to a
single-orientation convention; the kernel characterization is unaffected.
-/

namespace InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceMatrix

open SimpleGraph
open InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceKernel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unweighted real incidence matrix, with one row for each orientation
of an edge and signs `-1` at the tail and `+1` at the head. -/
noncomputable def graphIncidenceMatrix (G : SimpleGraph V) :
    Matrix (OrientedEdge G) V ℝ := by
  classical
  exact fun e v => (if v = e.1.2 then (1 : ℝ) else 0) -
    (if v = e.1.1 then (1 : ℝ) else 0)

/-- On an oriented edge, multiplication by the incidence matrix computes
the head potential minus the tail potential. -/
theorem graphIncidenceMatrix_mulVec_apply
    (G : SimpleGraph V) (f : V → ℝ) (e : OrientedEdge G) :
    (graphIncidenceMatrix G).mulVec f e = incidence G f e := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [graphIncidenceMatrix, incidence]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- Function-valued matrix-vector multiplication by the incidence matrix is
the graph coboundary. -/
theorem graphIncidenceMatrix_mulVec
    (G : SimpleGraph V) (f : V → ℝ) :
    (graphIncidenceMatrix G).mulVec f = incidence G f := by
  funext e
  exact graphIncidenceMatrix_mulVec_apply G f e

/-- The matrix kernel of the simple-graph incidence matrix is exactly the
functions constant on connected components. -/
theorem graphIncidenceMatrix_mulVec_eq_zero_iff_componentwise_constant
    (G : SimpleGraph V) (f : V → ℝ) :
    (graphIncidenceMatrix G).mulVec f = 0 ↔
      ∀ u v, G.connectedComponentMk u = G.connectedComponentMk v → f u = f v := by
  rw [graphIncidenceMatrix_mulVec]
  exact incidence_eq_zero_iff_componentwise_constant G f

end InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceMatrix
