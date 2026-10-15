import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Experimental.Sandbox.MadelungGraphIncidenceMatrix

/-!
# Incidence Gram energy and graph Laplacian normalization

The generic transpose-pairing identity specializes to the concrete
double-oriented simple-graph incidence matrix. Its Gram quadratic form is the
sum of squared edge differences. Since every undirected edge occurs in both
orientations, this quadratic form is twice the usual graph Laplacian quadratic
form, whose ordered-adjacency expression in Mathlib carries a factor `1 / 2`.

The generic algebraic identity is already available in
`Topology.EckmannDiscreteHodge`; this file supplies the graph-indexed
specialization and records its normalization relative to
`SimpleGraph.lapMatrix`.
-/

namespace Experimental.Sandbox.MadelungGraphIncidenceEnergy

open scoped BigOperators
open SimpleGraph
open Classical
open InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceKernel
open InfoGeometry.Experimental.Sandbox.MadelungGraphIncidenceMatrix

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Classical adjacency decisions are used only to construct the finite edge
subtype and its incidence matrix. -/
local instance orientedEdgeDecidableAdjacency (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

/-- The oriented-edge subtype is finite because it is a subtype of the finite
type `V × V`. -/
local instance orientedEdgeFintype (G : SimpleGraph V) :
    Fintype (OrientedEdge G) := by
  change Fintype {p : V × V // G.Adj p.1 p.2}
  exact Fintype.subtype
    (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2)
    (by simp)

/-- Incidence Gram energy is the sum of the squared edge differences. -/
theorem graphIncidence_gram_energy (G : SimpleGraph V) (f : V → ℝ) :
    dotProduct f
        (((graphIncidenceMatrix G).transpose * graphIncidenceMatrix G).mulVec f) =
      ∑ e : OrientedEdge G, ((graphIncidenceMatrix G).mulVec f e) ^ 2 := by
  classical
  rw [← Matrix.mulVec_mulVec]
  calc
    dotProduct f
        ((graphIncidenceMatrix G).transpose.mulVec
          ((graphIncidenceMatrix G).mulVec f)) =
      dotProduct ((graphIncidenceMatrix G).mulVec f)
        ((graphIncidenceMatrix G).mulVec f) := by
          exact Matrix.dotProduct_transpose_mulVec
            (graphIncidenceMatrix G) f ((graphIncidenceMatrix G).mulVec f)
    _ = ∑ e : OrientedEdge G, ((graphIncidenceMatrix G).mulVec f e) ^ 2 := by
      simp [dotProduct, pow_two]

/-- Sum over the two orientations of each edge equals twice the usual
Laplacian quadratic form. This records the normalization change caused by the
double-oriented edge carrier. -/
theorem graphIncidence_gram_eq_two_lapMatrix_form
    (G : SimpleGraph V) (f : V → ℝ) :
    dotProduct f
        (((graphIncidenceMatrix G).transpose * graphIncidenceMatrix G).mulVec f) =
      2 * Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f := by
  classical
  rw [graphIncidence_gram_energy]
  simp_rw [graphIncidenceMatrix_mulVec_apply, incidence]
  let q : V × V → Prop := fun p => G.Adj p.1 p.2
  have hsubtype :
      (∑ e : OrientedEdge G, (f e.1.2 - f e.1.1) ^ 2) =
        ∑ p : V × V, if q p then (f p.2 - f p.1) ^ 2 else 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype q
      (fun p : V × V => if q p then (f p.2 - f p.1) ^ 2 else 0)
    have hadjacent :
        (∑ p : {p : V × V // q p},
          if q p.1 then (f p.1.2 - f p.1.1) ^ 2 else 0) =
        ∑ p : {p : V × V // q p}, (f p.1.2 - f p.1.1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [ite_eq_left p.2]
    have hcomplement :
        (∑ p : {p : V × V // ¬ q p},
          if q p.1 then (f p.1.2 - f p.1.1) ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [p.2]
    rw [hadjacent, hcomplement, add_zero] at hsplit
    simpa [OrientedEdge, incidence, q] using hsplit
  have horder :
      (∑ p : V × V, if q p then (f p.2 - f p.1) ^ 2 else 0) =
        ∑ i : V, ∑ j : V,
          if G.Adj i j then (f i - f j) ^ 2 else 0 := by
    calc
      _ = ∑ i : V, ∑ j : V,
          if G.Adj i j then (f j - f i) ^ 2 else 0 := by
            simp only [q, Fintype.sum_prod_type]
      _ = ∑ i : V, ∑ j : V,
          if G.Adj i j then (f i - f j) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hadj : G.Adj i j
            · simp [hadj]
              ring
            · simp [hadj]
  rw [hsubtype, horder, G.lapMatrix_toLinearMap₂' ℝ f]
  ring

end

end Experimental.Sandbox.MadelungGraphIncidenceEnergy
