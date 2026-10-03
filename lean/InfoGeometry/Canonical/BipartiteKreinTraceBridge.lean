import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.ClusterMutationIndexBridge

open Matrix

namespace InfoGeometry.Canonical.BipartiteKreinTraceBridge

open InfoGeometry.Canonical.ClusterMutationIndexBridge

/-!
# Bipartite Krein Trace Bridge

This module formalizes the exact algebraic projection from the SPT Krein involution
(the grading of the bipartite Clifford Dirac network) to the macroscopic
topological invariants of the Amplituhedron's Plabic graphs.

The topological index of the Krein involution β over a bipartite state space
(with V_white and V_black counting the dimensions of the ±1 eigenspaces)
is shown to exactly match the negative `colorIndex` (Helicity Defect) of the
on-shell graph.
-/

variable {R : Type*} [CommRing R]

/-- The Krein involution β represented as a diagonal matrix over a disjoint sum
    of white (+1 eigenspace) and black (-1 eigenspace) indices. -/
def kreinInvolution (Vwhite Vblack : ℕ) :
    Matrix (Fin Vwhite ⊕ Fin Vblack) (Fin Vwhite ⊕ Fin Vblack) R :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

/-- The trace of the Krein involution is the difference in dimension:
    Tr(β) = V_white - V_black. -/
theorem trace_kreinInvolution (Vwhite Vblack : ℕ) :
    Matrix.trace (kreinInvolution (R := R) Vwhite Vblack) =
      (Vwhite : R) - (Vblack : R) := by
  dsimp [kreinInvolution]
  rw [Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp; ring

/-- The combinatorial count data derived from the bipartite state space. -/
def stateSpaceCounts (Vwhite Vblack Eint next : ℕ)
    (hbal : (next : ℤ) = 3 * ((Vblack : ℤ) + (Vwhite : ℤ)) - 2 * (Eint : ℤ)) :
    PlabicCounts where
  Vblack := (Vblack : ℤ)
  Vwhite := (Vwhite : ℤ)
  Eint := (Eint : ℤ)
  next := (next : ℤ)
  trivalentBalance := hbal

/-- Fundamental Theorem: The topological trace of the SPT Krein involution
    over the bipartite state space is exactly the negative color index
    (and thus the negative helicity defect) of the macroscopic Plabic graph. -/
theorem trace_krein_eq_neg_colorIndex (Vwhite Vblack Eint next : ℕ)
    (hbal : (next : ℤ) = 3 * ((Vblack : ℤ) + (Vwhite : ℤ)) - 2 * (Eint : ℤ)) :
    Matrix.trace (kreinInvolution (R := ℤ) Vwhite Vblack) =
      - (stateSpaceCounts Vwhite Vblack Eint next hbal).colorIndex := by
  rw [trace_kreinInvolution]
  dsimp [stateSpaceCounts, PlabicCounts.colorIndex]
  ring

/-- Extension to Helicity Defect: The Krein trace also exactly equals the
    negative helicity defect under the trivalent balance. -/
theorem trace_krein_eq_neg_helicityDefect (Vwhite Vblack Eint next : ℕ)
    (hbal : (next : ℤ) = 3 * ((Vblack : ℤ) + (Vwhite : ℤ)) - 2 * (Eint : ℤ)) :
    Matrix.trace (kreinInvolution (R := ℤ) Vwhite Vblack) =
      - (stateSpaceCounts Vwhite Vblack Eint next hbal).helicityDefect := by
  rw [trace_krein_eq_neg_colorIndex]
  have h_eq := PlabicCounts.helicityDefect_eq_colorIndex (stateSpaceCounts Vwhite Vblack Eint next hbal)
  rw [h_eq]

end InfoGeometry.Canonical.BipartiteKreinTraceBridge
