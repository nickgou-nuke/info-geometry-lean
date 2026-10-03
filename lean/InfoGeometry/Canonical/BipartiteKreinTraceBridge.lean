import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.ClusterMutationIndexBridge

open Matrix

namespace InfoGeometry.Canonical.BipartiteKreinTraceBridge

open InfoGeometry.Canonical.ClusterMutationIndexBridge

/-!
# Finite Grading Trace and Encoded Bipartite Counts

This module proves a finite-dimensional trace identity for a diagonal
involution with `Vwhite` positive and `Vblack` negative coordinates. It then
encodes those same two natural numbers as fields of `PlabicCounts` and rewrites
the trace as the negative of the resulting count index.

No map from a Clifford Dirac eigenspace to an on-shell graph is defined here.
The equalities below do not establish a topological index theorem, mutation
invariance of a grading trace, or a physical helicity theorem.
-/

variable {R : Type*} [CommRing R]

/-- A diagonal involution with `+1` coordinates indexed by `Fin Vwhite` and
    `-1` coordinates indexed by `Fin Vblack`. -/
def kreinInvolution (Vwhite Vblack : ℕ) :
    Matrix (Fin Vwhite ⊕ Fin Vblack) (Fin Vwhite ⊕ Fin Vblack) R :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

/-- The trace of this diagonal grading is the difference of the two index
    cardinalities. -/
theorem trace_kreinInvolution (Vwhite Vblack : ℕ) :
    Matrix.trace (kreinInvolution (R := R) Vwhite Vblack) =
      (Vwhite : R) - (Vblack : R) := by
  dsimp [kreinInvolution]
  rw [Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp; ring

/-- Plabic count fields filled from the same cardinalities and edge data.
    This is an encoding function; it does not construct a graph or a state
    space map. -/
def stateSpaceCounts (Vwhite Vblack Eint next : ℕ)
    (hbal : (next : ℤ) = 3 * ((Vblack : ℤ) + (Vwhite : ℤ)) - 2 * (Eint : ℤ)) :
    PlabicCounts where
  Vblack := (Vblack : ℤ)
  Vwhite := (Vwhite : ℤ)
  Eint := (Eint : ℤ)
  next := (next : ℤ)
  trivalentBalance := hbal

/-- After the cardinalities are encoded as count fields, the diagonal trace is
    the negative of their `colorIndex`. -/
theorem trace_krein_eq_neg_colorIndex (Vwhite Vblack Eint next : ℕ)
    (hbal : (next : ℤ) = 3 * ((Vblack : ℤ) + (Vwhite : ℤ)) - 2 * (Eint : ℤ)) :
    Matrix.trace (kreinInvolution (R := ℤ) Vwhite Vblack) =
      - (stateSpaceCounts Vwhite Vblack Eint next hbal).colorIndex := by
  rw [trace_kreinInvolution]
  dsimp [stateSpaceCounts, PlabicCounts.colorIndex]
  ring

/-- The encoded `helicityDefect` equals the encoded `colorIndex` by the count
    identity in `ClusterMutationIndexBridge`, so the same trace has this
    numerical expression. No physical helicity is defined here. -/
theorem trace_krein_eq_neg_helicityDefect (Vwhite Vblack Eint next : ℕ)
    (hbal : (next : ℤ) = 3 * ((Vblack : ℤ) + (Vwhite : ℤ)) - 2 * (Eint : ℤ)) :
    Matrix.trace (kreinInvolution (R := ℤ) Vwhite Vblack) =
      - (stateSpaceCounts Vwhite Vblack Eint next hbal).helicityDefect := by
  rw [trace_krein_eq_neg_colorIndex]
  have h_eq := PlabicCounts.helicityDefect_eq_colorIndex (stateSpaceCounts Vwhite Vblack Eint next hbal)
  rw [h_eq]

end InfoGeometry.Canonical.BipartiteKreinTraceBridge
