import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.ClusterMutationIndexBridge

open Matrix

namespace InfoGeometry.Canonical.BipartiteKreinTraceBridge

open PlabicAmplituhedron

/-!
# Finite Grading Trace and Encoded Bipartite Counts

This module proves a finite-dimensional trace identity for a diagonal
involution with `Vwhite` positive and `Vblack` negative coordinates. It then
encodes those same counts as a `PlabicCounts` value and rewrites the trace as
the negative of its algebraically defined `helicityDefect`.

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

/-- Plabic count fields filled from natural counts. This encoding does not
construct a graph or a map from an eigenspace to a graph. -/
def stateSpaceCounts (Vwhite Vblack Eint : ℕ) : PlabicCounts where
  V_black := (Vblack : ℤ)
  V_white := (Vwhite : ℤ)
  E_internal := (Eint : ℤ)

/-- The diagonal grading trace is the negative of the count structure's
algebraically defined `helicityDefect`. -/
theorem trace_krein_eq_neg_helicityDefect (Vwhite Vblack Eint : ℕ) :
  Matrix.trace (kreinInvolution (R := ℤ) Vwhite Vblack) =
      - PlabicAmplituhedron.helicityDefect (stateSpaceCounts Vwhite Vblack Eint) := by
  rw [trace_kreinInvolution]
  dsimp [stateSpaceCounts, PlabicAmplituhedron.helicityDefect]
  ring

end InfoGeometry.Canonical.BipartiteKreinTraceBridge
