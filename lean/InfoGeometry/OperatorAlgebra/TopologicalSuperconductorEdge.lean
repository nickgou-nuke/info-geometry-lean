/-
InfoGeometry/OperatorAlgebra/TopologicalSuperconductorEdge.lean

Topological-superconductor edge witness.

This module separates ordinary Andreev electron/hole closure from the stronger
claim that a superconducting boundary hosts Majorana-type edge modes.

Andreev reflection supplies electron-like ↔ hole-like closure.
Edge/topological claims require explicit BdG, localization, and index data.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace TopologicalSuperconductorEdge

open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.OperatorAlgebra.ClosureInvolution

/-! ## 1. BdG edge-mode witness -/

/--
BdG edge-mode witness.

This is separate from ordinary Andreev reflection. It records the extra data
usually needed to call a boundary mode Majorana-like in a topological
superconductor setting:

* closure-fixed;
* zero-energy for a supplied BdG Hamiltonian;
* nonzero;
* localized at a boundary label;
* nonzero topological index/winding supplied by the model.

This module does not derive topological superconductivity from Andreev
reflection.
-/
structure BdGEdgeModeWitness
    (Boundary V : Type*)
    [AddCommGroup V] [Module ℝ V] where
  boundaryDatum :
    AndreevBoundaryDatum V

  /-- Real-linear BdG Hamiltonian/readout. -/
  H :
    V →ₗ[ℝ] V

  /-- Boundary mode/readout. -/
  edgeMode :
    V

  /-- The mode is nonzero. -/
  edgeMode_ne_zero :
    edgeMode ≠ 0

  /-- The mode is particle-hole fixed. -/
  edgeMode_fixed :
    edgeMode ∈ boundaryDatum.closure.Fixed

  /-- The mode is zero-energy. -/
  edgeMode_zero_energy :
    H edgeMode = 0

  /-- Boundary/core/edge label. -/
  boundaryLocation :
    Boundary

  /-- Model-specific localization predicate. -/
  LocalizedAt :
    Boundary → V → Prop

  /-- The mode is localized at the boundary/core/edge. -/
  edgeMode_localized :
    LocalizedAt boundaryLocation edgeMode

  /-- Integer topological invariant supplied by the concrete model. -/
  topologicalIndex :
    ℤ

  /-- Nonzero topological invariant. -/
  topologicalIndex_ne_zero :
    topologicalIndex ≠ 0

namespace BdGEdgeModeWitness

variable
    {Boundary V : Type*}
    [AddCommGroup V] [Module ℝ V]

variable (T : BdGEdgeModeWitness Boundary V)

/-- The edge mode is fixed by closure. -/
theorem theta_edgeMode_eq_edgeMode :
    T.boundaryDatum.closure.theta T.edgeMode = T.edgeMode :=
  T.boundaryDatum.closure.theta_eq_self_of_fixed T.edgeMode_fixed

/-- The edge mode is a zero-energy mode of the supplied BdG Hamiltonian. -/
theorem edgeMode_is_zero_energy :
    T.H T.edgeMode = 0 :=
  T.edgeMode_zero_energy

/-- The edge mode is localized at the supplied boundary/core/edge label. -/
theorem edgeMode_is_localized :
    T.LocalizedAt T.boundaryLocation T.edgeMode :=
  T.edgeMode_localized

/-- The topological invariant is nonzero. -/
theorem topologicalIndex_nonzero :
    T.topologicalIndex ≠ 0 :=
  T.topologicalIndex_ne_zero

/-- Package the three algebraic Majorana-edge conditions. -/
theorem edgeMode_majorana_edge_grammar :
    T.edgeMode ≠ 0 ∧
    T.boundaryDatum.closure.theta T.edgeMode = T.edgeMode ∧
    T.H T.edgeMode = 0 := by
  exact
    ⟨T.edgeMode_ne_zero,
      T.theta_edgeMode_eq_edgeMode,
      T.edgeMode_zero_energy⟩

/-- The Andreev diagonal is a closure-fixed boundary combination. -/
theorem andreev_diagonal_fixed :
    T.boundaryDatum.electron + T.boundaryDatum.hole ∈
      T.boundaryDatum.closure.Fixed :=
  T.boundaryDatum.electron_hole_diagonal_fixed

/-- The Andreev imbalance is anti-fixed. -/
theorem andreev_imbalance_anti_fixed :
    T.boundaryDatum.closure.theta
        (T.boundaryDatum.electron - T.boundaryDatum.hole)
      =
        -(T.boundaryDatum.electron - T.boundaryDatum.hole) :=
  T.boundaryDatum.electron_hole_imbalance_anti_fixed

end BdGEdgeModeWitness

end TopologicalSuperconductorEdge
