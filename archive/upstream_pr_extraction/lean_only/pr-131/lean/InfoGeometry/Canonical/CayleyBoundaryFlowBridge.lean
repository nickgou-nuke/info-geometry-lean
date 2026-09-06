import InfoGeometry.Canonical.CayleyBoundaryIntertwiningOnDomain
import InfoGeometry.Canonical.CayleyBoundaryContinuity
import InfoGeometry.Canonical.ModularBoundaryFlowIntertwiner

namespace InfoGeometry.Canonical.CayleyBoundaryFlowBridge

open InfoGeometry.Topology

/-!
# Narrow bridge for the Cayley boundary flow

This file does not introduce any new carrier or boundary model.
It only re-exports the native continuity and intertwining facts already owned by
`CayleyBoundaryTopological`, `CayleyBoundaryContinuity`, and
`CayleyBoundaryIntertwiningOnDomain`.
-/

theorem continuous_cayleyBoundary :
    Continuous cayleyBoundary :=
  _root_.InfoGeometry.Canonical.continuous_cayleyBoundary

theorem continuous_diskBoundaryBoost (s : ℝ) :
    ContinuousOn (diskBoundaryBoost s) (diskBoundaryBoostDomain s) :=
  _root_.InfoGeometry.Canonical.continuousOn_diskBoundaryBoost s

theorem cayley_boundary_intertwining_on_domain (s : ℝ) :
    Set.EqOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) :=
  _root_.InfoGeometry.Canonical.cayley_modular_boundary_intertwining_eqOn s

theorem cayley_boundary_flow_bridge (s : ℝ) :
    ContinuousOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (cayleyIntertwiningDomain s) ∧
    ContinuousOn
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) ∧
    Set.EqOn
      (fun x : ℝ => cayleyBoundary (Real.exp (2 * s) * x))
      (fun x : ℝ => diskBoundaryBoost s (cayleyBoundary x))
      (cayleyIntertwiningDomain s) := by
  exact _root_.InfoGeometry.Canonical.continuous_cayley_modular_boundary_intertwiner s

end InfoGeometry.Canonical.CayleyBoundaryFlowBridge
