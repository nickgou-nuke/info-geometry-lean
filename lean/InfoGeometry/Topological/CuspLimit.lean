import Mathlib.Order.Filter.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic

namespace InfoGeometry.Topological

open Filter
open scoped Topology

/--
Filter-based cusp asymptotics.

This file is intentionally chart-free:
- no coordinate model of the cusp is assumed;
- no upper-half-plane point is singled out as `i∞`;
- cusp behavior is recorded only as a `Tendsto` fact.
-/
structure CuspLimitData (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  cuspFilter : Filter X
  cuspOrbit : X → Y
  cuspValue : Y
  orbit_tendsto : Tendsto cuspOrbit cuspFilter (𝓝 cuspValue)

namespace CuspLimitData

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The cusp limit is recorded purely as a `Tendsto` fact. -/
theorem tendsto_cuspOrbit (D : CuspLimitData X Y) :
    Tendsto D.cuspOrbit D.cuspFilter (𝓝 D.cuspValue) :=
  D.orbit_tendsto

/-- Compatibility alias for the cusp-limit contract. -/
theorem cuspLimit_tendsto (D : CuspLimitData X Y) :
    Tendsto D.cuspOrbit D.cuspFilter (𝓝 D.cuspValue) :=
  D.orbit_tendsto

end CuspLimitData

end InfoGeometry.Topological
