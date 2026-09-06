import Mathlib.Order.Filter.Basic
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
def CuspLimitData (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  {p : Filter X × (X → Y) × Y // Tendsto p.2.1 p.1 (𝓝 p.2.2)}

namespace CuspLimitData

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

abbrev cuspFilter (D : CuspLimitData X Y) : Filter X := D.1.1
abbrev cuspOrbit (D : CuspLimitData X Y) : X → Y := D.1.2.1
abbrev cuspValue (D : CuspLimitData X Y) : Y := D.1.2.2

theorem orbit_tendsto (D : CuspLimitData X Y) :
    Tendsto D.cuspOrbit D.cuspFilter (𝓝 D.cuspValue) :=
  D.2

/-- The cusp limit is recorded purely as a `Tendsto` fact. -/
alias tendsto_cuspOrbit := CuspLimitData.orbit_tendsto

/-- Compatibility alias for the cusp-limit contract. -/
alias cuspLimit_tendsto := CuspLimitData.orbit_tendsto

end CuspLimitData

end InfoGeometry.Topological
