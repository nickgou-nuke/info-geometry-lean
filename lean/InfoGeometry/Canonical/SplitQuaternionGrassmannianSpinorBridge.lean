import InfoGeometry.Canonical.SplitOctonionQuaternionGrassmannian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.DiscreteHodgeDiracBridge

/-!
# Spinor boundary data over the split-quaternion Grassmannian

The existing Grassmannian owner is algebraic and rational, while the
Dirichlet-to-Neumann theorem requires separate spaces of sections, boundary
sections, a trace map, and a boundary operator.  This file records exactly
that missing linear data.  It does not identify the Grassmannian with a
manifold, construct a boundary, or assert a Gelfand-spectrum or sheaf theorem.

The kernel equation is stored as data because it is the analytic content of a
Dirichlet-to-Neumann theorem; it cannot be derived from the finite octonion
multiplication or from the discrete monogenic kernel alone.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Topology.DiscreteHodgeDiracBridge
open InfoGeometry.Topology.DiscreteDiracHodgeChiral

noncomputable section

variable {Sections BoundarySections : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]

/-- Linear data for a spinor Dirichlet-to-Neumann problem over one
split-quaternion Grassmannian point. -/
structure SplitQuaternionSpinorDNData where
  base : SplitQuaternionGrassmannian
  monogenic : Submodule ℝ Sections
  trace : Sections →ₗ[ℝ] BoundarySections
  dirichletToNeumann : BoundarySections →ₗ[ℝ] BoundarySections
  kernel_eq_trace_monogenic :
    LinearMap.ker dirichletToNeumann = monogenic.map trace

/-- The trace space of monogenic sections. -/
abbrev traceMonogenic
    (D : SplitQuaternionSpinorDNData (Sections := Sections)
      (BoundarySections := BoundarySections)) :
    Submodule ℝ BoundarySections :=
  D.monogenic.map D.trace

/-- The native kernel readout of the DN data. -/
theorem dirichletToNeumann_kernel_eq_traceMonogenic
    (D : SplitQuaternionSpinorDNData (Sections := Sections)
      (BoundarySections := BoundarySections)) :
    LinearMap.ker D.dirichletToNeumann = traceMonogenic D :=
  D.kernel_eq_trace_monogenic

/-- Membership form of the DN kernel theorem. -/
theorem mem_dirichletToNeumann_kernel_iff
    (D : SplitQuaternionSpinorDNData (Sections := Sections)
      (BoundarySections := BoundarySections))
    (u : BoundarySections) :
    u ∈ LinearMap.ker D.dirichletToNeumann ↔ u ∈ traceMonogenic D := by
  rw [dirichletToNeumann_kernel_eq_traceMonogenic D]

/-- The finite discrete monogenic carrier already owned by the Hodge bridge. -/
abbrev discreteMonogenicCarrier (d δ : EndCochain n) :
    Submodule ℝ (Cochains n) :=
  MonogenicFields d δ

end

end InfoGeometry.Canonical
