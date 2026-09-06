import InfoGeometry.Canonical.ModularSpinorGaugeTransport
import InfoGeometry.Canonical.SplitQuaternionGrassmannianSpinorBridge

namespace InfoGeometry.Canonical

open InfoGeometry.Topology.DiscreteHodgeDiracBridge
open InfoGeometry.Topology.DiscreteDiracHodgeChiral

noncomputable section

/-!
# Modular-spinor / Grassmannian boundary bridge

This file adds the next honest bridge node after
`ModularSpinorGaugeTransport`. The current repository already contains:

* discrete split-`G₂` transport on the seven-dimensional carrier, and
* Dirichlet-to-Neumann boundary data over a split-quaternion Grassmannian point.

What is still missing is any theorem identifying those two surfaces by analytic
construction. Accordingly, this file only packages their coexistence in one
owner and re-exports the native laws that already hold on each side.
-/

variable {E Sections BoundarySections : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]

/-- Joint owner for modular-spinor transport and Grassmannian DN boundary data. -/
structure ModularSpinorGrassmannianBoundaryBridge where
  connection : ModularSpinorGaugeConnection E
  boundaryData : SplitQuaternionSpinorDNData
    (Sections := Sections) (BoundarySections := BoundarySections)

/-- The underlying split-quaternion Grassmannian point on the boundary side. -/
abbrev grassmannianBase
    (B : ModularSpinorGrassmannianBoundaryBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)) :
    SplitQuaternionGrassmannian :=
  B.boundaryData.base

/-- The native trace-monogenic subspace carried by the boundary side. -/
abbrev boundaryTraceMonogenic
    (B : ModularSpinorGrassmannianBoundaryBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)) :
    Submodule ℝ BoundarySections :=
  traceMonogenic B.boundaryData

/-- The DN kernel theorem remains available on the boundary side of the bridge. -/
theorem boundary_kernel_eq_traceMonogenic
    (B : ModularSpinorGrassmannianBoundaryBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)) :
    LinearMap.ker B.boundaryData.dirichletToNeumann = boundaryTraceMonogenic B :=
  dirichletToNeumann_kernel_eq_traceMonogenic B.boundaryData

/-- Membership form of the boundary kernel theorem inside the bridge. -/
theorem mem_boundary_kernel_iff
    (B : ModularSpinorGrassmannianBoundaryBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections))
    (u : BoundarySections) :
    u ∈ LinearMap.ker B.boundaryData.dirichletToNeumann ↔
      u ∈ boundaryTraceMonogenic B := by
  exact mem_dirichletToNeumann_kernel_iff B.boundaryData u

/-- The modular-spinor transport side still preserves the canonical three-form. -/
theorem bridge_transport_preserves_threeForm
    (B : ModularSpinorGrassmannianBoundaryBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections))
    (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        (modularSpinorTransport B.connection path x)
        (modularSpinorTransport B.connection path y)
        (modularSpinorTransport B.connection path z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact modularSpinorTransport_preserves_threeForm B.connection path x y z

/-- Curvature on the modular-spinor side still preserves the canonical three-form. -/
theorem bridge_curvature_preserves_threeForm
    (B : ModularSpinorGrassmannianBoundaryBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections))
    (e₁ e₂ e₃ : E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        (modularSpinorCurvature B.connection e₁ e₂ e₃ x)
        (modularSpinorCurvature B.connection e₁ e₂ e₃ y)
        (modularSpinorCurvature B.connection e₁ e₂ e₃ z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact modularSpinorCurvature_preserves_threeForm B.connection e₁ e₂ e₃ x y z

end

end InfoGeometry.Canonical
