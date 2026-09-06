import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Thermo.BuresWassersteinKMSCost

/-!
# Topological transport of positive states

The thermodynamic owner supplies the positive-state domain and the
domain-preserving KMS holonomy.  This file adds only the missing topological
interface: continuity on the positive-state subtype, its `TopCat` morphism,
and compactness transport.
-/

noncomputable section

namespace InfoGeometry.Topology.BuresWassersteinTransportTopCat

open InfoGeometry.Thermo.BuresWassersteinKMSCost

structure ContinuousKMSHolonomyTransport
    (State : Type*) [TopologicalSpace State]
    (Ω : PositiveStateDomain State)
    extends KMSHolonomyTransport State Ω where
  continuous_transport : Continuous transport

namespace ContinuousKMSHolonomyTransport

variable {State : Type*} [TopologicalSpace State]
variable {Ω : PositiveStateDomain State}
variable (H : ContinuousKMSHolonomyTransport State Ω)

theorem continuous_transported :
    Continuous H.transported := by
  exact (H.continuous_transport.comp continuous_subtype_val).subtype_mk
    (fun ρ : PositiveState Ω =>
      H.preserves_domain ρ.val ρ.property)

def toTopCatHom :
    TopCat.of (PositiveState Ω) ⟶ TopCat.of (PositiveState Ω) :=
  TopCat.ofHom
    { toFun := H.transported
      continuous_toFun := H.continuous_transported }

@[simp] theorem toTopCatHom_apply (ρ : PositiveState Ω) :
    H.toTopCatHom ρ = H.transported ρ :=
  rfl

theorem isCompact_transported_image
    {K : Set (PositiveState Ω)} (hK : IsCompact K) :
    IsCompact (H.transported '' K) :=
  hK.image H.continuous_transported

end ContinuousKMSHolonomyTransport

structure TopologicalBuresWassersteinTransport
    (State : Type*) [TopologicalSpace State]
    (Ω : PositiveStateDomain State) where
  metric : BuresWassersteinDatum State Ω
  holonomy : ContinuousKMSHolonomyTransport State Ω

namespace TopologicalBuresWassersteinTransport

variable {State : Type*} [TopologicalSpace State]
variable {Ω : PositiveStateDomain State}
variable (T : TopologicalBuresWassersteinTransport State Ω)

def transportTopCatHom :
    TopCat.of (PositiveState Ω) ⟶ TopCat.of (PositiveState Ω) :=
  T.holonomy.toTopCatHom

theorem transported_image_compact
    {K : Set (PositiveState Ω)} (hK : IsCompact K) :
    IsCompact (T.holonomy.transported '' K) :=
  T.holonomy.isCompact_transported_image hK

theorem holonomy_cost_nonnegative (ρ : PositiveState Ω) :
    0 ≤ holonomyCost T.metric T.holonomy.toKMSHolonomyTransport ρ :=
  holonomyCost_nonneg T.metric T.holonomy.toKMSHolonomyTransport ρ

theorem continuous_holonomy_cost
    (hcost : Continuous (fun p : PositiveState Ω × PositiveState Ω =>
      T.metric.squaredDist p.1 p.2)) :
    Continuous (fun ρ : PositiveState Ω =>
      holonomyCost T.metric T.holonomy.toKMSHolonomyTransport ρ) := by
  have hpair : Continuous (fun ρ : PositiveState Ω =>
      (ρ, T.holonomy.transported ρ)) :=
    continuous_id.prodMk T.holonomy.continuous_transported
  exact hcost.comp hpair

def transportComparisonCost
    (H₁ H₂ : ContinuousKMSHolonomyTransport State Ω)
    (ρ : PositiveState Ω) : ℝ :=
  T.metric.dist (H₁.transported ρ) (H₂.transported ρ)

theorem transportComparisonCost_nonnegative
    (H₁ H₂ : ContinuousKMSHolonomyTransport State Ω)
    (ρ : PositiveState Ω) :
    0 ≤ T.transportComparisonCost H₁ H₂ ρ :=
  T.metric.dist_nonneg (H₁.transported ρ) (H₂.transported ρ)

theorem continuous_transportComparisonCost
    (H₁ H₂ : ContinuousKMSHolonomyTransport State Ω)
    (hdist : Continuous (fun p : PositiveState Ω × PositiveState Ω =>
      T.metric.dist p.1 p.2)) :
    Continuous (T.transportComparisonCost H₁ H₂) := by
  have hpair : Continuous (fun ρ : PositiveState Ω =>
      (H₁.transported ρ, H₂.transported ρ)) :=
    H₁.continuous_transported.prodMk H₂.continuous_transported
  exact hdist.comp hpair

end TopologicalBuresWassersteinTransport

end InfoGeometry.Topology.BuresWassersteinTransportTopCat
