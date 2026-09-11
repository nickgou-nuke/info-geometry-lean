import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathImageTransport
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Topology

/-!
# Paths through the observational quotient

The observational quotient is the canonical latent carrier for a finite
family of observables.  This file transports a continuous latent path through
the quotient map and records the readout square pointwise.  No claim about a
homotopy quotient or injectivity of the path map is made here.
-/

def symbolicObservationQuotientProjection
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    X → _root_.Quotient (symbolicObservationalSetoid S) :=
  _root_.Quotient.mk (symbolicObservationalSetoid S)

theorem continuous_symbolicObservationQuotientProjection
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Continuous (symbolicObservationQuotientProjection S) := by
  exact continuous_quot_mk

def symbolicObservationQuotientPath
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPath (_root_.Quotient (symbolicObservationalSetoid S)) :=
  mapSymbolicLatentPathContinuous
    (symbolicObservationQuotientProjection S)
    (continuous_symbolicObservationQuotientProjection S) γ

@[simp] theorem symbolicObservationQuotientPath_apply
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    symbolicObservationQuotientPath S γ t =
      symbolicObservationQuotientProjection S (γ t) :=
  rfl

theorem symbolicObservationQuotientPath_readout
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    symbolicObservationQuotientMap S
        (symbolicObservationQuotientPath S γ t) =
      symbolicObservationPath S γ t := by
  change symbolicObservationQuotientMap S
      (symbolicObservationQuotientProjection S (γ t)) = _
  rfl

theorem symbolicObservationQuotientPath_image_eq_projection_image
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathImage (symbolicObservationQuotientPath S γ) =
      symbolicObservationQuotientProjection S ''
        symbolicLatentPathImage γ := by
  exact symbolicLatentPathImage_map_eq_image
    (symbolicObservationQuotientProjection S)
    (continuous_symbolicObservationQuotientProjection S) γ

theorem isCompact_symbolicObservationQuotientPath_image
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    IsCompact (symbolicLatentPathImage
      (symbolicObservationQuotientPath S γ)) := by
  exact isCompact_symbolicLatentPathImage
    (symbolicObservationQuotientPath S γ)

theorem symbolicObservationQuotientPath_readout_image_eq_observed_image
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    symbolicObservationQuotientMap S ''
        symbolicLatentPathImage (symbolicObservationQuotientPath S γ) =
      observedSymbolicLatentPathImage S γ := by
  ext y
  constructor
  · rintro ⟨q, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, symbolicObservationQuotientPath_readout S γ t⟩
  · rintro ⟨t, rfl⟩
    exact ⟨symbolicObservationQuotientPath S γ t, ⟨t, rfl⟩,
      symbolicObservationQuotientPath_readout S γ t⟩

end InfoGeometry.Topology
