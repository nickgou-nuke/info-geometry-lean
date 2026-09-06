import Mathlib.Tactic
import InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
import InfoGeometry.Canonical.AmplituhedronThermodynamicProjection

/-!
# Finite amplituhedron boundary data

This module records finite boundary readouts for a positive-geometry chart.
It does not assert a canonical-form theorem, a residue theorem, or a global
integration identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.AmplituhedronIntegrationLimits

open InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
open InfoGeometry.Canonical.AmplituhedronThermodynamicProjection

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
## 1. Boundary facets

The fields below are finite readouts for a chosen boundary coordinate and a
chosen positive domain.
-/

/-- 
The explicit algebraic boundary facet of a finite chart.
-/
structure AmplituhedronBoundaryFacet (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  /-- The coordinate function selected as a boundary readout. -/
  boundary_coordinate : E → ℝ
  /-- The chosen domain carries nonnegative boundary readout. -/
  is_positive_domain : ∀ (X : E), boundary_coordinate X ≥ 0

/-!
## 2. Boundary readout carrier

The record below stores a finite readout attached to the chosen facet.
-/

/--
Boundary readout attached to the facet.
-/
structure BoundaryReadout (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : AmplituhedronBoundaryFacet E) where
  /-- The finite readout on the ambient space. -/
  amplitude_form : E → ℝ
  /-- The readout vanishes on the selected boundary facet. -/
  vanishes_on_boundary : ∀ (X : E), B.boundary_coordinate X = 0 → amplitude_form X = 0

/-!
## 3. Explicit integration window

The record below stores a finite window together with a boundary-vanishing
readout.  No global integration theorem is asserted here.
-/

/--
The finite boundary window attached to the chosen readout.
-/
structure PositiveBoundaryWindow (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : AmplituhedronBoundaryFacet E)
    (C : BoundaryReadout E B) where
  /-- The finite integrated quantity. -/
  integrated_volume : ℝ
  /-- The chosen window vanishes on the negative side of the boundary readout. -/
  respects_limits : ∀ (X : E), B.boundary_coordinate X < 0 → C.amplitude_form X = 0

end InfoGeometry.Canonical.AmplituhedronIntegrationLimits
