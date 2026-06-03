import Mathlib

/-!
# InfoGeometry.LanglandsGWBridge

Carrier data for gauge-theoretic reduction in the Langlands--GW layer.

This module does not prove the Atiyah--Bott moment-map theorem or the full
Weyl integration formula. It also does not hide those facts in proof-carrying
data fields. The only closed facts here are the local definitional theorem-owner
readouts attached to the carrier data.
-/

noncomputable section

namespace InfoGeometry

namespace LanglandsGWBridge

/--
Symplectic quotient carrier data for a gauge action.

The fields are intentionally structural:

* `symplecticForm` is the symplectic-geometry carrier;
* `momentumMap` plays the role of a conserved/constraint-valued map `μ`;
* `zeroMomentum` marks the reduction locus `μ = 0`;
* `moduliSpace` is the reduced moduli object exported as carrier data.
* `gaugeAction` is the group action by the provided `Group` parameter.
--/
structure SymplecticQuotientData (Space : Type) (GaugeGroup : Type) [instGroup : Group GaugeGroup] where
  /-- Abstract symplectic-geometry data on the configuration space. -/
  symplecticForm : Type*
  /-- Optional momentum-value type for the moment map. -/
  momentumValue : Type*
  /-- Momentum map `μ : Space → momentumValue`. -/
  momentumMap : Space → momentumValue
  /-- Distinguished zero element in the momentum-value type. -/
  zeroMomentum : momentumValue
  /-- Group action on the configuration space by the provided `Group` parameter. -/
  gaugeAction : GaugeGroup → Space → Space
  /-- Moduli object obtained from the constrained quotient. -/
  moduliSpace : Type*
  /-- The moduli map from constrained points into the quotient object. -/
  moduliProjection : {a : Space // momentumMap a = zeroMomentum} → moduliSpace

/--
Fixed-point locus `μ⁻¹(0)` for the momentum map.
-/
def SymplecticQuotientData.zeroLocus
    {Space GaugeGroup : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData Space GaugeGroup) : Set Space :=
  {a : Space | Q.momentumMap a = Q.zeroMomentum}

/--
Closed local theorem: zero-locus membership is exactly the momentum-map equation.
-/
theorem SymplecticQuotientData.mem_zeroLocus_iff
    {Space GaugeGroup : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData Space GaugeGroup) (a : Space) :
    a ∈ Q.zeroLocus ↔ Q.momentumMap a = Q.zeroMomentum := by
  rfl

/--
Weyl-reduction carrier data for measure/integral descent from a group to a torus.

This structure stores the root data and a Jacobian-type root weight map that is
used as the reduction factor in Weyl-style formulas.
-/
structure WeylIntegrationData (GaugeGroup Torus : Type) where
  /-- Weyl group controlling residual symmetries. -/
  weylGroup : Type*
  /-- Positive root labels appearing in the Jacobian factor. -/
  positiveRoots : Type*
  /-- A root-valued weight used as a Jacobian ingredient (e.g. Vandermonde). -/
  rootWeight : positiveRoots → ℝ
  /-- A distinguished torus reduction map from the original group. -/
  torusMap : GaugeGroup → Torus
  /-- Total root-weight product; the structural shadow of the denominator factor. -/
  rootMeasureProduct : ℝ := 0
  /-- Numerical shadow of the reduced volume/integral. -/
  volumeShadow : ℝ

/--
Pullback along the torus map.
-/
def WeylIntegrationData.pullback
    {GaugeGroup Torus : Type} (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) : GaugeGroup → ℝ :=
  fun g => f (W.torusMap g)

/--
Closed local theorem: Weyl pullback evaluates by applying the function after
the torus reduction map.
-/
theorem WeylIntegrationData.pullback_apply
    {GaugeGroup Torus : Type} (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) (g : GaugeGroup) :
    W.pullback f g = f (W.torusMap g) := by
  rfl

/--
Combined carrier data for Atiyah--Bott/Abelian-reduction style localization.

The combined carrier is an owner-level shape: the moduli object is presented with
its momentum constraint and a Weyl-type torus reduction shadow.
-/
structure SymplecticWeylVolumeData (Space GaugeGroup Torus : Type) [instGroup : Group GaugeGroup] where
  /-- Symplectic quotient layer. -/
  quotient : SymplecticQuotientData Space GaugeGroup
  /-- Weyl torus-reduction layer. -/
  weyl : WeylIntegrationData GaugeGroup Torus

/--
Canonical assembly from separate symplectic-quotient and Weyl-reduction data.
-/
def constructSymplecticWeylVolumeData
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    SymplecticWeylVolumeData.{0, 0, 0, 0, 0} Space GaugeGroup Torus :=
  ⟨Q, W⟩

/--
Closed local theorem: the assembled carrier has the supplied quotient data.
-/
theorem constructSymplecticWeylVolumeData_quotient
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).quotient = Q := by
  rfl

/--
Closed local theorem: the assembled carrier has the supplied Weyl data.
-/
theorem constructSymplecticWeylVolumeData_weyl
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).weyl = W := by
  rfl

end LanglandsGWBridge

end InfoGeometry
