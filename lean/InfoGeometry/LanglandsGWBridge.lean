import Mathlib

/-!
# InfoGeometry.LanglandsGWBridge

Data-only gauge-reduction and Weyl-reduction carriers for the Langlands--GW
layer.

This module does not prove the Atiyah–Bott moment-map theorem or the full Weyl
integration formula. It exposes only raw data and definitional readback lemmas;
missing analytic/geometric closure remains outside this file rather than being
packaged as a theorem-like target.
-/

noncomputable section

namespace InfoGeometry

namespace LanglandsGWBridge

/--
Raw symplectic-quotient data for a gauge action.

The constrained locus is deliberately a namespace `def`, not a stored field plus
a proof field: membership is definitionally the equation
`momentumMap a = zeroMomentum`.
-/
structure SymplecticQuotientData (Space : Type) (GaugeGroup : Type)
    [instGroup : Group GaugeGroup] where
  /-- Abstract symplectic-geometry carrier on the configuration space. -/
  symplecticForm : Type*
  /-- Momentum-value type for the moment map. -/
  momentumValue : Type*
  /-- Momentum map `μ : Space → momentumValue`. -/
  momentumMap : Space → momentumValue
  /-- Distinguished zero element in the momentum-value type. -/
  zeroMomentum : momentumValue
  /-- Group action on the configuration space by the provided `Group` parameter. -/
  gaugeAction : GaugeGroup → Space → Space
  /-- Moduli object associated with the constrained carrier. -/
  moduliSpace : Type*
  /-- Map from constrained points into the quotient object. -/
  moduliProjection :
    {a : Space // momentumMap a = zeroMomentum} → moduliSpace

namespace SymplecticQuotientData

variable {Space GaugeGroup : Type} [Group GaugeGroup]

/-- The zero-momentum locus determined by the stored momentum map. -/
def zeroLocus (Q : SymplecticQuotientData Space GaugeGroup) : Set Space :=
  {a : Space | Q.momentumMap a = Q.zeroMomentum}

@[simp]
theorem mem_zeroLocus_iff (Q : SymplecticQuotientData Space GaugeGroup) (a : Space) :
    a ∈ Q.zeroLocus ↔ Q.momentumMap a = Q.zeroMomentum := by
  rfl

end SymplecticQuotientData

/--
Raw Weyl-reduction data for measure/integral descent from a group to a torus.

This stores only the maps and scalar shadows currently formalized here. It does
not assert a Weyl integration formula.
-/
structure WeylIntegrationData (GaugeGroup Torus : Type) where
  /-- Weyl group controlling residual symmetries. -/
  weylGroup : Type*
  /-- Positive root labels appearing in the Jacobian factor. -/
  positiveRoots : Type*
  /-- A root-valued weight used as a Jacobian ingredient. -/
  rootWeight : positiveRoots → ℝ
  /-- A distinguished torus reduction map from the original group. -/
  torusMap : GaugeGroup → Torus
  /-- Total root-weight product; a stored scalar shadow, not a formula theorem. -/
  rootMeasureProduct : ℝ := 0
  /-- Numerical shadow of the reduced volume/integral. -/
  volumeShadow : ℝ

namespace WeylIntegrationData

variable {GaugeGroup Torus : Type}

/-- Pull back a real-valued torus function along the stored torus map. -/
def pullback (W : WeylIntegrationData GaugeGroup Torus) (f : Torus → ℝ) (g : GaugeGroup) : ℝ :=
  f (W.torusMap g)

@[simp]
theorem pullback_apply (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) (g : GaugeGroup) :
    W.pullback f g = f (W.torusMap g) := by
  rfl

end WeylIntegrationData

/-- Combined raw data for Atiyah–Bott/Abelian-reduction style localization. -/
structure SymplecticWeylVolumeData (Space GaugeGroup Torus : Type)
    [instGroup : Group GaugeGroup] where
  /-- Symplectic quotient layer. -/
  quotient : SymplecticQuotientData Space GaugeGroup
  /-- Weyl torus-reduction layer. -/
  weyl : WeylIntegrationData GaugeGroup Torus

/-- Build the combined data from separate pieces. -/
def constructSymplecticWeylVolumeData
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    SymplecticWeylVolumeData.{0, 0, 0, 0, 0} Space GaugeGroup Torus :=
  ⟨Q, W⟩

@[simp]
theorem constructSymplecticWeylVolumeData_quotient
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).quotient = Q := by
  rfl

@[simp]
theorem constructSymplecticWeylVolumeData_weyl
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).weyl = W := by
  rfl

end LanglandsGWBridge

end InfoGeometry
