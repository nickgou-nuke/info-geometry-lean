import InfoGeometry.Nuclear.DetectorTransportKernel

/-!
# Detector response as an actual three-dimensional Bochner integral

The acceptance κ(p) is the probability of the selected recorded outcome,
conditional on the first collision at p (and the incident energy/direction).
For a full-energy peak, κ must include subsequent transport, secondary escape,
and collection. It is not defined to be one or inferred from geometry.
External transmission may be included multiplicatively in κ.

Continuity is a sufficient regularity hypothesis used here to PROVE
integrability on the compact cylinder. No inverse-power response law is assumed.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DetectorVolumeResponse

open Set MeasureTheory
open InfoGeometry.Nuclear.DetectorTransportKernel

/-- Recorded probability per emitted photon, in native Cartesian volume. -/
def response (μ d R L : ℝ) (κ : Point → ℝ) : ℝ :=
  ∫ p in cylinder R L, firstCollisionKernel μ d p * κ p

/-- All first interactions are accepted. This is not a full-energy efficiency. -/
def totalInteractionResponse (μ d R L : ℝ) : ℝ :=
  response μ d R L (fun _ => 1)

theorem integrableOn_response (μ d R L : ℝ) (hd : 0 < d) (hR : 0 ≤ R)
    {κ : Point → ℝ} (hκ : ContinuousOn κ (cylinder R L)) :
    IntegrableOn (fun p => firstCollisionKernel μ d p * κ p) (cylinder R L) := by
  exact ContinuousOn.integrableOn_compact (isCompact_cylinder R L hR)
    ((continuousOn_firstCollisionKernel R L μ d hd).mul hκ)

/-- Fubini reduction to a transverse-disk integral and a depth integral.
The integrability premise is discharged by the preceding theorem. -/
theorem response_eq_disk_depth (μ d R L : ℝ) (hd : 0 < d) (hR : 0 ≤ R)
    {κ : Point → ℝ} (hκ : ContinuousOn κ (cylinder R L)) :
    response μ d R L κ =
      ∫ q in transverseDisk R, ∫ z in Icc (0 : ℝ) L,
        firstCollisionKernel μ d (q, z) * κ (q, z) := by
  exact MeasureTheory.setIntegral_prod _ (integrableOn_response μ d R L hd hR hκ)

theorem response_nonneg (μ d R L : ℝ) (hμ : 0 ≤ μ) (hd : 0 < d)
    {κ : Point → ℝ} (hκ : ∀ p ∈ cylinder R L, 0 ≤ κ p) :
    0 ≤ response μ d R L κ := by
  apply setIntegral_nonneg (measurableSet_cylinder R L)
  intro p hp
  exact mul_nonneg (firstCollisionKernel_nonneg hμ hd hp.2.1) (hκ p hp)

theorem response_mono (μ d R L : ℝ) (hμ : 0 ≤ μ) (hd : 0 < d) (hR : 0 ≤ R)
    {κ η : Point → ℝ} (hκ : ContinuousOn κ (cylinder R L))
    (hη : ContinuousOn η (cylinder R L))
    (hκη : ∀ p ∈ cylinder R L, κ p ≤ η p) :
    response μ d R L κ ≤ response μ d R L η := by
  apply setIntegral_mono_on (integrableOn_response μ d R L hd hR hκ)
    (integrableOn_response μ d R L hd hR hη) (measurableSet_cylinder R L)
  intro p hp
  exact mul_le_mul_of_nonneg_left (hκη p hp) (firstCollisionKernel_nonneg hμ hd hp.2.1)

theorem response_le_totalInteraction (μ d R L : ℝ)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hR : 0 ≤ R)
    {κ : Point → ℝ} (hκ : ContinuousOn κ (cylinder R L))
    (hκ1 : ∀ p ∈ cylinder R L, κ p ≤ 1) :
    response μ d R L κ ≤ totalInteractionResponse μ d R L := by
  exact response_mono μ d R L hμ hd hR hκ continuousOn_const hκ1

@[simp] theorem response_zero_acceptance (μ d R L : ℝ) :
    response μ d R L (fun _ => 0) = 0 := by
  simp [response]

@[simp] theorem response_zero_attenuation (d R L : ℝ) (κ : Point → ℝ) :
    response 0 d R L κ = 0 := by
  simp [response, firstCollisionKernel]

/-- Source-strength and branching normalization can be moved outside the
integral, but they are not silently identified with an aperture area. -/
theorem response_const_mul (μ d R L c : ℝ) (κ : Point → ℝ) :
    response μ d R L (fun p => c * κ p) = c * response μ d R L κ := by
  unfold response
  calc
    (∫ p in cylinder R L, firstCollisionKernel μ d p * (c * κ p)) =
        ∫ p in cylinder R L, c * (firstCollisionKernel μ d p * κ p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by ring)
    _ = c * ∫ p in cylinder R L, firstCollisionKernel μ d p * κ p :=
      integral_const_mul _ _

theorem response_add (μ d R L : ℝ) (hd : 0 < d) (hR : 0 ≤ R)
    {κ η : Point → ℝ} (hκ : ContinuousOn κ (cylinder R L))
    (hη : ContinuousOn η (cylinder R L)) :
    response μ d R L (fun p => κ p + η p) =
      response μ d R L κ + response μ d R L η := by
  unfold response
  simp_rw [mul_add]
  exact integral_add (integrableOn_response μ d R L hd hR hκ)
    (integrableOn_response μ d R L hd hR hη)

/-- Conservative finite domination by a constant integral. The sharp
solid-angle probability bound requires an additional ray-coordinate theorem. -/
theorem response_le_front_bound (μ d R L : ℝ)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hR : 0 ≤ R)
    {κ : Point → ℝ} (hκ : ContinuousOn κ (cylinder R L))
    (hκ1 : ∀ p ∈ cylinder R L, κ p ≤ 1) :
    response μ d R L κ ≤
      ∫ _p in cylinder R L, μ / (4 * Real.pi * d ^ 2) := by
  apply setIntegral_mono_on (integrableOn_response μ d R L hd hR hκ)
    (ContinuousOn.integrableOn_compact (isCompact_cylinder R L hR) continuousOn_const)
    (measurableSet_cylinder R L)
  intro p hp
  calc
    firstCollisionKernel μ d p * κ p ≤ firstCollisionKernel μ d p :=
      mul_le_of_le_one_right (firstCollisionKernel_nonneg hμ hd hp.2.1) (hκ1 p hp)
    _ ≤ μ / (4 * Real.pi * d ^ 2) := firstCollisionKernel_le_front hμ hd hp.2.1

/-- A source activity A, photon emission probability b, and acquisition time t
enter as explicit multiplicative normalizations of the volume response. -/
def expectedCounts (A b t μ d R L : ℝ) (κ : Point → ℝ) : ℝ :=
  response μ d R L (fun p => (A * b * t) * κ p)

theorem expectedCounts_eq (A b t μ d R L : ℝ) (κ : Point → ℝ) :
    expectedCounts A b t μ d R L κ = A * b * t * response μ d R L κ :=
  response_const_mul μ d R L (A * b * t) κ

/-- Product response for an explicitly independent two-photon model.
Correlated cascade transport is not inferred from this definition. -/
def independentCoincidence (A branching μ₁ μ₂ d R L : ℝ)
    (κ₁ κ₂ : Point → ℝ) : ℝ :=
  A * branching * response μ₁ d R L κ₁ * response μ₂ d R L κ₂

end InfoGeometry.Nuclear.DetectorVolumeResponse
