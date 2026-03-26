import InfoGeometry.Canonical.PerelmanWSpinorial
import InfoGeometry.Canonical.GrandCanonicalExperts
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.SpectralInference

section MongeAmpereRicci

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Constant Monge-Ampere density scaffold:
there exists a global scalar density value `ρ₀`.
-/
def HasConstantMongeAmpereDensity (H : HessianGeometry E) : Prop :=
  ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0

/--
Unit relative-volume state in RN/Monge-Ampère form.
This is the normalized-volume branch `ρ ≡ 1`.
-/
def UnitRelativeVolumeState (K : KaehlerInformationGeometry E) : Prop :=
  SatisfiesMongeAmpere K.H (fun _ => (1 : ℝ))

/-- Ricci-flatness condition in this finite-dimensional scaffold. -/
def IsRicciFlat (R : RicciTensor E) : Prop :=
  ∀ u v : E, R u v = 0

/--
Constructive closure state for the Monge-Ampere-to-Ricci layer:
constant Monge-Ampere density together with an explicit Ricci-flat witness.
-/
def MongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) : Prop :=
  HasConstantMongeAmpereDensity K.H ∧ IsRicciFlat R

/-- Lemma `hasConstantMongeAmpereDensity_iff`. -/
private lemma hasConstantMongeAmpereDensity_iff
    (H : HessianGeometry E) :
    HasConstantMongeAmpereDensity H
      ↔ ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0 := Iff.rfl

/-- Lemma `hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const`. -/
private lemma hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const
    (H : HessianGeometry E) (ρ0 : ℝ)
    (hMA : SatisfiesMongeAmpere H (fun _ => ρ0)) :
    HasConstantMongeAmpereDensity H := by
  exact ⟨ρ0, hMA⟩

/-- Lemma `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity`. -/
private lemma satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity
    (H : HessianGeometry E)
    (hConst : HasConstantMongeAmpereDensity H) :
    ∃ ρ0 : ℝ, SatisfiesMongeAmpere H (fun _ => ρ0) := by
  obtain ⟨ρ0, hρ0⟩ := hConst
  refine ⟨ρ0, ?_⟩
  intro x
  exact hρ0 x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Lemma `ricciTensor_eq_of_isRicciFlat`. -/
private lemma ricciTensor_eq_of_isRicciFlat
    {R₁ R₂ : RicciTensor E}
    (h₁ : IsRicciFlat R₁) (h₂ : IsRicciFlat R₂) :
    R₁ = R₂ := by
  funext u v
  rw [h₁ u v, h₂ u v]

/-- Lemma `isEinsteinKaehlerAtWith_zero_of_isRicciFlat`. -/
private lemma isEinsteinKaehlerAtWith_zero_of_isRicciFlat
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hFlat : IsRicciFlat R) :
    IsEinsteinKaehlerAtWith 0 R K x := by
  intro u v
  rw [hFlat u v]
  ring

/--
Metric-side reverse bridge on the zero branch:
`Ric = 0 · g` implies Ricci-flatness.
-/
private lemma isRicciFlat_of_isEinsteinKaehlerAtWith_zero
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hEin0 : IsEinsteinKaehlerAtWith 0 R K x) :
    IsRicciFlat R := by
  intro u v
  simpa using hEin0 u v

/--
Bridge package from unit RN-relative-volume state to the Einstein zero branch.

This isolates the geometric/model-specific implication
`ρ ≡ 1  ⇒  Ric = 0 · g` as explicit data rather than assuming Ricci-flatness.
-/
structure MetricRNRicciBridge
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) : Prop where
  unitVolume_to_einstein_zero :
    UnitRelativeVolumeState K → IsEinsteinKaehlerAtWith 0 R K x

/--
Metric-derived RN bridge:
`R` is explicitly identified with the metric-derived Ricci tensor, and unit
relative volume forces that metric-derived tensor to vanish.
-/
structure MetricDerivedRNRicciBridge
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) : Prop where
  ricci_eq_metricDerived :
    R = ricciFromMetricOp K.H x
  metricOpNondegenerate :
    MetricOpNondegenerate K.H
  metricLogDetTwiceDifferentiable :
    MetricLogDetTwiceDifferentiable K.H
  unitVolume_metricDerived_zero :
    UnitRelativeVolumeState K → ∀ u v : E, ricciFromMetricOp K.H x u v = 0

/-- Unit relative volume forces the metric log-determinant to vanish pointwise. -/
lemma metricLogDet_eq_zero_of_unitRelativeVolume
    (K : KaehlerInformationGeometry E)
    (hUnit : UnitRelativeVolumeState K)
    (hdet : MetricOpNondegenerate K.H) :
    ∀ x : E, metricLogDet K.H x = 0 := by
  intro x
  have hMA : mongeAmpereDensity K.H x = 1 := hUnit x
  have hExp : Real.exp (metricLogDet K.H x) = 1 := by
    unfold metricLogDet
    rw [Real.exp_log (abs_pos.mpr (hdet x))]
    simpa [mongeAmpereDensity] using hMA
  have habs_pos :
      0 < |LinearMap.det (K.H.metricOp x).toLinearMap| := by
    exact abs_pos.mpr (hdet x)
  have habs_eq_one :
      |LinearMap.det (K.H.metricOp x).toLinearMap| = 1 := by
    unfold metricLogDet at hExp
    rw [Real.exp_log habs_pos] at hExp
    exact hExp
  unfold metricLogDet
  rw [habs_eq_one, Real.log_one]

/-- The first derivative of the metric log-determinant vanishes on the unit-volume branch. -/
lemma fderiv_metricLogDet_eq_zero_of_unitRelativeVolume
    (K : KaehlerInformationGeometry E)
    (hUnit : UnitRelativeVolumeState K)
    (hdet : MetricOpNondegenerate K.H)
    (hDiff : MetricLogDetTwiceDifferentiable K.H) :
    ∀ x : E, fderiv ℝ (metricLogDet K.H) x = 0 := by
  intro x
  have hconst : metricLogDet K.H = fun _ : E => (0 : ℝ) := by
    funext y
    exact metricLogDet_eq_zero_of_unitRelativeVolume (K := K) hUnit hdet y
  have hconst0 : ∀ y : E, metricLogDet K.H y = 0 := by
    intro y
    exact congrFun hconst y
  have hDiffAt : DifferentiableAt ℝ (metricLogDet K.H) x :=
    (metricLogDet_differentiable (H := K.H) hDiff).differentiableAt
  have hHas :
      HasFDerivAt (metricLogDet K.H) (fderiv ℝ (metricLogDet K.H) x) x :=
    hDiffAt.hasFDerivAt
  have hEventually : (fun _ : E => (0 : ℝ)) =ᶠ[nhds x] metricLogDet K.H := by
    filter_upwards with y
    exact (hconst0 y).symm
  have hZeroHas :
      HasFDerivAt (fun _ : E => (0 : ℝ)) (fderiv ℝ (metricLogDet K.H) x) x :=
    hHas.congr_of_eventuallyEq hEventually
  have hConstHas :
      HasFDerivAt (fun _ : E => (0 : ℝ)) (0 : E →L[ℝ] ℝ) x :=
    by simpa using (hasFDerivAt_const (x := x) (c := (0 : ℝ)))
  exact hZeroHas.unique hConstHas

/-- The metric-derived Ricci tensor vanishes once the log-determinant chain collapses. -/
lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume
    (K : KaehlerInformationGeometry E) (x : E)
    (hUnit : UnitRelativeVolumeState K)
    (hdet : MetricOpNondegenerate K.H)
    (hDiff : MetricLogDetTwiceDifferentiable K.H) :
    ∀ u v : E, ricciFromMetricOp K.H x u v = 0 := by
  intro u v
  have hfdZero :
      ∀ y : E, fderiv ℝ (metricLogDet K.H) y = 0 :=
    fderiv_metricLogDet_eq_zero_of_unitRelativeVolume
      (K := K) hUnit hdet hDiff
  have hInnerDiffAt :
      DifferentiableAt ℝ (fun y => fderiv ℝ (metricLogDet K.H) y u) x :=
    metricLogDet_fderiv_apply_differentiableAt (H := K.H) hDiff u x
  have hInnerHas :
      HasFDerivAt
        (fun y => fderiv ℝ (metricLogDet K.H) y u)
        (fderiv ℝ (fun y => fderiv ℝ (metricLogDet K.H) y u) x)
        x :=
    hInnerDiffAt.hasFDerivAt
  have hInnerEventually :
      (fun _ : E => (0 : ℝ)) =ᶠ[nhds x] fun y => fderiv ℝ (metricLogDet K.H) y u := by
    filter_upwards with y
    have hy : fderiv ℝ (metricLogDet K.H) y = 0 := hfdZero y
    exact (congrArg (fun L : E →L[ℝ] ℝ => L u) hy).symm
  have hInnerZeroHas :
      HasFDerivAt
        (fun _ : E => (0 : ℝ))
        (fderiv ℝ (fun y => fderiv ℝ (metricLogDet K.H) y u) x)
        x :=
    hInnerHas.congr_of_eventuallyEq hInnerEventually
  have hConstHas :
      HasFDerivAt (fun _ : E => (0 : ℝ)) (0 : E →L[ℝ] ℝ) x :=
    by simpa using (hasFDerivAt_const (x := x) (c := (0 : ℝ)))
  have hSecondZero :
      fderiv ℝ (fun y => fderiv ℝ (metricLogDet K.H) y u) x = 0 :=
    hInnerZeroHas.unique hConstHas
  unfold ricciFromMetricOp
  rw [hSecondZero]
  simp

/--
Constructive instantiation of the metric-derived bridge via true
differential log-det calculus. This leverages the formal definition
of Ricci as the log-det Hessian, proving it vanishes when volume is constant.
-/
lemma MetricDerivedRNRicciBridge.ofUnitRelativeVolume_fderiv
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hEq : R = ricciFromMetricOp K.H x)
    (hDiff : MetricLogDetTwiceDifferentiable K.H)
    (hdet : MetricOpNondegenerate K.H) :
    MetricDerivedRNRicciBridge R K x where
  ricci_eq_metricDerived := hEq
  metricOpNondegenerate := hdet
  metricLogDetTwiceDifferentiable := hDiff
  unitVolume_metricDerived_zero := by
    intro hUnit
    exact ricciFromMetricOp_eq_zero_of_unitRelativeVolume
      (K := K) (x := x) hUnit hdet hDiff

/--
Every metric-derived RN bridge induces the abstract metric-to-Ricci bridge.
-/
private theorem metricRNRicciBridge_of_metricDerived
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hM : MetricDerivedRNRicciBridge R K x) :
    MetricRNRicciBridge R K x := by
  refine ⟨?_⟩
  intro hUnit u v
  calc
    R u v = ricciFromMetricOp K.H x u v := by
      simpa [hM.ricci_eq_metricDerived]
    _ = 0 := hM.unitVolume_metricDerived_zero hUnit u v
    _ = (0 : ℝ) * K.H.metric x u v := by ring

/--
Constructive Ricci-flat derivation from unit relative volume via the
metric-derived RN bridge.
-/
theorem isRicciFlat_of_unitRelativeVolume_metricDerived
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hUnit : UnitRelativeVolumeState K)
    (hM : MetricDerivedRNRicciBridge R K x) :
    IsRicciFlat R := by
  intro u v
  have hRicciEq : R u v = ricciFromMetricOp K.H x u v := by
    have := congrFun (congrFun hM.ricci_eq_metricDerived u) v
    simpa using this
  calc
    R u v = ricciFromMetricOp K.H x u v := hRicciEq
    _ = 0 := hM.unitVolume_metricDerived_zero hUnit u v

/--
Constructive vacuum Einstein closure from unit relative volume via the
metric-derived RN bridge.
-/
  theorem vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hUnit : UnitRelativeVolumeState K)
    (hM : MetricDerivedRNRicciBridge R K x) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  intro u v
  unfold einsteinTensorAt
  rw [isRicciFlat_of_unitRelativeVolume_metricDerived
    (R := R) (K := K) (x := x) hUnit hM u v]
  ring

/--
AdS-like Einstein branch: negative Einstein multiple with positive scale.
-/
def IsAdSLikeEinsteinAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) : Prop :=
  ∃ Λ : ℝ, 0 < Λ ∧ IsEinsteinKaehlerAtWith (-Λ) R K x

/--
Any Einstein-Kähler branch with negative coefficient is AdS-like.
-/
private theorem isAdSLikeEinsteinAt_of_negative_einstein
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (c : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R K x)
    (hc : c < 0) :
    IsAdSLikeEinsteinAt R K x := by
  refine ⟨-c, by linarith, ?_⟩
  intro u v
  calc
    R u v = c * K.H.metric x u v := hEin u v
    _ = (-(-c)) * K.H.metric x u v := by ring

/--
AdS-like Einstein branch yields a vacuum Einstein equation with zero scalar
closure in this normalization.
-/
private theorem vacuumEinsteinEquation_zeroScalar_of_isAdSLikeEinsteinAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hAdS : IsAdSLikeEinsteinAt R K x) :
    ∃ Λ : ℝ, 0 < Λ ∧ VacuumEinsteinEquationAt R K x 0 Λ := by
  rcases hAdS with ⟨Λ, hΛpos, hEin⟩
  refine ⟨Λ, hΛpos, ?_⟩
  exact vacuumEinsteinEquation_of_scalar_relation
    (c := -Λ) (R := R) (K := K) (x := x) (scalar := 0) (Λ := Λ)
    hEin (by ring)

/-- Projection: a `MongeAmpereRicciState` carries the constant-density witness. -/
private theorem hasConstantMongeAmpereDensity_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState : MongeAmpereRicciState R K) :
    HasConstantMongeAmpereDensity K.H :=
  hState.1

/-- Projection: a `MongeAmpereRicciState` carries Ricci-flatness. -/
private theorem isRicciFlat_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState : MongeAmpereRicciState R K) :
    IsRicciFlat R :=
  hState.2

/--
Constructive state packaging:
constant Monge-Ampere density and explicit Ricci-flatness form the closure state.
-/
private theorem mongeAmpereRicciState_mk
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hConst : HasConstantMongeAmpereDensity K.H)
    (hFlat : IsRicciFlat R) :
    MongeAmpereRicciState R K := by
  exact ⟨hConst, hFlat⟩

/--
Uniqueness under constructive closure states:
if two Ricci tensors are both Ricci-flat under the same geometry scaffold, they coincide.
-/
private theorem ricciTensor_unique_of_mongeAmpereRicciState
    (R₁ R₂ : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState₁ : MongeAmpereRicciState R₁ K)
    (hState₂ : MongeAmpereRicciState R₂ K) :
    R₁ = R₂ := by
  funext u v
  rw [hState₁.2 u v, hState₂.2 u v]

/--
Constructive vacuum Einstein closure from an explicit Ricci-flat witness
(non-bridge form).
-/
private theorem vacuumEinsteinEquation_of_isRicciFlat
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hFlat : IsRicciFlat R) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  have hEin0 : IsEinsteinKaehlerAtWith 0 R K x :=
    isEinsteinKaehlerAtWith_zero_of_isRicciFlat (R := R) (K := K) (x := x) hFlat
  exact vacuumEinsteinEquation_of_scalar_relation
    (c := 0) (R := R) (K := K) (x := x) (scalar := 2 * Λ) (Λ := Λ)
    hEin0 (by ring)

/--
Constructive Ricci-flat derivation from unit relative-volume state via the
metric RN bridge.
-/
theorem isRicciFlat_of_unitRelativeVolume
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hUnit : UnitRelativeVolumeState K)
    (hBridge : MetricRNRicciBridge R K x) :
    IsRicciFlat R := by
  intro u v
  calc
    R u v = (0 : ℝ) * K.H.metric x u v := hBridge.unitVolume_to_einstein_zero hUnit u v
    _ = 0 := by ring

/--
Constructive vacuum Einstein closure from unit relative-volume state
and a metric RN bridge.
-/
theorem vacuumEinsteinEquation_of_unitRelativeVolume
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hUnit : UnitRelativeVolumeState K)
    (hBridge : MetricRNRicciBridge R K x) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  intro u v
  unfold einsteinTensorAt
  rw [isRicciFlat_of_unitRelativeVolume (R := R) (K := K) (x := x) hUnit hBridge u v]
  ring

/--
Constructive closure theorem in explicit state form:
from the `IsRicciFlat` portion of the state, we obtain the vacuum Einstein equation.
-/
private theorem vacuumEinsteinEquation_of_isRicciFlatState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hState : MongeAmpereRicciState R K) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  intro u v
  unfold einsteinTensorAt
  rw [hState.2 u v]
  ring

end MongeAmpereRicci

end InfoGeometry.Canonical.CalabiYauBridge
