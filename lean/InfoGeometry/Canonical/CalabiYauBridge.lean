import InfoGeometry.Canonical.PerelmanW
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.SpectralInference

section MongeAmpereRicci

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

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

/-- Constructive Calabi-Yau geometric state (non-bridge form). -/
abbrev CalabiYauRicciState (R : RicciTensor E) : Prop :=
  IsRicciFlat R

/--
Constructive closure state for the Monge-Ampere-to-Ricci layer:
constant Monge-Ampere density together with an explicit Ricci-flat witness.
-/
def MongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) : Prop :=
  HasConstantMongeAmpereDensity K.H ∧ IsRicciFlat R

/-- Lemma `hasConstantMongeAmpereDensity_iff`. -/
lemma hasConstantMongeAmpereDensity_iff
    (H : HessianGeometry E) :
    HasConstantMongeAmpereDensity H
      ↔ ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0 := Iff.rfl

/-- Lemma `hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const`. -/
lemma hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const
    (H : HessianGeometry E) (ρ0 : ℝ)
    (hMA : SatisfiesMongeAmpere H (fun _ => ρ0)) :
    HasConstantMongeAmpereDensity H := by
  exact ⟨ρ0, hMA⟩

/-- Lemma `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity`. -/
lemma satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity
    (H : HessianGeometry E)
    (hConst : HasConstantMongeAmpereDensity H) :
    ∃ ρ0 : ℝ, SatisfiesMongeAmpere H (fun _ => ρ0) := by
  obtain ⟨ρ0, hρ0⟩ := hConst
  refine ⟨ρ0, ?_⟩
  intro x
  exact hρ0 x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Lemma `ricciTensor_eq_of_isRicciFlat`. -/
lemma ricciTensor_eq_of_isRicciFlat
    {R₁ R₂ : RicciTensor E}
    (h₁ : IsRicciFlat R₁) (h₂ : IsRicciFlat R₂) :
    R₁ = R₂ := by
  funext u v
  rw [h₁ u v, h₂ u v]

/-- Lemma `isEinsteinKaehlerAtWith_zero_of_isRicciFlat`. -/
lemma isEinsteinKaehlerAtWith_zero_of_isRicciFlat
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
lemma isRicciFlat_of_isEinsteinKaehlerAtWith_zero
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
  unitVolume_metricDerived_zero :
    UnitRelativeVolumeState K → ∀ u v : E, ricciFromMetricOp K.H x u v = 0

/--
Every metric-derived RN bridge induces the abstract metric-to-Ricci bridge.
-/
theorem metricRNRicciBridge_of_metricDerived
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
theorem isAdSLikeEinsteinAt_of_negative_einstein
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
theorem vacuumEinsteinEquation_zeroScalar_of_isAdSLikeEinsteinAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hAdS : IsAdSLikeEinsteinAt R K x) :
    ∃ Λ : ℝ, 0 < Λ ∧ VacuumEinsteinEquationAt R K x 0 Λ := by
  rcases hAdS with ⟨Λ, hΛpos, hEin⟩
  refine ⟨Λ, hΛpos, ?_⟩
  exact vacuumEinsteinEquation_of_scalar_relation
    (c := -Λ) (R := R) (K := K) (x := x) (scalar := 0) (Λ := Λ)
    hEin (by ring)

/-- Projection: a `MongeAmpereRicciState` carries the constant-density witness. -/
theorem hasConstantMongeAmpereDensity_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState : MongeAmpereRicciState R K) :
    HasConstantMongeAmpereDensity K.H :=
  hState.1

/-- Projection: a `MongeAmpereRicciState` carries Ricci-flatness. -/
theorem isRicciFlat_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState : MongeAmpereRicciState R K) :
    IsRicciFlat R :=
  hState.2

/--
Constructive state packaging:
constant Monge-Ampere density and explicit Ricci-flatness form the closure state.
-/
theorem mongeAmpereRicciState_mk
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hConst : HasConstantMongeAmpereDensity K.H)
    (hFlat : IsRicciFlat R) :
    MongeAmpereRicciState R K := by
  exact ⟨hConst, hFlat⟩

/--
Uniqueness under constructive closure states:
if two Ricci tensors are both Ricci-flat under the same geometry scaffold, they coincide.
-/
theorem ricciTensor_unique_of_mongeAmpereRicciState
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
theorem vacuumEinsteinEquation_of_isRicciFlat
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
Constructive closure theorem in state form:
from `MongeAmpereRicciState` we obtain the vacuum Einstein equation.
-/
theorem vacuumEinsteinEquation_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hState : MongeAmpereRicciState R K) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  intro u v
  unfold einsteinTensorAt
  rw [hState.2 u v]
  ring

end MongeAmpereRicci

section WBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/--
Constructive Calabi-Yau spectral closure state:
constant Monge-Ampere density together with vanishing spinorial scalar curvature.
-/
def MongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E) : Prop :=
  HasConstantMongeAmpereDensity IST.H ∧ spinorialScalarCurvature IST = 0

/-- Constructive spectral Calabi-Yau state (non-bridge form). -/
def CalabiYauSpinorialState (IST : InfoSpectralTriple E) : Prop :=
  spinorialScalarCurvature IST = 0

/-- Constructor for the spinorial closure state. -/
theorem mongeAmpereSpinorialClosure_mk
    (IST : InfoSpectralTriple E)
    (hConst : HasConstantMongeAmpereDensity IST.H)
    (hSpin0 : CalabiYauSpinorialState IST) :
    MongeAmpereSpinorialClosure IST := by
  exact ⟨hConst, hSpin0⟩

/-- Extract spinorial vanishing from the constructive spinorial closure state. -/
theorem spinorialScalarCurvature_eq_zero_of_mongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E)
    (hCY : MongeAmpereSpinorialClosure IST) :
    CalabiYauSpinorialState IST :=
  hCY.2

/--
Connection to the `W`-flow layer:
under normalized spinorial tracking, Calabi-Yau closure makes `W` constant.
-/
theorem W_constant_of_mongeAmpereSpinorialClosure
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hCY : MongeAmpereSpinorialClosure IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  exact W_constant_of_spinorial_zero
    (E := E) (flow := flow) (IST := IST) (W := W)
    hDiff hW hNorm hTrack hCY.2

/--
Constructive `W`-constancy closure from an explicit zero-spinorial witness
(non-bridge form).
-/
theorem W_constant_of_spinorialState
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hSpin0 : CalabiYauSpinorialState IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  exact W_constant_of_spinorial_zero
    (E := E) (flow := flow) (IST := IST) (W := W)
    hDiff hW hNorm hTrack hSpin0

end WBridge

end InfoGeometry.Canonical.CalabiYauBridge
