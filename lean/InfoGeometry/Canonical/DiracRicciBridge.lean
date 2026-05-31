import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.GrandSynthesis
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Jordan.LogDet
import InfoGeometry.Canonical.PerelmanWSpinorial
import InfoGeometry.Thermo.FromLogDet

/-!
# InfoGeometry.Canonical.DiracRicciBridge

Bridge layer connecting:
- RN/Jacobian log-volume deformation and positivity,
- Jordan/log-det barrier positivity,
- Bott-Dirac splitting,
- and Perelman-style Ricci/Dirac entropy flow monotonicity.
-/

namespace InfoGeometry.Canonical.DiracRicciBridge

open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.GrandSynthesis
open InfoGeometry.Canonical.GrandUnification
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Jordan
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Thermo

section DeterminantChain

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Negative log-absolute Jacobian is additive under composition. -/
theorem neg_log_abs_jac_det_clm_comp
    (L₁ L₂ : E →L[ℝ] E)
    (h₁ : jacDetCLM L₁ ≠ 0)
    (h₂ : jacDetCLM L₂ ≠ 0) :
    -logAbsJacDetCLM (L₁.comp L₂)
      = -logAbsJacDetCLM L₁ - logAbsJacDetCLM L₂ := by
  rw [logAbsJacDetCLM_comp (L₁ := L₁) (L₂ := L₂) h₁ h₂]
  ring

end DeterminantChain

section BottDiracRicci

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pointwise derivative law tying `W` to spinorial dissipation. -/
def satisfies_spinorial_dissipation_True
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s

/--
Special constant-tracking regime used by the imported Perelman-style derivative
identity: normalized scalar Kähler-Ricci flow with `W` governed by spinorial
Dissipation and the flow frozen to the spinorial scalar curvature.
-/
def satisfies_normalized_constant_spinorial_tracking_True
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ) : Prop :=
  satisfies_spinorial_dissipation_True flow IST W ∧
    SatisfiesNormalizedKaehlerRicciFlow (E := E) flow ∧
    (∀ t : ℝ, flow t = spinorialScalarCurvature IST)

/-- Monotonicity of `W` in the normalized constant spinorial tracking regime. -/
theorem w_monotone_of_normalized_constant_spinorial_tracking_True
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hLaw : satisfies_normalized_constant_spinorial_tracking_True flow IST W) :
    Monotone W := by
  rcases hLaw with ⟨hW, hNorm, hTrack⟩
  apply monotone_of_deriv_nonneg hDiff
  intro s
  rw [deriv_W_eq_abs_spinorial_of_normalized_tracking
    (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack s]
  exact abs_nonneg _

/--
If the spinorial dissipation dominates a fixed Jordan/Bregman barrier level,
then the dissipation law alone already forces monotonicity of `W`.
-/
theorem w_monotone_of_spinorial_dissipation_lower_bound
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ)
    (J : JordanKKTData E) (x y : E)
    (hDiff : Differentiable ℝ W)
    (hLaw : satisfies_spinorial_dissipation_True flow IST W)
    (hLower : ∀ s : ℝ, J.DBregman x y ≤ spinorialWDissipation flow IST s) :
    Monotone W := by
  apply monotone_of_deriv_nonneg hDiff
  intro s
  rw [hLaw s]
  exact le_trans (J.DBregman_nonneg x y) (hLower s)

/-- Strict monotonicity in the normalized constant spinorial tracking regime. -/
theorem w_strict_mono_of_normalized_constant_spinorial_tracking_True
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (W : ℝ → ℝ)
    (hLaw : satisfies_normalized_constant_spinorial_tracking_True flow IST W)
    (hSpin : spinorialScalarCurvature IST ≠ 0) :
    StrictMono W := by
  rcases hLaw with ⟨hW, hNorm, hTrack⟩
  apply strictMono_of_deriv_pos
  intro s
  rw [deriv_W_eq_abs_spinorial_of_normalized_tracking
    (E := E) (flow := flow) (IST := IST) (W := W) hW hNorm hTrack s]
  exact abs_pos.mpr hSpin

end BottDiracRicci

section EntropyGravity

variable (n : Nat)
variable {X : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
/--
Proof-carrying unit-volume route for RN entropy sourced vacuum gravity.

This narrows the public hypothesis surface from a bare
`relativeVolumeChangeRN n M = 1` equality to the constructive
`UnitRelativeVolumeBit` packet.
-/
theorem gravity_from_rn_entropy_of_unitRelativeVolumeBit
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo := by
    intro x'
    have hSource' :
        mongeAmpereDensity Kgeo.H x' = relativeVolumeChangeRN n M := by
      simpa using hSource x'
    exact hSource'.trans bit.unit_relative_volume
  refine ⟨?_, ?_⟩
  · exact isRicciFlat_of_unitRelativeVolume
      (R := R) (K := Kgeo) (x := x) hUnitState hBridge
  · exact vacuumEinsteinEquation_of_unitRelativeVolume
      (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hBridge

omit [FiniteDimensional ℝ X] in
/-- RN entropy sourcing plus unit-volume metric bridge yields vacuum gravity. -/
theorem gravity_from_rn_entropy
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_from_rn_entropy_of_unitRelativeVolumeBit
    (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) (M := M) hSource
    (InfoGeometry.Canonical.IncompressibleBitBridge.unitRelativeVolumeBit_of_eq_one hUnit)
    hBridge

end EntropyGravity

end InfoGeometry.Canonical.DiracRicciBridge
