import InfoGeometry.Quantum.ZeroPointEnergy
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Canonical.WeylInformationGauge
import InfoGeometry.Canonical.GrandSynthesis
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# InfoGeometry.Canonical.MasterSynthesis

Capstone composition module linking the canonical bridges:

1. Cramer-Rao / zero-point lower bound (`Quantum.ZeroPointEnergy`)
2. Projector-obstruction sourced Einstein equation (`ConformalUnification`)
3. Anomaly-as-fluid-state bridge (`NavierStokesBridge`)
4. Thermal-time identity (`YangMillsContinuum`)
5. Lichnerowicz-balanced Bott-Dirac closure (`GrandSynthesis`)
-/

namespace InfoGeometry.Canonical.MasterSynthesis

open InfoGeometry.Quantum.ZeroPointEnergy
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.WeylInformationGauge
open InfoGeometry.Canonical.GrandSynthesis
open InfoGeometry.Canonical.ChiralEinsteinBridge
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.BottDirac

variable {E F : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Bridge step (Cramer-Rao -> chiral scale):
if the zero-point variance is bounded above by the conformal chiral scale,
strict positivity of the variance forces strict positivity of `chiralScale`.
-/
theorem chiralScale_pos_of_zeroPoint_bridge
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale) :
    0 < CI.chiralScale := by
  have hZPE : 0 < S.variance_limit :=
    zero_point_energy_topological_obstruction S hRankPos
  exact lt_of_lt_of_le hZPE hScaleLink

/--
Bridge step (positive chiral scale -> nonzero anomaly operator):
`chiralScale = ‖[P_D,P_MP]‖₊`, so strict positivity forces nonzero anomaly.
-/
theorem chiralAnomalyOperator_ne_zero_of_chiralScale_pos
    (CI : ConformalInference E)
    (hScalePos : 0 < CI.chiralScale) :
    CI.chiralAnomalyOperator ≠ 0 := by
  have hNormPos : 0 < ‖CI.chiralAnomalyOperator‖₊ := by
    simpa [CI.chiralScale_eq_projectorObstruction_norm] using hScalePos
  exact (nnnorm_pos).1 hNormPos

/--
Constructive Einstein closure from metric-derived Ricci data:
if Ricci is taken from the Hessian metric operator (`StrongRicciFromHessian`),
then the projector-obstruction source equation is derived with `c = 1`.
-/
theorem einsteinEquation_of_metricRicci_and_projectorObstruction
    (CI : ConformalInference E)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ) :
    EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale) := by
  have hEin : IsEinsteinKaehlerAtWith 1 Sric.ricci Kgeo Sric.x0 := by
    intro u v
    simp [StrongRicciFromHessian.ricci, ricciFromMetricOp, hH]
  exact CI.einsteinEquation_of_projectorObstruction_source
    (c := 1) (R := Sric.ricci) (Kgeo := Kgeo) (x := Sric.x0)
    (Λ := Λ) (κ := κ) hEin

/--
Bridge step (ZPE -> anomaly -> transported Einstein residual):
combines the Cramer-Rao/chiral-scale bridge with the Weyl anomaly source law.
-/
theorem transportedEinsteinResidual_nonzero_of_zeroPoint_bridge
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := Kgeo) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CI.chiralScale) :
    transportedEinsteinResidual (R := R) (K := Kgeo) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  have hScalePos : 0 < CI.chiralScale :=
    chiralScale_pos_of_zeroPoint_bridge S hRankPos CI hScaleLink
  have hAnom : CI.chiralAnomalyOperator ≠ 0 :=
    chiralAnomalyOperator_ne_zero_of_chiralScale_pos CI hScalePos
  exact nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI := CI) (R := R) (K := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource hAnom

/--
Canonical anomaly-to-metric transport built from a scalar functional:
`u ↦ φ(u) • (-Id)`.
-/
noncomputable def anomalyToMetric_fromScalar
    (φ : VelocityField E →ₗ[ℝ] ℝ) : VelocityField E →ₗ[ℝ] Endomorphism F :=
  φ.smulRight (-(LinearMap.id : Endomorphism F))

@[simp] lemma anomalyToMetric_fromScalar_apply
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (u : VelocityField E) :
    anomalyToMetric_fromScalar (E := E) (F := F) φ u
      = (φ u) • (-(LinearMap.id : Endomorphism F)) := rfl

/--
If the scalar functional is normalized on the Einstein anomaly (`φ(χ)=1`),
the induced anomaly-to-metric transport evaluates exactly to `-Id` on `χ`.
-/
lemma anomalyToMetric_fromScalar_apply_einsteinAnomaly
    (A B_mp B_dr : VelocityField E)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr)
      = -(LinearMap.id : Endomorphism F) := by
  simp [anomalyToMetric_fromScalar, hUnit]

/--
Hahn-Banach normalization on the Einstein anomaly:
for nonzero `χ = EinsteinAnomaly A B_mp B_dr`, there exists a linear functional
`φ` with `φ χ = 1`.
-/
lemma exists_scalarFunctional_unit_on_einsteinAnomaly
    (A B_mp B_dr : VelocityField E)
    (hAnomalyNe : EinsteinAnomaly A B_mp B_dr ≠ 0) :
    ∃ φ : VelocityField E →ₗ[ℝ] ℝ, φ (EinsteinAnomaly A B_mp B_dr) = 1 := by
  let χ : VelocityField E := EinsteinAnomaly A B_mp B_dr
  have hnorm : ‖χ‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [χ] using hAnomalyNe)
  obtain ⟨g, _hgNorm, hgEval⟩ := exists_dual_vector ℝ χ hnorm
  refine ⟨(‖χ‖)⁻¹ • g.toLinearMap, ?_⟩
  calc
    ((‖χ‖)⁻¹ • g.toLinearMap) χ = (‖χ‖)⁻¹ * (g χ) := by simp
    _ = (‖χ‖)⁻¹ * ‖χ‖ := by
      simpa using congrArg (fun r : ℝ => (‖χ‖)⁻¹ * r) hgEval
    _ = 1 := inv_mul_cancel₀ hnorm

/--
Direct closure step:
if the spectral metric operator is exactly the anomaly transport and that
transport evaluates to `-Id`, then the split Cl(1,1) Lichnerowicz balance holds.
-/
theorem lichnerowiczBalanced_of_anomalyMetric_eq_neg_id
    (A B_mp B_dr : VelocityField E)
    (IST : InfoSpectralTriple F)
    (anomalyToMetric : VelocityField E →ₗ[ℝ] Endomorphism F)
    (hMetric :
      IST.H.metricOp IST.x₀ = anomalyToMetric (EinsteinAnomaly A B_mp B_dr))
    (hAnomalyMetricNegId :
      anomalyToMetric (EinsteinAnomaly A B_mp B_dr) = -(LinearMap.id : Endomorphism F)) :
    LichnerowiczBalancedCl11 (A := E) IST := by
  unfold LichnerowiczBalancedCl11
  rw [hMetric, hAnomalyMetricNegId, cl11DiracSeed_involutive (E := E)]
  ext u v
  simp [TensorProduct.map_tmul]
  calc
    u ⊗ₜ[ℝ] v + u ⊗ₜ[ℝ] (-v) = u ⊗ₜ[ℝ] (v + (-v)) := by
      symm
      exact TensorProduct.tmul_add u v (-v)
    _ = 0 := by simp

/--
Direct closure corollary:
from the explicit anomaly-to-`-Id` metric coupling, the split Bott-Dirac square vanishes.
-/
theorem bottDirac_sq_eq_zero_of_anomalyMetric_eq_neg_id
    (A B_mp B_dr : VelocityField E)
    (IST : InfoSpectralTriple F)
    (anomalyToMetric : VelocityField E →ₗ[ℝ] Endomorphism F)
    (hMetric :
      IST.H.metricOp IST.x₀ = anomalyToMetric (EinsteinAnomaly A B_mp B_dr))
    (hAnomalyMetricNegId :
      anomalyToMetric (EinsteinAnomaly A B_mp B_dr) = -(LinearMap.id : Endomorphism F)) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  exact cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced
    (A := E) IST
    (lichnerowiczBalanced_of_anomalyMetric_eq_neg_id
      (E := E) (F := F) A B_mp B_dr IST anomalyToMetric hMetric hAnomalyMetricNegId)

/--
Combined direct closure:
anomaly-as-fluid realization plus Bott-Dirac square closure from explicit
anomaly metric coupling (no bridge wrapper structure).
-/
theorem fluid_and_bottDirac_closure_of_anomalyMetric_eq_neg_id
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (IST : InfoSpectralTriple F)
    (anomalyToMetric : VelocityField E →ₗ[ℝ] Endomorphism F)
    (hMetric :
      IST.H.metricOp IST.x₀ = anomalyToMetric (EinsteinAnomaly A B_mp B_dr))
    (hAnomalyMetricNegId :
      anomalyToMetric (EinsteinAnomaly A B_mp B_dr) = -(LinearMap.id : Endomorphism F)) :
    (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact anomaly_as_fluid_state A B_mp B_dr k h_mp h_dr
  · exact bottDirac_sq_eq_zero_of_anomalyMetric_eq_neg_id
      (E := E) (F := F) A B_mp B_dr IST anomalyToMetric hMetric hAnomalyMetricNegId

/--
Direct closure with scalar-normalized anomaly transport:
if `IST.H.metricOp x₀` is the canonical transport `u ↦ φ(u) • (-Id)` evaluated at
the Einstein anomaly and `φ(χ)=1`, then the split Bott-Dirac square vanishes.
-/
theorem bottDirac_sq_eq_zero_of_anomalyMetric_fromScalar
    (A B_mp B_dr : VelocityField E)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetric :
      IST.H.metricOp IST.x₀ =
        anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  have hNegId :
      anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr)
        = -(LinearMap.id : Endomorphism F) :=
    anomalyToMetric_fromScalar_apply_einsteinAnomaly
      (E := E) (F := F) A B_mp B_dr φ hUnit
  exact bottDirac_sq_eq_zero_of_anomalyMetric_eq_neg_id
    (E := E) (F := F) A B_mp B_dr IST
    (anomalyToMetric_fromScalar (E := E) (F := F) φ)
    hMetric hNegId

/--
Combined direct closure with scalar-normalized anomaly transport:
anomaly-as-fluid realization plus Bott-Dirac closure.
-/
theorem fluid_and_bottDirac_closure_of_anomalyMetric_fromScalar
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetric :
      IST.H.metricOp IST.x₀ =
        anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact anomaly_as_fluid_state A B_mp B_dr k h_mp h_dr
  · exact bottDirac_sq_eq_zero_of_anomalyMetric_fromScalar
      (E := E) (F := F) A B_mp B_dr IST φ hMetric hUnit

/--
Metric-coupling collapse:
if the spectral metric operator at `x₀` is `-Id` and `φ(χ)=1`, then the
explicit scalar transport already matches the metric operator on `χ`.
-/
lemma anomalyMetric_fromScalar_eq_metric_of_metricOp_eq_neg_id
    (A B_mp B_dr : VelocityField E)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetricNegId : IST.H.metricOp IST.x₀ = -(LinearMap.id : Endomorphism F))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    IST.H.metricOp IST.x₀ =
      anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr) := by
  calc
    IST.H.metricOp IST.x₀ = -(LinearMap.id : Endomorphism F) := hMetricNegId
    _ = anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr) := by
      symm
      exact anomalyToMetric_fromScalar_apply_einsteinAnomaly
        (E := E) (F := F) A B_mp B_dr φ hUnit

/--
Direct closure from spectral `-Id` metric and anomaly normalization:
no separate anomaly-metric coupling equation is needed.
-/
theorem bottDirac_sq_eq_zero_of_metricOp_eq_neg_id_and_anomaly_unit
    (A B_mp B_dr : VelocityField E)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetricNegId : IST.H.metricOp IST.x₀ = -(LinearMap.id : Endomorphism F))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  exact bottDirac_sq_eq_zero_of_anomalyMetric_fromScalar
    (E := E) (F := F) A B_mp B_dr IST φ
    (anomalyMetric_fromScalar_eq_metric_of_metricOp_eq_neg_id
      (E := E) (F := F) A B_mp B_dr IST φ hMetricNegId hUnit)
    hUnit

/--
Combined closure from spectral `-Id` metric and anomaly normalization.
-/
theorem fluid_and_bottDirac_closure_of_metricOp_eq_neg_id_and_anomaly_unit
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetricNegId : IST.H.metricOp IST.x₀ = -(LinearMap.id : Endomorphism F))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  refine ⟨?_, ?_⟩
  · exact anomaly_as_fluid_state A B_mp B_dr k h_mp h_dr
  · exact bottDirac_sq_eq_zero_of_metricOp_eq_neg_id_and_anomaly_unit
      (E := E) (F := F) A B_mp B_dr IST φ hMetricNegId hUnit

/--
Spectral-to-metric reduction:
if `D² = -Id` in the spectral triple, then `metricOp x₀ = -Id`.
-/
lemma metricOp_eq_neg_id_of_dirac_sq_eq_neg_id
    (IST : InfoSpectralTriple F)
    (hDiracSqNegId : IST.D * IST.D = -(ContinuousLinearMap.id ℝ F)) :
    IST.H.metricOp IST.x₀ = -(LinearMap.id : Endomorphism F) := by
  have hFromInfo :
      (IST.H.metricOp IST.x₀ : Endomorphism F) = (IST.D * IST.D).toLinearMap := by
    exact (congrArg ContinuousLinearMap.toLinearMap IST.dirac_sq_eq_metric).symm
  have hFromNeg :
      (IST.D * IST.D).toLinearMap = -(LinearMap.id : Endomorphism F) := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hDiracSqNegId
  exact hFromInfo.trans hFromNeg

/--
Master capstone composition:

- information-theoretic zero-point lower bound,
- anomaly-sourced Einstein equation,
- anomaly-induced fluid realization,
- Connes-Rovelli thermal-time identity,
- Lichnerowicz-balanced split Bott-Dirac closure.
-/
theorem bits_to_gravity_to_fluid_capstone
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (c : ℝ)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (hBal : LichnerowiczBalancedCl11 (A := E) IST) :
    0 < S.variance_limit
      ∧ EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo x CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact zero_point_energy_topological_obstruction S hRankPos
  · exact CI.einsteinEquation_of_projectorObstruction_source c R Kgeo x Λ κ hEin
  · exact anomaly_as_fluid_state A B_mp B_dr k h_mp h_dr
  · exact M.connesRovelliThermalTimeIdentity
  · exact cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced (A := E) IST hBal

/--
Hardened capstone:
replaces abstract Einstein-Kähler input by a metric-derived Ricci package and
adds the non-vacuous ZPE -> anomaly positivity bridge.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (hBal : LichnerowiczBalancedCl11 (A := E) IST) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact chiralScale_pos_of_zeroPoint_bridge S hRankPos CI hScaleLink
  · exact einsteinEquation_of_metricRicci_and_projectorObstruction
      (CI := CI) (Sric := Sric) (Kgeo := Kgeo) hH Λ κ
  · exact anomaly_as_fluid_state A B_mp B_dr k h_mp h_dr
  · exact M.connesRovelliThermalTimeIdentity
  · exact cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced (A := E) IST hBal

/--
Hardened capstone with constructive fluid -> Lichnerowicz closure:
replaces the free Lichnerowicz hypothesis by explicit anomaly-metric equations.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (anomalyToMetric : VelocityField E →ₗ[ℝ] Endomorphism F)
    (hMetric :
      IST.H.metricOp IST.x₀ = anomalyToMetric (EinsteinAnomaly A B_mp B_dr))
    (hAnomalyMetricNegId :
      anomalyToMetric (EinsteinAnomaly A B_mp B_dr) = -(LinearMap.id : Endomorphism F)) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  have hFluidCl :
      (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
        ∧
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
        (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 :=
    fluid_and_bottDirac_closure_of_anomalyMetric_eq_neg_id
      (E := E) (F := F) A B_mp B_dr k h_mp h_dr IST
      anomalyToMetric hMetric hAnomalyMetricNegId
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact chiralScale_pos_of_zeroPoint_bridge S hRankPos CI hScaleLink
  · exact einsteinEquation_of_metricRicci_and_projectorObstruction
      (CI := CI) (Sric := Sric) (Kgeo := Kgeo) hH Λ κ
  · exact hFluidCl.1
  · exact M.connesRovelliThermalTimeIdentity
  · exact hFluidCl.2

/--
Hardened capstone with scalar-normalized anomaly transport:
`hAnomalyMetricNegId` is derived from `φ(χ)=1` constructively.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromScalar
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetric :
      IST.H.metricOp IST.x₀ =
        anomalyToMetric_fromScalar (E := E) (F := F) φ (EinsteinAnomaly A B_mp B_dr))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  have hFluidCl :
      (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
        ∧
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
        (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 :=
    fluid_and_bottDirac_closure_of_anomalyMetric_fromScalar
      (E := E) (F := F) A B_mp B_dr k h_mp h_dr IST φ hMetric hUnit
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact chiralScale_pos_of_zeroPoint_bridge S hRankPos CI hScaleLink
  · exact einsteinEquation_of_metricRicci_and_projectorObstruction
      (CI := CI) (Sric := Sric) (Kgeo := Kgeo) hH Λ κ
  · exact hFluidCl.1
  · exact M.connesRovelliThermalTimeIdentity
  · exact hFluidCl.2

/--
Hardened capstone with minimal spectral closure inputs:
replace explicit anomaly-metric coupling by `IST.H.metricOp x₀ = -Id` plus
scalar anomaly normalization `φ(χ)=1`.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromMetricNegId
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hMetricNegId : IST.H.metricOp IST.x₀ = -(LinearMap.id : Endomorphism F))
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  have hFluidCl :
      (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
        ∧
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
        (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 :=
    fluid_and_bottDirac_closure_of_metricOp_eq_neg_id_and_anomaly_unit
      (E := E) (F := F) A B_mp B_dr k h_mp h_dr IST φ hMetricNegId hUnit
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact chiralScale_pos_of_zeroPoint_bridge S hRankPos CI hScaleLink
  · exact einsteinEquation_of_metricRicci_and_projectorObstruction
      (CI := CI) (Sric := Sric) (Kgeo := Kgeo) hH Λ κ
  · exact hFluidCl.1
  · exact M.connesRovelliThermalTimeIdentity
  · exact hFluidCl.2

/--
Hardened capstone with spectral `D² = -Id` closure:
`metricOp x₀ = -Id` is derived constructively from `dirac_sq_eq_metric` and
the supplied spectral square identity.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromDiracSqNegId
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (hDiracSqNegId : IST.D * IST.D = -(ContinuousLinearMap.id ℝ F))
    (φ : VelocityField E →ₗ[ℝ] ℝ)
    (hUnit : φ (EinsteinAnomaly A B_mp B_dr) = 1) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  exact bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromMetricNegId
    (E := E) (F := F)
    S hRankPos CI hScaleLink Sric Kgeo hH Λ κ
    A B_mp B_dr k h_mp h_dr M IST φ
    (metricOp_eq_neg_id_of_dirac_sq_eq_neg_id
      (F := F) IST hDiracSqNegId)
    hUnit

/--
Most reduced constructive closure currently available:
`φ(χ)=1` is derived from `χ ≠ 0` via Hahn-Banach, and `metricOp x₀ = -Id`
is derived from spectral `D² = -Id`.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromDiracSqNegId_anomalyNonzero
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (hAnomalyNe : EinsteinAnomaly A B_mp B_dr ≠ 0)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple F)
    (hDiracSqNegId : IST.D * IST.D = -(ContinuousLinearMap.id ℝ F)) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  obtain ⟨φ, hUnit⟩ :=
    exists_scalarFunctional_unit_on_einsteinAnomaly
      (E := E) A B_mp B_dr hAnomalyNe
  exact bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromDiracSqNegId
    (E := E) (F := F)
    S hRankPos CI hScaleLink Sric Kgeo hH Λ κ
    A B_mp B_dr k h_mp h_dr M IST hDiracSqNegId φ hUnit

/--
Concrete spectral closure on doubled space:
if `IST.D = complex_i`, then `IST.D² = -Id`.
-/
lemma dirac_sq_eq_neg_id_of_dirac_eq_complex_i
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (IST : InfoSpectralTriple (InfoGeometry.Krein.DoubledSpace G))
    (hDirac : IST.D = InfoGeometry.Krein.complex_i (E := G)) :
    IST.D * IST.D = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace G)) := by
  rw [hDirac]
  change
    (InfoGeometry.Krein.complex_i (E := G)).comp (InfoGeometry.Krein.complex_i (E := G))
      = -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace G))
  exact InfoGeometry.Krein.complex_i_sq G

/--
Most concrete closure currently available:
specialize the spectral channel to doubled-space `complex_i`; then `D² = -Id`
is derived, and combined with anomaly nonzero to obtain the full capstone closure.
-/
theorem bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromDiracEqComplexI_anomalyNonzero
    {G : Type}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (S : SpinFactorState E)
    (hRankPos : 0 < Module.finrank ℝ E)
    (CI : ConformalInference E)
    (hScaleLink : S.variance_limit ≤ CI.chiralScale)
    (Sric : StrongRicciFromHessian E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (hH : Kgeo.H = Sric.H)
    (Λ κ : ℝ)
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (hAnomalyNe : EinsteinAnomaly A B_mp B_dr ≠ 0)
    (M : ModularRadonNikodymData E)
    (IST : InfoSpectralTriple (InfoGeometry.Krein.DoubledSpace G))
    (hDirac : IST.D = InfoGeometry.Krein.complex_i (E := G)) :
    0 < CI.chiralScale
      ∧ EinsteinEquationAt Sric.ricci Kgeo Sric.x0 (2 * (1 + Λ - κ * CI.chiralScale)) Λ κ
          (anomalyStressEnergyAt Kgeo Sric.x0 CI.chiralScale)
      ∧ (∃ state : FluidState E, state.u = EinsteinAnomaly A B_mp B_dr)
      ∧ M.ConnesRovelliThermalTimeIdentity
      ∧ (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)).comp
          (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (spectralDiracLinear IST)) = 0 := by
  exact bits_to_gravity_to_fluid_capstone_hardened_constructiveLichnerowicz_fromDiracSqNegId_anomalyNonzero
    (E := E) (F := InfoGeometry.Krein.DoubledSpace G)
    S hRankPos CI hScaleLink Sric Kgeo hH Λ κ
    A B_mp B_dr k h_mp h_dr hAnomalyNe M IST
    (dirac_sq_eq_neg_id_of_dirac_eq_complex_i (IST := IST) hDirac)

end InfoGeometry.Canonical.MasterSynthesis
