import InfoGeometry.Canonical.GrandUnificationMetric
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.GrandCanonicalExperts
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.ChiralEinsteinBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Conformal Inference Structure.
Formalizes the unification of Conformal Algebra, Generalized Inverses,
and Geometric Chirality.
-/
structure ConformalInference (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] extends InfoGeometry.Canonical.InverseKernel E where

/--
Certified conformal inference package.

This is the proof-carrying refinement of `ConformalInference`: the supplied
Drazin and Moore-Penrose regularizations are certified against the base
operator `A`.
-/
structure CertifiedConformalInference (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] extends ConformalInference E where
  drazinIndex : ℕ
  hDrazin : IsDrazinInverse A A_D drazinIndex
  hMoorePenrose : IsMoorePenroseInverse A A_MP

namespace CertifiedConformalInference

variable (CCI : CertifiedConformalInference E)

/-- Adapter from the conformal surface to the canonical certified inverse kernel. -/
abbrev toCertifiedInverseKernel : InfoGeometry.Canonical.CertifiedInverseKernel E :=
  { toInverseKernel := CCI.toConformalInference.toInverseKernel
    drazinIndex := CCI.drazinIndex
    hDrazin := CCI.hDrazin
    hMoorePenrose := CCI.hMoorePenrose }

/-- The certified Drazin spectral projector. -/
abbrev spectralProjector : E →L[ℝ] E := CCI.toCertifiedInverseKernel.spectralProjector

/-- The certified Moore-Penrose range projector. -/
abbrev mpRangeProjector : E →L[ℝ] E :=
  CCI.toCertifiedInverseKernel.mpRangeProjector

/-- The certified Moore-Penrose domain projector. -/
abbrev metricProjector : E →L[ℝ] E := CCI.toCertifiedInverseKernel.metricProjector

/-- The certified Drazin spectral projector is idempotent. -/
theorem spectralProjector_idempotent :
    CCI.spectralProjector * CCI.spectralProjector = CCI.spectralProjector := by
  simpa [CertifiedConformalInference.spectralProjector] using
    CCI.toCertifiedInverseKernel.spectralProjector_idempotent

/-- The certified Moore-Penrose range projector is idempotent. -/
theorem mpRangeProjector_idempotent :
    CCI.mpRangeProjector * CCI.mpRangeProjector = CCI.mpRangeProjector := by
  simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_idempotent

/-- The certified Moore-Penrose domain projector is idempotent. -/
theorem metricProjector_idempotent :
    CCI.metricProjector * CCI.metricProjector = CCI.metricProjector := by
  simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_idempotent

/-- The certified Moore-Penrose domain projector is self-adjoint. -/
theorem metricProjector_star :
    star CCI.metricProjector = CCI.metricProjector := by
  simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_star

/-- The certified Moore-Penrose range projector is self-adjoint. -/
theorem mpRangeProjector_star :
    star CCI.mpRangeProjector = CCI.mpRangeProjector := by
  simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_star

end CertifiedConformalInference

namespace ConformalInference

variable (CI : ConformalInference E)

/-! ### 1. Conformal Generators -/

/--
Information Translation Generator (P).
Identified with the primary information operator A.
-/
def P : E →L[ℝ] E := CI.A

/--
Special Conformal Information Generator (K).
Identified with the Moore-Penrose inverse A+, representing metric inversion.
-/
def K : E →L[ℝ] E := CI.A_MP

/--
Conformal inversion realization of the special conformal generator:
if `J` implements inversion on translation, then `K = J P J`.
-/
theorem specialConformal_eq_modularInversion_translation
    (J : E →L[ℝ] E)
    (hJPJ : J * CI.P * J = CI.K) :
    CI.K = J * CI.P * J := by
  simpa using hJPJ.symm

/--
Involutive inversion (`J² = 1`) recovers translation from special conformal
generator: `P = J K J`.
-/
theorem translation_eq_modularInversion_specialConformal
    (J : E →L[ℝ] E)
    (hJ2 : J * J = (1 : E →L[ℝ] E))
    (hJPJ : J * CI.P * J = CI.K) :
    J * CI.K * J = CI.P := by
  calc
    J * CI.K * J = J * (J * CI.P * J) * J := by rw [hJPJ]
    _ = (J * J) * CI.P * (J * J) := by
          simp [mul_assoc]
    _ = (1 : E →L[ℝ] E) * CI.P * (1 : E →L[ℝ] E) := by
          simp [hJ2]
    _ = CI.P := by simp

/--
Emergent Information Dilation Generator (D).
D = 1/2 [P, K].
This operator generates the 'Information Scale' flow.
-/
noncomputable def D : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.P * CI.K - CI.K * CI.P)

/--
The dilation operator is exactly half the difference between the Moore-Penrose
range and domain projectors.
-/
theorem dilation_eq_half_sub_mp_projectors :
    CI.D =
      ((2 : ℝ)⁻¹) •
        (IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
          - IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) := by
  simp [D, P, K, IsMoorePenroseInverse.rightProjector, IsMoorePenroseInverse.leftProjector]

/-! ### 2. Chiral Projectors and Anomaly -/

/--
Spectral Chiral Projector (P_D).
Filters the belief space based on algebraic/nilpotent structure.
-/
def P_D : E →L[ℝ] E := IsDrazinInverse.projection CI.A CI.A_D

/-- Canonical naming alias for the spectral chiral projector. -/
abbrev spectralChiralProjector : E →L[ℝ] E := CI.P_D

/--
Metric Chiral Projector (P_MP).
Filters the belief space based on metric orthogonality.
-/
def P_MP : E →L[ℝ] E := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP

/-- Canonical naming alias for the metric chiral projector. -/
abbrev metricChiralProjector : E →L[ℝ] E := CI.P_MP

/--
Moore-Penrose range projector.
This is the right-projector convention used by `Singular.EinsteinAnomaly`.
-/
def P_MP_right : E →L[ℝ] E := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP

/-- Canonical naming alias for the right Moore-Penrose projector. -/
abbrev metricRangeProjector : E →L[ℝ] E := CI.P_MP_right

/--
The Geometric Chiral Anomaly (χ).
χ = [P_D, P_MP].
This measures the topological 'twist' between information gain and metric distance.
-/
noncomputable def chiralAnomaly : E →L[ℝ] E :=
  CI.P_D * CI.P_MP - CI.P_MP * CI.P_D

/-- Canonical naming alias for the chiral-anomaly operator. -/
noncomputable abbrev chiralAnomalyOperator : E →L[ℝ] E := CI.chiralAnomaly

/--
Right-projector chiral anomaly.
This is the anomaly built from the Moore-Penrose range projector instead of the
left projector used in `CI.chiralAnomaly`.
-/
noncomputable def rightChiralAnomaly : E →L[ℝ] E :=
  CI.P_D * CI.P_MP_right - CI.P_MP_right * CI.P_D

/--
The singular Einstein anomaly is exactly the negative of the right-projector
chiral anomaly.
-/
theorem einsteinAnomaly_eq_neg_rightChiralAnomaly :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = -CI.rightChiralAnomaly := by
  unfold InfoGeometry.Canonical.EinsteinAnomaly rightChiralAnomaly P_D P_MP_right
  unfold IsDrazinInverse.projection IsMoorePenroseInverse.rightProjector
  noncomm_ring

/--
If the Moore-Penrose left and right projectors coincide, then the singular
Einstein anomaly is the negative of the conformal left-projector anomaly.
-/
theorem einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CI.A CI.A_MP =
        IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = -CI.chiralAnomalyOperator := by
  rw [CI.einsteinAnomaly_eq_neg_rightChiralAnomaly]
  simp [rightChiralAnomaly, chiralAnomalyOperator, chiralAnomaly, P_D, P_MP_right, P_MP, hProj]

/--
The Scale Constant ε.
Generated by the non-commutativity of spectral and metric information.
-/
noncomputable def epsilon : ℝ :=
  nnnorm CI.chiralAnomaly

/-- Canonical naming alias for the anomaly scale. -/
noncomputable abbrev chiralScale : ℝ := CI.epsilon

/--
Exact obstruction identity: the anomaly source scale is the norm of the
projector commutator.
-/
theorem chiralScale_eq_projectorObstruction_norm :
    CI.chiralScale =
      ‖CI.spectralChiralProjector * CI.metricChiralProjector
          - CI.metricChiralProjector * CI.spectralChiralProjector‖₊ := by
  simp [chiralScale, epsilon, chiralAnomaly, spectralChiralProjector, metricChiralProjector]

/--
The commutator of the Drazin spectral projector with the dilation operator
decomposes into the difference of its commutators with the Moore-Penrose range
and domain projectors.
-/
theorem spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators :
    CI.P_D * CI.D - CI.D * CI.P_D =
      ((2 : ℝ)⁻¹) •
        ((CI.P_D * IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
            - IsMoorePenroseInverse.rightProjector CI.A CI.A_MP * CI.P_D)
          -
          (CI.P_D * IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
            - IsMoorePenroseInverse.leftProjector CI.A CI.A_MP * CI.P_D)) := by
  rw [CI.dilation_eq_half_sub_mp_projectors]
  simp [sub_eq_add_neg, smul_sub]
  noncomm_ring

/--
Equivalent bridge form: the spectral-projector/dilation commutator is half the
difference between the spectral-vs-range-projector commutator and the chiral
anomaly operator.
-/
theorem spectralProjector_commutator_dilation_eq_half_sub_anomaly :
    CI.P_D * CI.D - CI.D * CI.P_D =
      ((2 : ℝ)⁻¹) •
        ((CI.P_D * IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
            - IsMoorePenroseInverse.rightProjector CI.A CI.A_MP * CI.P_D)
          - CI.chiralAnomalyOperator) := by
  rw [CI.spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators]
  simp [chiralAnomalyOperator, chiralAnomaly, P_MP, metricChiralProjector,
    IsMoorePenroseInverse.leftProjector]

/--
Bridge identity between the singular/right-projector anomaly convention and the
conformal/left-projector anomaly convention.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral :
    CI.P_D * CI.D - CI.D * CI.P_D =
      -((2 : ℝ)⁻¹) •
        (InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D + CI.chiralAnomalyOperator) := by
  rw [CI.spectralProjector_commutator_dilation_eq_half_sub_anomaly]
  rw [CI.einsteinAnomaly_eq_neg_rightChiralAnomaly]
  simp [rightChiralAnomaly, chiralAnomalyOperator, chiralAnomaly, P_MP_right,
    IsMoorePenroseInverse.rightProjector, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm, smul_add, smul_neg]

/-! ### 3. Unification Theorems -/

omit [FiniteDimensional ℝ E] in
/--
Theorem: The chiral anomaly vanishes exactly when the spectral and metric
projectors commute.
-/
theorem chiral_commutation_link :
    CI.chiralAnomaly = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  simp [chiralAnomaly, spectralChiralProjector, metricChiralProjector, sub_eq_zero]

omit [FiniteDimensional ℝ E] in
/-- Vanishing anomaly iff spectral and metric projectors commute. -/
theorem chiralAnomalyOperator_eq_zero_iff_projectors_commute :
    CI.chiralAnomalyOperator = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  simpa [chiralAnomalyOperator] using (CI.chiral_commutation_link)

/--
Constructive forward direction: vanishing anomaly implies projector commutation.
-/
theorem projectors_commute_of_chiralAnomaly_eq_zero
    (hχ : CI.chiralAnomalyOperator = 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector :=
  (CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute).1 hχ

/--
Constructive reverse direction: projector commutation implies vanishing anomaly.
-/
theorem chiralAnomaly_eq_zero_of_projectors_commute
    (hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector) :
    CI.chiralAnomalyOperator = 0 :=
  (CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute).2 hComm

/-- Commuting projectors force zero anomaly source scale. -/
theorem chiralScale_eq_zero_of_projectors_commute
    (hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector) :
    CI.chiralScale = 0 := by
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    CI.chiralAnomaly_eq_zero_of_projectors_commute hComm
  simpa [chiralScale, epsilon, chiralAnomalyOperator, hAnomZero]

/-- Non-commuting projectors force nonzero anomaly source scale. -/
theorem chiralScale_ne_zero_of_projectors_not_commute
    (hCommNe :
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠ CI.metricChiralProjector * CI.spectralChiralProjector) :
    CI.chiralScale ≠ 0 := by
  intro hScaleZero
  have hNorm : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [chiralScale, epsilon, chiralAnomalyOperator] using hScaleZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 := (nnnorm_eq_zero).1 hNorm
  exact hCommNe ((CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute).1 hAnomZero)

/--
Constructive projector-commutation closure from scalar anomaly-driven Kähler-Ricci
dynamics at normalized RG fixed point.

This discharges commutation without assuming it directly:
the dynamics force `flow = 0` and `flow = chiralScale`, hence `chiralScale = 0`,
which forces vanishing anomaly and therefore projector commutation.
-/
private theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    (hAnomFlow :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
        (fun _ => CI.chiralScale)) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hFlowZero : ∀ s : ℝ, flow s = 0 :=
    normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := E) (flow := flow) hNorm hFixed
  have hFlowTracksScale : ∀ s : ℝ, flow s = CI.chiralScale :=
    anomalyDrivenScalarRicci_fixedpoint_tracks_source
      (E := E) (flow := flow) (A := fun _ => CI.chiralScale)
      hAnomFlow hFixed
  have hScaleZero : CI.chiralScale = 0 := by
    calc
      CI.chiralScale = flow 0 := by simpa using (hFlowTracksScale 0).symm
      _ = 0 := hFlowZero 0
  have hNormAnom : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [chiralScale, epsilon, chiralAnomalyOperator] using hScaleZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    (nnnorm_eq_zero).1 hNormAnom
  exact CI.projectors_commute_of_chiralAnomaly_eq_zero hAnomZero

/--
Derive anomaly-driven scalar Ricci dynamics from normalized Kähler-Ricci flow
once the conformal chiral scale vanishes (`ε = 0`).
-/
private theorem anomalyDrivenScalarRicciFlow_of_normalized_and_chiralScale_zero
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hScaleZero : CI.chiralScale = 0) :
    SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow (fun _ => CI.chiralScale) := by
  have hZeroSource :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow (fun _ => 0) :=
    (anomalyDriven_zeroSource_iff_normalized (E := E) (flow := flow)).2 hNorm
  intro s
  simpa [hScaleZero] using hZeroSource s

/--
Normality (`ε = 0`) from the Kähler/log-det layer:
if the conformal chiral scale matches the RN Kähler potential and the RN
relative volume is unit, then `ε = 0`.
-/
theorem chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.chiralScale = 0 := by
  have hNegKZero : -kahlerPotentialRN n M = 0 := by
    have hLog :
        Real.log (relativeVolumeChangeRN n M) = Real.log (1 : ℝ) :=
      congrArg Real.log hUnitVolume
    simpa [relativeVolumeChangeRN] using hLog
  have hKZero : kahlerPotentialRN n M = 0 := by
    have h := congrArg Neg.neg hNegKZero
    simpa using h
  calc
    CI.chiralScale = kahlerPotentialRN n M := hScaleFromKahler
    _ = 0 := hKZero

/--
Zero anomaly scale implies projector commutation.

This gives a direct algebraic closure path from scalar normality (`χ = 0`)
to vanishing projector obstruction.
-/
theorem projectors_commute_of_chiralScale_eq_zero
    (hScaleZero : CI.chiralScale = 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hNormAnom : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [chiralScale, epsilon, chiralAnomalyOperator] using hScaleZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    (nnnorm_eq_zero).1 hNormAnom
  exact CI.projectors_commute_of_chiralAnomaly_eq_zero hAnomZero

/--
Projector commutation directly from the Kähler/log-det layer:
matching `χ` to the RN Kähler potential and unit relative volume force
`χ = 0`, hence vanishing projector obstruction.
-/
theorem projectors_commute_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  exact CI.projectors_commute_of_chiralScale_eq_zero
    (CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume)

/--
Log-det barrier self-concordance mechanics package:
unit relative volume in the RN layer forces zero Kähler potential, zero anomaly
scale, normal inference, and projector-obstruction closure.
-/
theorem logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    kahlerPotentialRN n M = 0
      ∧ CI.chiralScale = 0
      ∧ (CI.spectralChiralProjector * CI.metricChiralProjector
            = CI.metricChiralProjector * CI.spectralChiralProjector) := by
  have hScaleZero : CI.chiralScale = 0 :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  have hKahlerZero : kahlerPotentialRN n M = 0 := by
    calc
      kahlerPotentialRN n M = CI.chiralScale := by
        simpa [eq_comm] using hScaleFromKahler
      _ = 0 := hScaleZero
  refine ⟨hKahlerZero, hScaleZero, ?_⟩
  exact CI.projectors_commute_of_chiralScale_eq_zero hScaleZero

/--
Canonical anomaly-flow derivation from the Kähler/log-det layer.

This discharges the anomaly-flow witness directly from normalized Kähler-Ricci
flow and unit relative volume in the log-det potential layer.
-/
theorem anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
      (fun _ => CI.chiralScale) := by
  have hScaleZero : CI.chiralScale = 0 :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  exact CI.anomalyDrivenScalarRicciFlow_of_normalized_and_chiralScale_zero
    (flow := flow) hNorm hScaleZero

/--
Projector commutation from normalized Kähler/log-det data at a scalar Ricci
fixed point.

This discharges the anomaly-flow witness internally:
`hAnomFlow` is derived from the Kähler/log-det layer and then fed into the
fixed-point commutation closure.
-/
theorem projectors_commute_of_kahlerLogDet_normalized_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hAnomFlow :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
        (fun _ => CI.chiralScale) :=
    CI.anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized
      (flow := flow) hNorm (M := M) hScaleFromKahler hUnitVolume
  exact CI.projectors_commute_of_anomalyDriven_normalized_fixedpoint
    (flow := flow) hNorm hFixed hAnomFlow

/--
Einstein closure with anomaly source taken directly from the projector-obstruction
scale `χ = ‖[P_D,P_MP]‖`.
-/
theorem einsteinEquation_of_projectorObstruction_source
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo x CI.chiralScale) := by
  exact einsteinEquation_of_anomaly_source
    (E := E)
    (c := c) (R := R) (K := Kgeo) (x := x)
    (Λ := Λ) (κ := κ) (A := CI.chiralScale) hEin

/--
Cartan-like Decomposition of the Information Manifold.
The space decomposes into a Normal sector (ε = 0) and a Chiral sector (ε > 0).
This mirrors the Cl(1,1) grading into even and odd endomorphisms.
-/
def IsNormalInference : Prop := CI.chiralScale = 0

/--
Normal-inference corollary from the log-det self-concordance mechanics package.
-/
theorem isNormalInference_of_logDetBarrier_selfConcordance_mechanics
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    IsNormalInference (CI := CI) := by
  have hMechanics :=
    CI.logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  simpa [IsNormalInference] using hMechanics.2.1

/-- Definition `IsChiralInference`. -/
def IsChiralInference : Prop := 0 < CI.chiralScale

-- Legacy alias: normal inference stated via `epsilon = 0`.
omit [FiniteDimensional ℝ E] in
/-- Theorem `isNormalInference_iff_epsilon_eq_zero`. -/
theorem isNormalInference_iff_epsilon_eq_zero :
    IsNormalInference (CI := CI) ↔ CI.epsilon = 0 := by
  simp [IsNormalInference, chiralScale]

-- Legacy alias: chiral inference stated via `0 < epsilon`.
omit [FiniteDimensional ℝ E] in
/-- Theorem `isChiralInference_iff_epsilon_pos`. -/
theorem isChiralInference_iff_epsilon_pos :
    IsChiralInference (CI := CI) ↔ 0 < CI.epsilon := by
  simp [IsChiralInference, chiralScale]

/-- Canonical alias for the normal (non-chiral) information state. -/
abbrev NormalInferenceState : Prop := IsNormalInference (CI := CI)

/-- Canonical alias for the chiral information state. -/
abbrev ChiralInferenceState : Prop := IsChiralInference (CI := CI)


/--
Zero anomaly follows from the normalized Kähler/log-det flow assumptions used
to derive projector commutation.
-/
theorem chiralAnomaly_eq_zero_of_kahlerLogDet_normalized_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.chiralAnomalyOperator = 0 := by
  have hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector :=
    CI.projectors_commute_of_kahlerLogDet_normalized_fixedpoint
      (flow := flow) hNorm hFixed (M := M) hScaleFromKahler hUnitVolume
  exact CI.chiralAnomaly_eq_zero_of_projectors_commute hComm

/--
The Structure Constant Operator (Σ).
Defined as the commutator of the spectral (Drazin) and metric (Penrose) projectors.
This operator sets the scale for the non-commutative deformation of the
information volume form.
-/
def actionStructureConstantOp : E →L[ℝ] E :=
  CI.P_D.comp CI.P_MP - CI.P_MP.comp CI.P_D

/--
The Scalar Unit of Action (h).
The operator norm of the structure constant operator.
This sets the fundamental 'grain' or 'scale' of the information manifold.
-/
noncomputable def unitOfAction : ℝ :=
  ‖CI.actionStructureConstantOp‖

/-- The structure-constant operator is exactly the chiral-anomaly operator. -/
theorem actionStructureConstantOp_eq_chiralAnomalyOperator :
    CI.actionStructureConstantOp = CI.chiralAnomalyOperator := by
  ext x
  rfl

/-- The scalar unit of action coincides with the chiral anomaly scale. -/
theorem unitOfAction_eq_chiralScale :
    CI.unitOfAction = CI.chiralScale := by
  simp [unitOfAction, chiralScale, epsilon, CI.actionStructureConstantOp_eq_chiralAnomalyOperator]

/-- In the normal phase, the unit of action vanishes. -/
theorem unitOfAction_eq_zero_of_normalInference
    (hNormal : NormalInferenceState (CI := CI)) :
    CI.unitOfAction = 0 := by
  rw [CI.unitOfAction_eq_chiralScale]
  exact hNormal

/-- In the chiral phase, the unit of action is strictly positive. -/
theorem unitOfAction_pos_of_chiralInference
    (hChiral : ChiralInferenceState (CI := CI)) :
    0 < CI.unitOfAction := by
  rw [CI.unitOfAction_eq_chiralScale]
  exact hChiral

/--
Theorem: Scale generation from non-commutativity.
If the spectral and metric projectors do not commute (Chiral Anomaly),
the unit of action is strictly positive.
-/
theorem unitOfAction_pos_of_noncommute
    (hAnom : CI.P_D.comp CI.P_MP ≠ CI.P_MP.comp CI.P_D) :
    0 < CI.unitOfAction := by
  unfold unitOfAction actionStructureConstantOp
  simp only [norm_pos_iff, ne_eq]
  exact sub_ne_zero.mpr hAnom

end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
