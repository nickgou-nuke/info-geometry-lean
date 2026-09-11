import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.InverseKernelNormalForm
import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Canonical.TransportLieDerivative
import Mathlib.Analysis.Normed.Algebra.Spectrum
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Projector compression helper. -/
@[rep_depth operator]
def compress (P A : EndH) : EndH :=
  P * A * P

/-- Metric-lane selector for physical realization. -/
@[rep_depth operator]
inductive MetricSide
  | left
  | right
  deriving DecidableEq, Repr

/-- Lane-selected metric projector. -/
@[rep_depth operator]
def metricProjectorOf (s : MetricSide) (CIK : CertifiedInverseKernel E) : EndH :=
  match s with
  | .left => CIK.metricProjector
  | .right => CIK.mpRangeProjector

@[rep_depth operator]
theorem metricProjectorOf_idempotent
    (s : MetricSide) (CIK : CertifiedInverseKernel E) :
    metricProjectorOf (E := E) s CIK * metricProjectorOf (E := E) s CIK
      = metricProjectorOf (E := E) s CIK := by
  cases s <;> simp [metricProjectorOf, CIK.metricProjector_idempotent, CIK.mpRangeProjector_idempotent]

/--
Certified modular reduction package for projector-controlled logarithmic lane
execution.

This is an interface object: support and anomaly laws are carried as certified
fields so downstream modules cannot apply `log`/`inverse`/entropy formulas to a
bare operator.
-/
@[rep_depth operator]
structure CertifiedModularReduction where
  Δ : EndH
  cik : CertifiedInverseKernel E

  -- analytic hooks
  logAdmissible : EndH → Prop
  logOn : {A : EndH} → logAdmissible A → EndH

  -- spectral lane
  hPreg_commutes_Δ : Commute cik.spectralProjector Δ
  logDomain : logAdmissible (compress cik.spectralProjector Δ)
  hRegularSpectrumPositive_to_logDomain :
    spectrum ℝ (compress cik.spectralProjector Δ) ⊆ Set.Ioi (0 : ℝ) →
      logAdmissible (compress cik.spectralProjector Δ)
  noLogOnDefect : ¬ logAdmissible (compress cik.spectralComplementaryProjector Δ)

  -- carrier lane
  hPregKrein : Commute cik.spectralProjector cik.GammaS

  -- metric lane
  metricSide : MetricSide
  hPmetricKrein : Commute (metricProjectorOf (E := E) metricSide cik) cik.GammaS

  -- certified execution laws
  hKambient_supported_on_Preg :
    let Kreg := -(logOn logDomain)
    let Kambient := compress cik.spectralProjector Kreg
    (cik.spectralProjector * Kambient = Kambient)
      ∧ (Kambient * cik.spectralProjector = Kambient)

  hKambient_kills_Pzero :
    let Kreg := -(logOn logDomain)
    let Kambient := compress cik.spectralProjector Kreg
    (cik.spectralComplementaryProjector * Kambient = 0)
      ∧ (Kambient * cik.spectralComplementaryProjector = 0)

  hKphys_supported_on_metric :
    let Kreg := -(logOn logDomain)
    let Kambient := compress cik.spectralProjector Kreg
    let Pmetric := metricProjectorOf (E := E) metricSide cik
    let Kphys := compress Pmetric Kambient
    (Pmetric * Kphys = Kphys)
      ∧ (Kphys * Pmetric = Kphys)

  hAnomaly_zero_iff_alignment :
    let anomaly :=
      match metricSide with
      | MetricSide.left => cik.chiralAnomaly
      | MetricSide.right => cik.rightChiralAnomaly
    let Pmetric := metricProjectorOf (E := E) metricSide cik
    anomaly = 0 ↔ Commute cik.spectralProjector Pmetric

namespace CertifiedModularReduction

variable (c : CertifiedModularReduction (E := E))

/-- Drazin regular projector lane. -/
@[rep_depth operator]
def Preg : EndH := c.cik.spectralProjector

/-- Drazin defect projector lane. -/
@[rep_depth operator]
def Pzero : EndH := c.cik.spectralComplementaryProjector

/-- Chosen metric projector lane. -/
@[rep_depth operator]
def Pmetric : EndH := metricProjectorOf (E := E) c.metricSide c.cik

/-- Regular compression of `Δ` on the Drazin support. -/
@[rep_depth operator]
def Δreg : EndH := compress (Preg c) c.Δ

/-- Regular logarithmic generator (analytic hook). -/
@[rep_depth operator]
def Kreg : EndH := -(c.logOn c.logDomain)

/-- Ambient support-compressed generator on the regular lane. -/
@[rep_depth operator]
def Kambient : EndH := compress (Preg c) (Kreg c)

/-- Physical generator after metric-lane projection. -/
@[rep_depth operator]
def Kphys : EndH := compress (Pmetric c) (Kambient c)

/-- Lane-selected anomaly observable. -/
@[rep_depth operator]
def anomaly : EndH :=
  match c.metricSide with
  | .left => c.cik.chiralAnomaly
  | .right => c.cik.rightChiralAnomaly

@[rep_depth operator]
def SpectralMetricAlignment : Prop :=
  Commute (Preg c) (Pmetric c)

/-- Spectral commutation certificate for `Preg` and `Δ`. -/
@[rep_depth operator]
theorem Preg_commutes :
    Commute (Preg c) c.Δ :=
  c.hPreg_commutes_Δ

/--
Functional-calculus readiness on the regular Drazin lane:
the logarithm domain certificate is available on `Δreg = Preg Δ Preg`.
-/
@[rep_depth operator]
theorem log_defined_on_Δreg :
    c.logAdmissible (Δreg c) := by
  simpa [Δreg, Preg] using c.logDomain

/--
Owner surface for regular-lane spectral positivity:
the spectrum of `Δreg` lies on the positive real axis.
-/
@[rep_depth operator]
def RegularSpectrumPositive : Prop :=
  spectrum ℝ (Δreg c) ⊆ Set.Ioi (0 : ℝ)

/--
Functional-calculus bridge law (owner form):
if regular-lane spectral positivity implies log-admissibility for this analytic
hook, then `Δreg` is log-admissible.
-/
@[rep_depth operator]
theorem log_defined_on_Δreg_of_regularSpectrumPositive
    (hPos : RegularSpectrumPositive c) :
    c.logAdmissible (Δreg c) := by
  simpa [Δreg, Preg] using c.hRegularSpectrumPositive_to_logDomain hPos

/-- `Kambient` is supported on `Preg` on both sides. -/
@[rep_depth operator]
theorem Kambient_supported_on_Preg :
    Preg c * Kambient c = Kambient c ∧ Kambient c * Preg c = Kambient c := by
  simpa [Preg, Kambient, Kreg, compress] using c.hKambient_supported_on_Preg

/-- `Kambient` annihilates the Drazin defect lane on both sides. -/
@[rep_depth operator]
theorem Kambient_kills_Pzero :
    Pzero c * Kambient c = 0 ∧ Kambient c * Pzero c = 0 := by
  simpa [Pzero, Kambient, Kreg, compress] using c.hKambient_kills_Pzero

/-- No analytic logarithm certificate is available on the pure defect compression. -/
@[rep_depth operator]
theorem no_log_on_zero_sector :
    ¬ c.logAdmissible (compress (Pzero c) c.Δ) :=
  c.noLogOnDefect

/-- `Kphys` is supported on the chosen metric lane on both sides. -/
@[rep_depth operator]
theorem Kphys_supported_on_metric :
    Pmetric c * Kphys c = Kphys c ∧ Kphys c * Pmetric c = Kphys c := by
  simpa [Pmetric, Kphys, Kambient, Kreg, compress] using c.hKphys_supported_on_metric

/--
Anomaly vanishes exactly when spectral and chosen metric lanes are aligned.
-/
@[rep_depth operator]
theorem anomaly_zero_iff_alignment :
    anomaly c = 0 ↔ SpectralMetricAlignment c := by
  simpa [anomaly, SpectralMetricAlignment, Preg, Pmetric, metricProjectorOf] using
    c.hAnomaly_zero_iff_alignment

/--
Named canonical surface for anomaly/support alignment:
`χ = 0` iff spectral and metric lanes are aligned.
-/
@[rep_depth operator]
theorem anomaly_vanishes_iff_alignment :
    anomaly c = 0 ↔ SpectralMetricAlignment c :=
  anomaly_zero_iff_alignment (c := c)

/--
Under spectral/metric alignment, the defect projector commutes with the chosen
metric projector.
-/
@[rep_depth operator]
theorem Pzero_commutes_Pmetric_of_alignment
    (hAlign : SpectralMetricAlignment c) :
    Commute (Pzero c) (Pmetric c) := by
  have hPzero :
      Pzero c = (1 : EndH) - Preg c := by
    simp [Pzero, Preg, CertifiedInverseKernel.spectralComplementaryProjector,
      CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
  exact
    calc
      Pzero c * Pmetric c
          = ((1 : EndH) - Preg c) * Pmetric c := by rw [hPzero]
      _ = Pmetric c - Preg c * Pmetric c := by simp [sub_mul]
      _ = Pmetric c - Pmetric c * Preg c := by rw [hAlign.eq]
      _ = Pmetric c * ((1 : EndH) - Preg c) := by simp [mul_sub]
      _ = Pmetric c * Pzero c := by rw [hPzero]

/--
Anomaly-closure law for the physical generator lane:
if `χ = 0` (alignment), then the metric-compressed generator has no defect
leakage across `Pzero`.
-/
@[rep_depth operator]
theorem Kphys_kills_Pzero_of_alignment
    (hχ : anomaly c = 0) :
    Pzero c * Kphys c = 0 ∧ Kphys c * Pzero c = 0 := by
  have hAlign : SpectralMetricAlignment c :=
    (anomaly_vanishes_iff_alignment (c := c)).mp hχ
  have hP0Pmetric : Commute (Pzero c) (Pmetric c) :=
    Pzero_commutes_Pmetric_of_alignment (c := c) hAlign
  have hKill : Pzero c * Kambient c = 0 ∧ Kambient c * Pzero c = 0 :=
    Kambient_kills_Pzero (c := c)
  constructor
  · calc
      Pzero c * Kphys c
          = Pzero c * (Pmetric c * Kambient c * Pmetric c) := by
              rfl
      _ = (Pzero c * Pmetric c) * Kambient c * Pmetric c := by simp [mul_assoc]
      _ = (Pmetric c * Pzero c) * Kambient c * Pmetric c := by
            rw [hP0Pmetric.eq]
      _ = Pmetric c * (Pzero c * Kambient c) * Pmetric c := by simp [mul_assoc]
      _ = 0 := by simp [hKill.1]
  · calc
      Kphys c * Pzero c
          = (Pmetric c * Kambient c * Pmetric c) * Pzero c := by
              rfl
      _ = Pmetric c * Kambient c * (Pmetric c * Pzero c) := by simp [mul_assoc]
      _ = Pmetric c * Kambient c * (Pzero c * Pmetric c) := by
            rw [hP0Pmetric.eq]
      _ = Pmetric c * (Kambient c * Pzero c) * Pmetric c := by simp [mul_assoc]
      _ = 0 := by simp [hKill.2]

/-- Flat/inertial regular lane: anomaly is cancelled. -/
@[rep_depth operator]
def InertialRegularLane : Prop := anomaly c = 0

/-- Curved regular lane: anomaly is not cancelled. -/
@[rep_depth operator]
def CurvedRegularLane : Prop := anomaly c ≠ 0

/-- Inertial lane is exactly spectral/metric alignment. -/
@[rep_depth operator]
theorem inertial_regular_lane_iff_alignment :
    InertialRegularLane c ↔ SpectralMetricAlignment c :=
  anomaly_vanishes_iff_alignment (c := c)

/-- Curved lane is exactly failure of spectral/metric alignment. -/
@[rep_depth operator]
theorem curved_regular_lane_iff_non_alignment :
    CurvedRegularLane c ↔ ¬ SpectralMetricAlignment c := by
  constructor
  · intro hCurved hAlign
    exact hCurved ((anomaly_vanishes_iff_alignment (c := c)).2 hAlign)
  · intro hNonAlign hZero
    exact hNonAlign ((anomaly_vanishes_iff_alignment (c := c)).1 hZero)

/-- Inertial-lane form of the no-defect-leakage law for `Kphys`. -/
@[rep_depth operator]
theorem Kphys_kills_Pzero_of_inertial_regular_lane
    (hInertial : InertialRegularLane c) :
    Pzero c * Kphys c = 0 ∧ Kphys c * Pzero c = 0 :=
  Kphys_kills_Pzero_of_alignment (c := c) hInertial

/--
Support-restricted modular Lie derivation generated by the ambient regularized
modular Hamiltonian `Kambient`.
-/
@[rep_depth operator]
noncomputable def modularLieDerivation : EndH →ₗ[ℝ] EndH :=
  { toFun := fun A => ⁅Kambient c, A⁆
    map_add' := by
      intro A B
      simp [Ring.lie_def, add_mul, mul_add, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm]
    map_smul' := by
      intro r A
      simp [Ring.lie_def, sub_eq_add_neg] }

@[rep_depth operator, simp]
theorem modularLieDerivation_apply
    (A : EndH) :
    modularLieDerivation (c := c) A = ⁅Kambient c, A⁆ := rfl

/-- Diagonal nested modular Lie variation generated by `Kambient`. -/
@[rep_depth operator]
noncomputable def modularLieHessian (A : EndH) : EndH :=
  modularLieDerivation (c := c) (modularLieDerivation (c := c) A)

@[rep_depth operator, simp]
theorem modularLieHessian_eq_nested_commutator
    (A : EndH) :
    modularLieHessian (c := c) A = ⁅Kambient c, ⁅Kambient c, A⁆⁆ := by
  simp [modularLieHessian, modularLieDerivation_apply]

/-- Support-restricted modular transport orbit generated by `Kambient`. -/
@[rep_depth operator]
noncomputable def modularTransportedObservable
    (A : EndH) (t : ℝ) : EndH :=
  expTransport (Kambient c) A t

/--
The infinitesimal generator of the support-restricted modular transport orbit
is the modular Lie derivation.
-/
@[rep_depth operator]
theorem deriv_modularTransportedObservable_at_zero
    (A : EndH) :
    deriv (fun t => modularTransportedObservable (c := c) A t) 0
      = modularLieDerivation (c := c) A := by
  simpa [modularTransportedObservable, modularLieDerivation_apply] using
    (deriv_expTransport_at_zero (A := EndH) (X := Kambient c) (A₀ := A))

/--
The second infinitesimal modular transport variation is the diagonal nested
modular Lie commutator.
-/
@[rep_depth operator]
theorem deriv2_modularTransportedObservable_at_zero
    (A : EndH) :
    deriv (fun t => deriv (fun s => modularTransportedObservable (c := c) A s) t) 0
      = modularLieHessian (c := c) A := by
  let K := Kambient c
  let δA := ⁅K, A⁆
  have hDeriv :
      (fun t => deriv (fun s => modularTransportedObservable (c := c) A s) t)
        = fun t => expTransport K δA t := by
    funext t
    simpa [K, δA, modularTransportedObservable] using
      (hasDerivAt_expTransport (A := EndH) (X := K) (A₀ := A) t).deriv
  rw [hDeriv]
  have hSecond :
      deriv (fun t => expTransport K δA t) 0 = ⁅K, δA⁆ := by
    simpa using (deriv_expTransport_at_zero (A := EndH) (X := K) (A₀ := δA))
  simpa [K, δA, modularLieHessian, modularLieDerivation_apply] using hSecond

/--
Gauge shifts by scalar multiples of the identity do not change the modular Lie
derivation.
-/
@[rep_depth operator]
theorem modularLieDerivation_gaugeShift
    (τ : ℝ) (A : EndH) :
    ⁅Kambient c + τ • (1 : EndH), A⁆ = modularLieDerivation (c := c) A := by
  simp [modularLieDerivation_apply, Ring.lie_def, sub_eq_add_neg, add_mul, mul_add,
    add_assoc, add_left_comm, add_comm]

/--
Gauge shifts by scalar multiples of the identity leave the diagonal nested
modular Lie variation unchanged.
-/
@[rep_depth operator]
theorem modularLieHessian_gaugeShift
    (τ : ℝ) (A : EndH) :
    ⁅Kambient c + τ • (1 : EndH), ⁅Kambient c + τ • (1 : EndH), A⁆⁆
      = modularLieHessian (c := c) A := by
  rw [modularLieDerivation_gaugeShift (c := c) (τ := τ)
    (A := ⁅Kambient c + τ • (1 : EndH), A⁆)]
  rw [modularLieDerivation_gaugeShift (c := c) (τ := τ) (A := A)]
  simp [modularLieHessian_eq_nested_commutator]

end CertifiedModularReduction

end InfoGeometry.Canonical
