import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.InverseKernelNormalForm
import InfoGeometry.Canonical.DrazinKreinCompatibility
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

end CertifiedModularReduction

end InfoGeometry.Canonical
