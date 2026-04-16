import InfoGeometry.Canonical.ModularHamiltonianDoubledBridge
import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

Support-restricted bridge from the canonical doubled Tomita package to the
`Preg/Pzero` execution lane.

This file does not redefine the modular Hamiltonian. It only proves that the
certified support-restricted lane is an explicit compression of the same
canonical `Δ/δ` package.
-/

namespace InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ModularSuperchargeClosure
open InfoGeometry.Canonical.ModularHamiltonianDoubledBridge

section Core

variable {V : Type 0}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

local notation "H₂" => DoubledSpace V
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
If the certified reduction is instantiated with the canonical Tomita `Δ`,
its regular compression is exactly the `Preg`-compression of that `Δ`.
-/
@[rep_depth krein]
theorem Delta_reg_eq_compress_Preg_canonicalDelta
    (c : CertifiedModularReduction (E := H₂))
    (hDelta : c.Δ = (canonicalTomitaLogData (E := V) c.cik).Delta) :
    c.Δreg
      = compress (CertifiedModularReduction.Preg c)
          ((canonicalTomitaLogData (E := V) c.cik).Delta) := by
  simp [CertifiedModularReduction.Δreg, hDelta]

/--
Equivalent regular-lane form with explicit exponential witness `Δ = exp(δ)`.
-/
@[rep_depth krein]
theorem Delta_reg_eq_compress_Preg_exp_canonicalDeltaLog
    (c : CertifiedModularReduction (E := H₂))
    (hDelta : c.Δ = (canonicalTomitaLogData (E := V) c.cik).Delta) :
    c.Δreg
      = compress (CertifiedModularReduction.Preg c)
          (NormedSpace.exp ((canonicalTomitaLogData (E := V) c.cik).deltaLog)) := by
  calc
    c.Δreg
        = compress (CertifiedModularReduction.Preg c)
            ((canonicalTomitaLogData (E := V) c.cik).Delta) :=
          Delta_reg_eq_compress_Preg_canonicalDelta (V := V) (c := c) hDelta
    _ = compress (CertifiedModularReduction.Preg c)
          (NormedSpace.exp ((canonicalTomitaLogData (E := V) c.cik).deltaLog)) := by
          rw [InfoGeometry.Canonical.ModularHamiltonianDoubledBridge.canonicalTomitaLogData_Delta_eq_exp_deltaLog
            (E := V) (CIK := c.cik)]

/--
If the certified logarithm hook is instantiated by canonical Tomita `δ`, the
ambient support-restricted generator is exactly the compressed `-δ`.
-/
@[rep_depth krein]
theorem Kambient_eq_compress_Preg_neg_canonicalDeltaLog
    (c : CertifiedModularReduction (E := H₂))
    (hLog : c.logOn c.logDomain = (canonicalTomitaLogData (E := V) c.cik).deltaLog) :
    c.Kambient
      = compress (CertifiedModularReduction.Preg c)
          (-((canonicalTomitaLogData (E := V) c.cik).deltaLog)) := by
  simp [CertifiedModularReduction.Kambient, CertifiedModularReduction.Kreg, hLog]

/--
`Preg/Pzero` support package specialized to canonical Tomita `δ` on the
certified reduction lane.
-/
@[rep_depth krein]
theorem canonicalTomita_support_package_on_Preg_of_certifiedReduction
    (c : CertifiedModularReduction (E := H₂))
    (hLog : c.logOn c.logDomain = (canonicalTomitaLogData (E := V) c.cik).deltaLog) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (-((canonicalTomitaLogData (E := V) c.cik).deltaLog))
    (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0) := by
  intro KambientCanonical
  have hEq : c.Kambient = KambientCanonical := by
    simpa [KambientCanonical] using
      (Kambient_eq_compress_Preg_neg_canonicalDeltaLog
        (V := V) (c := c) hLog)
  have hSupp := c.Kambient_supported_on_Preg
  have hKill := c.Kambient_kills_Pzero
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hEq] using hSupp.1
  · simpa [hEq] using hSupp.2
  · simpa [hEq] using hKill.1
  · simpa [hEq] using hKill.2

/--
Defect-lane logarithm exclusion specialized to the same certified reduction.
-/
@[rep_depth krein]
theorem canonicalTomita_no_log_on_Pzero_of_certifiedReduction
    (c : CertifiedModularReduction (E := H₂)) :
    ¬ c.logAdmissible
      (compress (CertifiedModularReduction.Pzero c) c.Δ) :=
  c.no_log_on_zero_sector

/--
Metric-lane physical compression specialized to canonical Tomita `δ`.
-/
@[rep_depth krein]
theorem Kphys_eq_metric_compress_of_canonicalTomita
    (c : CertifiedModularReduction (E := H₂))
    (hLog : c.logOn c.logDomain = (canonicalTomitaLogData (E := V) c.cik).deltaLog) :
    c.Kphys
      = compress (CertifiedModularReduction.Pmetric c)
          (compress (CertifiedModularReduction.Preg c)
            (-((canonicalTomitaLogData (E := V) c.cik).deltaLog))) := by
  simp [CertifiedModularReduction.Kphys, CertifiedModularReduction.Kambient,
    CertifiedModularReduction.Kreg, hLog]

end Core

end InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
