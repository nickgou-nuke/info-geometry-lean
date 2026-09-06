import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

Support-restricted bridge from the canonical doubled Tomita package to the
`Preg/Pzero` execution lane.

This file does not redefine the modular Hamiltonian. It only proves that the
property support-restricted lane is an explicit compression of the same
canonical `Δ/δ` package.
-/

namespace InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
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
Support-restricted logarithm is defined on the regular Drazin lane `Preg Δ`.

This is the property bridge form of the usual analytic precondition for
`K := -log (Preg Δ)`.
-/
@[rep_depth operator]
theorem log_defined_on_Preg
    (c : CertifiedModularReduction (E := H₂)) :
    c.logAdmissible
      (compress (CertifiedModularReduction.Preg c) c.Δ) :=
  c.logDomain

/--
Equivalent regular-lane form of the same property:
the logarithm is admitted on `Δreg = Preg Δ Preg`.
-/
@[rep_depth operator]
theorem log_defined_on_Δreg
    (c : CertifiedModularReduction (E := H₂)) :
    c.logAdmissible c.Δreg := by
  simpa [CertifiedModularReduction.Δreg, CertifiedModularReduction.Preg] using
    (log_defined_on_Preg (V := V) c)

/--
Regular-lane spectral positivity implies the same `Preg` log-domain property,
provided by the Hestenes--Krein bridge law encoded in
`CertifiedModularReduction`.
-/
@[rep_depth operator]
theorem log_defined_on_Preg_of_regularSpectrumPositive
    (c : CertifiedModularReduction (E := H₂))
    (hPos : CertifiedModularReduction.RegularSpectrumPositive (c := c)) :
    c.logAdmissible
      (compress (CertifiedModularReduction.Preg c) c.Δ) := by
  simpa [CertifiedModularReduction.Δreg, CertifiedModularReduction.Preg] using
    (CertifiedModularReduction.log_defined_on_Δreg_of_regularSpectrumPositive
      (c := c) hPos)

/--
Explicit support-restricted modular generator:
`K := -log (Preg Δ)` in property lane form.
-/
@[rep_depth operator]
noncomputable def K_neg_log_PregDelta
    (c : CertifiedModularReduction (E := H₂)) : EndH :=
  -(c.logOn c.logDomain)

/--
`K_neg_log_PregDelta` is definitionally the property regular generator `Kreg`.
-/
@[rep_depth operator]
theorem K_neg_log_PregDelta_eq_Kreg
    (c : CertifiedModularReduction (E := H₂)) :
    K_neg_log_PregDelta (V := V) c = c.Kreg := rfl

/--
`Kambient` is the `Preg`-compression of the canonical
`K := -logOn(logDomain)` regular generator.
-/
@[rep_depth operator]
theorem Kambient_eq_compress_Preg_K_neg_log_PregDelta
    (c : CertifiedModularReduction (E := H₂)) :
    c.Kambient
      = compress (CertifiedModularReduction.Preg c)
          (K_neg_log_PregDelta (V := V) c) := by
  rfl

/--
Support laws for the canonical support-restricted generator lane with no extra
compatibility wrappers:
- `Preg` supports `Kambient` on both sides,
- `Pzero` annihilates `Kambient` on both sides.
-/
@[rep_depth operator]
theorem K_neg_log_PregDelta_support_package
    (c : CertifiedModularReduction (E := H₂)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (K_neg_log_PregDelta (V := V) c)
    (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0) := by
  intro KambientCanonical
  have hEq : c.Kambient = KambientCanonical := by
    simpa [KambientCanonical] using
      (Kambient_eq_compress_Preg_K_neg_log_PregDelta (V := V) (c := c))
  have hSupp := c.Kambient_supported_on_Preg
  have hKill := c.Kambient_kills_Pzero
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hEq] using hSupp.1
  · simpa [hEq] using hSupp.2
  · simpa [hEq] using hKill.1
  · simpa [hEq] using hKill.2

/--
If the property reduction is instantiated with the canonical Tomita `Δ`,
its regular compression is exactly the `Preg`-compression of that `Δ`.
-/
@[rep_depth krein]
theorem Delta_reg_eq_compress_Preg_canonicalDelta
    (c : CertifiedModularReduction (E := H₂))
    (Δcanon : EndH)
    (hDelta : c.Δ = Δcanon) :
    c.Δreg
      = compress (CertifiedModularReduction.Preg c)
          Δcanon := by
  simp [CertifiedModularReduction.Δreg, hDelta]

/--
Equivalent regular-lane form with explicit exponential property `Δ = exp(δ)`.
-/
@[rep_depth krein]
theorem Delta_reg_eq_compress_Preg_exp_canonicalDeltaLog
    (c : CertifiedModularReduction (E := H₂))
    (Δcanon δcanon : EndH)
    (hDelta : c.Δ = Δcanon)
    (hDeltaExp : Δcanon = NormedSpace.exp δcanon) :
    c.Δreg
      = compress (CertifiedModularReduction.Preg c)
          (NormedSpace.exp δcanon) := by
  calc
    c.Δreg
        = compress (CertifiedModularReduction.Preg c)
            Δcanon :=
          Delta_reg_eq_compress_Preg_canonicalDelta
            (V := V) (c := c) Δcanon hDelta
    _ = compress (CertifiedModularReduction.Preg c)
          (NormedSpace.exp δcanon) := by
          rw [hDeltaExp]

/--
If the property logarithm hook is instantiated by canonical Tomita `δ`, the
ambient support-restricted generator is exactly the compressed `-δ`.
-/
@[rep_depth krein]
theorem Kambient_eq_compress_Preg_neg_canonicalDeltaLog
    (c : CertifiedModularReduction (E := H₂))
    (δcanon : EndH)
    (hLog : c.logOn c.logDomain = δcanon) :
    c.Kambient
      = compress (CertifiedModularReduction.Preg c)
          (-δcanon) := by
  simp [CertifiedModularReduction.Kambient, CertifiedModularReduction.Kreg, hLog]

/--
`Preg/Pzero` support package specialized to canonical Tomita `δ` on the
property reduction lane.
-/
@[rep_depth krein]
theorem canonicalTomita_support_package_on_Preg_of_propertyReduction
    (c : CertifiedModularReduction (E := H₂))
    (δcanon : EndH)
    (hLog : c.logOn c.logDomain = δcanon) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (-δcanon)
    (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0) := by
  intro KambientCanonical
  have hEq : c.Kambient = KambientCanonical := by
    simpa [KambientCanonical] using
      (Kambient_eq_compress_Preg_neg_canonicalDeltaLog
        (V := V) (c := c) δcanon hLog)
  have hSupp := c.Kambient_supported_on_Preg
  have hKill := c.Kambient_kills_Pzero
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hEq] using hSupp.1
  · simpa [hEq] using hSupp.2
  · simpa [hEq] using hKill.1
  · simpa [hEq] using hKill.2

/--
Defect-lane logarithm exclusion specialized to the same property reduction.
-/
@[rep_depth krein]
theorem canonicalTomita_no_log_on_Pzero_of_propertyReduction
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
    (δcanon : EndH)
    (hLog : c.logOn c.logDomain = δcanon) :
    c.Kphys
      = compress (CertifiedModularReduction.Pmetric c)
          (compress (CertifiedModularReduction.Preg c)
            (-δcanon)) := by
  simp [CertifiedModularReduction.Kphys, CertifiedModularReduction.Kambient,
    CertifiedModularReduction.Kreg, hLog]

end Core

end InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
