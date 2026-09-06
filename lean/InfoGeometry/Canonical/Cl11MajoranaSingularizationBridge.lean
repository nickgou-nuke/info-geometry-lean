import InfoGeometry.Canonical.Cl11MajoranaModularBridge
import InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Cl(1,1) Majorana support bridge

This owner connects the native doubled Majorana `K = J ε` operator to the
existing `Preg/Pzero` singularization lane.  The reduction datum remains the
repository owner of its support and logarithm domains; this file only supplies
the exact finite-dimensional operator identification and transports the
already-proved support laws.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11MajoranaSingularizationBridge

open InfoGeometry.Krein
open InfoGeometry.Quantum.RealMajoranaCategory
open InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private noncomputable abbrev cl11KContinuous :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  LinearMap.toContinuousLinearMap (cl11DoubledCore E).K

/-- The continuous finite-dimensional realization of the Majorana Cartan
operator is the native modular `J` followed by the native spectral sign. -/
@[rep_depth krein]
theorem cl11KContinuous_eq_modular_j_comp_spectral_epsilon :
    cl11KContinuous (E := E) =
      (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T => T v)
    (cl11DoubledCore_K_eq_modular_j_comp_spectral_epsilon (E := E))
  simpa [cl11KContinuous, ContinuousLinearMap.comp_apply] using h

/-- If the certified logarithmic hook is the native Cl(1,1) Majorana
operator, its regularized ambient generator is supported on `Preg` and
annihilates the `Pzero` defect sector. -/
@[rep_depth krein, capstone]
theorem cl11Majorana_regularization_support_package
    (c : CertifiedModularReduction (E := DoubledSpace E))
    (hLog : c.logOn c.logDomain = cl11KContinuous (E := E)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (-(cl11KContinuous (E := E)))
    (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0) := by
  simpa only [cl11KContinuous] using
    (canonicalTomita_support_package_on_Preg_of_certifiedReduction
      (V := E) c
      (LinearMap.toContinuousLinearMap (cl11DoubledCore E).K) hLog)

end FiniteDimensional

end InfoGeometry.Canonical.Cl11MajoranaSingularizationBridge

end
