import InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Canonical.AlgebraicKMSStateColimit
import InfoGeometry.Canonical.PrimonThermodynamicColimit

/-!
# Native Riemann/Hestenes/Krein thermodynamic bridge

This owner contains only finite or algebraic readouts already proved by the
repository owners.  The real doubled Hestenes phase axis is `clockAxis`, the
completed-zeta reflection is the existing `riemannXi_one_sub` theorem, the
Gibbs readout is descended through the native filtered colimit, and the
operatorial thermal boundary is the noncommutative KMS identity.

No scalar stand-in for a Krein operator, no global logarithm of `xi`, and no
analytic or thermodynamic-limit claim is introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannMetriplecticBilingualSynthesis

open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics
open InfoGeometry.Canonical.BilingualRealHestenesDictionary
open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open InfoGeometry.Canonical.PrimonThermodynamicColimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Krein

/-! ## Hestenes/Krein phase channel -/

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The real phase/complex-structure axis on the doubled carrier. -/
def phaseAxis : H₂ →L[ℝ] H₂ :=
  clockAxis (E := E)

@[simp]
theorem phaseAxis_sq :
    (phaseAxis (E := E)).comp (phaseAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂) := by
  exact clockAxis_sq (E := E)

theorem modular_sign_anticommute :
    (modular_j (E := E)).comp (spectral_epsilon (E := E)) =
      -((spectral_epsilon (E := E)).comp (modular_j (E := E))) := by
  exact modular_j_spectral_epsilon_anticommute E

/-! ## Completed-zeta reflection channel -/

/-- The completed xi readout is Weyl invariant. -/
theorem completedXi_reflection (s : ℂ) :
    riemannXi (1 - s) = riemannXi s :=
  riemannXi_one_sub s

/-- The concrete antiunitary fixed locus is the critical line. -/
theorem antiunitary_fixed_iff_criticalLine (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s = s ↔
      CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s := by
  exact completedAntiunitaryReflection_fixed_iff_criticalLine s

/-! ## Filtered Gibbs colimit -/

theorem Gibbs_colimit_readout_on_stage
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) (f : DiagAlg n) :
    gibbsExpectationColimit primes β
        ((colimit.ι primonThermoModuleDiagram n).hom f) =
      expectedValue primes β n f := by
  exact gibbsExpectationColimit_on_stage primes β n f

theorem Gibbs_colimit_readout_unique
    (primes : ℕ → ℕ) (β : ℝ)
    (F : primonThermoColimit →ₗ[ℂ] ℂ)
    (hF : ∀ (n : ℕ) (f : DiagAlg n),
      F ((colimit.ι primonThermoModuleDiagram n).hom f) =
        expectedValue primes β n f) :
    F = gibbsExpectationColimit primes β := by
  exact gibbsExpectationColimit_unique primes β F hF

/-! ## Noncommutative KMS boundary -/

theorem KMS_boundary
    (δ : Carrierˣ) (x y : Carrier) :
    deltaWeightedFunctional δ (x * y) =
      deltaWeightedFunctional δ
        (y * deltaImaginaryTimeAlgEquiv δ x) := by
  exact deltaWeightedFunctional_kms δ x y

end InfoGeometry.Arithmetic.RiemannMetriplecticBilingualSynthesis

end noncomputable section
