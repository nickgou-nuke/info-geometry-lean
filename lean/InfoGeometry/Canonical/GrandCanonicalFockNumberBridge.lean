import InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge
import InfoGeometry.Canonical.BogoliubovFockSuper

/-!
# InfoGeometry.Canonical.GrandCanonicalFockNumberBridge

Fock-side particle-number bridge for the grand-canonical chemical potential.

The finite owner lane has `E - μN` in `GrandCanonicalGaugePotentialBridge`.
The Fock owner lane already has
`grandCanonicalFockGenerator B H μ = H - μ • numberOperator B`.

This file records the exact shared algebraic form without asserting that finite
count profiles and Fock number operators are definitionally equal.
-/

namespace InfoGeometry.Canonical.GrandCanonicalFockNumberBridge

open InfoGeometry.Canonical.BogoliubovFockSuper

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chemical-potential background gauge coupling to the Bogoliubov number operator. -/
@[rep_depth thermo]
noncomputable def fockNumberGauge
    (B : BogoliubovMixingParams) : WeylGaugeField ℝ (FockEndomorphism E) where
  gaugeOf μ := μ • bogoliubovNumberOperator (E := E) B

/-- Pointwise expansion of the Fock number gauge coupling. -/
@[simp]
theorem fockNumberGauge_apply
    (B : BogoliubovMixingParams) (μ : ℝ) :
    (fockNumberGauge (E := E) B).gaugeOf μ =
      μ • bogoliubovNumberOperator (E := E) B := by
  rfl

/-- Zero chemical potential removes the Fock number coupling. -/
@[rep_depth thermo]
theorem fockNumberGauge_zero
    (B : BogoliubovMixingParams) :
    (fockNumberGauge (E := E) B).gaugeOf 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [fockNumberGauge]

/-- Fock number gauge couplings compose additively in the chemical potential. -/
@[rep_depth thermo]
theorem fockNumberGauge_add
    (B : BogoliubovMixingParams) (μ ν : ℝ) :
    (fockNumberGauge (E := E) B).gaugeOf (μ + ν) =
      (fockNumberGauge (E := E) B).gaugeOf μ
        + (fockNumberGauge (E := E) B).gaugeOf ν := by
  apply ContinuousLinearMap.ext
  intro v
  simp [fockNumberGauge, add_smul]

/--
The Fock grand-canonical generator is exactly the Hamiltonian minus the
chemical-potential gauge coupling to the Bogoliubov number operator.
-/
@[rep_depth thermo]
theorem grandCanonicalFockGenerator_eq_hamiltonian_sub_fockNumberGauge
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) (μ : ℝ) :
    grandCanonicalFockGenerator (E := E) B H μ =
      H - (fockNumberGauge (E := E) B).gaugeOf μ := by
  rfl

/--
The Fock bridge uses the same affine thermodynamic form as the finite
grand-canonical bridge: background parameter times number object.
-/
@[rep_depth thermo]
theorem fockNumberGauge_is_mu_times_numberOperator
    (B : BogoliubovMixingParams) (μ : ℝ) :
    (fockNumberGauge (E := E) B).gaugeOf μ =
      μ • bogoliubovNumberOperator (E := E) B := by
  rfl

/--
At zero chemical potential, the grand-canonical Fock generator collapses to the
bare Hamiltonian.
-/
@[rep_depth thermo]
theorem grandCanonicalFockGenerator_zero_mu
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) :
    grandCanonicalFockGenerator (E := E) B H 0 = H := by
  rw [grandCanonicalFockGenerator_eq_hamiltonian_sub_fockNumberGauge]
  rw [fockNumberGauge_zero]
  apply ContinuousLinearMap.ext
  intro v
  simp

end InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
