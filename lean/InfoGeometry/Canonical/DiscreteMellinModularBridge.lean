import InfoGeometry.Canonical.OperatorLightconeCoordinates
import InfoGeometry.Canonical.ModularHamiltonianDoubledBridge
import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.DiscreteModularSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# Discrete Mellin / Modular Bridge

Conservative operatorial bridge for the Fourier-to-Mellin intuition:

* additive rapidity samples `η₀ + k Δη`,
* logarithmic position samples `exp(η₀ + k Δη)`,
* light-cone boost scaling by those exponential samples.

This module is coordinate-free. Finite-dimensional scalar diagonal matrices 
are NOT allowed. The "diagonal" Hamiltonian is represented as a spectral 
sum of projectors in the operator algebra.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.DiscreteMellinModularBridge

open InfoGeometry.Canonical.OperatorLightconeCoordinates
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.DiscreteModularSpectrum

section LogSampling

/-- Additive rapidity grid point. -/
@[rep_depth transport]
noncomputable def discreteRapidity (η0 Δη : ℝ) (k : ℤ) : ℝ :=
  η0 + (k : ℝ) * Δη

/-- Logarithmic sample point `x_k = exp(η₀ + k Δη)`. -/
@[rep_depth transport]
noncomputable def logarithmicSample (η0 Δη : ℝ) (k : ℤ) : ℝ :=
  Real.exp (discreteRapidity η0 Δη k)

/-- The logarithm of the logarithmic sample is the additive rapidity coordinate. -/
@[rep_depth transport]
theorem log_logarithmicSample (η0 Δη : ℝ) (k : ℤ) :
    Real.log (logarithmicSample η0 Δη k) = discreteRapidity η0 Δη k := by
  simp [logarithmicSample]

/--
Successive logarithmic samples differ by the fixed multiplicative scale
`exp Δη`.
-/
@[rep_depth transport]
theorem logarithmicSample_succ_eq_exp_mul (η0 Δη : ℝ) (k : ℤ) :
    logarithmicSample η0 Δη (k + 1)
      = Real.exp Δη * logarithmicSample η0 Δη k := by
  rw [logarithmicSample, logarithmicSample, discreteRapidity, discreteRapidity]
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

end LogSampling

section LightconeRapidity

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
On the `+` light-cone channel, discrete Mellin/log samples are exactly the
Lorentz boost scale factors.
-/
@[rep_depth transport]
theorem rapidityPlusCoordinate_eq_logarithmicSample_mul_lightconePlus
    (ψ : H₂) (η0 Δη : ℝ) (k : ℤ) :
    rapidityPlusCoordinate (E := E) ψ (discreteRapidity η0 Δη k)
      = logarithmicSample η0 Δη k * lightconePlusCoordinate (E := E) ψ := by
  rw [rapidityPlusCoordinate_eq_exp_mul_lightconePlus]
  rfl

/--
On the `-` light-cone channel, the same rapidity sample acts by the inverse
scale factor.
-/
@[rep_depth transport]
theorem rapidityMinusCoordinate_eq_exp_neg_discreteRapidity_mul_lightconeMinus
    (ψ : H₂) (η0 Δη : ℝ) (k : ℤ) :
    rapidityMinusCoordinate (E := E) ψ (discreteRapidity η0 Δη k)
      =
    Real.exp (-(discreteRapidity η0 Δη k))
      * lightconeMinusCoordinate (E := E) ψ := by
  rw [rapidityMinusCoordinate_eq_exp_neg_mul_lightconeMinus]

end LightconeRapidity

section OperatorialModularHamiltonian

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Proof-carrying operatorial discrete modular Hamiltonian.

The intended analytic expression is the spectral series
`∑ k, (η₀ + k Δη) Pₖ`, but this file does not assert convergence of an
infinite operator sum.  A concrete model must provide the operator `H` and the
spectral-projector commutation gate.
-/
@[rep_depth operator]
structure OperatorialDiscreteModularHamiltonianContext
    (η0 Δη : ℝ) (P : ℤ → EndH) where
  H : EndH
  commutes_spectralProjectors : ∀ k : ℤ, Commute H (P k)

/-- The carried operatorial Hamiltonian commutes with its certified spectral projectors. -/
@[rep_depth operator]
theorem modularHamiltonian_commutes_spectralProjectors
    {η0 Δη : ℝ} {P : ℤ → EndH}
    (M : OperatorialDiscreteModularHamiltonianContext (E := E) η0 Δη P)
    (k : ℤ) :
    Commute M.H (P k) :=
  M.commutes_spectralProjectors k

end OperatorialModularHamiltonian

end InfoGeometry.Canonical.DiscreteMellinModularBridge
