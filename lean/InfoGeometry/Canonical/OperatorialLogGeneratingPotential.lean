import InfoGeometry.Canonical.InformationPartitionCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.OperatorialLogGeneratingPotential

Concrete theorem-rooted log-generating potentials for bounded operatorial
exponential families.

The scalar log-generating potential is not an extra witness field.  It is the
logarithm of a scalar readout applied to a bounded operator exponential:

`Φ_K(τ) = log (ω (exp (τ • K)))`.

For modular thermodynamic convention `β ↦ exp(-β • K)`, this file also exposes
the beta form:

`Φ_K^β(β) = log (ω (exp ((-β) • K)))`.

No trace, KMS state, density-matrix normalization, or type-I partition
function is assumed.  The only scalarization is the supplied continuous linear
readout `ω`.
-/

namespace InfoGeometry.Canonical.OperatorialLogGeneratingPotential

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedRing (EndH E) := inferInstance
noncomputable local instance : NormedAlgebra ℝ (EndH E) := inferInstance
noncomputable local instance : NormedSpace ℝ (EndH E) := inferInstance
local instance : IsTopologicalRing (EndH E) := inferInstance
local instance : CompleteSpace (EndH E) := inferInstance

/-- Concrete scalar partition/readout of the bounded operator exponential. -/
@[rep_depth operator]
noncomputable def operatorialPartitionReadout
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) : ℝ :=
  informationPartitionFunction ω K τ

/-- Concrete scalar log-generating potential `Φ_K(τ)=log(ω(exp(τK)))`. -/
@[rep_depth operator]
noncomputable def operatorialLogGeneratingPotential
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) : ℝ :=
  logInformationPartitionFunction ω K τ

/-- Readback: the partition readout is exactly `ω(exp(τ • K))`. -/
@[rep_depth operator]
theorem operatorialPartitionReadout_eq_readout_exp
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) :
    operatorialPartitionReadout (E := E) ω K τ = ω (NormedSpace.exp (τ • K)) := by
  rfl

/-- Readback: the log-generating potential is `log(ω(exp(τ • K)))`. -/
@[rep_depth operator]
theorem operatorialLogGeneratingPotential_eq_log_readout_exp
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) :
    operatorialLogGeneratingPotential (E := E) ω K τ =
      Real.log (ω (NormedSpace.exp (τ • K))) := by
  rfl

/-- At `τ=0`, the partition readout is the readout of the identity. -/
@[simp, rep_depth operator]
theorem operatorialPartitionReadout_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    operatorialPartitionReadout (E := E) ω K 0 = ω (1 : EndH E) := by
  simp [operatorialPartitionReadout]

/-- At `τ=0`, the log-generating potential is `log(ω 1)`. -/
@[simp, rep_depth operator]
theorem operatorialLogGeneratingPotential_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    operatorialLogGeneratingPotential (E := E) ω K 0 = Real.log (ω (1 : EndH E)) := by
  simp [operatorialLogGeneratingPotential, logInformationPartitionFunction]

/-- At `τ=1`, the partition readout is the readout of `exp K`. -/
@[simp, rep_depth operator]
theorem operatorialPartitionReadout_one
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    operatorialPartitionReadout (E := E) ω K 1 = ω (NormedSpace.exp K) := by
  simp [operatorialPartitionReadout]

/-- First derivative of `Z_K(τ)=ω(exp(τK))` at zero. -/
@[rep_depth operator]
theorem hasDerivAt_operatorialPartitionReadout_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    HasDerivAt (fun τ : ℝ => operatorialPartitionReadout (E := E) ω K τ) (ω K) 0 := by
  simpa [operatorialPartitionReadout] using
    hasDerivAt_informationPartitionFunction_zero (ω := ω) (K := K)

/--
First derivative of the log-generating potential at zero under the
nondegeneracy condition `ω 1 ≠ 0`.
-/
@[rep_depth operator]
theorem hasDerivAt_operatorialLogGeneratingPotential_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) ≠ 0) :
    HasDerivAt (fun τ : ℝ => operatorialLogGeneratingPotential (E := E) ω K τ)
      ((ω (1 : EndH E))⁻¹ * ω K) 0 := by
  simpa [operatorialLogGeneratingPotential] using
    hasDerivAt_logInformationPartitionFunction_zero (ω := ω) (K := K) hω1

/-- Normalized readout specialization: if `ω 1 = 1`, then `Φ'_K(0)=ω K`. -/
@[rep_depth operator]
theorem hasDerivAt_operatorialLogGeneratingPotential_zero_of_normalized
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) = 1) :
    HasDerivAt (fun τ : ℝ => operatorialLogGeneratingPotential (E := E) ω K τ)
      (ω K) 0 := by
  simpa [operatorialLogGeneratingPotential] using
    hasDerivAt_logInformationPartitionFunction_zero_of_normalized
      (ω := ω) (K := K) hω1

/-- Modular beta partition readout for the convention `β ↦ exp(-βK)`. -/
@[rep_depth operator]
noncomputable def modularBetaPartitionReadout
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (β : ℝ) : ℝ :=
  ω (NormedSpace.exp ((-β) • K))

/-- Modular beta log-generating potential for `β ↦ exp(-βK)`. -/
@[rep_depth operator]
noncomputable def modularBetaLogGeneratingPotential
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (β : ℝ) : ℝ :=
  Real.log (modularBetaPartitionReadout (E := E) ω K β)

/-- Beta readout is the ordinary partition readout of the negated generator. -/
@[rep_depth operator]
theorem modularBetaPartitionReadout_eq_operatorialPartitionReadout_neg
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (β : ℝ) :
    modularBetaPartitionReadout (E := E) ω K β =
      operatorialPartitionReadout (E := E) ω (-K) β := by
  simp [modularBetaPartitionReadout, operatorialPartitionReadout,
    informationPartitionFunction]

/-- Beta log potential is the ordinary log-generating potential of the negated generator. -/
@[rep_depth operator]
theorem modularBetaLogGeneratingPotential_eq_operatorialLogGeneratingPotential_neg
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (β : ℝ) :
    modularBetaLogGeneratingPotential (E := E) ω K β =
      operatorialLogGeneratingPotential (E := E) ω (-K) β := by
  simp [modularBetaLogGeneratingPotential, modularBetaPartitionReadout,
    operatorialLogGeneratingPotential, logInformationPartitionFunction,
    informationPartitionFunction]

/-- At `β=0`, the modular beta partition readout is the readout of the identity. -/
@[simp, rep_depth operator]
theorem modularBetaPartitionReadout_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    modularBetaPartitionReadout (E := E) ω K 0 = ω (1 : EndH E) := by
  simp [modularBetaPartitionReadout]

/-- At `β=0`, the modular beta log potential is `log(ω 1)`. -/
@[simp, rep_depth operator]
theorem modularBetaLogGeneratingPotential_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    modularBetaLogGeneratingPotential (E := E) ω K 0 = Real.log (ω (1 : EndH E)) := by
  simp [modularBetaLogGeneratingPotential, modularBetaPartitionReadout]

/-- First derivative of the beta partition readout at zero: `d/dβ Z(-βK)|₀ = -ω K`. -/
@[rep_depth operator]
theorem hasDerivAt_modularBetaPartitionReadout_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    HasDerivAt (fun β : ℝ => modularBetaPartitionReadout (E := E) ω K β) (-(ω K)) 0 := by
  have h :=
    hasDerivAt_operatorialPartitionReadout_zero (E := E) (ω := ω) (K := -K)
  simpa [modularBetaPartitionReadout_eq_operatorialPartitionReadout_neg] using h

/--
Normalized beta log-generator derivative:
`d/dβ log(ω(exp(-βK)))|₀ = -ω K`.
-/
@[rep_depth operator]
theorem hasDerivAt_modularBetaLogGeneratingPotential_zero_of_normalized
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) = 1) :
    HasDerivAt
      (fun β : ℝ => modularBetaLogGeneratingPotential (E := E) ω K β)
      (-(ω K)) 0 := by
  have h :=
    hasDerivAt_operatorialLogGeneratingPotential_zero_of_normalized
      (E := E) (ω := ω) (K := -K) hω1
  simpa [modularBetaLogGeneratingPotential_eq_operatorialLogGeneratingPotential_neg] using h

end InfoGeometry.Canonical.OperatorialLogGeneratingPotential
