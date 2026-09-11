import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge

Finite grand-canonical chemical potential as background gauge coupling.

This bridge records only the source-backed finite-state fact already owned by
`InfoGeometry.GrandCanonical.Core`:

- the chemical potential couples linearly to the count observable `N`,
- the grand-canonical kernel is `exp (-β * (E - μN))`,
- the Massieu/log-partition potential is `potentialGC = log Z(β, μ)`,
- the `μ`-derivative is the conjugate count readout
  `∂μ log Z = β * meanNumber`.

It does not identify `μ` with a Bogoliubov frame field or a Type III modular
background. Those require separate operatorial owner bridges.
-/

namespace InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge

open InfoGeometry.GrandCanonical
open InfoGeometry.Canonical

variable {α : Type _}

/-- Chemical potential background gauge coupling to the count observable. -/
@[rep_depth transport]
noncomputable def chemicalPotentialGauge
    (params : GrandCanonicalTwoParam α) : WeylGaugeField ℝ (α → ℝ) :=
  fun μ x => μ * params.number x

/-- Pointwise expansion of the chemical-potential gauge coupling. -/
@[simp]
theorem chemicalPotentialGauge_apply
    (params : GrandCanonicalTwoParam α) (μ : ℝ) (x : α) :
    (chemicalPotentialGauge params).gaugeOf μ x = μ * params.number x := by
  rfl

/--
The shifted grand-canonical observable is energy minus the chemical-potential
background gauge coupling.
-/
@[rep_depth transport]
theorem shiftedEnergy_eq_energy_sub_chemicalPotentialGauge
    (params : GrandCanonicalTwoParam α) (μ : ℝ) (x : α) :
    shiftedEnergy params μ x =
      params.energy x - (chemicalPotentialGauge params).gaugeOf μ x := by
  rfl

/-- Zero chemical potential removes the background count coupling. -/
@[rep_depth transport]
theorem chemicalPotentialGauge_zero
    (params : GrandCanonicalTwoParam α) :
    (chemicalPotentialGauge params).gaugeOf 0 = fun _ : α => 0 := by
  funext x
  simp [chemicalPotentialGauge]

/-- Chemical-potential couplings compose additively in the gauge parameter. -/
@[rep_depth transport]
theorem chemicalPotentialGauge_add
    (params : GrandCanonicalTwoParam α) (μ ν : ℝ) :
    (chemicalPotentialGauge params).gaugeOf (μ + ν) =
  fun x => (chemicalPotentialGauge params).gaugeOf μ x
        + (chemicalPotentialGauge params).gaugeOf ν x := by
  funext x
  simp [chemicalPotentialGauge, add_mul]

/-- Grand-canonical kernel exponent in gauge-coupled form. -/
@[rep_depth transport]
noncomputable def grandCanonicalGaugeKernelExponent
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) : ℝ :=
  -β * (params.energy x - (chemicalPotentialGauge params).gaugeOf μ x)

/-- The gauge-coupled exponent is definitionally the owner shifted-energy exponent. -/
@[rep_depth transport]
theorem grandCanonicalGaugeKernelExponent_eq
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) (x : α) :
    grandCanonicalGaugeKernelExponent params β μ x =
      -β * shiftedEnergy params μ x := by
  simp [grandCanonicalGaugeKernelExponent, shiftedEnergy, chemicalPotentialGauge, mul_sub]

/-- Grand-canonical Massieu potential as the log-generating potential `log Z(β, μ)`. -/
@[rep_depth transport]
noncomputable def grandCanonicalMassieuPotential
    [Fintype α] [Nonempty α]
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  potentialGC params β μ

/-- The bridge Massieu potential is exactly the owner `potentialGC`. -/
@[rep_depth transport]
theorem grandCanonicalMassieuPotential_eq_potentialGC
    [Fintype α] [Nonempty α]
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    grandCanonicalMassieuPotential params β μ = potentialGC params β μ := by
  rfl

/--
The chemical-potential direction is conjugate to the count observable:
`∂μ log Z(β, μ) = β * E_{β,μ}[N]`.
-/
@[rep_depth transport]
theorem chemicalPotential_conjugate_count_readout
    [Fintype α] [Nonempty α]
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => grandCanonicalMassieuPotential params β t) μ =
      β * meanNumber params β μ := by
  simpa [grandCanonicalMassieuPotential] using
    potentialGC_deriv_mu_eq_beta_meanNumber params β μ

/--
The inverse-temperature direction is conjugate to the shifted thermodynamic
observable `E - μN`.
-/
@[rep_depth transport]
theorem inverseTemperature_conjugate_shiftedEnergy_readout
    [Fintype α] [Nonempty α]
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    deriv (fun t => grandCanonicalMassieuPotential params t μ) β =
      -meanShift params β μ := by
  simpa [grandCanonicalMassieuPotential] using
    potentialGC_deriv_beta_eq_neg_meanShift params β μ

end InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge
