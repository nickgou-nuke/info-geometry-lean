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

namespace GrandCanonicalFockNumberBridge

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.GrandCanonicalGaugePotentialBridge
open InfoGeometry.GrandCanonical

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

/-! ## Functorial affine-form bridge to the finite chemical-potential gauge lane -/

/--
Proof-carrying functorial affine bridge between the finite count lane and the
Fock operator lane.

The fields record the shared thermodynamic pattern:

* finite: `E(x) - μ * N(x)`;
* Fock/operator: `H - μ • N_B`.

This package deliberately does not identify the finite count observable
`params.number` with the Bogoliubov number operator `N_B`.
-/
@[rep_depth thermo, spine_object]
structure FiniteFockChemicalPotentialAffineBridge
    {α : Type _}
    (params : GrandCanonicalTwoParam α)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (μ : ℝ) where
  finiteGauge :
    ∀ x : α,
      (chemicalPotentialGauge params).gaugeOf μ x = μ * params.number x
  finiteShiftedEnergy :
    ∀ x : α,
      shiftedEnergy params μ x =
        params.energy x - (chemicalPotentialGauge params).gaugeOf μ x
  fockGauge :
    (fockNumberGauge (E := E) B).gaugeOf μ =
      μ • bogoliubovNumberOperator (E := E) B
  fockShiftedHamiltonian :
    grandCanonicalFockGenerator (E := E) B H μ =
      H - (fockNumberGauge (E := E) B).gaugeOf μ

/--
Canonical constructor for the legitimate affine bridge.

This is a spine functorial lift: it preserves the affine thermodynamic form
`base - μ • number-object` across the finite count and Fock-operator
categories, without asserting that the objects themselves are equal.
-/
@[rep_depth thermo, spine_morphism, spine_functor, spine_functor_lift]
def finiteFockChemicalPotentialAffineBridge
    {α : Type _}
    (params : GrandCanonicalTwoParam α)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (μ : ℝ) :
    FiniteFockChemicalPotentialAffineBridge
      params B H μ where
  finiteGauge := by
    intro x
    exact chemicalPotentialGauge_apply params μ x
  finiteShiftedEnergy := by
    intro x
    exact shiftedEnergy_eq_energy_sub_chemicalPotentialGauge params μ x
  fockGauge :=
    fockNumberGauge_is_mu_times_numberOperator (E := E) B μ
  fockShiftedHamiltonian :=
    grandCanonicalFockGenerator_eq_hamiltonian_sub_fockNumberGauge
      (E := E) B H μ

/--
First-quantization reading of the affine bridge.

The finite lane treats energy and number as functions on count states; the
Fock lane treats the corresponding grand-canonical expression as an operator
on the doubled carrier.  This is only a functorial lift of the affine form,
not a diagonalization or an identification of function states with operators.
-/
@[rep_depth thermo, spine_morphism, spine_functor, spine_functor_lift]
def firstQuantizationChemicalPotentialAffineBridge
    {α : Type _}
    (params : GrandCanonicalTwoParam α)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (μ : ℝ) :
    FiniteFockChemicalPotentialAffineBridge
      params B H μ :=
  finiteFockChemicalPotentialAffineBridge params B H μ

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

end GrandCanonicalFockNumberBridge
