import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Finite commuting Connes cocycle shadow

This file isolates two finite/algebraic parts of relative modular transport.

First, it proves the pure group-theoretic Connes--Radon--Nikodym cocycle law
for two one-parameter unit-group functions.  This is the Lean-safe algebraic core:

`u_t = Uψ(t) * Uφ(t)⁻¹` satisfies
`u_{s+t} = u_s * σ_s^φ(u_t)`.

Second, it records the finite diagonal/commuting Cartan scalar shadow.

It deliberately separates two objects:

* `finitePositiveDensityRatio ΔK i = exp (-ΔK i)`, the positive
  Radon--Nikodym density-ratio shadow;
* `finiteCommutingConnesPhase ΔK t i = exp (-I * t * ΔK i)`, the unitary
  modular phase shadow.

The determinant-volume cocycle is not used here.  This module only proves the
commuting scalar exponential laws that are valid in the finite Cartan lane.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.FiniteConnesCocycle

open scoped BigOperators
open InfoGeometry.Thermodynamics.FiniteGibbsRelative

/-! ## Abstract finite Connes--Radon--Nikodym cocycle law -/

variable {G : Type*} [Group G]

/--
The finite Connes--Radon--Nikodym cocycle law.

This proves the algebraic core of
`(Dψ : Dφ)_{s+t} = (Dψ : Dφ)_s σ_s^φ((Dψ : Dφ)_t)`.
It does not assert the analytic Tomita--Takesaki theorem for arbitrary
von Neumann weights.
-/
theorem finiteConnesFlux_cocycle
    (Uψ Uφ : ℝ → G)
    (hψ_add : ∀ s t : ℝ, Uψ (s + t) = Uψ s * Uψ t)
    (hφ_add : ∀ s t : ℝ, Uφ (s + t) = Uφ s * Uφ t)
    (s t : ℝ) :
    Uψ (s + t) * (Uφ (s + t))⁻¹ =
      (Uψ s * (Uφ s)⁻¹) *
        (Uφ s * (Uψ t * (Uφ t)⁻¹) * (Uφ s)⁻¹) := by
  rw [hψ_add s t, hφ_add s t]
  group

@[simp]
theorem finiteConnesFlux_zero
    (Uψ Uφ : ℝ → G) (hψ_zero : Uψ 0 = 1) (hφ_zero : Uφ 0 = 1) :
    Uψ 0 * (Uφ 0)⁻¹ = 1 := by
  rw [hψ_zero, hφ_zero]
  simp

/-- If the two modular flows agree, the relative cocycle is trivial. -/
@[simp]
theorem finiteConnesFlux_eq_one_of_same
    (Uφ : ℝ → G) (t : ℝ) :
    Uφ t * (Uφ t)⁻¹ = 1 := by
  simp

variable {ι : Type*}

/-- Positive finite Radon--Nikodym density ratio for a real relative generator. -/
noncomputable def finitePositiveDensityRatio (ΔK : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-(ΔK i))

/-- Positive finite density ratio attached to two finite Cartan temperatures. -/
noncomputable def finitePositiveDensityRatioOfStates
    (φ ψ : FiniteTemperature ι) (i : ι) : ℝ :=
  finitePositiveDensityRatio (relativeHamiltonian φ ψ) i

/-- The finite positive density ratio is strictly positive. -/
theorem finitePositiveDensityRatio_pos
    (ΔK : ι → ℝ) (i : ι) :
    0 < finitePositiveDensityRatio ΔK i := by
  exact Real.exp_pos _

/-- Unitary finite commuting Connes phase for a real relative generator. -/
noncomputable def finiteCommutingConnesPhase
    (ΔK : ι → ℝ) (t : ℝ) (i : ι) : ℂ :=
  Complex.exp (-(Complex.I * ((t * ΔK i : ℝ) : ℂ)))

/-- Unitary finite commuting Connes phase attached to two finite Cartan temperatures. -/
noncomputable def finiteCommutingConnesPhaseOfStates
    (φ ψ : FiniteTemperature ι) (t : ℝ) (i : ι) : ℂ :=
  finiteCommutingConnesPhase (relativeHamiltonian φ ψ) t i

/-- The positive density ratio is multiplicative for additive relative generators. -/
theorem finitePositiveDensityRatio_add
    (ΔK₁ ΔK₂ : ι → ℝ) (i : ι) :
    finitePositiveDensityRatio (fun j => ΔK₁ j + ΔK₂ j) i =
      finitePositiveDensityRatio ΔK₁ i * finitePositiveDensityRatio ΔK₂ i := by
  unfold finitePositiveDensityRatio
  have h : -(ΔK₁ i + ΔK₂ i) = -ΔK₁ i + -ΔK₂ i := by ring
  rw [h, Real.exp_add]

/-- The finite commuting Connes phase is normalized at time zero. -/
theorem finiteCommutingConnesPhase_zero
    (ΔK : ι → ℝ) (i : ι) :
    finiteCommutingConnesPhase ΔK 0 i = 1 := by
  simp [finiteCommutingConnesPhase]

/--
The finite commuting Connes phase has the additive one-parameter law.

This is the commuting scalar shadow of the Connes cocycle law with trivial
reference modular action.
-/
theorem finiteCommutingConnesPhase_add_time
    (ΔK : ι → ℝ) (s t : ℝ) (i : ι) :
    finiteCommutingConnesPhase ΔK (s + t) i =
      finiteCommutingConnesPhase ΔK s i * finiteCommutingConnesPhase ΔK t i := by
  unfold finiteCommutingConnesPhase
  have h :
      -(Complex.I * (((s + t) * ΔK i : ℝ) : ℂ)) =
        -(Complex.I * ((s * ΔK i : ℝ) : ℂ)) +
          -(Complex.I * ((t * ΔK i : ℝ) : ℂ)) := by
    norm_num
    ring
  rw [h, Complex.exp_add]

/--
In the diagonal scalar Cartan lane, the reference modular action on scalar
readouts is trivial.  This is not a general von Neumann algebra modular action.
-/
def finiteScalarReferenceModularAction
    (_φ : FiniteTemperature ι) (_s : ℝ) (u : ι → ℂ) : ι → ℂ :=
  u

/--
Finite commuting Connes cocycle law with the explicit trivial scalar reference
action.

This is the exact finite/commuting specialization of
`u_{s+t} = u_s * σ_s(u_t)`.  The general noncommutative law remains owned by
`InfoGeometry.Volume.ConnesCocycle`.
-/
theorem finiteCommutingConnesPhase_connesLaw_trivialReference
    (φ ψ : FiniteTemperature ι) (s t : ℝ) :
    (fun i => finiteCommutingConnesPhaseOfStates φ ψ (s + t) i) =
      fun i =>
        finiteCommutingConnesPhaseOfStates φ ψ s i *
          finiteScalarReferenceModularAction φ s
            (fun j => finiteCommutingConnesPhaseOfStates φ ψ t j) i := by
  funext i
  simp [finiteScalarReferenceModularAction, finiteCommutingConnesPhaseOfStates,
    finiteCommutingConnesPhase_add_time]

/--
Roadmap-facing theorem name for the finite commuting Connes cocycle law.

This is the same proved scalar Cartan specialization as
`finiteCommutingConnesPhase_connesLaw_trivialReference`.
-/
theorem finite_commuting_connes_cocycle_satisfies_cocycle_law
    (φ ψ : FiniteTemperature ι) (s t : ℝ) :
    (fun i => finiteCommutingConnesPhaseOfStates φ ψ (s + t) i) =
      fun i =>
        finiteCommutingConnesPhaseOfStates φ ψ s i *
          finiteScalarReferenceModularAction φ s
            (fun j => finiteCommutingConnesPhaseOfStates φ ψ t j) i :=
  finiteCommutingConnesPhase_connesLaw_trivialReference φ ψ s t

/-- The finite commuting Connes phase is multiplicative for additive generators. -/
theorem finiteCommutingConnesPhase_add_generator
    (ΔK₁ ΔK₂ : ι → ℝ) (t : ℝ) (i : ι) :
    finiteCommutingConnesPhase (fun j => ΔK₁ j + ΔK₂ j) t i =
      finiteCommutingConnesPhase ΔK₁ t i *
        finiteCommutingConnesPhase ΔK₂ t i := by
  unfold finiteCommutingConnesPhase
  have h :
      -(Complex.I * ((t * (ΔK₁ i + ΔK₂ i) : ℝ) : ℂ)) =
        -(Complex.I * ((t * ΔK₁ i : ℝ) : ℂ)) +
          -(Complex.I * ((t * ΔK₂ i : ℝ) : ℂ)) := by
    norm_num
    ring
  rw [h, Complex.exp_add]

/-- State-chain law for finite positive density ratios. -/
theorem finitePositiveDensityRatio_stateChain
    (φ ψ χ : FiniteTemperature ι) (i : ι) :
    finitePositiveDensityRatioOfStates φ χ i =
      finitePositiveDensityRatioOfStates φ ψ i *
        finitePositiveDensityRatioOfStates ψ χ i := by
  unfold finitePositiveDensityRatioOfStates
  rw [← finitePositiveDensityRatio_add (relativeHamiltonian φ ψ) (relativeHamiltonian ψ χ) i]
  congr
  funext j
  unfold relativeHamiltonian
  ring

/-- State-chain law for finite commuting Connes phases. -/
theorem finiteCommutingConnesPhase_stateChain
    (φ ψ χ : FiniteTemperature ι) (t : ℝ) (i : ι) :
    finiteCommutingConnesPhaseOfStates φ χ t i =
      finiteCommutingConnesPhaseOfStates φ ψ t i *
        finiteCommutingConnesPhaseOfStates ψ χ t i := by
  unfold finiteCommutingConnesPhaseOfStates
  rw [← finiteCommutingConnesPhase_add_generator
    (relativeHamiltonian φ ψ) (relativeHamiltonian ψ χ) t i]
  congr
  funext j
  unfold relativeHamiltonian
  ring

end InfoGeometry.Thermodynamics.FiniteConnesCocycle
