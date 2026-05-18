import Mathlib
import InfoGeometry.Canonical.ZetaTrace

/-!
# InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas

Formula-first grand-canonical prime ensemble layer.

Policy enforced here:

* formulas are plain `def`s with explicit arguments;
* theorem statements use explicit hypotheses;
* no definitional formula is stored as a structure field;
* no proof certificate fields are used.

This file proves the finite grand-canonical normalization facts and a first
finite Clifford/Majorana cancellation theorem directly.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas

open scoped BigOperators

/-! ## 1. Grand-canonical formulas as functions -/

/-- Effective grand-canonical energy `E(x) - μ N(x)`. -/
def effectiveEnergy
    {State : Type*}
    (energy particleNumber : State → ℝ)
    (chemicalPotential : ℝ)
    (x : State) : ℝ :=
  energy x - chemicalPotential * particleNumber x

/-- Boltzmann weight `exp (-β(E(x) - μ N(x)))`. -/
def boltzmannWeight
    {State : Type*}
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ)
    (x : State) : ℝ :=
  Real.exp (-(beta * effectiveEnergy energy particleNumber chemicalPotential x))

/-- Finite grand-canonical partition function. -/
def partitionFunction
    {State : Type*} [Fintype State]
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ) : ℝ :=
  ∑ x : State, boltzmannWeight energy particleNumber beta chemicalPotential x

/-- Gibbs probability associated to a positive finite partition function. -/
def gibbsProbability
    {State : Type*} [Fintype State]
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ)
    (_hZ : 0 < partitionFunction energy particleNumber beta chemicalPotential)
    (x : State) : ℝ :=
  boltzmannWeight energy particleNumber beta chemicalPotential x /
    partitionFunction energy particleNumber beta chemicalPotential

/-! ## 2. Direct finite proofs -/

/-- Boltzmann weights are strictly positive. -/
theorem boltzmannWeight_pos
    {State : Type*}
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ)
    (x : State) :
    0 < boltzmannWeight energy particleNumber beta chemicalPotential x := by
  unfold boltzmannWeight
  exact Real.exp_pos _

/-- Boltzmann weights are nonnegative. -/
theorem boltzmannWeight_nonneg
    {State : Type*}
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ)
    (x : State) :
    0 ≤ boltzmannWeight energy particleNumber beta chemicalPotential x :=
  le_of_lt (boltzmannWeight_pos energy particleNumber beta chemicalPotential x)

/-- On a nonempty finite state space, the partition function is strictly positive. -/
theorem partitionFunction_pos
    {State : Type*} [Fintype State] [Nonempty State]
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ) :
    0 < partitionFunction energy particleNumber beta chemicalPotential := by
  unfold partitionFunction
  exact Finset.sum_pos
    (fun x _hx => boltzmannWeight_pos energy particleNumber beta chemicalPotential x)
    Finset.univ_nonempty

/-- Gibbs probabilities are nonnegative. -/
theorem gibbsProbability_nonneg
    {State : Type*} [Fintype State]
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ)
    (hZ : 0 < partitionFunction energy particleNumber beta chemicalPotential)
    (x : State) :
    0 ≤ gibbsProbability energy particleNumber beta chemicalPotential hZ x := by
  exact div_nonneg
    (boltzmannWeight_nonneg energy particleNumber beta chemicalPotential x)
    (le_of_lt hZ)

/-- Gibbs probabilities normalize to one. -/
theorem gibbsProbability_sum_eq_one
    {State : Type*} [Fintype State]
    (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ)
    (hZ : 0 < partitionFunction energy particleNumber beta chemicalPotential) :
    ∑ x : State,
      gibbsProbability energy particleNumber beta chemicalPotential hZ x = 1 := by
  calc
    ∑ x : State, gibbsProbability energy particleNumber beta chemicalPotential hZ x
        =
      (∑ x : State, boltzmannWeight energy particleNumber beta chemicalPotential x) /
        partitionFunction energy particleNumber beta chemicalPotential := by
          simp [gibbsProbability, Finset.sum_div]
    _ =
      partitionFunction energy particleNumber beta chemicalPotential /
        partitionFunction energy particleNumber beta chemicalPotential := by
          rfl
    _ = 1 := by
          exact div_self (ne_of_gt hZ)

/-! ## 3. Prime log-volume formulas -/

/-- Additive log-volume / energy coordinate. -/
def logVolumeEnergy
    {Profile : Type*}
    (volume : Profile → ℝ)
    (x : Profile) : ℝ :=
  Real.log (volume x)

/-- Grand-canonical energy specialized to log-volume. -/
def primeEffectiveEnergy
    {Profile : Type*}
    (volume : Profile → ℝ)
    (particleNumber : Profile → ℝ)
    (chemicalPotential : ℝ)
    (x : Profile) : ℝ :=
  effectiveEnergy (logVolumeEnergy volume) particleNumber chemicalPotential x

/-- Boltzmann weight specialized to log-volume energy. -/
def primeBoltzmannWeight
    {Profile : Type*}
    (volume : Profile → ℝ)
    (particleNumber : Profile → ℝ)
    (beta chemicalPotential : ℝ)
    (x : Profile) : ℝ :=
  boltzmannWeight (logVolumeEnergy volume) particleNumber beta chemicalPotential x

/-- The log-volume effective energy unfolds to `log(volume x) - μ N(x)`. -/
theorem primeEffectiveEnergy_eq
    {Profile : Type*}
    (volume : Profile → ℝ)
    (particleNumber : Profile → ℝ)
    (chemicalPotential : ℝ)
    (x : Profile) :
    primeEffectiveEnergy volume particleNumber chemicalPotential x =
      Real.log (volume x) - chemicalPotential * particleNumber x :=
  rfl

/-- The prime Boltzmann weight unfolds to the explicit log-volume formula. -/
theorem primeBoltzmannWeight_eq
    {Profile : Type*}
    (volume : Profile → ℝ)
    (particleNumber : Profile → ℝ)
    (beta chemicalPotential : ℝ)
    (x : Profile) :
    primeBoltzmannWeight volume particleNumber beta chemicalPotential x =
      Real.exp (-(beta * (Real.log (volume x) -
        chemicalPotential * particleNumber x))) :=
  rfl

/-! ## 4. Existing theorem-owned zeta readout -/

/--
Existing theorem-owned zeta channel.

The repo already owns this Euler-product-to-zeta theorem in the convergence
region `1 < Re(s)`.
-/
theorem primeEulerProduct_eq_riemannZeta
    {s : ℂ}
    (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = riemannZeta s :=
  InfoGeometry.Canonical.ZetaTrace.zeta_trace_bridge hs

/-! ## 5. Majorana cancellation as a genuine proof -/

/-- Two-mode Majorana/Clifford Dirac formula. -/
def twoMajoranaDirac
    {Op : Type*} [Ring Op]
    (gamma₁ gamma₂ : Op) : Op :=
  gamma₁ + gamma₂

/--
The square of a two-mode Majorana Dirac operator is `2` when the two modes
square to `1` and anticommute.
-/
theorem twoMajoranaDirac_sq
    {Op : Type*} [Ring Op]
    (gamma₁ gamma₂ : Op)
    (h₁ : gamma₁ * gamma₁ = 1)
    (h₂ : gamma₂ * gamma₂ = 1)
    (hanti : gamma₁ * gamma₂ + gamma₂ * gamma₁ = 0) :
    twoMajoranaDirac gamma₁ gamma₂ * twoMajoranaDirac gamma₁ gamma₂ = (2 : Op) := by
  unfold twoMajoranaDirac
  calc
    (gamma₁ + gamma₂) * (gamma₁ + gamma₂)
        =
      gamma₁ * gamma₁ + (gamma₁ * gamma₂ + gamma₂ * gamma₁) + gamma₂ * gamma₂ := by
        noncomm_ring
    _ = 1 + 0 + 1 := by
        rw [h₁, h₂, hanti]
    _ = (2 : Op) := by
        norm_num

end InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas
