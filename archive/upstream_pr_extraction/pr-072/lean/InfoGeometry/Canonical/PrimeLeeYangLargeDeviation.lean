import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.Cramer
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Fenchel

/-!
# InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

Finite fluctuation and large-deviation foundations for the prime Lee--Yang chain,
reformulated through categorical colimits with NO infinities, NO `atTop`, NO
`Filter.limsup/liminf`, and NO analytic thermodynamic limit.

This module defines:

* the square-free occupation readout `kᵢ = (1 + σᵢ) / 2`;
* the finite logarithmic prime energy `Σᵢ kᵢ log pᵢ`;
* finite Boltzmann weights and partition functions;
* finite log-moment/cumulant readouts;
* a finite-grid Cramér transform using the repo-owned `InfoGeometry.cramerRateOn`.

No large-deviation principle is asserted here.  The finite-stage data are the
sole authority; no `sorry`, no analytic limit, and no measure-theoretic LDP
debt are introduced.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/-! ## Occupation and finite prime energy -/

/-- Square-free occupation readout `k = (1 + σ) / 2`. -/
def spinOccupation
    (σ : IsingSpin) : ℝ :=
  (1 + IsingSpin.sign σ) / 2

@[simp]
theorem spinOccupation_up :
    spinOccupation IsingSpin.up = 1 := by
  norm_num [spinOccupation]

@[simp]
theorem spinOccupation_down :
    spinOccupation IsingSpin.down = 0 := by
  norm_num [spinOccupation]

/-- Occupation is nonnegative. -/
theorem spinOccupation_nonneg
    (σ : IsingSpin) :
    0 ≤ spinOccupation σ := by
  cases σ <;> norm_num [spinOccupation]

/-- The Lee--Yang spin occupation agrees with the canonical prime-chain
occupation convention owned by `PrimeLeeYangFerromagneticChain`. -/
@[simp]
theorem spinOccupation_eq_chainOccupation
    (σ : IsingSpin) :
    spinOccupation σ = PrimeFerromagneticChain.occupation σ := by
  cases σ <;> simp [spinOccupation, PrimeFerromagneticChain.occupation]

variable {n : ℕ}
variable (C : PrimeFerromagneticChain n)

/-- Square-free logarithmic prime energy `Σᵢ kᵢ log pᵢ`. -/
def configurationLogEnergy
    (σ : Fin n → IsingSpin) : ℝ :=
  ∑ i : Fin n, spinOccupation (σ i) * C.siteEnergy i

/-- The logarithmic prime energy is nonnegative. -/
theorem configurationLogEnergy_nonneg
    (σ : Fin n → IsingSpin) :
    0 ≤ configurationLogEnergy C σ := by
  unfold configurationLogEnergy
  exact Finset.sum_nonneg (by
    intro i _
    exact mul_nonneg (spinOccupation_nonneg (σ i)) (C.siteEnergy_nonneg i))

/-- The finite logarithmic energy descends to the chain's canonical
occupation readout, so the Lee--Yang and Gibbs descriptions use the same
finite observable. -/
theorem configurationLogEnergy_eq_chainOccupation_sum
    (σ : Fin n → IsingSpin) :
    configurationLogEnergy C σ =
      ∑ i : Fin n,
        PrimeFerromagneticChain.occupation (σ i) * C.siteEnergy i := by
  unfold configurationLogEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [spinOccupation_eq_chainOccupation]

/-- Squared logarithmic prime energy, the finite fluctuation observable. -/
def squaredLogEnergy
    (σ : Fin n → IsingSpin) : ℝ :=
  (configurationLogEnergy C σ) ^ 2

/-- The squared logarithmic prime energy is nonnegative. -/
theorem squaredLogEnergy_nonneg
    (σ : Fin n → IsingSpin) :
    0 ≤ squaredLogEnergy C σ := by
  unfold squaredLogEnergy
  exact sq_nonneg _

/-! ## Finite Gibbs and cumulant readouts -/

/-- Finite Boltzmann weight for the prime Lee--Yang chain. -/
def boltzmannWeight
    (β : ℝ)
    (h : Fin n → ℝ)
    (σ : Fin n → IsingSpin) : ℝ :=
  Real.exp (-β * C.isingHamiltonian h σ)

/-- Boltzmann weights are positive. -/
theorem boltzmannWeight_pos
    (β : ℝ)
    (h : Fin n → ℝ)
    (σ : Fin n → IsingSpin) :
    0 < boltzmannWeight C β h σ := by
  unfold boltzmannWeight
  exact Real.exp_pos _

/-- Finite partition function over all spin configurations. -/
def finitePartition
    (β : ℝ)
    (h : Fin n → ℝ) : ℝ :=
  ∑ σ : Fin n → IsingSpin, boltzmannWeight C β h σ

/-- The finite partition function is strictly positive. -/
theorem finitePartition_pos
    (β : ℝ)
    (h : Fin n → ℝ) :
    0 < finitePartition C β h := by
  unfold finitePartition
  exact Finset.sum_pos (fun σ _ => boltzmannWeight_pos C β h σ)
    ⟨fun _ => IsingSpin.up, Finset.mem_univ _⟩

/-- At zero inverse temperature, every finite spin configuration has unit weight. -/
theorem finitePartition_zero_eq_card
    (h : Fin n → ℝ) :
    finitePartition C 0 h = Fintype.card (Fin n → IsingSpin) := by
  unfold finitePartition boltzmannWeight
  simp

/-- The zero-temperature finite partition has the expected two-state count. -/
theorem finitePartition_zero_eq_two_pow
    (h : Fin n → ℝ) :
    finitePartition C 0 h = (2 : ℝ) ^ n := by
  rw [finitePartition_zero_eq_card]
  have hcard : Fintype.card IsingSpin = 2 := by
    rfl
  rw [Fintype.card_fun, hcard]
  simp [Fintype.card_fin]

/-- Tilted finite partition function for an observable `O`. -/
def tiltedPartition
    (β : ℝ)
    (h : Fin n → ℝ)
    (O : (Fin n → IsingSpin) → ℝ)
    (θ : ℝ) : ℝ :=
  ∑ σ : Fin n → IsingSpin,
    Real.exp (-β * C.isingHamiltonian h σ + θ * O σ)

/-- The tilted finite partition function is strictly positive. -/
theorem tiltedPartition_pos
    (β : ℝ)
    (h : Fin n → ℝ)
    (O : (Fin n → IsingSpin) → ℝ)
    (θ : ℝ) :
    0 < tiltedPartition C β h O θ := by
  unfold tiltedPartition
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _)
    ⟨fun _ => IsingSpin.up, Finset.mem_univ _⟩

/-- The zero tilt leaves the finite Boltzmann partition unchanged. -/
theorem tiltedPartition_zero_eq_finitePartition
    (β : ℝ)
    (h : Fin n → ℝ)
    (O : (Fin n → IsingSpin) → ℝ) :
    tiltedPartition C β h O 0 = finitePartition C β h := by
  unfold tiltedPartition finitePartition boltzmannWeight
  simp

/--
Finite log-moment generating function:

`log Σ exp(-βH + θO) - log Σ exp(-βH)`.
-/
def logMomentGenerating
    (β : ℝ)
    (h : Fin n → ℝ)
    (O : (Fin n → IsingSpin) → ℝ)
    (θ : ℝ) : ℝ :=
  Real.log (tiltedPartition C β h O θ) - Real.log (finitePartition C β h)

@[simp]
theorem logMomentGenerating_zero
    (β : ℝ)
    (h : Fin n → ℝ)
    (O : (Fin n → IsingSpin) → ℝ) :
    logMomentGenerating C β h O 0 = 0 := by
  unfold logMomentGenerating tiltedPartition finitePartition boltzmannWeight
  simp

/-- Finite cumulant readout for the logarithmic prime energy. -/
def logEnergyCumulant
    (β : ℝ)
    (h : Fin n → ℝ)
    (θ : ℝ) : ℝ :=
  logMomentGenerating C β h (configurationLogEnergy C) θ

/-- Finite cumulant readout for the squared logarithmic prime-energy fluctuation. -/
def squaredLogEnergyCumulant
    (β : ℝ)
    (h : Fin n → ℝ)
    (θ : ℝ) : ℝ :=
  logMomentGenerating C β h (squaredLogEnergy C) θ

/-! ## Finite-grid Cramér transform and Fenchel--Young packet -/

/-- Finite-grid Cramér transform for any chosen cumulant readout `ψ`. -/
def finiteCramerRate
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η : ℝ) : ℝ :=
  InfoGeometry.cramerRateOn Θ hΘ ψ η

/-- Fenchel--Young inequality on a finite parameter grid. -/
theorem fenchelYoung_finiteCramerRate
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η θ : ℝ)
    (hθ : θ ∈ Θ) :
    η * θ ≤ ψ θ + finiteCramerRate Θ hΘ ψ η := by
  exact InfoGeometry.fenchelYoung_on_cramerRateOn Θ hΘ ψ η θ hθ

/-- The finite-grid Cramér rate is attained at some grid point. -/
theorem exists_argmax_finiteCramerRate
    (Θ : Finset ℝ)
    (hΘ : Θ.Nonempty)
    (ψ : ℝ → ℝ)
    (η : ℝ) :
    ∃ θ0, θ0 ∈ Θ ∧
      ∀ θ, θ ∈ Θ → η * θ - ψ θ ≤ η * θ0 - ψ θ0 := by
  exact InfoGeometry.exists_argmax_cramerRateOn Θ hΘ ψ η

end InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

end noncomputable section
