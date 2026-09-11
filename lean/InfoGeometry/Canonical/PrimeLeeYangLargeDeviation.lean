import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import InfoGeometry.Cramer
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Fenchel

open MeasureTheory

/-!
# InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

Finite fluctuation and large-deviation sockets for the prime Lee--Yang chain.

This module sits downstream of `PrimeLeeYangFerromagneticChain`. It defines:

* the square-free occupation readout `kᵢ = (1 + σᵢ) / 2`;
* the finite logarithmic prime energy `Σᵢ kᵢ log pᵢ`;
* finite Boltzmann weights and partition functions;
* finite log-moment/cumulant readouts;
* a finite-grid Cramér transform using the repo-owned `InfoGeometry.cramerRateOn`.

The thermodynamic large-deviation principle is not proved here.  The
`PrimeChainLargeDeviationWitness` carries only the finite data needed to state
that problem.  Unsupported asymptotic conclusions are exposed below as explicit
`sorry` debt, not as arbitrary `Prop` fields.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangLargeDeviation

open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open Filter

/-- A measure together with the measurable space on its configuration carrier. -/
structure ConfigurationMeasure (X : Type*) where
  measurableSpace : MeasurableSpace X
  measure : @Measure X measurableSpace

namespace ConfigurationMeasure

variable {X Y : Type*} [MeasurableSpace Y]

/-- Measurability of a map relative to the carrier's explicit measurable space. -/
def MeasurableMap (C : ConfigurationMeasure X) (f : X → Y) : Prop :=
  @Measurable X Y C.measurableSpace inferInstance f

/-- Push a measurable observable forward to its target law. -/
noncomputable def map (C : ConfigurationMeasure X) (f : X → Y)
    : Measure Y := by
  letI := C.measurableSpace
  exact Measure.map f C.measure

end ConfigurationMeasure

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

/-! ## Asymptotic LDP owner -/

/-
The large-deviation principle is stated in the standard closed/open-set form.
The law sequence remains explicit: the finite chain observable must be linked
to it by a separate theorem rather than being silently identified with it.
-/
def LargeDeviationPrinciple
    (law : ℕ → Measure ℝ)
    (speed : ℕ → ℝ)
    (rateFunction : ℝ → ℝ) : Prop :=
  (∀ F : Set ℝ, IsClosed F →
    Filter.limsup
        (fun N => (speed N)⁻¹ * Real.log ((law N F).toReal)) atTop ≤
      -sInf (rateFunction '' F)) ∧
  (∀ G : Set ℝ, IsOpen G →
    -sInf (rateFunction '' G) ≤
      Filter.liminf
        (fun N => (speed N)⁻¹ * Real.log ((law N G).toReal)) atTop)

/--
Proof-carrying large-deviation packet for a sequence of finite prime chains.

The fields isolate the exact analytic work needed after the finite definitions:
choice of scaling speed, convergence of finite cumulants, a rate function, and
the final large-deviation principle.
-/
@[socket_debt_tag]
structure PrimeChainLargeDeviationWitness where
  chain : ℕ → Σ n : ℕ, PrimeFerromagneticChain n
  speed : ℕ → ℝ
  observable : ∀ N : ℕ, (Fin (chain N).1 → IsingSpin) → ℝ
  /-- The configuration-space law before pushing forward by the observable. -/
  configurationLaw :
    ∀ N : ℕ, ConfigurationMeasure (Fin (chain N).1 → IsingSpin)
  law : ℕ → Measure ℝ
  observable_measurable :
    ∀ N : ℕ,
      (configurationLaw N).MeasurableMap (observable N)
  law_eq_observable_map :
    ∀ N : ℕ,
      law N = (configurationLaw N).map (observable N)
  finiteCumulant : ℕ → ℝ → ℝ
  limitingCumulant : ℝ → ℝ
  rateFunction : ℝ → ℝ
  /-- The scaling speed diverges in the genuine filter sense. -/
  speed_tends_to_infinity : Tendsto speed atTop atTop
  /-- Finite cumulants converge pointwise to the limiting cumulant. -/
  finiteCumulant_converges :
    ∀ θ : ℝ,
      Tendsto (fun N => finiteCumulant N θ) atTop
        (nhds (limitingCumulant θ))
  /-- The rate function is a Fenchel upper-bound dual of the limiting cumulant. -/
  rateFunction_is_legendre :
    InfoGeometry.Convex.OneD.IsLegendreConjugate
      limitingCumulant rateFunction
  /-- The closed/open-set large-deviation law for the explicit measure sequence. -/
  largeDeviationPrinciple :
    LargeDeviationPrinciple law speed rateFunction

namespace PrimeChainLargeDeviationWitness

/--
Debt surface for the missing speed-divergence theorem.

This cannot be discharged by the finite data in the packet.
-/
@[bridge_target_tag]
theorem speed_tends_to_infinity_readback
    (W : PrimeChainLargeDeviationWitness) :
    Tendsto W.speed atTop atTop :=
  W.speed_tends_to_infinity

/--
Debt surface for convergence of finite cumulant readouts.

This requires an analytic limit theorem not present in this file.
-/
@[bridge_target_tag]
theorem finiteCumulant_converges_readback
    (W : PrimeChainLargeDeviationWitness) :
    ∀ θ : ℝ,
      Tendsto (fun N => W.finiteCumulant N θ) atTop
        (nhds (W.limitingCumulant θ)) :=
  W.finiteCumulant_converges

/--
Debt surface for identifying the rate function as the Legendre transform of the
limiting cumulant.
-/
@[bridge_target_tag]
theorem rateFunction_is_legendre_readback
    (W : PrimeChainLargeDeviationWitness) :
    InfoGeometry.Convex.OneD.IsLegendreConjugate
      W.limitingCumulant W.rateFunction :=
  W.rateFunction_is_legendre

/--
Debt surface for the large-deviation principle itself.

No finite theorem in this owner file proves it.
-/
@[bridge_target_tag]
theorem largeDeviationPrinciple_readback
    (W : PrimeChainLargeDeviationWitness) :
    LargeDeviationPrinciple W.law W.speed W.rateFunction :=
  W.largeDeviationPrinciple

end PrimeChainLargeDeviationWitness

end InfoGeometry.Canonical.PrimeLeeYangLargeDeviation
