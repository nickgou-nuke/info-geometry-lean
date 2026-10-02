import InfoGeometry.Modular.ConnesCocycle
import InfoGeometry.Modular.NoncommutativeRadonNikodymDLog
import InfoGeometry.Prequantum.JaynesKLPotential
import InfoGeometry.Thermodynamics.FiniteConnesCocycle

namespace InfoGeometry.Canonical.ConnesRadonNikodymLogBridge

open InfoGeometry.Modular.ConnesCocycle
open InfoGeometry.Modular.NoncommutativeRN

inductive Archetype
  | modularFlow
  | connesCocycle
  | relativeLogarithm
  | logarithmicForm
  | fisherPairing
  deriving DecidableEq, Repr

def precedes : Archetype → Archetype → Prop
  | .modularFlow, .connesCocycle => True
  | .connesCocycle, .relativeLogarithm => True
  | .relativeLogarithm, .logarithmicForm => True
  | .logarithmicForm, .fisherPairing => True
  | _, _ => False

theorem causal_chain :
    precedes .modularFlow .connesCocycle ∧
    precedes .connesCocycle .relativeLogarithm ∧
    precedes .relativeLogarithm .logarithmicForm ∧
    precedes .logarithmicForm .fisherPairing :=
  ⟨trivial, trivial, trivial, trivial⟩

theorem cocycle_is_normalized
    {R A : Type*} [CommSemiring R] [StarRing R]
    [Ring A] [Algebra R A] [StarRing A] [StarModule R A]
    (σ : ModularFlow R A) (c : ConnesOneCocycle σ) :
    c.u 0 = 1 :=
  c.cocycle_zero

theorem cocycle_perturbed_flow_is_compositional
    {R A : Type*} [CommSemiring R] [StarRing R]
    [Ring A] [Algebra R A] [StarRing A] [StarModule R A]
    (σ : ModularFlow R A) (c : ConnesOneCocycle σ) (s t : ℝ) (x : A) :
    perturbedFlow c (s + t) x = perturbedFlow c s (perturbedFlow c t x) :=
  perturbedFlow_add c s t x

/-! ### Finite commuting scalar readout

These aliases expose the finite Cartan specialization without redefining its
carrier or cocycle. -/

theorem finite_cocycle_phase_additive
    {ι : Type*} (delta : ι → ℝ) (s t : ℝ) (i : ι) :
    InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhase
        delta (s + t) i =
      InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhase
        delta s i *
        InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhase
          delta t i :=
  InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhase_add_time
    delta s t i

theorem finite_density_ratio_generator
    {ι : Type*} (delta : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt
      (fun tau : ℝ =>
        InfoGeometry.Thermodynamics.FiniteConnesCocycle.finitePositiveDensityRatioAtTime
          delta tau i)
      ((-delta i) *
        InfoGeometry.Thermodynamics.FiniteConnesCocycle.finitePositiveDensityRatioAtTime
          delta t i)
      t :=
  InfoGeometry.Thermodynamics.FiniteConnesCocycle.finitePositiveDensityRatioAtTime_hasDerivAt
    delta t i

theorem relative_logarithm_chain_rule
    {A : Type*} [Ring A] (D : NoncommutativeDerivation A) (u v w : Aˣ) :
    dlogL D (rnUnit u v * rnUnit v w) =
      (↑(rnUnit v w)⁻¹ : A) * dlogL D (rnUnit u v) *
        (↑(rnUnit v w) : A) + dlogL D (rnUnit v w) := by
  rw [dlogL_mul_noncommutative]

theorem fisher_pairing_bound (p : ℝ) : p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

noncomputable def binaryRelativeEntropy (p : ℝ) : ℝ :=
  p * Real.log (2 * p) + (1 - p) * Real.log (2 * (1 - p))

noncomputable def binaryNegentropy (p : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p)

theorem binaryRelativeEntropy_decomposition (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    binaryRelativeEntropy p = Real.log 2 + binaryNegentropy p := by
  dsimp [binaryRelativeEntropy, binaryNegentropy]
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hq0 : 1 - p ≠ 0 := ne_of_gt hq
  rw [Real.log_mul (by norm_num) hp0, Real.log_mul (by norm_num) hq0]
  ring

theorem binaryRelativeEntropy_at_half :
    binaryRelativeEntropy (1 / 2) = 0 := by
  dsimp [binaryRelativeEntropy]
  have h : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [h]
  norm_num [Real.log_one]

theorem binaryRelativeEntropy_nonneg (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ binaryRelativeEntropy p := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have h0 := InfoGeometry.Prequantum.JaynesKLPotential.kl_divergence_nonneg
    p (1 / 2) hp (by norm_num)
  have h1 := InfoGeometry.Prequantum.JaynesKLPotential.kl_divergence_nonneg
    (1 - p) (1 / 2) hq (by norm_num)
  have h0' : p * Real.log (2 * p) = p * Real.log (p / (1 / 2 : ℝ)) := by
    congr 2
    ring
  have h1' : (1 - p) * Real.log (2 * (1 - p)) =
      (1 - p) * Real.log ((1 - p) / (1 / 2 : ℝ)) := by
    congr 2
    ring
  dsimp [binaryRelativeEntropy]
  rw [h0', h1']
  linarith

theorem logit_fisher_eq_quarter_iff (p : ℝ) :
    p * (1 - p) = 1 / 4 ↔ p = 1 / 2 := by
  constructor
  · intro h
    nlinarith [sq_nonneg (p - 1 / 2)]
  · intro h
    rw [h]
    norm_num

end InfoGeometry.Canonical.ConnesRadonNikodymLogBridge
