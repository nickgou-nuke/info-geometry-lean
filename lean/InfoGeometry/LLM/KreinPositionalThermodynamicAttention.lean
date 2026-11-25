/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.KreinAttentionEnergy
import InfoGeometry.LLM.KMSSoftmaxBridge
import InfoGeometry.LLM.ALiBi
import InfoGeometry.LLM.EarlyLearningFoundations
import InfoGeometry.Thermodynamics.SoftmaxGibbsVariationalPrinciple
import InfoGeometry.Clifford.SplitQ11
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Split-Signature Krein Positional Attention, Variational KMS Uniqueness, Souriau–Fisher Cumulants & Zero-Temperature Crystallization

Formalizes Corridor 3 ("Thermodynamic & Group-Theoretic Foundations of Transformers / LLMs"):

1. **Split-Signature `SO^+(1,1)` Boost Positional Encodings & Krein Attention Covariance:**
   - Explicit `2 × 2` Lorentzian boost subgroup `lorentzBoost2 η`, proving `lorentzBoost2_zero`,
     `lorentzBoost2_add`, `lorentzBoost2_det`, `lorentzBoost2_krein_isometry` (`Bᵀ η₁₁ B = η₁₁`),
     non-commutativity witness `exists_noncomm_krein_generators`, exact split-bilinear covariance
     `splitB11 (boostVec2 (ω * t) q) (boostVec2 (ω * s) k) = splitB11 (boostVec2 (ω * (t - s)) q) k`,
     and stacked multi-channel hyperbolic relative attention.

2. **Variational KMS/Gibbs Free-Energy Uniqueness & Goutev Gauge Invariance:**
   - Identifies `kreinAttentionWeights` with `SoftmaxGibbsVariational.gibbsState`.
   - Proves strict uniqueness of the free-energy minimizer (`gibbsState_unique_freeEnergy_minimizer`)
     via `EarlyLearningFoundations.klDivergence_eq_zero_iff`.
   - Proves Goutev additive energy gauge invariance (`H ↦ H + c`), ratio cocycle law
     `p_i / p_j = exp(-β (H_i - H_j))`, and specialization to `kreinAttentionWeights` and `ALiBi`.

3. **Souriau–Fisher Log-Partition Cumulant Metric:**
   - Proves exact cumulant derivatives `ψ'(β) = -𝔼_β[H]` (`hasDerivAt_tempLogPartition`) and
     `(-𝔼_β[H])'(β) = Var_β(H) ≥ 0` (`hasDerivAt_neg_gibbsMeanEnergy`), characterizing strict
     positivity vs. constant energy (`gibbsEnergyVariance_eq_zero_iff_const`).

4. **Zero-Temperature Argmax Crystallization (`β → +∞`):**
   - Proves exponential extinction of excited weights `p_β(i) → 0` (`H i > minEnergy H`),
     uniform ground-state crystallization `p_β(i) → 1 / |groundSet H|` (`H i = minEnergy H`),
     and zero-temperature Souriau–Fisher metric collapse `Var_β(H) → 0`.
-/

noncomputable section

namespace InfoGeometry.LLM.KreinPositionalThermodynamicAttention

open scoped BigOperators Matrix
open Filter
open InfoGeometry.Clifford
open InfoGeometry.Canonical.Attention
open InfoGeometry.LLM.KreinAttentionEnergy
open InfoGeometry.LLM.KMSSoftmaxBridge
open InfoGeometry.Thermodynamics.SoftmaxGibbsVariational

/-! ## 1. Split-Signature `SO^+(1,1)` Boost Group & Krein Attention Covariance -/

/-- Split-signature metric matrix `η₁₁ = diag(1, -1)`. -/
def eta11 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]

/-- Infinitesimal boost generator `K_boost = [[0, 1], [1, 0]]` (`K_boost² = I`). -/
def boostGen2 : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]

/-- Hyperbolic `SO^+(1,1)` boost matrix `exp(η K_boost)`. -/
def lorentzBoost2 (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![Real.cosh η, Real.sinh η], ![Real.sinh η, Real.cosh η]]

/-- Vector action of `lorentzBoost2 η` on `ℝ × ℝ`. -/
def boostVec2 (η : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cosh η * v.1 + Real.sinh η * v.2, Real.sinh η * v.1 + Real.cosh η * v.2)

private lemma scalar_cosh_mul_cosh_add_sinh_mul_sinh (s t : ℝ) :
    Real.cosh s * Real.cosh t + Real.sinh s * Real.sinh t = Real.cosh (s + t) := by
  rw [Real.cosh_add]

private lemma scalar_cosh_mul_sinh_add_sinh_mul_cosh (s t : ℝ) :
    Real.cosh s * Real.sinh t + Real.sinh s * Real.cosh t = Real.sinh (s + t) := by
  rw [Real.sinh_add]
  ring

private lemma scalar_sinh_mul_cosh_add_cosh_mul_sinh (s t : ℝ) :
    Real.sinh s * Real.cosh t + Real.cosh s * Real.sinh t = Real.sinh (s + t) := by
  rw [Real.sinh_add]

private lemma scalar_sinh_mul_sinh_add_cosh_mul_cosh (s t : ℝ) :
    Real.sinh s * Real.sinh t + Real.cosh s * Real.cosh t = Real.cosh (s + t) := by
  rw [Real.cosh_add, add_comm]

private lemma scalar_cosh_sq_sub_sinh_sq (η : ℝ) :
    Real.cosh η * Real.cosh η - Real.sinh η * Real.sinh η = 1 := by
  simpa [sq] using Real.cosh_sq_sub_sinh_sq η

private lemma scalar_boost_split_bilinear (s t q1 q2 k1 k2 : ℝ) :
    (Real.cosh t * q1 + Real.sinh t * q2) * (Real.cosh s * k1 + Real.sinh s * k2) -
        (Real.sinh t * q1 + Real.cosh t * q2) * (Real.sinh s * k1 + Real.cosh s * k2) =
      (Real.cosh (t - s) * q1 + Real.sinh (t - s) * q2) * k1 -
        (Real.sinh (t - s) * q1 + Real.cosh (t - s) * q2) * k2 := by
  rw [Real.cosh_sub, Real.sinh_sub]
  ring

theorem lorentzBoost2_zero : lorentzBoost2 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentzBoost2]

theorem lorentzBoost2_add (s t : ℝ) :
    lorentzBoost2 (s + t) = lorentzBoost2 s * lorentzBoost2 t := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [lorentzBoost2]
  · exact (scalar_cosh_mul_cosh_add_sinh_mul_sinh s t).symm
  · exact (scalar_cosh_mul_sinh_add_sinh_mul_cosh s t).symm
  · exact (scalar_sinh_mul_cosh_add_cosh_mul_sinh s t).symm
  · exact (scalar_sinh_mul_sinh_add_cosh_mul_cosh s t).symm

theorem lorentzBoost2_det (η : ℝ) : (lorentzBoost2 η).det = 1 := by
  rw [Matrix.det_fin_two]
  simpa [lorentzBoost2] using scalar_cosh_sq_sub_sinh_sq η

private lemma scalar_krein_diag (η : ℝ) :
    Real.cosh η * Real.cosh η + -(Real.sinh η * Real.sinh η) = 1 := by
  simpa [sub_eq_add_neg] using scalar_cosh_sq_sub_sinh_sq η

private lemma scalar_krein_diag_neg (η : ℝ) :
    Real.sinh η * Real.sinh η + -(Real.cosh η * Real.cosh η) = -1 := by
  linarith [scalar_cosh_sq_sub_sinh_sq η]

theorem lorentzBoost2_krein_isometry (η : ℝ) :
    (lorentzBoost2 η)ᵀ * eta11 * lorentzBoost2 η = eta11 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [lorentzBoost2, eta11] <;> simp
  · exact scalar_krein_diag η
  · exact add_neg_eq_zero.mpr (mul_comm (Real.cosh η) (Real.sinh η))
  · exact add_neg_eq_zero.mpr (mul_comm (Real.sinh η) (Real.cosh η))
  · exact scalar_krein_diag_neg η

theorem boostGen2_sq : boostGen2 * boostGen2 = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [boostGen2] <;> norm_num

theorem eta11_sq : eta11 * eta11 = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [eta11] <;> norm_num

theorem eta11_mul_boostGen2_anticomm :
    eta11 * boostGen2 = -(boostGen2 * eta11) := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [eta11, boostGen2] <;> norm_num

/-- Closed non-commutativity witness for split-signature Krein generators (`η₁₁` vs `K_boost`). -/
theorem exists_noncomm_krein_generators :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨eta11, boostGen2, ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h01
  dsimp [eta11, boostGen2] at h01
  norm_num at h01

theorem boostVec2_zero (v : ℝ × ℝ) : boostVec2 0 v = v := by
  ext <;> simp [boostVec2]

theorem boostVec2_add (s t : ℝ) (v : ℝ × ℝ) :
    boostVec2 (s + t) v = boostVec2 s (boostVec2 t v) := by
  ext
  · simp only [boostVec2, Real.cosh_add, Real.sinh_add]
    ring
  · simp only [boostVec2, Real.cosh_add, Real.sinh_add]
    ring

/-- **Relative-rapidity covariance of split-signature `splitB11`**: boosting query by `ω t` and
key by `ω s` equals boosting query by relative position `ω (t - s)`. -/
theorem splitB11_boostVec2_relative (ω t s : ℝ) (q k : ℝ × ℝ) :
    splitB11 (boostVec2 (ω * t) q) (boostVec2 (ω * s) k) =
      splitB11 (boostVec2 (ω * (t - s)) q) k := by
  have hsub : ω * t - ω * s = ω * (t - s) := by ring
  rw [← hsub]
  simpa [splitB11_apply, boostVec2] using
    scalar_boost_split_bilinear (ω * s) (ω * t) q.1 q.2 k.1 k.2

/-- Exact translation invariance of hyperbolic Krein interaction energy under boost encodings. -/
theorem kreinInteractionEnergy_boost_relative (ω t s : ℝ) (q k : ℝ × ℝ) :
    kreinInteractionEnergy (boostVec2 (ω * t) q) (boostVec2 (ω * s) k) =
      kreinInteractionEnergy (boostVec2 (ω * (t - s)) q) k := by
  unfold kreinInteractionEnergy interactionEnergy
  rw [splitB11_boostVec2_relative]

theorem kreinInteractionEnergy_boost_shift_invariant (ω t s a : ℝ) (q k : ℝ × ℝ) :
    kreinInteractionEnergy (boostVec2 (ω * (t + a)) q) (boostVec2 (ω * (s + a)) k) =
      kreinInteractionEnergy (boostVec2 (ω * t) q) (boostVec2 (ω * s) k) := by
  rw [kreinInteractionEnergy_boost_relative, kreinInteractionEnergy_boost_relative]
  have hts : t + a - (s + a) = t - s := by ring
  rw [hts]

/-- Multi-channel stacked hyperbolic Krein attention score across `m` rapidity channels. -/
def stackedKreinEnergy {m : ℕ} (q k : Fin m → ℝ × ℝ) : ℝ :=
  ∑ c : Fin m, kreinInteractionEnergy (q c) (k c)

theorem stackedKreinEnergy_boost_relative {m : ℕ} (freqs : Fin m → ℝ) (t s : ℝ)
    (q k : Fin m → ℝ × ℝ) :
    stackedKreinEnergy (fun c => boostVec2 (freqs c * t) (q c))
        (fun c => boostVec2 (freqs c * s) (k c)) =
      stackedKreinEnergy (fun c => boostVec2 (freqs c * (t - s)) (q c)) k := by
  unfold stackedKreinEnergy
  refine Finset.sum_congr rfl fun c _ => ?_
  exact kreinInteractionEnergy_boost_relative (freqs c) t s (q c) (k c)

/-! ## 2. Variational KMS/Gibbs Free-Energy Uniqueness & Goutev Gauge Invariance -/

/-- Exact identification of `kreinAttentionWeights` with `SoftmaxGibbsVariational.gibbsState`. -/
theorem kreinAttentionWeights_eq_gibbsState
    {n : ℕ} [Fact (0 < n)] {V : Type*}
    (q : ℝ × ℝ) (ctx : ContextWindow n (ℝ × ℝ) V)
    (T : InverseTemperature) (i : Fin n) :
    kreinAttentionWeights q ctx T.beta i =
      gibbsState T (fun j => kreinInteractionEnergy q (ctx.keys j)) i := by
  change InfoGeometry.GrandCanonical.gibbsWeight (attentionParams q ctx splitB11) T.beta i =
    gibbsState T (fun j => kreinInteractionEnergy q (ctx.keys j)) i
  simp [InfoGeometry.GrandCanonical.gibbsWeight, InfoGeometry.GrandCanonical.partition,
    attentionParams, kreinInteractionEnergy, gibbsState, partitionSum]

/-- **Strict Variational Uniqueness of the Gibbs / Softmax State**:
on positive normalized simplex distributions `p`, free energy achieves its minimum
`-(1/β) log Z` if and only if `p = gibbsState T H` everywhere. -/
theorem gibbsState_unique_freeEnergy_minimizer
    {I : Type*} [Fintype I] [Nonempty I]
    (T : InverseTemperature) (H : I → ℝ) (p : I → ℝ)
    (hp_sum : ∑ i : I, p i = 1)
    (hp_pos : ∀ i : I, 0 < p i) :
    freeEnergy T H p = -(1 / T.beta) * Real.log (partitionSum T H) ↔ p = gibbsState T H := by
  have hdiff := freeEnergy_sub_equilibrium_eq_kl T H p hp_sum hp_pos
  have hkl_eq :
      InfoGeometry.Thermodynamics.SoftmaxGibbsVariational.klDivergence p (gibbsState T H) =
        InfoGeometry.LLM.EarlyLearningFoundations.klDivergence p (gibbsState T H) := rfl
  have hinv_ne : (1 / T.beta : ℝ) ≠ 0 := one_div_ne_zero T.beta_ne_zero
  constructor
  · intro hmin
    have hmul0 : (1 / T.beta) *
        InfoGeometry.Thermodynamics.SoftmaxGibbsVariational.klDivergence p (gibbsState T H) = 0 := by
      linarith [hdiff, hmin]
    have hkl0 : InfoGeometry.LLM.EarlyLearningFoundations.klDivergence p (gibbsState T H) = 0 := by
      rcases mul_eq_zero.mp hmul0 with h1 | h2
      · exact absurd h1 hinv_ne
      · simpa [hkl_eq] using h2
    exact (InfoGeometry.LLM.EarlyLearningFoundations.klDivergence_eq_zero_iff
      hp_pos (gibbsState_pos T H) hp_sum (gibbsState_sum_one T H)).mp hkl0
  · intro hp_eq
    subst hp_eq
    exact freeEnergy_gibbsState T H

/-- **Goutev Gauge Invariance**: shifting every energy level `H i ↦ H i + c` shifts `log Z` by
`-β c` and leaves `gibbsState T H` strictly invariant (projective / relational invariance). -/
theorem partitionSum_energy_shift
    {I : Type*} [Fintype I] [Nonempty I]
    (T : InverseTemperature) (H : I → ℝ) (c : ℝ) :
    partitionSum T (fun i => H i + c) = Real.exp (-T.beta * c) * partitionSum T H := by
  unfold partitionSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have harg : -T.beta * (H i + c) = -T.beta * c + -T.beta * H i := by ring
  rw [harg, Real.exp_add]

theorem gibbsState_energy_shift_invariant
    {I : Type*} [Fintype I] [Nonempty I]
    (T : InverseTemperature) (H : I → ℝ) (c : ℝ) (i : I) :
    gibbsState T (fun j => H j + c) i = gibbsState T H i := by
  unfold gibbsState
  rw [partitionSum_energy_shift]
  have harg : -T.beta * (H i + c) = -T.beta * c + -T.beta * H i := by ring
  have hne : Real.exp (-T.beta * c) ≠ 0 := (Real.exp_pos _).ne'
  rw [harg, Real.exp_add, mul_div_mul_left _ _ hne]

/-- **Goutev Ratio Cocycle Law**: ratio of Gibbs weights depends solely on the relative energy
difference `H i - H j`, independent of any absolute energy origin or normalization factor. -/
theorem gibbsState_ratio_eq_exp_neg_diff
    {I : Type*} [Fintype I] [Nonempty I]
    (T : InverseTemperature) (H : I → ℝ) (i j : I) :
    gibbsState T H i / gibbsState T H j = Real.exp (-T.beta * (H i - H j)) := by
  unfold gibbsState
  have hZ : partitionSum T H ≠ 0 := partitionSum_ne_zero T H
  rw [div_div_div_cancel_right₀ hZ, ← Real.exp_sub]
  congr 1
  ring

/-- ALiBi score bias satisfies exact translation invariance when wrapped inside Gibbs equilibrium weights
(`H_j(t, s_j) ↦ -alibiScore dot p q k_j t s_j`). -/
theorem alibi_gibbsState_shift_invariant
    {n : ℕ} [Fact (0 < n)] {Q : Type*} (dot : Q → Q → ℝ)
    (p : ℝ) (q : Q) (k : Fin n → Q) (s : Fin n → ℝ) (t a : ℝ) (T : InverseTemperature) :
    gibbsState T (fun j => -alibiScore dot p q (k j) (t + a) (s j + a)) =
      gibbsState T (fun j => -alibiScore dot p q (k j) t (s j)) := by
  funext i
  congr 1
  funext j
  rw [alibiScore_translation_invariant]

/-! ## 3. Souriau–Fisher Log-Partition Cumulant Metric -/

/-- Unconstrained-temperature partition sum `Z(β, H) = ∑ᵢ exp(-β Hᵢ)`. -/
def tempPartitionSum {I : Type*} [Fintype I] (H : I → ℝ) (β : ℝ) : ℝ :=
  ∑ i : I, Real.exp (-β * H i)

/-- Log-partition (Massieu) potential `ψ(β) = log ∑ᵢ exp(-β Hᵢ)`. -/
def tempLogPartition {I : Type*} [Fintype I] (H : I → ℝ) (β : ℝ) : ℝ :=
  Real.log (tempPartitionSum H β)

/-- Gibbs distribution `p_β(i) = exp(-β Hᵢ) / Z(β, H)` for arbitrary `β : ℝ`. -/
def tempGibbsWeight {I : Type*} [Fintype I] (H : I → ℝ) (β : ℝ) (i : I) : ℝ :=
  Real.exp (-β * H i) / tempPartitionSum H β

/-- Thermal mean energy `𝔼_β[H] = ∑ᵢ p_β(i) Hᵢ`. -/
def gibbsMeanEnergy {I : Type*} [Fintype I] (H : I → ℝ) (β : ℝ) : ℝ :=
  ∑ i : I, tempGibbsWeight H β i * H i

/-- Souriau–Fisher inverse-temperature variance `g_H^{SF}(β) = ∑ᵢ p_β(i) (Hᵢ - 𝔼_β[H])^2`. -/
def gibbsEnergyVariance {I : Type*} [Fintype I] (H : I → ℝ) (β : ℝ) : ℝ :=
  ∑ i : I, tempGibbsWeight H β i * (H i - gibbsMeanEnergy H β) ^ 2

theorem tempPartitionSum_pos {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    0 < tempPartitionSum H β :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem tempGibbsWeight_pos {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) (i : I) :
    0 < tempGibbsWeight H β i :=
  div_pos (Real.exp_pos _) (tempPartitionSum_pos H β)

theorem tempGibbsWeight_sum_one {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    ∑ i : I, tempGibbsWeight H β i = 1 := by
  unfold tempGibbsWeight
  rw [← Finset.sum_div]
  exact div_self (tempPartitionSum_pos H β).ne'

private lemma hasDerivAt_tempPartitionSum {I : Type*} [Fintype I] (H : I → ℝ) (β : ℝ) :
    HasDerivAt (tempPartitionSum H) (-(∑ i : I, Real.exp (-β * H i) * H i)) β := by
  have h_term : ∀ i ∈ (Finset.univ : Finset I),
      HasDerivAt (fun x : ℝ => Real.exp (-x * H i)) (-(Real.exp (-β * H i) * H i)) β := by
    intro i _
    have h_lin : HasDerivAt (fun x : ℝ => -x * H i) (-H i) β := by
      simpa using (hasDerivAt_id β).neg.mul_const (H i)
    convert h_lin.exp using 1
    ring
  have hsum := HasDerivAt.fun_sum h_term
  have heq : (fun x => ∑ i : I, Real.exp (-x * H i)) = tempPartitionSum H := by
    funext x; rfl
  have hder : (∑ i : I, -(Real.exp (-β * H i) * H i)) = -(∑ i : I, Real.exp (-β * H i) * H i) := by
    rw [Finset.sum_neg_distrib]
  rw [heq, hder] at hsum
  exact hsum

/-- First cumulant identity: `d/dβ log Z(β, H) = -𝔼_β[H]`. -/
theorem hasDerivAt_tempLogPartition {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    HasDerivAt (tempLogPartition H) (-gibbsMeanEnergy H β) β := by
  have hlog := (hasDerivAt_tempPartitionSum H β).log (tempPartitionSum_pos H β).ne'
  have heq : (fun x => Real.log (tempPartitionSum H x)) = tempLogPartition H := rfl
  rw [heq] at hlog
  convert hlog using 1
  unfold gibbsMeanEnergy tempGibbsWeight
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, neg_div]

private lemma gibbsEnergyVariance_eq_secondMoment_sub_sq
    {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    gibbsEnergyVariance H β =
      (∑ i : I, tempGibbsWeight H β i * H i ^ 2) - (gibbsMeanEnergy H β) ^ 2 := by
  unfold gibbsEnergyVariance
  have h1 : ∀ i : I,
      tempGibbsWeight H β i * (H i - gibbsMeanEnergy H β) ^ 2 =
        tempGibbsWeight H β i * H i ^ 2 - 2 * gibbsMeanEnergy H β * (tempGibbsWeight H β i * H i) +
          (gibbsMeanEnergy H β) ^ 2 * tempGibbsWeight H β i := by
    intro i
    ring
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [tempGibbsWeight_sum_one]
  change (∑ i : I, tempGibbsWeight H β i * H i ^ 2) - 2 * gibbsMeanEnergy H β * gibbsMeanEnergy H β +
      (gibbsMeanEnergy H β) ^ 2 * 1 =
    (∑ i : I, tempGibbsWeight H β i * H i ^ 2) - (gibbsMeanEnergy H β) ^ 2
  ring

/-- Second cumulant identity: `d/dβ (-𝔼_β[H]) = Var_β(H)` (Souriau–Fisher metric). -/
theorem hasDerivAt_neg_gibbsMeanEnergy {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    HasDerivAt (fun x => -gibbsMeanEnergy H x) (gibbsEnergyVariance H β) β := by
  have hnum :
      HasDerivAt (fun x => -(∑ i : I, Real.exp (-x * H i) * H i))
        (∑ i : I, Real.exp (-β * H i) * H i ^ 2) β := by
    have ht : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun x : ℝ => -(Real.exp (-x * H i) * H i))
          (Real.exp (-β * H i) * H i ^ 2) β := by
      intro i _
      have h_lin : HasDerivAt (fun x : ℝ => -x * H i) (-H i) β := by
        simpa using (hasDerivAt_id β).neg.mul_const (H i)
      convert (h_lin.exp.mul_const (H i)).neg using 1
      ring
    have hsum := HasDerivAt.fun_sum ht
    have heq : (fun x => ∑ i : I, -(Real.exp (-x * H i) * H i)) =
        (fun x => -(∑ i : I, Real.exp (-x * H i) * H i)) := by
      funext x
      rw [Finset.sum_neg_distrib]
    rw [heq] at hsum
    exact hsum
  have hden := hasDerivAt_tempPartitionSum H β
  have hZne : tempPartitionSum H β ≠ 0 := (tempPartitionSum_pos H β).ne'
  have hdiv := hnum.fun_div hden hZne
  have heq : (fun x => -gibbsMeanEnergy H x) =
      (fun x => (-(∑ i : I, Real.exp (-x * H i) * H i)) / tempPartitionSum H x) := by
    funext x
    unfold gibbsMeanEnergy tempGibbsWeight
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, neg_div]
  rw [heq]
  convert hdiv using 1
  rw [gibbsEnergyVariance_eq_secondMoment_sub_sq]
  have hsum_num :
      (∑ i : I, Real.exp (-β * H i) * H i ^ 2) / tempPartitionSum H β =
        ∑ i : I, tempGibbsWeight H β i * H i ^ 2 := by
    unfold tempGibbsWeight
    simp_rw [div_mul_eq_mul_div, Finset.sum_div]
  have hmean_num :
      (-(∑ i : I, Real.exp (-β * H i) * H i)) / tempPartitionSum H β = -gibbsMeanEnergy H β := by
    unfold gibbsMeanEnergy tempGibbsWeight
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, neg_div]
  rw [← neg_sq (gibbsMeanEnergy H β), ← hsum_num, ← hmean_num]
  field_simp [hZne]

theorem gibbsEnergyVariance_nonneg {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    0 ≤ gibbsEnergyVariance H β := by
  unfold gibbsEnergyVariance
  exact Finset.sum_nonneg fun i _ => mul_nonneg (tempGibbsWeight_pos H β i).le (sq_nonneg _)

/-- The Souriau–Fisher variance vanishes at `β` iff the Hamiltonian `H` is constant. -/
theorem gibbsEnergyVariance_eq_zero_iff_const
    {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    gibbsEnergyVariance H β = 0 ↔ ∃ c : ℝ, ∀ i : I, H i = c := by
  constructor
  · intro hzero
    refine ⟨gibbsMeanEnergy H β, fun i => ?_⟩
    have hnonneg : ∀ j ∈ (Finset.univ : Finset I),
        0 ≤ tempGibbsWeight H β j * (H j - gibbsMeanEnergy H β) ^ 2 := fun j _ =>
      mul_nonneg (tempGibbsWeight_pos H β j).le (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hterm with hw | hsq
    · exact absurd hw (tempGibbsWeight_pos H β i).ne'
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · rintro ⟨c, hc⟩
    have hmean : gibbsMeanEnergy H β = c := by
      unfold gibbsMeanEnergy
      simp_rw [hc, ← Finset.sum_mul, tempGibbsWeight_sum_one, one_mul]
    unfold gibbsEnergyVariance
    simp [hc, hmean]

/-! ## 4. Zero-Temperature Argmax Crystallization (`β → +∞`) -/

/-- Minimum attention energy `E_min = minᵢ Hᵢ`. -/
def minEnergy {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty H

/-- Argmin ground set `G(H) = {i | H i = E_min}`. -/
def groundSet {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) : Finset I :=
  Finset.univ.filter fun i => H i = minEnergy H

theorem minEnergy_le {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (i : I) :
    minEnergy H ≤ H i :=
  Finset.inf'_le H (Finset.mem_univ i)

theorem groundSet_nonempty {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) :
    (groundSet H).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty H
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.symm⟩⟩

private lemma tempPartitionSum_factor_min {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) :
    tempPartitionSum H β =
      Real.exp (-β * minEnergy H) *
        ((groundSet H).card +
          ∑ j ∈ Finset.univ.filter (fun j => minEnergy H < H j),
            Real.exp (-β * (H j - minEnergy H))) := by
  classical
  unfold tempPartitionSum
  have hsplit :
      ∀ i : I, Real.exp (-β * H i) = Real.exp (-β * minEnergy H) * Real.exp (-β * (H i - minEnergy H)) := by
    intro i
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hsplit, ← Finset.mul_sum]
  congr 1
  have hpart :
      (Finset.univ : Finset I) =
        groundSet H ∪ Finset.univ.filter (fun j => minEnergy H < H j) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_union, groundSet, Finset.mem_filter, true_and, true_iff]
    exact (eq_or_lt_of_le (minEnergy_le H j)).imp Eq.symm id
  have hdisj : Disjoint (groundSet H) (Finset.univ.filter fun j => minEnergy H < H j) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [groundSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    linarith
  conv_lhs => rw [hpart]
  rw [Finset.sum_union hdisj]
  have hground :
      ∑ j ∈ groundSet H, Real.exp (-β * (H j - minEnergy H)) = ((groundSet H).card : ℝ) := by
    calc
      ∑ j ∈ groundSet H, Real.exp (-β * (H j - minEnergy H))
          = ∑ _j ∈ groundSet H, (1 : ℝ) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj' : H j = minEnergy H := (Finset.mem_filter.mp hj).2
              simp [hj']
      _ = ((groundSet H).card : ℝ) := by simp
  rw [hground]

/-- Exponential upper bound on excited-state weights `p_β(i) ≤ exp(-β (H i - E_min))` for all `β : ℝ`. -/
theorem tempGibbsWeight_excited_le_exp
    {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) (β : ℝ) (i : I) :
    tempGibbsWeight H β i ≤ Real.exp (-β * (H i - minEnergy H)) := by
  unfold tempGibbsWeight
  rw [tempPartitionSum_factor_min]
  have hexp_eq :
      Real.exp (-β * H i) = Real.exp (-β * minEnergy H) * Real.exp (-β * (H i - minEnergy H)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hne : Real.exp (-β * minEnergy H) ≠ 0 := (Real.exp_pos _).ne'
  rw [hexp_eq, mul_div_mul_left _ _ hne]
  have hcard : (1 : ℝ) ≤ (groundSet H).card := by
    exact_mod_cast Finset.card_pos.mpr (groundSet_nonempty H)
  have hrest :
      0 ≤ ∑ j ∈ Finset.univ.filter (fun j => minEnergy H < H j),
        Real.exp (-β * (H j - minEnergy H)) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  exact div_le_self (Real.exp_pos _).le (by linarith)

/-- Any non-ground token weight `p_β(i)` (`H i > minEnergy H`) vanishes exponentially as `β → +∞`. -/
theorem tempGibbsWeight_excited_tendsto_zero
    {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) {i : I} (hi : minEnergy H < H i) :
    Tendsto (fun β : ℝ => tempGibbsWeight H β i) atTop (nhds 0) := by
  have hgap : 0 < H i - minEnergy H := sub_pos.mpr hi
  have hlim_exp : Tendsto (fun β : ℝ => Real.exp (-β * (H i - minEnergy H))) atTop (nhds 0) := by
    have hmul : Tendsto (fun β : ℝ => (-β) * (H i - minEnergy H)) atTop atBot :=
      Tendsto.atBot_mul_const hgap tendsto_neg_atTop_atBot
    exact Real.tendsto_exp_atBot.comp hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_exp
    (Eventually.of_forall fun β => (tempGibbsWeight_pos H β i).le)
    (Eventually.of_forall fun β => tempGibbsWeight_excited_le_exp H β i)

/-- Every ground-state token (`H i = minEnergy H`) converges to the uniform ground distribution
`1 / |groundSet H|` as `β → +∞` (zero-temperature argmax crystallization). -/
theorem tempGibbsWeight_ground_tendsto_inv_card
    {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) {i : I} (hi : H i = minEnergy H) :
    Tendsto (fun β : ℝ => tempGibbsWeight H β i) atTop (nhds ((groundSet H).card : ℝ)⁻¹) := by
  let tail : ℝ → ℝ := fun β =>
    ∑ j ∈ Finset.univ.filter (fun j => minEnergy H < H j), Real.exp (-β * (H j - minEnergy H))
  have htail : Tendsto tail atTop (nhds 0) := by
    have hzero : (0 : ℝ) = ∑ _j ∈ Finset.univ.filter (fun j => minEnergy H < H j), (0 : ℝ) := by
      simp
    rw [hzero]
    refine tendsto_finset_sum _ fun j hj => ?_
    have hj_gt : minEnergy H < H j := (Finset.mem_filter.mp hj).2
    have hgap : 0 < H j - minEnergy H := sub_pos.mpr hj_gt
    exact Real.tendsto_exp_atBot.comp (Tendsto.atBot_mul_const hgap tendsto_neg_atTop_atBot)
  have hden_lim :
      Tendsto (fun β : ℝ => ((groundSet H).card : ℝ) + tail β) atTop (nhds ((groundSet H).card : ℝ)) := by
    simpa using htail.const_add ((groundSet H).card : ℝ)
  have hcard_ne : ((groundSet H).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (groundSet_nonempty H)).ne'
  have hinv_lim :
      Tendsto (fun β : ℝ => (((groundSet H).card : ℝ) + tail β)⁻¹) atTop
        (nhds ((groundSet H).card : ℝ)⁻¹) :=
    hden_lim.inv₀ hcard_ne
  refine hinv_lim.congr fun β => ?_
  unfold tempGibbsWeight
  rw [tempPartitionSum_factor_min]
  have hne : Real.exp (-β * minEnergy H) ≠ 0 := (Real.exp_pos _).ne'
  rw [hi, ← one_div, div_mul_eq_div_div, div_self hne, one_div]

/-- Souriau–Fisher metric collapse at zero temperature: `Var_β(H) → 0` as `β → +∞`. -/
theorem gibbsEnergyVariance_tendsto_zero
    {I : Type*} [Fintype I] [Nonempty I] (H : I → ℝ) :
    Tendsto (fun β : ℝ => gibbsEnergyVariance H β) atTop (nhds 0) := by
  classical
  have hmean_lim : Tendsto (fun β : ℝ => gibbsMeanEnergy H β) atTop (nhds (minEnergy H)) := by
    have hsum_target :
        (∑ i : I, (if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ else 0) * H i) =
          minEnergy H := by
      have hite :
          (∑ i : I, (if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ else 0) * H i) =
            ∑ i : I, if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ * H i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ite_mul, zero_mul]
      calc
        (∑ i : I, (if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ else 0) * H i)
            = ∑ i : I, if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ * H i else 0 := hite
        _ = ∑ i ∈ groundSet H, ((groundSet H).card : ℝ)⁻¹ * H i := by
              rw [← Finset.sum_filter]
              rfl
        _ = ∑ _i ∈ groundSet H, ((groundSet H).card : ℝ)⁻¹ * minEnergy H := by
              refine Finset.sum_congr rfl fun i hi' => ?_
              have hi'' : H i = minEnergy H := (Finset.mem_filter.mp hi').2
              rw [hi'']
        _ = ((groundSet H).card : ℝ) * (((groundSet H).card : ℝ)⁻¹ * minEnergy H) := by simp
        _ = minEnergy H := by
              have hne : ((groundSet H).card : ℝ) ≠ 0 := by
                exact_mod_cast (Finset.card_pos.mpr (groundSet_nonempty H)).ne'
              field_simp [hne]
    rw [← hsum_target]
    refine tendsto_finset_sum _ fun i _ => ?_
    refine Tendsto.mul_const (H i) ?_
    by_cases hi : H i = minEnergy H
    · simp only [hi, ↓reduceIte]
      exact tempGibbsWeight_ground_tendsto_inv_card H hi
    · have hi_gt : minEnergy H < H i := lt_of_le_of_ne (minEnergy_le H i) (Ne.symm hi)
      simp only [hi, ↓reduceIte]
      exact tempGibbsWeight_excited_tendsto_zero H hi_gt
  have hvar_zero :
      (∑ i : I, (if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ else 0) *
        (H i - minEnergy H) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : H i = minEnergy H
    · simp [hi]
    · simp [hi]
  rw [← hvar_zero]
  unfold gibbsEnergyVariance
  refine tendsto_finset_sum _ fun i _ => ?_
  have hw : Tendsto (fun β : ℝ => tempGibbsWeight H β i) atTop
      (nhds (if H i = minEnergy H then ((groundSet H).card : ℝ)⁻¹ else 0)) := by
    by_cases hi : H i = minEnergy H
    · simp only [hi, ↓reduceIte]
      exact tempGibbsWeight_ground_tendsto_inv_card H hi
    · have hi_gt : minEnergy H < H i := lt_of_le_of_ne (minEnergy_le H i) (Ne.symm hi)
      simp only [hi, ↓reduceIte]
      exact tempGibbsWeight_excited_tendsto_zero H hi_gt
  have hdiff_sq :
      Tendsto (fun β : ℝ => (H i - gibbsMeanEnergy H β) ^ 2) atTop
        (nhds ((H i - minEnergy H) ^ 2)) :=
    ((tendsto_const_nhds.sub hmean_lim).pow 2)
  exact hw.mul hdiff_sq

end InfoGeometry.LLM.KreinPositionalThermodynamicAttention
