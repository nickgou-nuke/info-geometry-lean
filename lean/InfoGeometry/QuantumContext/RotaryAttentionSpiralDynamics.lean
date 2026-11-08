/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.PlanarRotation
import InfoGeometry.Routing.DiscreteRoPERepresentation
import InfoGeometry.Routing.CliffordRoPETorus
import InfoGeometry.QuantumContext.TransformerLatentSpace
import InfoGeometry.QuantumContext.MarkovMetriplecticReversibleRotation
import InfoGeometry.QuantumContext.MarkovMetriplecticQuadraticDecay
import InfoGeometry.QuantumContext.AttentionKMSState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Finite Softmax, RoPE, Radial Normalization, and Metriplectic Identities

This module collects finite identities from the repository's planar rotation, discrete RoPE,
Clifford torus, transformer softmax attention, KMS attention state, and Markov metriplectic owners
(`PlanarRotation`, `DiscreteRoPERepresentation`, `CliffordRoPETorus`,
`TransformerLatentSpace`, `AttentionKMSState`, `MarkovMetriplecticReversibleRotation`,
`MarkovMetriplecticQuadraticDecay`):

1. **Archetype I — Finite Softmax Attention Coupling, Row-Stochasticity, Directed Asymmetry, and Anchor-Column Positivity**:
   - Defines `attentionCouplingMatrix scores β` via `AttentionKMSState.softmaxWeight`,
     proves strict positivity, row normalization, membership in `Matrix.rowStochastic`,
     and identifies `β = 1` on `Fin 2` with `TransformerLatentSpace.softmaxAttention`.
   - Defines `stationaryAttentionCoupling logits β` and proves both `Matrix.rowStochastic`
     membership and `InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β)`.
   - Constructs the explicit 2-token directed asymmetry witness `asymmetricScores`
     proving `attentionCouplingMatrix asymmetricScores β 0 1 ≠ attentionCouplingMatrix asymmetricScores β 1 0`
     for all `β ≠ 0` (and `∃ scores, softmaxAttention scores 0 1 ≠ softmaxAttention scores 1 0`),
     together with positivity of the pruned state energy on an anchor column of
     `attentionCouplingMatrix`.

2. **Archetype II — Rotary Position Embeddings (RoPE) as an $\mathrm{SO}(2)$ Phase Clock & Clifford Bivector Torus**:
   - Bridges `PlanarRotation.rotation`, `PlanarRotation.ellipticGenerator`, and
     `DiscreteRoPERepresentation.ropeRotor` with `CliffordRoPETorus.EllipticBivectorTorus`
     (`planarEllipticBivectorTorus_R_plane_eq_rotation`) and with
     `MarkovDrazin.ReversibleRotation.coordinateSkewMatrix`
     (`coordinateSkewMatrix_zero_one_eq_neg_ellipticGenerator`).
   - Proves Euclidean dot-product and squared-norm preservation under `PlanarRotation.rotation`
     and establishes relative-position dot-product invariance `rope_dotProduct_relative_invariance`:
     the inner product of RoPE-rotated query $q$ at position $m$ and key $k$ at position $n$
     depends purely on $n - m$.

3. **Archetype III — Radial Normalization onto $S^1(\gamma)$ & Exact RoPE Equivariance**:
   - Defines `sphericalNorm2 γ v`, a radial normalization map (not the full Transformer
     LayerNorm or RMSNorm operation), and proves the exact circle constraint
     `vecNormSq2 (sphericalNorm2 γ v) = γ ^ 2` for `0 < vecNormSq2 v`, positive radial scale
     invariance `sphericalNorm2_smul_pos`, and exact commutation with RoPE rotations
     `ropeAct_sphericalNorm2_comm`.

4. **Archetype IV — A Defined Logarithmic-Spiral Ansatz & Its Radial-Normalization Identity**:
   - Defines the vector path `spiralTrajectory a b θ t v₀ = spiralRadius a b θ t • ropeAct (θ * t) v₀`,
     proving the exact radial norm envelope, strict dissipative radial contraction for `b < 0`,
     the additive flow law, and its image under `sphericalNorm2`. This path is a separate
     algebraic definition; it is not derived from softmax attention, a sink force, or a
     Transformer layer update.

5. **Archetype V — Orbital Resonance, Periodic Limit Cycles & Metriplectic Quadratic Decay Bridge**:
   - Proves $2\pi$-periodicity of `PlanarRotation.rotation` and resonant $p$-step periodicity
     `sphericalNorm2_spiralTrajectory_resonant_periodic` when $p \cdot \theta = 2\pi$.
   - Connects `PlanarRotation.ellipticGenerator` and `AttentionKMSState.softmaxWeight`
     directly to `MarkovDrazin.weightedMatrixPairing_quadratic_decay_eq` and
     `MarkovDrazin.weightedSkewAction_quadratic_decay_nonpos`, and instantiates the
     unconditional corollary `stationaryAttentionCoupling_ellipticGenerator_quadratic_decay_nonpos`
     using `stationaryAttentionCoupling`.

## Scope Note

This module formalizes finite-dimensional matrix and vector dynamics on `Fin 2 → ℝ`,
`Mat2 = Matrix (Fin 2) (Fin 2) ℝ`, and `Matrix ι ι ℝ` for `[Fintype ι]`.
1. The general directed attention coupling `attentionCouplingMatrix` is a row-stochastic finite
   softmax coupling; it is not claimed to be a symmetric potential gradient or a
   detailed-balance reversible chain unless an explicit `DetailedBalance` hypothesis is supplied
   (as instantiated on `stationaryAttentionCoupling`).
2. The logarithmic spiral `spiralTrajectory` and its normalization `sphericalNorm2` model
   2D RoPE sub-plane trajectories and radial projection directly; they do not claim global
   convergence of arbitrary deep multi-layer nonlinear transformer networks.
3. The spiral and split-rotation constructions are independent finite-dimensional models;
   no theorem identifies them with a Transformer trajectory or a sink-generated potential.
4. The metriplectic decay theorems (`ellipticGenerator_markovOnsager_quadratic_decay_eq`,
   `ellipticGenerator_markovOnsager_quadratic_decay_nonpos`, and
   `stationaryAttentionCoupling_ellipticGenerator_quadratic_decay_nonpos`) establish
   instantaneous algebraic quadratic nonpositivity on the full matrix carrier.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics

open BigOperators Matrix
open InfoGeometry.Routing
open InfoGeometry.Routing.PlanarRotation
open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.Routing.CliffordRoPETorus
open InfoGeometry.QuantumContext.TransformerLatentSpace
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation

variable {ι : Type*}

/-! ### Elementary `Fin 2` & Scalar Helper Lemmas -/

private theorem fin2_cases {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  rcases i with ⟨_ | _ | n, hn⟩
  · exact h0
  · exact h1
  · omega

private theorem matrix_fin2_ext {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) :
    A = B := by
  ext i j
  refine fin2_cases (P := fun i => A i j = B i j) ?_ ?_ i
  · exact fin2_cases (P := fun j => A 0 j = B 0 j) h00 h01 j
  · exact fin2_cases (P := fun j => A 1 j = B 1 j) h10 h11 j

private theorem one_div_one_add_one : (1 : ℝ) / (1 + 1) = 1 / 2 := by
  norm_num

private theorem mul_sub_mul_comm_eq_zero (a b : ℝ) :
    a * b - b * a = 0 := by
  ring

private theorem half_ne_exp_div_exp_add_one (β : ℝ) (hβ : β ≠ 0) :
    (1 : ℝ) / 2 ≠ Real.exp β / (Real.exp β + 1) := by
  intro h
  have hpos : 0 < Real.exp β + 1 := by
    linarith [Real.exp_pos β]
  have hne : Real.exp β + 1 ≠ 0 := ne_of_gt hpos
  have hmul : (1 : ℝ) / 2 * (Real.exp β + 1) = Real.exp β := by
    rw [h, div_mul_cancel₀ _ hne]
  have hexp : Real.exp β = 1 := by
    linarith
  rw [Real.exp_eq_one_iff] at hexp
  exact hβ hexp

private theorem add_neg_mul_eq_sub (a b c d : ℝ) :
    a * b + -c * d = a * b - c * d := by
  ring

private theorem normSq2_scale_scalar (c x y : ℝ) :
    (c * x) * (c * x) + (c * y) * (c * y) = c ^ 2 * (x * x + y * y) := by
  ring

private theorem div_mul_scale_cancel (γ c s x : ℝ) (hc : c ≠ 0) :
    (γ / (c * s)) * (c * x) = (γ / s) * x := by
  rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
  calc
    γ * (c⁻¹ * s⁻¹) * (c * x) = (c * c⁻¹) * (γ * s⁻¹ * x) := by ring
    _ = 1 * (γ * s⁻¹ * x) := by rw [mul_inv_cancel₀ hc]
    _ = (γ * s⁻¹) * x := by ring

private theorem mul_three_lt_of_neg_pos_lt (b θ t₁ t₂ : ℝ)
    (hb : b < 0) (hθ : 0 < θ) (ht : t₁ < t₂) :
    b * θ * t₂ < b * θ * t₁ := by
  have hbθ : b * θ < 0 := mul_neg_of_neg_of_pos hb hθ
  exact mul_lt_mul_of_neg_left ht hbθ

private theorem spiral_arg_add (b θ t s : ℝ) :
    b * θ * (t + s) = b * θ * t + b * θ * s := by
  ring

private theorem one_mul_mul_one_mul (x y : ℝ) :
    1 * (x * y) = (1 * x) * (1 * y) := by
  ring

private theorem mul_add_eq_add_two_pi (θ m p : ℝ) (h_res : p * θ = 2 * Real.pi) :
    θ * (m + p) = θ * m + 2 * Real.pi := by
  calc
    θ * (m + p) = θ * m + p * θ := by ring
    _ = θ * m + 2 * Real.pi := by rw [h_res]

private theorem add_mul_sub_eq_sq_sub_sq (t x : ℝ) :
    (t + x) * (t - x) = t ^ 2 - x ^ 2 := by
  ring

private theorem nullPlus_split_scalar (b t x : ℝ) :
    (Real.cosh b * t + Real.sinh b * x) + (Real.sinh b * t + Real.cosh b * x) =
      (Real.cosh b + Real.sinh b) * (t + x) := by
  ring

private theorem nullMinus_split_scalar (b t x : ℝ) :
    (Real.cosh b * t + Real.sinh b * x) - (Real.sinh b * t + Real.cosh b * x) =
      (Real.cosh b - Real.sinh b) * (t - x) := by
  ring

private theorem mul_exp_mul_exp_neg_scalar (b u v : ℝ) :
    (Real.exp b * u) * (Real.exp (-b) * v) = u * v := by
  calc
    (Real.exp b * u) * (Real.exp (-b) * v)
      = (Real.exp b * Real.exp (-b)) * (u * v) := by ring
    _ = Real.exp (b + -b) * (u * v) := by rw [← Real.exp_add]
    _ = 1 * (u * v) := by rw [add_neg_cancel, Real.exp_zero]
    _ = u * v := one_mul _

private theorem poincare_scale_scalar (c σ dσ dθ : ℝ) (hc : c ≠ 0) :
    ((c * dσ) ^ 2 + (c * dθ) ^ 2) / ((c * σ) ^ 2) =
      (dσ ^ 2 + dθ ^ 2) / (σ ^ 2) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hnum : (c * dσ) ^ 2 + (c * dθ) ^ 2 = c ^ 2 * (dσ ^ 2 + dθ ^ 2) := by ring
  have hden : (c * σ) ^ 2 = c ^ 2 * σ ^ 2 := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hc2]

private theorem poincare_scaled_velocity_algebra (σ b ω : ℝ) (hσ : σ ≠ 0) :
    ((b * σ) ^ 2 + (ω * σ) ^ 2) / (σ ^ 2) = b ^ 2 + ω ^ 2 := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hnum : (b * σ) ^ 2 + (ω * σ) ^ 2 = (b ^ 2 + ω ^ 2) * σ ^ 2 := by ring
  rw [hnum, mul_div_cancel_right₀ _ hσ2]

/-! ### Archetype I: Finite Softmax Attention Coupling, Directed Asymmetry, and Anchor-Column Positivity -/

/-- Pairwise $N$-body softmax attention coupling matrix on a finite token context `ι`:
`A_{i,j} = softmaxWeight (scores i) β j`. -/
noncomputable def attentionCouplingMatrix [Fintype ι]
    (scores : ι → ι → ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  fun i j => softmaxWeight (scores i) β j

/-- Every entry of the attention coupling matrix is strictly positive. -/
theorem attentionCouplingMatrix_pos [Fintype ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (β : ℝ) (i j : ι) :
    0 < attentionCouplingMatrix scores β i j :=
  softmaxWeight_pos (scores i) β j

/-- Every row of the attention coupling matrix sums to `1`. -/
theorem attentionCouplingMatrix_row_sum_one [Fintype ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (β : ℝ) (i : ι) :
    ∑ j, attentionCouplingMatrix scores β i j = 1 :=
  softmaxWeight_sum_one (scores i) β

/-- The attention coupling matrix `attentionCouplingMatrix scores β` belongs to Mathlib's
row-stochastic matrix monoid `Matrix.rowStochastic ℝ ι`. -/
theorem attentionCouplingMatrix_mem_rowStochastic [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (β : ℝ) :
    attentionCouplingMatrix scores β ∈ Matrix.rowStochastic ℝ ι := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    exact le_of_lt (attentionCouplingMatrix_pos scores β i j)
  · intro i
    exact attentionCouplingMatrix_row_sum_one scores β i

/-- Stationary rank-1 softmax attention coupling matrix where every query row shares the
context logit vector `logits : ι → ℝ`. -/
noncomputable def stationaryAttentionCoupling [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  attentionCouplingMatrix (fun _ => logits) β

/-- The stationary attention coupling matrix belongs to `Matrix.rowStochastic ℝ ι`. -/
theorem stationaryAttentionCoupling_mem_rowStochastic [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    stationaryAttentionCoupling logits β ∈ Matrix.rowStochastic ℝ ι :=
  attentionCouplingMatrix_mem_rowStochastic (fun _ => logits) β

/-- The stationary attention coupling matrix satisfies exact detailed balance with respect
to `softmaxWeight logits β`. -/
theorem stationaryAttentionCoupling_detailedBalance [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) :
    InfoGeometry.Probability.DetailedBalance
      (softmaxWeight logits β) (stationaryAttentionCoupling logits β) := by
  ext i j
  rw [InfoGeometry.Probability.detailedBalanceResidual_apply]
  dsimp [InfoGeometry.Probability.stationaryEdgeCurrent, stationaryAttentionCoupling,
    attentionCouplingMatrix, Matrix.zero_apply]
  exact mul_sub_mul_comm_eq_zero (softmaxWeight logits β i) (softmaxWeight logits β j)

/-- On the two-token carrier `Fin 2`, `TransformerLatentSpace.softmaxAttention scores`
coincides identically with `attentionCouplingMatrix scores 1`. -/
theorem softmaxAttention_eq_attentionCouplingMatrix_one
    (scores : PlanarRotation.Mat2) :
    TransformerLatentSpace.softmaxAttention scores =
      attentionCouplingMatrix scores 1 := by
  ext i j
  dsimp [TransformerLatentSpace.softmaxAttention,
    InfoGeometry.Routing.FiniteSoftmax.weight,
    InfoGeometry.Routing.FiniteSoftmax.partitionZ,
    attentionCouplingMatrix, softmaxWeight]
  simp only [div_one, one_mul]

/-- Pruned state anchor-column positivity for `attentionCouplingMatrix`: if `anchor` has
positive weight in `pw : PrunedWeights ι`, the quadratic energy of `attentionCouplingMatrix`
under `prunedState pw` is strictly positive. -/
theorem prunedState_attentionCouplingMatrix_pos [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (pw : PrunedWeights ι) (anchor : ι) (h_anchor : 0 < pw.weights anchor)
    (scores : ι → ι → ℝ) (β : ℝ) :
    0 < prunedState pw
      ((attentionCouplingMatrix scores β).transpose * attentionCouplingMatrix scores β) :=
  sink_anchor_column_positive pw anchor h_anchor (attentionCouplingMatrix scores β) anchor
    (ne_of_gt (attentionCouplingMatrix_pos scores β anchor anchor))

/-- Two-token score matrix where token `0` has uniform scores `(0, 0)` and token `1`
has sink-biased score `1` toward token `0` and `0` toward token `1`. -/
def asymmetricScores : PlanarRotation.Mat2 :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- For `asymmetricScores`, token `0` attends uniformly to token `1` with weight `1 / 2`. -/
theorem attentionCouplingMatrix_asymmetricScores_zero_one (β : ℝ) :
    attentionCouplingMatrix asymmetricScores β 0 1 = 1 / 2 := by
  dsimp [attentionCouplingMatrix, softmaxWeight]
  rw [Fin.sum_univ_two]
  have h00 : asymmetricScores 0 0 = 0 := rfl
  have h01 : asymmetricScores 0 1 = 0 := rfl
  rw [h00, h01, mul_zero, Real.exp_zero]
  exact one_div_one_add_one

/-- For `asymmetricScores`, token `1` attends to sink token `0` with Boltzmann weight
`exp β / (exp β + 1)`. -/
theorem attentionCouplingMatrix_asymmetricScores_one_zero (β : ℝ) :
    attentionCouplingMatrix asymmetricScores β 1 0 =
      Real.exp β / (Real.exp β + 1) := by
  dsimp [attentionCouplingMatrix, softmaxWeight]
  rw [Fin.sum_univ_two]
  have h10 : asymmetricScores 1 0 = 1 := rfl
  have h11 : asymmetricScores 1 1 = 0 := rfl
  rw [h10, h11, mul_one, mul_zero, Real.exp_zero]

/-- **Directed Non-Conservative Asymmetry (`A_{0,1} ≠ A_{1,0}`)**:
For any non-zero inverse temperature `β ≠ 0`, the attention coupling matrix of
`asymmetricScores` is strictly asymmetric across `(0, 1)` and `(1, 0)`. -/
theorem attentionCouplingMatrix_asymmetricScores_ne_of_ne_zero
    (β : ℝ) (hβ : β ≠ 0) :
    attentionCouplingMatrix asymmetricScores β 0 1 ≠
      attentionCouplingMatrix asymmetricScores β 1 0 := by
  rw [attentionCouplingMatrix_asymmetricScores_zero_one,
    attentionCouplingMatrix_asymmetricScores_one_zero]
  exact half_ne_exp_div_exp_add_one β hβ

/-- The `TransformerLatentSpace.softmaxAttention` operator on `asymmetricScores` is
strictly asymmetric (`A_{0,1} ≠ A_{1,0}`). -/
theorem softmaxAttention_asymmetricScores_ne :
    TransformerLatentSpace.softmaxAttention asymmetricScores 0 1 ≠
      TransformerLatentSpace.softmaxAttention asymmetricScores 1 0 := by
  rw [softmaxAttention_eq_attentionCouplingMatrix_one]
  exact attentionCouplingMatrix_asymmetricScores_ne_of_ne_zero 1 one_ne_zero

/-- Existence of a 2-token score matrix whose `softmaxAttention` coupling is asymmetric. -/
theorem exists_softmaxAttention_asymmetric :
    ∃ scores : PlanarRotation.Mat2,
      TransformerLatentSpace.softmaxAttention scores 0 1 ≠
        TransformerLatentSpace.softmaxAttention scores 1 0 :=
  ⟨asymmetricScores, softmaxAttention_asymmetricScores_ne⟩

/-! ### Archetype II: RoPE $\mathrm{SO}(2)$ Phase Clock, Clifford Bivector Torus & Relative Position Invariance -/

/-- 2D matrix-vector action of the planar RoPE rotation `PlanarRotation.rotation φ` on `Fin 2 → ℝ`. -/
noncomputable def ropeAct (φ : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  PlanarRotation.rotation φ *ᵥ v

/-- The planar elliptic generator `PlanarRotation.ellipticGenerator = !![0, -1; 1, 0]`
is skew-symmetric. -/
theorem ellipticGenerator_transpose :
    (PlanarRotation.ellipticGenerator)ᵀ = -PlanarRotation.ellipticGenerator := by
  refine matrix_fin2_ext ?_ ?_ ?_ ?_ <;>
    simp [PlanarRotation.ellipticGenerator, Matrix.transpose_apply]

/-- Exact bridge between `MarkovDrazin.ReversibleRotation.coordinateSkewMatrix` on `Fin 2`
and `PlanarRotation.ellipticGenerator`: `coordinateSkewMatrix 0 1 = -ellipticGenerator`. -/
theorem coordinateSkewMatrix_zero_one_eq_neg_ellipticGenerator :
    MarkovDrazin.ReversibleRotation.coordinateSkewMatrix (0 : Fin 2) 1 =
      -PlanarRotation.ellipticGenerator := by
  refine matrix_fin2_ext ?_ ?_ ?_ ?_ <;>
    simp [MarkovDrazin.ReversibleRotation.coordinateSkewMatrix,
      PlanarRotation.ellipticGenerator]

/-- Converse sign bridge: `coordinateSkewMatrix 1 0 = ellipticGenerator`. -/
theorem coordinateSkewMatrix_one_zero_eq_ellipticGenerator :
    MarkovDrazin.ReversibleRotation.coordinateSkewMatrix (1 : Fin 2) 0 =
      PlanarRotation.ellipticGenerator := by
  refine matrix_fin2_ext ?_ ?_ ?_ ?_ <;>
    simp [MarkovDrazin.ReversibleRotation.coordinateSkewMatrix,
      PlanarRotation.ellipticGenerator]

/-- Canonical 1-plane `CliffordRoPETorus.EllipticBivectorTorus` instance on `Mat2`
generated by `PlanarRotation.ellipticGenerator`. -/
noncomputable def planarEllipticBivectorTorus :
    CliffordRoPETorus.EllipticBivectorTorus 1 PlanarRotation.Mat2 where
  B := fun _ => PlanarRotation.ellipticGenerator
  sq_neg_one := fun _ => PlanarRotation.ellipticGenerator_sq
  commute := fun _ _ => rfl
  transpose_involution := Matrix.transpose
  transpose_add := fun X Y => Matrix.transpose_add X Y
  transpose_mul := fun X Y => Matrix.transpose_mul X Y
  transpose_smul := fun r X => Matrix.transpose_smul r X
  transpose_one := Matrix.transpose_one
  transpose_B := fun _ => ellipticGenerator_transpose

/-- The Clifford torus planar rotation `planarEllipticBivectorTorus.R_plane 0 φ`
coincides with `PlanarRotation.rotation φ`. -/
theorem planarEllipticBivectorTorus_R_plane_eq_rotation (φ : ℝ) :
    planarEllipticBivectorTorus.R_plane 0 φ = PlanarRotation.rotation φ :=
  (PlanarRotation.rotation_as_elliptic_generator φ).symm

/-- Right orthogonality identity: `rotation φ * (rotation φ)ᵀ = 1`. -/
theorem rotation_mul_transpose_self (φ : ℝ) :
    PlanarRotation.rotation φ * (PlanarRotation.rotation φ)ᵀ = 1 := by
  rw [PlanarRotation.rotation_transpose, PlanarRotation.rotation_mul_neg_rotation]

/-- Euclidean dot product on `Fin 2 → ℝ` (`dotProduct u v`). -/
def vecDot2 (u v : Fin 2 → ℝ) : ℝ :=
  dotProduct u v

/-- Squared Euclidean norm on `Fin 2 → ℝ` (`dotProduct v v`). -/
def vecNormSq2 (v : Fin 2 → ℝ) : ℝ :=
  dotProduct v v

/-- Expansion of `vecDot2 u v` into its two coordinate products `u 0 * v 0 + u 1 * v 1`. -/
theorem vecDot2_eq_add (u v : Fin 2 → ℝ) :
    vecDot2 u v = u 0 * v 0 + u 1 * v 1 := by
  dsimp [vecDot2, dotProduct]
  exact Fin.sum_univ_two _

/-- Expansion of `vecNormSq2 v` into `v 0 * v 0 + v 1 * v 1`. -/
theorem vecNormSq2_eq_add (v : Fin 2 → ℝ) :
    vecNormSq2 v = v 0 * v 0 + v 1 * v 1 := by
  dsimp [vecNormSq2, dotProduct]
  exact Fin.sum_univ_two _

/-- First coordinate of the RoPE vector action `ropeAct φ v`. -/
theorem ropeAct_apply_zero (φ : ℝ) (v : Fin 2 → ℝ) :
    ropeAct φ v 0 = Real.cos φ * v 0 - Real.sin φ * v 1 := by
  have h00 : PlanarRotation.rotation φ 0 0 = Real.cos φ := rfl
  have h01 : PlanarRotation.rotation φ 0 1 = -Real.sin φ := rfl
  dsimp [ropeAct, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, h00, h01]
  exact add_neg_mul_eq_sub (Real.cos φ) (v 0) (Real.sin φ) (v 1)

/-- Second coordinate of the RoPE vector action `ropeAct φ v`. -/
theorem ropeAct_apply_one (φ : ℝ) (v : Fin 2 → ℝ) :
    ropeAct φ v 1 = Real.sin φ * v 0 + Real.cos φ * v 1 := by
  have h10 : PlanarRotation.rotation φ 1 0 = Real.sin φ := rfl
  have h11 : PlanarRotation.rotation φ 1 1 = Real.cos φ := rfl
  dsimp [ropeAct, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, h10, h11]

/-- Identity action at zero angle: `ropeAct 0 v = v`. -/
theorem ropeAct_zero (v : Fin 2 → ℝ) :
    ropeAct 0 v = v := by
  dsimp [ropeAct]
  rw [PlanarRotation.rotation_zero, Matrix.one_mulVec]

/-- Additive composition of the RoPE vector action:
`ropeAct (φ₁ + φ₂) v = ropeAct φ₁ (ropeAct φ₂ v)`. -/
theorem ropeAct_add (φ₁ φ₂ : ℝ) (v : Fin 2 → ℝ) :
    ropeAct (φ₁ + φ₂) v = ropeAct φ₁ (ropeAct φ₂ v) := by
  dsimp [ropeAct]
  rw [← PlanarRotation.rotation_mul_rotation, Matrix.mulVec_mulVec]

/-- `PlanarRotation.rotation φ` preserves the Euclidean dot product on `Fin 2 → ℝ`. -/
theorem rotation_dotProduct_preserved (φ : ℝ) (u v : Fin 2 → ℝ) :
    dotProduct (PlanarRotation.rotation φ *ᵥ u) (PlanarRotation.rotation φ *ᵥ v) =
      dotProduct u v := by
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    PlanarRotation.rotation_transpose_mul_self, Matrix.one_mulVec]
  exact dotProduct_comm v u

/-- `ropeAct φ` preserves `vecDot2`. -/
theorem ropeAct_dotProduct_preserved (φ : ℝ) (u v : Fin 2 → ℝ) :
    vecDot2 (ropeAct φ u) (ropeAct φ v) = vecDot2 u v :=
  rotation_dotProduct_preserved φ u v

/-- `ropeAct φ` preserves the squared Euclidean norm `vecNormSq2`. -/
theorem ropeAct_normSq_preserved (φ : ℝ) (v : Fin 2 → ℝ) :
    vecNormSq2 (ropeAct φ v) = vecNormSq2 v :=
  rotation_dotProduct_preserved φ v v

/-- Transpose of the discrete RoPE rotor negates the sequence position index. -/
theorem ropeRotor_transpose (θ : ℝ) (m : ℤ) :
    (DiscreteRoPERepresentation.ropeRotor θ m)ᵀ =
      DiscreteRoPERepresentation.ropeRotor θ (-m) := by
  dsimp [DiscreteRoPERepresentation.ropeRotor]
  rw [PlanarRotation.rotation_transpose, Int.cast_neg, neg_mul]

/-- **RoPE Relative Position Dot-Product Invariance**:
The Euclidean inner product of a query `q` rotated at sequence position `m` and a key `k`
rotated at sequence position `n` depends only on the relative displacement `n - m`. -/
theorem rope_dotProduct_relative_invariance (θ : ℝ) (m n : ℤ) (q k : Fin 2 → ℝ) :
    dotProduct (DiscreteRoPERepresentation.ropeRotor θ m *ᵥ q)
      (DiscreteRoPERepresentation.ropeRotor θ n *ᵥ k) =
      dotProduct q (DiscreteRoPERepresentation.ropeRotor θ (n - m) *ᵥ k) := by
  rw [← Matrix.vecMul_transpose (DiscreteRoPERepresentation.ropeRotor θ m) q,
    ropeRotor_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    DiscreteRoPERepresentation.ropeRotor_relative, ← Matrix.dotProduct_mulVec]

/-! ### Archetype III: Radial Normalization onto $S^1(\gamma)$ & RoPE Equivariance -/

/-- Squared Euclidean norm on `Fin 2 → ℝ` is always non-negative. -/
theorem vecNormSq2_nonneg (v : Fin 2 → ℝ) : 0 ≤ vecNormSq2 v := by
  rw [vecNormSq2_eq_add]
  exact add_nonneg (mul_self_nonneg (v 0)) (mul_self_nonneg (v 1))

/-- Homogeneous quadratic scaling of `vecNormSq2` under scalar multiplication `c • v`. -/
theorem vecNormSq2_smul (c : ℝ) (v : Fin 2 → ℝ) :
    vecNormSq2 (c • v) = c ^ 2 * vecNormSq2 v := by
  rw [vecNormSq2_eq_add, vecNormSq2_eq_add]
  exact normSq2_scale_scalar c (v 0) (v 1)

/-- 2D radial normalization onto the circle $S^1(\gamma)$:
`sphericalNorm2 γ v = (γ / √‖v‖²) • v`. This definition omits the centering,
coordinatewise gain, and epsilon used by Transformer LayerNorm/RMSNorm. -/
noncomputable def sphericalNorm2 (γ : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (γ / Real.sqrt (vecNormSq2 v)) • v

/-- At unit gain `γ = 1`, `sphericalNorm2 1 v` is `(Real.sqrt (dotProduct v v))⁻¹ • v`. -/
theorem sphericalNorm2_one_eq_inv_sqrt_smul (v : Fin 2 → ℝ) :
    sphericalNorm2 1 v = (Real.sqrt (dotProduct v v))⁻¹ • v := by
  dsimp [sphericalNorm2, vecNormSq2]
  rw [one_div]

/-- **Exact Hyperspherical Constraint**:
For any vector `v` with strictly positive squared norm `0 < vecNormSq2 v`, projecting via
`sphericalNorm2 γ` places the output on the circle of squared radius `γ ^ 2`. -/
theorem sphericalNorm2_normSq_eq (γ : ℝ) (v : Fin 2 → ℝ) (hv : 0 < vecNormSq2 v) :
    vecNormSq2 (sphericalNorm2 γ v) = γ ^ 2 := by
  dsimp [sphericalNorm2]
  rw [vecNormSq2_smul, div_pow, Real.sq_sqrt (le_of_lt hv),
    div_mul_cancel₀ _ (ne_of_gt hv)]

/-- **Positive Radial Scale Invariance (`c • v`)**:
Scaling `v` by any strictly positive scalar `0 < c` leaves `sphericalNorm2 γ` invariant. -/
theorem sphericalNorm2_smul_pos (γ c : ℝ) (hc : 0 < c) (v : Fin 2 → ℝ) :
    sphericalNorm2 γ (c • v) = sphericalNorm2 γ v := by
  funext a
  dsimp [sphericalNorm2]
  rw [vecNormSq2_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq (le_of_lt hc)]
  exact div_mul_scale_cancel γ c (Real.sqrt (vecNormSq2 v)) (v a) (ne_of_gt hc)

/-- **Exact Commutation of RoPE and Radial Normalization**:
Rotating by `ropeAct φ` and projecting onto the hypersphere via `sphericalNorm2 γ`
commute identically. -/
theorem ropeAct_sphericalNorm2_comm (γ φ : ℝ) (v : Fin 2 → ℝ) :
    sphericalNorm2 γ (ropeAct φ v) = ropeAct φ (sphericalNorm2 γ v) := by
  dsimp only [sphericalNorm2]
  rw [ropeAct_normSq_preserved]
  dsimp [ropeAct]
  rw [Matrix.mulVec_smul]

/-! ### Archetype IV: Logarithmic Spiral Trajectories & Collapse to Circular Limit Cycles -/

/-- Logarithmic spiral radius `r(t) = a * exp(b * θ * t)`. -/
noncomputable def spiralRadius (a b θ t : ℝ) : ℝ :=
  a * Real.exp (b * θ * t)

/-- Logarithmic spiral trajectory in $\mathbb{R}^2$:
`z(t) = spiralRadius a b θ t • ropeAct (θ * t) v₀`. -/
noncomputable def spiralTrajectory (a b θ t : ℝ) (v₀ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  spiralRadius a b θ t • ropeAct (θ * t) v₀

/-- For `0 < a`, the spiral radius `spiralRadius a b θ t` is strictly positive at all times `t`. -/
theorem spiralRadius_pos (a b θ t : ℝ) (ha : 0 < a) :
    0 < spiralRadius a b θ t :=
  mul_pos ha (Real.exp_pos _)

/-- **Dissipative Radial Contraction**:
When `0 < a`, `b < 0`, and `0 < θ`, the spiral radius strictly decreases as `t` increases. -/
theorem spiralRadius_strict_decreasing (a b θ t₁ t₂ : ℝ)
    (ha : 0 < a) (hb : b < 0) (hθ : 0 < θ) (ht : t₁ < t₂) :
    spiralRadius a b θ t₂ < spiralRadius a b θ t₁ := by
  dsimp [spiralRadius]
  exact mul_lt_mul_of_pos_left
    (Real.exp_lt_exp.mpr (mul_three_lt_of_neg_pos_lt b θ t₁ t₂ hb hθ ht)) ha

/-- **Exact Radial Norm Envelope**:
The squared Euclidean norm of `spiralTrajectory a b θ t v₀` is `(spiralRadius a b θ t)² ‖v₀‖²`. -/
theorem spiralTrajectory_normSq_eq (a b θ t : ℝ) (v₀ : Fin 2 → ℝ) :
    vecNormSq2 (spiralTrajectory a b θ t v₀) =
      (spiralRadius a b θ t) ^ 2 * vecNormSq2 v₀ := by
  dsimp [spiralTrajectory]
  rw [vecNormSq2_smul, ropeAct_normSq_preserved]

/-- At unit initial scale `a = 1`, the spiral radius satisfies the multiplicative group law. -/
theorem spiralRadius_one_add (b θ t s : ℝ) :
    spiralRadius 1 b θ (t + s) = spiralRadius 1 b θ t * spiralRadius 1 b θ s := by
  dsimp [spiralRadius]
  rw [spiral_arg_add b θ t s, Real.exp_add]
  exact one_mul_mul_one_mul (Real.exp (b * θ * t)) (Real.exp (b * θ * s))

/-- **Additive Dynamical Flow Group Law**:
At unit initial scale `a = 1`, `spiralTrajectory` forms a 1-parameter dynamical semigroup:
`spiralTrajectory 1 b θ (t + s) v₀ = spiralTrajectory 1 b θ t (spiralTrajectory 1 b θ s v₀)`. -/
theorem spiralTrajectory_flow_add (b θ t s : ℝ) (v₀ : Fin 2 → ℝ) :
    spiralTrajectory 1 b θ (t + s) v₀ =
      spiralTrajectory 1 b θ t (spiralTrajectory 1 b θ s v₀) := by
  dsimp [spiralTrajectory, ropeAct]
  rw [spiralRadius_one_add, mul_add, ← PlanarRotation.rotation_mul_rotation,
    Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, smul_smul]

/-- **Collapse of Dissipative Spiral to Circular Limit Cycle**:
For any `0 < a`, applying `sphericalNorm2 γ` to `spiralTrajectory a b θ t v₀` cancels the
exponential radial factor `a * exp(b * θ * t) > 0` identically and yields the pure circular
RoPE orbit on the sphere of radius `γ`. -/
theorem sphericalNorm2_spiralTrajectory_eq_limitCycle
    (a b θ t γ : ℝ) (ha : 0 < a) (v₀ : Fin 2 → ℝ) :
    sphericalNorm2 γ (spiralTrajectory a b θ t v₀) =
      ropeAct (θ * t) (sphericalNorm2 γ v₀) := by
  dsimp [spiralTrajectory]
  rw [sphericalNorm2_smul_pos γ (spiralRadius a b θ t) (spiralRadius_pos a b θ t ha)]
  exact ropeAct_sphericalNorm2_comm γ (θ * t) v₀

/-- At unit gain `γ = 1`, `sphericalNorm2 1 (spiralTrajectory a b θ t v₀)` collapses to
`(Real.sqrt (dotProduct v₀ v₀))⁻¹ • (PlanarRotation.rotation (θ * t) *ᵥ v₀)`. -/
theorem sphericalNorm2_one_spiralTrajectory_eq_limitCycle
    (a b θ t : ℝ) (ha : 0 < a) (v₀ : Fin 2 → ℝ) :
    sphericalNorm2 1 (spiralTrajectory a b θ t v₀) =
      (Real.sqrt (dotProduct v₀ v₀))⁻¹ • (PlanarRotation.rotation (θ * t) *ᵥ v₀) := by
  rw [sphericalNorm2_spiralTrajectory_eq_limitCycle a b θ t 1 ha v₀,
    sphericalNorm2_one_eq_inv_sqrt_smul]
  dsimp [ropeAct]
  rw [Matrix.mulVec_smul]

/-! ### Archetype V: Orbital Resonance, Periodic Limit Cycles & Metriplectic Quadratic Decay Bridge -/

/-- A full $2\pi$ turn is the identity matrix: `PlanarRotation.rotation (2 * Real.pi) = 1`. -/
theorem rotation_two_pi_eq_one : PlanarRotation.rotation (2 * Real.pi) = 1 := by
  rw [PlanarRotation.rotation_as_elliptic_generator, Real.cos_two_pi, Real.sin_two_pi,
    one_smul, zero_smul, add_zero]

/-- $2\pi$-periodicity of the planar RoPE rotation matrix:
`PlanarRotation.rotation (φ + 2 * Real.pi) = PlanarRotation.rotation φ`. -/
theorem rotation_periodic (φ : ℝ) :
    PlanarRotation.rotation (φ + 2 * Real.pi) = PlanarRotation.rotation φ := by
  rw [← PlanarRotation.rotation_mul_rotation, rotation_two_pi_eq_one, mul_one]

/-- $2\pi$-periodicity of the RoPE vector action:
`ropeAct (φ + 2 * Real.pi) v = ropeAct φ v`. -/
theorem ropeAct_periodic (φ : ℝ) (v : Fin 2 → ℝ) :
    ropeAct (φ + 2 * Real.pi) v = ropeAct φ v := by
  dsimp [ropeAct]
  rw [rotation_periodic]

/-- **Resonant $p$-Step Periodicity of the Defined Orbit**:
When the angular frequency `θ` and period `p` satisfy the orbital resonance condition
`p * θ = 2 * Real.pi`, advancing the radially normalized spiral trajectory by `p` steps
returns the representation to its exact state at step `m`. -/
theorem sphericalNorm2_spiralTrajectory_resonant_periodic
    (a b θ γ : ℝ) (ha : 0 < a) (m p : ℝ) (h_res : p * θ = 2 * Real.pi)
    (v₀ : Fin 2 → ℝ) :
    sphericalNorm2 γ (spiralTrajectory a b θ (m + p) v₀) =
      sphericalNorm2 γ (spiralTrajectory a b θ m v₀) := by
  rw [sphericalNorm2_spiralTrajectory_eq_limitCycle a b θ (m + p) γ ha v₀,
    sphericalNorm2_spiralTrajectory_eq_limitCycle a b θ m γ ha v₀,
    mul_add_eq_add_two_pi θ m p h_res,
    ropeAct_periodic]

/-- **Metriplectic Reversible-Plus-Dissipative Quadratic Identity for the RoPE Elliptic Generator**:
In the softmax-weighted Frobenius pairing `weightedMatrixPairing (softmaxWeight logits β)`,
the weighted-skew reversible action built from `PlanarRotation.ellipticGenerator` contributes
zero to the diagonal quadratic pairing, leaving purely the Markov Onsager dissipative term. -/
theorem ellipticGenerator_markovOnsager_quadratic_decay_eq
    (logits : Fin 2 → ℝ) (β : ℝ) (P : PlanarRotation.Mat2)
    (γ : ℝ) (X : PlanarRotation.Mat2) :
    MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) X
        (mulLeftLinearMap (Fin 2) ℝ
          (MarkovDrazin.ReversibleRotation.weightedSkewActionMatrix
            (softmaxWeight logits β) PlanarRotation.ellipticGenerator) X -
          γ • MarkovDrazin.markovLeftOnsager P X) =
      -γ * MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) X
        (MarkovDrazin.markovLeftOnsager P X) := by
  refine MarkovDrazin.weightedMatrixPairing_quadratic_decay_eq
    (softmaxWeight logits β) P
    (mulLeftLinearMap (Fin 2) ℝ
      (MarkovDrazin.ReversibleRotation.weightedSkewActionMatrix
        (softmaxWeight logits β) PlanarRotation.ellipticGenerator))
    (fun U V => ?_) γ X
  exact MarkovDrazin.ReversibleRotation.weightedMatrixPairing_weightedSkewActionMatrix_skew
    (softmaxWeight logits β) PlanarRotation.ellipticGenerator
    (softmaxWeight_pos logits β) ellipticGenerator_transpose U V

/-- **Metriplectic Instantaneous Quadratic Decay for RoPE Elliptic Rotation + Softmax Markov Dissipation**:
Under row-stochasticity and softmax detailed balance (`DetailedBalance (softmaxWeight logits β) P`)
with nonnegative damping rate `0 ≤ γ`, combining the weighted-skew RoPE `ellipticGenerator`
rotation with the Markov attention Onsager dissipation `markovLeftOnsager P` yields a
nonpositive instantaneous quadratic rate of change. -/
theorem ellipticGenerator_markovOnsager_quadratic_decay_nonpos
    (logits : Fin 2 → ℝ) (β : ℝ) (P : PlanarRotation.Mat2)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin 2))
    (hDB : InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β) P)
    (γ : ℝ) (hγ : 0 ≤ γ) (X : PlanarRotation.Mat2) :
    MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) X
        (mulLeftLinearMap (Fin 2) ℝ
          (MarkovDrazin.ReversibleRotation.weightedSkewActionMatrix
            (softmaxWeight logits β) PlanarRotation.ellipticGenerator) X -
          γ • MarkovDrazin.markovLeftOnsager P X) ≤ 0 :=
  MarkovDrazin.weightedSkewAction_quadratic_decay_nonpos P (softmaxWeight logits β)
    hP hDB (softmaxWeight_pos logits β)
    PlanarRotation.ellipticGenerator ellipticGenerator_transpose γ hγ X

/-- **Unconditional Metriplectic Instantaneous Quadratic Decay on `stationaryAttentionCoupling`**:
Instantiating `ellipticGenerator_markovOnsager_quadratic_decay_nonpos` with the concrete
row-stochastic, detailed-balance stationary softmax attention coupling
`stationaryAttentionCoupling logits β` yields unconditional nonpositive instantaneous
quadratic change for any `0 ≤ γ`. -/
theorem stationaryAttentionCoupling_ellipticGenerator_quadratic_decay_nonpos
    (logits : Fin 2 → ℝ) (β : ℝ) (γ : ℝ) (hγ : 0 ≤ γ) (X : PlanarRotation.Mat2) :
    MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) X
        (mulLeftLinearMap (Fin 2) ℝ
          (MarkovDrazin.ReversibleRotation.weightedSkewActionMatrix
            (softmaxWeight logits β) PlanarRotation.ellipticGenerator) X -
          γ • MarkovDrazin.markovLeftOnsager (stationaryAttentionCoupling logits β) X) ≤ 0 :=
  ellipticGenerator_markovOnsager_quadratic_decay_nonpos logits β
    (stationaryAttentionCoupling logits β)
    (stationaryAttentionCoupling_mem_rowStochastic logits β)
    (stationaryAttentionCoupling_detailedBalance logits β)
    γ hγ X

/-! ### Archetype VI: Independent Split-Boost and Quadratic-Form Identities -/

/-- Forward null lightcone coordinate $u = t + x$ on `Fin 2 → ℝ`. -/
def nullPlusCoord (x : Fin 2 → ℝ) : ℝ :=
  x 0 + x 1

/-- Backward null lightcone coordinate $v = t - x$ on `Fin 2 → ℝ`. -/
def nullMinusCoord (x : Fin 2 → ℝ) : ℝ :=
  x 0 - x 1

/-- 2D Lorentzian quadratic interval $t^2 - x^2$ on `Fin 2 → ℝ`. -/
def lorentzInterval (x : Fin 2 → ℝ) : ℝ :=
  (x 0) ^ 2 - (x 1) ^ 2

/-- Factorization of the Lorentzian interval into null lightcone coordinates:
`nullPlusCoord x * nullMinusCoord x = lorentzInterval x`. -/
theorem nullCoords_mul_eq_lorentzInterval (x : Fin 2 → ℝ) :
    nullPlusCoord x * nullMinusCoord x = lorentzInterval x :=
  add_mul_sub_eq_sq_sub_sq (x 0) (x 1)

/-- First coordinate of the hyperbolic boost `PlanarRotation.splitRotation b *ᵥ x`. -/
theorem splitRotation_mulVec_apply_zero (b : ℝ) (x : Fin 2 → ℝ) :
    (PlanarRotation.splitRotation b *ᵥ x) 0 =
      Real.cosh b * x 0 + Real.sinh b * x 1 := by
  have h00 : PlanarRotation.splitRotation b 0 0 = Real.cosh b := rfl
  have h01 : PlanarRotation.splitRotation b 0 1 = Real.sinh b := rfl
  dsimp [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, h00, h01]

/-- Second coordinate of the hyperbolic boost `PlanarRotation.splitRotation b *ᵥ x`. -/
theorem splitRotation_mulVec_apply_one (b : ℝ) (x : Fin 2 → ℝ) :
    (PlanarRotation.splitRotation b *ᵥ x) 1 =
      Real.sinh b * x 0 + Real.cosh b * x 1 := by
  have h10 : PlanarRotation.splitRotation b 1 0 = Real.sinh b := rfl
  have h11 : PlanarRotation.splitRotation b 1 1 = Real.cosh b := rfl
  dsimp [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, h10, h11]

/-- **Forward Null Lightcone Eigen-Scaling under `PlanarRotation.splitRotation`**:
The hyperbolic boost `splitRotation b` scales the forward null coordinate `u = t + x`
by `exp b`. -/
theorem nullPlusCoord_splitRotation (b : ℝ) (x : Fin 2 → ℝ) :
    nullPlusCoord (PlanarRotation.splitRotation b *ᵥ x) =
      Real.exp b * nullPlusCoord x := by
  dsimp [nullPlusCoord]
  rw [splitRotation_mulVec_apply_zero, splitRotation_mulVec_apply_one,
    nullPlus_split_scalar, Real.cosh_add_sinh]

/-- **Backward Null Lightcone Eigen-Scaling under `PlanarRotation.splitRotation`**:
The hyperbolic boost `splitRotation b` scales the backward null coordinate `v = t - x`
by `exp (-b)`. -/
theorem nullMinusCoord_splitRotation (b : ℝ) (x : Fin 2 → ℝ) :
    nullMinusCoord (PlanarRotation.splitRotation b *ᵥ x) =
      Real.exp (-b) * nullMinusCoord x := by
  dsimp [nullMinusCoord]
  rw [splitRotation_mulVec_apply_zero, splitRotation_mulVec_apply_one,
    nullMinus_split_scalar, Real.cosh_sub_sinh]

/-- **Lorentz Interval Invariance under `PlanarRotation.splitRotation`**:
Opposing exponential scalings `exp b` and `exp (-b)` on the null lightcone axes cancel,
preserving `lorentzInterval x = (x 0)² - (x 1)²`. -/
theorem lorentzInterval_splitRotation_invariant (b : ℝ) (x : Fin 2 → ℝ) :
    lorentzInterval (PlanarRotation.splitRotation b *ᵥ x) =
      lorentzInterval x := by
  rw [← nullCoords_mul_eq_lorentzInterval, ← nullCoords_mul_eq_lorentzInterval,
    nullPlusCoord_splitRotation, nullMinusCoord_splitRotation]
  exact mul_exp_mul_exp_neg_scalar b (nullPlusCoord x) (nullMinusCoord x)

/-- Upper half-plane quadratic line element
$ds^2 = (d\sigma^2 + d\theta^2) / \sigma^2$. -/
def poincareHalfPlaneMetric (σ dσ dθ : ℝ) : ℝ :=
  (dσ ^ 2 + dθ ^ 2) / (σ ^ 2)

/-- Poincaré disk conformal metric factor $4 / (1 - r^2)^2$. -/
def poincareDiskConformalFactor (r : ℝ) : ℝ :=
  4 / ((1 - r ^ 2) ^ 2)

/-- The displayed quadratic-form expression is non-negative for all inputs. -/
theorem poincareHalfPlaneMetric_nonneg (σ dσ dθ : ℝ) :
    0 ≤ poincareHalfPlaneMetric σ dσ dθ := by
  dsimp [poincareHalfPlaneMetric]
  exact div_nonneg (add_nonneg (sq_nonneg dσ) (sq_nonneg dθ)) (sq_nonneg σ)

/-- **Scale Invariance of the Upper Half-Plane Quadratic Expression**:
Simultaneous rescaling `(σ, dσ, dθ) ↦ (c * σ, c * dσ, c * dθ)` for `c ≠ 0` leaves
`poincareHalfPlaneMetric` invariant. -/
theorem poincareHalfPlaneMetric_scale_invariant (c σ dσ dθ : ℝ) (hc : c ≠ 0) :
    poincareHalfPlaneMetric (c * σ) (c * dσ) (c * dθ) =
      poincareHalfPlaneMetric σ dσ dθ :=
  poincare_scale_scalar c σ dσ dθ hc

/-- Algebraic evaluation of the quadratic line element on the prescribed tangent components
`dσ = b * σ` and `dθ = ω * σ`. This substitution identity does not assert that these
components are the derivative of `spiralTrajectory` or of a Transformer trajectory. -/
theorem poincareHalfPlaneMetric_scaled_velocity_identity (σ b ω : ℝ) (hσ : σ ≠ 0) :
    poincareHalfPlaneMetric σ (b * σ) (ω * σ) = b ^ 2 + ω ^ 2 :=
  poincare_scaled_velocity_algebra σ b ω hσ

/-- Inside the open unit disk `r ^ 2 < 1`, the Poincaré disk conformal factor is strictly positive. -/
theorem poincareDiskConformalFactor_pos (r : ℝ) (hr : r ^ 2 < 1) :
    0 < poincareDiskConformalFactor r := by
  dsimp [poincareDiskConformalFactor]
  have hsub : 0 < 1 - r ^ 2 := sub_pos.mpr hr
  exact div_pos (by norm_num) (pow_pos hsub 2)

/-- At the origin `r = 0` of the Poincaré disk, the conformal metric factor equals `4`. -/
theorem poincareDiskConformalFactor_zero :
    poincareDiskConformalFactor 0 = 4 := by
  dsimp [poincareDiskConformalFactor]
  norm_num

end InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics

end
