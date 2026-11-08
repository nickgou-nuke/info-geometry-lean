/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Routing.PlanarRotation
import InfoGeometry.Routing.DiscreteRoPERepresentation
import InfoGeometry.Synthesis.DoubleKreinCausalSelfAdjoint
import InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis

/-!
# Transactional Query–Key Duality, KV-Cache Asymmetry, Krein Backpropagation Duality, RoPE Proper-Time Cancellation, and Cotangent Phase-Space Synthesis

This module formalizes the geometric and algebraic structure of autoregressive query–key–value
attention across five coupled layers:

1. **Transactional Query–Key Handshake & KV-Cache Asymmetry**:
   - Defines the feature-space bilinear pairing `featureInner`, the transactional handshake
     logit matrix `transactionalLogitMatrix`, and the causal value payload transfer
     `causalValueOutput`.
   - Proves `causalValueOutput_kv_cache_prefix_invariance` (past keys and values up to step `i`
     suffice under lower-triangular causality) and
     `transactionalLogitMatrix_row_depends_only_on_instant_query` (the current logit row at
     step `i` depends only on the instantaneous query `Q i`, explaining why past queries
     never need to be cached).

2. **Krein Duality of Forward Inference and Backward Error Backpropagation**:
   - Defines `forwardKeyContraction` and `backwardKeyGradient`, proving the exact adjoint
     transposition identity `forward_backward_query_key_gradient_duality`, the anti-causal
     upper-triangular dependence of key gradients on future queries
     `backwardKeyGradient_depends_only_on_future_queries`, and Double Krein self-adjointness
     `forward_backward_doubleKrein_selfAdjoint`.

3. **RoPE as Relative Proper-Time Cancellation & Logarithmic Radial Interval**:
   - Certifies $2 \times 2$ matrix non-commutativity on `Mat2` (`rope_mat2_noncommute`),
     proves `ropeRotor_transpose`, `rope_inner_product_relative_time_cancellation`,
     `rope_inner_product_shift_invariant`, and the conformal logarithmic proper-time
     interval law `conformal_log_proper_time_interval`.

4. **Phase-Space Cotangent Symplectic Pairing**:
   - Defines `cotangentSymplecticForm` on query–key phase space `(Fin d → ℝ) × (Fin d → ℝ)`,
     proving skew-symmetry and self-annihilation (`cotangentSymplecticForm_skew`) as well as
     Lagrangian isotropy of the pure-query and pure-key sheets and cross-sheet canonical
     pairing (`cotangentSymplecticForm_lagrangian_sheets`).

5. **Transactional Cotangent Action Surprisal**:
   - Connects the cotangent symplectic pairing to `transactionalLogitMatrix` and the modular
     surprisal of softmax attention weights via `attentionSoftmax_surprisal_eq`.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge

noncomputable section

open scoped BigOperators Matrix
open Finset Matrix
open InfoGeometry.Routing.PlanarRotation
open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.Synthesis.DoubleKreinCausalSelfAdjoint
open InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis

/-!
## Section 1: Transactional Query–Key Handshake & KV-Cache Asymmetry
-/

/-- Feature-space canonical pairing $\langle q, k \rangle = \sum_{a} q_a k_a$ on $\operatorname{Fin} d \to \mathbb{R}$. -/
def featureInner {d : ℕ} (q k : Fin d → ℝ) : ℝ :=
  ∑ a : Fin d, q a * k a

/-- Transactional handshake logit matrix $S_{ij} = \mathrm{scale} \cdot \langle Q_i, K_j \rangle$. -/
def transactionalLogitMatrix {n d : ℕ} (scale : ℝ) (Q K : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => scale * featureInner (Q i) (K j)

/-- Causal value payload transfer $(A V)_{i, a} = \sum_{j} A_{ij} V_{j, a}$. -/
def causalValueOutput {n d_v : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (V : Fin n → Fin d_v → ℝ)
    (i : Fin n) (a : Fin d_v) : ℝ :=
  ∑ j : Fin n, A i j * V j a

/-- KV-Cache Causal Prefix Invariance: if the attention matrix `A` is causal lower-triangular
and two value histories `V₁, V₂` agree on all causal past/present tokens `j ≤ i`, then the
value payload output at step `i` is identical. -/
theorem causalValueOutput_kv_cache_prefix_invariance {n d_v : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (V₁ V₂ : Fin n → Fin d_v → ℝ) (i : Fin n)
    (hA : IsCausalLowerTriangular A)
    (hV : ∀ j : Fin n, j ≤ i → V₁ j = V₂ j) :
    causalValueOutput A V₁ i = causalValueOutput A V₂ i := by
  funext a
  dsimp [causalValueOutput]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [hA i j hij, zero_mul, zero_mul]
  · rw [hV j (not_lt.mp hij)]

/-- Transient Query Locality: if two query sequences `Q₁, Q₂` agree at the current frontier
step `i`, then the entire `i`-th logit row `transactionalLogitMatrix scale Q₁ K i j` agrees for
every key position `j`, independent of any past queries `Q₁ m` for `m ≠ i`. -/
theorem transactionalLogitMatrix_row_depends_only_on_instant_query {n d : ℕ}
    (scale : ℝ) (Q₁ Q₂ K : Fin n → Fin d → ℝ) (i j : Fin n)
    (hQi : Q₁ i = Q₂ i) :
    transactionalLogitMatrix scale Q₁ K i j =
      transactionalLogitMatrix scale Q₂ K i j := by
  dsimp [transactionalLogitMatrix]
  rw [hQi]

/-!
## Section 2: Krein Duality of Forward Inference and Backward Error Backpropagation
-/

/-- Forward contraction of logit sensitivities/weights `G` against keys `K` at query step `i`. -/
def forwardKeyContraction {n d : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (K : Fin n → Fin d → ℝ)
    (i : Fin n) (a : Fin d) : ℝ :=
  ∑ j : Fin n, G i j * K j a

/-- Backward error backpropagation gradient with respect to past key `K j` accumulated across
all queries `Q i`. -/
def backwardKeyGradient {n d : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Fin d → ℝ)
    (j : Fin n) (a : Fin d) : ℝ :=
  ∑ i : Fin n, G i j * Q i a

private theorem forward_backward_scalar_comm (q g k : ℝ) :
    q * (g * k) = (g * q) * k := by
  ring

/-- Forward–Backward Query–Key Adjoint Transposition Identity: pairing queries `Q i` with the
forward key contraction of `G` equals pairing the backward key gradient of `G` with keys `K j`. -/
theorem forward_backward_query_key_gradient_duality {n d : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (Q K : Fin n → Fin d → ℝ) :
    (∑ i : Fin n, featureInner (Q i) (forwardKeyContraction G K i)) =
      ∑ j : Fin n, featureInner (backwardKeyGradient G Q j) (K j) := by
  dsimp [featureInner, forwardKeyContraction, backwardKeyGradient]
  calc
    (∑ i : Fin n, ∑ a : Fin d, Q i a * ∑ j : Fin n, G i j * K j a)
      = ∑ i : Fin n, ∑ a : Fin d, ∑ j : Fin n, Q i a * (G i j * K j a) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => ?_))
        rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin d, (G i j * Q i a) * K j a := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun a _ => ?_))
        exact forward_backward_scalar_comm (Q i a) (G i j) (K j a)
    _ = ∑ j : Fin n, ∑ i : Fin n, ∑ a : Fin d, (G i j * Q i a) * K j a :=
        Finset.sum_comm
    _ = ∑ j : Fin n, ∑ a : Fin d, ∑ i : Fin n, (G i j * Q i a) * K j a := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ a : Fin d, (∑ i : Fin n, G i j * Q i a) * K j a := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun a _ => ?_))
        rw [← Finset.sum_mul]

/-- Backward Key Gradient Upper-Triangular Causality: when the logit gradient `G` is causal
lower-triangular (`G i j = 0` for `i < j`), the backward gradient with respect to key `j`
depends only on present and future queries `i ≥ j`. -/
theorem backwardKeyGradient_depends_only_on_future_queries {n d : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (Q₁ Q₂ : Fin n → Fin d → ℝ) (j : Fin n)
    (hG : IsCausalLowerTriangular G)
    (hQ : ∀ i : Fin n, j ≤ i → Q₁ i = Q₂ i) :
    backwardKeyGradient G Q₁ j = backwardKeyGradient G Q₂ j := by
  funext a
  dsimp [backwardKeyGradient]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i < j
  · rw [hG i j hij, zero_mul, zero_mul]
  · rw [hQ i (not_lt.mp hij)]

/-- Double Krein Self-Adjointness of Forward–Backward Propagation: for any transition matrix
`P` and nowhere-vanishing measure `π`, the lifted operator `doubleKreinOp P π` is strictly
self-adjoint with respect to `kreinMetricPi π`. -/
theorem forward_backward_doubleKrein_selfAdjoint {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i : Fin n, π i ≠ 0)
    (u v : DoubleKreinSpace n) :
    kreinMetricPi π (doubleKreinOp P π u) v =
      kreinMetricPi π u (doubleKreinOp P π v) :=
  doubleKreinOp_krein_selfAdjoint P π hπ u v

/-!
## Section 3: RoPE as Relative Proper-Time Cancellation & Logarithmic Radial Interval
-/

/-- Explicit $2 \times 2$ matrix non-commutativity witness on `Mat2`: the elliptic rotation
generator and the split Lorentzian metric anti-commute and therefore do not commute. -/
theorem rope_mat2_noncommute :
    ellipticGenerator * splitMetric ≠ splitMetric * ellipticGenerator := by
  intro h
  have h01 : (ellipticGenerator * splitMetric) 0 1 =
      (splitMetric * ellipticGenerator) 0 1 := by
    rw [h]
  have h_eval : (ellipticGenerator * splitMetric) 0 1 = 1 ∧
      (splitMetric * ellipticGenerator) 0 1 = -1 := by
    simp [ellipticGenerator, splitMetric, Matrix.mul_apply, Fin.sum_univ_two]
  linarith [h_eval.1, h_eval.2]

/-- Standard Euclidean inner product on the 2D RoPE carrier plane $\operatorname{Fin} 2 \to \mathbb{R}$. -/
def vec2Inner (u v : Fin 2 → ℝ) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- Action of the discrete RoPE rotor at token position `m : ℤ` with frequency `θ : ℝ` on a 2D
feature vector `u : Fin 2 → ℝ`. -/
def ropeApply (θ : ℝ) (m : ℤ) (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (ropeRotor θ m).mulVec u

/-- Transposing a discrete RoPE rotor negates its integer token position:
$(R_\theta(m))^\top = R_\theta(-m)$. -/
theorem ropeRotor_transpose (θ : ℝ) (m : ℤ) :
    (ropeRotor θ m).transpose = ropeRotor θ (-m) := by
  unfold ropeRotor
  rw [rotation_transpose]
  congr 1
  push_cast
  ring

/-- Adjointness of $2 \times 2$ matrix-vector multiplication on the right of `vec2Inner`. -/
theorem planarInner_mulVec_right (A B : Mat2) (u v : Fin 2 → ℝ) :
    vec2Inner (A.mulVec u) (B.mulVec v) =
      vec2Inner u ((A.transpose * B).mulVec v) := by
  simp only [vec2Inner, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- Adjointness of $2 \times 2$ matrix-vector multiplication on the left of `vec2Inner`. -/
theorem planarInner_mulVec_left (A B : Mat2) (u v : Fin 2 → ℝ) :
    vec2Inner (A.mulVec u) (B.mulVec v) =
      vec2Inner ((B.transpose * A).mulVec u) v := by
  simp only [vec2Inner, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- RoPE Relative Proper-Time Cancellation: the inner product between a query rotated at
token position `m` and a key rotated at token position `n` depends only on the relative
proper-time offset `n - m` (or `m - n`). -/
theorem rope_inner_product_relative_time_cancellation
    (θ : ℝ) (m n : ℤ) (u v : Fin 2 → ℝ) :
    vec2Inner (ropeApply θ m u) (ropeApply θ n v) =
      vec2Inner u (ropeApply θ (n - m) v) ∧
    vec2Inner (ropeApply θ m u) (ropeApply θ n v) =
      vec2Inner (ropeApply θ (m - n) u) v := by
  refine ⟨?_, ?_⟩
  · dsimp [ropeApply]
    rw [planarInner_mulVec_right, ropeRotor_transpose, ropeRotor_relative]
  · dsimp [ropeApply]
    rw [planarInner_mulVec_left, ropeRotor_transpose, ropeRotor_relative]

/-- Absolute Context Translation Invariance: shifting both query position `m` and key position `n`
by any common integer offset `s : ℤ` leaves the RoPE inner product strictly invariant. -/
theorem rope_inner_product_shift_invariant
    (θ : ℝ) (m n s : ℤ) (u v : Fin 2 → ℝ) :
    vec2Inner (ropeApply θ (m + s) u) (ropeApply θ (n + s) v) =
      vec2Inner (ropeApply θ m u) (ropeApply θ n v) := by
  rw [(rope_inner_product_relative_time_cancellation θ (m + s) (n + s) u v).1,
      (rope_inner_product_relative_time_cancellation θ m n u v).1]
  have h_sub : (n + s) - (m + s) = n - m := by ring
  rw [h_sub]

/-- Conformal Logarithmic Proper-Time Interval: under the Milne/conformal radial clock
$\tau(r) = \ln(r / r_0)$, the reference scale $r_0 > 0$ cancels from the proper-time interval
$\tau(r_m) - \tau(r_n) = \ln(r_m / r_n)$, and the relative planar rotation depends only on the
dimensionless scale ratio $r_m / r_n$. -/
theorem conformal_log_proper_time_interval
    (θ r_m r_n r₀ : ℝ) (hr_m : 0 < r_m) (hr_n : 0 < r_n) (hr₀ : 0 < r₀) :
    Real.log (r_m / r₀) - Real.log (r_n / r₀) = Real.log (r_m / r_n) ∧
    (rotation (θ * Real.log (r_m / r₀))).transpose *
      rotation (θ * Real.log (r_n / r₀)) =
      rotation (-θ * Real.log (r_m / r_n)) := by
  have hr_m_ne : r_m ≠ 0 := ne_of_gt hr_m
  have hr_n_ne : r_n ≠ 0 := ne_of_gt hr_n
  have hr₀_ne : r₀ ≠ 0 := ne_of_gt hr₀
  have h_log : Real.log (r_m / r₀) - Real.log (r_n / r₀) = Real.log (r_m / r_n) := by
    rw [Real.log_div hr_m_ne hr₀_ne, Real.log_div hr_n_ne hr₀_ne, Real.log_div hr_m_ne hr_n_ne]
    ring
  refine ⟨h_log, ?_⟩
  rw [rotation_transpose, rotation_mul_rotation]
  congr 1
  calc
    -(θ * Real.log (r_m / r₀)) + θ * Real.log (r_n / r₀)
      = -θ * (Real.log (r_m / r₀) - Real.log (r_n / r₀)) := by ring
    _ = -θ * Real.log (r_m / r_n) := by rw [h_log]

/-!
## Section 4: Phase-Space Cotangent Symplectic Pairing
-/

/-- Canonical cotangent symplectic form $\omega((q_1, k_1), (q_2, k_2)) = \langle q_1, k_2 \rangle - \langle q_2, k_1 \rangle$
on the query–key phase space $(\operatorname{Fin} d \to \mathbb{R}) \times (\operatorname{Fin} d \to \mathbb{R})$. -/
def cotangentSymplecticForm {d : ℕ}
    (z₁ z₂ : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ :=
  featureInner z₁.1 z₂.2 - featureInner z₂.1 z₁.2

/-- Pairing any query vector with the zero key vector vanishes. -/
theorem featureInner_zero_right {d : ℕ} (q : Fin d → ℝ) :
    featureInner q 0 = 0 := by
  dsimp [featureInner]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  change q a * 0 = 0
  exact mul_zero (q a)

/-- Pairing the zero query vector with any key vector vanishes. -/
theorem featureInner_zero_left {d : ℕ} (k : Fin d → ℝ) :
    featureInner 0 k = 0 := by
  dsimp [featureInner]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  change 0 * k a = 0
  exact zero_mul (k a)

/-- Skew-symmetry, alternating self-nullity, Lagrangian isotropy of the pure-query momentum
sheet `(q, 0)` and pure-key configuration sheet `(0, k)`, and canonical cross-sheet pairing
of `cotangentSymplecticForm`. -/
theorem cotangentSymplecticForm_skew {d : ℕ}
    (z₁ z₂ : (Fin d → ℝ) × (Fin d → ℝ))
    (q q₁ q₂ k k₁ k₂ : Fin d → ℝ) :
    cotangentSymplecticForm z₁ z₂ = -cotangentSymplecticForm z₂ z₁ ∧
    cotangentSymplecticForm z₁ z₁ = 0 ∧
    (cotangentSymplecticForm (q₁, 0) (q₂, 0) = 0 ∧
      cotangentSymplecticForm (0, k₁) (0, k₂) = 0) ∧
    cotangentSymplecticForm (q, 0) (0, k) = featureInner q k := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · dsimp [cotangentSymplecticForm]
    ring
  · dsimp [cotangentSymplecticForm]
    ring
  · dsimp [cotangentSymplecticForm]
    rw [featureInner_zero_right, featureInner_zero_right, sub_self]
  · dsimp [cotangentSymplecticForm]
    rw [featureInner_zero_left, featureInner_zero_left, sub_self]
  · dsimp [cotangentSymplecticForm]
    rw [featureInner_zero_left, sub_zero]

/-!
## Section 5: Transactional Cotangent Action Surprisal
-/

/-- The transactional attention logit $S_{ij}$ equals the scaled cotangent symplectic pairing
between the pure-query momentum state $(Q_i, 0)$ and the pure-key configuration state $(0, K_j)$. -/
theorem transactionalLogit_eq_scaled_cotangentSymplecticForm {n d : ℕ}
    (scale : ℝ) (Q K : Fin n → Fin d → ℝ) (i j : Fin n) :
    transactionalLogitMatrix scale Q K i j =
      scale * cotangentSymplecticForm (Q i, 0) (0, K j) := by
  dsimp [transactionalLogitMatrix, cotangentSymplecticForm]
  rw [featureInner_zero_left, sub_zero]

/-- Modular surprisal of the transactional softmax attention weight $A_{ij} = \exp(S_{ij}) / Z$
equals the negative scaled cotangent symplectic pairing plus the log-partition potential $\ln Z$. -/
theorem transactionalSoftmax_modularSurprisal_eq_cotangentAction {n d : ℕ}
    (Z scale : ℝ) (Q K : Fin n → Fin d → ℝ) (i j : Fin n) (hZ : 0 < Z) :
    modularSurprisal (attentionSoftmaxWeight Z (transactionalLogitMatrix scale Q K i j)) =
      -scale * cotangentSymplecticForm (Q i, 0) (0, K j) + Real.log Z := by
  rw [attentionSoftmax_surprisal_eq Z (transactionalLogitMatrix scale Q K i j) hZ,
      transactionalLogit_eq_scaled_cotangentSymplecticForm]
  ring

end

end InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge
