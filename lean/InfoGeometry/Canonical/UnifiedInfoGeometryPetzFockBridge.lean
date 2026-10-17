/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.AmariChentsovDualConnections
import InfoGeometry.Canonical.ParaKahlerGradedFockCAR
import InfoGeometry.QuantumContext.AttentionKMSPetzRecoveryBridge

/-!
# Unified Information Geometry, Token-Simplex Petz Recovery, and Para-Kähler Fock CAR Bridge

This module synthesizes the token-simplex Petz transpose recovery map, the stationary
KMS modular operator (`AttentionKMSPetzRecoveryBridge`), the Amari–Chentsov dual
`(e, m)`-connection manifold on `(ι → ℝ)`, and the graded Fock CAR superbracket:

1. **Archetype I — Classical / Token-Simplex Petz Recovery Map & Chi-Squared Adjointness**:
   - Defines forward Markov coarse-graining `markovCoarseGrain T x`, the inverse-prior
     chi-squared / Fisher bilinear form `chiSquaredInner ρ u v = ∑ a, u_a v_a / ρ_a`,
     the classical Petz transpose recovery map `petzRecoveryVec ρ T coarsePrior y`, and its
     canonical softmax specialization `attentionPetzRecovery logits β T y`.
   - Proves exact chi-squared adjointness (`petzRecoveryVec_chiSquared_adjoint` and
     `attentionPetzRecovery_chiSquared_adjoint`):
     `⟨R_{ρ,T}(y), x⟩_{ρ⁻¹} = ⟨y, T x⟩_{(T ρ)⁻¹}`.

2. **Archetype II — Probability Mass Conservation, Stationary Modular Bridge & Prior Reconstruction**:
   - Proves probability mass conservation `∑ i, R_{ρ,T}(y)_i = ∑ j, y_j` (`petzRecoveryVec_sum_eq`),
     exact prior reconstruction `R_{ρ,T}(T ρ) = ρ` under column-stochasticity
     (`petzRecoveryVec_coarseGrain_self` and `attentionPetzRecovery_coarseGrain_softmaxWeight`),
     automatic discharge of `0 < (T ρ)_j` for non-negative row-non-degenerate kernels `T`
     (`markovCoarseGrain_pos_of_pos`, `markovCoarseGrain_softmaxWeight_pos`,
     `attentionPetzRecovery_sum_eq_of_nonneg_pos`, `attentionPetzRecovery_coarseGrain_of_nonneg_pos`),
     and entrywise non-negativity (`petzRecoveryVec_nonneg`).
   - Bridges stationary Petz recovery (`coarsePrior = ρ`) to
     `AttentionKMSPetzRecoveryBridge.weightedAdjoint_transpose_eq_modularDelta` and
     `detailedBalance_softmax_iff_modularDelta_eq_transpose`, showing that under stationarity
     and detailed balance of `Tᵀ`, `attentionPetzRecovery logits β T` coincides with
     `markovCoarseGrain T`.

3. **Archetype III — Chi-Squared Amari–Chentsov `DualConnectionManifold (ι → ℝ)`**:
   - Proves strict positive definiteness `chiSquaredInner_pos_of_ne_zero` for strictly
     positive priors `0 < ρ_i`.
   - Constructs the concrete `DualConnectionManifold (ι → ℝ)` (`chiSquaredDualManifold` and
     `attentionDualManifold`) with metric `chiSquaredInner ρ`, cubic skewness tensor
     `diff_g X Y Z = ∑ i, X_i Y_i Z_i / ρ_i²`, exponential connection
     `(∇^(e)_X Y)_i = X_i Y_i / ρ_i`, and flat mixture connection `∇^(m) = 0`, proving
     Amari `(α, -α)` metric conjugacy and Petz metric adjointness on `attentionDualManifold`.

4. **Archetype IV — Fock CAR Superbracket — Petz Chi-Squared Synthesis & Pooling Witnesses**:
   - Defines `chiSquaredDualFunctional` in `Module.Dual ℝ (ι → ℝ)` and proves
     `fock_superBracket_attentionPetzRecovery_eq_coarseGrain_chiSquared` and
     `paraKahler_fock_superBracket_eq_chiSquared_petz`, directly equating the odd-odd Fock
     CAR superbracket of a fine mode `x` and a Petz-recovered covector mode `R_{ρ,T}(y)` to
     `chiSquaredInner (T ρ) y (T x) • 1`.
   - Constructs both the 2-to-1 token pooling kernel `uniformPoolingMatrix : Matrix (Fin 1) (Fin 2) ℝ`
     and the 4-to-2 block cluster pooling kernel `blockClusterPoolingMatrix : Matrix (Fin 2) (Fin 4) ℝ`,
     proving exact cluster-wise Boltzmann ratio recovery on `Fin 4`.

## Scope Note

This module formalizes:
1. the commutative / classical token-simplex Petz recovery map
   `R_{ρ,T}(y)_i = ρ_i ∑_j T_{j,i} (y_j / (T ρ)_j)`, its exact adjointness with respect to
   `chiSquaredInner`, and its stationary bridge to `MatrixGNS.modularDelta` /
   `attentionModularDelta`,
2. the concrete `DualConnectionManifold (ι → ℝ)` induced by `chiSquaredInner ρ` and its
   cubic skewness tensor, and
3. the all-degree algebraic exterior CAR superbracket on `FockSpace (ι → ℝ)` and
   `FockExteriorEnvelope K` paired via `chiSquaredDualFunctional`.

It does not claim a non-commutative operator-valued CPTP square-root Petz recovery channel
`σ^{1/2} N†(N(σ)^{-1/2} · N(σ)^{-1/2}) σ^{1/2}` or an infinite-dimensional Hilbert-Fock completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge

open BigOperators Matrix
open InfoGeometry.Modular
open InfoGeometry.Canonical
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionKMSPetzRecoveryBridge

variable {α ι κ : Type*}

/-! ### Archetype I: Classical / Token-Simplex Petz Recovery Map & Chi-Squared Adjointness -/

private theorem mul_self_div_nonneg (u r : ℝ) (hr : 0 ≤ r) :
    0 ≤ u * u / r :=
  div_nonneg (mul_self_nonneg u) hr

private theorem petz_inner_term_rearrange (t y c x : ℝ) :
    (t * (y / c)) * x = y * (t * x) / c := by
  ring

/-- Forward Markov / transition coarse-graining of a fine token vector `x : ι → ℝ`
by a kernel matrix `T : Matrix κ ι ℝ`: `(T x)_j = ∑ i, T_{j,i} x_i`. -/
def markovCoarseGrain [Fintype ι] (T : Matrix κ ι ℝ) (x : ι → ℝ) : κ → ℝ :=
  fun j => ∑ i, T j i * x i

/-- Inverse-prior chi-squared / Fisher bilinear form on `α → ℝ`:
`⟨u, v⟩_{ρ⁻¹} = ∑ a, u_a v_a / ρ_a`. -/
def chiSquaredInner [Fintype α] (ρ u v : α → ℝ) : ℝ :=
  ∑ a, u a * v a / ρ a

/-- Classical / token-simplex Petz transpose recovery map associated with fine prior `ρ`,
transition kernel `T : Matrix κ ι ℝ`, and coarse prior `coarsePrior`:
`R_{ρ,T}(y)_i = ρ_i ∑ j, T_{j,i} (y_j / coarsePrior_j)`. -/
def petzRecoveryVec [Fintype κ]
    (ρ : ι → ℝ) (T : Matrix κ ι ℝ) (coarsePrior : κ → ℝ) (y : κ → ℝ) : ι → ℝ :=
  fun i => ρ i * ∑ j, T j i * (y j / coarsePrior j)

/-- Canonical specialization of `petzRecoveryVec` to the softmax thermal prior
`ρ = softmaxWeight logits β` and its pushed-forward coarse prior
`markovCoarseGrain T (softmaxWeight logits β)`. -/
def attentionPetzRecovery [Fintype ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ) (y : κ → ℝ) : ι → ℝ :=
  petzRecoveryVec (softmaxWeight logits β) T
    (markovCoarseGrain T (softmaxWeight logits β)) y

/-- Symmetry of the inverse-prior chi-squared bilinear form:
`chiSquaredInner ρ u v = chiSquaredInner ρ v u`. -/
theorem chiSquaredInner_symm [Fintype α] (ρ u v : α → ℝ) :
    chiSquaredInner ρ u v = chiSquaredInner ρ v u := by
  dsimp [chiSquaredInner]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm (u a) (v a)]

/-- Non-negativity of the quadratic chi-squared form `chiSquaredInner ρ u u`
for non-negative prior weights `0 ≤ ρ_a`. -/
theorem chiSquaredInner_self_nonneg [Fintype α]
    (ρ u : α → ℝ) (hρ : ∀ a, 0 ≤ ρ a) :
    0 ≤ chiSquaredInner ρ u u := by
  dsimp [chiSquaredInner]
  apply Finset.sum_nonneg
  intro a _
  exact mul_self_div_nonneg (u a) (ρ a) (hρ a)

/-- Strict positive definiteness of `chiSquaredInner ρ u u` when `0 < ρ_a` for all `a`
and `u ≠ 0`. -/
theorem chiSquaredInner_pos_of_ne_zero [Fintype α] [DecidableEq α]
    (ρ u : α → ℝ) (hρ : ∀ a, 0 < ρ a) (hu : u ≠ 0) :
    0 < chiSquaredInner ρ u u := by
  obtain ⟨a₀, ha₀⟩ : ∃ a, u a ≠ 0 := Function.ne_iff.mp hu
  dsimp [chiSquaredInner]
  have h_pos : 0 < u a₀ * u a₀ / ρ a₀ :=
    div_pos (mul_self_pos.mpr ha₀) (hρ a₀)
  have h_le : u a₀ * u a₀ / ρ a₀ ≤ ∑ a, u a * u a / ρ a :=
    Finset.single_le_sum
      (fun a _ => mul_self_div_nonneg (u a) (ρ a) (le_of_lt (hρ a)))
      (Finset.mem_univ a₀)
  exact lt_of_lt_of_le h_pos h_le

/-- **Exact Petz Chi-Squared Adjointness**:
For any everywhere non-zero fine prior `ρ`, transition kernel `T : Matrix κ ι ℝ`, and coarse
reference weight `coarsePrior`, `petzRecoveryVec ρ T coarsePrior` is the exact adjoint of
`markovCoarseGrain T` between `chiSquaredInner coarsePrior` and `chiSquaredInner ρ`. -/
theorem petzRecoveryVec_chiSquared_adjoint [Fintype ι] [Fintype κ]
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i ≠ 0) (T : Matrix κ ι ℝ)
    (coarsePrior : κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    chiSquaredInner ρ (petzRecoveryVec ρ T coarsePrior y) x =
      chiSquaredInner coarsePrior y (markovCoarseGrain T x) := by
  dsimp [chiSquaredInner, petzRecoveryVec, markovCoarseGrain]
  have h_lhs :
      (∑ i, ρ i * (∑ j, T j i * (y j / coarsePrior j)) * x i / ρ i) =
        ∑ i, ∑ j, (T j i * (y j / coarsePrior j)) * x i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc (ρ i), mul_div_cancel_left₀ _ (hρ i), Finset.sum_mul]
  rw [h_lhs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  exact petz_inner_term_rearrange (T j i) (y j) (coarsePrior j) (x i)

/-- **Attention KMS Petz Chi-Squared Adjointness**:
Because `softmaxWeight logits β i > 0` for every token `i`, `attentionPetzRecovery logits β T`
is the exact chi-squared adjoint of `markovCoarseGrain T` without any external positivity
hypothesis on the fine prior. -/
theorem attentionPetzRecovery_chiSquared_adjoint
    [Fintype ι] [Nonempty ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    chiSquaredInner (softmaxWeight logits β)
        (attentionPetzRecovery logits β T y) x =
      chiSquaredInner (markovCoarseGrain T (softmaxWeight logits β))
        y (markovCoarseGrain T x) :=
  petzRecoveryVec_chiSquared_adjoint (softmaxWeight logits β)
    (fun i => ne_of_gt (softmaxWeight_pos logits β i)) T
    (markovCoarseGrain T (softmaxWeight logits β)) x y

/-! ### Archetype II: Probability Mass Conservation, Stationary Modular Bridge & Prior Reconstruction -/

private theorem mul_mul_div_rearrange (r t y c : ℝ) :
    r * (t * (y / c)) = (t * r) * (y / c) := by
  ring

private theorem stationary_petz_term_eq (ri rj tji yj : ℝ) :
    ri * (tji * (yj / rj)) = (rj⁻¹ * tji * ri) * yj := by
  rw [div_eq_mul_inv]
  ring

/-- **Probability Mass Conservation of Petz Recovery**:
Whenever the coarse prior `markovCoarseGrain T ρ` is everywhere non-zero, the Petz recovery
map preserves total mass: `∑ i, R_{ρ,T}(y)_i = ∑ j, y_j`. -/
theorem petzRecoveryVec_sum_eq [Fintype ι] [Fintype κ]
    (ρ : ι → ℝ) (T : Matrix κ ι ℝ)
    (h_pos : ∀ j, markovCoarseGrain T ρ j ≠ 0) (y : κ → ℝ) :
    ∑ i, petzRecoveryVec ρ T (markovCoarseGrain T ρ) y i = ∑ j, y j := by
  dsimp [petzRecoveryVec]
  have h_expand :
      (∑ i, ρ i * ∑ j, T j i * (y j / markovCoarseGrain T ρ j)) =
        ∑ i, ∑ j, (T j i * ρ i) * (y j / markovCoarseGrain T ρ j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_mul_div_rearrange (ρ i) (T j i) (y j) (markovCoarseGrain T ρ j)
  rw [h_expand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  change markovCoarseGrain T ρ j * (y j / markovCoarseGrain T ρ j) = y j
  exact mul_div_cancel₀ (y j) (h_pos j)

/-- **Exact Prior Fixed-Point Reconstruction**:
If `T` is column-stochastic (`∀ i, ∑ j, T j i = 1`) and `markovCoarseGrain T ρ` is nowhere
zero, applying `petzRecoveryVec` to the coarse-grained prior `markovCoarseGrain T ρ`
recovers the exact fine prior `ρ`. -/
theorem petzRecoveryVec_coarseGrain_self [Fintype ι] [Fintype κ]
    (ρ : ι → ℝ) (T : Matrix κ ι ℝ)
    (h_pos : ∀ j, markovCoarseGrain T ρ j ≠ 0)
    (h_col : ∀ i, ∑ j, T j i = 1) (i : ι) :
    petzRecoveryVec ρ T (markovCoarseGrain T ρ) (markovCoarseGrain T ρ) i = ρ i := by
  dsimp [petzRecoveryVec]
  have h_sum :
      (∑ j, T j i * (markovCoarseGrain T ρ j / markovCoarseGrain T ρ j)) =
        ∑ j, T j i := by
    apply Finset.sum_congr rfl
    intro j _
    rw [div_self (h_pos j), mul_one]
  rw [h_sum, h_col i, mul_one]

/-- **Exact Softmax Thermal Prior Reconstruction**:
Under a column-stochastic coarse-graining kernel `T` with non-vanishing coarse prior,
`attentionPetzRecovery logits β T` reconstructs `softmaxWeight logits β` from its coarse
marginal `markovCoarseGrain T (softmaxWeight logits β)`. -/
theorem attentionPetzRecovery_coarseGrain_softmaxWeight
    [Fintype ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ)
    (h_pos : ∀ j, markovCoarseGrain T (softmaxWeight logits β) j ≠ 0)
    (h_col : ∀ i, ∑ j, T j i = 1) (i : ι) :
    attentionPetzRecovery logits β T
        (markovCoarseGrain T (softmaxWeight logits β)) i =
      softmaxWeight logits β i :=
  petzRecoveryVec_coarseGrain_self (softmaxWeight logits β) T h_pos h_col i

/-- If `ρ` is strictly positive and every coarse row `j` of a non-negative kernel `T` has
at least one strictly positive entry `T_{j,i₀} > 0`, then `0 < markovCoarseGrain T ρ j`. -/
theorem markovCoarseGrain_pos_of_pos [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (T : Matrix κ ι ℝ)
    (hT_nonneg : ∀ j i, 0 ≤ T j i) (hT_pos : ∀ j, ∃ i, 0 < T j i) (j : κ) :
    0 < markovCoarseGrain T ρ j := by
  obtain ⟨i₀, hi₀⟩ := hT_pos j
  dsimp [markovCoarseGrain]
  have h_pos : 0 < T j i₀ * ρ i₀ := mul_pos hi₀ (hρ i₀)
  have h_le : T j i₀ * ρ i₀ ≤ ∑ i, T j i * ρ i :=
    Finset.single_le_sum
      (fun i _ => mul_nonneg (hT_nonneg j i) (le_of_lt (hρ i)))
      (Finset.mem_univ i₀)
  exact lt_of_lt_of_le h_pos h_le

/-- Under a non-negative coarse-graining kernel `T` with no identically zero rows,
the coarse-grained softmax prior `markovCoarseGrain T (softmaxWeight logits β)` is
strictly positive at every coarse token `j`. -/
theorem markovCoarseGrain_softmaxWeight_pos
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ)
    (hT_nonneg : ∀ j i, 0 ≤ T j i) (hT_pos : ∀ j, ∃ i, 0 < T j i) (j : κ) :
    0 < markovCoarseGrain T (softmaxWeight logits β) j :=
  markovCoarseGrain_pos_of_pos (softmaxWeight logits β)
    (softmaxWeight_pos logits β) T hT_nonneg hT_pos j

/-- Probability mass conservation for `attentionPetzRecovery` with `(T ρ)_j ≠ 0`
discharged automatically from non-negativity and row non-degeneracy of `T` together with
`softmaxWeight_pos`. -/
theorem attentionPetzRecovery_sum_eq_of_nonneg_pos
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ)
    (hT_nonneg : ∀ j i, 0 ≤ T j i) (hT_pos : ∀ j, ∃ i, 0 < T j i) (y : κ → ℝ) :
    ∑ i, attentionPetzRecovery logits β T y i = ∑ j, y j :=
  petzRecoveryVec_sum_eq (softmaxWeight logits β) T
    (fun j => ne_of_gt (markovCoarseGrain_softmaxWeight_pos logits β T hT_nonneg hT_pos j)) y

/-- Exact softmax thermal prior reconstruction with `(T ρ)_j ≠ 0` discharged automatically
from non-negativity, row non-degeneracy, and column-stochasticity of `T`. -/
theorem attentionPetzRecovery_coarseGrain_of_nonneg_pos
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ)
    (hT_nonneg : ∀ j i, 0 ≤ T j i) (hT_pos : ∀ j, ∃ i, 0 < T j i)
    (h_col : ∀ i, ∑ j, T j i = 1) (i : ι) :
    attentionPetzRecovery logits β T
        (markovCoarseGrain T (softmaxWeight logits β)) i =
      softmaxWeight logits β i :=
  attentionPetzRecovery_coarseGrain_softmaxWeight logits β T
    (fun j => ne_of_gt (markovCoarseGrain_softmaxWeight_pos logits β T hT_nonneg hT_pos j))
    h_col i

/-- Entrywise non-negativity of `petzRecoveryVec` for non-negative weights, transition
entries, coarse prior, and input vector. -/
theorem petzRecoveryVec_nonneg [Fintype κ]
    (ρ : ι → ℝ) (T : Matrix κ ι ℝ) (coarsePrior : κ → ℝ) (y : κ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hT : ∀ j i, 0 ≤ T j i)
    (h_cp : ∀ j, 0 ≤ coarsePrior j) (hy : ∀ j, 0 ≤ y j) (i : ι) :
    0 ≤ petzRecoveryVec ρ T coarsePrior y i := by
  dsimp [petzRecoveryVec]
  apply mul_nonneg (hρ i)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hT j i) (div_nonneg (hy j) (h_cp j))

/-- When `κ = ι` and `coarsePrior = ρ` (a stationary distribution of `T`), the classical
Petz recovery action `petzRecoveryVec ρ T ρ y` agrees with the matrix-vector action of
`(Probability.weightedAdjoint ρ Tᵀ)ᵀ`. -/
theorem petzRecoveryVec_stationary_eq_weightedAdjoint [Fintype ι]
    (ρ : ι → ℝ) (T : Matrix ι ι ℝ) (y : ι → ℝ) (i : ι) :
    petzRecoveryVec ρ T ρ y i =
      ∑ j, (InfoGeometry.Probability.weightedAdjoint ρ Tᵀ)ᵀ i j * y j := by
  dsimp [petzRecoveryVec, InfoGeometry.Probability.weightedAdjoint, Matrix.transpose_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact stationary_petz_term_eq (ρ i) (ρ j) (T j i) (y j)

/-- By `AttentionKMSPetzRecoveryBridge.weightedAdjoint_transpose_eq_modularDelta`,
when `coarsePrior = ρ`, the classical Petz recovery action `petzRecoveryVec ρ T ρ y`
is the matrix-vector action of `MatrixGNS.modularDelta ρ Tᵀ`. -/
theorem petzRecoveryVec_stationary_eq_modularDelta [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (T : Matrix ι ι ℝ) (y : ι → ℝ) (i : ι) :
    petzRecoveryVec ρ T ρ y i =
      ∑ j, InfoGeometry.QuantumContext.MatrixGNS.modularDelta ρ Tᵀ i j * y j := by
  rw [petzRecoveryVec_stationary_eq_weightedAdjoint]
  apply Finset.sum_congr rfl
  intro j _
  rw [weightedAdjoint_transpose_eq_modularDelta]

/-- When `softmaxWeight logits β` is stationary under `markovCoarseGrain T`,
`attentionPetzRecovery logits β T y` equals the matrix-vector action of the KMS modular
operator `attentionModularDelta logits β Tᵀ` on `y`. -/
theorem attentionPetzRecovery_of_stationary_eq_attentionModularDelta
    [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix ι ι ℝ)
    (h_stat : markovCoarseGrain T (softmaxWeight logits β) = softmaxWeight logits β)
    (y : ι → ℝ) (i : ι) :
    attentionPetzRecovery logits β T y i =
      ∑ j, attentionModularDelta logits β Tᵀ i j * y j := by
  dsimp [attentionPetzRecovery, attentionModularDelta]
  rw [h_stat]
  exact petzRecoveryVec_stationary_eq_modularDelta (softmaxWeight logits β) T y i

/-- Under stationarity `markovCoarseGrain T ρ = ρ` and detailed balance of `Tᵀ` with respect
to `softmaxWeight logits β`, `attentionPetzRecovery logits β T` coincides entrywise with
`markovCoarseGrain T` via `detailedBalance_softmax_iff_modularDelta_eq_transpose`. -/
theorem attentionPetzRecovery_eq_markovCoarseGrain_of_detailedBalance
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix ι ι ℝ)
    (h_stat : markovCoarseGrain T (softmaxWeight logits β) = softmaxWeight logits β)
    (hDB : InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β) Tᵀ)
    (y : ι → ℝ) (i : ι) :
    attentionPetzRecovery logits β T y i = markovCoarseGrain T y i := by
  rw [attentionPetzRecovery_of_stationary_eq_attentionModularDelta logits β T h_stat y i]
  have h_mod : attentionModularDelta logits β Tᵀ = (Tᵀ)ᵀ :=
    (detailedBalance_softmax_iff_modularDelta_eq_transpose logits β Tᵀ).mp hDB
  rw [h_mod, Matrix.transpose_transpose]
  rfl

/-! ### Archetype III: Chi-Squared Amari–Chentsov `DualConnectionManifold (ι → ℝ)` -/

private theorem add_mul_div_eq (a b c r : ℝ) :
    (a + b) * c / r = a * c / r + b * c / r := by
  ring

private theorem mul_add_div_eq (a b c r : ℝ) :
    a * (b + c) / r = a * b / r + a * c / r := by
  ring

private theorem smul_mul_div_eq (c a b r : ℝ) :
    (c * a) * b / r = c * (a * b / r) := by
  ring

private theorem mul_smul_div_eq (c a b r : ℝ) :
    a * (c * b) / r = c * (a * b / r) := by
  ring

private theorem cubic_symm_eq (x y z rr : ℝ) :
    x * y * z / rr = x * z * y / rr := by
  ring

private theorem cubic_add_left_eq (x y z w rr : ℝ) :
    (x + y) * z * w / rr = x * z * w / rr + y * z * w / rr := by
  ring

private theorem cubic_duality_term_eq (x y z r : ℝ) :
    x * y * z / (r * r) = (x * y / r) * z / r + y * 0 / r := by
  ring

/-- At `α = 1`, the Amari `α`-connection recovers the exponential connection `∇^(e)`. -/
theorem alphaConnection_pos_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : AmariChentsovDualConnections.DualConnectionManifold V) (X Y : V) :
    AmariChentsovDualConnections.alphaConnection M 1 X Y = M.nabla_e X Y := by
  dsimp [AmariChentsovDualConnections.alphaConnection]
  have h1 : ((1 + (1 : ℝ)) / 2 : ℝ) = 1 := by norm_num
  have h0 : ((1 - (1 : ℝ)) / 2 : ℝ) = 0 := by norm_num
  rw [h1, h0, one_smul, zero_smul, add_zero]

/-- At `α = -1`, the Amari `α`-connection recovers the mixture connection `∇^(m)`. -/
theorem alphaConnection_neg_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : AmariChentsovDualConnections.DualConnectionManifold V) (X Y : V) :
    AmariChentsovDualConnections.alphaConnection M (-1) X Y = M.nabla_m X Y := by
  dsimp [AmariChentsovDualConnections.alphaConnection]
  have h0 : ((1 + (-1 : ℝ)) / 2 : ℝ) = 0 := by norm_num
  have h1 : ((1 - (-1 : ℝ)) / 2 : ℝ) = 1 := by norm_num
  rw [h0, h1, zero_smul, one_smul, zero_add]

/-- At `α = 0`, the Amari `α`-connection equals the metric-compatible Levi-Civita midpoint
connection `leviCivitaBridge M` and satisfies the Leibniz metric compatibility law. -/
theorem dualConnection_midpoint_is_leviCivita {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : AmariChentsovDualConnections.DualConnectionManifold V) (X Y Z : V) :
    AmariChentsovDualConnections.alphaConnection M 0 X Y =
        AmariChentsovDualConnections.leviCivitaBridge M X Y ∧
      M.g (AmariChentsovDualConnections.leviCivitaBridge M X Y) Z +
        M.g Y (AmariChentsovDualConnections.leviCivitaBridge M X Z) =
          M.diff_g X Y Z :=
  ⟨AmariChentsovDualConnections.alpha_zero_eq_levi_civita_bridge M X Y,
   AmariChentsovDualConnections.levi_civita_bridge_metric_compatibility M X Y Z⟩

/-- Non-trivial Amari–Chentsov `DualConnectionManifold (ι → ℝ)` equipped with the
inverse-prior chi-squared metric `chiSquaredInner ρ`, the cubic skewness tensor
`diff_g X Y Z = ∑ i, X_i Y_i Z_i / ρ_i²`, the exponential connection
`(∇^(e)_X Y)_i = X_i Y_i / ρ_i`, and the flat mixture connection `∇^(m) = 0`. -/
def chiSquaredDualManifold [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) :
    AmariChentsovDualConnections.DualConnectionManifold (ι → ℝ) where
  g := chiSquaredInner ρ
  g_add_left x y z := by
    dsimp [chiSquaredInner]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => add_mul_div_eq (x i) (y i) (z i) (ρ i))
  g_add_right x y z := by
    dsimp [chiSquaredInner]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => mul_add_div_eq (x i) (y i) (z i) (ρ i))
  g_smul_left r x y := by
    dsimp [chiSquaredInner]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => smul_mul_div_eq r (x i) (y i) (ρ i))
  g_smul_right r x y := by
    dsimp [chiSquaredInner]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_smul_div_eq r (x i) (y i) (ρ i))
  g_symm := chiSquaredInner_symm ρ
  g_pos_def x hx := chiSquaredInner_pos_of_ne_zero ρ x hρ hx
  diff_g X Y Z := ∑ i, X i * Y i * Z i / (ρ i * ρ i)
  diff_g_symm x y z :=
    Finset.sum_congr rfl (fun i _ => cubic_symm_eq (x i) (y i) (z i) (ρ i * ρ i))
  diff_g_add x y z w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => cubic_add_left_eq (x i) (y i) (z i) (w i) (ρ i * ρ i))
  nabla_e X Y i := X i * Y i / ρ i
  nabla_m _ _ _ := 0
  nabla_e_add_left x y z := funext (fun i => add_mul_div_eq (x i) (y i) (z i) (ρ i))
  nabla_e_add_right x y z := funext (fun i => mul_add_div_eq (x i) (y i) (z i) (ρ i))
  nabla_e_smul_left r x y := funext (fun i => smul_mul_div_eq r (x i) (y i) (ρ i))
  nabla_e_smul_right r x y := funext (fun i => mul_smul_div_eq r (x i) (y i) (ρ i))
  nabla_m_add_left _ _ _ := (add_zero 0).symm
  nabla_m_add_right _ _ _ := (add_zero 0).symm
  nabla_m_smul_left r _ _ := (smul_zero r).symm
  nabla_m_smul_right r _ _ := (smul_zero r).symm
  amari_duality X Y Z := by
    dsimp [chiSquaredInner]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => cubic_duality_term_eq (X i) (Y i) (Z i) (ρ i))

/-- Canonical Amari–Chentsov `DualConnectionManifold (ι → ℝ)` induced by the
softmax thermal weights `softmaxWeight logits β`. -/
def attentionDualManifold [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    AmariChentsovDualConnections.DualConnectionManifold (ι → ℝ) :=
  chiSquaredDualManifold (softmaxWeight logits β) (softmaxWeight_pos logits β)

/-- Specializing `AmariChentsovDualConnections.alpha_connection_duality` to
`attentionDualManifold logits β`: the `(α, -α)` connections are dual with respect to the
softmax chi-squared metric and cubic skewness tensor. -/
theorem attentionDualManifold_alpha_duality
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β alpha : ℝ) (X Y Z : ι → ℝ) :
    (attentionDualManifold logits β).g
        (AmariChentsovDualConnections.alphaConnection (attentionDualManifold logits β) alpha X Y) Z +
      (attentionDualManifold logits β).g Y
        (AmariChentsovDualConnections.alphaConnection (attentionDualManifold logits β) (-alpha) X Z) =
      (attentionDualManifold logits β).diff_g X Y Z :=
  AmariChentsovDualConnections.alpha_connection_duality
    (attentionDualManifold logits β) alpha X Y Z

/-- The Riemannian metric `(attentionDualManifold logits β).g` of the softmax dual connection
manifold satisfies Petz recovery adjointness with respect to `markovCoarseGrain T`. -/
theorem attentionDualManifold_petz_adjoint
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (attentionDualManifold logits β).g (attentionPetzRecovery logits β T y) x =
      chiSquaredInner (markovCoarseGrain T (softmaxWeight logits β))
        y (markovCoarseGrain T x) :=
  attentionPetzRecovery_chiSquared_adjoint logits β T x y

/-! ### Archetype IV: Fock CAR Superbracket — Petz Chi-Squared Synthesis & Pooling Witnesses -/

/-- The linear covector functional `v ↦ chiSquaredInner ρ u v` in `Module.Dual ℝ (ι → ℝ)`
associated with a fine vector `u : ι → ℝ` under the inverse-prior metric `chiSquaredInner ρ`. -/
def chiSquaredDualFunctional [Fintype ι] (ρ u : ι → ℝ) :
    Module.Dual ℝ (ι → ℝ) where
  toFun v := chiSquaredInner ρ u v
  map_add' v w := by
    dsimp [chiSquaredInner]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => mul_add_div_eq (u i) (v i) (w i) (ρ i))
  map_smul' c v := by
    dsimp [chiSquaredInner]
    change (∑ i, u i * (c * v i) / ρ i) = c * ∑ i, u i * v i / ρ i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_smul_div_eq c (u i) (v i) (ρ i))

@[simp]
theorem chiSquaredDualFunctional_apply [Fintype ι] (ρ u v : ι → ℝ) :
    chiSquaredDualFunctional ρ u v = chiSquaredInner ρ u v :=
  rfl

/-- **All-Degree Exterior Fock CAR — Attention KMS Petz Chi-Squared Adjointness Bridge**:
On the exterior Fock space `FockSpace (ι → ℝ) = ⋀ (ι → ℝ)`, the odd-odd graded Lie
superbracket between the creation endomorphism `creationOperator x` of a fine mode `x`
and the annihilation endomorphism `annihilationOperator` of the Petz-recovered covector
`chiSquaredDualFunctional (softmaxWeight logits β) (attentionPetzRecovery logits β T y)`
evaluates across all exterior degrees to the coarse-grained chi-squared inner product
`chiSquaredInner (markovCoarseGrain T (softmaxWeight logits β)) y (markovCoarseGrain T x) • 1`. -/
theorem fock_superBracket_attentionPetzRecovery_eq_coarseGrain_chiSquared
    [Fintype ι] [Nonempty ι] [Fintype κ]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ ι ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (InfoGeometry.Clifford.FockSpaceCAR.creationOperator x)
        (InfoGeometry.Clifford.FockSpaceCAR.annihilationOperator
          (chiSquaredDualFunctional (softmaxWeight logits β)
            (attentionPetzRecovery logits β T y))) =
      (chiSquaredInner (markovCoarseGrain T (softmaxWeight logits β))
        y (markovCoarseGrain T x)) •
        (1 : Module.End ℝ (InfoGeometry.Clifford.FockSpaceCAR.FockSpace (ι → ℝ))) := by
  rw [InfoGeometry.Clifford.FockSpaceCAR.creation_annihilation_superBracket]
  rw [chiSquaredDualFunctional_apply]
  rw [attentionPetzRecovery_chiSquared_adjoint logits β T x y]

/-- **Para-Kähler Graded Fock CAR — Petz Chi-Squared Bridge**:
When the hyperbolic cross-sheet pairing `g α.1 u.1` between a covector mode
`α : covectorVacuumSheet K` and a primal mode `u : primalSheet K` realizes the fine
chi-squared pairing `chiSquaredInner ρ (petzRecoveryVec ρ T coarsePrior y) x`, the odd-odd
superbracket `[c†(u), c(α)]` on `FockExteriorEnvelope K` equals the coarse-grained
chi-squared pairing `chiSquaredInner coarsePrior y (markovCoarseGrain T x) • 1`. -/
theorem paraKahler_fock_superBracket_eq_chiSquared_petz
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (u : SuperGrassmannianProjectorEnvelope.primalSheet K)
    (α : SuperGrassmannianProjectorEnvelope.covectorVacuumSheet K)
    [Fintype ι] [Fintype κ]
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i ≠ 0) (T : Matrix κ ι ℝ)
    (coarsePrior : κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (h_pair : g α.1 u.1 = chiSquaredInner ρ (petzRecoveryVec ρ T coarsePrior y) x) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (ParaKahlerGradedFockCAR.paraKahlerCreateEnd K u)
        (ParaKahlerGradedFockCAR.paraKahlerAnnihilateEnd g K α) =
      (chiSquaredInner coarsePrior y (markovCoarseGrain T x)) •
        (1 : Module.End ℝ (SuperGrassmannianProjectorEnvelope.FockExteriorEnvelope K)) := by
  rw [ParaKahlerGradedFockCAR.superBracket_create_annihilate g K u α,
    h_pair, petzRecoveryVec_chiSquared_adjoint ρ hρ T coarsePrior x y]

/-- Concrete 2-to-1 token pooling transition kernel `uniformPoolingMatrix : Matrix (Fin 1) (Fin 2) ℝ`
that sums the two fine token coordinates into a single coarse summary token. -/
def uniformPoolingMatrix : Matrix (Fin 1) (Fin 2) ℝ :=
  fun _ _ => 1

/-- Every column of `uniformPoolingMatrix` sums to `1` (column-stochastic coarse-graining). -/
theorem uniformPoolingMatrix_col_sum (i : Fin 2) :
    ∑ j : Fin 1, uniformPoolingMatrix j i = 1 := by
  rw [Fin.sum_univ_one]
  rfl

/-- Under `uniformPoolingMatrix`, the coarse-grained softmax prior on `Fin 1` evaluates to `1`. -/
theorem markovCoarseGrain_uniformPoolingMatrix_softmaxWeight
    (logits : Fin 2 → ℝ) (β : ℝ) :
    markovCoarseGrain uniformPoolingMatrix (softmaxWeight logits β) 0 = 1 := by
  dsimp [markovCoarseGrain, uniformPoolingMatrix]
  simp only [one_mul]
  exact softmaxWeight_sum_one logits β

/-- **Concrete Two-Token Pooling Petz Recovery Readout**:
When two fine tokens on `Fin 2` are pooled into a single coarse summary `y : Fin 1 → ℝ` via
`uniformPoolingMatrix`, the Boltzmann-weighted Petz recovery map `attentionPetzRecovery`
un-pools `y 0` back to fine token `i` in exact proportion to its KMS Boltzmann weight:
`attentionPetzRecovery logits β uniformPoolingMatrix y i = softmaxWeight logits β i * y 0`. -/
theorem attentionPetzRecovery_uniformPoolingMatrix_apply
    (logits : Fin 2 → ℝ) (β : ℝ) (y : Fin 1 → ℝ) (i : Fin 2) :
    attentionPetzRecovery logits β uniformPoolingMatrix y i =
      softmaxWeight logits β i * y 0 := by
  dsimp [attentionPetzRecovery, petzRecoveryVec]
  rw [Fin.sum_univ_one]
  rw [markovCoarseGrain_uniformPoolingMatrix_softmaxWeight logits β]
  have hT : uniformPoolingMatrix 0 i = 1 := rfl
  rw [hT, one_mul, div_one]

/-- Concrete 4-to-2 block cluster pooling kernel `blockClusterPoolingMatrix : Matrix (Fin 2) (Fin 4) ℝ`
mapping fine tokens `{0, 1}` to coarse cluster `0` and fine tokens `{2, 3}` to coarse cluster `1`. -/
def blockClusterPoolingMatrix : Matrix (Fin 2) (Fin 4) ℝ :=
  fun j i => if (j = 0 ∧ i.val < 2) ∨ (j = 1 ∧ 2 ≤ i.val) then 1 else 0

/-- Every column of `blockClusterPoolingMatrix` sums to `1` (each of the 4 fine tokens belongs
to a unique coarse cluster). -/
theorem blockClusterPoolingMatrix_col_sum (i : Fin 4) :
    ∑ j : Fin 2, blockClusterPoolingMatrix j i = 1 := by
  rw [Fin.sum_univ_two]
  fin_cases i <;>
    (dsimp [blockClusterPoolingMatrix]; norm_num)

/-- On fine token `0` (in cluster `0`), `attentionPetzRecovery` under `blockClusterPoolingMatrix`
scales `softmaxWeight logits β 0` by the non-constant cluster-`0` marginal ratio
`y 0 / markovCoarseGrain blockClusterPoolingMatrix (softmaxWeight logits β) 0`. -/
theorem attentionPetzRecovery_blockClusterPoolingMatrix_zero
    (logits : Fin 4 → ℝ) (β : ℝ) (y : Fin 2 → ℝ) :
    attentionPetzRecovery logits β blockClusterPoolingMatrix y 0 =
      softmaxWeight logits β 0 *
        (y 0 / markovCoarseGrain blockClusterPoolingMatrix (softmaxWeight logits β) 0) := by
  dsimp [attentionPetzRecovery, petzRecoveryVec]
  rw [Fin.sum_univ_two]
  have h00 : blockClusterPoolingMatrix 0 0 = 1 := rfl
  have h10 : blockClusterPoolingMatrix 1 0 = 0 := rfl
  rw [h00, h10, one_mul, zero_mul, add_zero]

/-- On fine token `2` (in cluster `1`), `attentionPetzRecovery` under `blockClusterPoolingMatrix`
scales `softmaxWeight logits β 2` by the non-constant cluster-`1` marginal ratio
`y 1 / markovCoarseGrain blockClusterPoolingMatrix (softmaxWeight logits β) 1`. -/
theorem attentionPetzRecovery_blockClusterPoolingMatrix_two
    (logits : Fin 4 → ℝ) (β : ℝ) (y : Fin 2 → ℝ) :
    attentionPetzRecovery logits β blockClusterPoolingMatrix y 2 =
      softmaxWeight logits β 2 *
        (y 1 / markovCoarseGrain blockClusterPoolingMatrix (softmaxWeight logits β) 1) := by
  dsimp [attentionPetzRecovery, petzRecoveryVec]
  rw [Fin.sum_univ_two]
  have h02 : blockClusterPoolingMatrix 0 2 = 0 := rfl
  have h12 : blockClusterPoolingMatrix 1 2 = 1 := rfl
  rw [h02, h12, zero_mul, one_mul, zero_add]

end InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge

end
