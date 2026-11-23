/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Star.Basic
import InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset


/-!
# InfoGeometry.Canonical.SouriauMetriplecticAttentionCasimirPoset

Provides a zero‑`sorry` Lean 4 formalisation of a metric‑Poisson (metriplectic)
framework for a non‑commutative attention model.  The development works over an
arbitrary ring `B` equipped with a cyclic additive functional `τ : B →+ R`.
All theorems are proved without auxiliary structures. The base assumptions are
`[Ring B]`, `[CommRing R]` and cyclicity of `τ`; the positivity results (Theorems 4,
6, 7) additionally assume `[StarRing B]`, `[PartialOrder R]`, and that `τ` is positive
(`0 ≤ τ (Y⋆ Y)`) and faithful (`τ (Y⋆ Y) = 0 → Y = 0`).

Main results:
1. A Fisher‑Rao replicator flow on the 3‑simplex preserves normalisation.
2. Lie‑Poisson antisymmetry, Morrison‑bracket symmetry, Casimir degeneracies, and
   first‑order conservation of `τ W`, `τ W²`, `τ W³` under the Brockett‑Souriau flow.
3. For an idempotent `P`: `[P, Φ] = J`, `J Φ = -Φ J`, `V = Φ²`, `Σ² = V²`, where
   `J = [P, X]`, `Φ = [P, [P, X]]` (built on the Peirce owner
   `SouriauMetriplecticParabolicWeitzenbockPoset`).
4. For self‑adjoint `P, X`: `V = J⋆ J`, `0 ≤ τ V`, and `τ V = 0 ↔ [P, X] = 0`.
5. First‑order conservation of `τ (W ^ k)` for every `k : ℕ` (`powDeriv`).
6. Metriplectic second law: `0 ≤ ⟨⟨F, F⟩⟩_H`, with equality iff `[H, F] = 0`;
   bundled with the other bracket axioms in `metriplectic_axioms`.
7. Lyapunov theorem: if `[Ω, H] = 0`, then `τ (dW · H) = τ ([W, H]⋆ [W, H]) ≥ 0`.

All statements are algebraic (first‑order / pointwise); no time‑dependent ODE
solution is constructed here. Matrix instances live in
`SouriauMetriplecticAttentionMatrixInstance`. No `sorry`, `admit`, or custom axioms.
-/



namespace SouriauMetriplecticAttentionCasimirPoset

universe u v
variable {B : Type u} [Ring B]
variable {R : Type v} [CommRing R]

/-- Commute (commutator) of two elements in a ring. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Lie–Poisson (Souriau) bracket `{F, G}_LP(ρ) = τ (ρ * [F, G])`. -/
def liePoissonBracket (τ : B →+ R) (ρ F G : B) : R :=
  τ (ρ * comm F G)

/-- Morrison‑metric bracket `<<F, G>>_H = - τ ([H, F] * [H, G])`. -/
def morrisonMetricBracket (τ : B →+ R) (H F G : B) : R :=
  - τ (comm H F * comm H G)

/-- Isospectral metriplectic flow for a weight matrix `W`. -/
def brockettSouriauWeightFlow (Ω H W : B) : B :=
  comm Ω W + comm W (comm W H)

-- Helper lemmas -----------------------------------------------------------------

/-- If `τ` is cyclic, every commutator has zero trace. -/
lemma trace_comm_eq_zero (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (X Y : B) :
    τ (comm X Y) = 0 := by
  dsimp [comm]
  rw [map_sub, h_cyc X Y, sub_self]

@[simp] lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

-- =============================================================================
-- 1. Fisher‑Rao covariant replicator flow on the attention simplex
-- =============================================================================

/--
**Theorem 1** – Covariant replicator‑Softmax flow preserves the simplex constraint.
-/
theorem attention_simplex_replicator_normalization
    (γ a1 a2 a3 e1 e2 e3 : R) (h_norm : a1 + a2 + a3 = 1) :
    let e_bar := a1 * e1 + a2 * e2 + a3 * e3
    let da1 := γ * (e1 - e_bar) * a1
    let da2 := γ * (e2 - e_bar) * a2
    let da3 := γ * (e3 - e_bar) * a3
    da1 + da2 + da3 = 0 := by
  dsimp
  calc
    γ * (e1 - (a1 * e1 + a2 * e2 + a3 * e3)) * a1 +
        γ * (e2 - (a1 * e1 + a2 * e2 + a3 * e3)) * a2 +
        γ * (e3 - (a1 * e1 + a2 * e2 + a3 * e3)) * a3
        = γ * (a1 * e1 + a2 * e2 + a3 * e3) * (1 - (a1 + a2 + a3)) := by ring
    _ = 0 := by rw [h_norm, sub_self, mul_zero]

-- =============================================================================
-- 2. Casimir invariants and metriplectic degeneracy
-- =============================================================================

/--
**Theorem 2** – Lie‑Poisson antisymmetry, metric symmetry, Casimir degeneracy, and
conservation of spectral moments under the Brockett‑Souriau flow.
-/
theorem souriau_casimir_invariants_and_metriplectic_degeneracy
    (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (ρ H Ω W F G S : B) (hS : comm ρ S = 0) :
    let dW := brockettSouriauWeightFlow Ω H W
    -- 1. Duality of brackets
    liePoissonBracket τ ρ F G = - liePoissonBracket τ ρ G F ∧
    morrisonMetricBracket τ H F G = morrisonMetricBracket τ H G F ∧
    morrisonMetricBracket τ H F G = τ (F * comm H (comm H G)) ∧
    -- 2. First Casimir condition (centralizer of ρ)
    liePoissonBracket τ ρ F S = 0 ∧
    liePoissonBracket τ ρ F ρ = 0 ∧
    liePoissonBracket τ ρ F (ρ * ρ) = 0 ∧
    -- 3. Second Casimir condition (energy blind to dissipation)
    morrisonMetricBracket τ H F H = 0 ∧
    -- 4. Conservation of spectral moments for W
    τ dW = 0 ∧
    τ (dW * W + W * dW) = 0 ∧
    τ (dW * W * W + W * dW * W + W * W * dW) = 0 := by
  -- auxiliary: generic Casimir from centralizer
  have h_casimir_gen : ∀ U : B, comm ρ U = 0 → liePoissonBracket τ ρ F U = 0 := by
    intro U hU
    dsimp [liePoissonBracket]
    have h_id : ρ * comm F U = comm (ρ * F) U - comm ρ U * F := by
      dsimp [comm]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    rw [h_id, hU, zero_mul, sub_zero]
    exact trace_comm_eq_zero τ h_cyc (ρ * F) U
  -- rewrite dW as a single commutator
  have h_dW_comm : brockettSouriauWeightFlow Ω H W = comm (Ω - comm W H) W := by
    dsimp [brockettSouriauWeightFlow, comm]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  refine ⟨?_, ?_, ?_, h_casimir_gen S hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- antisymmetry of Lie‑Poisson
    dsimp [liePoissonBracket, comm]
    have h_neg : ρ * (F * G - G * F) = - (ρ * (G * F - F * G)) := by
      simp only [mul_sub]; abel
    rw [h_neg, map_neg]
  · -- symmetry of metric bracket
    dsimp [morrisonMetricBracket]
    rw [h_cyc (comm H F) (comm H G)]
  · -- metric bracket expressed via double commutator
    dsimp [morrisonMetricBracket]
    have h_ibp : F * comm H (comm H G) = comm H (F * comm H G) - comm H F * comm H G := by
      dsimp [comm]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    rw [h_ibp, map_sub, trace_comm_eq_zero τ h_cyc H (F * comm H G), zero_sub]
  · -- first Casimir for ρ
    apply h_casimir_gen ρ
    dsimp [comm]; abel
  · -- first Casimir for ρ²
    apply h_casimir_gen (ρ * ρ)
    dsimp [comm]; simp only [mul_assoc]; abel
  · -- metric bracket with H vanishes
    dsimp [morrisonMetricBracket, comm]
    rw [sub_self, mul_zero, map_zero, neg_zero]
  · -- trace of dW vanishes
    rw [h_dW_comm]
    exact trace_comm_eq_zero τ h_cyc (Ω - comm W H) W
  · -- trace of quadratic Casimir vanishes
    rw [h_dW_comm]
    set K := Ω - comm W H
    have h_sq : comm K W * W + W * comm K W = comm K (W * W) := by
      dsimp [comm]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    rw [h_sq]
    exact trace_comm_eq_zero τ h_cyc K (W * W)
  · -- trace of cubic Casimir vanishes
    rw [h_dW_comm]
    set K := Ω - comm W H
    have h_cube : comm K W * W * W + W * comm K W * W + W * W * comm K W = comm K (W * W * W) := by
      dsimp [comm]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    rw [h_cube]
    exact trace_comm_eq_zero τ h_cyc K (W * W * W)

-- =============================================================================
-- 3. Metriplectic ontology tensor for a projection barrier
-- =============================================================================

/-- `J = [P, X]`, the first Peirce component of a projection barrier. -/
def J_barrier     (P X : B) : B := comm P X

/-- `Φ = [P, [P, X]]`, the second-order Peirce component. -/
def Phi_barrier   (P X : B) : B := comm P (comm P X)

/-- The quadratic potential `-J²`; positivity needs a star structure. -/
def V_barrier     (P X : B) : B := - (J_barrier P X * J_barrier P X)

/-- The ordered spin term `J Φ` associated with the barrier. -/
def Sigma_barrier (P X : B) : B := J_barrier P X * Phi_barrier P X

open InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset
  (Q_pos Q_neg V_P Sigma_P corner_strict_nilpotency metriplectic_lindblad_modular_synthesis)

/-- The barrier potential `V = -J²` is the sum of the two Peirce core blocks
`V_P = Q₊Q₋` and `Σ_P = Q₋Q₊` of the Weitzenböck owner. -/
lemma V_barrier_eq_core {P : B} (hP : P * P = P) (X : B) :
    V_barrier P X = V_P P X + Sigma_P P X := by
  obtain ⟨hpp, hnn⟩ := corner_strict_nilpotency hP X X
  have hJ : J_barrier P X = Q_pos P X - Q_neg P X :=
    (metriplectic_lindblad_modular_synthesis hP X X).1
  simp only [V_barrier, hJ, V_P, Sigma_P, mul_sub, sub_mul, hpp, hnn]
  abel

/--
**Theorem 3** – Metriplectic ontology tensor for a projection barrier.

For an idempotent `P` (`P * P = P`) in an arbitrary (noncommutative) ring, with
`J = [P, X]` and `Φ = [P, [P, X]]`:
1. `[P, Φ] = J` (so `ad_P³ = ad_P` on `X`);
2. `J` and `Φ` anticommute: `J Φ = - Φ J`;
3. `V = -J² = Φ²`;
4. `Σ² = V²` where `Σ = J Φ`.

The proof uses the Peirce pieces `Q₊(X) = P X (1 - P)` and `Q₋(X) = (1 - P) X P`
of `SouriauMetriplecticParabolicWeitzenbockPoset`, for which `J = Q₊ - Q₋`,
`Φ = Q₊ + Q₋`, and `Q₊² = Q₋² = 0` (`corner_strict_nilpotency`).
-/
theorem metriplectic_ontology_tensor_prevents_gradient_collapse
    (P X : B) (hP : P * P = P) :
    comm P (Phi_barrier P X) = J_barrier P X ∧
    J_barrier P X * Phi_barrier P X = - (Phi_barrier P X * J_barrier P X) ∧
    V_barrier P X = Phi_barrier P X * Phi_barrier P X ∧
    Sigma_barrier P X * Sigma_barrier P X = V_barrier P X * V_barrier P X := by
  obtain ⟨haa, hcc⟩ := corner_strict_nilpotency hP X X
  have hPeirce := metriplectic_lindblad_modular_synthesis hP X X
  have hPeirceJ := metriplectic_lindblad_modular_synthesis hP (J_barrier P X) (J_barrier P X)
  have hJ : J_barrier P X = Q_pos P X - Q_neg P X := hPeirce.1
  have hΦ : Phi_barrier P X = Q_pos P X + Q_neg P X := hPeirce.2.1
  have hΦJ : Phi_barrier P (J_barrier P X) =
      Q_pos P (J_barrier P X) + Q_neg P (J_barrier P X) := hPeirceJ.2.1
  -- `[P, Φ] = [P, [P, J]]`-type identity: `Φ` is itself `[P, J]`, so apply the
  -- Peirce sum formula to `J` and note `Q₊(J) = Q₊(X)`, `Q₋(J) = -Q₋(X)`.
  have hPhiJ : comm P (Phi_barrier P X) = Phi_barrier P (J_barrier P X) := rfl
  have hQpJ : Q_pos P (J_barrier P X) = Q_pos P X := by
    simp only [Q_pos, J_barrier, comm,
      InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset.P_perp,
      mul_sub, sub_mul, mul_one, mul_assoc, hP]
    simp only [← mul_assoc, hP]
    abel
  have hQnJ : Q_neg P (J_barrier P X) = - Q_neg P X := by
    simp only [Q_neg, J_barrier, comm,
      InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset.P_perp,
      mul_sub, sub_mul, one_mul, mul_assoc, hP]
    simp only [← mul_assoc, hP]
    abel
  have hca : ∀ Z : B, Q_neg P X * (Q_neg P X * Z) = 0 := fun Z => by
    rw [← mul_assoc, hcc, zero_mul]
  have haa' : ∀ Z : B, Q_pos P X * (Q_pos P X * Z) = 0 := fun Z => by
    rw [← mul_assoc, haa, zero_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hPhiJ, hΦJ, hQpJ, hQnJ, hJ]; abel
  · rw [hΦ, hJ]
    simp only [mul_add, add_mul, mul_sub, sub_mul, haa, hcc]
    abel
  · simp only [V_barrier, hΦ, hJ, mul_add, add_mul, mul_sub, sub_mul, haa, hcc]
    abel
  · simp only [V_barrier, Sigma_barrier, hΦ, hJ, mul_add, add_mul, mul_sub, sub_mul,
      mul_neg, neg_mul, mul_assoc, haa, hcc, haa', hca, mul_zero, zero_mul]
    abel

-- =============================================================================
-- 4. Positivity of the barrier potential (no gradient collapse)
-- =============================================================================

/--
**Theorem 4** – Positivity and faithfulness of the barrier potential.

Let `B` be a star ring and `τ : B →+ R` a positive (`0 ≤ τ (Y⋆ Y)`) and faithful
(`τ (Y⋆ Y) = 0 → Y = 0`) functional into an ordered ring. For self-adjoint `P` and `X`
the commutator `J = [P, X]` is skew-adjoint, hence the barrier potential
`V = -J²` equals `J⋆ J`. Therefore `τ V ≥ 0`, and `τ V = 0` exactly when `[P, X] = 0`:
the potential vanishes only on the commutant of `P`. Idempotency of `P` is not needed;
combined with Theorem 3 (`V = Φ²`) it yields `0 ≤ τ (Φ²)` for projections.
-/
theorem barrier_potential_nonneg_and_faithful
    [StarRing B] [PartialOrder R] (τ : B →+ R)
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    (P X : B) (hPs : star P = P) (hXs : star X = X) :
    star (J_barrier P X) = - J_barrier P X ∧
    V_barrier P X = star (J_barrier P X) * J_barrier P X ∧
    0 ≤ τ (V_barrier P X) ∧
    (τ (V_barrier P X) = 0 ↔ comm P X = 0) := by
  have hstar : star (J_barrier P X) = - J_barrier P X := by
    simp only [J_barrier, comm, star_sub, star_mul, hPs, hXs, neg_sub]
  have hV : V_barrier P X = star (J_barrier P X) * J_barrier P X := by
    rw [hstar, neg_mul, V_barrier]
  refine ⟨hstar, hV, ?_, ?_⟩
  · rw [hV]; exact hpos _
  · constructor
    · intro h
      exact hfaith (J_barrier P X) (hV ▸ h)
    · intro h
      have hJ0 : J_barrier P X = 0 := h
      rw [hV, hJ0, mul_zero, map_zero]

-- =============================================================================
-- 5. All-order moment conservation, metriplectic second law, Lyapunov function
-- =============================================================================

/-- Directional derivative of `W ^ k` along `D` (Leibniz rule):
`∂_D (W⁰) = 0`, `∂_D (W^(k+1)) = D W^k + W ∂_D (W^k)`. -/
def powDeriv (W D : B) : ℕ → B
  | 0 => 0
  | k + 1 => D * W ^ k + W * powDeriv W D k

/-- Along an inner derivation `D = [K, W]`, the derivative of `W ^ k` is `[K, W ^ k]`. -/
lemma powDeriv_comm (K W : B) (k : ℕ) : powDeriv W (comm K W) k = comm K (W ^ k) := by
  induction k with
  | zero => simp [powDeriv, comm]
  | succ k ih =>
    rw [powDeriv, ih, pow_succ']
    simp only [comm, mul_sub, sub_mul, mul_assoc]
    abel

/-- The Brockett–Souriau flow is the inner derivation `[Ω - [W, H], W]`. -/
lemma brockettSouriauWeightFlow_eq_comm (Ω H W : B) :
    brockettSouriauWeightFlow Ω H W = comm (Ω - comm W H) W := by
  dsimp [brockettSouriauWeightFlow, comm]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- With zero energy the flow is the Hamiltonian inner derivation `[Ω, W]`. -/
lemma brockettSouriauWeightFlow_zero_energy (Ω W : B) :
    brockettSouriauWeightFlow Ω 0 W = comm Ω W := by
  simp [brockettSouriauWeightFlow, comm]

/--
**Theorem 5** – Conservation of all spectral moments: for every `k : ℕ`, the
first-order variation of `τ (W ^ k)` along the Brockett–Souriau flow vanishes.
(Theorem 2 covers `k = 1, 2, 3`.)
-/
theorem brockett_souriau_all_moments_conserved
    (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (Ω H W : B) (k : ℕ) :
    τ (powDeriv W (brockettSouriauWeightFlow Ω H W) k) = 0 := by
  rw [brockettSouriauWeightFlow_eq_comm, powDeriv_comm]
  exact trace_comm_eq_zero τ h_cyc _ _

/-- For self-adjoint `A, C` the commutator is skew-adjoint, so `-[A, C]² = [A, C]⋆ [A, C]`. -/
lemma neg_comm_sq_eq_star_mul_self [StarRing B] {A C : B}
    (hA : star A = A) (hC : star C = C) :
    -(comm A C * comm A C) = star (comm A C) * comm A C := by
  have h : star (comm A C) = - comm A C := by
    simp only [comm, star_sub, star_mul, hA, hC, neg_sub]
  rw [h, neg_mul]

/-- Positivity and faithfulness of `τ (-[A, C]²)` for self-adjoint `A, C`. -/
lemma trace_neg_comm_sq_nonneg_and_faithful [StarRing B] [PartialOrder R] (τ : B →+ R)
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    {A C : B} (hA : star A = A) (hC : star C = C) :
    0 ≤ τ (-(comm A C * comm A C)) ∧ (τ (-(comm A C * comm A C)) = 0 ↔ comm A C = 0) := by
  rw [neg_comm_sq_eq_star_mul_self hA hC]
  refine ⟨hpos _, fun h => hfaith _ h, fun h => ?_⟩
  rw [h, mul_zero, map_zero]

/--
**Theorem 6** – Metriplectic second law: for self-adjoint `H, F` and a positive faithful
`τ`, the Morrison metric bracket is positive semidefinite on the diagonal,
`⟨⟨F, F⟩⟩_H = τ ([H, F]⋆ [H, F]) ≥ 0`, vanishing exactly when `[H, F] = 0`.
-/
theorem morrison_metric_bracket_nonneg_and_faithful [StarRing B] [PartialOrder R]
    (τ : B →+ R)
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    {H F : B} (hH : star H = H) (hF : star F = F) :
    0 ≤ morrisonMetricBracket τ H F F ∧
      (morrisonMetricBracket τ H F F = 0 ↔ comm H F = 0) := by
  have h : morrisonMetricBracket τ H F F = τ (-(comm H F * comm H F)) := by
    rw [morrisonMetricBracket, map_neg]
  rw [h]
  exact trace_neg_comm_sq_nonneg_and_faithful τ hpos hfaith hH hF

/--
**Metriplectic axioms** – bundled: antisymmetry of the Lie–Poisson bracket, symmetry and
positive semidefiniteness of the Morrison metric bracket, the Casimir degeneracy of the
Lie–Poisson bracket on the centralizer of `ρ`, and the energy degeneracy `⟨⟨F, H⟩⟩_H = 0`.
-/
theorem metriplectic_axioms [StarRing B] [PartialOrder R] (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    (ρ H F G S : B) (hH : star H = H) (hF : star F = F) (hS : comm ρ S = 0) :
    liePoissonBracket τ ρ F G = - liePoissonBracket τ ρ G F ∧
    morrisonMetricBracket τ H F G = morrisonMetricBracket τ H G F ∧
    0 ≤ morrisonMetricBracket τ H F F ∧
    liePoissonBracket τ ρ F S = 0 ∧
    morrisonMetricBracket τ H F H = 0 := by
  have h2 := souriau_casimir_invariants_and_metriplectic_degeneracy τ h_cyc ρ H 0 0 F G S hS
  exact ⟨h2.1, h2.2.1, (morrison_metric_bracket_nonneg_and_faithful τ hpos hfaith hH hF).1,
    h2.2.2.2.1, h2.2.2.2.2.2.2.1⟩

/-- Rate identity behind Theorem 7 (no star structure needed): if `[Ω, H] = 0` then
`τ (dW · H) = τ (-[W, H]²)` along `dW = brockettSouriauWeightFlow Ω H W`. -/
lemma brockett_souriau_rate_eq (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (Ω H W : B) (hΩH : comm Ω H = 0) :
    τ (brockettSouriauWeightFlow Ω H W * H) = τ (-(comm W H * comm W H)) := by
  have hHΩ : H * Ω = Ω * H := by
    have h := hΩH
    unfold comm at h
    exact (sub_eq_zero.mp h).symm
  have h1 : τ (comm Ω W * H) = 0 := by
    simp only [comm, sub_mul, map_sub, mul_assoc]
    rw [h_cyc Ω (W * H), mul_assoc, hHΩ, sub_self]
  have h2 : ∀ K : B, τ (comm W K * H) = τ (K * (H * W)) - τ (K * (W * H)) := by
    intro K
    simp only [comm, sub_mul, map_sub, mul_assoc]
    rw [h_cyc W (K * H), mul_assoc]
  rw [brockettSouriauWeightFlow, add_mul, map_add, h1, zero_add, h2]
  simp only [comm, mul_sub, sub_mul, map_sub, map_neg, mul_assoc]
  abel

/-- Nonnegativity of the Lyapunov rate (positivity of `τ` only; faithfulness not needed). -/
lemma brockett_souriau_rate_nonneg [StarRing B] [PartialOrder R] (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (Ω H W : B) (hΩH : comm Ω H = 0) (hH : star H = H) (hW : star W = W) :
    0 ≤ τ (brockettSouriauWeightFlow Ω H W * H) := by
  rw [brockett_souriau_rate_eq τ h_cyc Ω H W hΩH, neg_comm_sq_eq_star_mul_self hW hH]
  exact hpos _

/-- Star-equivariance of the Brockett–Souriau vector field: for skew-adjoint `Ω` and
self-adjoint `H`, `(dW)⋆ = dW⋆`, i.e. `star ∘ F = F ∘ star`. -/
lemma brockettSouriauWeightFlow_star [StarRing B] {Ω H : B}
    (hΩ : star Ω = -Ω) (hH : star H = H) (W : B) :
    star (brockettSouriauWeightFlow Ω H W) = brockettSouriauWeightFlow Ω H (star W) := by
  simp only [brockettSouriauWeightFlow, comm, star_add, star_sub, star_mul, hΩ, hH]
  noncomm_ring

/-- The Brockett–Souriau vector field is tangent to the self-adjoint operators: if `Ω` is
skew-adjoint and `H, W` are self-adjoint, then `dW` is self-adjoint. -/
lemma brockettSouriauWeightFlow_star_self [StarRing B] {Ω H W : B}
    (hΩ : star Ω = -Ω) (hH : star H = H) (hW : star W = W) :
    star (brockettSouriauWeightFlow Ω H W) = brockettSouriauWeightFlow Ω H W := by
  simp only [brockettSouriauWeightFlow, comm, star_add, star_sub, star_mul, hΩ, hH, hW]
  noncomm_ring

/--
**Theorem 7** – Lyapunov (H-)theorem for the Brockett–Souriau flow.
If the symplectic generator `Ω` commutes with the energy `H`, and `W, H` are self-adjoint,
then the first-order rate of `τ (W H)` along `dW = [Ω, W] + [W, [W, H]]` is
`τ (dW H) = τ (-[W, H]²) = τ ([W, H]⋆ [W, H]) ≥ 0`, vanishing exactly on the commutant
`[W, H] = 0`. The symplectic part `[Ω, W]` contributes nothing.
-/
theorem brockett_souriau_lyapunov [StarRing B] [PartialOrder R] (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    (Ω H W : B) (hΩH : comm Ω H = 0) (hH : star H = H) (hW : star W = W) :
    τ (brockettSouriauWeightFlow Ω H W * H) = τ (-(comm W H * comm W H)) ∧
    0 ≤ τ (brockettSouriauWeightFlow Ω H W * H) ∧
    (τ (brockettSouriauWeightFlow Ω H W * H) = 0 ↔ comm W H = 0) := by
  have hrate := brockett_souriau_rate_eq τ h_cyc Ω H W hΩH
  rw [hrate]
  exact ⟨rfl, trace_neg_comm_sq_nonneg_and_faithful τ hpos hfaith hW hH⟩

end SouriauMetriplecticAttentionCasimirPoset
