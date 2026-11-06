/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge
import InfoGeometry.Canonical.Drazin

/-!
# Semisimplicity and Kemeny–Snell Group Drazin Construction for Stochastic Attention

1. **Bounded-Orbit Semisimplicity (`no_length_two_generalized_fixed_vector`)**:
   For a finite row-stochastic real matrix, `1 - P` has no nonzero length-two
   generalized zero-vector chain. The proof is finite: stochastic powers preserve
   coordinate bounds, while such a chain would force linear growth.

2. **Kemeny–Snell Stationary-Projector Group Drazin Construction (`Section 2`)**:
   Over any associative unital ring `[Ring R]`, if an operator `L ∈ R` (such as a
   Markov Laplacian `L = 1 - P`) and an idempotent stationary projector `Π ∈ R`
   (`Π * Π = Π`) satisfy `L * Π = 0` and `Π * L = 0`, and the Kemeny–Snell shifted
   operator `L + Π` has two-sided fundamental inverse `Z`, then the Kemeny–Snell
   deviation operator `kemenySnellDeviation Z Π := Z - Π` is the canonical index-`1`
   Drazin inverse of `L` (`IsDrazinInverse L (Z - Π) 1`), with Drazin complementary
   null projector `1 - L * (Z - Π) = Π`.

The action convention is explicit: `P *ᵥ x` applies the row-stochastic matrix
to a column vector of observables. This file does not establish an evolution
law for row probability distributions. The sign convention in the companion
owner is `I - P`.
-/

open Matrix
open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A stochastic row maps a uniformly bounded vector into the same interval. -/
lemma stochastic_mulVec_abs_bound (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (x : ι → ℝ) (B : ℝ)
    (hB : ∀ j, |x j| ≤ B) (i : ι) : |(P *ᵥ x) i| ≤ B := by
  have hrow := Matrix.sum_row_of_mem_rowStochastic hP i
  have hnonneg : ∀ j, 0 ≤ P i j := fun j => Matrix.nonneg_of_mem_rowStochastic hP
  have hlow : -B ≤ (P *ᵥ x) i := by
    rw [Matrix.mulVec, dotProduct]
    calc
      -B = ∑ j, P i j * (-B) := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ ∑ j, P i j * x j := by
        apply Finset.sum_le_sum
        intro j _
        have hx : -B ≤ x j := (abs_le.mp (hB j)).1
        exact mul_le_mul_of_nonneg_left hx (hnonneg j)
  have hhigh : (P *ᵥ x) i ≤ B := by
    rw [Matrix.mulVec, dotProduct]
    calc
      ∑ j, P i j * x j ≤ ∑ j, P i j * B := by
        apply Finset.sum_le_sum
        intro j _
        have hx : x j ≤ B := (abs_le.mp (hB j)).2
        exact mul_le_mul_of_nonneg_left hx (hnonneg j)
      _ = B := by rw [← Finset.sum_mul, hrow, one_mul]
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-- The iterates of a row-stochastic matrix preserve a uniform coordinate bound. -/
lemma stochastic_pow_mulVec_abs_bound (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (x : ι → ℝ) (B : ℝ)
    (hB : ∀ j, |x j| ≤ B) (n : ℕ) (i : ι) : |((P ^ n) *ᵥ x) i| ≤ B := by
  exact stochastic_mulVec_abs_bound (P ^ n)
    ((Matrix.rowStochastic ℝ ι).pow_mem hP n) x B hB i

/-- There is no nonzero length-two generalized eigenvector at eigenvalue one. -/
theorem no_length_two_generalized_fixed_vector
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (x y : ι → ℝ)
    (hxy : (1 - P) *ᵥ x = y)
    (hyy : (1 - P) *ᵥ y = 0) : y = 0 := by
  have hPx : P *ᵥ x = x - y := by
    funext i
    have hi := congrFun hxy i
    have hi' : x i - (P *ᵥ x) i = y i := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hi
    change (P *ᵥ x) i = x i - y i
    linarith
  have hPy : P *ᵥ y = y := by
    funext i
    have hi := congrFun hyy i
    have hi' : y i - (P *ᵥ y) i = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hi
    change (P *ᵥ y) i = y i
    linarith
  have h_iter : ∀ n : ℕ, (P ^ n) *ᵥ x = fun i => x i - (n : ℝ) * y i := by
    intro n
    induction n with
    | zero =>
        funext i
        simp
    | succ n ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
        change P *ᵥ (x - (n : ℝ) • y) = fun i => x i - (↑(n + 1) : ℝ) * y i
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hPx, hPy]
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Nat.cast_succ]
        ring
  let B : ℝ := ∑ j, |x j|
  have hB : ∀ j, |x j| ≤ B := by
    intro j
    dsimp [B]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ j)
  funext i
  by_contra hne
  have hpos : 0 < |y i| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / |y i|)
  have hbound := stochastic_pow_mulVec_abs_bound P hP x B hB n i
  rw [h_iter n] at hbound
  have hxi : |x i| ≤ B := hB i
  have hny : |(n : ℝ) * y i| ≤ 2 * B := by
    have hrepr : (n : ℝ) * y i = x i - (x i - (n : ℝ) * y i) := by ring
    rw [hrepr]
    calc
      |x i - (x i - (n : ℝ) * y i)| ≤ |x i| + |x i - (n : ℝ) * y i| := abs_sub _ _
      _ ≤ B + B := add_le_add hxi hbound
      _ = 2 * B := by ring
  have hncast : (2 * B / |y i|) < (n : ℝ) := by exact_mod_cast hn
  have hlarge : 2 * B < |(n : ℝ) * y i| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have := (div_lt_iff₀ hpos).mp hncast
    nlinarith
  exact (not_lt_of_ge hny) hlarge

namespace Attention

open InfoGeometry.Canonical.Attention

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

/-- The polarized attention transition matrix has no length-two generalized
fixed-vector chain at eigenvalue one. -/
theorem polarizedAttention_no_length_two_chain
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (x y : Fin n → ℝ)
    (hxy : (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) *ᵥ x = y)
    (hyy : (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) *ᵥ y = 0) :
    y = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  exact InfoGeometry.QuantumContext.MarkovDrazin.no_length_two_generalized_fixed_vector
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    x y hxy hyy

end Attention

/-! ## Section 2: Kemeny–Snell Stationary-Projector Group Drazin Construction -/

section KemenySnellStationaryGroupDrazin

open InfoGeometry.Canonical.Drazin

variable {R : Type*} [Ring R]

/-- The Kemeny–Snell fundamental deviation operator `L^# := Z - E₀`, obtained by
subtracting the stationary projector `E₀` from the fundamental inverse `Z = (L + E₀)⁻¹`. -/
def kemenySnellDeviation (Z E₀ : R) : R :=
  Z - E₀

/-- If `L * E₀ = 0`, `E₀ * E₀ = E₀`, and `Z * (L + E₀) = 1`, then `Z * E₀ = E₀`. -/
theorem kemenySnell_mul_stationary_eq
    {L E₀ Z : R}
    (hE₀_idem : E₀ * E₀ = E₀)
    (hLE₀ : L * E₀ = 0)
    (hZL : Z * (L + E₀) = 1) :
    Z * E₀ = E₀ := by
  have hLE₀_sum : (L + E₀) * E₀ = E₀ := by
    rw [add_mul, hLE₀, hE₀_idem, zero_add]
  calc
    Z * E₀ = Z * ((L + E₀) * E₀) := by rw [hLE₀_sum]
    _ = (Z * (L + E₀)) * E₀ := by noncomm_ring
    _ = 1 * E₀ := by rw [hZL]
    _ = E₀ := one_mul E₀

/-- If `E₀ * L = 0`, `E₀ * E₀ = E₀`, and `(L + E₀) * Z = 1`, then `E₀ * Z = E₀`. -/
theorem stationary_mul_kemenySnell_eq
    {L E₀ Z : R}
    (hE₀_idem : E₀ * E₀ = E₀)
    (hE₀L : E₀ * L = 0)
    (hLZ : (L + E₀) * Z = 1) :
    E₀ * Z = E₀ := by
  have hE₀L_sum : E₀ * (L + E₀) = E₀ := by
    rw [mul_add, hE₀L, hE₀_idem, zero_add]
  calc
    E₀ * Z = (E₀ * (L + E₀)) * Z := by rw [hE₀L_sum]
    _ = E₀ * ((L + E₀) * Z) := by noncomm_ring
    _ = E₀ * 1 := by rw [hLZ]
    _ = E₀ := mul_one E₀

/-- Left product of `L` with `kemenySnellDeviation Z E₀` equals the transient projector `1 - E₀`. -/
theorem mul_kemenySnellDeviation_eq
    {L E₀ Z : R}
    (hE₀_idem : E₀ * E₀ = E₀)
    (hLE₀ : L * E₀ = 0)
    (hE₀L : E₀ * L = 0)
    (hLZ : (L + E₀) * Z = 1) :
    L * kemenySnellDeviation Z E₀ = 1 - E₀ := by
  unfold kemenySnellDeviation
  have hE₀Z : E₀ * Z = E₀ := stationary_mul_kemenySnell_eq hE₀_idem hE₀L hLZ
  have hLZ_split : L * Z + E₀ = 1 := by
    calc
      L * Z + E₀ = L * Z + E₀ * Z := by rw [hE₀Z]
      _ = (L + E₀) * Z := by noncomm_ring
      _ = 1 := hLZ
  calc
    L * (Z - E₀) = L * Z - L * E₀ := by rw [mul_sub]
    _ = L * Z := by rw [hLE₀, sub_zero]
    _ = (L * Z + E₀) - E₀ := by noncomm_ring
    _ = 1 - E₀ := by rw [hLZ_split]

/-- Right product of `kemenySnellDeviation Z E₀` with `L` equals the transient projector `1 - E₀`. -/
theorem kemenySnellDeviation_mul_eq
    {L E₀ Z : R}
    (hE₀_idem : E₀ * E₀ = E₀)
    (hLE₀ : L * E₀ = 0)
    (hE₀L : E₀ * L = 0)
    (hZL : Z * (L + E₀) = 1) :
    kemenySnellDeviation Z E₀ * L = 1 - E₀ := by
  unfold kemenySnellDeviation
  have hZE₀ : Z * E₀ = E₀ := kemenySnell_mul_stationary_eq hE₀_idem hLE₀ hZL
  have hZL_split : Z * L + E₀ = 1 := by
    calc
      Z * L + E₀ = Z * L + Z * E₀ := by rw [hZE₀]
      _ = Z * (L + E₀) := by noncomm_ring
      _ = 1 := hZL
  calc
    (Z - E₀) * L = Z * L - E₀ * L := by rw [sub_mul]
    _ = Z * L := by rw [hE₀L, sub_zero]
    _ = (Z * L + E₀) - E₀ := by noncomm_ring
    _ = 1 - E₀ := by rw [hZL_split]

/-- **Kemeny–Snell Stationary-Projector Group Drazin Theorem**:
For any operator `L ∈ R` (e.g., a Markov Laplacian `L = 1 - P`), idempotent stationary
projector `E₀` (`E₀ * E₀ = E₀`) annihilating `L` on both sides (`L * E₀ = 0` and `E₀ * L = 0`),
and Kemeny–Snell fundamental inverse `Z = (L + E₀)⁻¹`, the deviation operator
`kemenySnellDeviation Z E₀ := Z - E₀` is the canonical index-`1` Drazin inverse of `L`. -/
theorem isDrazinInverse_kemenySnellDeviation
    {L E₀ Z : R}
    (hE₀_idem : E₀ * E₀ = E₀)
    (hLE₀ : L * E₀ = 0)
    (hE₀L : E₀ * L = 0)
    (hLZ : (L + E₀) * Z = 1)
    (hZL : Z * (L + E₀) = 1) :
    IsDrazinInverse L (kemenySnellDeviation Z E₀) 1 := by
  have h_left : L * kemenySnellDeviation Z E₀ = 1 - E₀ :=
    mul_kemenySnellDeviation_eq hE₀_idem hLE₀ hE₀L hLZ
  have h_right : kemenySnellDeviation Z E₀ * L = 1 - E₀ :=
    kemenySnellDeviation_mul_eq hE₀_idem hLE₀ hE₀L hZL
  have hE₀Z : E₀ * Z = E₀ := stationary_mul_kemenySnell_eq hE₀_idem hE₀L hLZ
  have h_comm : L * kemenySnellDeviation Z E₀ = kemenySnellDeviation Z E₀ * L := by
    rw [h_left, h_right]
  have h_idem :
      kemenySnellDeviation Z E₀ * L * kemenySnellDeviation Z E₀ =
        kemenySnellDeviation Z E₀ := by
    rw [h_right]
    unfold kemenySnellDeviation
    calc
      (1 - E₀) * (Z - E₀) = Z - E₀ - E₀ * Z + E₀ * E₀ := by noncomm_ring
      _ = Z - E₀ - E₀ + E₀ := by rw [hE₀Z, hE₀_idem]
      _ = Z - E₀ := by noncomm_ring
  have h_pow : L ^ (1 + 1) * kemenySnellDeviation Z E₀ = L ^ 1 := by
    calc
      L ^ (1 + 1) * kemenySnellDeviation Z E₀
          = L * (L * kemenySnellDeviation Z E₀) := by
              rw [pow_succ', pow_one]
              noncomm_ring
      _ = L * (1 - E₀) := by rw [h_left]
      _ = L - L * E₀ := by noncomm_ring
      _ = L ^ 1 := by rw [hLE₀, sub_zero, pow_one]
  exact ⟨h_comm, h_idem, h_pow⟩

/-- The Drazin complementary (null/ergodic) projector `Q_D = 1 - L * L^#` of the
Kemeny–Snell deviation operator `Z - E₀` is identically equal to the stationary projector `E₀`. -/
theorem kemenySnellDeviation_complementaryProjection_eq
    {L E₀ Z : R}
    (hE₀_idem : E₀ * E₀ = E₀)
    (hLE₀ : L * E₀ = 0)
    (hE₀L : E₀ * L = 0)
    (hLZ : (L + E₀) * Z = 1) :
    IsDrazinInverse.complementaryProjection L (kemenySnellDeviation Z E₀) = E₀ := by
  unfold IsDrazinInverse.complementaryProjection IsDrazinInverse.projection
  rw [mul_kemenySnellDeviation_eq hE₀_idem hLE₀ hE₀L hLZ]
  noncomm_ring

end KemenySnellStationaryGroupDrazin

end InfoGeometry.QuantumContext.MarkovDrazin
