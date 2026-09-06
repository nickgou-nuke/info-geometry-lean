import Mathlib.Tactic
import Mathlib.NumberTheory.SumPrimeReciprocals
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# O_∞ Dirac Operator — ℓ² Convergence Theorem

This file combines the algebraic Cuntz relations with the analytic convergence 
theory of the Boltzmann-regularized Dirac operator.

For the prime-indexed Cuntz isometries S_p with orthogonal ranges,
the Boltzmann-regularized Dirac operator

  D_β = Σ_p p^{-β} · (S_p + S*_p)

converges in norm for β > 1/2. The proof uses ℓ² summability
and Cuntz orthogonality.
-/

open scoped BigOperators
open scoped Topology

namespace InfoGeometry.Algebra.Cuntz

open InfoGeometry.Algebra.CuntzTensorQuotient

/-! ## Prime ℓ² summability -/

/--
For `β > 1/2`, the prime-indexed coefficients `p^{-β}` are square-summable:
`∑_{p prime} p^{-2β}` converges.  This is exactly mathlib's prime zeta
summability theorem `Nat.Primes.summable_rpow` with exponent `-2β < -1`.
-/
lemma prime_l2_summable {β : ℝ} (hβ : β > 1/2) :
    Summable (λ (p : Nat.Primes) => (((p : ℕ) : ℝ) ^ (-2 * β))) := by
  have hr : (-2 * β : ℝ) < (-1 : ℝ) := by linarith
  exact (Nat.Primes.summable_rpow (r := -2 * β)).mpr hr

/-! ## Tensor-algebra quotient Cuntz facts -/

/--
The finite algebraic Cuntz quotient is a tensor-algebra quotient satisfying
`Sᵢ†Sⱼ = δᵢⱼ` and `Σᵢ SᵢSᵢ† = 1`.
-/
theorem finite_cuntz_tensor_quotient_relations (n : ℕ) :
    (∀ i j : Fin n, cuntzSdag n i * cuntzS n j = if i = j then 1 else 0) ∧
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 :=
  ⟨CuntzTensorQuotient.cuntz_orthogonality n,
    CuntzTensorQuotient.cuntz_ranges_sum_one n⟩

/-- Each generator in the finite Cuntz tensor quotient is an isometry. -/
theorem finite_cuntz_isometry (n : ℕ) (i : Fin n) :
    cuntzSdag n i * cuntzS n i = 1 :=
  CuntzTensorQuotient.cuntz_isometry n i

/-- Distinct finite Cuntz generators are orthogonal on the initial side. -/
theorem finite_cuntz_orthogonal {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    cuntzSdag n i * cuntzS n j = 0 :=
  CuntzTensorQuotient.cuntz_distinct_orthogonal n hij

/-! ## Analytic Convergence in a C*-algebra -/

lemma norm_sum_cuntz_aux {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [StarModule ℝ A]
    (S : ℕ → A) (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    star (∑ p ∈ s, a p • S p) * (∑ p ∈ s, a p • S p) = ∑ p ∈ s, (a p)^2 • (1 : A) := by
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have H : ∀ p ∈ s, ∀ q ∈ s, star (a p • S p) * (a q • S q) = if p = q then (a p)^2 • (1 : A) else 0 := by
    intro p _ q _
    rw [star_smul, star_trivial, smul_mul_smul, h_orth]
    split_ifs with h
    · subst h; rw [sq]
    · exact smul_zero _
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · rw [H p hp p hp, if_pos rfl]
  · intro q hq hneq
    rw [H p hp q hq]
    exact if_neg (Ne.symm hneq)
  · intro hp_not
    exact (hp_not hp).elim

lemma norm_sum_cuntz {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [StarModule ℝ A]
    (S : ℕ → A) (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ p ∈ s, a p • S p‖^2 = ∑ p ∈ s, (a p)^2 := by
  have h1 := CStarRing.norm_star_mul_self (x := ∑ p ∈ s, a p • S p)
  rw [← sq] at h1
  rw [← h1]
  rw [norm_sum_cuntz_aux S h_orth a s]
  rw [← Finset.sum_smul]
  have h2 : 0 ≤ ∑ p ∈ s, (a p)^2 := Finset.sum_nonneg (fun p _ => sq_nonneg (a p))
  rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg h2]

/--
**ℓ² convergence of the weighted Cuntz sum.**

Hypotheses:
- A is a C*-algebra over ℝ (or ℂ).
- S : ℕ → A are isometries with orthogonal ranges.
- a : ℕ → ℝ are real coefficients.
- ha_l2 : ∑_p a_p² < ∞ (ℓ² summability).

Then the infinite series A_∞ = Σ_p a_p·S_p converges.
-/
lemma weightedCuntzSum_converges {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [CompleteSpace A] [StarModule ℝ A]
    (S : ℕ → A)
    (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (a : ℕ → ℝ)
    (ha_l2 : Summable (λ p => (a p) ^ 2)) :
    ∃ L : A, HasSum (λ p ↦ a p • S p) L := by
  have H : Summable (λ p ↦ a p • S p) := by
    rw [summable_iff_vanishing_norm]
    intro ε hε
    have hε2 : 0 < ε^2 := sq_pos_of_pos hε
    have h_l2_vanish := summable_iff_vanishing_norm.mp ha_l2 (ε^2) hε2
    rcases h_l2_vanish with ⟨s, hs⟩
    use s
    intro t ht
    have h_t := hs t ht
    have ht_nonneg : 0 ≤ ∑ p ∈ t, (a p)^2 := Finset.sum_nonneg (fun p _ => sq_nonneg (a p))
    rw [Real.norm_eq_abs, abs_of_nonneg ht_nonneg] at h_t
    have h_norm_sq := norm_sum_cuntz S h_orth a t
    have h_lt : ‖∑ p ∈ t, a p • S p‖^2 < ε^2 := by linarith
    have h_sqrt := Real.sqrt_lt_sqrt (sq_nonneg _) h_lt
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (le_of_lt hε)] at h_sqrt
    exact h_sqrt
  exact ⟨_, H.hasSum⟩

/--
**Convergence of the Cuntz Dirac operator D_β.**

  D_β = Σ_p p^{-β}·(S_p + S*_p)
-/
lemma primeDirac_converges {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [CompleteSpace A] [StarModule ℝ A]
    (S : ℕ → A)
    (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (β : ℝ) (hβ : β > 1/2) : 
    ∃ L : A, HasSum (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p))) L := by
  have H1 : Summable (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • S p) := by
    let s : Set ℕ := setOf Nat.Prime
    let a : ℕ → ℝ := s.indicator (λ p => (p : ℝ) ^ (-β))
    have h_a_sq : (λ p => (a p) ^ 2) = s.indicator (λ p => (p : ℝ) ^ (-2 * β)) := by
      ext p
      by_cases hp : p ∈ s
      · simp [a, hp]
        have h_pow : ((((p : ℕ) : ℝ) ^ (-β)) ^ 2) = (((p : ℕ) : ℝ) ^ (-β)) ^ (2 : ℝ) := by exact Real.rpow_two _ |>.symm
        rw [h_pow]
        rw [← Real.rpow_mul (Nat.cast_nonneg p)]
        congr 1
        ring
      · simp [a, hp]
    have ha_l2 : Summable (λ p => (a p) ^ 2) := by
      rw [h_a_sq, ← summable_subtype_iff_indicator]
      exact prime_l2_summable hβ
    have h_sum := weightedCuntzSum_converges S h_orth a ha_l2
    have h_sum_ind : (λ p => a p • S p) = s.indicator (λ p => (p : ℝ) ^ (-β) • S p) := by
      ext p
      by_cases hp : p ∈ s
      · simp [a, hp]
      · simp [a, hp]
    have h_sum' : Summable (s.indicator (λ p => (p : ℝ) ^ (-β) • S p)) := by
      rw [← h_sum_ind]
      exact h_sum
    exact summable_subtype_iff_indicator.mpr h_sum'
  have H2 : Summable (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • star (S p)) := by
    have h_star : (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • star (S p)) = 
                  (λ (p : Nat.Primes) ↦ star ((((p : ℕ) : ℝ) ^ (-β)) • S p)) := by
      ext p
      have h_real_star : star ((((p : ℕ) : ℝ) ^ (-β))) = (((p : ℕ) : ℝ) ^ (-β)) := rfl
      rw [star_smul, h_real_star]
    rw [h_star]
    exact Summable.star H1
  have H3 : (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p))) =
            (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • S p + (((p : ℕ) : ℝ) ^ (-β)) • star (S p)) := by
    ext p
    rw [smul_add]
  rw [H3]
  exact ⟨_, (Summable.add H1 H2).hasSum⟩

/--
**Self-adjointness of D_β.**
The limit D_β is self-adjoint.
-/
lemma primeDirac_selfAdjoint {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [CompleteSpace A] [StarModule ℝ A]
    (S : ℕ → A)
    (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (β : ℝ) (hβ : β > 1/2)
    (L : A) (hL : HasSum (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p))) L) :
    star L = L := by
  have h_star : (λ (p : Nat.Primes) ↦ star ((((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p)))) = 
                (λ (p : Nat.Primes) ↦ (((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p))) := by
    ext p
    rw [star_smul, star_add, star_star]
    have h_real_star : star ((((p : ℕ) : ℝ) ^ (-β))) = (((p : ℕ) : ℝ) ^ (-β)) := rfl
    rw [h_real_star, add_comm]
  have hL_star := HasSum.star hL
  rw [h_star] at hL_star
  exact HasSum.unique hL_star hL

end InfoGeometry.Algebra.Cuntz
