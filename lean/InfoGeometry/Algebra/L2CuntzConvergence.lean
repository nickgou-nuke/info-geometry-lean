import Mathlib
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
  finite_cuntz_tensor_quotient_packet n

/-- Each generator in the finite Cuntz tensor quotient is an isometry. -/
theorem finite_cuntz_isometry (n : ℕ) (i : Fin n) :
    cuntzSdag n i * cuntzS n i = 1 :=
  CuntzTensorQuotient.cuntz_isometry n i

/-- Distinct finite Cuntz generators are orthogonal on the initial side. -/
theorem finite_cuntz_orthogonal {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    cuntzSdag n i * cuntzS n j = 0 :=
  CuntzTensorQuotient.cuntz_distinct_orthogonal n hij

/-! ## Analytic Convergence in a C*-algebra -/

/--
**ℓ² convergence of the weighted Cuntz sum.**

Hypotheses:
- A is a C*-algebra over ℝ (or ℂ).
- S : ℕ → A are isometries with orthogonal ranges.
- a : ℕ → ℝ are real coefficients.
- ha_l2 : ∑_p a_p² < ∞ (ℓ² summability).

Then the infinite series A_∞ = Σ_p a_p·S_p converges.
-/
lemma weightedCuntzSum_converges {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [CompleteSpace A]
    (S : ℕ → A)
    (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (a : ℕ → ℝ)
    (ha_l2 : Summable (λ p => (a p) ^ 2)) :
    ∃ L : A, HasSum (λ p, a p • S p) L := by
  -- OPEN OWNER DEBT: The proof requires using the Cuntz orthogonality 
  -- relation to bound finite partial sums and completeness.
  sorry

/--
**Convergence of the Cuntz Dirac operator D_β.**

  D_β = Σ_p p^{-β}·(S_p + S*_p)
-/
lemma primeDirac_converges {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [CompleteSpace A]
    (S : ℕ → A)
    (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (β : ℝ) (hβ : β > 1/2) : 
    ∃ L : A, HasSum (λ (p : Nat.Primes), (((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p))) L := by
  -- OPEN OWNER DEBT: The prime zeta function guarantees the ℓ² summability of coefficients.
  sorry

/--
**Self-adjointness of D_β.**
The limit D_β is self-adjoint.
-/
lemma primeDirac_selfAdjoint {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [StarRing A] [CStarRing A] [CompleteSpace A]
    (S : ℕ → A)
    (h_orth : ∀ p q, star (S p) * S q = if p = q then 1 else 0)
    (β : ℝ) (hβ : β > 1/2)
    (L : A) (hL : HasSum (λ (p : Nat.Primes), (((p : ℕ) : ℝ) ^ (-β)) • (S p + star (S p))) L) :
    star L = L := by
  -- OPEN OWNER DEBT: The self-adjoint subspace is closed in A.
  sorry

end InfoGeometry.Algebra.Cuntz
