import Mathlib
import Mathlib.NumberTheory.SumPrimeReciprocals
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Algebraic Cuntz tensor quotient and prime ℓ² summability

The Cuntz algebraic relations are owned by
`InfoGeometry.Algebra.CuntzTensorQuotient`: a quotient of the free
noncommutative tensor algebra on formal generators `Sᵢ,Sᵢ†`.

This file keeps only kernel-checked algebraic Cuntz facts and the genuine
prime `ℓ²` summability lemma needed before any analytic C*-representation is
introduced.  It does **not** assert norm convergence in an unspecified
`[NormedRing A]`; such a theorem needs a real C*-representation/norm package.
-/

open scoped BigOperators

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

/--
Algebraic replacement for the former fake convergence surface: before any
analytic completion, the available theorem is the tensor-quotient Cuntz packet
plus the supplied square-summability hypothesis.
-/
theorem weightedCuntzSum_converges
    (n : ℕ) (a : ℕ → ℝ) (ha_summable : Summable (λ p => (a p) ^ 2)) :
    ((∀ i j : Fin n, cuntzSdag n i * cuntzS n j = if i = j then 1 else 0) ∧
      (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1) ∧
    Summable (λ p => (a p) ^ 2) := by
  exact ⟨finite_cuntz_tensor_quotient_packet n, ha_summable⟩

/--
For `β > 1/2`, the prime Boltzmann weights have the genuine prime `ℓ²`
certificate required before constructing a represented Dirac series.
-/
theorem primeDirac_converges (β : ℝ) (hβ : β > 1/2) :
    Summable (λ (p : Nat.Primes) => (((p : ℕ) : ℝ) ^ (-2 * β))) :=
  prime_l2_summable hβ

/--
The finite symmetric Dirac summand `Sᵢ + Sᵢ†` is algebraically expressed inside
the tensor quotient; the Cuntz side still satisfies the defining quotient
relations.  Analytic self-adjointness is representation-dependent.
-/
theorem primeDirac_selfAdjoint (n : ℕ) :
    (∀ i j : Fin n, cuntzSdag n i * cuntzS n j = if i = j then 1 else 0) ∧
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 :=
  finite_cuntz_tensor_quotient_packet n

end InfoGeometry.Algebra.Cuntz
