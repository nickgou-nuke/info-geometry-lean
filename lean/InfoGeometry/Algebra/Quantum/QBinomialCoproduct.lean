import Mathlib.RingTheory.TensorProduct.Basic
import InfoGeometry.Algebra.Quantum.QBinomial

/-!
# Tensor realization of the q-binomial expansion

The q-binomial theorem itself is owned by `Algebra.Quantum.QBinomial`.  This
module records its direct tensor-algebra consequence for the two summands
`K ⊗ d` and `d ⊗ 1`.  It proves an algebra identity; no Hopf structure or
coproduct homomorphism is assumed.
-/

namespace InfoGeometry.Algebra.Quantum

open scoped TensorProduct BigOperators

section TensorCoproduct

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- Powers of a pure tensor in the tensor-product algebra are computed
componentwise. -/
lemma tmul_pow (x y : A) (n : ℕ) :
    (x ⊗ₜ[k] y) ^ n = x ^ n ⊗ₜ[k] y ^ n := by
  induction n with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ n ih =>
    rw [pow_succ, ih, Algebra.TensorProduct.tmul_mul_tmul,
      ← pow_succ, ← pow_succ]

/-- The two tensor summands q-commute when `d` and `K` do.  Scalars are
expressed with `Algebra.smul_def`, matching the q-binomial owner API. -/
lemma braidedTensorSummands_commute
    (K d : A) (q : k)
    (hcomm : d * K = q • (K * d)) :
    (d ⊗ₜ[k] (1 : A)) * (K ⊗ₜ[k] d) =
      algebraMap k (A ⊗[k] A) q *
        ((K ⊗ₜ[k] d) * (d ⊗ₜ[k] (1 : A))) := by
  calc
    (d ⊗ₜ[k] (1 : A)) * (K ⊗ₜ[k] d)
        = (d * K) ⊗ₜ[k] d := by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    _ = (q • (K * d)) ⊗ₜ[k] d := by rw [hcomm]
    _ = q • ((K * d) ⊗ₜ[k] d) :=
          (TensorProduct.smul_tmul' q (K * d) d).symm
    _ = algebraMap k (A ⊗[k] A) q * ((K * d) ⊗ₜ[k] d) := by
          rw [Algebra.smul_def]
    _ = algebraMap k (A ⊗[k] A) q *
          ((K ⊗ₜ[k] d) * (d ⊗ₜ[k] (1 : A))) := by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Braided coproduct power identity.  Its summand is the ordered tensor
product `K^(n-m) d^m ⊗ d^(n-m)`, as dictated by the q-commutation convention
`(d ⊗ 1)(K ⊗ d) = q (K ⊗ d)(d ⊗ 1)`. -/
theorem qBinomial_braidedCoproduct
    (K d : A) (q : k) (hcomm : d * K = q • (K * d)) (n : ℕ) :
    ((K ⊗ₜ[k] d) + (d ⊗ₜ[k] (1 : A))) ^ n =
      ∑ m ∈ Finset.range (n + 1),
        algebraMap k (A ⊗[k] A) (qBinomial q n m) *
          ((K ^ (n - m) * d ^ m) ⊗ₜ[k] d ^ (n - m)) := by
  rw [q_binomial_expansion q (K ⊗ₜ[k] d) (d ⊗ₜ[k] (1 : A))
      (braidedTensorSummands_commute K d q hcomm) n]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  rw [tmul_pow, tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

end TensorCoproduct

end InfoGeometry.Algebra.Quantum
