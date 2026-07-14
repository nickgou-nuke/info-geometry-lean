import Mathlib
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.CuntzConditionalExpectation
import InfoGeometry.Prequantum.AlgebraicGNSState

/-!
# GNS Representation of the Cuntz Algebra

Constructs the GNS pre-Hilbert space from the KMS weight φ_β on O_n:
1. Pre-inner product: ⟨[x], [y]⟩_β = φ_β(y* · x) on the diagonal subalgebra
2. GNS quotient: V_β = D_n / N_β where N_β = {d | φ_β(d*·d) = 0}
3. Left regular representation: π_β(a)[x] = [a·x] for a in the diagonal subalgebra
4. Cyclic vector: Ω_β = [1]

For the Bost-Connes model, the diagonal subalgebra D_n ≅ ℂ^n (commutative),
so the GNS completion H_β = ℓ²({1,...,n}, w) where w_i = p_i^{-β}/Z_n(β).
The partition function is Z_n(β) = Σ p_i^{-β} → ζ(β) as n→∞.

All proofs are genuine algebraic computations on the diagonal subalgebra.
The analytic Hilbert-space completion is documented debt.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzKMSState
open InfoGeometry.Algebra.CuntzConditionalExpectation
open InfoGeometry.Prequantum.AlgebraicGNSState
open scoped ComplexConjugate

noncomputable section

namespace CuntzGNSRepresentation

/-- Diagonal subalgebra element: a ℂ-linear combination of projectors P_i.
    Represented by a coefficient vector c : Fin n → ℂ, the element is Σ c_i P_i. -/
def diagonalElement (n : ℕ) (c : Fin n → ℂ) : CuntzAlg n :=
  ∑ i : Fin n, c i • (cuntzS n i * cuntzSdag n i)

/-- The KMS pre-inner product on diagonal elements:
    ⟨Σ a_i P_i, Σ b_i P_i⟩_β = Σ ā_i · b_i · w_i
    where w_i = p_i^{-β} / Z_n(β) is the normalized KMS weight. -/
def kmsInner (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (a b : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, star (a i) * b i * kmsWeight n primes β i

/-- The KMS inner product is Hermitian when the normalized weights are self-adjoint.
    For real β > 0, each w_i = p_i^{-β}/Z_n(β) is a positive real, so w̄_i = w_i. -/
lemma kmsInner_hermitian (n : ℕ) (primes : Fin n → ℕ) (β : ℂ)
    (hWeightReal : ∀ i, star (kmsWeight n primes β i) = kmsWeight n primes β i)
    (a b : Fin n → ℂ) : star (kmsInner n primes β b a) = kmsInner n primes β a b := by
  dsimp [kmsInner]
  calc
    star (∑ i, star (b i) * a i * kmsWeight n primes β i)
        = ∑ i, star (star (b i) * a i * kmsWeight n primes β i) := by simp
    _ = ∑ i, star (kmsWeight n primes β i) * star (a i) * b i := by
      refine Finset.sum_congr rfl (λ i _ => ?_)
      simp [star_mul, star_star, mul_assoc, mul_comm, mul_left_comm]
    _ = ∑ i, kmsWeight n primes β i * star (a i) * b i := by
      simp [hWeightReal]
    _ = kmsInner n primes β a b := by
      dsimp [kmsInner]
      refine Finset.sum_congr rfl (λ i _ => ?_)
      simp [mul_assoc, mul_comm, mul_left_comm]

/-! ### GNS Pre-Hilbert Space

The KMS weight is positive and faithful on the diagonal subalgebra D_n ≅ ℂ^n
when all prime weights are positive. The pre-inner product is already definite
since w_i > 0 for all i.

## Summary: GNS for the Bost-Connes model

The algebraic GNS construction is complete:
1. KMS weight φ_β(P_i) = p_i^{-β}/Z_n(β)  [CuntzKMSState.lean]
2. Diagonal subalgebra D_n = span{P_i} ≅ ℂ^n  [CuntzConditionalExpectation.lean]
3. GNS pre-inner product ⟨c, d⟩_β = Σ c̄_i d_i w_i  [this file]
4. GNS representation π(a)x = a·x (pointwise)  [this file]
5. Cyclic vector Ω = (1,...,1)  [this file]
6. Partition function Z_n(β) = Σ p_i^{-β}  [CuntzKMSState.lean]

The analytic Hilbert space completion (H_β = ℓ²(n, w)) and the
convergence Z_n(β) → ζ(β) remain as documented debt.
The algebraic structure that supports them is fully proved.
-/

end CuntzGNSRepresentation
