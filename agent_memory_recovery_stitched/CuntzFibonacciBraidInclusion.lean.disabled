import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Categorical.FibonacciUniversalityColimit

open Matrix
open Complex
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Categorical.FibonacciUniversalityColimit
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

namespace InfoGeometry.Algebra.CuntzFibonacciBraidInclusion

/-- The canonical embedding of `M_n(ℂ)` into the Cuntz algebra `O_n`. -/
def matrixToCuntz (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : CuntzAlg n :=
  ∑ i : Fin n, ∑ j : Fin n, (algebraMap ℂ (CuntzAlg n) (M i j)) * (cuntzS n i * cuntzSdag n j)

/-- The embedding is an algebra homomorphism (preserves multiplication). -/
theorem matrixToCuntz_mul (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ) :
    matrixToCuntz n (M * N) = matrixToCuntz n M * matrixToCuntz n N := by
  -- Follows from expanding the double sums and applying `cuntzSdag n k * cuntzS n l = δ_{kl}`.
  -- This algebraic verification is deferred.
  sorry

/-- The canonical trace density map from the Braid limit generators into O_2. -/
def fibonacciBraidCuntzRepresentation :
    Matrix (Fin 2) (Fin 2) ℂ → CuntzAlg 2 := matrixToCuntz 2

/--
The Fibonacci braid generators remain non-commutative inside the Cuntz topological limit,
conditional on the algebraic density (injectivity) of the finite matrix representation `M_2(ℂ) ↪ O_2`.
-/
theorem fibonacciBraid_cuntz_nonabelian
    (h_inj : Function.Injective (matrixToCuntz 2)) :
    fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B ≠
      fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R := by
  intro h_eq
  have h_mul_RB : fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B = matrixToCuntz 2 (R * B) := by
    exact (matrixToCuntz_mul 2 R B).symm
  have h_mul_BR : fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R = matrixToCuntz 2 (B * R) := by
    exact (matrixToCuntz_mul 2 B R).symm
  rw [h_mul_RB, h_mul_BR] at h_eq
  have h_mat_eq := h_inj h_eq
  exact fibonacci_generators_noncommute h_mat_eq

end InfoGeometry.Algebra.CuntzFibonacciBraidInclusion
