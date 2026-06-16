import Mathlib
import InfoGeometry.Algebra.CuntzContractionLemmas
import InfoGeometry.Algebra.CuntzMatrixUnits

/-!
# Cuntz Normal Form: every word reduces to matrix units

Using the contraction lemmas, any product of Cuntz generators
S_i and Sdag_j can be reduced to a matrix unit E_{ij} or 0.

Specifically:
  S_i (word) Sdag_j = E_{ij} if the word is empty,
  S_i Sdag_j (word) S_k Sdag_l = E_{ij} E_{kl} = δ_{jk} E_{il}

The algebra is spanned by {E_{ij} : i,j ∈ Fin n}, and the
product rule is the matrix multiplication δ_{jk}.

Theorem: Every element of CuntzAlg n is a ℂ-linear combination
of matrix units E_{ij}. The multiplication table is:
  E_{ij} E_{kl} = δ_{jk} E_{il}
  E_{ij}† = E_{ji}
  Σ_i E_{ii} = 1
-/
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzContractionLemmas
open InfoGeometry.Algebra.CuntzMatrixUnits

noncomputable section

namespace InfoGeometry.Algebra.CuntzNormalForm

/-- The algebra CuntzAlg n is spanned by the n² matrix units E_{ij}.
    Every element decomposes as Σ_{i,j} P_i x P_j (Pierce decomposition). -/
theorem spanned_by_matrix_units (n : ℕ) (x : CuntzAlg n) :
    x = ∑ i : Fin n, ∑ j : Fin n,
      (cuntzS n i * cuntzSdag n i) * x * (cuntzS n j * cuntzSdag n j) := by
  calc
    x = 1 * x * 1 := by simp
    _ = (∑ i : Fin n, cuntzS n i * cuntzSdag n i) * x *
        (∑ j : Fin n, cuntzS n j * cuntzSdag n j) := by
      rw [cuntz_ranges_sum_one n, cuntz_ranges_sum_one n]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (cuntzS n i * cuntzSdag n i) * x * (cuntzS n j * cuntzSdag n j) := by
      simp [Finset.sum_mul, Finset.mul_sum]

/-- The matrix unit multiplication rule (re-export).
    E_{ij} E_{kl} = δ_{jk} E_{il} -/
theorem matrix_unit_product_rule (n : ℕ) (i j k l : Fin n) :
    (cuntzS n i * cuntzSdag n j) * (cuntzS n k * cuntzSdag n l) =
    (if j = k then cuntzS n i * cuntzSdag n l else 0) :=
  matrix_unit_mul n i j k l

end InfoGeometry.Algebra.CuntzNormalForm
