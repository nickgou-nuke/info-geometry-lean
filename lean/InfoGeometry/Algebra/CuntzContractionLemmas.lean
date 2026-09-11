import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Contraction Lemmas

Basic identities that make the Cuntz algebra computable:
  Sdag_i S_j = δ_{ij}        (orthogonality, proved)
  S_i Sdag_j S_k = δ_{jk} S_i    (contraction from right)
  Sdag_j S_k Sdag_l = δ_{jk} Sdag_l  (contraction from left)

All proofs use `simp [mul_assoc]` for associativity, `rw` for
the Cuntz relation, and `split_ifs` for Kronecker deltas.
-/
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzContractionLemmas

/-- Right contraction: S_i Sdag_j S_k = δ_{jk} S_i -/
theorem right_contract (n : ℕ) (i j k : Fin n) :
    cuntzS n i * cuntzSdag n j * cuntzS n k =
    (if j = k then cuntzS n i else 0) := by
  calc
    cuntzS n i * cuntzSdag n j * cuntzS n k
        = cuntzS n i * (cuntzSdag n j * cuntzS n k) := by simp [mul_assoc]
    _ = cuntzS n i * (if j = k then 1 else 0) := by rw [cuntz_orthogonality n j k]
    _ = (if j = k then cuntzS n i else 0) := by split_ifs <;> simp

/-- Left contraction: Sdag_j S_k Sdag_l = δ_{jk} Sdag_l -/
theorem left_contract (n : ℕ) (j k l : Fin n) :
    cuntzSdag n j * cuntzS n k * cuntzSdag n l =
    (if j = k then cuntzSdag n l else 0) := by
  calc
    cuntzSdag n j * cuntzS n k * cuntzSdag n l
        = (cuntzSdag n j * cuntzS n k) * cuntzSdag n l := by simp [mul_assoc]
    _ = (if j = k then 1 else 0) * cuntzSdag n l := by rw [cuntz_orthogonality n j k]
    _ = (if j = k then cuntzSdag n l else 0) := by split_ifs <;> simp

/-- Double contraction: Sdag_i S_j Sdag_k S_l = δ_{ij} δ_{kl} -/
theorem double_contract (n : ℕ) (i j k l : Fin n) :
    cuntzSdag n i * cuntzS n j * cuntzSdag n k * cuntzS n l =
    (if i = j then (if k = l then 1 else 0) else 0) := by
  calc
    cuntzSdag n i * cuntzS n j * cuntzSdag n k * cuntzS n l
        = (cuntzSdag n i * cuntzS n j) * (cuntzSdag n k * cuntzS n l) := by simp [mul_assoc]
    _ = (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
      rw [cuntz_orthogonality n i j, cuntz_orthogonality n k l]
    _ = (if i = j then (if k = l then 1 else 0) else 0) := by split_ifs <;> simp

/-- Range projector contraction: P_i S_j = δ_{ij} S_i -/
theorem projector_right_contract (n : ℕ) (i j : Fin n) :
    (cuntzS n i * cuntzSdag n i) * cuntzS n j =
    (if i = j then cuntzS n i else 0) := by
  calc
    (cuntzS n i * cuntzSdag n i) * cuntzS n j
        = cuntzS n i * (cuntzSdag n i * cuntzS n j) := by simp [mul_assoc]
    _ = cuntzS n i * (if i = j then 1 else 0) := by rw [cuntz_orthogonality n i j]
    _ = (if i = j then cuntzS n i else 0) := by split_ifs <;> simp

/-- Range projector contraction: Sdag_j P_i = δ_{ij} Sdag_i -/
theorem projector_left_contract (n : ℕ) (i j : Fin n) :
    cuntzSdag n j * (cuntzS n i * cuntzSdag n i) =
    (if i = j then cuntzSdag n i else 0) := by
  by_cases hij : i = j
  · subst j; rw [← mul_assoc, cuntz_isometry n i, one_mul]; simp
  · calc
      cuntzSdag n j * (cuntzS n i * cuntzSdag n i)
          = (cuntzSdag n j * cuntzS n i) * cuntzSdag n i := by simp [mul_assoc]
      _ = 0 * cuntzSdag n i := by rw [cuntz_distinct_orthogonal n (Ne.symm hij)]
      _ = 0 := by simp
      _ = (if i = j then cuntzSdag n i else 0) := by simp [hij]

/-- S_i Sdag_i S_i = S_i (the partial isometry identity, re-proved). -/
theorem partial_isometry (n : ℕ) (i : Fin n) :
    cuntzS n i * cuntzSdag n i * cuntzS n i = cuntzS n i := by
  rw [right_contract n i i i]
  simp

/-- Sdag_i S_i Sdag_i = Sdag_i (adjoint partial isometry). -/
theorem adjoint_partial_isometry (n : ℕ) (i : Fin n) :
    cuntzSdag n i * cuntzS n i * cuntzSdag n i = cuntzSdag n i := by
  rw [left_contract n i i i]
  simp

end InfoGeometry.Algebra.CuntzContractionLemmas
