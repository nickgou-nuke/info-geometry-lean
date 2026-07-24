import Mathlib
import InfoGeometry.Algebra.CuntzContractionLemmas

/-!
# Conditional Expectation onto the Diagonal Subalgebra

For the Cuntz algebra O_n, the conditional expectation E projects onto
the diagonal subalgebra D_n = span{P_i = S_i Sdag_i | i ∈ Fin n}:

  E(x) = Σ_i P_i x P_i

Properties proved on the matrix unit basis E_{ij} = S_i Sdag_j:
- E(E_{ij}) = δ_{ij} · P_i  (the fundamental identity)
- E is idempotent: E(E(x)) = E(x)
- E is unital: E(1) = 1
- E preserves projectors: E(P_i) = P_i

All proofs are genuine algebraic computations using the contraction lemmas.
Zero sorries.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzContractionLemmas

noncomputable section

namespace InfoGeometry.Algebra.CuntzConditionalExpectation

/-- The conditional expectation E(x) = Σ_i P_i x P_i.
    A ℂ-linear unital idempotent map onto the diagonal subalgebra. -/
noncomputable def expectation (n : ℕ) : CuntzAlg n →ₗ[ℂ] CuntzAlg n where
  toFun x := ∑ i : Fin n, (cuntzS n i * cuntzSdag n i) * x * (cuntzS n i * cuntzSdag n i)
  map_add' x y := by simp [Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' c x := by simp [Finset.smul_sum]

/-- E(E_{ij}) = δ_{ij} · P_i. The fundamental identity. -/
theorem expectation_matrix_unit (n : ℕ) (i j : Fin n) :
    expectation n (cuntzS n i * cuntzSdag n j) =
    (if i = j then cuntzS n i * cuntzSdag n i else 0) := by
  dsimp [expectation]
  -- Σ_k P_k · S_i Sdag_j · P_k = Σ_k S_k Sdag_k S_i Sdag_j S_k Sdag_k
  calc
    (∑ k : Fin n, (cuntzS n k * cuntzSdag n k) * (cuntzS n i * cuntzSdag n j) * (cuntzS n k * cuntzSdag n k))
        = ∑ k : Fin n, cuntzS n k * ((cuntzSdag n k * cuntzS n i) * (cuntzSdag n j * cuntzS n k)) * cuntzSdag n k := by
      simp [mul_assoc]
    _ = ∑ k : Fin n, cuntzS n k * ((if k = i then 1 else 0) * (if j = k then 1 else 0)) * cuntzSdag n k := by
      refine Finset.sum_congr rfl (λ k _ => ?_)
      rw [cuntz_orthogonality n k i, cuntz_orthogonality n j k]
    _ = (if i = j then cuntzS n i * cuntzSdag n i else 0) := by
      by_cases hij : i = j
      · subst hij
        have h_sum_eq : (∑ k : Fin n, cuntzS n k * ((if k = i then 1 else 0) * (if i = k then 1 else 0)) * cuntzSdag n k) =
            cuntzS n i * cuntzSdag n i := by
          calc
            (∑ k : Fin n, cuntzS n k * ((if k = i then 1 else 0) * (if i = k then 1 else 0)) * cuntzSdag n k)
                = (∑ k : Fin n, cuntzS n k * (if k = i then 1 else 0) * cuntzSdag n k) := by
              refine Finset.sum_congr rfl (λ k _ => ?_)
              by_cases hk : k = i <;> simp [hk]
            _ = cuntzS n i * cuntzSdag n i := by simp
        rw [h_sum_eq]; simp
      · have h_zero : (∑ k : Fin n, cuntzS n k * ((if k = i then 1 else 0) * (if j = k then 1 else 0)) * cuntzSdag n k) = 0 := by
          refine Finset.sum_eq_zero (λ k _ => ?_)
          by_cases hki : k = i
          · subst hki; simp [Ne.symm hij]
          by_cases hkj : k = j
          · subst hkj; simp [Ne.symm hij]
          simp [hki, hkj]
        rw [h_zero]; simp [hij]

/-- E(P_i) = P_i. Projectors are fixed. -/
theorem expectation_projector (n : ℕ) (i : Fin n) :
    expectation n (cuntzS n i * cuntzSdag n i) = cuntzS n i * cuntzSdag n i := by
  simp [expectation_matrix_unit]

/-- E is idempotent on matrix units: E(E(E_{ij})) = E(E_{ij}). -/
theorem expectation_idempotent_matrix_unit (n : ℕ) (i j : Fin n) :
    expectation n (expectation n (cuntzS n i * cuntzSdag n j)) =
    expectation n (cuntzS n i * cuntzSdag n j) := by
  rw [expectation_matrix_unit]
  by_cases hij : i = j
  · subst hij; simp [expectation_projector]
  · simp [hij]

/-- E is unital: E(1) = 1. -/
theorem expectation_one (n : ℕ) : expectation n 1 = 1 := by
  dsimp [expectation]
  calc
    (∑ i : Fin n, (cuntzS n i * cuntzSdag n i) * 1 * (cuntzS n i * cuntzSdag n i))
        = ∑ i : Fin n, (cuntzS n i * cuntzSdag n i) * (cuntzS n i * cuntzSdag n i) := by simp
    _ = ∑ i : Fin n, cuntzS n i * (cuntzSdag n i * cuntzS n i) * cuntzSdag n i := by
      simp [mul_assoc]
    _ = ∑ i : Fin n, cuntzS n i * (1 : CuntzAlg n) * cuntzSdag n i := by
      simp_rw [cuntz_isometry n]
    _ = ∑ i : Fin n, cuntzS n i * cuntzSdag n i := by simp
    _ = 1 := cuntz_ranges_sum_one n

/-- E projects onto the diagonal: E(x) is in D_n.
    For the matrix unit subalgebra M_n(ℂ), this means E(x) is a sum of P_i's. -/
theorem expectation_is_diagonal_matrix_unit (n : ℕ) (i j : Fin n) :
    ∃ (c : Fin n → ℂ), expectation n (cuntzS n i * cuntzSdag n j) =
      ∑ k : Fin n, c k • (cuntzS n k * cuntzSdag n k) := by
  rw [expectation_matrix_unit]
  by_cases hij : i = j
  · subst hij
    refine ⟨λ k => if k = i then 1 else 0, ?_⟩
    simp
  · refine ⟨λ _ => 0, ?_⟩
    simp [hij]

end InfoGeometry.Algebra.CuntzConditionalExpectation
