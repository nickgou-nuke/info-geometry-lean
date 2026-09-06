import InfoGeometry.Categorical.FibonacciFinMulAssoc
import InfoGeometry.Categorical.FibonacciBraidedCategory

namespace InfoGeometry.Categorical.FibonacciBraidedCategory

open InfoGeometry.Categorical.FibonacciFinMulAssoc

set_option maxHeartbeats 20000000 in
theorem kron_assoc
    {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B : Matrix (Fin m₂) (Fin n₂) ℂ)
    (C : Matrix (Fin m₃) (Fin n₃) ℂ) :
    Matrix.reindex
        (finMulAssocEquiv m₁ m₂ m₃)
        (finMulAssocEquiv n₁ n₂ n₃)
        (kron (kron A B) C) =
      kron A (kron B C) := by
  unfold kron
  simp only [Matrix.kronecker]
  let f : ℂ → ℂ → ℂ := fun x y => x * y
  have hleft := Matrix.kroneckerMap_reindex_left f
    (finProdFinEquiv : Fin m₁ × Fin m₂ ≃ Fin (m₁ * m₂))
    (finProdFinEquiv : Fin n₁ × Fin n₂ ≃ Fin (n₁ * n₂))
    (Matrix.kroneckerMap f A B) C
  have hright := Matrix.kroneckerMap_reindex_right f
    (finProdFinEquiv : Fin m₂ × Fin m₃ ≃ Fin (m₂ * m₃))
    (finProdFinEquiv : Fin n₂ × Fin n₃ ≃ Fin (n₂ * n₃))
    A (Matrix.kroneckerMap f B C)
  rw [hleft]
  simp only [reindex_reindex]
  rw [hright]
  simp only [reindex_reindex]
  change Matrix.reindex
      (leftAssocIndexEquiv m₁ m₂ m₃)
      (leftAssocIndexEquiv n₁ n₂ n₃) _ =
    Matrix.reindex
      (rightAssocIndexEquiv m₁ m₂ m₃)
      (rightAssocIndexEquiv n₁ n₂ n₃) _
  rw [leftAssocIndexEquiv_eq_prodAssoc_trans_rightAssoc,
    leftAssocIndexEquiv_eq_prodAssoc_trans_rightAssoc]
  rw [← reindex_reindex]
  exact congrArg
    (fun M => Matrix.reindex
      (rightAssocIndexEquiv m₁ m₂ m₃)
      (rightAssocIndexEquiv n₁ n₂ n₃) M)
    (Matrix.kronecker_assoc A B C)

end InfoGeometry.Categorical.FibonacciBraidedCategory
