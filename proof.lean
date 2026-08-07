  have h30 : ι Q (gamma Q 3) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 3 (by decide))
  have h21 : ι Q (gamma Q 2) * ι Q (gamma Q 1) = - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 1 (by decide))
  have h31 : ι Q (gamma Q 3) * ι Q (gamma Q 1) = - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 3 1 (by decide))
  have h32 : ι Q (gamma Q 3) * ι Q (gamma Q 2) = - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 3 (by decide))
  have h12 : ι Q (gamma Q 1) * ι Q (gamma Q 2) = - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 1 (by decide))
  have h13 : ι Q (gamma Q 1) * ι Q (gamma Q 3) = - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 3 1 (by decide))
  have sq0 := ι_sq_scalar Q (gamma Q 0)
  have sq1 := ι_sq_scalar Q (gamma Q 1)
  have sq2 := ι_sq_scalar Q (gamma Q 2)
  have sq3 := ι_sq_scalar Q (gamma Q 3)
  fin_cases i
  · -- 0: 01
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 1)) * basisBivector Q 3) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h10]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq1]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 1)) * basisBivector Q 3) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  · -- 1: 02
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * basisBivector Q 4) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h20]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [sq0]
        _ = algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1))]
        _ = algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [sq2]
        _ = algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2))) * ι Q (gamma Q 3) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)))]
        _ = algebraMap R _ (Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by rw [← Algebra.commutes (Q (gamma Q 2))]
        _ = algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [← RingHom.map_mul]
        _ = algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by rw [h13]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * basisBivector Q 4) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
  · -- 2: 03
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * basisBivector Q 5) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h30]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h31]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ((ι Q (gamma Q 1) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)))) := by rw [Algebra.commutes (Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by rw [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * basisBivector Q 5) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, rfl⟩))
  · -- 3: 23
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h30]
        _ = - ((ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h20]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h31]
        _ = - (ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by rw [sq2]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (algebraMap R _ (Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by rw [algebraMap_comm_left]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · -- 4: 31
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h10]
        _ = - ((ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h30]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [sq1]
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1))) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [← Algebra.commutes]
        _ = ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [← Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 1)))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * (ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 2)))) := by rw [Algebra.commutes (Q (gamma Q 3)) (ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 3))) * ι Q (gamma Q 2))) := by rw [← mul_assoc (ι Q (gamma Q 0)) (algebraMap R _ (Q (gamma Q 3))) (ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 0)) * ι Q (gamma Q 2))) := by rw [Algebra.commutes (Q (gamma Q 3)) (ι Q (gamma Q 0))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← mul_assoc (algebraMap R _ (Q (gamma Q 1))) (algebraMap R _ (Q (gamma Q 3))) (ι Q (gamma Q 0) * ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [mul_comm (Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · -- 5: 12
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h20]
        _ = - ((ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h10]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h21]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [mul_assoc (ι Q (gamma Q 0))]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq1]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [mul_assoc (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)))]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [sq2]
        _ = - (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - ((ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1))) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3))) := by rw [← mul_assoc (ι Q (gamma Q 0)) (algebraMap R _ (Q (gamma Q 1))) (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3))]
        _ = - ((algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3))) := by rw [Algebra.commutes (Q (gamma Q 1)) (ι Q (gamma Q 0))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 2))) * ι Q (gamma Q 3))) := by rw [← mul_assoc (ι Q (gamma Q 0)) (algebraMap R _ (Q (gamma Q 2))) (ι Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 0)) * ι Q (gamma Q 3))) := by rw [Algebra.commutes (Q (gamma Q 2)) (ι Q (gamma Q 0))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by rw [← mul_assoc (algebraMap R _ (Q (gamma Q 1))) (algebraMap R _ (Q (gamma Q 2))) (ι Q (gamma Q 0) * ι Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

theorem hodge_preserves_bivector (B : CliffordAlgebra Q) (h : B ∈ Bivector13 Q) :
    B * Omega (Q := Q) ∈ Bivector13 Q := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · intro B hB
    rcases hB with ⟨i, hi⟩
    rw [← hi]
    apply basisBivector_mul_omega
  · rw [zero_mul]; apply Submodule.zero_mem
  · intro x y hx hy hx_omega hy_omega
    rw [add_mul]
    apply Submodule.add_mem _ hx_omega hy_omega
  · intro a x hx hx_omega
    rw [Algebra.smul_mul_assoc]
    apply Submodule.smul_mem _ a hx_omega

theorem hodge_sq_bivector (B : CliffordAlgebra Q) (h : B ∈ Bivector13 Q) :
    (B * Omega (Q := Q)) * Omega (Q := Q) = - B := by
  rw [mul_assoc, omega_sq (Q := Q), mul_neg, mul_one]

def hodgeBivector : Bivector13 Q →ₗ[R] Bivector13 Q where
  toFun B := ⟨(B : CliffordAlgebra Q) * Omega (Q := Q), hodge_preserves_bivector Q (B : CliffordAlgebra Q) B.property⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp [Algebra.smul_mul_assoc]

