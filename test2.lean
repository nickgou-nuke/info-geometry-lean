import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega_test (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  fin_cases i
  · -- case 0
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
    have sq1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
    have h10 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h10]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1)) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))) := by rw [sq0, sq1]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul, neg_mul]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 3
  · -- case 1
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
    have sq2 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) := ι_sq_scalar Q _
    have h12 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h02 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h13 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 2)) • basisBivector Q 4 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h02]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h12]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [sq0, sq2]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.commutes]; simp only [mul_assoc]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * (- (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1))) := by rw [h13]
        _ = (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 2)) • basisBivector Q 4 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_mul, mul_neg]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 4
  · -- case 2
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
    have sq3 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) := ι_sq_scalar Q _
    have h03 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h13 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h23 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 3))) • basisBivector Q 5 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h03]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h13]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (- (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h23]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3)))) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)))) := by rw [sq0, sq3]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2))) := by rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.commutes]; simp only [mul_assoc]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 3))) • basisBivector Q 5 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_mul, map_neg, neg_mul]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 5
  · -- case 3
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sq2 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) := ι_sq_scalar Q _
    have sq3 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) := ι_sq_scalar Q _
    have h02 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h12 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h03 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h13 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (- (Q (HasSpacetimeBasis.gamma Q 2) * Q (HasSpacetimeBasis.gamma Q 3))) • basisBivector Q 0 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
        _ = ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (HasSpacetimeBasis.gamma Q 2) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h03]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - ((- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2))) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h02, h13]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h12]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * (- (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h23]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3)))) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)))) := by rw [sq2, sq3]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 2) * Q (HasSpacetimeBasis.gamma Q 3))) • basisBivector Q 0 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul, neg_mul, Algebra.commutes, Algebra.smul_mul_assoc]; simp only [mul_assoc]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 0
  · -- case 4
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sq1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
    have sq3 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) := ι_sq_scalar Q _
    have h03 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h12 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h23 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h13 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (- (Q (HasSpacetimeBasis.gamma Q 1) * Q (HasSpacetimeBasis.gamma Q 3))) • basisBivector Q 1 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
        _ = ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (HasSpacetimeBasis.gamma Q 3) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h01]
        _ = - ((ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - ((- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3))) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h03, sq1]
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [Algebra.commutes]; simp only [mul_assoc]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h23]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3))) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3))) := by rw [sq3]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 1) * Q (HasSpacetimeBasis.gamma Q 3))) • basisBivector Q 1 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul, neg_mul, Algebra.commutes]; simp only [mul_assoc]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 1
  · -- case 5
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sq1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
    have sq2 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) := ι_sq_scalar Q _
    have h01 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h12 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (- (Q (HasSpacetimeBasis.gamma Q 1) * Q (HasSpacetimeBasis.gamma Q 2))) • basisBivector Q 2 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
        _ = ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0))) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h01]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 1) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h12]
        _ = (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [sq1]; simp only [mul_assoc]
        _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h02]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 0) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [sq2]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 1) * Q (HasSpacetimeBasis.gamma Q 2))) • basisBivector Q 2 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul, neg_mul, Algebra.commutes]; simp only [mul_assoc]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 2
