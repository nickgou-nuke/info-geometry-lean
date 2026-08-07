#exit
import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega_test (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  have a1 (x : CliffordAlgebra Q) (y : R) : x * algebraMap R _ y = algebraMap R _ y * x := (Algebra.commutes x y).symm
  have a1_assoc (x : CliffordAlgebra Q) (y : R) (z : CliffordAlgebra Q) : x * (algebraMap R _ y * z) = algebraMap R _ y * (x * z) := by rw [← mul_assoc, a1, mul_assoc]
  have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
  have sq0_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 0) * z) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * z := by rw [← mul_assoc, sq0]
  have sq1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
  have sq1_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 1) * z) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * z := by rw [← mul_assoc, sq1]
  have sq2 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) := ι_sq_scalar Q _
  have sq2_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 2) * z) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * z := by rw [← mul_assoc, sq2]
  have sq3 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) := ι_sq_scalar Q _
  have sq3_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 3) * z) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) * z := by rw [← mul_assoc, sq3]
  have h10 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h10_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * z) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * z)) := by rw [← mul_assoc, h10, neg_mul, mul_assoc]
  have h20 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h20_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * z) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * z)) := by rw [← mul_assoc, h20, neg_mul, mul_assoc]
  have h30 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h30_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 0) * z) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 3) * z)) := by rw [← mul_assoc, h30, neg_mul, mul_assoc]
  have h21 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h21_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 1) * z) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * z)) := by rw [← mul_assoc, h21, neg_mul, mul_assoc]
  have h31 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h31_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 1) * z) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 3) * z)) := by rw [← mul_assoc, h31, neg_mul, mul_assoc]
  have h32 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h32_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q 3) * (ι Q (HasSpacetimeBasis.gamma Q 2) * z) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 3) * z)) := by rw [← mul_assoc, h32, neg_mul, mul_assoc]

  fin_cases i
  · -- case 0
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))))) = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))))
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))))) := by rw [h10_assoc]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))))) := by rw [mul_neg]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))) := by rw [sq0_assoc, sq1_assoc]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul, neg_mul, mul_assoc]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 3
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
