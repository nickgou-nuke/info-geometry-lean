#exit
import InfoGeometry.Canonical.HestenesBivectorCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega_0 : basisBivector Q 0 * Omega (Q := Q) ∈ Bivector13 Q := by
  dsimp [basisBivector, gamma]
  rw [HasSpacetimeBasis.omega_eq (Q := Q)]
  have h10 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by
    apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
  have sq1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
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

lemma basisBivector_mul_omega_1 : basisBivector Q 1 * Omega (Q := Q) ∈ Bivector13 Q := by
  dsimp [basisBivector, gamma]
  rw [HasSpacetimeBasis.omega_eq (Q := Q)]
  have h20 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by
    apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h21 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by
    apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h13 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3) = - (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by
    apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
  have sq2 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) := ι_sq_scalar Q _
  have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 2)) • basisBivector Q 4 := by
    calc ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
      _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
      _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h20]
      _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1)) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul]
      _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2))) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [h21]
      _ = ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
      _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [sq0, sq2]
      _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.commutes]; simp only [mul_assoc]
      _ = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) * (- (ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1))) := by rw [h13]
      _ = (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 2)) • basisBivector Q 4 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_mul, mul_neg]
  rw [h_eq]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Set.mem_range_self 4
