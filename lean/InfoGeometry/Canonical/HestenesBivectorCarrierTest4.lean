#exit
import InfoGeometry.Canonical.HestenesBivectorCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma case_0 : 
    basisBivector Q 0 * Omega (Q := Q) ∈ Bivector13 Q := by
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
      _ = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by 
          dsimp [basisBivector, gamma]
          rw [Algebra.smul_def, map_neg, map_mul, neg_mul]
  rw [h_eq]
  apply Submodule.smul_mem
  have : basisBivector Q 3 = (⟨basisBivector Q 3, by exact Submodule.subset_span (Set.mem_range_self 3)⟩ : Bivector13 Q).1 := rfl
  rw [this]
  exact (⟨basisBivector Q 3, by exact Submodule.subset_span (Set.mem_range_self 3)⟩ : Bivector13 Q).2

