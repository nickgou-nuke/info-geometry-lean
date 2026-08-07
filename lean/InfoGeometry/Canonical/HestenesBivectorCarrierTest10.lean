#exit
import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega (i : Fin 6) : basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  have s0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
  have s1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
  have s2 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 2) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 2)) := ι_sq_scalar Q _
  have s3 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 3) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 3)) := ι_sq_scalar Q _
  have h10 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h20 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h30 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h21 : ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h31 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h32 : ι Q (HasSpacetimeBasis.gamma Q 3) * ι Q (HasSpacetimeBasis.gamma Q 2) = - (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have a1 (x : CliffordAlgebra Q) (y : R) : x * algebraMap R _ y = algebraMap R _ y * x := (Algebra.commutes x y).symm
  
  fin_cases i
  · -- case 0
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by
      dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul]
      simp only [s0, s1, s2, s3, h10, h20, h30, h21, h31, h32, a1, mul_assoc, mul_neg, neg_mul, neg_neg]
    rw [h_eq]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self 3
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
