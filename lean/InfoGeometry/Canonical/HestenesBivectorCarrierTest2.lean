#exit
import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega_0 : 
    basisBivector Q 0 * Omega (Q := Q) ∈ Bivector13 Q := by
  dsimp [basisBivector, gamma]
  rw [HasSpacetimeBasis.omega_eq (Q := Q)]
  have h01 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) = - (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0)) := by
    apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have h10 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0) = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1)) := by
    apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide
  have sq0 : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) := ι_sq_scalar Q _
  have sq1 : ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) := ι_sq_scalar Q _
  
  -- ι0 * ι1 * (ι0 * ι1 * ι2 * ι3)
  -- = ι0 * (ι1 * ι0) * ι1 * ι2 * ι3
  -- = ι0 * (- (ι0 * ι1)) * ι1 * ι2 * ι3
  -- = - (ι0 * ι0) * (ι1 * ι1) * ι2 * ι3
  -- = - Q0 * Q1 * (ι2 * ι3)
  calc ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))
    _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 0)) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by simp only [mul_assoc]
    _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1))) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3) := by rw [h10]
    _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 1) * ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)) := by sorry
