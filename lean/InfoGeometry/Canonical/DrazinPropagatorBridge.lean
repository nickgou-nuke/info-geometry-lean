import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.RealHestenesKreinHomology

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The index-one Drazin inverse is a generalized inverse on the regular part. -/
theorem drazin_propagator_identity
    (A G : Module.End ℝ V)
    (hG : IsDrazinInverse A G 1) :
    A * G * A = A := by
  calc
    A * G * A = A * (G * A) := by simp [mul_assoc]
    _ = A * (A * G) := by rw [hG.comm]
    _ = A ^ 2 * G := by simp [pow_two, mul_assoc]
    _ = A := by simpa [pow_two] using hG.power

/-- A Drazin inverse commutes with its operator. -/
theorem drazin_propagator_commutes
    (A G : Module.End ℝ V)
    (hG : IsDrazinInverse A G 1) :
    A * G = G * A :=
  hG.comm

/-- The generalized inverse law supplied by the Drazin property. -/
theorem drazin_propagator_reverse_identity
    (A G : Module.End ℝ V)
    (hG : IsDrazinInverse A G 1) :
    G * A * G = G :=
  hG.idempotent

/-- The Green identity for the square of a real differential operator. -/
theorem differential_square_propagator_identity
    (𝒟 : RealHestenesKreinHomology.RealDifferential V)
    (G : Module.End ℝ V)
    (hG : IsDrazinInverse (𝒟.D.comp 𝒟.D) G 1) :
    (𝒟.D.comp 𝒟.D) * G * (𝒟.D.comp 𝒟.D) = 𝒟.D.comp 𝒟.D := by
  exact drazin_propagator_identity _ _ hG

/-- The chain-complex square has the canonical zero Drazin property.  This is
the degenerate finite case forced by `RealDifferential.D_sq_zero`; it is not a
claim about an analytic inverse on a nonzero Laplacian. -/
theorem realDifferential_square_zero_drazin
    (𝒟 : RealHestenesKreinHomology.RealDifferential V) :
    IsDrazinInverse (𝒟.D.comp 𝒟.D) (0 : Module.End ℝ V) 1 := by
  rw [𝒟.D_sq_zero]
  exact IsDrazinInverse.of_idempotent (by simp)

theorem realDifferential_square_zero_propagator_identity
    (𝒟 : RealHestenesKreinHomology.RealDifferential V) :
    (𝒟.D.comp 𝒟.D) * (0 : Module.End ℝ V) * (𝒟.D.comp 𝒟.D) =
      𝒟.D.comp 𝒟.D := by
  exact differential_square_propagator_identity 𝒟 0
    (realDifferential_square_zero_drazin 𝒟)

end InfoGeometry.Canonical
