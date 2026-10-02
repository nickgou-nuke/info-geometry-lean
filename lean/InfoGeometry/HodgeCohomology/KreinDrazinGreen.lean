import InfoGeometry.Canonical.DrazinPairingAdjunction
import InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded

namespace InfoGeometry.HodgeCohomology.KreinDrazinGreen

open InfoGeometry.Canonical InfoGeometry.Krein
open Drazin KreinSpace KreinHodgeDiracBounded

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [metric : KreinSpace Space]
variable {operator green : Space →L[ℝ] Space} {index : ℕ}

omit [CompleteSpace Space] metric in
theorem linear_drazin_inverse (inverse : IsDrazinInverse operator green index) :
    IsDrazinInverse operator.toLinearMap green.toLinearMap index := by
  let forget : (Space →L[ℝ] Space) →+* Module.End ℝ Space :=
    ContinuousLinearMap.toLinearMapRingHom
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · exact congrArg forget inverse.comm
  · exact congrArg forget inverse.idempotent
  · simpa only [map_mul, map_pow] using congrArg forget inverse.power

theorem green_krein_adjoint (inverse : IsDrazinInverse operator green index)
    (self_adjoint : IsKreinSelfAdjoint operator) : kreinAdjoint green = green := by
  apply kreinAdjoint_eq_of_pairing green green
  exact DrazinPairingAdjunction.inverse_adjoint kreinBilin
    ((isKreinSelfAdjoint_iff operator).mp self_adjoint) (linear_drazin_inverse inverse)

theorem regular_projector_krein_adjoint (inverse : IsDrazinInverse operator green index)
    (self_adjoint : IsKreinSelfAdjoint operator) :
    kreinAdjoint (IsDrazinInverse.projection operator green) =
      IsDrazinInverse.projection operator green := by
  change kreinAdjoint (operator * green) = operator * green
  rw [kreinAdjoint_mul, green_krein_adjoint inverse self_adjoint, self_adjoint, inverse.comm]

theorem complementary_projector_krein_adjoint (inverse : IsDrazinInverse operator green index)
    (self_adjoint : IsKreinSelfAdjoint operator) :
    kreinAdjoint (IsDrazinInverse.complementaryProjection operator green) =
      IsDrazinInverse.complementaryProjection operator green := by
  unfold IsDrazinInverse.complementaryProjection
  rw [kreinAdjoint_sub, regular_projector_krein_adjoint inverse self_adjoint]
  rw [show kreinAdjoint (1 : Space →L[ℝ] Space) = 1 from kreinAdjoint_id]

end InfoGeometry.HodgeCohomology.KreinDrazinGreen
