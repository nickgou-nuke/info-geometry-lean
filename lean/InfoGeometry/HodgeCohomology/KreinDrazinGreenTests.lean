import InfoGeometry.HodgeCohomology.KreinDrazinGreen
import InfoGeometry.HodgeCohomology.KreinHodgeObstruction

namespace InfoGeometry.HodgeCohomology.KreinDrazinGreen.Tests

open InfoGeometry.Canonical InfoGeometry.Krein
open Drazin KreinSpace KreinHodgeObstruction

noncomputable section

def shifted : Plane →L[ℝ] Plane := 1 + nullDirac

def shiftedGreen : Plane →L[ℝ] Plane := 1 - nullDirac

theorem shifted_inverse : IsDrazinInverse shifted shiftedGreen 0 := by
  have forward : shifted * shiftedGreen = 1 := by
    unfold shifted shiftedGreen
    rw [mul_sub, mul_one, add_mul, one_mul, nullDirac_square, add_zero, add_sub_cancel_right]
  have reverse : shiftedGreen * shifted = 1 := by
    unfold shifted shiftedGreen
    rw [mul_add, mul_one, sub_mul, one_mul, nullDirac_square, sub_zero, sub_add_cancel]
  exact IsDrazinInverse.mk (forward.trans reverse.symm)
    (by rw [reverse, one_mul]) (by simpa using forward)

theorem shifted_self_adjoint : IsKreinSelfAdjoint shifted := by
  change kreinAdjoint (1 + nullDirac) = 1 + nullDirac
  rw [kreinAdjoint_add, nullDirac_krein_adjoint]
  rw [show kreinAdjoint (1 : Plane →L[ℝ] Plane) = 1 from kreinAdjoint_id]

example : kreinAdjoint shiftedGreen = shiftedGreen :=
  green_krein_adjoint shifted_inverse shifted_self_adjoint

example : kreinAdjoint (IsDrazinInverse.projection shifted shiftedGreen) =
    IsDrazinInverse.projection shifted shiftedGreen :=
  regular_projector_krein_adjoint shifted_inverse shifted_self_adjoint

example : kreinAdjoint (IsDrazinInverse.complementaryProjection shifted shiftedGreen) =
    IsDrazinInverse.complementaryProjection shifted shiftedGreen :=
  complementary_projector_krein_adjoint shifted_inverse shifted_self_adjoint

theorem green_not_commuting_metric :
    shiftedGreen * spectral_epsilon ≠ spectral_epsilon * shiftedGreen := by
  intro equality
  have witness := congrArg (fun operator : Plane →L[ℝ] Plane =>
    WithLp.snd (operator (to_doubled 1 0))) equality
  norm_num [shiftedGreen, ContinuousLinearMap.mul_apply, nullDirac_apply,
    spectral_epsilon, to_doubled] at witness

theorem modular_mirror_exchanges_inverse :
    modular_j * shiftedGreen * modular_j = shifted := by
  apply ContinuousLinearMap.ext
  intro state
  apply DoubledSpace.ext <;>
    simp [shiftedGreen, shifted, ContinuousLinearMap.mul_apply, modular_j, nullDirac_apply]
  all_goals ring

#print axioms linear_drazin_inverse
#print axioms green_krein_adjoint
#print axioms regular_projector_krein_adjoint
#print axioms complementary_projector_krein_adjoint
#print axioms shifted_inverse
#print axioms green_not_commuting_metric
#print axioms modular_mirror_exchanges_inverse

end

end InfoGeometry.HodgeCohomology.KreinDrazinGreen.Tests
