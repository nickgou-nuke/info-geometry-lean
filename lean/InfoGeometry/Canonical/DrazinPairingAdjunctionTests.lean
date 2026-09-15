import InfoGeometry.Canonical.DrazinPairingAdjunction
import InfoGeometry.HodgeCohomology.KreinGreenEnergyTests

namespace InfoGeometry.Canonical.DrazinPairingAdjunction.Tests

open Drazin HodgeGreenProjectorConstruction.Tests

noncomputable section

def pairing : LinearMap.BilinForm ℝ Triple :=
  let first := LinearMap.fst ℝ ℝ (ℝ × ℝ)
  let second := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  let third := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  first.smulRight first + second.smulRight third + third.smulRight second

def operator : Module.End ℝ Triple :=
  (LinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (2, 0, 0) +
    ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight (0, 1, 0)

def green : Module.End ℝ Triple :=
  (LinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (1 / 2, 0, 0)

theorem operator_adjoint : LinearMap.IsAdjointPair pairing pairing operator operator := by
  intro left right
  simp [pairing, operator]
  ring

theorem green_inverse : IsDrazinInverse operator green 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  all_goals
    apply LinearMap.ext
    intro state
    simp [operator, green, pow_succ, Module.End.mul_apply]

example : LinearMap.IsAdjointPair pairing pairing green green :=
  inverse_adjoint pairing operator_adjoint green_inverse

example : pairing (0, 1, 1) (0, 1, 1) = 2 ∧
    pairing (0, 1, -1) (0, 1, -1) = -2 := by
  norm_num [pairing]

example : operator (0, 0, 1) = (0, 1, 0) ∧ operator (0, 1, 0) = 0 := by
  norm_num [operator]

example : operator (1, 0, 0) = (2, 0, 0) ∧ green (1, 0, 0) = (1 / 2, 0, 0) := by
  norm_num [operator, green]

#print axioms power_adjoint
#print axioms inverse_pairing_nilpotent_eq_zero
#print axioms nilpotent_pairing_inverse_eq_zero
#print axioms inverse_adjoint
#print axioms operator_adjoint
#print axioms green_inverse

end

end InfoGeometry.Canonical.DrazinPairingAdjunction.Tests
