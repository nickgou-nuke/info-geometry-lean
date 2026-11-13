/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceChannelCounterexamples
import InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralReynolds

/-!
# Failure of unrestricted integral Reynolds scaled idempotence

The existing dense frame in the full real four-by-four matrix algebra gives
an adjoint-paired Peirce system with `V X = X`, `X V = 0`, and `K X = X`.
Thus `K (K X) = 4 V² K X` fails on this ambient input. The cut is the existing
self-adjoint idempotent `frameUnit 0 0`; the amplitude is `frameUnit 0 1`.
The witness lies outside the mass centralizer, exactly as the generic
composition theorem requires.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.PeirceChannelCounterexamples

open InfoGeometry.Canonical.TripotentMatrixExample
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The same nonzero test operator is fixed on the left and annihilated on
the right by the existing adjoint-paired mass. -/
theorem integralReynolds_test_mass_actions :
    genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) * frameUnit 0 2 =
        frameUnit 0 2 ∧
      frameUnit 0 2 *
        genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) = 0 := by
  constructor <;> simp [adjoint_pair_metric, mul_add, add_mul, frameUnit_mul]

/-- The integral four-sandwich operator fixes this ambient matrix. -/
theorem integralReynolds_test_eq :
    integralReynolds (frameUnit 0 0) (frameUnit 0 1)
      (star (frameUnit 0 1)) (frameUnit 0 2) = frameUnit 0 2 := by
  rw [integralReynolds_eq_sandwich]
  simp only [adjoint_pair_metric]
  simp [genPhi, genJ, genSig, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    conePlus, coneMinus, frameUnit_star,
    mul_add, add_mul, mul_sub, sub_mul, pow_two, frameUnit_mul]

/-- The centralizer hypothesis genuinely excludes the test operator. -/
theorem integralReynolds_test_not_commute_mass :
    ¬ Commute
      (genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)))
      (frameUnit 0 2) := by
  intro h
  have hZero : frameUnit 0 2 = 0 := by
    simpa only [integralReynolds_test_mass_actions.1,
      integralReynolds_test_mass_actions.2] using h.eq
  exact frameUnit_ne_zero 0 2 hZero

/-- The integral scale-four law is false on the full ambient matrix ring,
even for a self-adjoint cut and an adjoint pair of Peirce channels. -/
theorem integralReynolds_comp_ne_scaled :
    integralReynolds (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1))
        (integralReynolds (frameUnit 0 0) (frameUnit 0 1)
          (star (frameUnit 0 1)) (frameUnit 0 2)) ≠
      (4 : ℤ) •
        ((genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) *
            genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1))) *
          integralReynolds (frameUnit 0 0) (frameUnit 0 1)
            (star (frameUnit 0 1)) (frameUnit 0 2)) := by
  intro h
  have hScaled : frameUnit 0 2 = (4 : ℤ) • frameUnit 0 2 := by
    simpa only [integralReynolds_test_eq, mul_assoc,
      integralReynolds_test_mass_actions.1] using h
  have hEntry := congrArg (fun X : Mat => X 0 0) hScaled
  norm_num [Matrix.smul_apply, frameUnit_apply, reflection] at hEntry

end InfoGeometry.Canonical.PeirceChannelCounterexamples
