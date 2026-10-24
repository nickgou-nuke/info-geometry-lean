/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperMetriplectic.WittDiracSolder
import InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability

/-! The existing neutral Witt CAR pair realizes the integral operator
cyclotomic identities with active unit equal to the full matrix identity.
This is an algebraic specialization; no principal-bundle or cotangent-space
classification is asserted.
-/
namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
open InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability

theorem wittAnnihilator_inner_inverse (n : ℕ) :
    wittAnnihilator n * wittCreator n * wittAnnihilator n = wittAnnihilator n := by
  have h := congrArg (fun X => X * wittAnnihilator n) (witt_car_anticomm n)
  simpa only [add_mul, mul_assoc, wittAnnihilator_sq_zero, mul_zero, add_zero,
    one_mul] using h

theorem wittCreator_inner_inverse (n : ℕ) :
    wittCreator n * wittAnnihilator n * wittCreator n = wittCreator n := by
  have h := congrArg (fun X => X * wittCreator n) (witt_car_anticomm n)
  simpa only [add_mul, mul_assoc, wittCreator_sq_zero, mul_zero, zero_add,
    one_mul] using h

/-- The order-three polynomial operator is built from the actual Witt CAR pair. -/
theorem witt_cyclotomic3_cube (n : ℕ) :
    cyclotomic3Op (wittAnnihilator n) (wittCreator n) ^ 3 = 1 := by
  have h := cyclotomic_and_orientability_master
    (wittAnnihilator_sq_zero n) (wittCreator_sq_zero n)
    (wittAnnihilator_inner_inverse n) (wittCreator_inner_inverse n)
  simpa only [witt_car_anticomm] using h.1.2.2.2.2.1

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
