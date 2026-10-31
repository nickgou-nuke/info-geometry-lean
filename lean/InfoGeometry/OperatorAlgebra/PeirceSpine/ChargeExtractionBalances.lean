/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtraction

/-! # Corrected paired extraction coefficients in A53 -/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
include hP
local notation "D" => chargeIter P (cornerOperatorSum P A C)

theorem charge_extract_unit_sum :
    (4 : ℤ) • D 2 X - D 4 X =
      (3 : ℤ) • (comm (conePlus P A) X + comm (coneMinus P C) X) := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem charge_extract_unit_difference :
    (4 : ℤ) • D 1 X - D 3 X =
      (3 : ℤ) • (comm (conePlus P A) X - comm (coneMinus P C) X) := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

/-- Adding the two unit-charge extraction rows isolates six times the
charge-`+1` component. The coefficient is six, so this is a scaled polynomial
extraction rather than an integral projector. -/
theorem charge_extract_unit_positive :
    ((4 : ℤ) • D 2 X - D 4 X) + ((4 : ℤ) • D 1 X - D 3 X) =
      (6 : ℤ) • comm (conePlus P A) X := by
  rw [charge_extract_unit_sum hP A C X, charge_extract_unit_difference hP A C X]
  abel

/-- Subtracting the two unit-charge extraction rows isolates six times the
charge-`-1` component, again without dividing by the coefficient. -/
theorem charge_extract_unit_negative :
    ((4 : ℤ) • D 2 X - D 4 X) - ((4 : ℤ) • D 1 X - D 3 X) =
      (6 : ℤ) • comm (coneMinus P C) X := by
  rw [charge_extract_unit_sum hP A C X, charge_extract_unit_difference hP A C X]
  abel

theorem charge_extract_extreme_sum :
    D 4 X - D 2 X = (12 : ℤ) • sandwichSame P A C X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich, sandwichSame]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
