/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge

/-!
# Integer polynomial extraction of corner operators

Contract: arbitrary associative ring, idempotent P, the existing five-term
cornerOperatorSum. These are scaled extraction identities, not inversion over
ℤ. The ±1 factors are 6, the ±2 factors 24, and the zero factor 4.
Dependency order: corner relations → charge iteration → extraction.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B)
include hP

theorem charge_extract_zero :
    chargeIter P (cornerOperatorSum P A C) 4 X -
      (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X +
      (4 : ℤ) • cornerOperatorSum P A C X = (4 : ℤ) • sandwichCross P A C X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem charge_extract_plus_one :
    ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X -
      chargeIter P (cornerOperatorSum P A C) 4 X) +
      ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X -
      chargeIter P (cornerOperatorSum P A C) 3 X) =
      (6 : ℤ) • comm (conePlus P A) X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem charge_extract_minus_one :
    ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X -
      chargeIter P (cornerOperatorSum P A C) 4 X) -
      ((4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X -
      chargeIter P (cornerOperatorSum P A C) 3 X) =
      (6 : ℤ) • comm (coneMinus P C) X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem charge_extract_plus_two :
    (chargeIter P (cornerOperatorSum P A C) 4 X -
      chargeIter P (cornerOperatorSum P A C) 2 X) +
      (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
      chargeIter P (cornerOperatorSum P A C) 1 X) =
      (24 : ℤ) • sandwich (conePlus P A) (conePlus P A) X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem charge_extract_minus_two :
    (chargeIter P (cornerOperatorSum P A C) 4 X -
      chargeIter P (cornerOperatorSum P A C) 2 X) -
      (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
      chargeIter P (cornerOperatorSum P A C) 1 X) =
      (24 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
