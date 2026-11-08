import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect

/-!
# Complementary transfer-power sums

The two complementary Peirce elements obey the same quadratic relation.
Their power sums therefore obey a second-order operator-valued recurrence.
No trace, collision statistic, field extension, or scalar spectrum is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Sum of the powers of the transfer element and its complement. -/
def transferMoment (P A C : B) (n : ℕ) : B :=
  peirceTransfer P A C ^ n + peirceTransferComplement P A C ^ n

variable {P : B} (hP : P * P = P)
include hP

theorem peirceTransferComplement_quadratic_relation (A C : B) :
    peirceTransferComplement P A C * peirceTransferComplement P A C =
      peirceTransferComplement P A C + genV P A C := by
  simp only [peirceTransferComplement]
  peirce_nf hP

theorem peirceTransferComplement_power_recurrence (A C : B) (n : ℕ) :
    peirceTransferComplement P A C ^ (n + 2) =
      peirceTransferComplement P A C ^ (n + 1) +
        genV P A C * peirceTransferComplement P A C ^ n :=
  quadratic_power_recurrence _ _
    (peirceTransferComplement_quadratic_relation hP A C) n

omit hP in
@[simp] theorem transferMoment_zero (P A C : B) :
    transferMoment P A C 0 = 1 + 1 := by
  simp [transferMoment]

omit hP in
@[simp] theorem transferMoment_one (P A C : B) :
    transferMoment P A C 1 = 1 := by
  simp only [transferMoment, pow_one, peirceTransfer, peirceTransferComplement]
  abel

/-- The power sum has the same second-order recurrence as each summand. -/
theorem transferMoment_recurrence (A C : B) (n : ℕ) :
    transferMoment P A C (n + 2) = transferMoment P A C (n + 1) +
      genV P A C * transferMoment P A C n := by
  simp only [transferMoment, peirceTransfer_power_recurrence hP,
    peirceTransferComplement_power_recurrence hP, mul_add]
  abel

/-- Initial nontrivial moment, with integer scaling and no division. -/
theorem transferMoment_two (A C : B) :
    transferMoment P A C 2 = 1 + (2 : ℤ) • genV P A C := by
  rw [transferMoment_recurrence hP A C 0, transferMoment_one, transferMoment_zero]
  simp only [mul_add, mul_one, two_zsmul]

theorem transferMoment_three (A C : B) :
    transferMoment P A C 3 = 1 + (3 : ℤ) • genV P A C := by
  rw [transferMoment_recurrence hP A C 1, transferMoment_two hP,
    transferMoment_one, mul_one]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
