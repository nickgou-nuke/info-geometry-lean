/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.DihedralArtinI2SixSpinLift

namespace InfoGeometry.Algebra.DihedralArtin

namespace SpinWeylG2

variable {G : Type*} [Group G] (SW : SpinWeylG2 G)

/-- A spin lift has the claimed nontrivial half-turn exactly when its central
    sign is nontrivial.  This separates the proved twelfth-periodicity from
    the additional hypothesis needed for an exact-order claim. -/
theorem spin_coxeter_twelfth_and_nontrivial_sixth
    (hε : SW.eps ≠ 1) :
    SW.c_tilde ^ 12 = 1 ∧ SW.c_tilde ^ 6 ≠ 1 := by
  constructor
  · exact SW.spin_coxeter_pow_twelve
  · rw [SW.c_tilde_pow_six]
    exact hε

/-- The remaining lower-order obstruction is the fourth power: together with
    a nontrivial sixth power, its exclusion gives the complete divisor test
    for a twelfth-periodic element. -/
theorem spin_coxeter_twelfth_lower_order_obstructions
    (hε : SW.eps ≠ 1) (h4 : SW.c_tilde ^ 4 ≠ 1) :
    SW.c_tilde ^ 12 = 1 ∧ SW.c_tilde ^ 4 ≠ 1 ∧ SW.c_tilde ^ 6 ≠ 1 := by
  rcases SW.spin_coxeter_twelfth_and_nontrivial_sixth hε with ⟨h12, h6⟩
  exact ⟨h12, h4, h6⟩

/-- Exact order is obtained from twelfth-periodicity together with the explicit
    exclusion of every positive smaller exponent.  The latter is deliberately
    a readback hypothesis for a concrete lift, not an assertion of the generic
    spin contract. -/
theorem spin_coxeter_orderOf_eq_twelve
    (hsmall : ∀ m : ℕ, m < 12 → 0 < m → SW.c_tilde ^ m ≠ 1) :
    orderOf SW.c_tilde = 12 := by
  apply (orderOf_eq_iff (x := SW.c_tilde) (by norm_num)).2
  exact ⟨SW.spin_coxeter_pow_twelve, hsmall⟩

end SpinWeylG2

end InfoGeometry.Algebra.DihedralArtin
