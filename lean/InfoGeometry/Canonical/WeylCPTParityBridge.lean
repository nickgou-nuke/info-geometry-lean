/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.WeylSignum
import InfoGeometry.Canonical.CPTGradingCompass
import InfoGeometry.Clifford.Cl11GradedMorita

/-!
# Weyl signum as the CPT bivector parity

The finite A₁^P Weyl sign (-1)^|w| is realized as the parity of the CPT
bivector B = e₀e₁ in Cl(1,1): the operator B^|w| is 1 or B according to the
Weyl sign, and its square is always 1.
-/
noncomputable section

namespace InfoGeometry.Canonical.WeylCPTParityBridge

open InfoGeometry.Algebra
open _root_.Cl11Fermions
open InfoGeometry.Canonical.CPTGradingCompass
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Canonical.WeylSignum

variable {S : PrimeA1RootSystem}

/-- Weyl element as the CPT bivector raised to the reflection count. -/
def cptWeylOperator (w : S.WeylGroup) : CliffordAlgebra _root_.Cl11Fermions.q11 :=
  cptBivector ^ w.card

/-- The bivector square as a power. -/
theorem cptBivector_pow_two : cptBivector ^ 2 = (1 : CliffordAlgebra _root_.Cl11Fermions.q11) := by
  simpa [pow_two] using cptBivector_sq

theorem cptWeylOperator_sq (w : S.WeylGroup) :
    cptWeylOperator w * cptWeylOperator w = 1 := by
  unfold cptWeylOperator
  rw [← pow_add]
  rw [show w.card + w.card = 2 * w.card by omega]
  rw [pow_mul, cptBivector_pow_two, one_pow]

theorem cptWeylOperator_even (w : S.WeylGroup) (h : w.card % 2 = 0) :
    cptWeylOperator w = 1 := by
  unfold cptWeylOperator
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  rw [hk, pow_mul, cptBivector_pow_two, one_pow]

theorem cptWeylOperator_odd (w : S.WeylGroup) (h : w.card % 2 ≠ 0) :
    cptWeylOperator w = cptBivector := by
  unfold cptWeylOperator
  have hmod : w.card % 2 = 1 := by omega
  have hdecomp : w.card = 2 * (w.card / 2) + 1 := by omega
  rw [hdecomp, pow_add, pow_mul, cptBivector_pow_two, one_pow]
  simp

/-- Weyl signum is the parity of the reflection count. -/
theorem weylSignum_eq_parity (w : S.WeylGroup) :
    weylSignum w = if w.card % 2 = 0 then (1 : ℤ) else -1 := by
  simp [weylSignum, PrimeA1RootSystem.signature]

/-- The same parity decides whether the CPT operator is 1 or B. -/
theorem cptWeylOperator_parity (w : S.WeylGroup) :
    (w.card % 2 = 0 → cptWeylOperator w = 1) ∧
      (w.card % 2 ≠ 0 → cptWeylOperator w = cptBivector) :=
  ⟨cptWeylOperator_even w, cptWeylOperator_odd w⟩

end InfoGeometry.Canonical.WeylCPTParityBridge

end
