import Mathlib

/-!
# Inner supercharge derivations and their commutator channel

This is the finite algebraic identity available without a grading
representation: the commutator of two ordinary inner derivations is the inner
derivation of the commutator of their generators.  The graded odd--odd
anticommutator requires an explicit parity action and is therefore not silently
identified with this ungraded identity.
-/

namespace InfoGeometry.Canonical.SuperchargeInnerDerivationTranslation

def innerDerivation {A : Type*} [Ring A] (Q X : A) : A :=
  Q * X - X * Q

/-! The translation channel is genuinely a derivation of the underlying
associative product. -/

theorem innerDerivation_mul {A : Type*} [Ring A] (Q X Y : A) :
    innerDerivation Q (X * Y) =
      innerDerivation Q X * Y + X * innerDerivation Q Y := by
  unfold innerDerivation
  noncomm_ring

def superchargeCommutatorTranslation {A : Type*} [Ring A]
    (Qplus Qminus X : A) : A :=
  innerDerivation Qplus (innerDerivation Qminus X) -
    innerDerivation Qminus (innerDerivation Qplus X)

theorem superchargeCommutatorTranslation_eq_commutator_innerDerivation
    {A : Type*} [Ring A] (Qplus Qminus X : A) :
    superchargeCommutatorTranslation Qplus Qminus X =
      innerDerivation (Qplus * Qminus - Qminus * Qplus) X := by
  unfold superchargeCommutatorTranslation innerDerivation
  simp only [sub_eq_add_neg]
  noncomm_ring

theorem superchargeCommutatorTranslation_eq_zero_of_commutator_eq_zero
    {A : Type*} [Ring A] (Qplus Qminus X : A)
    (hQ : Qplus * Qminus - Qminus * Qplus = 0) :
    superchargeCommutatorTranslation Qplus Qminus X = 0 := by
  rw [superchargeCommutatorTranslation_eq_commutator_innerDerivation, hQ]
  simp [innerDerivation]

end InfoGeometry.Canonical.SuperchargeInnerDerivationTranslation
