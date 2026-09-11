import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Galois-stable exponent sets for the twelvefold spectrum

This owner records the finite arithmetic content of the twelvefold spectral
discussion.  It deliberately does not identify a permutation of exponents
with a semilinear map on the concrete matrix carrier.
-/

namespace InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets

noncomputable section

abbrev C12 := ZMod 12

def sixCharacterSet : Finset C12 := {0, 1, 4, 5, 8, 9}

def galoisCharacterSet : Finset C12 := {0, 1, 3, 4, 5, 7, 8, 9, 11}

def galoisPower (u : C12ˣ) (k : C12) : C12 := (u : C12) * k

def sigma5 : C12ˣ := Units.mkOfMulEqOne 5 5 (by decide)

def sigma7 : C12ˣ := Units.mkOfMulEqOne 7 7 (by decide)

def sigma11 : C12ˣ := Units.mkOfMulEqOne 11 11 (by decide)

theorem sixCharacterSet_stable_sigma5 :
    sixCharacterSet.image (galoisPower sigma5) = sixCharacterSet := by
  native_decide

theorem sixCharacterSet_not_stable_sigma7 :
    sixCharacterSet.image (galoisPower sigma7) ≠ sixCharacterSet := by
  native_decide

theorem sixCharacterSet_not_stable_sigma11 :
    sixCharacterSet.image (galoisPower sigma11) ≠ sixCharacterSet := by
  native_decide

theorem galoisCharacterSet_stable_sigma5 :
    galoisCharacterSet.image (galoisPower sigma5) = galoisCharacterSet := by
  native_decide

theorem galoisCharacterSet_stable_sigma7 :
    galoisCharacterSet.image (galoisPower sigma7) = galoisCharacterSet := by
  native_decide

theorem galoisCharacterSet_stable_sigma11 :
    galoisCharacterSet.image (galoisPower sigma11) = galoisCharacterSet := by
  native_decide

theorem sixCharacterSet_card : sixCharacterSet.card = 6 := by
  native_decide

theorem galoisCharacterSet_card : galoisCharacterSet.card = 9 := by
  native_decide

theorem sigma5_fixes_quartic_exponent :
    galoisPower sigma5 3 = 3 := by
  native_decide

theorem sigma5_inverts_colour_exponent :
    galoisPower sigma5 8 = 4 := by
  native_decide

theorem sigma5_inverts_triality_exponent :
    galoisPower sigma5 2 = 10 := by
  native_decide

theorem sigma5_fixes_parity_exponent :
    galoisPower sigma5 6 = 6 := by
  native_decide

theorem sigma7_inverts_quartic_exponent :
    galoisPower sigma7 3 = 9 := by
  native_decide

theorem sigma7_fixes_colour_exponent :
    galoisPower sigma7 8 = 8 := by
  native_decide

theorem sigma7_fixes_triality_exponent :
    galoisPower sigma7 2 = 2 := by
  native_decide

theorem sigma11_inverts_quartic_exponent :
    galoisPower sigma11 3 = 9 := by
  native_decide

theorem sigma11_inverts_colour_exponent :
    galoisPower sigma11 8 = 4 := by
  native_decide

theorem sigma11_inverts_triality_exponent :
    galoisPower sigma11 2 = 10 := by
  native_decide

theorem every_galois_unit_fixes_parity_exponent (u : C12ˣ) :
    galoisPower u 6 = 6 := by
  fin_cases u <;> native_decide

end
end InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets
