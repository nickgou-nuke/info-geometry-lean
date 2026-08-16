import Mathlib
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Itakura--Saito remainder on the native Zorn nilpotent

This compatibility owner keeps the historical theorem names while using the
repository's native split-octonion/Zorn carrier.  No auxiliary `2 × 2`
matrix carrier is introduced here.
-/

noncomputable section

namespace NilpotentItakuraSaito

open InfoGeometry.Physics.SplitOctonionBraidSU3

/-- Compatibility name for the native complexified Zorn carrier. -/
abbrev M2C := Zorn

/-- The native nonzero square-zero Zorn boundary mode. -/
abbrev KNil : M2C := zornNilpotent

/-- Native Zorn square-zero predicate. -/
def IsNilpotent2 (Z : M2C) : Prop := zornMul Z Z = zornZero

theorem KNil_sq_zero : IsNilpotent2 KNil := by
  exact zornNilpotent_sq_zero

/-- Truncated exponential in the native Zorn algebra. -/
def nilExp (K : M2C) : M2C := zornAdd I_zorn K

/-- Operator-valued Itakura--Saito remainder in the native Zorn algebra. -/
def nilItakuraSaito (K : M2C) : M2C :=
  zornSub (zornSub (nilExp K) I_zorn) K

/-- The truncated remainder cancels for every native Zorn element. -/
theorem nilItakuraSaito_zero (K : M2C) :
    nilItakuraSaito K = zornZero := by
  apply zorn_ext <;>
    simp [nilItakuraSaito, nilExp, zornAdd, zornSub, I_zorn, zornZero]

theorem KNil_itakura_zero : nilItakuraSaito KNil = zornZero :=
  nilItakuraSaito_zero KNil

/-- Scalar transport of the cancellation through the native Zorn module law. -/
theorem scaled_nilItakuraSaito_zero (eps : ℂ) (K : M2C) :
    nilItakuraSaito (zornSmul eps K) = zornZero :=
  nilItakuraSaito_zero (zornSmul eps K)

theorem nilpotent_itakura_saito_synthesis
    (K : M2C) (hK : zornMul K K = zornZero)
    (hMassless : K.a = 0)
    (hPara : K ≠ zornZero) :
    IsNilpotent2 KNil ∧
    nilItakuraSaito KNil = zornZero ∧
    (∀ eps : ℂ, nilItakuraSaito (zornSmul eps K) = zornZero) ∧
    zornMul K K = zornZero ∧
    K.a = 0 ∧ K ≠ zornZero := by
  exact ⟨KNil_sq_zero, KNil_itakura_zero,
    fun eps => scaled_nilItakuraSaito_zero eps K,
    hK, hMassless, hPara⟩

end NilpotentItakuraSaito

end noncomputable section
