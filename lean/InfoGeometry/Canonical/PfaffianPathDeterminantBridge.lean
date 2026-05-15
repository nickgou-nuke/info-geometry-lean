import Mathlib

/-!
# InfoGeometry.Canonical.PfaffianPathDeterminantBridge

Closed finite Pfaffian/determinant shadow readback.
-/

noncomputable section

namespace InfoGeometry.Canonical.PfaffianPathDeterminantBridge

open scoped BigOperators

/-- Finite signed pairing amplitude. -/
def signedPairingAmplitude {ι : Type*} [Fintype ι] (sign weight : ι → ℝ) : ℝ :=
  Finset.univ.sum fun i : ι => sign i * weight i

/-- The determinant shadow associated to a signed pairing amplitude. -/
def determinantShadow {ι : Type*} [Fintype ι] (sign weight : ι → ℝ) : ℝ :=
  signedPairingAmplitude sign weight ^ 2

/-- The determinant shadow is the square of the signed pairing amplitude. -/
theorem determinantShadow_eq_sq {ι : Type*} [Fintype ι] (sign weight : ι → ℝ) :
    determinantShadow sign weight = signedPairingAmplitude sign weight ^ 2 := by
  rfl

end InfoGeometry.Canonical.PfaffianPathDeterminantBridge
