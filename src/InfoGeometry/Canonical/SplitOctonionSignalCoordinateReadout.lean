import InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Native readouts for split-octonion signal coordinates

This owner records the coordinate change between the paper's
`(omega, lambda, position, time)` packet and the native Zorn slots.  The
physical wavelength and action interpretations are deliberately not encoded
as algebraic consequences; they can be supplied later as explicit hypotheses.
-/

namespace InfoGeometry.Canonical.SplitOctonionSignalCoordinateReadout

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open SplitOctonionGogberashviliNormBridge

def omegaReadout (Z : ZornMatrix ℝ) : ℝ := (Z.a + Z.b) / 2

def ctReadout (Z : ZornMatrix ℝ) : ℝ := (Z.a - Z.b) / 2

def lambdaReadout (Z : ZornMatrix ℝ) (i : Fin 3) : ℝ :=
  (Z.v i + Z.w i) / 2

def positionReadout (Z : ZornMatrix ℝ) (i : Fin 3) : ℝ :=
  (Z.w i - Z.v i) / 2

@[simp] theorem omegaReadout_toNativeZorn (c : ℝ) (s : SignalCoordinates) :
    omegaReadout (toNativeZorn c s) = s.omega := by
  simp [omegaReadout, toNativeZorn]

@[simp] theorem ctReadout_toNativeZorn (c : ℝ) (s : SignalCoordinates) :
    ctReadout (toNativeZorn c s) = c * s.time := by
  simp [ctReadout, toNativeZorn]

@[simp] theorem lambdaReadout_toNativeZorn (c : ℝ) (s : SignalCoordinates)
    (i : Fin 3) :
    lambdaReadout (toNativeZorn c s) i = s.lambda i := by
  fin_cases i <;>
    simp [lambdaReadout, toNativeZorn, Vec3.add, Vec3.sub]

@[simp] theorem positionReadout_toNativeZorn (c : ℝ) (s : SignalCoordinates)
    (i : Fin 3) :
    positionReadout (toNativeZorn c s) i = s.position i := by
  fin_cases i <;>
    simp [positionReadout, toNativeZorn, Vec3.add, Vec3.sub]

theorem native_coordinate_reconstruction (c : ℝ) (s : SignalCoordinates) :
    (toNativeZorn c s).a = s.omega + c * s.time ∧
    (toNativeZorn c s).b = s.omega - c * s.time ∧
    (∀ i, (toNativeZorn c s).v i = s.lambda i - s.position i) ∧
    (∀ i, (toNativeZorn c s).w i = s.lambda i + s.position i) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [toNativeZorn, Vec3.sub]
  · intro i
    fin_cases i <;> simp [toNativeZorn, Vec3.add]

end
end InfoGeometry.Canonical.SplitOctonionSignalCoordinateReadout
