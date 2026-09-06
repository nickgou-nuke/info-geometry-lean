import InfoGeometry.Nuclear.SplitOctonionNambuGorkovBridge
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Nambu--Gorkov transport to the Peirce coordinate carrier

The Nambu--Gorkov family is a four-parameter subcarrier of the eight
coordinate Peirce carrier.  This file records that inclusion explicitly;
it does not identify the full carriers.
-/

namespace InfoGeometry.Nuclear.NambuGorkovPeirceCarrierBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Nuclear.NambuGorkov

noncomputable def toPeirce (N : NambuGorkovCarrier ℝ) : PeirceCarrier :=
  peirceExterior3Equiv (N.xi, N.delta, N.delta, -N.xi)

theorem toPeirce_apply (N : NambuGorkovCarrier ℝ) :
    toPeirce N =
      ![N.xi, N.delta 0, N.delta 1, N.delta 2,
        -N.xi, N.delta 0, N.delta 1, N.delta 2] := by
  rw [toPeirce, peirceExterior3Equiv_apply]
  ext i
  fin_cases i <;> rfl

theorem toPeirce_injective :
    Function.Injective toPeirce := by
  intro X Y h
  rw [toPeirce_apply X, toPeirce_apply Y] at h
  cases X with
  | mk xiX deltaX =>
    cases Y with
    | mk xiY deltaY =>
      simp at h
      have hxi : xiX = xiY := h.1
      have hd0 : deltaX 0 = deltaY 0 := h.2.1
      have hd1 : deltaX 1 = deltaY 1 := h.2.2.1
      have hd2 : deltaX 2 = deltaY 2 := h.2.2.2.1
      cases hxi
      have hdelta : deltaX = deltaY := by
        funext i
        fin_cases i <;> assumption
      cases hdelta
      rfl

end InfoGeometry.Nuclear.NambuGorkovPeirceCarrierBridge
