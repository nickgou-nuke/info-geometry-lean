import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Energy-coordinate shifts of Pauli-soldered momentum

This module computes the determinant deformation produced by translating the
energy coordinate of a complex four-momentum.
-/

noncomputable section

namespace ChemicalPotentialMetricBridge

open InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-- Shift the energy coordinate of a Pauli-soldered four-momentum. -/
def chemicalShiftMomentum (P : FourMomentum) (δμ : ℂ) : FourMomentum where
  E := P.E - δμ
  px := P.px
  py := P.py
  pz := P.pz

/-- The energy-coordinate shift changes the determinant/Minkowski quadratic form
by an explicit quadratic deformation term. -/
theorem det_pauliMomentum_chemicalShiftMomentum
    (P : FourMomentum) (δμ : ℂ) :
    (pauliMomentum (chemicalShiftMomentum P δμ)).det =
      minkowskiSq P + (δμ ^ 2 - 2 * δμ * P.E) := by
  rw [det_pauliMomentum]
  cases P with
  | mk E px py pz =>
    simp [chemicalShiftMomentum, minkowskiSq]
    ring

end ChemicalPotentialMetricBridge

end noncomputable section
