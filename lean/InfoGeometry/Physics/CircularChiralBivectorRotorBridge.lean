import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.CircularChiralFockOperatorZornBridge

/-!
# Bivector-rotor replacement for the complex phase symbol

The real Cl(1,1) matrix `bivector_J_base` is the native phase axis.  It
squares to `-1`, so it supplies the real replacement for an external complex
unit in chiral operator formulas.
-/

namespace InfoGeometry.Physics.CircularChiralBivectorRotorBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

abbrev RotorCarrier := Matrix (Fin 2) (Fin 2) ℝ

def bivectorRotor : RotorCarrier := bivector_J_base

theorem bivectorRotor_sq : bivectorRotor * bivectorRotor = -(1 : RotorCarrier) := by
  exact bivector_J_base_sq

end
end InfoGeometry.Physics.CircularChiralBivectorRotorBridge
