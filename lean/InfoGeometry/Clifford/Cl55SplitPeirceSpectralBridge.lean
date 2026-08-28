import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Clifford.Cl55WittProjectors

/-! Spectral normal form for the native split rotor.

This file records the algebraic Peirce decomposition separately from any
routing or thermodynamic interpretation. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SplitPeirceSpectralBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

theorem splitRotor55_eq_peirceSpectral (i : Fin 5) (t : ℝ) :
    splitRotor55 i t =
      (Real.exp t) • hyperbolicProjector55Plus i +
        (Real.exp (-t)) • hyperbolicProjector55Minus i := by
  unfold splitRotor55 hyperbolicProjector55Plus hyperbolicProjector55Minus
  simp only [hyperbolicInvolution55, InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft,
    InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright]
  rw [Real.cosh_eq, Real.sinh_eq]
  module

theorem splitRotor55_eq_peirceSpectral_zero (i : Fin 5) :
    splitRotor55 i 0 =
      hyperbolicProjector55Plus i + hyperbolicProjector55Minus i := by
  rw [splitRotor55_eq_peirceSpectral]
  simp [splitRotor55_zero]

end InfoGeometry.Clifford.Cl55SplitPeirceSpectralBridge
