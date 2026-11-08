import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

theorem splitRotor55_mul_peircePlus (i : Fin 5) (t : ℝ) :
    splitRotor55 i t * hyperbolicProjector55Plus i =
      (Real.exp t) • hyperbolicProjector55Plus i := by
  rw [splitRotor55_eq_peirceSpectral]
  simp only [add_mul, smul_mul_assoc, mul_smul_comm,
    hyperbolicProjector55Plus_idem,
    hyperbolicProjector55Minus_mul_plus, smul_zero, add_zero]

theorem splitRotor55_mul_peirceMinus (i : Fin 5) (t : ℝ) :
    splitRotor55 i t * hyperbolicProjector55Minus i =
      (Real.exp (-t)) • hyperbolicProjector55Minus i := by
  rw [splitRotor55_eq_peirceSpectral]
  simp only [add_mul, smul_mul_assoc, mul_smul_comm,
    hyperbolicProjector55Plus_mul_minus,
    hyperbolicProjector55Minus_idem, smul_zero, zero_add]

theorem peircePlus_mul_splitRotor55 (i : Fin 5) (t : ℝ) :
    hyperbolicProjector55Plus i * splitRotor55 i t =
      (Real.exp t) • hyperbolicProjector55Plus i := by
  rw [splitRotor55_eq_peirceSpectral]
  simp only [mul_add, mul_smul_comm, smul_mul_assoc,
    hyperbolicProjector55Plus_idem,
    hyperbolicProjector55Plus_mul_minus, smul_zero, add_zero]

theorem peirceMinus_mul_splitRotor55 (i : Fin 5) (t : ℝ) :
    hyperbolicProjector55Minus i * splitRotor55 i t =
      (Real.exp (-t)) • hyperbolicProjector55Minus i := by
  rw [splitRotor55_eq_peirceSpectral]
  simp only [mul_add, mul_smul_comm, smul_mul_assoc,
    hyperbolicProjector55Minus_mul_plus,
    hyperbolicProjector55Minus_idem, smul_zero, zero_add]

end InfoGeometry.Clifford.Cl55SplitPeirceSpectralBridge
