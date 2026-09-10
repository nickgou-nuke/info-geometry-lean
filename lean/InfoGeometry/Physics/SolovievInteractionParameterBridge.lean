import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem

namespace InfoGeometry.Physics.SolovievInteractionParameterBridge

open InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- The diagonal quasiparticle/phonon part of the finite truncation. -/
def diagonalPart (eQ eP : ℝ) : M2R := !![eQ, 0; 0, eP]

/-- The symmetric off-diagonal interaction part. -/
def interactionPart (v : ℝ) : M2R := !![0, v; v, 0]

theorem qpnmMatrix_eq_diagonal_add_interaction (eQ eP v : ℝ) :
    qpnmMatrix eQ (eP - eQ) v = diagonalPart eQ eP + interactionPart v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qpnmMatrix, diagonalPart, interactionPart]

theorem interactionPart_zero (eQ eP : ℝ) :
    diagonalPart eQ eP + interactionPart 0 = diagonalPart eQ eP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [interactionPart]

end InfoGeometry.Physics.SolovievInteractionParameterBridge
