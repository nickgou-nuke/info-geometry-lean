import Mathlib
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

noncomputable section

namespace InfoGeometry.Physics.SolovievProjectedParameterBridge

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

abbrev Hamiltonian := Matrix (Fin 2) (Fin 2) ℝ

/-! A finite projection reads the three independent entries of a symmetric
two-channel Hamiltonian.  No nuclear interpretation is built into this map. -/

def qpEnergy (H : Hamiltonian) : ℝ := H 0 0

def phononEnergy (H : Hamiltonian) : ℝ := H 1 1

def coupling (H : Hamiltonian) : ℝ := H 0 1

def isSymmetric (H : Hamiltonian) : Prop := H 1 0 = H 0 1

theorem projected_parameter_reconstruction
    (H : Hamiltonian) (hSymm : isSymmetric H) :
    blockHamiltonian (qpEnergy H) (phononEnergy H) (coupling H) = H := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · simpa [isSymmetric] using hSymm.symm
  · rfl

theorem projected_secular_determinant
    (H : Hamiltonian) (hSymm : isSymmetric H) (E : ℝ) :
    (H - E • (1 : Hamiltonian)).det =
      secularPolynomial (qpEnergy H) (phononEnergy H) (coupling H) E := by
  rw [← projected_parameter_reconstruction H hSymm]
  exact block_secular_determinant _ _ _ _

theorem projected_eigenpair_iff
    (H : Hamiltonian) (hSymm : isSymmetric H) (c : Carrier) (E : ℝ) :
    isEigenpair H c E ↔
      (qpEnergy H * c 0 + coupling H * c 1 = E * c 0 ∧
       coupling H * c 0 + phononEnergy H * c 1 = E * c 1) := by
  rw [← projected_parameter_reconstruction H hSymm]
  exact block_eigenpair_iff _ _ _ _ _

end InfoGeometry.Physics.SolovievProjectedParameterBridge
