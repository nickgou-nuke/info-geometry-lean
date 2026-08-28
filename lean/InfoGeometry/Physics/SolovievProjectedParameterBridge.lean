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

def diagonalPart (H : Hamiltonian) : Hamiltonian :=
  !![H 0 0, 0; 0, H 1 1]

def interactionPart (H : Hamiltonian) : Hamiltonian :=
  !![0, H 0 1; H 1 0, 0]

theorem projected_parameter_reconstruction
    (H : Hamiltonian) (hSymm : isSymmetric H) :
    blockHamiltonian (qpEnergy H) (phononEnergy H) (coupling H) = H := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · simpa [isSymmetric] using hSymm.symm
  · rfl

/-- The three projected parameters are uniquely determined by the block matrix. -/
theorem projected_parameters_unique
    (H : Hamiltonian) (eQ eP v : ℝ)
    (h_repr : blockHamiltonian eQ eP v = H) :
    qpEnergy H = eQ ∧ phononEnergy H = eP ∧ coupling H = v := by
  have h00 := congrArg (fun M : Hamiltonian => M 0 0) h_repr
  have h11 := congrArg (fun M : Hamiltonian => M 1 1) h_repr
  have h01 := congrArg (fun M : Hamiltonian => M 0 1) h_repr
  simp [blockHamiltonian] at h00 h11 h01
  exact ⟨h00.symm, h11.symm, h01.symm⟩

/-- A secular root of a symmetric projected matrix lifts to an eigenpair of that matrix. -/
theorem projected_root_has_eigenpair_of_coupling_ne_zero
    (H : Hamiltonian) (hSymm : isSymmetric H) (E : ℝ)
    (hroot : secularPolynomial (qpEnergy H) (phononEnergy H) (coupling H) E = 0)
    (hv : coupling H ≠ 0) :
    ∃ c : Carrier, c ≠ 0 ∧ isEigenpair H c E := by
  obtain ⟨c, hc, heig⟩ :=
    secular_root_has_eigenpair_of_coupling_ne_zero
      (qpEnergy H) (phononEnergy H) (coupling H) E hv hroot
  refine ⟨c, hc, ?_⟩
  rw [← projected_parameter_reconstruction H hSymm]
  exact heig

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

theorem diagonal_plus_interaction (H : Hamiltonian) :
    diagonalPart H + interactionPart H = H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalPart, interactionPart]

theorem coupling_is_off_diagonal_matrix_element (H : Hamiltonian) :
    interactionPart H 0 1 = coupling H := by
  rfl

end InfoGeometry.Physics.SolovievProjectedParameterBridge
