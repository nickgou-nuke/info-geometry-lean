import Mathlib
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem
import InfoGeometry.Physics.SolovievTransitionStrength

noncomputable section

namespace InfoGeometry.Physics.SolovievProjectedParameterBridge

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievQPNMEigenproblem
open InfoGeometry.Physics.SolovievTransitionStrength

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

/-! The QPNM convention stores the phonon increment rather than the full
diagonal phonon energy.  This theorem is the exact adapter from the
projection interface to that convention. -/
theorem projected_qpnm_matrix_identification
    (H : Hamiltonian) (hSymm : isSymmetric H) :
    qpnmMatrix (qpEnergy H) (phononEnergy H - qpEnergy H) (coupling H) = H := by
  rw [show qpnmMatrix (qpEnergy H) (phononEnergy H - qpEnergy H) (coupling H) =
      blockHamiltonian (qpEnergy H) (phononEnergy H) (coupling H) by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [qpnmMatrix, blockHamiltonian]]
  exact projected_parameter_reconstruction H hSymm

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

/-! The projected interaction parameter is also the transition amplitude
between the two coordinate basis states.  This is an algebraic readout only;
no physical operator interpretation is assumed. -/
theorem coupling_is_basis_transition_amplitude
    (H : Hamiltonian) (hSymm : isSymmetric H) :
    amplitude H ![1, 0] ![0, 1] = coupling H := by
  rw [basis_transition_amplitude]
  simpa [coupling] using hSymm

theorem coupling_squared_is_basis_transition_strength
    (H : Hamiltonian) (hSymm : isSymmetric H) :
    strength H ![1, 0] ![0, 1] = (coupling H) ^ 2 := by
  rw [show strength H ![1, 0] ![0, 1] =
      amplitude H ![1, 0] ![0, 1] ^ 2 by rfl]
  rw [coupling_is_basis_transition_amplitude H hSymm]

end InfoGeometry.Physics.SolovievProjectedParameterBridge
