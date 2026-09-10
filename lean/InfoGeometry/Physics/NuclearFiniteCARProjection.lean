import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SolovievProjectedParameterBridge
import InfoGeometry.Physics.SolovievSecularRoots

noncomputable section

namespace InfoGeometry.Physics.NuclearFiniteCARProjection

open Matrix
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievQPNMEigenproblem
open InfoGeometry.Physics.SolovievProjectedParameterBridge
open InfoGeometry.Physics.SolovievSecularRoots
open InfoGeometry.Physics.SolovievTransitionStrength

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

def annihilation : M2R := !![0, 1; 0, 0]

def creation : M2R := !![0, 0; 1, 0]

def number : M2R := creation * annihilation

def oneModeHamiltonian (epsilon : ℝ) : M2R := epsilon • number

/-- Explicit one-mode CAR interaction with a second channel. -/
def carInteraction (v : ℝ) : M2R := v • (annihilation + creation)

/-- The coupled finite CAR Hamiltonian used by the two-channel truncation. -/
def coupledHamiltonian (epsilon v : ℝ) : M2R :=
  oneModeHamiltonian epsilon + carInteraction v

theorem annihilation_sq : annihilation * annihilation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilation, Matrix.mul_apply, Fin.sum_univ_two]

theorem creation_sq : creation * creation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [creation, Matrix.mul_apply, Fin.sum_univ_two]

theorem car_anticommutator :
    annihilation * creation + creation * annihilation = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilation, creation]

theorem number_eq_diagonal : number = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [number, creation, annihilation, Matrix.mul_apply, Fin.sum_univ_two]

theorem number_idempotent : number * number = number := by
  rw [number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem oneModeHamiltonian_commutator_annihilation (epsilon : ℝ) :
    oneModeHamiltonian epsilon * annihilation -
      annihilation * oneModeHamiltonian epsilon = -(epsilon • annihilation) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneModeHamiltonian, number, annihilation, creation,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem oneModeHamiltonian_commutator_creation (epsilon : ℝ) :
    oneModeHamiltonian epsilon * creation -
      creation * oneModeHamiltonian epsilon = epsilon • creation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneModeHamiltonian, number, annihilation, creation,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem carInteraction_commutator_annihilation (v : ℝ) :
    carInteraction v * annihilation - annihilation * carInteraction v =
      !![-v, 0; 0, v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [carInteraction, annihilation, creation, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem carInteraction_commutator_creation (v : ℝ) :
    carInteraction v * creation - creation * carInteraction v =
      !![v, 0; 0, -v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [carInteraction, annihilation, creation, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem oneModeHamiltonian_eq_block (epsilon : ℝ) :
    oneModeHamiltonian epsilon = blockHamiltonian 0 epsilon 0 := by
  rw [oneModeHamiltonian, number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockHamiltonian]

theorem carInteraction_eq_off_diagonal (v : ℝ) :
    carInteraction v = interactionPart (blockHamiltonian 0 0 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [carInteraction, annihilation, creation, interactionPart,
      blockHamiltonian,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem coupledHamiltonian_eq_qpnm (epsilon v : ℝ) :
    coupledHamiltonian epsilon v = qpnmMatrix 0 epsilon v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coupledHamiltonian, oneModeHamiltonian, carInteraction,
      number, annihilation, creation, qpnmMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem coupledHamiltonian_transpose (epsilon v : ℝ) :
    (coupledHamiltonian epsilon v)ᵀ = coupledHamiltonian epsilon v := by
  rw [coupledHamiltonian_eq_qpnm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qpnmMatrix]

theorem coupled_secular_determinant (epsilon v E : ℝ) :
    (coupledHamiltonian epsilon v - E • (1 : M2R)).det =
      (0 - E) * (epsilon - E) - v ^ 2 := by
  rw [coupledHamiltonian_eq_qpnm]
  simpa [secularMatrix] using secular_determinant_eq 0 epsilon v E

theorem coupled_dispersion_iff (epsilon v E : ℝ) :
    (coupledHamiltonian epsilon v - E • (1 : M2R)).det = 0 ↔
      (E - 0) * (E - epsilon) = v ^ 2 := by
  rw [coupledHamiltonian_eq_qpnm]
  simpa [secularMatrix] using soloviev_dispersion_iff 0 epsilon v E

theorem coupled_root_has_nonzero_eigenpair_of_v_ne_zero
    (epsilon v E : ℝ) (hv : v ≠ 0)
    (hroot : (E - 0) * (E - epsilon) = v ^ 2) :
    ∃ c : Carrier, c ≠ 0 ∧
      isEigenpair (coupledHamiltonian epsilon v) c E := by
  have hdet : (coupledHamiltonian epsilon v - E • (1 : M2R)).det = 0 := by
    apply (coupled_dispersion_iff epsilon v E).2
    exact hroot
  have hsec : secularPolynomial 0 epsilon v E = 0 := by
    dsimp [secularPolynomial]
    nlinarith [hroot]
  obtain ⟨c, hc, heig⟩ :=
    secular_root_has_eigenpair_of_coupling_ne_zero 0 epsilon v E hv hsec
  refine ⟨c, hc, ?_⟩
  rw [coupledHamiltonian_eq_qpnm]
  simpa [qpnmMatrix, blockHamiltonian] using heig

/-! The concrete root witness is the usual two-channel vector
    `(v, E)`.  Exporting it avoids hiding the spectral readout behind an
    existential witness. -/
theorem coupled_root_has_explicit_eigenpair_of_v_ne_zero
    (epsilon v E : ℝ)
    (hroot : (E - 0) * (E - epsilon) = v ^ 2) :
    isEigenpair (coupledHamiltonian epsilon v) ![v, E] E := by
  rw [coupledHamiltonian_eq_qpnm]
  rw [show qpnmMatrix 0 epsilon v = blockHamiltonian 0 epsilon v by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qpnmMatrix, blockHamiltonian]]
  apply (block_eigenpair_iff 0 epsilon v E ![v, E]).mpr
  constructor
  · simp
    ring
  · simp
    nlinarith [hroot]

theorem coupled_lower_root_has_nonzero_eigenpair
    (epsilon v : ℝ) (hv : v ≠ 0) :
    ∃ c : Carrier, c ≠ 0 ∧
      isEigenpair (coupledHamiltonian epsilon v) c (lowerRoot 0 epsilon v) := by
  apply coupled_root_has_nonzero_eigenpair_of_v_ne_zero epsilon v
    (lowerRoot 0 epsilon v) hv
  have h := lowerRoot_is_secular_root 0 epsilon v
  dsimp [secularPolynomial] at h
  nlinarith [h]

theorem coupled_upper_root_has_nonzero_eigenpair
    (epsilon v : ℝ) (hv : v ≠ 0) :
    ∃ c : Carrier, c ≠ 0 ∧
      isEigenpair (coupledHamiltonian epsilon v) c (upperRoot 0 epsilon v) := by
  apply coupled_root_has_nonzero_eigenpair_of_v_ne_zero epsilon v
    (upperRoot 0 epsilon v) hv
  have h := upperRoot_is_secular_root 0 epsilon v
  dsimp [secularPolynomial] at h
  nlinarith [h]

theorem coupled_spectral_gap (epsilon v : ℝ) :
    upperRoot 0 epsilon v - lowerRoot 0 epsilon v =
      Real.sqrt (epsilon ^ 2 + 4 * v ^ 2) := by
  rw [upperRoot_sub_lowerRoot]
  dsimp [discriminant]
  ring

theorem coupled_spectral_gap_pos (epsilon v : ℝ) (hv : v ≠ 0) :
    0 < upperRoot 0 epsilon v - lowerRoot 0 epsilon v := by
  rw [coupled_spectral_gap]
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg epsilon, sq_pos_of_ne_zero hv]

theorem coupled_trace (epsilon v : ℝ) :
    (coupledHamiltonian epsilon v).trace = epsilon := by
  rw [coupledHamiltonian_eq_qpnm]
  simp [qpnmMatrix]

theorem coupled_determinant (epsilon v : ℝ) :
    (coupledHamiltonian epsilon v).det = -(v ^ 2) := by
  rw [coupledHamiltonian_eq_qpnm]
  simp [qpnmMatrix, Matrix.det_fin_two]
  ring

/-! The concrete CAR coupling is the off-diagonal transition readout of the
    projected Hamiltonian.  This is an algebraic matrix-element statement;
    no nuclear observable is inferred from it. -/
theorem coupled_coupling_is_basis_transition_amplitude
    (epsilon v : ℝ) :
    amplitude (coupledHamiltonian epsilon v) ![1, 0] ![0, 1] = v := by
  have hSymm : isSymmetric (coupledHamiltonian epsilon v) := by
    rw [coupledHamiltonian_eq_qpnm]
    simp [isSymmetric, qpnmMatrix]
  have h := coupling_is_basis_transition_amplitude
    (coupledHamiltonian epsilon v) hSymm
  simpa [coupling, coupledHamiltonian_eq_qpnm, qpnmMatrix] using h

theorem coupled_coupling_squared_is_basis_transition_strength
    (epsilon v : ℝ) :
    strength (coupledHamiltonian epsilon v) ![1, 0] ![0, 1] = v ^ 2 := by
  have hSymm : isSymmetric (coupledHamiltonian epsilon v) := by
    rw [coupledHamiltonian_eq_qpnm]
    simp [isSymmetric, qpnmMatrix]
  have h := coupling_squared_is_basis_transition_strength
    (coupledHamiltonian epsilon v) hSymm
  simpa [coupling, coupledHamiltonian_eq_qpnm, qpnmMatrix] using h

theorem oneMode_parameters_reconstruct (epsilon : ℝ) :
    blockHamiltonian (qpEnergy (oneModeHamiltonian epsilon))
      (phononEnergy (oneModeHamiltonian epsilon))
      (coupling (oneModeHamiltonian epsilon)) =
      oneModeHamiltonian epsilon := by
  apply projected_parameter_reconstruction
  rw [oneModeHamiltonian_eq_block]
  rfl

end InfoGeometry.Physics.NuclearFiniteCARProjection
