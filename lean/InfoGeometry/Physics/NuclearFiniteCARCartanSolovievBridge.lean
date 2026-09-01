import Mathlib.Tactic
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearFiniteCARProjection

/-!
# Finite CAR Cartan and Soloviev parity bridge

The concrete `2 × 2` CAR truncation used by the Soloviev lane is an actual
instance of the abstract nuclear `QuasiparticleCAR` owner.  Consequently the
Cartan/projector/parity theorems derived from CAR specialize to this model.

The resulting one-mode parity leaves the diagonal quasiparticle Hamiltonian
even and reverses the off-diagonal coupling.  Thus parity conjugation maps
`H(epsilon,v)` to `H(epsilon,-v)`.  The already-proved secular determinant and
spectral-gap formulas are even in `v`, yielding a theorem-level symmetry of the
finite spectral problem.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiniteCARCartanSolovievBridge

open Matrix
open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.NuclearFiniteCARProjection

/-- The concrete Soloviev two-state CAR carrier realizes the abstract nuclear
quasiparticle CAR axioms. -/
def finiteCAR : QuasiparticleCAR (Fin 1) M2R where
  a := fun _ => annihilation
  adag := fun _ => creation
  anticomm_a_a := by
    intro i j
    rw [annihilation_sq]
    simp
  anticomm_adag_adag := by
    intro i j
    rw [creation_sq]
    simp
  anticomm_a_adag := by
    intro i j
    have hij : i = j := Subsingleton.elim i j
    simp [hij, car_anticommutator]

/-- The generic number operator specializes exactly to the finite-model number matrix. -/
theorem finiteCAR_numberOp_eq_number :
    finiteCAR.numberOp 0 = number := by
  rfl

/-- Concrete centered occupation Cartan generator. -/
def finiteCartan : M2R :=
  finiteCAR.centeredOccupationCartan 0

/-- Concrete one-mode fermion parity. -/
def finiteParity : M2R :=
  finiteCAR.fermionParity 0

/-- Concrete vacancy projector. -/
def finiteVacancyProjector : M2R :=
  finiteCAR.vacancyProjector 0

/-- The finite Cartan generator has weights `-1,+1`. -/
theorem finiteCartan_eq_diagonal :
    finiteCartan = !![-1, 0; 0, 1] := by
  rw [finiteCartan, QuasiparticleCAR.centeredOccupationCartan,
    finiteCAR_numberOp_eq_number, number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The finite fermion parity has eigenvalues `+1,-1`. -/
theorem finiteParity_eq_diagonal :
    finiteParity = !![1, 0; 0, -1] := by
  rw [finiteParity, QuasiparticleCAR.fermionParity,
    finiteCAR_numberOp_eq_number, number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Vacancy is the complementary rank-one diagonal projector. -/
theorem finiteVacancyProjector_eq_diagonal :
    finiteVacancyProjector = !![1, 0; 0, 0] := by
  rw [finiteVacancyProjector, QuasiparticleCAR.vacancyProjector,
    finiteCAR_numberOp_eq_number, number_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- In the finite realization, fermion parity is the negative centered Cartan. -/
theorem finiteParity_eq_neg_finiteCartan :
    finiteParity = -finiteCartan := by
  rw [finiteParity_eq_diagonal, finiteCartan_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Concrete parity is an involution, inherited from the abstract CAR theorem. -/
theorem finiteParity_sq : finiteParity * finiteParity = 1 := by
  exact finiteCAR.fermionParity_sq 0

/-- Concrete creation is Cartan weight `+2`. -/
theorem finiteCartan_comm_creation :
    QuasiparticleCAR.comm finiteCartan creation = creation + creation := by
  exact finiteCAR.comm_centeredOccupationCartan_adag 0

/-- Concrete annihilation is Cartan weight `-2`. -/
theorem finiteCartan_comm_annihilation :
    QuasiparticleCAR.comm finiteCartan annihilation =
      -(annihilation + annihilation) := by
  exact finiteCAR.comm_centeredOccupationCartan_a 0

/-- Creation/annihilation commutator closes on the concrete Cartan generator. -/
theorem finite_creation_annihilation_comm :
    QuasiparticleCAR.comm creation annihilation = finiteCartan := by
  exact finiteCAR.comm_adag_a_eq_centeredOccupationCartan 0

/-- The diagonal one-mode Hamiltonian is parity-even. -/
theorem parity_conj_oneModeHamiltonian (epsilon : ℝ) :
    finiteParity * oneModeHamiltonian epsilon * finiteParity =
      oneModeHamiltonian epsilon := by
  rw [finiteParity_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneModeHamiltonian, number, creation, annihilation,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit CAR interaction is parity-odd. -/
theorem parity_conj_carInteraction (v : ℝ) :
    finiteParity * carInteraction v * finiteParity =
      -carInteraction v := by
  rw [finiteParity_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [carInteraction, annihilation, creation,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Parity conjugation reverses the sign of the Soloviev/CAR coupling. -/
theorem parity_conj_coupledHamiltonian (epsilon v : ℝ) :
    finiteParity * coupledHamiltonian epsilon v * finiteParity =
      coupledHamiltonian epsilon (-v) := by
  rw [coupledHamiltonian, coupledHamiltonian]
  calc
    finiteParity * (oneModeHamiltonian epsilon + carInteraction v) * finiteParity =
        finiteParity * oneModeHamiltonian epsilon * finiteParity +
          finiteParity * carInteraction v * finiteParity := by noncomm_ring
    _ = oneModeHamiltonian epsilon - carInteraction v := by
      rw [parity_conj_oneModeHamiltonian, parity_conj_carInteraction]
    _ = oneModeHamiltonian epsilon + carInteraction (-v) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [carInteraction, annihilation, creation]

/-- The finite secular determinant is invariant under the parity-induced
coupling reversal. -/
theorem coupled_secular_determinant_even_in_coupling
    (epsilon v E : ℝ) :
    (coupledHamiltonian epsilon (-v) - E • (1 : M2R)).det =
      (coupledHamiltonian epsilon v - E • (1 : M2R)).det := by
  rw [coupled_secular_determinant, coupled_secular_determinant]
  ring

/-- The exact two-channel spectral gap is invariant under `v ↦ -v`. -/
theorem coupled_spectral_gap_even_in_coupling (epsilon v : ℝ) :
    upperRoot 0 epsilon (-v) - lowerRoot 0 epsilon (-v) =
      upperRoot 0 epsilon v - lowerRoot 0 epsilon v := by
  rw [coupled_spectral_gap, coupled_spectral_gap]
  congr 1
  ring

/-- Transition strength between the two basis channels is parity-even because
it is the square of the coupling. -/
theorem coupled_transition_strength_even_in_coupling (epsilon v : ℝ) :
    strength (coupledHamiltonian epsilon (-v)) ![1, 0] ![0, 1] =
      strength (coupledHamiltonian epsilon v) ![1, 0] ![0, 1] := by
  rw [coupled_coupling_squared_is_basis_transition_strength,
    coupled_coupling_squared_is_basis_transition_strength]
  ring

/-- Finite nuclear parity/spectral packet. -/
theorem finite_cartan_parity_soloviev_packet (epsilon v E : ℝ) :
    finiteParity * finiteParity = 1 ∧
      finiteParity * coupledHamiltonian epsilon v * finiteParity =
        coupledHamiltonian epsilon (-v) ∧
      (coupledHamiltonian epsilon (-v) - E • (1 : M2R)).det =
        (coupledHamiltonian epsilon v - E • (1 : M2R)).det ∧
      upperRoot 0 epsilon (-v) - lowerRoot 0 epsilon (-v) =
        upperRoot 0 epsilon v - lowerRoot 0 epsilon v :=
  ⟨finiteParity_sq,
    parity_conj_coupledHamiltonian epsilon v,
    coupled_secular_determinant_even_in_coupling epsilon v E,
    coupled_spectral_gap_even_in_coupling epsilon v⟩

end InfoGeometry.Physics.NuclearFiniteCARCartanSolovievBridge
