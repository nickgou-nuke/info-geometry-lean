import InfoGeometry.Physics.OperatorZornMatrixAlgebra
import InfoGeometry.Physics.NuclearBdGSolovievCompression

noncomputable section

namespace InfoGeometry.Physics.MengCircularOperatorZorn

open OperatorZornMatrix NuclearBdGSolovievCompression

variable {Coeff : Type*} [Ring Coeff] [StarRing Coeff]

def phaseBasis (imaginary : Coeff) : Matrix (Fin 2) (Fin 2) Coeff :=
  !![imaginary, 0; 0, 1]

def phaseBasisInverse (imaginary : Coeff) : Matrix (Fin 2) (Fin 2) Coeff :=
  !![-imaginary, 0; 0, 1]

omit [StarRing Coeff] in
theorem phaseBasis_inverse (imaginary : Coeff) (square : imaginary * imaginary = -1) :
    phaseBasis imaginary * phaseBasisInverse imaginary = 1 ∧
      phaseBasisInverse imaginary * phaseBasis imaginary = 1 := by
  constructor <;> ext row col <;> fin_cases row <;> fin_cases col <;>
    simp [phaseBasis, phaseBasisInverse, Matrix.mul_apply, Fin.sum_univ_two, square]

def circularReadout (imaginary : Coeff) (operator : OperatorZornMatrix Coeff) :
    OperatorZornMatrix Coeff :=
  ofMatrix (phaseBasis imaginary * toMatrix operator * phaseBasisInverse imaginary)

theorem circularReadout_entries (imaginary : Coeff) (operator : OperatorZornMatrix Coeff) :
    toMatrix (circularReadout imaginary operator) =
      !![imaginary * operator.n_plus_op * (-imaginary), imaginary * operator.sigma_plus_op;
         operator.sigma_minus_op * (-imaginary), operator.n_minus_op] := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [circularReadout, ofMatrix, toMatrix, phaseBasis, phaseBasisInverse,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem circularReadout_mul (imaginary : Coeff) (square : imaginary * imaginary = -1)
    (first second : OperatorZornMatrix Coeff) :
    circularReadout imaginary (first * second) =
      circularReadout imaginary first * circularReadout imaginary second := by
  apply (equivMatrix (A := Coeff)).injective
  change toMatrix (circularReadout imaginary (first * second)) =
    toMatrix (circularReadout imaginary first * circularReadout imaginary second)
  have readout (operator : OperatorZornMatrix Coeff) :
      toMatrix (circularReadout imaginary operator) =
        phaseBasis imaginary * toMatrix operator * phaseBasisInverse imaginary :=
    (equivMatrix (A := Coeff)).apply_symm_apply _
  rw [toMatrix_mul, readout, readout, readout, toMatrix_mul]
  have inverse := (phaseBasis_inverse imaginary square).2
  symm
  calc
    phaseBasis imaginary * toMatrix first * phaseBasisInverse imaginary *
        (phaseBasis imaginary * toMatrix second * phaseBasisInverse imaginary) =
      phaseBasis imaginary * toMatrix first *
        (phaseBasisInverse imaginary * phaseBasis imaginary) *
          toMatrix second * phaseBasisInverse imaginary := by noncomm_ring
    _ = phaseBasis imaginary * (toMatrix first * toMatrix second) *
        phaseBasisInverse imaginary := by rw [inverse]; simp [mul_assoc]

def circularSoloviev (energy phonon coupling : ℂ) : OperatorZornMatrix ℂ :=
  circularReadout Complex.I (ofMatrix (solovievBlock energy phonon coupling))

theorem circularSoloviev_matrix (energy phonon coupling : ℂ) :
    toMatrix (circularSoloviev energy phonon coupling) =
      !![energy, Complex.I * coupling; -Complex.I * coupling, energy + phonon] := by
  rw [circularSoloviev, circularReadout_entries]
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [ofMatrix, solovievBlock] <;> ring_nf
  simp [Complex.I_sq]

theorem circularSoloviev_characteristic (energy phonon coupling spectral : ℂ) :
    Matrix.det (toMatrix (circularSoloviev energy phonon coupling) -
      spectral • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        (energy - spectral) * (energy + phonon - spectral) - coupling ^ 2 := by
  rw [circularSoloviev_matrix, Matrix.det_fin_two]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

end InfoGeometry.Physics.MengCircularOperatorZorn
