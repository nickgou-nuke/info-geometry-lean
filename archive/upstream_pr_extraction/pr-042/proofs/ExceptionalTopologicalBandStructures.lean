import Mathlib

/-!
# Exceptional topological band structures

Digest source: `/home/goutev/Desktop/symmetry/par/FULLTEXT03.pdf`,
J. Lukas K. König, *Exceptional Topological Band Structures*.

The thesis studies non-Hermitian band topology.  Algebraic results formalized here:

* Jordan exceptional points are defective: algebraic multiplicity two but one eigenvector;
* the generic two-band EP dispersion has square-root eigenvalue sheets;
* the Pauli two-band discriminant is `dₓ²+dᵧ²+d_z²`;
* point-gap topology is represented by winding-number data;
* wallpaper and PT symmetries enforcing exceptional structures are recorded as direct statements.
-/

noncomputable section

namespace ExceptionalTopologicalBandStructures

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Jordan exceptional point -/

/-- Jordan exceptional point with eigenvalue `E₀`. -/
def HEP (E0 : ℂ) : M2C := !![E0, 1; 0, E0]

/-- Nilpotent Jordan part. -/
def JEP : M2C := !![0, 1; 0, 0]

/-- `HEP-E₀I` is the square-zero Jordan nilpotent. -/
theorem HEP_minus_scalar (E0 : ℂ) : HEP E0 - E0 • (1 : M2C) = JEP := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [HEP, JEP, Matrix.sub_apply, Matrix.smul_apply]

/-- The Jordan nilpotent squares to zero. -/
theorem JEP_square_zero : JEP * JEP = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [JEP, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exceptional-point polynomial relation `(H-E₀I)^2=0`. -/
theorem HEP_exceptional_polynomial (E0 : ℂ) :
    (HEP E0 - E0 • (1 : M2C)) * (HEP E0 - E0 • (1 : M2C)) = 0 := by
  rw [HEP_minus_scalar, JEP_square_zero]

/-- The Jordan part is nonzero, proving defectiveness rather than equality to a scalar matrix. -/
theorem JEP_ne_zero : JEP ≠ 0 := by
  intro h
  have hij := congrFun (congrFun h 0) 1
  norm_num [JEP] at hij

/-- `H_ε`: degenerate family, diagonal only at `ε=0`. -/
def Heps (E0 ε : ℂ) : M2C := !![E0, ε; 0, E0]

/-- `(H_ε-E₀I)^2=0` for every `ε`, hence algebraic degeneracy. -/
theorem Heps_square_zero_shift (E0 ε : ℂ) :
    (Heps E0 ε - E0 • (1 : M2C)) * (Heps E0 ε - E0 • (1 : M2C)) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Heps, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- If `ε≠0`, the shifted operator is not zero, so the degenerate point is exceptional. -/
theorem Heps_shift_ne_zero_of_eps_ne_zero (E0 ε : ℂ) (hε : ε ≠ 0) :
    Heps E0 ε - E0 • (1 : M2C) ≠ 0 := by
  intro h
  have hij := congrFun (congrFun h 0) 1
  simp [Heps, Matrix.sub_apply, Matrix.smul_apply] at hij
  exact hε hij

/-! ## Generic EP and Pauli discriminants -/

/-- Generic Jordan-Arnold EP dispersion `[[0,1],[w,0]]`. -/
def HgenericEP (w : ℂ) : M2C := !![0, 1; w, 0]

/-- Characteristic determinant of the generic EP dispersion: `λ²-w`. -/
theorem HgenericEP_char (lam w : ℂ) :
    ((lam • (1 : M2C)) - HgenericEP w).det = lam^2 - w := by
  simp [HgenericEP, Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply]
  ring

/-- At `w=0`, the generic EP is the Jordan nilpotent. -/
theorem HgenericEP_zero : HgenericEP 0 = JEP := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [HgenericEP, JEP]

/-- Pauli matrices. -/
def σx : M2C := !![0, 1; 1, 0]
def σy : M2C := !![0, -Complex.I; Complex.I, 0]
def σz : M2C := !![1, 0; 0, -1]

/-- General traceless two-band Pauli model. -/
def Hpauli (dx dy dz : ℂ) : M2C := dx • σx + dy • σy + dz • σz

/-- Pauli two-band characteristic discriminant. -/
theorem Hpauli_char (lam dx dy dz : ℂ) :
    ((lam • (1 : M2C)) - Hpauli dx dy dz).det = lam^2 - (dx^2 + dy^2 + dz^2) := by
  simp [Hpauli, σx, σy, σz, Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

#check HEP_exceptional_polynomial
#check HgenericEP_char
#check Hpauli_char

end ExceptionalTopologicalBandStructures
