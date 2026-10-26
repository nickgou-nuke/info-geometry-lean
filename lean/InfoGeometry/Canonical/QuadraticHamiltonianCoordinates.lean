import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Quadratic oscillator coordinates

Algebraic part of Bagarello--Balistreri--Kuzhel, arXiv:2610.08437v1,
Sections II and II.1. The paper omits the usual overall factor `1/2`.
No commutation assumption is needed for the coordinate identities. The finite
matrices below encode quadratic coefficients and classical Hamilton equations;
they are NOT a finite-dimensional representation of the quantum CCR.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuadraticHamiltonian

variable {A : Type*} [Ring A]

/-- Paper's harmonic quadratic expression, with no factor `1/2`. -/
def H0 (q p : A) : A := p * p + q * q

/-- Paper's Berry--Keating quadratic expression. -/
def H1 (q p : A) : A := p * q + q * p

/-- Paper's inverted quadratic expression. -/
def H2 (q p : A) : A := p * p - q * q

section Coordinates
variable {R : Type*} [CommRing R] [Algebra R A]

def hamiltonian (a0 a1 a2 : R) (q p : A) : A :=
  a0 • H0 q p + a1 • H1 q p + a2 • H2 q p

def rotatedQ (c s : R) (q p : A) : A := c • q + s • p

def rotatedP (c s : R) (q p : A) : A := -s • q + c • p

def doubleCos (c s : R) : R := c * c - s * s

def doubleSin (c s : R) : R := 2 * c * s

theorem rotated_commutator (c s : R) (q p : A) :
    ⁅rotatedQ c s q p, rotatedP c s q p⁆ = (c * c + s * s) • ⁅q, p⁆ := by
  simp only [Ring.lie_def, rotatedQ, rotatedP, add_mul, mul_add,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_sub]
  module

theorem H0_rotated (c s : R) (q p : A) :
    H0 (rotatedQ c s q p) (rotatedP c s q p) = (c * c + s * s) • H0 q p := by
  simp only [H0, rotatedQ, rotatedP, add_mul, mul_add,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_add]
  module

theorem H1_rotated (c s : R) (q p : A) :
    H1 (rotatedQ c s q p) (rotatedP c s q p) =
      doubleCos c s • H1 q p + doubleSin c s • H2 q p := by
  simp only [H1, H2, rotatedQ, rotatedP, doubleCos, doubleSin, add_mul, mul_add,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_add, smul_sub]
  module

theorem H2_rotated (c s : R) (q p : A) :
    H2 (rotatedQ c s q p) (rotatedP c s q p) =
      doubleCos c s • H2 q p - doubleSin c s • H1 q p := by
  simp only [H1, H2, rotatedQ, rotatedP, doubleCos, doubleSin, add_mul, mul_add,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_add, smul_sub]
  module

/-- Coordinate covariance; no implementation by a Hilbert-space unitary is asserted. -/
theorem hamiltonian_rotated (a0 a1 a2 c s : R) (q p : A)
    (hcs : c * c + s * s = 1) :
    hamiltonian a0 a1 a2 (rotatedQ c s q p) (rotatedP c s q p) =
      hamiltonian a0 (a1 * doubleCos c s - a2 * doubleSin c s)
        (a1 * doubleSin c s + a2 * doubleCos c s) q p := by
  simp only [hamiltonian, H0_rotated, H1_rotated, H2_rotated, hcs, one_smul]
  module

def discriminant (a0 a1 a2 : R) : R := a0 * a0 - a1 * a1 - a2 * a2

theorem discriminant_rotated (a0 a1 a2 c s : R)
    (hcs : c * c + s * s = 1) :
    discriminant a0 (a1 * doubleCos c s - a2 * doubleSin c s)
      (a1 * doubleSin c s + a2 * doubleCos c s) = discriminant a0 a1 a2 := by
  unfold discriminant doubleCos doubleSin
  calc
    _ = a0 * a0 - (a1 * a1 + a2 * a2) * (c * c + s * s) ^ 2 := by ring
    _ = _ := by rw [hcs]; ring

end Coordinates

section RealCoordinates
variable [Algebra ℝ A]

/-- Inverse coefficient formulas (2.7), without dividing by `cos (2 theta)`. -/
theorem diagonal_reconstruction (b0 b1 c s : ℝ) (q p : A)
    (hcs : c * c + s * s = 1) :
    b0 • (rotatedP c s q p * rotatedP c s q p) +
      b1 • (rotatedQ c s q p * rotatedQ c s q p) =
    hamiltonian ((b0 + b1) / 2) ((b1 - b0) * c * s)
      ((b0 - b1) * (c * c - s * s) / 2) q p := by
  calc
    _ = hamiltonian ((b0 + b1) / 2) 0 ((b0 - b1) / 2)
        (rotatedQ c s q p) (rotatedP c s q p) := by
      unfold hamiltonian H0 H1 H2
      module
    _ = _ := by
      rw [hamiltonian_rotated _ _ _ _ _ _ _ hcs]
      congr 1 <;> dsimp [doubleCos, doubleSin] <;> ring

/-- Product invariant underlying Theorem 1, including the zero Hamiltonian. -/
theorem diagonal_discriminant (b0 b1 c s : ℝ)
    (hcs : c * c + s * s = 1) :
    discriminant ((b0 + b1) / 2) ((b1 - b0) * c * s)
      ((b0 - b1) * (c * c - s * s) / 2) = b0 * b1 := by
  unfold discriminant
  calc
    _ = ((b0 + b1) ^ 2 - (b0 - b1) ^ 2 * (c * c + s * s) ^ 2) / 4 := by ring
    _ = _ := by rw [hcs]; ring

/-- The exceptional angle in II.1 is handled directly, without tangent division. -/
theorem quarter_turn (q p : A) :
    H1 (rotatedQ (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) q p)
        (rotatedP (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) q p) = H2 q p ∧
    H2 (rotatedQ (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) q p)
        (rotatedP (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) q p) = -H1 q p := by
  have heq : Real.cos (Real.pi / 4) = Real.sin (Real.pi / 4) := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsum := Real.cos_sq_add_sin_sq (Real.pi / 4)
  have hc : doubleCos (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) = 0 := by
    unfold doubleCos
    rw [heq]
    ring
  have hs : doubleSin (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) = 1 := by
    unfold doubleSin
    rw [heq] at *
    nlinarith
  simp [H1_rotated, H2_rotated, hc, hs]

end RealCoordinates

/-- Symmetric coefficient matrix on ordered phase coordinates `(q,p)`. -/
def coefficientMatrix (a0 a1 a2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a0 - a2, a1; a1, a0 + a2]

theorem coefficientMatrix_det (a0 a1 a2 : ℝ) :
    (coefficientMatrix a0 a1 a2).det = discriminant a0 a1 a2 := by
  simp [coefficientMatrix, Matrix.det_fin_two, discriminant]
  ring

/-- Classical Hamilton vector-field matrix for the paper's unhalved quadratic. -/
def phaseGenerator (a0 a1 a2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * a1, 2 * (a0 + a2); -2 * (a0 - a2), -2 * a1]

/-- An additional finite-matrix consequence of the paper's discriminant. -/
theorem phaseGenerator_sq (a0 a1 a2 : ℝ) :
    phaseGenerator a0 a1 a2 ^ 2 = (-4 * discriminant a0 a1 a2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGenerator, pow_two, Matrix.mul_apply, Fin.sum_univ_two, discriminant] <;> ring

theorem phaseGenerator_trace (a0 a1 a2 : ℝ) :
    Matrix.trace (phaseGenerator a0 a1 a2) = 0 := by
  simp [phaseGenerator, Matrix.trace_fin_two]

theorem phaseGenerator_sq_zero_of_null (a0 a1 a2 : ℝ)
    (h : discriminant a0 a1 a2 = 0) : phaseGenerator a0 a1 a2 ^ 2 = 0 := by
  rw [phaseGenerator_sq, h]
  simp

end InfoGeometry.Canonical.QuadraticHamiltonian
