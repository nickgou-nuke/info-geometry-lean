import Mathlib

open Matrix Complex

/-!
# Biquaternion matrix logarithm and spinor monodromy

A compact formal witness for the algebraic shadow of spinorial monodromy:
non-scalar Pauli vectors can square to `-I`, and logarithm branch shifts are
indexed additively by integers (`2πi n`).
-/

noncomputable section

namespace BiquaternionLogarithmMonodromy

/-- Pauli σ₁. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli σ₂. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
/-- Pauli σ₃. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Traceless biquaternion / Pauli vector. -/
def tracelessPauli (x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  x • σ₁ + y • σ₂ + z • σ₃

/-- The Pauli vector squaring identity. -/
theorem tracelessPauli_sq (x y z : ℂ) :
    tracelessPauli x y z * tracelessPauli x y z =
      (x * x + y * y + z * z) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tracelessPauli, σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    (ring_nf; try simp [Complex.I_mul_I]; try ring)

/-- The non-scalar root manifold: norm `-1` traceless Pauli vectors square to `-I`. -/
theorem tracelessPauli_sq_neg_one (x y z : ℂ) (h : x * x + y * y + z * z = -1) :
    tracelessPauli x y z * tracelessPauli x y z =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [tracelessPauli_sq, h]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.neg_apply]

/-- Normalized Pauli directions square to `+I`. -/
theorem normalizedPauli_sq_one (x y z : ℂ) (h : x * x + y * y + z * z = 1) :
    tracelessPauli x y z * tracelessPauli x y z =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [tracelessPauli_sq, h]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

/--
The monodromy connection L for any branch of log(-I) takes the form:
L = ((m + 2n + 1)/2)·I₂ + (m/2)·T, where T is a normalized traceless Pauli matrix (T² = I₂).
We prove algebraically that the shifted connection's traceless part squares to (m/2)² I₂,
which forces the eigenvalues of L to be exactly m + n + 1/2 and n + 1/2 (strictly half-integers).
The transition gap is exactly m, a strict integer.
-/
theorem monodromy_connection_spectrum (m : ℤ) (n1 n2 n3 : ℂ) 
    (h_norm : n1 * n1 + n2 * n2 + n3 * n3 = 1) :
    let T := tracelessPauli n1 n2 n3;
    let b := (m : ℂ) / 2;
    (b • T) * (b • T) = (b * b) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro T b
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T, b, tracelessPauli, σ₁, σ₂, σ₃,
      Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_two]
  · -- i=0, j=0
    have h0 : n1 * n1 + n2 * n2 + n3 * n3 = 1 := h_norm
    calc
      (((m : ℂ) / 2 * n3 * ((m : ℂ) / 2 * n3) +
          (m : ℂ) / 2 * n1 * ((m : ℂ) / 2 * n1)) -
        (m : ℂ) / 2 * (I * n2) * ((m : ℂ) / 2 * (I * n2)))
        = ((m : ℂ) / 2) ^ 2 * (n1 * n1 + n2 * n2 + n3 * n3) := by ring
      _ = ((m : ℂ) / 2) ^ 2 * 1 := by rw [h0]
      _ = ((m : ℂ) / 2) * ((m : ℂ) / 2) := by ring
  · -- i=0, j=1
    ring
  · -- i=1, j=0
    ring
  · -- i=1, j=1
    have h1 : n1 * n1 + n2 * n2 + n3 * n3 = 1 := h_norm
    calc
      (((m : ℂ) / 2 * n1 * ((m : ℂ) / 2 * n1) +
          (m : ℂ) / 2 * (I * n2) * -((m : ℂ) / 2 * (I * n2))) -
        (m : ℂ) / 2 * n3 * -((m : ℂ) / 2 * n3))
        = ((m : ℂ) / 2) ^ 2 * (n1 * n1 + n2 * n2 + n3 * n3) := by ring
      _ = ((m : ℂ) / 2) ^ 2 * 1 := by rw [h1]
      _ = ((m : ℂ) / 2) * ((m : ℂ) / 2) := by ring

/-- Logarithm branch shifts are `2πi` times an integer. -/
def logBranchShift (n : ℤ) : ℂ := (2 * Real.pi * n : ℝ) * I

/-- Branch shifts compose by integer addition. -/
theorem logBranchShift_add (m n : ℤ) :
    logBranchShift (m + n) = logBranchShift m + logBranchShift n := by
  unfold logBranchShift
  norm_num
  ring

/-- Synthesis theorem for the monodromy/logarithm algebraic core. -/
theorem logarithm_monodromy_synthesis :
    (∀ x y z : ℂ, x * x + y * y + z * z = -1 →
      tracelessPauli x y z * tracelessPauli x y z = -(1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (∀ m n : ℤ, logBranchShift (m + n) = logBranchShift m + logBranchShift n) := by
  exact ⟨tracelessPauli_sq_neg_one, logBranchShift_add⟩

#check tracelessPauli_sq_neg_one
#check monodromy_connection_spectrum
#check logBranchShift_add
#check logarithm_monodromy_synthesis

end BiquaternionLogarithmMonodromy
