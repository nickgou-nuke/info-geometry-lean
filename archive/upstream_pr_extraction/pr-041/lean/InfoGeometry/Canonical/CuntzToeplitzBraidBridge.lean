import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Canonical.FibonacciHadjiivanovIntertwiner

/-!
# Cuntz-Toeplitz matrix-unit bridge to a square-zero Jordan shear

This file does not claim that a specific Fibonacci braid word is already equal
to a Cuntz-Toeplitz operator.  What it does record is the honest finite-stage
bridge that the existing Cuntz--Toeplitz quotient already supports:

* matrix units built from `toeplitzS i * toeplitzSdag j`;
* off-diagonal square-zero elements;
* a unipotent Jordan shear with the exact finite power law.

That is the reusable algebraic layer needed for later braid/monodromy
transport, without pretending the transport theorem has already been proved.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzToeplitzBraidBridge

open InfoGeometry.Algebra.CuntzTensorQuotient

/-- Toeplitz matrix units `E_ij = S_i S_j†` in the Cuntz-Toeplitz quotient. -/
def toeplitzMatrixUnit (n : ℕ) (i j : Fin n) : CuntzToeplitzAlg n :=
  toeplitzS n i * toeplitzSdag n j

@[simp] theorem toeplitzMatrixUnit_apply (n : ℕ) (i j : Fin n) :
    toeplitzMatrixUnit n i j = toeplitzS n i * toeplitzSdag n j := rfl

/-- Matrix-unit multiplication in the Toeplitz quotient. -/
theorem toeplitzMatrixUnit_mul (n : ℕ) (i j k l : Fin n) :
    toeplitzMatrixUnit n i j * toeplitzMatrixUnit n k l =
      if j = k then toeplitzMatrixUnit n i l else 0 := by
  dsimp [toeplitzMatrixUnit]
  calc
    (toeplitzS n i * toeplitzSdag n j) * (toeplitzS n k * toeplitzSdag n l)
        = toeplitzS n i * (toeplitzSdag n j * toeplitzS n k) * toeplitzSdag n l := by
          noncomm_ring
    _ = toeplitzS n i * (if j = k then (1 : CuntzToeplitzAlg n) else 0) *
          toeplitzSdag n l := by
          rw [toeplitz_orthogonality n j k]
    _ = (if j = k then toeplitzS n i * toeplitzSdag n l else 0) := by
          split_ifs <;> simp

/-- Off-diagonal Toeplitz matrix units are square-zero. -/
theorem toeplitzMatrixUnit_sq_off_diag
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    toeplitzMatrixUnit n i j * toeplitzMatrixUnit n i j = 0 := by
  rw [toeplitzMatrixUnit_mul]
  have hji : j ≠ i := by
    intro h
    exact hij h.symm
  simp [hji]

/-- The canonical square-zero Jordan shear built from a Toeplitz matrix unit. -/
def toeplitzJordanShear (n : ℕ) (i j : Fin n) : CuntzToeplitzAlg n :=
  hadjiivanovMonodromyMatrix (1 : ℂ) (toeplitzMatrixUnit n i j)

/--
Finite Jordan power law for a Toeplitz off-diagonal matrix unit.

This is the honest Cuntz-Toeplitz bridge we currently own: it packages the
square-zero matrix-unit shear as a Hadjiivanov-style unipotent monodromy.
-/
theorem toeplitzJordanShear_power
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) (m : ℕ) :
    toeplitzJordanShear n i j ^ m =
      1 + (m : ℂ) • toeplitzMatrixUnit n i j := by
  have h_nil :
      toeplitzMatrixUnit n i j * toeplitzMatrixUnit n i j = 0 :=
    toeplitzMatrixUnit_sq_off_diag n i j hij
  simpa [toeplitzJordanShear, hadjiivanovMonodromyMatrix] using
    (scalar_jordan_power
      (R := ℂ)
      (B := CuntzToeplitzAlg n)
      (lambda := (1 : ℂ))
      (N := toeplitzMatrixUnit n i j)
      h_nil
      m)

end InfoGeometry.Canonical.CuntzToeplitzBraidBridge
