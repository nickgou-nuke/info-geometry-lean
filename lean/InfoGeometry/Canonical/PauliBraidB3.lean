import Mathlib
import InfoGeometryCore.Basic

open InfoGeometryCore
/-!
# Finite Pauli `B₃` braid shadow

This file records the exact finite `2 × 2` complex matrix identity behind the
standard Pauli-matrix braid shadow.  It is deliberately local:

* the matrices `pauliBraidX = 1 + i σ₁` and `pauliBraidY = 1 + i σ₂` satisfy
  the adjacent Artin braid relation;
* their triple product is the explicit matrix `2 i (σ₁ + σ₂)`.

Boundary: this is a finite matrix identity.  It is not a construction of the
full braid group `Bₙ`, not a proof of a biquaternion/Clifford algebra
isomorphism, not a quantum-group centralizer theorem, not a Hecke/BMW theorem,
not a `PSL(2,ℝ)` quotient construction, and not an `osp(1|8)` formalization.
-/

open scoped Matrix

set_option linter.unnecessarySeqFocus false

namespace PauliBraidB3

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

@[simp] lemma I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  simp

/-- First Pauli matrix. -/
abbrev sigma1 := sigma1C

/-- Second Pauli matrix. -/
abbrev sigma2 := sigma2C

/-- Third Pauli matrix. -/
abbrev sigma3 := sigma3C

/-- Unnormalised Pauli braid generator `1 + i σ₁`.

The normalized unitary generator is `(√2)⁻¹ • pauliBraidX`; the scalar cancels
from the Artin relation, so the exact algebraic proof avoids analytic square
roots. -/
def pauliBraidX : Mat2C := 1 + Complex.I • sigma1

/-- Unnormalised Pauli braid generator `1 + i σ₂`. -/
def pauliBraidY : Mat2C := 1 + Complex.I • sigma2

@[simp] theorem sigma1_sq : sigma1 * sigma1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma1C, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

@[simp] theorem sigma2_sq : sigma2 * sigma2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma2C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;> ring_nf

@[simp] theorem sigma3_sq : sigma3 * sigma3 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma3C, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

/-- Pauli anticommutation in the `σ₁, σ₂` plane. -/
theorem sigma1_sigma2_anticomm : sigma1 * sigma2 = -(sigma2 * sigma1) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma1C, sigma2C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;> ring_nf

/-- The concrete product `σ₁σ₂ = i σ₃`. -/
theorem sigma1_mul_sigma2 : sigma1 * sigma2 = Complex.I • sigma3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma1C, sigma2C, sigma3C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;> ring_nf

/-- Exact unnormalised Pauli braid relation. -/
theorem pauli_braid_relation :
    pauliBraidX * pauliBraidY * pauliBraidX =
      pauliBraidY * pauliBraidX * pauliBraidY := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliBraidX, pauliBraidY, sigma1C, sigma2C, sigma3C,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> rw [I_sq] <;> ring_nf

/-- Exact triple product for the unnormalised Pauli braid generators. -/
theorem pauli_braid_triple_product :
    pauliBraidX * pauliBraidY * pauliBraidX =
      (2 * Complex.I : ℂ) • (sigma1 + sigma2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliBraidX, pauliBraidY, sigma1C, sigma2C, sigma3C,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> rw [I_sq] <;> ring_nf

/-- The two finite identities packaged as a local `B₃` braid shadow. -/
theorem pauli_b3_braid_shadow_packet :
    pauliBraidX * pauliBraidY * pauliBraidX =
        pauliBraidY * pauliBraidX * pauliBraidY ∧
      pauliBraidX * pauliBraidY * pauliBraidX =
        (2 * Complex.I : ℂ) • (sigma1 + sigma2) :=
  ⟨pauli_braid_relation, pauli_braid_triple_product⟩

end PauliBraidB3
