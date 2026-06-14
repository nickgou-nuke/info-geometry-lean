import Mathlib

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

namespace InfoGeometry.Canonical.PauliBraidB3

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

@[simp] lemma I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  rw [pow_two, Complex.I_mul_I]

/-- First Pauli matrix. -/
def sigma1 : Mat2C := !![(0 : ℂ), 1; 1, 0]

/-- Second Pauli matrix. -/
def sigma2 : Mat2C := !![(0 : ℂ), -Complex.I; Complex.I, 0]

/-- Third Pauli matrix. -/
def sigma3 : Mat2C := !![(1 : ℂ), 0; 0, -1]

/-- Unnormalised Pauli braid generator `1 + i σ₁`.

The normalized unitary generator is `(√2)⁻¹ • pauliBraidX`; the scalar cancels
from the Artin relation, so the exact algebraic proof avoids analytic square
roots. -/
def pauliBraidX : Mat2C := 1 + Complex.I • sigma1

/-- Unnormalised Pauli braid generator `1 + i σ₂`. -/
def pauliBraidY : Mat2C := 1 + Complex.I • sigma2

@[simp] theorem sigma1_sq : sigma1 * sigma1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sigma2_sq : sigma2 * sigma2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sigma2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

@[simp] theorem sigma3_sq : sigma3 * sigma3 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sigma3, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli anticommutation in the `σ₁, σ₂` plane. -/
theorem sigma1_sigma2_anticomm : sigma1 * sigma2 = -(sigma2 * sigma1) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, sigma2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The concrete product `σ₁σ₂ = i σ₃`. -/
theorem sigma1_mul_sigma2 : sigma1 * sigma2 = Complex.I • sigma3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, sigma2, sigma3, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact unnormalised Pauli braid relation. -/
theorem pauli_braid_relation :
    pauliBraidX * pauliBraidY * pauliBraidX =
      pauliBraidY * pauliBraidX * pauliBraidY := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliBraidX, pauliBraidY, sigma1, sigma2,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring_nf <;>
    simp <;> ring_nf

/-- Exact triple product for the unnormalised Pauli braid generators. -/
theorem pauli_braid_triple_product :
    pauliBraidX * pauliBraidY * pauliBraidX =
      (2 * Complex.I : ℂ) • (sigma1 + sigma2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliBraidX, pauliBraidY, sigma1, sigma2,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring_nf <;>
    simp <;> ring_nf

/-- The two finite identities packaged as a local `B₃` braid shadow. -/
theorem pauli_b3_braid_shadow_packet :
    pauliBraidX * pauliBraidY * pauliBraidX =
        pauliBraidY * pauliBraidX * pauliBraidY ∧
      pauliBraidX * pauliBraidY * pauliBraidX =
        (2 * Complex.I : ℂ) • (sigma1 + sigma2) :=
  ⟨pauli_braid_relation, pauli_braid_triple_product⟩

end InfoGeometry.Canonical.PauliBraidB3
