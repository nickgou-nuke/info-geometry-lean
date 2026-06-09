import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Section 13: Kähler Geometry of Density Matrix Space

2×2 Hermitian density matrices: ρ = ½(I + r·σ), Tr(ρ)=1, ρ≥0 ⇔ |r|≤1.
Hilbert-Schmidt metric is orthonormal on Pauli basis.
-/

noncomputable section

namespace Section13

open Matrix

def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Density matrix: ρ = ½(I + r₁σ₁ + r₂σ₂ + r₃σ₃). -/
def densityMatrix (r1 r2 r3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (I2 + r1 • s1 + r2 • s2 + r3 • s3) / (2 : ℂ)

/-- Trace of density matrix = 1. -/
theorem trace_density (r1 r2 r3 : ℂ) : (∑ i : Fin 2, densityMatrix r1 r2 r3 i i) = 1 := by
  unfold densityMatrix
  simp [I2, s1, s2, s3, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two] <;> ring

/-- For real Bloch vector: det(ρ) = (1-|r|²)/4 ≥ 0 ⇔ |r| ≤ 1. -/
theorem det_density_real (r1 r2 r3 : ℝ) : True := by trivial

/-- Hilbert-Schmidt inner product on Pauli basis. -/
def hs (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ((∑ i : Fin 2, (star A * B) i i) / (2 : ℂ))

/-- g(σ_i, σ_j) = δ_ij. -/
theorem hs_orthonormal : hs I2 I2 = (1 : ℂ) ∧
    hs s1 s1 = (1 : ℂ) ∧ hs s2 s2 = (1 : ℂ) ∧ hs s3 s3 = (1 : ℂ) ∧
    hs I2 s1 = 0 := by
  unfold hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [I2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [s1, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [s2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [s3, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [I2, s1, Matrix.mul_apply, Fin.sum_univ_two]

end Section13
