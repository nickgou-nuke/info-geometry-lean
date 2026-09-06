import InfoGeometry.Quantum.QutritMeasurement

/-!
# Pure qutrit density matrices

This module realizes a normalized qutrit vector as the rank-one matrix
`|ψ⟩⟨ψ|`. It proves Hermiticity, trace normalization, the computational Born
trace formula, and the exact Lüders numerator for coordinate measurements.
-/

noncomputable section

namespace InfoGeometry.Quantum.Qutrit

open Matrix
open scoped ComplexConjugate

/-- Rank-one computational projector `|i⟩⟨i|`. -/
def computationalProjector (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.single i i 1

@[simp] theorem computationalProjector_idempotent (i : Fin 3) :
    computationalProjector i * computationalProjector i = computationalProjector i := by
  simp [computationalProjector]

@[simp] theorem computationalProjector_star (i : Fin 3) :
    star (computationalProjector i) = computationalProjector i := by
  change (computationalProjector i)ᴴ = computationalProjector i
  simp [computationalProjector]

/-- Pure qutrit density matrix `|ψ⟩⟨ψ|`. -/
def pureDensityMatrix (ψ : QutritState) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (ψ : QutritSpace) i * conj ((ψ : QutritSpace) j)

@[simp] theorem pureDensityMatrix_diagonal (ψ : QutritState) (i : Fin 3) :
    pureDensityMatrix ψ i i = (computationalProbability ψ i : ℂ) := by
  change (ψ : QutritSpace) i * conj ((ψ : QutritSpace) i) =
    ((‖(ψ : QutritSpace) i‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A pure qutrit density matrix is Hermitian. -/
@[simp] theorem pureDensityMatrix_star (ψ : QutritState) :
    star (pureDensityMatrix ψ) = pureDensityMatrix ψ := by
  ext i j
  simp [pureDensityMatrix, mul_comm]

/-- A normalized pure qutrit density matrix has trace one. -/
theorem pureDensityMatrix_trace (ψ : QutritState) :
    Matrix.trace (pureDensityMatrix ψ) = 1 := by
  rw [Matrix.trace]
  calc
    ∑ i, pureDensityMatrix ψ i i =
        ∑ i, (computationalProbability ψ i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact pureDensityMatrix_diagonal ψ i
    _ = ((∑ i, computationalProbability ψ i : ℝ) : ℂ) := by norm_cast
    _ = 1 := by rw [sum_computationalProbability]; norm_num

/-- Born trace readout for a computational projector. -/
theorem computationalProjector_trace_mul_pureDensityMatrix
    (ψ : QutritState) (i : Fin 3) :
    Matrix.trace (computationalProjector i * pureDensityMatrix ψ) =
      (computationalProbability ψ i : ℂ) := by
  rw [computationalProjector, Matrix.trace_single_mul]
  simp

/-- Lüders numerator for a computational outcome on a pure qutrit. -/
theorem computationalProjector_sandwich_pureDensityMatrix
    (ψ : QutritState) (i : Fin 3) :
    computationalProjector i * pureDensityMatrix ψ * computationalProjector i =
      (computationalProbability ψ i : ℂ) • computationalProjector i := by
  simp [computationalProjector, Matrix.single_mul_mul_single]

end InfoGeometry.Quantum.Qutrit
