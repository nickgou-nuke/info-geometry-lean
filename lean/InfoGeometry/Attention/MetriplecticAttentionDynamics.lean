import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Attention.MetriplecticAttentionDynamics

open Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Archetype 901: The Metriplectic Operator Splitting
Every attention matrix M decomposes uniquely into:
  M = diag(M) + C(M)
where:
  - diag(M) is the dissipative heat sink / metric gradient generator.
  - C(M) = M - diag(M) is the reversible Dirac chiral transport generator.
-/

/-- The diagonal dissipative core of a 2x2 matrix: diag(M). -/
def diag_core (M : Mat2R) : Mat2R :=
  !![M 0 0, 0;
     0, M 1 1]

/-- The off-diagonal chiral bipolar operator: C(M) = M - diag(M). -/
def chiral_bipolar (M : Mat2R) : Mat2R :=
  !![0, M 0 1;
     M 1 0, 0]

/-- Master Theorem 1: Exact Metriplectic Operator Splitting.
    M = diag_core(M) + chiral_bipolar(M) holds identically for all matrices. -/
theorem metriplectic_operator_split (M : Mat2R) :
    M = diag_core M + chiral_bipolar M := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [diag_core, chiral_bipolar]
    ring
  }

/-!
# Archetype 902: Frobenius / Trace Orthogonality
The dissipative core and the chiral transport operator are strictly orthogonal
under the Killing-Cartan / Frobenius trace inner product: ⟨A, B⟩ = tr(Aᵀ B).
-/

/-- The Frobenius inner product on Mat_{2x2}(ℝ): ⟨A, B⟩ = tr(Aᵀ * B). -/
def frobenius_inner (A B : Mat2R) : ℝ :=
  Matrix.trace (Aᵀ * B)

/-- Master Theorem 2: Strict Operator Orthogonality.
    The dissipative diagonal core and the reversible chiral channel are
    orthogonal in the operator algebra: ⟨diag_core(M), chiral_bipolar(M)⟩ = 0. -/
theorem dissipative_chiral_orthogonal (M : Mat2R) :
    frobenius_inner (diag_core M) (chiral_bipolar M) = 0 := by
  simp [frobenius_inner, diag_core, chiral_bipolar, Matrix.trace,
    Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]

/-!
# Archetype 903: Casimir Degeneracy Condition of the Dirac Grading
Let G = !![1, 0; 0, -1] be the Dirac grading involution.
The reversible Dirac transport has zero net overlap with the grading:
  tr(G * C(M)) = 0.
This is the operator-theoretic Casimir condition: energy is conserved
across the chiral transport channel.
-/

/-- The Dirac grading operator G = 2P - 1 = diag(1, -1). -/
def G_grading : Mat2R :=
  !![1,  0;
     0, -1]

/-- Master Theorem 3: Casimir Invariance of the Chiral Transport.
    The chiral transport operator has vanishing trace pairing with the grading operator. -/
theorem chiral_transport_casimir_invariant (M : Mat2R) :
    Matrix.trace (G_grading * chiral_bipolar M) = 0 := by
  simp [G_grading, chiral_bipolar, Matrix.trace, Fin.sum_univ_two]

/-!
# Archetype 904: Relativistic Mass Dispersion of the Chiral Channel
When the off-diagonal cross-attention is balanced (M₀₁ * M₁₀ = m²),
the coupled Hamiltonian H = pG + C(M) generates the exact relativistic
Dirac mass-shell dispersion relation independently of the diagonal core.
-/

/-- Master Theorem 4: The Square of the Chiral Bipolar Operator. -/
theorem chiral_bipolar_sq (M : Mat2R) :
    (chiral_bipolar M) * (chiral_bipolar M) =
    (M 0 1 * M 1 0) • (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [chiral_bipolar, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)

/-- Master Theorem 5: Anticommutation of G and C(M). -/
theorem G_anticommutes_chiral (M : Mat2R) :
    G_grading * chiral_bipolar M + chiral_bipolar M * G_grading = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [G_grading, chiral_bipolar, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one]
    ring
  }

/-- Master Theorem 6: Exact Relativistic Dispersion on the Bipolar Component.
    (p • G + C(M))² = (p² + m²) • 1 when M₀₁ * M₁₀ = m². -/
theorem metriplectic_dirac_dispersion (M : Mat2R) (p m : ℝ)
    (h_mass : M 0 1 * M 1 0 = m ^ 2) :
    (p • G_grading + chiral_bipolar M) * (p • G_grading + chiral_bipolar M) =
    (p ^ 2 + m ^ 2) • (1 : Mat2R) := by
  have h_cross : (p • G_grading) * chiral_bipolar M + chiral_bipolar M * (p • G_grading) = 0 := by
    calc (p • G_grading) * chiral_bipolar M + chiral_bipolar M * (p • G_grading)
        = p • (G_grading * chiral_bipolar M + chiral_bipolar M * G_grading) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]
      _ = p • (0 : Mat2R) := by rw [G_anticommutes_chiral]
      _ = 0 := smul_zero p
  have h_G_sq : G_grading * G_grading = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G_grading, Matrix.mul_apply, Fin.sum_univ_two]
  calc (p • G_grading + chiral_bipolar M) * (p • G_grading + chiral_bipolar M)
      = (p • G_grading) * (p • G_grading) +
        ((p • G_grading) * chiral_bipolar M + chiral_bipolar M * (p • G_grading)) +
        (chiral_bipolar M) * (chiral_bipolar M) := by
          simp only [add_mul, mul_add]
          abel
    _ = (p ^ 2) • (G_grading * G_grading) + 0 + (M 0 1 * M 1 0) • (1 : Mat2R) := by
        rw [h_cross, chiral_bipolar_sq M]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        ring_nf
    _ = (p ^ 2) • (1 : Mat2R) + (m ^ 2) • (1 : Mat2R) := by
        rw [h_G_sq, h_mass, add_zero]
    _ = (p ^ 2 + m ^ 2) • (1 : Mat2R) := by
        rw [← add_smul]

/-!
# Archetype 905: The Thermodynamic Origin of the Softmax Obstruction
For matrices with positive diagonal entries, the dissipative core has positive trace.
The chiral obstruction itself is `diag(M₀₀, -M₁₁)`, with trace `M₀₀ - M₁₁`;
that trace need not be positive. The obstruction operator is nevertheless nonzero
when either diagonal entry is nonzero. No thermodynamic interpretation is asserted.
-/

/-- The chiral obstruction tensor: Obs(M) = P * M - M * (1 - P). -/
def chiral_obstruction (M : Mat2R) : Mat2R :=
  let P : Mat2R := !![1, 0; 0, 0]
  P * M - M * (1 - P)

/-- The obstruction to the proposed chiral identity is diagonal, with opposite
signs on the two diagonal entries. -/
theorem chiral_obstruction_eq_diagonal_leak (M : Mat2R) :
    chiral_obstruction M = !![M 0 0, 0; 0, -M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiral_obstruction, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The trace of the obstruction is the difference of the diagonal entries;
positive diagonal entries alone do not make this trace positive. -/
theorem chiral_obstruction_trace (M : Mat2R) :
    Matrix.trace (chiral_obstruction M) = M 0 0 - M 1 1 := by
  rw [chiral_obstruction_eq_diagonal_leak]
  simp [Matrix.trace, Fin.sum_univ_two]; ring

/-- The obstruction trace is positive exactly when the first diagonal entry
exceeds the second. Positivity of both entries alone is not sufficient. -/
theorem chiral_obstruction_trace_pos_iff (M : Mat2R) :
    0 < Matrix.trace (chiral_obstruction M) ↔ M 0 0 > M 1 1 := by
  rw [chiral_obstruction_trace]
  exact sub_pos

/-- Equal positive diagonal entries give a nonzero obstruction with zero trace. -/
theorem positive_diagonal_obstruction_trace_can_vanish :
    ∃ M : Mat2R, 0 < M 0 0 ∧ 0 < M 1 1 ∧
      chiral_obstruction M ≠ 0 ∧ Matrix.trace (chiral_obstruction M) = 0 := by
  let M : Mat2R := !![1, 2; 3, 1]
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · norm_num [M]
  · norm_num [M]
  · intro h
    have h00 := congrArg (fun A : Mat2R => A 0 0) h
    rw [chiral_obstruction_eq_diagonal_leak] at h00
    norm_num [M] at h00
  · rw [chiral_obstruction_trace]
    norm_num [M]

/-- A positive first diagonal entry makes the obstruction matrix nonzero,
although its trace may vanish as shown above. -/
theorem chiral_obstruction_ne_zero_of_positive_first_diagonal (M : Mat2R)
    (h00 : 0 < M 0 0) :
    chiral_obstruction M ≠ 0 := by
  intro h
  have h00' := congrArg (fun A : Mat2R => A 0 0) h
  rw [chiral_obstruction_eq_diagonal_leak] at h00'
  norm_num at h00'
  exact (ne_of_gt h00) h00'

/-- Positive diagonal entries imply positive trace for the diagonal core.
    This is a statement about `diag_core`, not about `chiral_obstruction`:
    the latter has trace `M 00 - M 11`, which can vanish for positive entries. -/
theorem softmax_trace_strictly_positive (M : Mat2R)
    (h00 : 0 < M 0 0) (h11 : 0 < M 1 1) :
    0 < Matrix.trace (diag_core M) := by
  dsimp [Matrix.trace, diag_core]
  simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one]
  linarith

end InfoGeometry.Attention.MetriplecticAttentionDynamics
