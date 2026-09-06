import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix BigOperators

namespace HilbertSchmidtMatrix

variable {n : ℕ}

/-- Real Hilbert-Schmidt Inner Product on n × n real matrices: <A, B>_HS = Tr(Aᵀ B). -/
def hilbertSchmidtPairing (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  trace (A.transpose * B)

/-- **Theorem**: Hilbert-Schmidt Pairing Sum Formula: <A, B>_HS = ∑_{i,j} A_ji * B_ji. -/
theorem hilbertSchmidtPairing_eq_sum (A B : Matrix (Fin n) (Fin n) ℝ) :
    hilbertSchmidtPairing A B = ∑ i, ∑ j, A j i * B j i := by
  simp [hilbertSchmidtPairing, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

/-- **Theorem**: Hilbert-Schmidt Metric Symmetry: <A, B>_HS = <B, A>_HS. -/
theorem hilbertSchmidt_symmetry (A B : Matrix (Fin n) (Fin n) ℝ) :
    hilbertSchmidtPairing A B = hilbertSchmidtPairing B A := by
  rw [hilbertSchmidtPairing_eq_sum, hilbertSchmidtPairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Theorem**: Hilbert-Schmidt Metric Positive Semi-Definiteness: <A, A>_HS ≥ 0. -/
theorem hilbertSchmidt_pos_semidef (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ hilbertSchmidtPairing A A := by
  rw [hilbertSchmidtPairing_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  simpa [pow_two] using sq_nonneg (A j i)

/-!
The previous version packaged a universal kernel equation as a field of a
"metriplectic system".  That equation is not a consequence of the
Hilbert--Schmidt pairing and is false for arbitrary matrices.  The honest
finite-dimensional statement needs the usual self-adjointness hypotheses.
-/
theorem hilbertSchmidt_commutator_energy_orthogonal
    (H rho : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.transpose = H)
    (hrho : rho.transpose = rho) :
    hilbertSchmidtPairing (H * rho - rho * H) H = 0 := by
  dsimp [hilbertSchmidtPairing]
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    hH, hrho, Matrix.sub_mul, Matrix.trace_sub]
  have h₁ : trace (rho * H * H) = trace (H * (rho * H)) := by
    calc
      trace (rho * H * H) = trace ((rho * H) * H) := by
        rw [Matrix.mul_assoc]
      _ = trace (H * (rho * H)) := Matrix.trace_mul_comm (rho * H) H
  have h₂ : trace (H * rho * H) = trace (H * (rho * H)) := by
    rw [Matrix.mul_assoc]
  rw [h₁, h₂]
  exact sub_self _

/-- **Theorem**: Hilbert-Schmidt Entropy Dissipation Non-Negativity. -/
theorem hilbertSchmidt_dissipation_nonneg (dS : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ hilbertSchmidtPairing dS dS :=
  hilbertSchmidt_pos_semidef dS

end HilbertSchmidtMatrix
