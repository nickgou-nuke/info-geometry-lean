import Mathlib
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Phase 5: Spectral Theorem for Self-Adjoint Operators (PROVED)

Uses mathlib's existing `LinearMap.IsSymmetric.diagonalization` to prove the
finite-dimensional spectral theorem for self-adjoint operators on a real
inner product space.

This completes the AFP Spectral_Theorem.thy analog in finite dimensions.
-/

noncomputable section

open FiniteDimensional

namespace HilbertTensorProduct.SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/--
**Finite-Dimensional Spectral Theorem (REAL, SELF-ADJOINT) — PROVED.**

Every self-adjoint operator A : H → H on a finite-dimensional real Hilbert space
admits an orthonormal basis of eigenvectors. Equivalently, there exist:
  - An orthonormal basis e₁, ..., e_n of H
  - Real eigenvalues λ₁, ..., λ_n
such that A e_i = λ_i e_i for all i.

This is the real analog of the Isabelle AFP's Spectral_Theorem.thy and
Compact_Operators.thy (compact self-adjoint case). In finite dimensions,
every operator is compact, so the general spectral theorem reduces to
this diagonalization result.

Proof: mathlib's `LinearMap.IsSymmetric.diagonalization` (imported from
`Mathlib/LinearAlgebra/Matrix/Diagonalization`).
-/
theorem spectral_theorem_self_adjoint (A : H →L[ℝ] H) (h_adj : A.adjoint = A) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℝ H) (ls : Fin n → ℝ),
      ∀ i, A (e i) = ls i • (e i) := by
  -- Step 1: Convert to `LinearMap.IsSymmetric`.
  have h_sym : (A.toLinearMap).IsSymmetric := by
    intro x y
    simpa [h_adj] using (A.adjoint_inner_right x y).symm

  -- Step 2: mathlib's eigenvector basis theorem.
  refine ⟨Module.finrank ℝ H, h_sym.eigenvectorBasis rfl, h_sym.eigenvalues rfl, ?_⟩
  intro i
  exact h_sym.apply_eigenvectorBasis rfl i

end HilbertTensorProduct.SpectralTheorem
