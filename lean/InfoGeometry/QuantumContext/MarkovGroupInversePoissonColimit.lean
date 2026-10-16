/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit

/-!
# Markov group-inverse Poisson equation in the matrix-stage colimit

The finite Markov Laplacian and one of its group inverses are transported
into the quotient direct colimit of full complex matrix stages. On the image
of left multiplication by that Laplacian (its principal right ideal), the
transported group inverse solves the Poisson equation exactly. This is an
algebraic statement about the full noncommutative colimit ring; it does not
assign stochasticity or positivity to arbitrary colimit elements.
-/

namespace InfoGeometry.QuantumContext.MarkovGroupInversePoissonColimit

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit

/-- A group inverse solves the left-multiplication equation on the image of
left multiplication by its operator (the principal right ideal `A * R`). The
multiplication is that of an arbitrary, possibly noncommutative ring. -/
theorem groupInverse_recovers_on_leftRange {R : Type*} [Ring R]
    (A G b : R) (hG : IsGroupInverse A G)
    (hb : ∃ y : R, b = A * y) : A * (G * b) = b := by
  obtain ⟨y, rfl⟩ := hb
  calc
    A * (G * (A * y)) = (A * G * A) * y := by
      simp only [mul_assoc]
    _ = A * y := by rw [hG.1]

/-- For a finite real row-stochastic matrix, the Markov Laplacian and a group
inverse can be transported to the quotient matrix-stage colimit. The
transported Green operator solves `L * x = b` for every `b` in the image of
left multiplication by the transported `L` (the principal right ideal `L * R`). -/
theorem exists_rowStochastic_groupInverse_poissonSolver_inMatrixStageLimit
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (n : ℕ) (e : ι ≃ BitWord n) (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : MatrixStageLimit,
      IsGroupInverse
        (canonicalStageHom n (realMatrixToComplexStage n e (1 - P))) G ∧
      ∀ b : MatrixStageLimit,
        (∃ y : MatrixStageLimit,
          b = canonicalStageHom n (realMatrixToComplexStage n e (1 - P)) * y) →
        canonicalStageHom n (realMatrixToComplexStage n e (1 - P)) * (G * b) = b := by
  obtain ⟨G, hG⟩ :=
    exists_rowStochastic_groupInverse_inMatrixStageLimit n e P hP
  refine ⟨G, hG, ?_⟩
  intro b hb
  exact groupInverse_recovers_on_leftRange
    (canonicalStageHom n (realMatrixToComplexStage n e (1 - P))) G b hG hb

end InfoGeometry.QuantumContext.MarkovGroupInversePoissonColimit
