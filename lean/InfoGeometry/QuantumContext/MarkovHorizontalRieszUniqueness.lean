/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMatrixRieszGradient

/-!
# Unique horizontal representative for a Markov matrix objective

The ambient full-matrix Riesz representative projects to the unique
horizontal matrix representing the restriction of the objective to the
Markov horizontal subspace. Uniqueness uses strict positivity of the
stationary-weighted pairing; no inverse of the singular Markov Laplacian or
flow/convergence statement is asserted.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.NaturalGradientSubmersionFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The horizontal variational equation has exactly one solution: the
horizontal projection of the ambient full-matrix Riesz representative. -/
theorem existsUnique_markovHorizontalGradient
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i)
    (objective : Module.Dual ℝ (Matrix ι ι ℝ)) :
    ∃! X : Matrix ι ι ℝ,
      (markovNaturalGradientSubmersionSystem P π hP hDB).split.projH X = X ∧
      ∀ Y, (markovNaturalGradientSubmersionSystem P π hP hDB).split.projH Y = Y →
        weightedMatrixPairing π X Y = objective Y := by
  let sys := markovNaturalGradientSubmersionSystem P π hP hDB
  let grad := weightedMatrixGradient π hπ objective
  let horiz := sys.split.projH grad
  refine ⟨horiz, ?_, ?_⟩
  · constructor
    · exact sys.split.idemH grad
    · intro Y hY
      have hrep := markovHorizontalGradient_represents P π hP hDB hπ
        objective Y
      rw [hY] at hrep
      simpa [sys, horiz, grad] using hrep
  · intro X hX
    rcases hX with ⟨hXh, hXrep⟩
    have hHoriz : sys.split.projH horiz = horiz := by
      dsimp [horiz]
      exact sys.split.idemH grad
    have hDelta : sys.split.projH (X - horiz) = X - horiz := by
      rw [map_sub, hXh, hHoriz]
    have hXtest := hXrep (X - horiz) hDelta
    have hHtest := markovHorizontalGradient_represents P π hP hDB hπ
      objective (X - horiz)
    rw [hDelta] at hHtest
    have hPair : weightedMatrixPairing π X (X - horiz) =
        weightedMatrixPairing π horiz (X - horiz) := by
      rw [hXtest, hHtest]
    have hPairB : weightedMatrixBilin π X (X - horiz) =
        weightedMatrixBilin π horiz (X - horiz) := hPair
    have hDiff : weightedMatrixPairing π (X - horiz) (X - horiz) = 0 := by
      change weightedMatrixBilin π (X - horiz) (X - horiz) = 0
      have hlinearMap : weightedMatrixBilin π (X - horiz) =
          weightedMatrixBilin π X - weightedMatrixBilin π horiz :=
        map_sub (weightedMatrixBilin π) X horiz
      have hlinear := congrArg
        (fun f : Matrix ι ι ℝ →ₗ[ℝ] ℝ => f (X - horiz)) hlinearMap
      rw [hlinear, LinearMap.sub_apply, hPairB]
      exact sub_self _
    have hZero : X - horiz = 0 :=
      (weightedMatrixPairing_self_eq_zero_iff π hπ (X - horiz)).mp hDiff
    exact sub_eq_zero.mp hZero

end InfoGeometry.QuantumContext.MarkovDrazin

end
