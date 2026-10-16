/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.Probability.FiniteMarkovWeightedAdjoint
import InfoGeometry.QuantumContext.MarkovAttentionFiniteDirichlet

/-!
# Weighted reciprocity of finite Markov Green operators

Detailed balance makes the Markov Laplacian self-adjoint for its stationary
weighted pairing. Uniqueness of the group inverse then makes the Green
operator self-adjoint for that same pairing. No positivity or nondegeneracy
claim about the weights is made here beyond the nonzero hypothesis needed to
define the weighted adjoint.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted self-adjoint matrix has a weighted self-adjoint group inverse. -/
theorem weightedAdjoint_groupInverse_self
    (π : ι → ℝ) (L G : Matrix ι ι ℝ)
    (hπ : ∀ i, π i ≠ 0)
    (hL : InfoGeometry.Probability.weightedAdjoint π L = L)
    (hG : IsGroupInverse L G) :
    InfoGeometry.Probability.weightedAdjoint π G = G := by
  have hGadj : IsGroupInverse L (InfoGeometry.Probability.weightedAdjoint π G) := by
    constructor
    · have h := congrArg (InfoGeometry.Probability.weightedAdjoint π) hG.1
      rw [InfoGeometry.Probability.weightedAdjoint_mul π (L * G) L hπ,
        InfoGeometry.Probability.weightedAdjoint_mul π L G hπ, hL] at h
      simpa only [mul_assoc] using h
    constructor
    · have h := congrArg (InfoGeometry.Probability.weightedAdjoint π) hG.2.1
      rw [InfoGeometry.Probability.weightedAdjoint_mul π (G * L) G hπ,
        InfoGeometry.Probability.weightedAdjoint_mul π G L hπ, hL] at h
      simpa only [mul_assoc] using h
    · have h := congrArg (InfoGeometry.Probability.weightedAdjoint π) hG.2.2
      rw [InfoGeometry.Probability.weightedAdjoint_mul π L G hπ,
        InfoGeometry.Probability.weightedAdjoint_mul π G L hπ, hL] at h
      exact h.symm
  exact (IsGroupInverse.unique hG hGadj).symm

/-- Under detailed balance, the group inverse of `I - P` is symmetric for
the stationary-weighted bilinear pairing. The group inverse itself is an
explicit hypothesis; this theorem does not claim its existence. -/
theorem weightedMarkovPairing_groupInverse_symmetric
    (P G : Matrix ι ι ℝ) (π x y : ι → ℝ)
    (hπ : ∀ i, π i ≠ 0)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hG : IsGroupInverse (1 - P) G) :
    weightedMarkovPairing π x (Matrix.mulVec G y) =
      weightedMarkovPairing π (Matrix.mulVec G x) y := by
  have hP :=
    (InfoGeometry.Probability.detailedBalance_iff_weightedAdjoint_eq π P hπ).mp hDB
  have hL : InfoGeometry.Probability.weightedAdjoint π (1 - P) = 1 - P := by
    rw [InfoGeometry.Probability.weightedAdjoint_sub,
      InfoGeometry.Probability.weightedAdjoint_one π hπ, hP]
  have hGself := weightedAdjoint_groupInverse_self π (1 - P) G hπ hL hG
  have hGDB : InfoGeometry.Probability.DetailedBalance π G :=
    (InfoGeometry.Probability.detailedBalance_iff_weightedAdjoint_eq π G hπ).mpr hGself
  exact weightedMarkovPairing_mulVec_symmetric G π x y hGDB

end InfoGeometry.QuantumContext.MarkovDrazin
